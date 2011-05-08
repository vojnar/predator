/*
 * Copyright (C) 2010 Kamil Dudka <kdudka@redhat.com>
 *
 * This file is part of predator.
 *
 * predator is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version.
 *
 * predator is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with predator.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "config.h"
#include "symcut.hh"

#include <cl/cl_msg.hh>
#include <cl/clutil.hh>
#include <cl/code_listener.h>
#include <cl/storage.hh>

#include "symclone.hh"
#include "symplot.hh"
#include "symseg.hh"
#include "symutil.hh"
#include "worklist.hh"

#include <algorithm>            // for std::copy, std::set_difference
#include <iomanip>
#include <map>
#include <set>
#include <stack>
#include <vector>

#include <boost/foreach.hpp>
#include <boost/tuple/tuple.hpp>

#ifndef SE_DISABLE_SYMCUT
#   define SE_DISABLE_SYMCUT 0
#endif

#ifndef DEBUG_SYMCUT
#   define DEBUG_SYMCUT 0
#endif

template <class TSet, class TList>
void fillSet(TSet &dst, const TList &src)
{
    std::copy(src.begin(), src.end(), std::inserter(dst, dst.begin()));
}

struct DeepCopyData {
    typedef std::map<TValId   /* src */, TValId   /* dst */>    TValMap;
    typedef std::pair<TObjId  /* src */, TObjId   /* dst */>    TItem;
    typedef std::set<CVar>                                      TCut;

    SymHeap             &src;
    SymHeap             &dst;
    TCut                &cut;
    const bool          digBackward;

    TValMap             valMap;

    WorkList<TItem>     wl;

    DeepCopyData(const SymHeap &src_, SymHeap &dst_, TCut &cut_,
                 bool digBackward_):
        src(/* XXX */ const_cast<SymHeap &>(src_)),
        dst(dst_),
        cut(cut_),
        digBackward(digBackward_)
    {
    }
};

class DCopyObjVisitor {
    private:
        DeepCopyData &dc_;

    public:
        DCopyObjVisitor(DeepCopyData &dc): dc_(dc) { }

        bool operator()(const boost::array<TObjId, 2> &item) {
            const TObjId objSrc = item[/* src */ 0];
            const TObjId objDst = item[/* dst */ 1];

            const TValId srcAt = dc_.src.placedAt(objSrc);
            const TValId dstAt = dc_.dst.placedAt(objDst);
            dc_.valMap[srcAt] = dstAt;

            // FIXME: schedule by values instead
            dc_.wl.schedule(objSrc, objDst);

            return /* continue */ true;
        }
};

void digSubObjs(DeepCopyData &dc, TValId addrSrc, TValId addrDst)
{
    boost::array<const SymHeap *, 2> sh;
    sh[0] = &dc.src;
    sh[1] = &dc.dst;

    boost::array<TObjId, 2> root;
    root[0] = /* XXX */ dc.src.objAt(addrSrc);
    root[1] = /* XXX */ dc.dst.objAt(addrDst);

    // FIXME: schedule by values instead
    dc.wl.schedule(root[0], root[1]);
    dc.valMap[addrSrc] = addrDst;

    DCopyObjVisitor objVisitor(dc);
    traverseSubObjs<2>(sh, root, objVisitor);
}

void addObjectIfNeeded(DeepCopyData &dc, TValId rootSrcAt) {
    if (hasKey(dc.valMap, rootSrcAt))
        // mapping already known
        return;

    SymHeap &src = dc.src;
    SymHeap &dst = dc.dst;

    CVar cv;
    if (SymHeap::isProgramVar(src.valTarget(rootSrcAt))) {
        // program variable
        cv = src.cVarByRoot(rootSrcAt);
#if DEBUG_SYMCUT
        const size_t orig = dc.cut.size();
#endif
        // enlarge the cut if needed
        dc.cut.insert(cv);
#if DEBUG_SYMCUT
        if (dc.cut.size() != orig)
            CL_DEBUG("addObjectIfNeeded() is enlarging the cut by cVar #"
                    << cv.uid << ", nestlevel = " << cv.inst);
#endif
        const TValId rootDstAt = dst.addrOfVar(cv);
        digSubObjs(dc, rootSrcAt, rootDstAt);
        return;
    }

    // create the object in 'dst'
    const TObjId rootSrc = src.objAt(rootSrcAt);
    TValId rootDstAt = (OBJ_RETURN == rootSrc)
        ? dst.placedAt(OBJ_RETURN)
        : dst.heapAlloc(src.valSizeOfTarget(rootSrcAt));
    const TObjType clt = src.objType(rootSrc);
    if (clt)
        dst.objDefineType(dst.objAt(rootDstAt), clt);

    // preserve metadata of abstract objects
    const bool isProto = src.valTargetIsProto(rootSrcAt);
    dst.valTargetSetProto(rootDstAt, isProto);
    if (SymHeap::isAbstract(src.valTarget(rootSrcAt))) {
        const EObjKind kind = src.valTargetKind(rootSrcAt);
        const BindingOff &off = segBinding(src, rootSrc);
        dst.valTargetSetAbstract(rootDstAt, kind, off);
    }

    // look inside
    digSubObjs(dc, rootSrcAt, rootDstAt);
}

// TODO: optimize out all the unnecessary dc.valMap lookups
TValId handleValueCore(DeepCopyData &dc, TValId srcAt) {
    SymHeap &src = dc.src;
    if (!hasKey(dc.valMap, srcAt)) {
        const TValId rootSrcAt = src.valRoot(srcAt);
        const TOffset off = src.valOffset(srcAt);
        addObjectIfNeeded(dc, rootSrcAt);
        if (off)
            dc.valMap[srcAt] = dc.dst.valByOffset(dc.valMap[rootSrcAt], off);
    }

    return dc.valMap[srcAt];
}

void trackUses(DeepCopyData &dc, TValId valSrc) {
    if (!dc.digBackward)
        // optimization
        return;

    // go from the value backward
    TObjList uses;
    dc.src.usedBy(uses, valSrc);
    BOOST_FOREACH(TObjId objSrc, uses) {
        const TValId srcAt = dc.src.placedAt(objSrc);
        handleValueCore(dc, srcAt);
    }
}

TValId handleValue(DeepCopyData &dc, TValId valSrc) {
    const SymHeap   &src = dc.src;
    SymHeap         &dst = dc.dst;

    if (valSrc <= 0)
        // special value IDs always match
        return valSrc;

    DeepCopyData::TValMap &valMap = dc.valMap;
    DeepCopyData::TValMap::iterator iterValSrc = valMap.find(valSrc);
    if (valMap.end() != iterValSrc)
        // good luck, we have already handled the value before
        return iterValSrc->second;

    trackUses(dc, valSrc);

    const int custom = src.valGetCustom(valSrc);
    if (-1 != custom) {
        // custom value, e.g. fnc pointer
        const TValId valDst = dst.valCreateCustom(custom);
        valMap[valSrc] = valDst;
        return valDst;
    }

    const EUnknownValue code = src.valGetUnknown(valSrc);
    switch (code) {
        case UV_ABSTRACT:
            // will be handled later
        case UV_KNOWN:
            break;

        default: {
            // a proper unkonwn value
            const TValId valDst = dst.valCreateUnknown(code);
            valMap[valSrc] = valDst;
            return valDst;
        }
    }

    // now is the time to "dereference" the value
    const TObjId targetSrc = src.pointsTo(valSrc);
    CL_BREAK_IF(OBJ_INVALID == targetSrc);

    if (targetSrc < 0) {
        // special handling for OBJ_DELETED/OBJ_LOST
        CL_BREAK_IF(OBJ_DELETED != targetSrc && OBJ_LOST != targetSrc);
        const TValId valDst = dst.valCreateDangling(targetSrc);
        valMap[valSrc] = valDst;
        return valDst;
    }

    // create the target object, if it does not exist already
    return handleValueCore(dc, valSrc);
}

void deepCopy(DeepCopyData &dc) {
    const SymHeap   &src = dc.src;
    SymHeap         &dst = dc.dst;

    DeepCopyData::TItem item;
    while (dc.wl.next(item)) {
        const TObjId objSrc = item.first;
        const TObjId objDst = item.second;
        CL_BREAK_IF(objSrc < 0 || objDst < 0);

        // read the address
        const TValId atSrc = src.placedAt(objSrc);
        CL_BREAK_IF(atSrc <= 0);
        trackUses(dc, atSrc);

        // read the original value
        TValId valSrc = src.valueOf(objSrc);
        CL_BREAK_IF(VAL_INVALID == valSrc);
        if (-1 != src.valGetCompositeObj(valSrc))
            continue;

        // do whatever we need to do with the value
        const TValId valDst = handleValue(dc, valSrc);
        CL_BREAK_IF(VAL_INVALID == valDst);

        // now set object's value
        dst.objSetValue(objDst, valDst);
    }

    // finally copy all relevant Neq predicates
    src.copyRelevantPreds(dst, dc.valMap);
}

void prune(const SymHeap &src, SymHeap &dst,
           /* NON-const */ DeepCopyData::TCut &cut, bool forwardOnly = false)
{
    DeepCopyData dc(src, dst, cut, !forwardOnly);
    DeepCopyData::TCut snap(cut);

    // go through all program variables
    BOOST_FOREACH(CVar cv, snap) {
        const TValId srcAt = dc.src.addrOfVar(cv);
        const TValId dstAt = dc.dst.addrOfVar(cv);
        digSubObjs(dc, srcAt, dstAt);
    }

    // go through the worklist
    deepCopy(dc);
}

namespace {
    void plotHeap(const SymHeap &sh, const char *name)
    {
        SymPlot plotter(sh);
        plotter.plot(name);
    }
}

void splitHeapByCVars(
        SymHeap                     *srcDst,
        const TCVarList             &cut,
        SymHeap                     *saveSurroundTo)
{
#if SE_DISABLE_SYMCUT
    return;
#endif
    CL_DEBUG("splitHeapByCVars() started: cut by " << cut.size() << " variable(s)");

    // get the set of live program variables
    TCVarList liveList;
    srcDst->gatherCVars(liveList);
    DeepCopyData::TCut live;
    fillSet(live, liveList);

    // make an intersection with the cut
    DeepCopyData::TCut cset;
    BOOST_FOREACH(const CVar &cv, cut) {
#if SE_LAZY_VARS_CREATION
        if (hasKey(live, cv))
#endif
            cset.insert(cv);
    }

    // cut the first part
    const unsigned cntOrig = cset.size();
    SymHeap dst(srcDst->stor());
    prune(*srcDst, dst, cset);

    if (!saveSurroundTo) {
        // we're done
        *srcDst = dst;
        return;
    }
#if DEBUG_SYMCUT
    CL_DEBUG("splitHeapByCVars() is computing the surround...");
#endif
    // get the complete list of program variables
    TCVarList all;
    srcDst->gatherCVars(all);

    // compute set difference
    DeepCopyData::TCut complement;
    std::set_difference(all.begin(), all.end(), cset.begin(), cset.end(),
            std::inserter(complement, complement.begin()));

    // compute the surrounding part of heap
    prune(*srcDst, *saveSurroundTo, complement);

    // print some statistics
    const unsigned cntA = cset.size();
    const unsigned cntB = complement.size();
    const unsigned cntTotal = all.size();
    CL_DEBUG("splitHeapByCVars() finished: "
            << cntOrig << " -> " << cntA << " |" << cntB
            << " (" << cntTotal << " program variables in total)");

    const float ratio = 100.0 * dst.lastId() / srcDst->lastId();
    CL_DEBUG("splitHeapByCVars() resulting heap size: " << std::fixed
            << std::setprecision(2) << std::setw(5) << ratio << "%");

#ifndef NDEBUG
    // basic sanity check
    if (cntA < cntOrig || cntA + cntB != cntTotal) {
        CL_ERROR("symcut: splitHeapByCVars() failed, attempt to plot heaps...");
        plotHeap(*srcDst,         "prune-input");
        plotHeap( dst,            "prune-output");
        plotHeap(*saveSurroundTo, "prune-surround");
        CL_NOTE("symcut: plot done, please consider analyzing the results");
        CL_TRAP;
    }
#endif

    // update *srcDst (we can't do it sooner because of the plotting above)
    *srcDst = dst;
}

void joinHeapsByCVars(
        SymHeap                     *srcDst,
        const SymHeap               *src2)
{
#if SE_DISABLE_SYMCUT
    return;
#endif
    // gather _all_ program variables of *src2
    TCVarList all;
    src2->gatherCVars(all);

    // std::vector -> std::set
    DeepCopyData::TCut cset;
    fillSet(cset, all);
    
    // forward-only merge of *src2 into *srcDst
    prune(*src2, *srcDst, cset, /* optimization */ true);
}
