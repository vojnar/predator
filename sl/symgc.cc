/*
 * Copyright (C) 2009 Kamil Dudka <kdudka@redhat.com>
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
#include "symgc.hh"

#include <cl/cl_msg.hh>
#include <cl/storage.hh>

#include "symheap.hh"
#include "symplot.hh"
#include "symutil.hh"
#include "worklist.hh"

#include <stack>
#include <vector>

#include <boost/foreach.hpp>

void gatherReferredRoots(TValList &dst, SymHeap &sh, TValId at) {
    CL_BREAK_IF(sh.valOffset(at));

    ObjList ptrs;
    sh.gatherLivePointers(ptrs, at);
    BOOST_FOREACH(const ObjHandle &obj, ptrs) {
        const TValId val = obj.value();
        if (val <= 0)
            continue;

        const TValId root = sh.valRoot(val);
        dst.push_back(root);
    }
}

template <class TWL>
void digPointingObjects(TWL &wl, const SymHeap &sh, TValId val) {
    // go through all objects having the value
    ObjList cont;
    sh.usedBy(cont, val);
    BOOST_FOREACH(const ObjHandle &obj, cont) {
        wl.schedule(obj);
    }

    // seek object's root
    const TValId root = sh.valRoot(val);
    if (root < 0)
        return;

    // traverse all subobjects
    ObjList refs;
    sh.pointedBy(refs, root);
    BOOST_FOREACH(const ObjHandle &obj, refs) {
        wl.schedule(obj);
    }
}

bool digJunk(SymHeap &heap, TValId *ptrVal) {
    if (*ptrVal <= 0)
        return false;

    const EValueTarget code = heap.valTarget(*ptrVal);
    if (!isOnHeap(code))
        // non-heap objects cannot be JUNK
        return false;

    // only root objects can be destroyed
    *ptrVal = heap.valRoot(*ptrVal);

    WorkList<ObjHandle> wl;
    digPointingObjects(wl, heap, *ptrVal);

    ObjHandle obj;
    while (wl.next(obj)) {
        const TValId val = obj.placedAt();
        if (!isOnHeap(heap.valTarget(val)))
            // non-heap object simply can't be JUNK
            return false;

        digPointingObjects(wl, heap, val);
    }

    return true;
}

bool collectJunk(SymHeap &sh, TValId root, TValList *leakList) {
    CL_BREAK_IF(sh.valOffset(root));
    bool detected = false;

    std::stack<TValId> todo;
    todo.push(root);
    while (!todo.empty()) {
        root = todo.top();
        todo.pop();

        if (digJunk(sh, &root)) {
            detected = true;

            // gather all referred roots pointed by the junk object
            std::vector<TValId> refs;
            gatherReferredRoots(refs, sh, root);

            if (leakList)
                leakList->push_back(root);

            // destroy junk
            sh.valDestroyTarget(root);

            // schedule just created junk candidates for next wheel
            BOOST_FOREACH(TValId refRoot, refs)
                todo.push(refRoot);
        }
    }

    return detected;
}

bool destroyRootAndCollectJunk(
        SymHeap                 &sh,
        const TValId             root,
        TValList                *leakList)
{
    CL_BREAK_IF(sh.valOffset(root));
    CL_BREAK_IF(!isPossibleToDeref(sh.valTarget(root)));

    // gather potentialy destroyed pointer values
    TValList killedPtrs;
    gatherReferredRoots(killedPtrs, sh, root);

    // destroy the target
    sh.valDestroyTarget(root);

    // now check for memory leakage
    bool leaking = false;
    BOOST_FOREACH(TValId val, killedPtrs) {
        if (collectJunk(sh, val, leakList))
            leaking = true;
    }

    return leaking;
}

// /////////////////////////////////////////////////////////////////////////////
// implementation of LeakMonitor
static bool debuggingGarbageCollector = static_cast<bool>(DEBUG_SYMGC);

void debugGarbageCollector(const bool enable) {
    if (enable == ::debuggingGarbageCollector)
        return;

    CL_DEBUG("symgc: debugGarbageCollector(" << enable << ") takes effect");
    ::debuggingGarbageCollector = enable;
}

void LeakMonitor::enter() {
    if (::debuggingGarbageCollector)
        snap_ = sh_;
}

void LeakMonitor::leave() {
    if (leakList_.empty())
        return;

    if (::debuggingGarbageCollector)
        plotHeap(snap_, "memleak", /* TODO: loc */ 0, leakList_,
                /* digForward */ false);
}
