/*
 * Copyright (C) 2009 Kamil Dudka <kdudka@redhat.com>
 *
 * This file is part of sl.
 *
 * sl is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version.
 *
 * sl is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sl.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "symexec.hh"

#include "cl_private.hh"
#include "location.hh"
#include "storage.hh"
#include "symheap.hh"

#include <map>
#include <set>
#include <stack>

#include <boost/foreach.hpp>
#include <boost/tuple/tuple.hpp>

class SymHeapProcessor {
    public:
        SymHeapProcessor(SymbolicHeap::SymHeap &heap):
            heap_(heap)
        {
        }

        void exec(const CodeStorage::Insn &insn);

    private:
        int /* val */ heapValFromCst(const struct cl_operand &op);
        void heapVarHandleAccessor(int *pVar, const struct cl_accessor *ac);
        int /* var */ heapVarFromOperand(const struct cl_operand &op);
        int /* val */ heapValFromOperand(const struct cl_operand &op);
        void execUnary(const CodeStorage::Insn &insn);
        void execMalloc(const CodeStorage::TOperandList &opList);
        void execFree(const CodeStorage::TOperandList &opList);
        void execCall(const CodeStorage::Insn &insn);

    private:
        SymbolicHeap::SymHeap       &heap_;
        LocationWriter              lw_;
};

class SymHeapUnion {
    private:
        typedef std::vector<SymbolicHeap::SymHeap> TList;

    public:
        typedef TList::const_iterator const_iterator;
        typedef const_iterator iterator;

    public:
        void insert(const SymbolicHeap::SymHeap &heap);

        /**
         * return STL-like iterator to go through the container
         */
        const_iterator begin() const { return heaps_.begin(); }

        /**
         * return STL-like iterator to go through the container
         */
        const_iterator end()   const { return heaps_.end();   }

        /**
         * return count of object stored in the container
         */
        size_t size()          const { return heaps_.size();  }

    private:
        TList heaps_;
};

typedef std::set<const CodeStorage::Block *>                TBlockSet;
typedef std::map<const CodeStorage::Block *, SymHeapUnion>  TStateMap;

// /////////////////////////////////////////////////////////////////////////////
// SymHeapProcessor implementation
int /* val */ SymHeapProcessor::heapValFromCst(const struct cl_operand &op) {
    enum cl_type_e code = op.type->code;
    switch (code) {
        case CL_TYPE_INT:
            CL_DEBUG("CL_TYPE_INT treated as pointer");
            // go through!

        case CL_TYPE_PTR:
            break;

        default:
            TRAP;
    }

    const struct cl_cst &cst = op.data.cst;
    code = cst.code;
    switch (code) {
        case CL_TYPE_INT:
            if (0 == cst.data.cst_int.value)
                return SymbolicHeap::VAL_NULL;
            // go through!

        default:
            TRAP;
            return SymbolicHeap::VAL_INVALID;
    }
}

void SymHeapProcessor::heapVarHandleAccessor(int *pObj,
                                             const struct cl_accessor *ac)
{
    using namespace SymbolicHeap;
    if (CL_ACCESSOR_DEREF != ac->code)
        // not implemented yet
        TRAP;

    // attempt to dereference
    const int val = heap_.valueOf(*pObj);
    switch (val) {
        case VAL_NULL:
            CL_MSG_STREAM(cl_error, lw_ << "error: dereference of NULL value");
            goto unknown_obj;

        case VAL_UNINITIALIZED:
            CL_MSG_STREAM(cl_error, lw_ << "error: dereference of uninitialized value");
            goto unknown_obj;

        // TODO
        case VAL_UNKNOWN:
        case VAL_INVALID:
            TRAP;

        default:
            break;
    }

    // value lookup
    *pObj = heap_.pointsTo(val);
    switch (*pObj) {
        // TODO
        case OBJ_DELETED:
        case OBJ_INVALID:
            TRAP;

        default:
            return;
    }

unknown_obj:
    *pObj = OBJ_UNKNOWN;
}

int /* var */ SymHeapProcessor::heapVarFromOperand(const struct cl_operand &op)
{
    using SymbolicHeap::OBJ_INVALID;
    int uid;

    const enum cl_operand_e code = op.code;
    switch (code) {
        case CL_OPERAND_VAR:
            uid = op.data.var.id;
            break;

        case CL_OPERAND_REG:
            uid = op.data.reg.id;
            break;

        default:
            TRAP;
            return OBJ_INVALID;
    }

    int var = heap_.varByCVar(uid);
    if (OBJ_INVALID == var)
        // unable to resolve static variable
        TRAP;

    // go through the list of accessors
    const struct cl_accessor *ac = op.accessor;
    if (ac && ac->code == CL_ACCESSOR_REF)
        // CL_ACCESSOR_REF will be processed as soon as this function finishes
        // ... otherwise we are encountering a bug!
        ac = ac->next;

    // process all other accessors (only CL_ACCESSOR_DEREF for now)
    while (ac) {
        this->heapVarHandleAccessor(&var, ac);
        ac = ac->next;
    }

    return var;
}

int /* val */ SymHeapProcessor::heapValFromOperand(const struct cl_operand &op)
{
    using namespace SymbolicHeap;

    const enum cl_operand_e code = op.code;
    switch (code) {
        case CL_OPERAND_VAR:
        case CL_OPERAND_REG: {
            int var = heapVarFromOperand(op);
            if (OBJ_INVALID == var)
                TRAP;

            const struct cl_accessor *ac = op.accessor;
            return (ac && ac->code == CL_ACCESSOR_REF)
                ? heap_.placedAt(var)
                : heap_.valueOf(var);
        }

        case CL_OPERAND_CST:
            return heapValFromCst(op);

        default:
            TRAP;
            return OBJ_INVALID;
    }
}

void SymHeapProcessor::execFree(const CodeStorage::TOperandList &opList) {
    using namespace SymbolicHeap;
    if (/* dst + fnc + ptr */ 3 != opList.size())
        TRAP;

    if (CL_OPERAND_VOID != opList[0].code)
        // Oops, free() does not usually return a value
        TRAP;

    const int val = heapValFromOperand(opList[/* ptr given to free() */ 2]);
    if (VAL_INVALID == val)
        // could not resolve value to be freed
        TRAP;

    switch (val) {
        case VAL_NULL:
            CL_MSG_STREAM(cl_debug, lw_
                    << "debug: ignoring free() called with NULL value");
            return;

        case VAL_INVALID:
        case VAL_UNINITIALIZED:
        case VAL_UNKNOWN:
            CL_MSG_STREAM(cl_error, lw_
                    << "error: invalid free() detected");
            return;

        default:
            break;
    }

    const int obj = heap_.pointsTo(val);
    switch (obj) {
        case OBJ_DELETED:
            CL_MSG_STREAM(cl_error, lw_
                    << "error: double free() detected");
            return;

        case OBJ_UNKNOWN:
        case OBJ_INVALID:
            TRAP;
        default:
            break;
    }

    CL_MSG_STREAM(cl_debug, lw_ << "executing free()");
    heap_.objDestroy(obj);
}

void SymHeapProcessor::execMalloc(const CodeStorage::TOperandList &opList) {
    using namespace SymbolicHeap;
    if (/* dst + fnc + size */ 3 != opList.size())
        TRAP;

    const struct cl_operand &dst = opList[0];
    int varLhs = heapVarFromOperand(dst);
    if (OBJ_INVALID == varLhs)
        // could not resolve lhs
        TRAP;

    const struct cl_operand &amount = opList[2];
    if (CL_OPERAND_CST != amount.code)
        // amount of allocated memory not constant
        TRAP;

    const struct cl_cst &cst = amount.data.cst;
    if (CL_TYPE_INT != cst.code)
        // amount of allocated memory not a number
        TRAP;

    // FIXME: we simply ignore the ammount of allocated memory
    const int cbAmount = cst.data.cst_int.value;
    CL_MSG_STREAM(cl_debug, lw_ << "executing malloc(" << cbAmount << ")");

    // FIXME: we can't use dst.type as type of the created obj in most cases :-(
    const int obj = heap_.varCreate(dst.type, /* heap obj */ -1);
    if (OBJ_INVALID == obj)
        // unable to create dynamic variable
        TRAP;

    // TODO: delayed var creation?
    const int val = heap_.placedAt(obj);
    switch (val) {
        case VAL_NULL:
        case VAL_INVALID:
        case VAL_UNINITIALIZED:
        case VAL_UNKNOWN:
            TRAP;

        default:
            break;
    }

    // store the result of malloc
    // TODO: check for possible JUNK here!
    heap_.objSetValue(varLhs, val);
}

void SymHeapProcessor::execCall(const CodeStorage::Insn &insn) {
    using namespace SymbolicHeap;

    const CodeStorage::TOperandList &opList = insn.operands;
    const struct cl_operand &fnc = opList[1];
    if (CL_OPERAND_CST != fnc.code)
        // indirect call not implemented yet
        TRAP;

    const struct cl_cst &cst = fnc.data.cst;
    if (CL_TYPE_FNC != cst.code)
        // incorrect cst used as fnc in call
        TRAP;

    const char *fncName = cst.data.cst_fnc.name;
    if (!fncName)
        // Aieee, anonymous fnc is going to be called
        TRAP;

    if (CL_SCOPE_GLOBAL != fnc.scope || !cst.data.cst_fnc.is_extern)
        // generic function call not implemented yet
        TRAP;

    if (STREQ(fncName, "malloc")) {
        this->execMalloc(opList);
        return;
    }

    if (STREQ(fncName, "free")) {
        this->execFree(opList);
        return;
    }

    // TODO: handle generic function call
    TRAP;
}

void SymHeapProcessor::execUnary(const CodeStorage::Insn &insn) {
    using namespace SymbolicHeap;

    enum cl_unop_e code = static_cast<enum cl_unop_e> (insn.subCode);
    if (CL_UNOP_ASSIGN != code)
        // not implemented yet
        TRAP;

    int varLhs = heapVarFromOperand(insn.operands[0]);
    switch (varLhs) {
        case OBJ_UNKNOWN:
            CL_MSG_STREAM(cl_debug, lw_ <<
                    "ignoring OBJ_UNKNOWN as lhs, this is definitely a bug "
                    "if there is no error reported above...");
            return;

        case OBJ_DELETED:
        case OBJ_INVALID:
            TRAP;
    }

    int valRhs = heapValFromOperand(insn.operands[1]);
    if (VAL_INVALID == valRhs)
        // could not resolve rhs
        TRAP;


    // TODO: check for possible JUNK here!
    heap_.objSetValue(varLhs, valRhs);
}

void SymHeapProcessor::exec(const CodeStorage::Insn &insn) {
    using namespace CodeStorage;

    lw_ = &insn.loc;
    CL_MSG_STREAM(cl_debug, lw_ << "debug: executing non-terminal insn...");

    const enum cl_insn_e code = insn.code;
    switch (code) {
        case CL_INSN_UNOP:
            this->execUnary(insn);
            break;

        case CL_INSN_CALL:
            this->execCall(insn);
            break;

        default:
            TRAP;
    }
}

// /////////////////////////////////////////////////////////////////////////////
// SymHeapUnion implementation
namespace {
    bool checkNonPosValues(int a, int b) {
        if (0 < a && 0 < b)
            // we'll need to properly compare positive values
            return false;

        // non-positive value always have to match, bail out otherwise
        return a != b;
    }

    template <class TSubst>
    bool matchValues(TSubst &subst, int v1, int v2) {
        if (checkNonPosValues(v1, v2))
            // null vs. non-null, etc.
            return false;

        typename TSubst::iterator iter = subst.find(v1);
        if (iter != subst.end())
            // substitution already defined, check if it applies seamlessly
            return iter->second == v2;

        // define a new substitution
        subst[v1] = v2;
        return true;
    }
}

namespace SymbolicHeap {
    template <class TStack, class TSubst>
    bool dfsCmp(TStack &todo,
                TSubst &valSubst,
                const SymHeap &heap1,
                const SymHeap &heap2)
    {
        // FIXME: not very efficient implementation of DFS
        std::set<int> done;

        // DFS loop
        while (!todo.empty()) {
            int value1, value2;
            boost::tie(value1, value2) = todo.top();
            todo.pop();
            done.insert(value1);

            // TODO: distinguish among SLS and single dynamic variables here
            const int obj1 = heap1.pointsTo(value1);
            const int obj2 = heap2.pointsTo(value2);
            if (checkNonPosValues(obj1, obj2))
                // variable mismatch
                return false;

            // TODO: here handle structured variables
            value1 = heap1.valueOf(obj1);
            value2 = heap2.valueOf(obj2);
            if (!matchValues(valSubst, value1, value2))
                // value mismatch
                return false;

            if (!hasKey(done, value1))
                // schedule values for next wheel
                todo.push(value1, value2);
        }

        // heaps are equal (isomorphism)
        return true;
    }

    bool operator== (const SymHeap &heap1, const SymHeap &heap2) {
        // DFS stack
        typedef std::pair<int, int> TValuePair;
        typedef std::stack<TValuePair> TValueStack;
        TValueStack dfsStack;

        // value substitution (isomorphism)
        typedef std::map<int, int> TSubst;
        TSubst valSubst;

        // NOTE: we do not check cVars themselves among heaps
        // they are *supposed* to be the same
        SymHeap::TCont cVars;
        heap1.gatherCVars(cVars);
        BOOST_FOREACH(int uid, cVars) {
            const int var1 = heap1.varByCVar(uid);
            const int var2 = heap2.varByCVar(uid);
            if (var1 < 0 || var2 < 0)
                // heap corruption detected
                TRAP;

            // retrieve values of static variables
            const int value1 = heap1.valueOf(var1);
            const int value2 = heap2.valueOf(var2);
            if (!matchValues(valSubst, value1, value2))
                // value mismatch, bail out now
                return false;

            // schedule for DFS
            dfsStack.push(value1, value2);
        }

        // bad luck, we need to run DFS
        return dfsCmp(dfsStack, valSubst, heap1, heap2);
    }
}

void SymHeapUnion::insert(const SymbolicHeap::SymHeap &heap) {
    using SymbolicHeap::SymHeap;

    // FIXME: not very efficient implementation of union :-)
    // TODO: implement the container as either hash or tree data structure
    BOOST_FOREACH(const SymHeap &current, heaps_) {
        // TODO: check for entailment instead
        if (heap == current)
            return;
    }

    // add given heap to union
    heaps_.push_back(heap);
}

// /////////////////////////////////////////////////////////////////////////////
// SymExec implementation
struct SymExec::Private {
    CodeStorage::Storage        &stor;
    const CodeStorage::Fnc      *fnc;
    const CodeStorage::Block    *bb;
    LocationWriter              lw;
    TStateMap                   state;
    TBlockSet                   todo;

    Private(CodeStorage::Storage &stor_):
        stor(stor_)
    {
    }

    void updateState(const CodeStorage::Block *ofBlock,
                     const SymbolicHeap::SymHeap &heap);
    void execTermInsn(const CodeStorage::Insn &insn,
                      const SymbolicHeap::SymHeap &heap);
    void execBb();
    void execFncBody();
    void execFnc();
};

SymExec::SymExec(CodeStorage::Storage &stor):
    d(new Private(stor))
{
}

SymExec::~SymExec() {
    delete d;
}

void SymExec::Private::updateState(const CodeStorage::Block *ofBlock,
                                   const SymbolicHeap::SymHeap &heap)
{
    // update *target* state
    SymHeapUnion &huni = this->state[ofBlock];
    const size_t last = huni.size();
    huni.insert(heap);

    // check if anything has changed
    if (huni.size() != last)

        // schedule for next wheel
        todo.insert(ofBlock);
}
        
void SymExec::Private::execTermInsn(const CodeStorage::Insn &insn,
                                    const SymbolicHeap::SymHeap &heap)
{
    const CodeStorage::TTargetList &tlist = insn.targets;

    const enum cl_insn_e code = insn.code;
    switch (code) {
        case CL_INSN_RET:
            CL_MSG_STREAM(cl_warn, LocationWriter(&insn.loc)
                    << "warning: return statement ignored [not implemented]");
            break;

        case CL_INSN_JMP:
            if (1 == tlist.size()) {
                this->updateState(tlist[0], heap);
                break;
            }
            // go through!

        default:
            TRAP;
    }
}

void SymExec::Private::execBb() {
    using namespace CodeStorage;
    using SymbolicHeap::SymHeap;

    // some debugging stuff
    int bbCnt = 0;
    const std::string &name = bb->name();
    CL_MSG_STREAM(cl_debug, lw << "debug: >>> entering " << name << "...");

    // FIXME: we simply copy whole container to avoid its damage by inserting
    // during traversal ... that's really awkward due to performance
    SymHeapUnion huni(this->state[this->bb]);

    // go through all symbolic heaps corresponding to entry of this BB
    BOOST_FOREACH(const SymHeap &heap, huni) {
        CL_MSG_STREAM(cl_debug, this->lw << "debug: *** processing heap #"
                << (++bbCnt) << " of BB " << name << "...");

        // TODO: COW semantic
        SymHeap workingHeap(heap);
        SymHeapProcessor proc(workingHeap);

        // go through all BB insns
        BOOST_FOREACH(const Insn *insn, *bb) {
            if (0 < insn->loc.line)
                // update location info
                this->lw = &insn->loc;

            if (cl_is_term_insn(insn->code))
                // terminal insn
                this->execTermInsn(*insn, workingHeap);
            else
                // non-terminal insn
                proc.exec(*insn);
        }
    }
}

void SymExec::Private::execFncBody() {
    if (!this->todo.empty())
        // not implemented yet
        TRAP;

    // start with Fnc entry
    this->todo.insert(this->bb);

    // main loop
    while (!todo.empty()) {
        // FIXME: take BBs in some reasonable order instead
        TBlockSet::iterator i = this->todo.begin();
        this->bb = *i;
        this->todo.erase(i);

        this->execBb();
    }

    CL_DEBUG("execFncBody(): main loop terminated correctly...");
}

void SymExec::Private::execFnc() {
    using namespace CodeStorage;
    using SymbolicHeap::SymHeap;

    // create initial state for called function
    // TODO: handle fnc args somehow
    SymHeap init;
    BOOST_FOREACH(const Var &var, fnc->vars) {
        CL_DEBUG("--- creating stack variable: #" << var.uid
                << " (" << var.name << ")" );
        init.varCreate(var.clt, var.uid);
    }

    // insert initial state to the corresponding union
    SymHeapUnion &huni = this->state[this->bb];
    huni.insert(init);

    this->execFncBody();
}

void SymExec::exec(const CodeStorage::Fnc &fnc) {
    using namespace CodeStorage;
    using SymbolicHeap::SymHeap;

    d->fnc = &fnc;
    d->lw = &fnc.def.loc;

    CL_MSG_STREAM(cl_debug, d->lw << "debug: >>> entering "
            << nameOf(fnc) << "()...");

    CL_DEBUG("looking for entry block...");
    const ControlFlow &cfg = fnc.cfg;
    d->bb = cfg.entry();
    if (d->bb) {
        // we are indeed ready to execute the function
        d->execFnc();
        return;
    }

    CL_MSG_STREAM(cl_error, d->lw << "error: "
            << nameOf(fnc) << ": "
            << "entry block not found");
}
