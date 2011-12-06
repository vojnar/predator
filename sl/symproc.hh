/*
 * Copyright (C) 2009-2011 Kamil Dudka <kdudka@redhat.com>
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

#ifndef H_GUARD_SYM_PROC_H
#define H_GUARD_SYM_PROC_H

/**
 * @file symproc.hh
 * SymProc - a layer on top of SymHeap, providing some higher-level
 * operations
 */

#include "config.h"

#include <cl/storage.hh>

#include "symbt.hh"
#include "symid.hh"
#include "symheap.hh"

class SymBackTrace;
class SymState;

struct CmpOpTraits {
    bool negative;
    bool preserveEq;
    bool preserveNeq;
    bool leftToRight;
    bool rightToLeft;
};

bool describeCmpOp(CmpOpTraits *pTraits, const enum cl_binop_e code);

TValId compareValues(
        SymHeap                     &sh,
        const enum cl_binop_e       code,
        const TObjType              clt,
        const TValId                v1,
        const TValId                v2);

bool reflectCmpResult(
        SymHeap                     &sh,
        const enum cl_binop_e       code,
        const bool                  branch,
        const TValId                v1,
        const TValId                v2);

/**
 * a layer on top of SymHeap, providing some higher-level operations
 */
class SymProc {
    public:
        /**
         * creation of the symbolic heap processor is a really cheap operation
         * @param heap an instance of SymHeap to operate on
         * @param bt an instance of symbolic backtrace used to distinguish among
         * instances of automatic variables and to print backtraces when
         * necessary/suitable
         */
        SymProc(SymHeap &heap, const SymBackTrace *bt):
            sh_(heap),
            bt_(bt),
            lw_(0),
            errorDetected_(false)
        {
        }

        SymHeap&                    sh() { return sh_; }
        const SymBackTrace*         bt() { return bt_; }
        const struct cl_loc*        lw() { return lw_; }

        /**
         * update location info
         * @note this method is used to provide as accurate as possible location
         * info in error/warning messages
         * @param lw where to retrieve the location info from
         */
        void setLocation(const struct cl_loc *lw) {
            lw_ = lw;
        }

    public:
        /// obtain a heap object corresponding to the given operand
        ObjHandle objByOperand(const struct cl_operand &op);

        /// obtain a heap value corresponding to the given operand
        TValId valFromOperand(const struct cl_operand &op);

        /// resolve Fnc uid from the given operand, return true on success
        bool fncFromOperand(int *pUid, const struct cl_operand &op);

        /// high-level interface to SymHeap::objSetValue()
        void objSetValue(const ObjHandle &lhs, TValId rhs);

        /// high-level interface to SymHeap::valDestroyTarget()
        void valDestroyTarget(TValId at);

        /// invalidate all variables that are killed by the given instruction
        void killInsn(const CodeStorage::Insn &);

        /// invalidate all variables killed by the given instruction per target
        void killPerTarget(const CodeStorage::Insn &, unsigned target);

        /// check whether we can safely access sizeOfTarget at the given address
        bool checkForInvalidDeref(TValId val, const TSizeOf sizeOfTarget);

        /// print backtrace and update the current error level correspondingly
        void printBackTrace(EMsgLevel level, bool forcePtrace = false);

        /// if true, the current state is not going to be inserted into dst
        bool hasFatalError() const;

    protected:
        TValId varAt(const CVar &cv);
        TValId varAt(const struct cl_operand &op);
        TValId targetAt(const struct cl_operand &op);
        virtual void varInit(TValId at);
        friend void initGlVar(SymHeap &sh, const CVar &cv);

    private:
        TValId valFromObj(const struct cl_operand &op);
        TValId valFromCst(const struct cl_operand &op);
        void killVar(const CodeStorage::KillVar &kv);

    protected:
        SymHeap                     &sh_;
        const SymBackTrace          *bt_;
        const struct cl_loc         *lw_;
        bool                         errorDetected_;
};

/// @todo make the API more generic and better documented
void describeUnknownVal(
        SymProc                     &proc,
        const TValId                 val,
        const char                  *action);

void executeMemset(
        SymProc                     &proc,
        const TValId                 addr,
        const TValId                 valToWrite,
        const TValId                 valSize);

struct SymExecCoreParams {
    bool trackUninit;       ///< enable/disable @b track_uninit @b mode
    bool oomSimulation;     ///< enable/disable @b oom @b simulation mode
    bool skipPlot;          ///< simply ignore all ___sl_plot* calls
    bool skipVarInit;       ///< used internally
    std::string errLabel;   ///< if not empty, treat reaching the label as error

    SymExecCoreParams():
        trackUninit(false),
        oomSimulation(false),
        skipPlot(false),
        skipVarInit(false)
    {
    }
};

/// extension of SymProc, now only used by SymExecEngine::execNontermInsn()
class SymExecCore: public SymProc {
    public:
        /**
         * @copydoc SymProc::SymProc
         * @param ep execution parameters - see SymExecCoreParams for details
         */
        SymExecCore(SymHeap &heap, const SymBackTrace *bt,
                    const SymExecCoreParams &ep):
            SymProc(heap, bt),
            ep_(ep)
        {
        }

        const SymExecCoreParams& params() const { return ep_; }

    public:
        /**
         * execute a @b non-terminal instruction using the managed symbolic heap
         * @note see also CodeStorage::Insn
         * @note see also code_listener.h::cl_is_term_insn()
         * @param dst a container to store the result(s) to
         * @param insn an instruction to be executed
         * @note returning false in this case does @b not mean there has been an
         * error
         * @return true, if the requested instruction has been processed; false
         * if the instruction has to be processed elsewhere (usually
         * CL_INSN_CALL)
         */
        bool exec(SymState &dst, const CodeStorage::Insn &insn);

        void execHeapAlloc(SymState &dst, const CodeStorage::Insn &,
                           const TSizeOf size, const bool nullified);

        void execFree(TValId val);

    private:
        template <int ARITY>
        void execOp(const CodeStorage::Insn &insn);

        template <class TDerefs>
        bool concretizeLoop(SymState &dst, const CodeStorage::Insn &insn,
                            const TDerefs &derefs);

        void handleLabel(const CodeStorage::Insn &);

        bool execCore(SymState &dst, const CodeStorage::Insn &insn);

    protected:
        virtual void varInit(TValId at);

    private:
        const SymExecCoreParams ep_;
};

#endif /* H_GUARD_SYM_PROC_H */
