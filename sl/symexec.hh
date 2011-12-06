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

#ifndef H_GUARD_SYM_EXEC_H
#define H_GUARD_SYM_EXEC_H

#include <string>

/**
 * @file symexec.hh
 * SymExec - top level algorithm of the @b symbolic @b execution
 */

class SymHeap;
class SymState;

namespace CodeStorage {
    struct Fnc;
    struct Storage;
}

struct SymExecParams {
    bool trackUninit;       ///< enable/disable @b track_uninit @b mode
    bool oomSimulation;     ///< enable/disable @b oom @b simulation mode
    bool skipPlot;          ///< simply ignore all ___sl_plot* calls
    bool ptrace;            ///< enable path tracing (a bit chatty)
    std::string errLabel;   ///< if not empty, treat reaching the label as error

    SymExecParams():
        trackUninit(false),
        oomSimulation(false),
        skipPlot(false),
        ptrace(false)
    {
    }
};

void execute(
        SymState                        &results,
        const SymHeap                   &entry,
        const CodeStorage::Fnc          &fnc,
        const SymExecParams             &ep);

#endif /* H_GUARD_SYM_EXEC_H */
