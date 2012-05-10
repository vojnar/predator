/*
 * Copyright (C) 2009-2010 Kamil Dudka <kdudka@redhat.com>
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

#include <cl/easy.hh>
#include <cl/cl_msg.hh>
#include <cl/clutil.hh>
#include <cl/storage.hh>

#include "memdebug.hh"
#include "symbt.hh"
#include "symdump.hh"
#include "symexec.hh"
#include "symproc.hh"
#include "symstate.hh"
#include "symtrace.hh"
#include "util.hh"

#include <string>

#include <boost/foreach.hpp>

// required by the gcc plug-in API
extern "C" { int plugin_is_GPL_compatible; }

// FIXME: the implementation is amusing
void parseConfigString(SymExecParams &sep, std::string cnf) {
    using std::string;
    if (cnf.empty())
        return;

    if (string("oom") == cnf) {
        CL_DEBUG("parseConfigString: \"OOM simulation\" mode requested");
        sep.oomSimulation = true;
        return;
    }

    if (string("track_uninit") == cnf) {
        CL_DEBUG("parseConfigString: \"track_uninit\" mode requested");
        sep.trackUninit = true;
        return;
    }

    // TODO: make it possible to handle both parameters together (comma
    // separated list or whatever)
    // TODO: document all the parameters somewhere
    if (string("noplot") == cnf) {
        CL_DEBUG("parseConfigString: \"noplot\" mode requested");
        sep.skipPlot = true;
        return;
    }

    if (string("ptrace") == cnf) {
        CL_DEBUG("parseConfigString: \"ptrace\" mode requested");
        sep.ptrace = true;
        return;
    }

    const char *cstr = cnf.c_str();
    const char *elPrefix = "error_label:";
    const size_t elPrefixLen = strlen(elPrefix);
    if (!strncmp(cstr, elPrefix, elPrefixLen)) {
        cstr += elPrefixLen;
        CL_DEBUG("parseConfigString: error label is \"" << cstr << "\"");
        sep.errLabel = cstr;
        return;
    }

    CL_WARN("unhandled config string: \"" << cnf << "\"");
}

void digGlJunk(SymHeap &sh) {
    using namespace CodeStorage;
    TStorRef stor = sh.stor();
    SymBackTrace bt(stor);
    SymProc proc(sh, &bt);

    TValList glVars;
    sh.gatherRootObjects(glVars, isProgramVar);
    BOOST_FOREACH(const TValId root, glVars) {
        // ensure we are dealing with a gl variable
        const CVar cv(sh.cVarByRoot(root));
        CL_BREAK_IF(cv.inst);

        // dig var identity and location info
        const struct cl_loc *loc = 0;
        std::string varString = varToString(stor, cv.uid, &loc);
        CL_DEBUG_MSG(loc, "(g) destroying gl variable: " << varString);

        // destroy the junk if needed
        proc.setLocation(loc);
        proc.valDestroyTarget(root);
    }
}

void execFnc(const CodeStorage::Fnc &fnc, const SymExecParams &ep,
             bool lookForGlJunk = false)
{
    const CodeStorage::Storage &stor = *fnc.stor;
    const struct cl_loc *lw = locationOf(fnc);
    CL_DEBUG_MSG(lw, "creating fresh initial state for "
            << nameOf(fnc) << "()...");

    Trace::RootNode *traceRoot = new Trace::RootNode(&fnc);

    // run the symbolic execution
    SymStateWithJoin results;
    execute(results, SymHeap(stor, traceRoot), fnc, ep);
    if (!lookForGlJunk)
        return;

    CL_DEBUG_MSG(lw, "(g) looking for gl junk...");
    const unsigned cnt = results.size();

    unsigned i = 0;
    BOOST_FOREACH(SymHeap *sh, results) {
        if (1 < cnt) {
            CL_DEBUG("*** destroying gl variables in heap #"
                    << (i++) << " of " << cnt << " heaps total");
        }

        digGlJunk(*sh);
    }
}

void execVirtualRoots(const CodeStorage::Storage &stor, const SymExecParams &ep)
{
    namespace CG = CodeStorage::CallGraph;

    // go through all root nodes
    const CG::Graph &cg = stor.callGraph;
    BOOST_FOREACH(const CG::Node *node, cg.roots) {
        const CodeStorage::Fnc &fnc = *node->fnc;
        CL_BREAK_IF(!isDefined(fnc));

        const struct cl_loc *lw = locationOf(fnc);
        CL_DEBUG_MSG(lw, nameOf(fnc)
                << "() is defined, but not called from anywhere");

        // perform symbolic execution for a virtual root
        execFnc(fnc, ep);
        printMemUsage("execFnc");
    }
}

void launchSymExec(const CodeStorage::Storage &stor, const SymExecParams &ep) {
    using namespace CodeStorage;

    // look for main() by name
    CL_DEBUG("looking for 'main()' at gl scope...");
    const NameDb::TNameMap &glNames = stor.fncNames.glNames;
    const NameDb::TNameMap::const_iterator iter = glNames.find("main");
    if (glNames.end() == iter) {
        CL_WARN("main() not found at global scope");
        execVirtualRoots(stor, ep);
        return;
    }

    // look for definition of main()
    const FncDb &fncs = stor.fncs;
    const Fnc *main = fncs[iter->second];
    if (!main || !isDefined(*main)) {
        CL_WARN("main() not defined");
        execVirtualRoots(stor, ep);
        return;
    }

    // just execute the main() function
    execFnc(*main, ep, /* lookForGlJunk */ true);
    printMemUsage("execFnc");
}

// /////////////////////////////////////////////////////////////////////////////
// see easy.hh for details
void clEasyRun(const CodeStorage::Storage &stor, const char *configString) {
    // read parameters of symbolic execution
    SymExecParams ep;
    parseConfigString(ep, configString);

    // run symbolic execution
    launchSymExec(stor, ep);

    if (Trace::Globals::alive()) {
        // plot all pending trace graphs
        Trace::GraphProxy *glProxy = Trace::Globals::instance()->glProxy();
        glProxy->plotAll();

        // kill Trace::Globals, which may trigger the final trace graph cleanup
        Trace::Globals::cleanup();
        printMemUsage("Trace::Globals::cleanup");
    }

    printPeakMemUsage();
}
