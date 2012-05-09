/*
 * Copyright (C) 2010 Jiri Simacek
 *
 * This file is part of forester.
 *
 * forester is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * any later version.
 *
 * forester is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with forester.  If not, see <http://www.gnu.org/licenses/>.
 */

// Standard library headers
#include <sstream>
#include <vector>
#include <list>
#include <set>
#include <algorithm>

// Code Listener headers
#include <cl/code_listener.h>
#include <cl/cl_msg.hh>
#include <cl/cldebug.hh>
#include <cl/clutil.hh>
#include <cl/storage.hh>
#include "../cl/ssd.h"

// Forester headers
#include "forestautext.hh"
#include "symctx.hh"
#include "executionmanager.hh"
#include "fixpointinstruction.hh"
#include "regdef.hh"
#include "restart_request.hh"
#include "symexec.hh"
#include "virtualmachine.hh"

using namespace ssd;
using std::vector;
using std::list;
using std::set;

#if 0
void dumpOperandTypes(std::ostream& os, const cl_operand* op) {
	os << "operand:" << std::endl;
	cltToStream(os, op->type, false);
	os << "accessors:" << std::endl;
	const cl_accessor* acc = op->accessor;
	while (acc) {
		cltToStream(os, acc->type, false);
		acc = acc->next;
	}
}
#endif

class SymExec::Engine {

	TA<label_type>::Backend taBackend;
	TA<label_type>::Backend fixpointBackend;
	BoxMan boxMan;

#if 0
	std::vector<const Box*> boxes;
	std::vector<const Box*> basicBoxes;
	boost::unordered_map<const Box*, std::vector<const Box*> > hierarchy;
#endif

	Compiler compiler_;
	Compiler::Assembly assembly_;

	ExecutionManager execMan;

	bool dbgFlag;

	std::vector<std::string> vars;

protected:

#if 0
	bool foldBox(SymState* target, FAE& fae, size_t root, const Box* box) {
		CL_CDEBUG("trying " << *(const AbstractBox*)box << " at " << root);
		if (!fae.foldBox(root, box))
			return false;
		CL_CDEBUG("match");
		std::set<size_t> tmp;
		fae.getNearbyReferences(fae.varGet(ABP_INDEX).d_ref.root, tmp);
		FAE::NormInfo normInfo;
		fae.normalize(normInfo, tmp);
		boost::unordered_map<const Box*, std::vector<const Box*> >::iterator i =
			this->hierarchy.find(box);
		if (i == this->hierarchy.end())
			return true;
		this->recAbstractAndFold(target, fae, i->second);
		return true;
	}

	void recAbstractAndFold(SymState* target, FAE& fae, const std::vector<const Box*>& boxes) {

		CL_CDEBUG("abstracting and folding ... " << target->absHeight);
//		fae.heightAbstraction(target->absHeight, ExactLabelMatchF());
		CL_CDEBUG(std::endl << fae);

		// do not fold at 0
		for (size_t i = 1; i < fae.getRootCount(); ++i) {
			fae.heightAbstraction(i, target->absHeight, ExactLabelMatchF());
			for (std::vector<const Box*>::const_iterator j = boxes.begin(); j != boxes.end(); ++j) {
				if (this->foldBox(target, fae, i, *j))
					i = 1;
			}
		}

	}
	struct InvalidateF {

		list<SymState*>& queue;
		set<CfgStateExt*>& s;

		InvalidateF(list<SymState*>& queue, set<CfgStateExt*>& s) : queue(queue), s(s) {}

		void operator()(SymState* state) {
			CfgState* cfgState = CFG_FROM_FAE(*state->fae);
			if (state->queueTag != this->queue.end())
				this->queue.erase(state->queueTag);
//			state->invalidate(this->queue, node->fae);
			if (cfgState->hasExt)
				s.insert((CfgStateExt*)cfgState);
		}

	};

	void processState(SymState* state) {

		assert(state);

		CfgState* cfgState = CFG_FROM_FAE(*state->fae);

		if (cfgState->hasExt && ((CfgStateExt*)cfgState)->testInclusion(*state->fae)) {

			++this->tracesEvaluated;

			CL_CDEBUG("hit");

			this->traceRecorder.destroyBranch(state, DestroySimpleF());

			return;

		}

		state->queueTag = this->queue.end();

		try {

			const cl_loc& loc = (*cfgState->insn)->loc;

			CL_CDEBUG(loc << ' ' << **cfgState->insn);
			CL_CDEBUG("preprocessing " << state);
			CL_CDEBUG(std::endl << SymCtx::Dump(*cfgState->ctx, *state->fae));
			CL_CDEBUG(std::endl << *state->fae);

			std::vector<FAE*> tmp;

			ContainerGuard<std::vector<FAE*> > g(tmp);

			cfgState->prepareOperands(tmp, *state->fae);

			for (FAE*& fae : tmp) {

				ExecInfo info(state, cfgState, fae);

				this->processState(info);

				fae = NULL;

			}

			g.release();

		} catch (const ProgramError& e) {

			CL_CDEBUG(e.what());

			this->printTrace(state);

			throw;

			TraceRecorder::Item* item = this->revRun(*fae);

			if (!item)

				throw ProgramError(e.what(), &(*state->insn)->loc);

			CL_DEBUG("spurious counter example ...");

			this->printTrace(*fae);

			throw;

			state = STATE_FROM_FAE(*item->fae);

			assert(state->entryPoint);

			set<SymState*> s;

			this->traceRecorder.invalidateChildren(item, InvalidateF(this->queue, s));

			const FAE* tmp2 = item->fae;

			TraceRecorder::Item* parent = item->parent;

			InvalidateF(this->queue, s)(item);

			this->traceRecorder.remove(tmp2);

			assert(parent);

			parent->removeChild(item);

			for (set<SymState*>::iterator i = s.begin(); i != s.end(); ++i) {
				(*i)->recompute();
				CL_CDEBUG("new fixpoint:" << std::endl << (*i)->fwdConf);
			}

			const cl_loc& loc = (*state->insn)->loc;

			CL_CDEBUG("adjusting abstraction ... " << ++state->absHeight);
			CL_CDEBUG("resuming execution ... ");
			CL_CDEBUG(loc << ' ' << **state->insn);

			parent->queueTag = this->queue.insert(this->queue.end(), parent->fae);

		}

	}

	void printInfo(SymState* state) {
		if (this->dbgFlag) {
			CfgState* cfgState = CFG_FROM_FAE(*state->fae);
			assert(cfgState);
			if (!cfgState->hasExt)
				return;
			CL_DEBUG(std::endl << SymCtx::Dump(*((CfgStateExt*)cfgState)->ctx, *state->fae));
			CL_DEBUG(std::endl << *state->fae);
			CL_DEBUG("evaluated states: " << this->statesEvaluated << ", evaluated traces: " << this->tracesEvaluated);
			this->dbgFlag = false;
		}
	}
#endif
#if 0
	TraceRecorder::Item* revRun(const FAE& fae) {

		CL_CDEBUG("reconstructing abstract trace ...");

		vector<pair<const FAE*, const CodeStorage::Insn*> > trace;

		TraceRecorder::Item* item = this->traceRecorder.find(&fae);

		FAE tmp(fae);

		SymState* state = NULL;

		while (item->parent) {

			CL_CDEBUG(std::endl << SymCtx::Dump(*STATE_FROM_FAE(*item->fae)->ctx, *item->fae));
			CL_CDEBUG(std::endl << tmp);

			state = STATE_FROM_FAE(*item->parent->fae);

			CL_CDEBUG("rewinding " << (*state->insn)->loc << ' ' << **state->insn);

			switch (item->itemType) {

				case tr_item_type::itDenormalize: {

					CL_CDEBUG("denormalizing " << std::endl << tmp << "with" << std::endl << *item->fae);
					CL_CDEBUG(item->normInfo);

					if (!Normalization(tmp).denormalize(*item->fae, item->normInfo)) {
						CL_CDEBUG("spurious counter example (denormalization)!" << std::endl << *item->fae);
						return item;
					}

					break;

				}

				case tr_item_type::itReverse: {

					CL_CDEBUG("reversing " << std::endl << tmp << "with" << std::endl << *item->parent->fae);

					if (!ReverseRun(tmp).reverse(*item->parent->fae)) {
						CL_CDEBUG("spurious counter example (reversal)!" << std::endl << *item->parent->fae);
						return item;
					}

					NormInfo normInfo;

					VirtualMachine vm(tmp);

					std::set<size_t> s;
					vm.getNearbyReferences(vm.varGet(ABP_INDEX).d_ref.root, s);
					Normalization(tmp).normalize(normInfo, s);

					break;

				}

			}

			if (item->itemType == tr_item_type::itDenormalize)
				trace.push_back(make_pair(item->fae, *state->insn));

			item = item->parent;

		}

		assert(state);

//		trace.push_back(make_pair(item->fae, *state->insn));

		CL_CDEBUG("trace:");

		for (vector<pair<const FAE*, const CodeStorage::Insn*> >::reverse_iterator i = trace.rbegin(); i != trace.rend(); ++i) {
			if (i->second)
				CL_NOTE_MSG(&i->second->loc, *(i->second));
//			STATE_FROM_FAE(*i->first)->ctx->dumpContext(*i->first);
//			CL_CDEBUG(std::endl << *(i->first));
		}

		CL_NOTE_MSG(&this->currentInsn->loc, *this->currentInsn);

		return NULL;

	}
#endif
#if 0
	void printQueue() const {
		for (SymState* state : this->queue)
			std::cerr << *state->fae;
	}
#endif

	static void getStatus(SymState* state, ExecutionManager& execMan, string& status)
	{
		status = "unknown";
		std::ostringstream ss;
		ss << state->instr->insn();

		for (size_t i = 0; i < execMan.condQueue_.size(); ++i)
		{
			if(execMan.condQueue_.at(i).first == state)
			{
				status =  execMan.condQueue_.at(i).second;
			}
		}
	}

	static void getAbsTA(SymState* state, ExecutionManager& execMan,
		std::vector<FAE>& absFaes, int& status)
	{
		status = 0;
		absFaes.clear();

		for (size_t i = 0; i < execMan.absQueue_.size(); i++)
		{
			if (execMan.absQueue_.at(i).first == state)
			{
				status = 1;
				absFaes = execMan.absQueue_.at(i).second;
			}
		}
	}

	static void getAbsTrace(AbstractInstruction::StateType state,
		std::vector<std::vector<FAE>>& absTrace)
	{
		SymState* s = state.second;
		string ss1 = "";
		std::ostringstream ss;
		absTrace.clear();
		std::vector<SymState*> trace;

		for ( ; s; s = s->parent)
		{
			trace.push_back(s);
		}

		std::reverse(trace.begin(), trace.end());

		for (size_t i = 0; i < trace.size()-1; i++)
		{
			if (trace.at(i)->instr->insn())
			{
				std::cerr << "     " << *trace.at(i)->instr->insn() << "-------"
					<< *trace.at(i)->instr << std::endl;
			}
		}
	}

	static void getCondTrace(AbstractInstruction::StateType state,
		std::vector<string>& condTrace, ExecutionManager& execMan)
	{
		SymState* s = state.second;
		for ( ; s; s = s->parent)
		{
			string status;
			getStatus(s,execMan,status);
			if (s->instr->insn())
			{
				std::ostringstream ss;
				ss << *s->instr->insn();

				if (status.find("unknown") == string::npos
					&& ss.str().find("if") != string::npos)
				{
					condTrace.push_back(status);
				}
			}
		}

		std::reverse(condTrace.begin(), condTrace.end());
	}

	/**
	 * @brief  Prints a trace of preceding symbolic states
	 *
	 * This static method prints the backtrace from the given symbolic state to
	 * the initial state.
	 *
	 * @param[in]  state  The state for which the backtrace is desired
	 */
	static void printTrace(const AbstractInstruction::StateType& state,
		std::vector<pair<FAE,string>>& statements)
	{
		SymState* s = state.second;

		std::vector<SymState*> trace;

		statements = {};
		int size = 0;

		for ( ; s; s = s->parent)
		{	// until we reach the initial state of the execution tree
			trace.push_back(s);
		}

		// invert the trace so that it is in the natural order
		std::reverse(trace.begin(), trace.end());

		CL_NOTE("trace:");

		for (auto s : trace)
		{	// print out the trace
			if (s->instr->insn())
			{
//				CL_NOTE_MSG(&s->instr->insn()->loc,
//					SSD_INLINE_COLOR(C_LIGHT_RED, *s->instr->insn()));
//				CL_DEBUG_AT(2, std::endl << *s->fae);
				std::stringstream ss, ss2, ss1;
				ss2 << *s->instr;
				if (ss2.str().find("abs") != string::npos)
				{
					ss << *s->instr->insn() << "--abs";
				}
				else
				{
					ss << *s->instr->insn();
				}

				ss1 << *s->fae;
				statements.push_back(pair<FAE,string>(*s->fae,ss.str()));
				size++;
			}

			CL_DEBUG_AT(2, *s->instr);
		}
	}

	static size_t sizeTrace(const AbstractInstruction::StateType state)
	{
		SymState* s = state.second;
		size_t size = 0;
		for ( ; s; s = s->parent)
		{
			if (s->instr->insn())
			{
				size++;
			}
		}

		return size;
	}


	static void printTrace2(std::vector<pair<FAE,string>> statements)
	{
		CL_NOTE("trace:");
		int size = 0;
		for (size_t i = 0; i < statements.size(); i++)
		{
			if (statements.at(i).second.find("deleted") == string::npos)
			{
				std::cerr << statements.at(i).second << std::endl;
			}

			size++;
		}
	}

	static void refineStatements(std::vector<pair<FAE,string>>& instructions,
		std::vector<string> condTrace)
	{
		for (size_t i = 0; i < instructions.size(); i++)
		{
			if (i+2 < instructions.size())
			{
				if (instructions.at(i).second.find("nondet") != string::npos
					&& instructions.at(i+2).second.find("if")!=string::npos)
				{
					if(instructions.at(i).second.find("--abs") == string::npos)
					{
						instructions.at(i) = std::make_pair(instructions.at(i).first, "deleted");
					}

					instructions.at(i+1) = std::make_pair(instructions.at(i+1).first, "deleted");
					instructions.at(i+2) = std::make_pair(instructions.at(i+2).first, "Check (ND) "
						+ condTrace.at(i+3));

					continue;
				}
			}

			if (instructions.at(i).second.find("if") != string::npos)
			{
				int x = int(instructions.at(i).second.find("("));
				int y = int(instructions.at(i).second.find(")"));
				string z = instructions.at(i).second.substr(x+1, y-x - 1);
				string s = instructions.at(i).second.substr(y);
				string expression;

				if (instructions.at(i-1).second.find(z) != string::npos)
				{
					x = int(instructions.at(i-1).second.find("("));
					string exp;
					if (instructions.at(i-1).second.find("==") != string::npos)
					{
						y = int(instructions.at(i-1).second.find("=="));
						exp = "==";
					}
					if (instructions.at(i-1).second.find("<=") != string::npos)
					{
						y = int(instructions.at(i-1).second.find("<="));
						exp = "<=";
					}
					if(instructions.at(i-1).second.find("< ") != string::npos)
					{
						y = int(instructions.at(i-1).second.find("< "));
						exp = "< ";
					}
					if(instructions.at(i-1).second.find("!=") != string::npos)
					{
						y = int(instructions.at(i-1).second.find("!="));
						exp = "!=";
					}
					int t = int(instructions.at(i-1).second.find(")"));
					string left;
					string right;
					// for case of full expression
					if (instructions.at(i-1).second.substr(x,y-x).find(":") == string::npos
						&& instructions.at(i-1).second.substr(y,t-y).find(":")==string::npos
						&& instructions.at(i-1).second.substr(y,t-y).find("NULL")==string::npos)
					{
						if (instructions.at(i-3).second.find(instructions.at(i-1).second.substr(x+1,y-x-1)) != string::npos)
						{
							int x1 = int(instructions.at(i-3).second.find("="));
							left = instructions.at(i-3).second.substr(x1);
							if (left.find("#") != string::npos)
							{
								left = left.substr(int(left.find(":"))+1);
							}
							instructions.at(i-3) = std::make_pair(instructions.at(i-3).first, "deleted");
						}
						if (instructions.at(i-2).second.find(instructions.at(i-1).second.substr(y+3, t-y-3)) != string::npos)
						{
							int x2 = int(instructions.at(i-2).second.find("="));
							right = instructions.at(i-2).second.substr(x2);
							if (right.find("#") != string::npos)
							{
								right = right.substr(int(right.find(":"))+1);
							}
							instructions.at(i-2) = pair<FAE,string>(instructions.at(i-2).first, "deleted");
						}
						expression = left + exp + right;
						instructions.at(i) = std::make_pair(instructions.at(i).first,"Check (" + expression + ")" + condTrace.at(i+1));
						if (instructions.at(i-1).second.find("--abs") == string::npos)
						{
							instructions.at(i-1) = std::make_pair(instructions.at(i-1).first, "deleted");
						}
					}
					else
					{
						if (instructions.at(i-1).second.substr(x,y-x).find(":")==string::npos)
						{
							int x1 = int(instructions.at(i-2).second.find("="));
							left = instructions.at(i-2).second.substr(x1);
							if (left.find("#") != string::npos)
							{
								left = left.substr(int(left.find(":"))+1);
							}

							if (instructions.at(i-1).second.substr(y,t-y).find("NULL") == string::npos)
							{
								int x2 = int(instructions.at(i-1).second.find(":"));
								right = instructions.at(i-1).second.substr(x2+1,1);
							}
							else
							{
								right = "NULL";
							}

							expression = left + exp + right;
							instructions.at(i) = std::make_pair(instructions.at(i).first,
								"Check (" + expression + ")" + condTrace.at(i+1));

							instructions.at(i-2) = pair<FAE,string>(instructions.at(i-2).first, "deleted");
							if (instructions.at(i-1).second.find("--abs") == string::npos)
							{
								instructions.at(i-1) = std::make_pair(instructions.at(i-1).first, "deleted");
							}
						}
						else
						{
							if (instructions.at(i-1).second.substr(y,t-y).find(":")!=string::npos)
							{
								int x1 = int(instructions.at(i-1).second.substr(x,y-x).find(":"));
								left = instructions.at(i-1).second.substr(x,y-x).substr(x1+1,1);
								int x2 = int(instructions.at(i-1).second.substr(y,t-y).find(":"));
								right = instructions.at(i-1).second.substr(y,t-y).substr(x2+1,1);
								expression = left + exp + right;
								instructions.at(i) = std::make_pair(instructions.at(i).first,"Check (" + expression + ")"
										+ condTrace.at(i+1));
								if (instructions.at(i-1).second.find("--abs") == string::npos)
								{
									instructions.at(i-1) = std::make_pair(instructions.at(i-1).first, "deleted");
								}
							}
							else
							{
								int x1 = int(instructions.at(i-1).second.substr(x,y-x).find(":"));
								left = instructions.at(i-1).second.substr(x,y-x).substr(x1+1,1);
								right = "NULL";
								expression = left + exp + right;
								instructions.at(i) = std::make_pair(instructions.at(i).first,"Check (" + expression + ")"
										+ condTrace.at(i+1));
								if (instructions.at(i-1).second.find("--abs") == string::npos)
								{
									instructions.at(i-1) = std::make_pair(instructions.at(i-1).first, "deleted");
								}
							}
						}
					}
				}
			}

			if (instructions.at(i).second.find("malloc") != string::npos)
			{	// malloc
				instructions.at(i) = std::make_pair(instructions.at(i).first,"Node* "
					+ instructions.at(i).second.substr(int(instructions.at(i).second.find(":"))+1,1)
					+ " = New Node()");
			}
			else
			{	// assignment
				if (instructions.at(i).second.find("=")!=string::npos)
				{
					if (instructions.at(i).second.find(":")!=string::npos
						&& int(instructions.at(i).second.find("=")) > int(instructions.at(i).second.find(":")))
					{
						int x = int(instructions.at(i).second.find(":"));
						string first = instructions.at(i).second.substr(x+1);
						string left, right;
						if (first.find(":")!=string::npos)
						{
							int y = int(first.find(":"));
							int z = int(first.find("#"));
							left = first.substr(0,z);
							right = first.substr(y+1);
							instructions.at(i) = pair<FAE,string>(instructions.at(i).first,left + right);
						}
						else
						{
							instructions.at(i) = pair<FAE,string>(instructions.at(i).first,first);
						}
					}
				}
			}

			if (instructions.at(i).second.find("free") != string::npos)
			{	// free
				int x = int(instructions.at(i).second.find(":"));
				instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Free("
					+ instructions.at(i).second.substr(x+1,1) + ")");
			}
			if (instructions.at(i).second.find("(int)0") != string::npos
				&& instructions.at(i+1).second.find("return") != string::npos)
			{	// return
				instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"deleted");
				instructions.at(i+1) = pair<FAE,string>(instructions.at(i+1).first,"Return 0");
			}
			if (instructions.at(i).second.find("(int)1") != string::npos
				&& instructions.at(i+1).second.find("return") != string::npos)
			{
				instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"deleted");
				instructions.at(i+1) = pair<FAE,string>(instructions.at(i+1).first,"Return 1");
			}
		}

		for (size_t i = 0; i < instructions.size()-1; i++)
		{
			if (instructions.at(i).second.find("#") != string::npos)
			{
				int x,y;
				x = int(instructions.at(i).second.find("#"));
				y = int(instructions.at(i).second.find("="));
				string right = instructions.at(i).second.substr(x,y-x-1);
				if (instructions.at(i+1).second.find(right) != string::npos)
				{
					y = int(instructions.at(i).second.find(":"));
					right = instructions.at(i).second.substr(y+1);
					x = int(instructions.at(i+1).second.find(":"));
					y = int(instructions.at(i+1).second.find("="));
					string left = instructions.at(i+1).second.substr(0,y-1);
					instructions.at(i+1) = pair<FAE,string>(instructions.at(i+1).first,left
						+ "=" + right);
					instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"deleted");
				}
				for (size_t i = 0; i < instructions.size(); i++)
				{
					if (instructions.at(i).second.find(")--abs") != string::npos)
					{
						instructions.at(i) = pair<FAE,string>(instructions.at(i).first,"Abstraction");
					}
				}
			}
		}
	}


	/**
	 * @brief  Prints boxes
	 *
	 * Method that prints all boxes from the box manager.
	 */
	void printBoxes() const
	{
		std::vector<const Box*> boxes;

		this->boxMan.boxDatabase().asVector(boxes);

		std::map<std::string, const Box*> orderedBoxes;

		// reorder according to the name
		for (auto& box : boxes)
		{
			std::stringstream ss;

			ss << *(const AbstractBox*)box;

			orderedBoxes.insert(std::make_pair(ss.str(), box));
		}

		for (auto& nameBoxPair : orderedBoxes)
		{
			CL_DEBUG_AT(1, nameBoxPair.first << ':' << std::endl << *nameBoxPair.second);
		}
	}


	static void readStackFrame(const FAE& fae, std::vector<Data>& out)
	{
		out = {};
		VirtualMachine vm(fae);
		size_t root = vm.varGet(ABP_INDEX).d_ref.root;
		auto& t = fae.roots[root]->getAcceptingTransition();
		int n = 0;
		for (auto i = t.lhs().begin(); i != t.lhs().end(); ++i)
		{
			out.push_back(fae.getData(*i));
		}

		n++;
	}

	static void collectTA(std::vector<string>& ta, string& fae)
	{
		ta = {};

		while (fae.find("===") != string::npos)
		{
			int x = int(fae.find("==="));
			if (fae.substr(x+3).find("===") != string::npos)
			{
				int y = fae.substr(x+3).find("===");
				ta.push_back(fae.substr(x+3).substr(0,y));
				fae.assign(fae.substr(y));
			}
			else
			{
				ta.push_back(fae.substr(x+3));
				break;
			}
		}
	}

	static void printTAwithvariables(std::vector<Data> stack,
		std::vector<string> vars,std::vector<string>& ta)
	{
		for (size_t i = 2; i < stack.size(); i++)
		{
			std::stringstream ss,ss1;
			ss << stack.at(i);
			if (ss.str().find("(ref)") != string::npos)
			{
				int index = 0;
				std::stringstream os(ss.str().substr(5,1));
				os >> index;
				ss1 << vars.at(i-2);

				for(size_t j = 0; j < ta.size(); j++)
				{
					if (ta.at(j).find("root " + os.str())!=string::npos)
					{
						ta.at(j)= "var: [" +  ss1.str() + "]: " + "\n  |\n  v\n " + ta.at(j);
					}
				}
			}
		}
	}


	static void printAbsTAs(std::vector<FAE> absTrace, std::vector<string> vars)
	{
		std::vector<string> msg;
		for (int i = absTrace.size()-1; i >= 0; i--)
		{
			int z = absTrace.size() - 1- i;
			if((z % 2) == 0)
			{
				msg.push_back("After Abstraction");
			}
			else
			{
				msg.push_back("After Norminaze and Fold");
			}
		}

		std::reverse(msg.begin(), msg.end());
		std::vector<Data> out;
		std::vector<string> ta = {};
		for (size_t i = 0; i < absTrace.size(); i++)
		{
			string fae;
			std::stringstream ss;
			ss << absTrace.at(i);
			fae = ss.str();
			ta.clear();
			collectTA(ta,fae);
			readStackFrame(absTrace.at(i), out);
			printTAwithvariables(out,vars,ta);
			std::cerr << msg.at(i) << std::endl;
			for (size_t j = 0; j < ta.size(); j++)
			{
				std::cerr << ta.at(j) << std::endl;
			}
		}
	}

	static void printBoxes(std::vector<string>& boxes)
	{
		for (size_t i = 0; i < boxes.size(); i++)
		{
			std::cerr << boxes.at(i) << std::endl;
		}
	}

	static void printTATrace(std::vector<pair<FAE,string>>& statements,
		std::vector<string> vars, std::vector<std::vector<FAE>> absTrace,
		std::vector<std::vector<string>>& boxes)
	{
		int size = 0;
		std::vector<std::vector<Data>> stacklist = {};
		std::vector<Data> out;
		std::vector<string> ta = {};

		for (size_t i = 0; i < statements.size(); i++)
		{
			string fae;
			std::stringstream ss;
			ss << statements.at(i).first;
			fae = ss.str();
			ta.clear();
			Engine::collectTA(ta,fae);
			readStackFrame(statements.at(i).first, out);
			stacklist.push_back(out);
			printTAwithvariables(out,vars,ta);

			if (i>0 && statements.at(i-1).second.find("Abstraction") != string::npos)
			{
				if(statements.at(i).second.find("deleted") == string::npos)
				{
					std::cerr << "--------------------------------------------------------------------------------" << std::endl;
					std::cerr << statements.at(i).second << std::endl;
					std::cerr << "--------------------------------------------------------------------------------" << std::endl;
				}
				continue;
			}

			if (statements.at(i).second.find("Abstraction") != string::npos)
			{
				for (size_t j = 0; j < ta.size(); j++)
				{
					std::cerr << ta.at(j) << std::endl;
				}

				std::cerr << "--------------------------------------------------------------------------------" << std::endl;
				std::cerr << "Abstraction" << std::endl;
				std::cerr << "--------------------------------------------------------------------------------" << std::endl;
				printBoxes(boxes.at(i+1));
				printAbsTAs(absTrace.at(i+1),vars);
			}
			else if (
				(
					statements.at(i).second.find("deleted") == string::npos
					&& i > 0
					&& statements.at(i-1).second.find("deleted") == string::npos
				) ||
				(statements.at(i).second.find("deleted") == string::npos && i == 0))
			{
				for (size_t j = 0; j < ta.size(); j++)
				{
					std::cerr << ta.at(j) << std::endl;
				}

				std::cerr << "--------------------------------------------------------------------------------" << std::endl;
				std::cerr << statements.at(i).second << std::endl;
				std::cerr << "--------------------------------------------------------------------------------" << std::endl;
				size++;
			}
			else
			{
				if (i>0 && statements.at(i-1).second.find("deleted") == string::npos)
				{
					for (size_t j = 0; j < ta.size(); j++)
					{
						std::cerr << ta.at(j) << std::endl;
					}
				}

				if(i>0 && statements.at(i).second.find("deleted") == string::npos)
				{
					std::cerr << "--------------------------------------------------------------------------------" << std::endl;
					std::cerr << statements.at(i).second << std::endl;
					std::cerr << "--------------------------------------------------------------------------------" << std::endl;
				}
			}
		}
	}


	/**
	 * @brief  The main execution loop
	 *
	 * This method is the main execution loop for the symbolic execution. It
	 * assumes that the microcode is already compiled, etc.
	 */
	bool main()
	{
		CL_CDEBUG(2, "creating empty heap ...");

		// create an empty heap
		std::shared_ptr<FAE> fae = std::shared_ptr<FAE>(
			new FAE(this->taBackend, this->boxMan));

		CL_CDEBUG(2, "sheduling initial state ...");

		// schedule the initial state for processing
		this->execMan.init(
			std::vector<Data>(this->assembly_.regFileSize_, Data::createUndef()),
			fae,
			this->assembly_.code_.front()
		);

		AbstractInstruction::StateType state;

		std::vector<std::vector<pair<FAE,string>>> statelist = {};
		std::vector<std::vector<string>> condTraceList = {};
		std::vector<string> condTrace;
		std::vector<std::vector<std::vector<FAE>>> absTraceList;
		std::vector<std::vector<string>> boxTrace = {};
		std::vector<std::vector<std::vector<string>>> boxTraceList = {};
		std::vector<pair<std::vector<string>, string>> instructions = {};
		std::vector<pair<FAE,string>> statements;
		std::vector<Data> out;
		std::vector<string> ta = {};
		std::vector<std::vector<Data>> stacklist = {};
		std::vector<std::vector<FAE>> absTrace = {};

		try
		{	// expecting problems...
			std::string fae;
			AbstractInstruction::StateType laststate, oldstate;

			while (this->execMan.dequeueDFS(state))
			{	// process all states in the DFS order
				if (state.second->instr->insn())
				{	// in case current instruction IS an instruction
					string insn;
					std::ostringstream ss;
					ss << *state.second->instr->insn();
					insn = ss.str();
					ss << *state.second->fae;
					fae = ss.str();
					collectTA(ta,fae);

					VirtualMachine vm(*state.second->fae);
					if (sizeTrace(state) <= statements.size())
					{
						// add cond, abs, box trace into their lists
						absTrace.push_back(execMan.absFAEs_);
						execMan.absFAEs_.clear();
						absTraceList.push_back(absTrace);
						boxTrace.push_back(execMan.avaiBoxes_);
						execMan.avaiBoxes_.clear();
						boxTraceList.push_back(boxTrace);
						condTraceList.push_back(condTrace);
						statelist.push_back(statements);
						// Change condition trace, abs trace, box trace
						absTrace.erase(absTrace.begin() + sizeTrace(state) , absTrace.end());
						condTrace.erase(condTrace.begin() + sizeTrace(state) - 1, condTrace.end());
						boxTrace.erase(boxTrace.begin() + sizeTrace(state), boxTrace.end());
						Engine::printTrace(state, statements);
						condTrace.push_back(execMan.condStatus_);
						execMan.condStatus_ = "...";
					}
					else
					{
						Engine::printTrace(state, statements);
						// update cond, abs, box traces
						absTrace.push_back(execMan.absFAEs_);
						condTrace.push_back(execMan.condStatus_);
						boxTrace.push_back(execMan.avaiBoxes_);
						execMan.avaiBoxes_.clear();
						execMan.absFAEs_.clear();
						execMan.condStatus_ = "...";
					}
				}

				// run the state
				this->execMan.execute(state);
			}

			for (size_t i = 0; i < statelist.size(); i++)
			{
				refineStatements(statelist.at(i), condTraceList.at(i));
				Engine::printTrace2(statelist.at(i));
				Engine::printTATrace(statelist.at(i),vars,absTraceList.at(i),boxTraceList.at(i));
			}

			return true;
		}
		catch (ProgramError& e)
		{
			//  Engine::printTrace(state);
			if (state.second->instr->insn()) {
				CL_NOTE_MSG(&state.second->instr->insn()->loc,
					SSD_INLINE_COLOR(C_LIGHT_RED, *state.second->instr->insn()));
				CL_DEBUG_AT(2, std::endl << *state.second->fae);
			}
			throw;
		}
		catch (RestartRequest& e)
		{	// in case a restart is requested, clear all fixpoint computation points
			for (auto instr : this->assembly_.code_)
			{
				if (instr->getType() != fi_type_e::fiFix)
				{
					continue;
				}

				// clear the fixpoint
				static_cast<FixpointInstruction*>(instr)->clear();
			}

			CL_CDEBUG(2, e.what());

			return false;
		}
	}

public:

	/**
	 * @brief  The default constructor
	 *
	 * The default constructor.
	 */
	Engine() :
		boxMan(), compiler_(this->fixpointBackend, this->taBackend, this->boxMan),
		dbgFlag(false)
	{ }

	/**
	 * @brief  Loads types from a storage
	 *
	 * This method loads data types and function stackframes from the provided
	 * storage.
	 *
	 * @param[in]  stor  The code storage containing types
	 */
	void loadTypes(const CodeStorage::Storage& stor)
	{
		CL_DEBUG_AT(3, "loading types ...");

		// clear the box manager
		this->boxMan.clear();

		for (auto type : stor.types)
		{	// for each data type in the storage
			std::vector<size_t> v;
			std::string name;

			switch (type->code)
			{
				case cl_type_e::CL_TYPE_STRUCT: // for a structure

					NodeBuilder::buildNode(v, type);

					if (type->name)
					{	// in case the structure has a name
						name = std::string(type->name);
					}
					else
					{	// in case the structure is nameless
						std::ostringstream ss;
						ss << type->uid;
						name = ss.str();
					}

					CL_DEBUG_AT(3, name);

					this->boxMan.createTypeInfo(name, v);
					break;

				default: // for other types
					break;
			}
		}

		for (auto fnc : stor.fncs)
		{	// for each function in the storage, create a data structure representing
			// its stackframe
			std::vector<size_t> v;

			for (auto sel : SymCtx(*fnc).sfLayout)
			{	// create the stackframe
				v.push_back(sel.offset);
			}

			std::ostringstream ss;
			ss << nameOf(*fnc) << ':' << uidOf(*fnc);

			CL_DEBUG_AT(3, ss.str());

			this->boxMan.createTypeInfo(ss.str(), v);
		}
	}

#if 0
	void loadBoxes(const std::unordered_map<std::string, std::string>& db) {

		CL_DEBUG_AT(2, "loading boxes ...");

		for (auto p : db) {

			this->boxes.push_back((const Box*)this->boxMan.loadBox(p.first, db));

			CL_DEBUG(p.first << ':' << std::endl << *(const FA*)this->boxes.back());

		}

		this->boxMan.buildBoxHierarchy(this->hierarchy, this->basicBoxes);

	}
#endif

	void compile(const CodeStorage::Storage& stor, const CodeStorage::Fnc& entry)
	{
		CL_DEBUG_AT(2, "compiling ...");
		this->compiler_.compile(this->assembly_, stor, entry, vars);
		CL_DEBUG_AT(2, "assembly instructions:" << std::endl << this->assembly_);
	}

	void run()
	{
		// Assertions
		assert(this->assembly_.code_.size());

		try
		{	// expect problems...
			while (!this->main())
			{	// while the analysis hasn't terminated
			}

			// print out boxes
			this->printBoxes();

			for (auto instr : this->assembly_.code_)
			{	// print out all fixpoints
				if (instr->getType() != fi_type_e::fiFix)
				{
					continue;
				}

				if (instr->insn()) {
					CL_DEBUG_AT(1, "fixpoint at " << instr->insn()->loc << std::endl
						<< ((FixpointInstruction*)instr)->getFixPoint());
				} else {
					CL_DEBUG_AT(1, "fixpoint at unknown location" << std::endl
						<< ((FixpointInstruction*)instr)->getFixPoint());
				}
			}

			// print out stats
			CL_DEBUG_AT(1, "forester has evaluated " << this->execMan.statesEvaluated()
				<< " state(s) in " << this->execMan.tracesEvaluated() << " trace(s) using "
				<< this->boxMan.boxDatabase().size() << " box(es)");

		}
		catch (std::exception& e)
		{
			CL_DEBUG(e.what());

			this->printBoxes();

			throw;
		}
	}

	void run(const Compiler::Assembly& assembly)
	{
		this->assembly_ = assembly;

		try {

			this->run();
			this->assembly_.code_.clear();

		} catch (...) {

			this->assembly_.code_.clear();

			throw;

		}

	}

	void setDbgFlag()
	{
		this->dbgFlag = 1;
	}

};

SymExec::SymExec() :
	engine(new Engine())
{ }

SymExec::~SymExec()
{
	// Assertions
	assert(engine != nullptr);

	delete this->engine;
}

void SymExec::loadTypes(const CodeStorage::Storage& stor)
{
	// Assertions
	assert(engine != nullptr);

	this->engine->loadTypes(stor);
}

#if 0
void SymExec::loadBoxes(const std::unordered_map<std::string, std::string>& db) {
	this->engine->loadBoxes(db);
}
#endif

void SymExec::compile(const CodeStorage::Storage& stor,
	const CodeStorage::Fnc& main)
{
	// Assertions
	assert(engine != nullptr);

	this->engine->compile(stor, main);
}

void SymExec::run()
{
	// Assertions
	assert(engine != nullptr);

	this->engine->run();
}

void SymExec::run(const Compiler::Assembly& assembly)
{
	// Assertions
	assert(engine != nullptr);

	this->engine->run(assembly);
}

void SymExec::setDbgFlag()
{
	// Assertions
	assert(engine != nullptr);

	this->engine->setDbgFlag();
}
