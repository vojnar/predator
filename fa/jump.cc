/*
 * Copyright (C) 2011 Jiri Simacek
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


// Forester headers
#include "jump.hh"


void FI_jmp::execute(ExecutionManager& /* execMan */,
	const AbstractInstruction::StateType&)
{
	// not implemented
	assert(false);
}


void FI_jmp::finalize(const std::unordered_map<const CodeStorage::Block*,
	AbstractInstruction*>& codeIndex,
	std::vector<AbstractInstruction*>::const_iterator)
{
	next_ = this;

	while (next_->getType() == fi_type_e::fiJump)
	{
		next_ = ((FI_jmp*)next_)->getTarget(codeIndex);
	}

	next_->setTarget();
}
