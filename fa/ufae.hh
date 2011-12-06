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

#ifndef UFAE_H
#define UFAE_H

#include <vector>
#include <ostream>

#include "utils.hh"
#include "treeaut.hh"
#include "label.hh"
#include "boxman.hh"
#include "forestautext.hh"

class UFAE {

	TA<label_type>& backend;

	size_t stateOffset;

	BoxMan& boxMan;

public:

	UFAE(TA<label_type>& backend, BoxMan& boxMan) : backend(backend), stateOffset(1), boxMan(boxMan) {
		// let 0 be the only accepting state
		this->backend.addFinalState(0);
	}

	void clear() { this->stateOffset = 1; }

	size_t getStateOffset() const {
		return this->stateOffset;
	}

	void setStateOffset(size_t offset) {
		this->stateOffset = offset;
	}
/*
	struct RenameNonleafF {

		Index<size_t>& index;

		size_t offset;

		RenameNonleafF(Index<size_t>& index, size_t offset = 0)
			: index(index), offset(offset) {}

		size_t operator()(size_t s) {
			if (_MSB_TEST(s))
				return s;
			return this->index.translateOTF(s) + this->offset;
		}

	};
*/
	template <class T>
	struct Cursor {
		T begin;
		T end;
		T curr;
		Cursor(T begin, T end) : begin(begin), end(end), curr(begin) {}
		bool inc() {
			if (++this->curr != this->end)
				return true;
			this->curr = this->begin;
			return false;
		}
	};

	TA<label_type>& fae2ta(TA<label_type>& dst, Index<size_t>& index, const FAE& src) const {
		dst.addFinalState(0);
		std::vector<Cursor<std::set<size_t>::const_iterator> > tmp;
		for (auto root : src.roots) {
			TA<label_type>::rename(dst, *root, FAE::RenameNonleafF(index, this->stateOffset), false);
			assert(root->getFinalStates().size());
			tmp.push_back(Cursor<std::set<size_t>::const_iterator>(root->getFinalStates().begin(), root->getFinalStates().end()));
		}
		std::vector<size_t> lhs(tmp.size());
		label_type label = this->boxMan.lookupLabel(tmp.size(), src.variables);
		bool valid = true;
//		std::cerr << index << std::endl;
		while (valid) {
			for (size_t i = 0; i < lhs.size(); ++i) {
//				std::cerr << *tmp[i].curr << ' ';
				lhs[i] = index[*tmp[i].curr] + this->stateOffset;
			}
			dst.addTransition(lhs, label, 0);
			valid = false;
			for (std::vector<Cursor<std::set<size_t>::const_iterator> >::iterator i = tmp.begin(); !valid && i != tmp.end(); ++i)
				valid = i->inc();
		}
		return dst;
	}

	void join(const TA<label_type>& src, const Index<size_t>& index) {
		TA<label_type>::disjointUnion(this->backend, src, false);
		this->stateOffset += index.size();
	}

	void adjust(const Index<size_t>& index) {
		this->stateOffset += index.size();
	}

	void ta2fae(vector<FAE*>& dst, TA<label_type>::Backend& backend, BoxMan& boxMan) const {
		TA<label_type>::td_cache_type cache;
		this->backend.buildTDCache(cache);
		vector<const TT<label_type>*>& v = cache.insert(make_pair(0, vector<const TT<label_type>*>())).first->second;
		// iterate over all "synthetic" transitions and constuct new FAE for each
		for (vector<const TT<label_type>*>::iterator i = v.begin(); i != v.end(); ++i) {
			FAE* fae = new FAE(backend, boxMan);
			dst.push_back(fae);
			fae->loadTA(this->backend, cache, *i, this->stateOffset);
		}
	}

	friend std::ostream& operator<<(std::ostream& os, const UFAE& ufae) {
		TAWriter<label_type>(os).writeOne(ufae.backend);
		return os;
	}

};

#endif
