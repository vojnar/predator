/*
 * Copyright (C) 2009-2010 Kamil Dudka <kdudka@redhat.com>
 * Copyright (C) 2010 Petr Peringer, FIT
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

#ifndef H_GUARD_SYMABSTRACT_H
#define H_GUARD_SYMABSTRACT_H

/**
 * @file symabstract.hh
 * list segment based abstraction/concretization of heap objects
 */

#include "config.h"
#include "symheap.hh"

#include <list>

/**
 * container for symbolic heaps scheduled for processing.  It's feed by
 * concretizeObj() and consumed by SymExecCore::concretizeLoop().
 */
typedef std::list<SymHeap> TSymHeapList;

/**
 * concretize the given @b abstract object.  If the result is non-deterministic,
 * more than one symbolic heap can be produced.
 * @param sh an instance of symbolic heap, used in read/write mode
 * @param addr address of the @b abstract heap object that should be concretized
 * @param dst a container for the results caused by non-deterministic decisions
 * @param leakList if not NULL, push all leaked root objects to the list
 * @note the first result is always stored into sh, the use of dst is optional
 */
void concretizeObj(
        SymHeap                     &sh,
        const TValId                 addr,
        TSymHeapList                &dst,
        TValList                    *leakList = 0);

/**
 * analyze the given symbolic heap and consider abstraction of some shapes that
 * we know ho to rewrite to their more abstract way of existence
 * @param sh an instance of symbolic heap, used in read/write mode
 */
void abstractIfNeeded(SymHeap &sh);

/**
 * attempt to splice out a chain of (possibly empty) empty list segments when
 * the caller has some explicit info that there are in fact no list segments
 * @note The operation may fail under some circumstances, caller should be
 * probably ready for both variants.
 * @note This operation may be used on traversing of a non-deterministic
 * condition during symbolic execution.
 * @param sh an instance of symbolic heap, used in read/write mode
 * @param atAddr address of the list segment that should be eliminated
 * @param pointingTo target point of the segment
 * @param leakList if not NULL, push all leaked root objects to the list
 */
bool spliceOutAbstractPath(
        SymHeap                     &sh,
        const TValId                 atAddr,
        const TValId                 pointingTo,
        TValList                    *leakList = 0);

void decrementProtoLevel(SymHeap &sh, const TValId at);

/// enable/disable debugging of symabstract
void debugSymAbstract(const bool enable);

#endif /* H_GUARD_SYMABSTRACT_H */
