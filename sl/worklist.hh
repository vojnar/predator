/*
 * Copyright (C) 2010 Kamil Dudka <kdudka@redhat.com>
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

#include <set>
#include <stack>

#include "cl_private.hh"

// really stupid, but easy to use, DFS implementation
template <class T>
class WorkList {
    private:
        std::stack<T> todo;
        std::set<T>   done;

    public:
        WorkList() { }
        WorkList(const T &item) {
            todo.push(item);
            done.insert(item);
        }

        bool next(T &dst) {
            if (todo.empty())
                return false;

            dst = todo.top();
            todo.pop();
            return true;
        }

        bool schedule(const T &item) {
            if (hasKey(done, item))
                return false;

            todo.push(item);
            done.insert(item);
            return true;
        }
};