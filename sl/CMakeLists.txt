# Copyright (C) 2010 Kamil Dudka <kdudka@redhat.com>
#
# This file is part of predator.
#
# predator is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# any later version.
#
# predator is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with predator.  If not, see <http://www.gnu.org/licenses/>.

# project metadata
cmake_minimum_required(VERSION 2.6)
project(sl C CXX)
enable_testing()

include("../build-aux/common.cmake")

option(SL_DEBUG "Set to ON to enable debugging support" OFF)
if(SL_DEBUG)
    add_definitions("-O0 -g")
    message (STATUS "Debugging support enabled...")
else()
    add_definitions("-O3 -DNDEBUG")
endif()

# libsl.so
add_library(sl SHARED
    cl_symexec.cc
    intrange.cc
    memdebug.cc
    plotenum.cc
    sigcatch.cc
    symabstract.cc
    symbin.cc
    symbt.cc
    symcall.cc
    symcmp.cc
    symcut.cc
    symdiscover.cc
    symdump.cc
    symexec.cc
    symgc.cc
    symheap.cc
    symjoin.cc
    sympath.cc
    symplot.cc
    symproc.cc
    symseg.cc
    symstate.cc
    symtrace.cc
    symutil.cc
    version.c)

# link with code_listener
find_library(CL_LIB cl ../cl_build)
target_link_libraries(sl ${CL_LIB})

# get the full path of libsl.so
get_property(GCC_PLUG TARGET sl PROPERTY LOCATION)
message (STATUS "GCC_PLUG: ${GCC_PLUG}")

# helping scripts
configure_file(${PROJECT_SOURCE_DIR}/slgcc.in     ${PROJECT_BINARY_DIR}/slgcc     @ONLY)
configure_file(${PROJECT_SOURCE_DIR}/slgccv.in    ${PROJECT_BINARY_DIR}/slgccv    @ONLY)
configure_file(${PROJECT_SOURCE_DIR}/slgdb.in     ${PROJECT_BINARY_DIR}/slgdb     @ONLY)
configure_file(${PROJECT_SOURCE_DIR}/probe.sh.in  ${PROJECT_BINARY_DIR}/probe.sh  @ONLY)

configure_file(${PROJECT_SOURCE_DIR}/register-paths.sh.in
    ${PROJECT_BINARY_DIR}/register-paths.sh                                       @ONLY)

configure_file(${PROJECT_SOURCE_DIR}/chk-error-label-reachability.sh.in
    ${PROJECT_BINARY_DIR}/chk-error-label-reachability.sh                         @ONLY)

# make install
install(TARGETS sl DESTINATION lib)

option(TEST_ONLY_FAST "Set to OFF to boost test coverage" ON)

set(GCC_EXEC_PREFIX "timeout 3600"
    CACHE STRING "Set to empty string if not sure")

set(testdir "${sl_SOURCE_DIR}/../tests/predator-regre")

# basic tests
set(tests
         0001 0002 0003 0004 0005 0006 0007 0008 0009
    0010 0011 0012 0013 0014 0015 0016 0017 0018 0019
    0020 0021 0022 0023 0024 0025 0026 0027 0028 0029
    0030 0031 0032 0033 0034 0035 0036 0037 0038 0039
    0040 0041 0042 0043 0044 0045 0046 0047 0048 0049
    0050 0051 0052 0053 0054 0055 0056 0057 0058 0059
    0060 0061 0062 0063 0064 0065 0066 0067 0068 0069
    0070 0071 0072 0073 0074 0075 0076 0077 0078 0079
    0080 0081 0082 0083 0084 0085 0086 0087 0088 0089
    0090 0091 0092 0093 0094 0095 0096 0097 0098 0099
    0100 0101 0102 0103 0104 0105      0107 0108 0109
    0110 0111 0112      0114 0115 0116 0117 0118 0119
    0120 0121 0122 0123      0125 0126 0127 0128 0129
    0130 0131 0132 0133 0134 0135 0136 0137 0138 0139
    0140 0141 0142 0143 0144 0145 0146 0147 0148 0149
    0150 0151 0152 0153 0154 0155 0156      0158 0159
    0160 0161 0162 0163 0164      0166      0168
    0170 0171 0172 0173 0174 0175 0176 0177 0178 0179
    0180 0181 0182 0183 0184 0185 0186 0187 0188 0189
    0190 0191 0192 0193 0194 0195 0196 0197 0198 0199
    0200 0201 0202 0203 0204 0205      0207 0208 0209
    0210      0212      0214 0215      0217 0218 0219
    0220 0221 0222 0223 0224 0225 0226 0227 0228 0229
    0230 0231 0232 0233 0234      0236 0237
    0300      0302
    0400 0401 0402 0403 0404      0406      0408
         0411
              0432
                        0464      0466 0467
    0500 0501 0502 0503 0504 0505           0508 0509
    0510 0511 0512 0513 0514 0515 0516 0517 0518
    0520)

if(TEST_ONLY_FAST)
else()
    # expensive tests (ordered from the fastest to the most expensive)
    set(tests ${tests}
        0416 0167 0124 0415 0414 0418 0417 0471 0412 0157
        0235 0469 0405 0409 0407 0521 0410 0413 0474)
endif()

set(cost 1)

# FIXME: define this macro more generically, in particular the count of args
macro(test_predator_smoke label tool arg1 arg2 arg3)
    foreach (num ${tests})
        set(test_name "${label}___example-${num}")
        add_test(${test_name} ${tool} ${arg1} ${arg2} ${arg3}
            -S "${testdir}/test-${num}.c" -o /dev/null
            -I../include/predator-builtins -DPREDATOR
            -fplugin=${sl_BINARY_DIR}/libsl.so
            -fplugin-arg-libsl-args=noplot
            -fplugin-arg-libsl-preserve-ec
            -fplugin-arg-libsl-verbose=1)

        SET_TESTS_PROPERTIES(${test_name} PROPERTIES COST ${cost})
        MATH(EXPR cost "${cost} + 1")
    endforeach()
endmacro()

# FIXME: define this macro more generically, in particular the count of args
macro(test_predator_regre name_suff ext arg1)
    foreach (num ${tests})
        set(cmd "LC_ALL=C CCACHE_DISABLE=1 ${GCC_EXEC_PREFIX} ${GCC_HOST}")

        # we use the following flag to avoid differences on 32bit vs 64bit archs
        # in the error output, which is checked for exact match
        set(cmd "${cmd} -m32")

        set(cmd "${cmd} -S ${testdir}/test-${num}.c -o /dev/null")
        set(cmd "${cmd} -I../include/predator-builtins -DPREDATOR")
        set(cmd "${cmd} -fplugin=${sl_BINARY_DIR}/libsl.so ${arg1}")
        set(cmd "${cmd} -fplugin-arg-libsl-preserve-ec")
        set(cmd "${cmd} 2>&1")

        # filter out messages that are unrelated to our plug-in
        set(cmd "${cmd} | (grep -E '\\\\[-fplugin=libsl.so\\\\]\$|compiler error|undefined symbol'; true)")
        set(cmd "${cmd} | sed 's/ \\\\[-fplugin=libsl.so\\\\]\$//'")

        # filter out NOTE messages with internal location
        set(cmd "${cmd} | (grep -v 'note: .*\\\\[internal location\\\\]'; true)")

        # drop absolute paths
        set(cmd "${cmd} | sed 's|^[^:]*/||'")

        # ... and finally diff with the expected output
        set(cmd "${cmd} | diff -up ${testdir}/test-${num}.err${ext} -")
        set(test_name "test-${num}.c${name_suff}")
        add_test(${test_name} bash -o pipefail -c "${cmd}")

        SET_TESTS_PROPERTIES(${test_name} PROPERTIES COST ${cost})
        MATH(EXPR cost "${cost} + 1")
    endforeach()
endmacro(test_predator_regre)

# default mode
test_predator_regre("" "" "-fplugin-arg-libsl-args=error_label:ERROR")

# track_uninit mode
test_predator_regre("-TRACK_UNINIT" ".uninit"
    "-fplugin-arg-libsl-args=track_uninit")

# OOM simulation mode
test_predator_regre("-OOM" ".oom" "-fplugin-arg-libsl-args=oom")

if(TEST_WITH_VALGRIND)
    message (STATUS "valgrind enabled for testing...")
    test_predator_smoke("valgrind-test" valgrind
        --trace-children=yes
        --error-exitcode=7
        ${GCC_HOST})
endif()

if(TEST_ONLY_FAST)
else()
    add_test("headers_sanity-0" gcc -ansi -Wall -Wextra -Werror -pedantic
        -o /dev/null
        -c ${sl_SOURCE_DIR}/config.h)

    add_test("headers_sanity-1" make -j
        -C ${sl_SOURCE_DIR}
        -f ${sl_SOURCE_DIR}/Makefile.chk)
endif()
