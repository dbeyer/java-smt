#!/usr/bin/env bash

# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

# This script builds libyices2j.so.

# INFO: Before running this script, you need to do build Yices2.
# See the corresponding section in doc/Developers.md for details.

# This script searches for all included libraries in the current directory first.
# You can use this to override specific libraries installed on your system.
# You can also use this to force static linking of a specific library,
# if you put only the corresponding .a file in this directory, not the .so file.

# For example, to statically link against libstdc++,
# compile this library with --with-pic,
# and put the resulting libstdc++.a file in this directory.

SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
  DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ ${SOURCE} != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" && pwd )"

cd ${DIR}

JNI_HEADERS="$(../get_jni_headers.sh)"

RELATIVE_ROOT_DIR="../../../.."
YICES_SRC_DIR=$RELATIVE_ROOT_DIR/"$1"/src/include
YICES_LIB_DIR=$RELATIVE_ROOT_DIR/"$1"/build/x86_64-pc-linux-gnu-release/lib/
GMP_HEADER_DIR=$RELATIVE_ROOT_DIR/"$2"
GMP_LIB_DIR=$GMP_HEADER_DIR/.libs
GPERF_HEADER_DIR=$RELATIVE_ROOT_DIR/"$3"
GPERF_LIB_DIR=$GPERF_HEADER_DIR/lib

LDFLAGS="-L. $LDFLAGS"
add_include_lib() {
    [ -d "$1" ] && CFLAGS="$CFLAGS -I$1"
    [ -d "$2" ] && LDFLAGS="$LDFLAGS -L$2"
}
add_include_lib "$YICES_SRC_DIR" "$YICES_LIB_DIR"
add_include_lib "$GMP_HEADER_DIR" "$GMP_LIB_DIR"
add_include_lib "$GPERF_HEADER_DIR" "$GPERF_LIB_DIR"

command_exists() {
    command -v "$1" >/dev/null 2>&1
}
header_exists() {
    for F in ${CFLAGS} -I/usr/include -I/include; do
        [ "${F}" != "${F#-I}" ] && [ -f "${F#-I}/$1" ] && return 0
    done
    echo "Missing path to header \"$1\" in CFLAGS."
    return 1
}
find_library() {
    for F in ${LDFLAGS} -L/usr/lib -L/lib; do
        [ "${F}" != "${F#-L}" ] && [ -f "${F#-L}/$1" ] && echo "${F#-L}/$1" && return 0
    done
    return 1
}
library_exists() {
    find_library "$1" >/dev/null && return 0
    echo "Missing path to library \"$1\" in LDFLAGS."
    return 1
}

# check requirements
command_exists cc
header_exists gmp.h
header_exists yices.h
header_exists jni.h
library_exists libyices.a
library_exists libgmp.a
[ $(uname -s) != "Darwin" ] && [ $(uname -m) == "x86_64" ] && library_exists libgp.a

SRC_FILE="org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.c"
OBJ_FILE="org_sosy_1lab_java_1smt_solvers_yices2_Yices2NativeApi.o"

OUT_FILE="libyices2j.so"
[ $(uname -s) = "Darwin" ] && OUT_FILE="libyices2j.dylib"

echo "Compiling the C wrapper code and creating the \"$OUT_FILE\" library..."

# This will compile the JNI wrapper part, given the JNI and the Yices header files
cc -g -std=gnu99 -Wall -Wextra -Wpedantic -Wno-return-type -Wno-unused-parameter \
    $CFLAGS $JNI_HEADERS $SRC_FILE -fPIC -c -o $OBJ_FILE

echo "Compilation Done"
echo "Linking libraries together into one file..."

# This will link together the file produced above, the Yices library, the GMP library and the standard libraries.
# Everything except the standard libraries is included statically.
# The result is a single shared library containing all necessary components.
if [ $(uname -s) = "Darwin" ]; then
    LDFLAGS="$LDFLAGS -dynamiclib $(find_library libyices.a) $(find_library libgmp.a)"
elif [ $(uname -m) = "x86_64" ]; then
    LDFLAGS="$LDFLAGS -shared -Wl,-soname,libyices2j.so
    -Wl,-Bstatic -lyices -lgmpxx -lgmp -lgp -static-libstdc++ -lstdc++
    -Wl,-Bdynamic -lc -lm
    -Wl,--version-script=libyices2j.version"
else
    # TODO compiling for/on a 32bit system was not done for quite a long time. We should drop it.
    LDFLAGS="$LDFLAGS -shared -Wl,-soname,libyices2j.so
    -Wl,-Bstatic -lyices -lgmpxx -lgmp
    -Wl,-Bdynamic -lc -lm -lstdc++"
fi
cc -Wall -g -o "$OUT_FILE" $LDFLAGS "$OBJ_FILE"

if [ $? -ne 0 ]; then
    echo "There was a problem during compilation of \"$SRC_FILE\""
    exit 1
fi

echo "Linking Done"
echo "Reducing file size by dropping unused symbols..."

STRIP_FLAGS=""
[ $(uname -s) = "Darwin" ] && STRIP_FLAGS="-u"
strip $STRIP_FLAGS "$OUT_FILE"

echo "Reduction Done"

if command_exists readelf; then
    MISSING_SYMBOLS="$(readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND)"
    if [ ! -z "$MISSING_SYMBOLS" ]; then
        echo "Warning: There are the following unresolved dependencies in libyices2j.so:"
        readelf -Ws ${OUT_FILE} | grep NOTYPE | grep GLOBAL | grep UND
        exit 1
    fi
fi

echo "All Done"
