# This file is part of JavaSMT,
# an API wrapper for a collection of SMT solvers:
# https://github.com/sosy-lab/java-smt
#
# SPDX-FileCopyrightText: 2021 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

FROM ubuntu:bionic

# Install basic packages for building several solvers
RUN apt-get update \
 && apt-get install -y \
        wget curl git \
        build-essential cmake patchelf \
        openjdk-11-jdk ant maven \
        mingw-w64 zlib1g-dev m4

# Yices2 requires some dependencies
RUN apt-get update \
 && apt-get install -y \
        autoconf gperf

# CVC5 requires some dependencies
RUN apt-get update \
 && apt-get install -y \
        python3.10 python3.10-venv python3-toml python3-pyparsing flex libssl-dev cmake \
 && wget https://github.com/Kitware/CMake/releases/download/v3.26.3/cmake-3.26.3.tar.gz \
 && tar -zxvf cmake-3.26.3.tar.gz \
 && cd cmake-3.26.3 \
 && ./bootstrap \
 && make \
 && make install

# set default locale
RUN apt-get update \
 && apt-get install -y \
        locales locales-all
ENV LC_ALL en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US.UTF-8

# OpenSMT requires swig, gmp, flex and bison
# - swig needs to built manually to get version 4.1 for unique_ptr support
# - libpcre2-dev is a dependency of swig
# - gmp needs to be recompiled to generate PIC code
# - lzip is required to unpack the gmp tar ball
RUN apt-get update \
 && apt-get install -y \
        flex \
        bison \
        libpcre2-dev  \
        lzip
WORKDIR /dependencies
RUN wget http://prdownloads.sourceforge.net/swig/swig-4.1.1.tar.gz \
 && tar xf swig-4.1.1.tar.gz \
 && cd swig-4.1.1 \
 && ./configure \
 && make -j4 \
 && make install \
 && cd --
RUN wget https://gmplib.org/download/gmp/gmp-6.2.1.tar.lz \
 && tar xf gmp-6.2.1.tar.lz \
 && cd gmp-6.2.1 \
 && ./configure --enable-cxx --with-pic --disable-shared --enable-fat \
 && make -j4 \
 && make install \
 && cd --

# JNI is not found when compiling Boolector in the image, so we need to set JAVA_HOME
ENV JAVA_HOME=/usr/lib/jvm/java-11-openjdk-amd64/
