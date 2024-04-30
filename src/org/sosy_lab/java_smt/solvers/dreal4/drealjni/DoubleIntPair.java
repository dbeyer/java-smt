// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (https://www.swig.org).
 * Version 4.1.1
 *
 * Do not make changes to this file unless you know what you are doing - modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */
package org.sosy_lab.java_smt.solvers.dreal4.drealjni;

import javax.annotation.concurrent.NotThreadSafe;

@NotThreadSafe
public class DoubleIntPair {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected DoubleIntPair(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(DoubleIntPair obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(DoubleIntPair obj) {
    long ptr = 0;
    if (obj != null) {
      if (!obj.swigCMemOwn) {
        throw new RuntimeException("Cannot release ownership as memory is not owned");
      }
      ptr = obj.swigCPtr;
      obj.swigCMemOwn = false;
      obj.delete();
    }
    return ptr;
  }

  protected void finalize1() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        DrealJNI.deleteDoubleIntPair(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public DoubleIntPair() {
    this(DrealJNI.newDoubleIntPairSWIG0(), true);
  }

  public DoubleIntPair(double first, int second) {
    this(DrealJNI.newDoubleIntPairSWIG1(first, second), true);
  }

  public DoubleIntPair(DoubleIntPair other) {
    this(DrealJNI.newDoubleIntPairSWIG2(DoubleIntPair.getCPtr(other), other), true);
  }

  public void setFirst(double value) {
    DrealJNI.doubleIntPairFirstSet(swigCPtr, this, value);
  }

  public double getFirst() {
    return DrealJNI.doubleIntPairFirstGet(swigCPtr, this);
  }

  public void setSecond(int value) {
    DrealJNI.doubleIntPairSecondSet(swigCPtr, this, value);
  }

  public int getSecond() {
    return DrealJNI.doubleIntPairSecondGet(swigCPtr, this);
  }
}
