/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2016  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

/* ----------------------------------------------------------------------------
 * This file was automatically generated by SWIG (https://www.swig.org).
 * Version 4.1.1
 *
 * Do not make changes to this file unless you know what you are doing - modify
 * the SWIG interface file instead.
 * ----------------------------------------------------------------------------- */
package org.sosy_lab.java_smt.solvers.dreal4.drealjni;


public class BoxBoxPair {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected BoxBoxPair(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(BoxBoxPair obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(BoxBoxPair obj) {
    long ptr = 0;
    if (obj != null) {
      if (!obj.swigCMemOwn)
        throw new RuntimeException("Cannot release ownership as memory is not owned");
      ptr = obj.swigCPtr;
      obj.swigCMemOwn = false;
      obj.delete();
    }
    return ptr;
  }

  @SuppressWarnings("deprecation")
  protected void finalize() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        drealJNI.delete_BoxBoxPair(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public BoxBoxPair() {
    this(drealJNI.new_BoxBoxPair__SWIG_0(), true);
  }

  public BoxBoxPair(Box first, Box second) {
    this(drealJNI.new_BoxBoxPair__SWIG_1(Box.getCPtr(first), first, Box.getCPtr(second), second), true);
  }

  public BoxBoxPair(BoxBoxPair other) {
    this(drealJNI.new_BoxBoxPair__SWIG_2(BoxBoxPair.getCPtr(other), other), true);
  }

  public void setFirst(Box value) {
    drealJNI.BoxBoxPair_first_set(swigCPtr, this, Box.getCPtr(value), value);
  }

  public Box getFirst() {
    long cPtr = drealJNI.BoxBoxPair_first_get(swigCPtr, this);
    return (cPtr == 0) ? null : new Box(cPtr, false);
  }

  public void setSecond(Box value) {
    drealJNI.BoxBoxPair_second_set(swigCPtr, this, Box.getCPtr(value), value);
  }

  public Box getSecond() {
    long cPtr = drealJNI.BoxBoxPair_second_get(swigCPtr, this);
    return (cPtr == 0) ? null : new Box(cPtr, false);
  }

}
