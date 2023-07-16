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

public class ExpressionVector extends java.util.AbstractList<Expression> implements java.util.RandomAccess {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected ExpressionVector(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(ExpressionVector obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(ExpressionVector obj) {
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
        drealJNI.delete_ExpressionVector(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public ExpressionVector(Expression[] initialElements) {
    this();
    reserve(initialElements.length);

    for (Expression element : initialElements) {
      add(element);
    }
  }

  public ExpressionVector(Iterable<Expression> initialElements) {
    this();
    for (Expression element : initialElements) {
      add(element);
    }
  }

  public Expression get(int index) {
    return doGet(index);
  }

  public Expression set(int index, Expression e) {
    return doSet(index, e);
  }

  public boolean add(Expression e) {
    modCount++;
    doAdd(e);
    return true;
  }

  public void add(int index, Expression e) {
    modCount++;
    doAdd(index, e);
  }

  public Expression remove(int index) {
    modCount++;
    return doRemove(index);
  }

  protected void removeRange(int fromIndex, int toIndex) {
    modCount++;
    doRemoveRange(fromIndex, toIndex);
  }

  public int size() {
    return doSize();
  }

  public ExpressionVector() {
    this(drealJNI.new_ExpressionVector__SWIG_0(), true);
  }

  public ExpressionVector(ExpressionVector other) {
    this(drealJNI.new_ExpressionVector__SWIG_1(ExpressionVector.getCPtr(other), other), true);
  }

  public long capacity() {
    return drealJNI.ExpressionVector_capacity(swigCPtr, this);
  }

  public void reserve(long n) {
    drealJNI.ExpressionVector_reserve(swigCPtr, this, n);
  }

  public boolean isEmpty() {
    return drealJNI.ExpressionVector_isEmpty(swigCPtr, this);
  }

  public void clear() {
    drealJNI.ExpressionVector_clear(swigCPtr, this);
  }

  public ExpressionVector(int count, Expression value) {
    this(drealJNI.new_ExpressionVector__SWIG_2(count, Expression.getCPtr(value), value), true);
  }

  private int doSize() {
    return drealJNI.ExpressionVector_doSize(swigCPtr, this);
  }

  private void doAdd(Expression x) {
    drealJNI.ExpressionVector_doAdd__SWIG_0(swigCPtr, this, Expression.getCPtr(x), x);
  }

  private void doAdd(int index, Expression x) {
    drealJNI.ExpressionVector_doAdd__SWIG_1(swigCPtr, this, index, Expression.getCPtr(x), x);
  }

  private Expression doRemove(int index) {
    return new Expression(drealJNI.ExpressionVector_doRemove(swigCPtr, this, index), true);
  }

  private Expression doGet(int index) {
    return new Expression(drealJNI.ExpressionVector_doGet(swigCPtr, this, index), false);
  }

  private Expression doSet(int index, Expression val) {
    return new Expression(drealJNI.ExpressionVector_doSet(swigCPtr, this, index, Expression.getCPtr(val), val), true);
  }

  private void doRemoveRange(int fromIndex, int toIndex) {
    drealJNI.ExpressionVector_doRemoveRange(swigCPtr, this, fromIndex, toIndex);
  }

}
