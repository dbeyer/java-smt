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

public class ExpressionVector extends java.util.AbstractList<Expression>
    implements java.util.RandomAccess {
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
  protected void finalize1() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        DrealJNI.deleteExpressionVector(swigCPtr);
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

  @Override
  public Expression get(int index) {
    return doGet(index);
  }

  @Override
  public Expression set(int index, Expression e) {
    return doSet(index, e);
  }

  @Override
  public boolean add(Expression e) {
    modCount++;
    doAdd(e);
    return true;
  }

  @Override
  public void add(int index, Expression e) {
    modCount++;
    doAdd(index, e);
  }

  @Override
  public Expression remove(int index) {
    modCount++;
    return doRemove(index);
  }

  @Override
  protected void removeRange(int fromIndex, int toIndex) {
    modCount++;
    doRemoveRange(fromIndex, toIndex);
  }

  @Override
  public int size() {
    return doSize();
  }

  public ExpressionVector() {
    this(DrealJNI.newExpressionVectorSWIG0(), true);
  }

  public ExpressionVector(ExpressionVector other) {
    this(DrealJNI.newExpressionVectorSWIG1(ExpressionVector.getCPtr(other), other), true);
  }

  public long capacity() {
    return DrealJNI.expressionVectorCapacity(swigCPtr, this);
  }

  public void reserve(long n) {
    DrealJNI.expressionVectorReserve(swigCPtr, this, n);
  }

  @Override
  public boolean isEmpty() {
    return DrealJNI.expressionVectorIsEmpty(swigCPtr, this);
  }

  @Override
  public void clear() {
    DrealJNI.expressionVectorClear(swigCPtr, this);
  }

  public ExpressionVector(int count, Expression value) {
    this(DrealJNI.newExpressionVectorSWIG2(count, Expression.getCPtr(value), value), true);
  }

  private int doSize() {
    return DrealJNI.expressionVectorDoSize(swigCPtr, this);
  }

  private void doAdd(Expression x) {
    DrealJNI.expressionVectorDoAddSWIG0(swigCPtr, this, Expression.getCPtr(x), x);
  }

  private void doAdd(int index, Expression x) {
    DrealJNI.expressionVectorDoAddSWIG1(swigCPtr, this, index, Expression.getCPtr(x), x);
  }

  private Expression doRemove(int index) {
    return new Expression(DrealJNI.expressionVectorDoRemove(swigCPtr, this, index), true);
  }

  private Expression doGet(int index) {
    return new Expression(DrealJNI.expressionVectorDoGet(swigCPtr, this, index), false);
  }

  private Expression doSet(int index, Expression val) {
    return new Expression(
        DrealJNI.expressionVectorDoSet(swigCPtr, this, index, Expression.getCPtr(val), val), true);
  }

  private void doRemoveRange(int fromIndex, int toIndex) {
    DrealJNI.expressionVectorDoRemoveRange(swigCPtr, this, fromIndex, toIndex);
  }
}
