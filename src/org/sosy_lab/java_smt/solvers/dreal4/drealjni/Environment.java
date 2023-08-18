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

public class Environment {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected Environment(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(Environment obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(Environment obj) {
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

  @SuppressWarnings("deprecation")
  protected void finalize1() {
    delete();
  }

  public synchronized void delete() {
    if (swigCPtr != 0) {
      if (swigCMemOwn) {
        swigCMemOwn = false;
        DrealJNI.deleteEnvironment(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public Environment(Environment arg0) {
    this(DrealJNI.newEnvironmentSWIG0(Environment.getCPtr(arg0), arg0), true);
  }

  public Environment assignOperator(Environment arg0) {
    return new Environment(
        DrealJNI.environmentAssignOperatorSWIG0(swigCPtr, this, Environment.getCPtr(arg0), arg0),
        false);
  }

  public Environment(Variable[] varArr) {
    this(DrealJNI.newEnvironmentSWIG1(), true);
    for (Variable var : varArr) {
      if (var.isDummy()) {
        throw new IllegalArgumentException(
            "Dummy variable is detected in the initialization of an environment.");
      } else {
        this.insert(var, 0.0);
      }
    }
  }

  public Environment() {
    this(DrealJNI.newEnvironmentSWIG1(), true);
  }

  public Environment(
      SwigTypeStdInitializerListStdUnorderedMapTVariableDoubleHashValueVariableValueType
          init) {
    this(
        DrealJNI.newEnvironmentSWIG2(
            SwigTypeStdInitializerListStdUnorderedMapTVariableDoubleHashValueVariableValueType
                .getCPtr(init)),
        true);
  }

  public Environment(SwigTypePStdInitializerListTDrealDrakeSymboliVariableT vars) {
    this(
        DrealJNI.newEnvironmentSWIG3(
            SwigTypePStdInitializerListTDrealDrakeSymboliVariableT.getCPtr(vars)),
        true);
  }

  public Environment(
      SwigTypePStdUnorderedMapVariableDoubleHashValueVariable
          m) {
    this(
        DrealJNI.newEnvironmentSWIG4(
            SwigTypePStdUnorderedMapVariableDoubleHashValueVariable
                .getCPtr(m)),
        true);
  }

  public SwigTypePStdUnorderedMapVariableDoubleHashValueVariableIterator
      begin() {
    return new SwigTypePStdUnorderedMapVariableDoubleHashValueVariableIterator(
        DrealJNI.environmentBeginSWIG0(swigCPtr, this), true);
  }

  public SwigTypePStdUnorderedMapVariableDoubleHashValueVariableIterator
      end() {
    return new SwigTypePStdUnorderedMapVariableDoubleHashValueVariableIterator(
        DrealJNI.environmentEndSWIG0(swigCPtr, this), true);
  }

  public SwigTypePStdUnorderedMapVariableDoubleHashValueVariableConstIterator
      cbegin() {
    return new SwigTypePStdUnorderedMapVariableDoubleHashValueVariableConstIterator(
        DrealJNI.environmentCbegin(swigCPtr, this), true);
  }

  public SwigTypePStdUnorderedMapVariableDoubleHashValueVariableConstIterator
      cend() {
    return new SwigTypePStdUnorderedMapVariableDoubleHashValueVariableConstIterator(
        DrealJNI.environmentCend(swigCPtr, this), true);
  }

  public void insert(Variable key, double elem) {
    DrealJNI.environmentInsert(swigCPtr, this, Variable.getCPtr(key), key, elem);
  }

  public boolean empty() {
    return DrealJNI.environmentEmpty(swigCPtr, this);
  }

  public long size() {
    return DrealJNI.environmentSize(swigCPtr, this);
  }

  public SwigTypePStdUnorderedMapVariableDoubleHashValueVariableIterator
      find(Variable key) {
    return new SwigTypePStdUnorderedMapVariableDoubleHashValueVariableIterator(
        DrealJNI.environmentFindSWIG0(swigCPtr, this, Variable.getCPtr(key), key), true);
  }

  public Variables domain() {
    return new Variables(DrealJNI.environmentDomain(swigCPtr, this), true);
  }

  @Override
  public String toString() {
    return DrealJNI.environmentToString(swigCPtr, this);
  }

  public SwigTypePDouble indexing(Variable key) {
    return new SwigTypePDouble(
        DrealJNI.environmentIndexingSWIG0(swigCPtr, this, Variable.getCPtr(key), key), false);
  }
}
