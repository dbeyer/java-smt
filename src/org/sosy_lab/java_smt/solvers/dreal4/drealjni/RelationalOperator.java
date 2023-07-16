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

public final class RelationalOperator {
  public final static RelationalOperator EQ = new RelationalOperator("EQ");
  public final static RelationalOperator NEQ = new RelationalOperator("NEQ");
  public final static RelationalOperator GT = new RelationalOperator("GT");
  public final static RelationalOperator GEQ = new RelationalOperator("GEQ");
  public final static RelationalOperator LT = new RelationalOperator("LT");
  public final static RelationalOperator LEQ = new RelationalOperator("LEQ");

  public final int swigValue() {
    return swigValue;
  }

  public String toString() {
    return swigName;
  }

  public static RelationalOperator swigToEnum(int swigValue) {
    if (swigValue < swigValues.length && swigValue >= 0 && swigValues[swigValue].swigValue == swigValue)
      return swigValues[swigValue];
    for (int i = 0; i < swigValues.length; i++)
      if (swigValues[i].swigValue == swigValue)
        return swigValues[i];
    throw new IllegalArgumentException("No enum " + RelationalOperator.class + " with value " + swigValue);
  }

  private RelationalOperator(String swigName) {
    this.swigName = swigName;
    this.swigValue = swigNext++;
  }

  private RelationalOperator(String swigName, int swigValue) {
    this.swigName = swigName;
    this.swigValue = swigValue;
    swigNext = swigValue+1;
  }

  private RelationalOperator(String swigName, RelationalOperator swigEnum) {
    this.swigName = swigName;
    this.swigValue = swigEnum.swigValue;
    swigNext = this.swigValue+1;
  }

  private static RelationalOperator[] swigValues = { EQ, NEQ, GT, GEQ, LT, LEQ };
  private static int swigNext = 0;
  private final int swigValue;
  private final String swigName;
}

