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

import com.google.common.base.Preconditions;
import javax.annotation.concurrent.NotThreadSafe;

@NotThreadSafe
public class Config {
  private transient long swigCPtr;
  protected transient boolean swigCMemOwn;

  protected Config(long cPtr, boolean cMemoryOwn) {
    swigCMemOwn = cMemoryOwn;
    swigCPtr = cPtr;
  }

  protected static long getCPtr(Config obj) {
    return (obj == null) ? 0 : obj.swigCPtr;
  }

  protected static long swigRelease(Config obj) {
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
        DrealJNI.deleteConfig(swigCPtr);
      }
      swigCPtr = 0;
    }
  }

  public Config() {
    this(DrealJNI.newConfigSWIG0(), true);
  }

  public Config(Config arg0) {
    this(DrealJNI.newConfigSWIG1(Config.getCPtr(arg0), arg0), true);
  }

  public Config assignOperator(Config arg0) {
    return new Config(
        DrealJNI.configAssignOperatorSWIG0(swigCPtr, this, Config.getCPtr(arg0), arg0), false);
  }

  public double precision() {
    return DrealJNI.configPrecision(swigCPtr, this);
  }

  public OptionValueDouble mutablePrecision() {
    return new OptionValueDouble(DrealJNI.configMutablePrecision(swigCPtr, this), false);
  }

  public void mutablePrecision(double value) {
    DrealJNI.configMutablePrecision0(value, Config.getCPtr(this));
  }

  public boolean produceModels() {
    return DrealJNI.configProduceModels(swigCPtr, this);
  }

  public OptionValueBool mutableProduceModels() {
    return new OptionValueBool(DrealJNI.configMutableProduceModels(swigCPtr, this), false);
  }

  public void mutableProduceModels(boolean bool) {
    DrealJNI.configMutableProduceModels0(bool, Config.getCPtr(this));
  }

  public boolean usePolytope() {
    return DrealJNI.configUsePolytope(swigCPtr, this);
  }

  public OptionValueBool mutableUsePolytope() {
    return new OptionValueBool(DrealJNI.configMutableUsePolytope(swigCPtr, this), false);
  }

  public void mutableUsePolytope(boolean bool) {
    DrealJNI.configMutableUsePolytope0(bool, Config.getCPtr(this));
  }

  public boolean usePpolytopeInForall() {
    return DrealJNI.configUsePolytopeInForall(swigCPtr, this);
  }

  public OptionValueBool mutableUsePolytopeInForall() {
    return new OptionValueBool(DrealJNI.configMutableUsePolytopeInForall(swigCPtr, this), false);
  }

  public void mutableUsePolytopeInForall(boolean bool) {
    DrealJNI.configMutableUsePolytopeInForall0(bool, Config.getCPtr(this));
  }

  public boolean useWorklistFixpoint() {
    return DrealJNI.configUseWorklistFixpoint(swigCPtr, this);
  }

  public OptionValueBool mutableUseWorklistFixpoint() {
    return new OptionValueBool(DrealJNI.configMutableUseWorklistFixpoint(swigCPtr, this), false);
  }

  public void mutableUseWorklistFixpoint(boolean bool) {
    DrealJNI.configMutableUseWorklistFixpoint0(bool, Config.getCPtr(this));
  }

  public boolean useLocalOtimization() {
    return DrealJNI.configUseLocalOptimization(swigCPtr, this);
  }

  public OptionValueBool mutableUseLocalOptimization() {
    return new OptionValueBool(DrealJNI.configMutableUseLocalOptimization(swigCPtr, this), false);
  }

  public void mutableUseLocalOptimization(boolean bool) {
    DrealJNI.configMutableUseLocalOptimization0(bool, Config.getCPtr(this));
  }

  public boolean dumpTheoryLiterals() {
    return DrealJNI.configDumpTheoryLiterals(swigCPtr, this);
  }

  public OptionValueBool mutableDumpTheoryLiterals() {
    return new OptionValueBool(DrealJNI.configMutableDumpTheoryLiterals(swigCPtr, this), false);
  }

  public void mutableDumpTheoryLiterals(boolean bool) {
    DrealJNI.configMutableDumpTheoryLiterals0(bool, Config.getCPtr(this));
  }

  public int numberOfJobs() {
    return DrealJNI.configNumberOfJobs(swigCPtr, this);
  }

  public OptionValueInt mutableNumberOfJobs() {
    return new OptionValueInt(DrealJNI.configMutableNumberOfJobs(swigCPtr, this), false);
  }

  public void mutableNumberOfJobs(int i) {
    DrealJNI.configMutableNumberOfJobs0(i, Config.getCPtr(this));
  }

  public boolean stackLeftBoxFirst() {
    return DrealJNI.configStackLeftBoxFirst(swigCPtr, this);
  }

  public OptionValueBool mutableStackLeftBoxFirst() {
    return new OptionValueBool(DrealJNI.configMutableStackLeftBoxFirst(swigCPtr, this), false);
  }

  public void mutableStackLeftBoxFirst(boolean bool) {
    DrealJNI.configMutableStackLeftBoxFirst0(bool, Config.getCPtr(this));
  }

  public SwigTypePStdFunctionIntBoxConstDynamicBitsetConstBoxPBox brancher() {
    return new SwigTypePStdFunctionIntBoxConstDynamicBitsetConstBoxPBox(
        DrealJNI.configBrancher(swigCPtr, this), false);
  }

  public SwigTypeOptionValueStdFunctionIntBoxConstDynamicBitsetConstBoxPBox mutableBrancher() {
    return new SwigTypeOptionValueStdFunctionIntBoxConstDynamicBitsetConstBoxPBox(
        DrealJNI.configMutableBrancher(swigCPtr, this), false);
  }

  public double nloptFtolRel() {
    return DrealJNI.configNloptFtolRel(swigCPtr, this);
  }

  public OptionValueDouble mutableNloptFtolRel() {
    return new OptionValueDouble(DrealJNI.configMutableNloptFtolRel(swigCPtr, this), false);
  }

  public void mutableNloptFtolRel(double value) {
    DrealJNI.configMutableNloptFtolRel0(value, Config.getCPtr(this));
  }

  public double nloptFtolAbs() {
    return DrealJNI.configNloptFtolAbs(swigCPtr, this);
  }

  public OptionValueDouble mutableNloptFtolAbs() {
    return new OptionValueDouble(DrealJNI.configMutableNloptFtolAbs(swigCPtr, this), false);
  }

  public void mutableNloptFtolAbs(double value) {
    DrealJNI.configMutableNloptFtolAbs0(value, Config.getCPtr(this));
  }

  public int nloptMaxeval() {
    return DrealJNI.configNloptMaxeval(swigCPtr, this);
  }

  public OptionValueInt mutableNloptMaxeval() {
    return new OptionValueInt(DrealJNI.configMutableNloptMaxeval(swigCPtr, this), false);
  }

  public void mutableNloptMaxeval(int i) {
    DrealJNI.configMutableNloptMaxeval0(i, Config.getCPtr(this));
  }

  public double nloptMaxtime() {
    return DrealJNI.configNloptMaxtime(swigCPtr, this);
  }

  public OptionValueDouble mutableNloptMaxtime() {
    return new OptionValueDouble(DrealJNI.configMutableNloptMaxtime(swigCPtr, this), false);
  }

  public void mutableNloptMaxtime(double value) {
    DrealJNI.configMutableNloptMaxtime0(value, Config.getCPtr(this));
  }

  public Config.SatDefaultPhase satDefaultPhase() {
    return Config.SatDefaultPhase.swigToEnum(DrealJNI.configSatDefaultPhase(swigCPtr, this));
  }

  public SwigTypePDrealOptionValueTDrealConfigSatDefaultPhaseT mutableSatDefaultPhase() {
    return new SwigTypePDrealOptionValueTDrealConfigSatDefaultPhaseT(
        DrealJNI.configMutableSatDefaultPhase(swigCPtr, this), false);
  }

  public long randomSeed() {
    return DrealJNI.configRandomSeed(swigCPtr, this);
  }

  public OptionValueUnsignedInt mutableRandomSeed() {
    return new OptionValueUnsignedInt(DrealJNI.configMutableRandomSeed(swigCPtr, this), false);
  }

  public void mutableRandomSeed(long seed) {
    Preconditions.checkArgument(seed >= 0, "Seed must be greater than zero");
    DrealJNI.configMutableRandomSeed0(seed, Config.getCPtr(this));
  }

  public boolean smtlib2Compliant() {
    return DrealJNI.configSmtlib2Compliant(swigCPtr, this);
  }

  public OptionValueBool mutableSmtlib2Compliant() {
    return new OptionValueBool(DrealJNI.configMutableSmtlib2Compliant(swigCPtr, this), false);
  }

  public void mutableSmtlib2Compliant(boolean bool) {
    DrealJNI.configMutableSmtlib2Compliant0(bool, Config.getCPtr(this));
  }

  public static double getKDefaultPrecision() {
    return DrealJNI.configKDefaultPrecisionGet();
  }

  public static double getKDefaultNloptFtolRel() {
    return DrealJNI.configKDefaultNloptFtolRelGet();
  }

  public static double getKDefaultNloptFtolAbs() {
    return DrealJNI.configKDefaultNloptFtolAbsGet();
  }

  public static int getKDefaultNloptMaxEval() {
    return DrealJNI.configKDefaultNloptMaxEvalGet();
  }

  public static double getKDefaultNloptMaxTime() {
    return DrealJNI.configKDefaultNloptMaxTimeGet();
  }

  public static final class SatDefaultPhase {
    public static final Config.SatDefaultPhase FALSE =
        new Config.SatDefaultPhase("False", DrealJNI.configSatDefaultPhaseFalseGet());
    public static final Config.SatDefaultPhase TRUE =
        new Config.SatDefaultPhase("True", DrealJNI.configSatDefaultPhaseTrueGet());
    public static final Config.SatDefaultPhase JEROSLOW_WANG =
        new Config.SatDefaultPhase("JeroslowWang", DrealJNI.configSatDefaultPhaseJeroslowWangGet());
    public static final Config.SatDefaultPhase RANDOM_INITIAL_PHASE =
        new Config.SatDefaultPhase(
            "RandomInitialPhase", DrealJNI.configSatDefaultPhaseRandomInitialPhaseGet());

    public int swigValue() {
      return swigValue;
    }

    @Override
    public String toString() {
      return swigName;
    }

    public static SatDefaultPhase swigToEnum(int swigValue) {
      if (swigValue < swigValues.length
          && swigValue >= 0
          && swigValues[swigValue].swigValue == swigValue) {
        return swigValues[swigValue];
      }
      for (int i = 0; i < swigValues.length; i++) {
        if (swigValues[i].swigValue == swigValue) {
          return swigValues[i];
        }
      }
      throw new IllegalArgumentException(
          "No enum " + SatDefaultPhase.class + " with value " + swigValue);
    }

    @SuppressWarnings("unused")
    private SatDefaultPhase(String swigName) {
      this.swigName = swigName;
      this.swigValue = swigNext++;
    }

    @SuppressWarnings("StaticAssignmentInConstructor")
    private SatDefaultPhase(String swigName, int swigValue) {
      this.swigName = swigName;
      this.swigValue = swigValue;
      swigNext = swigValue + 1;
    }

    @SuppressWarnings({"unused", "StaticAssignmentInConstructor"})
    private SatDefaultPhase(String swigName, SatDefaultPhase swigEnum) {
      this.swigName = swigName;
      this.swigValue = swigEnum.swigValue;
      swigNext = this.swigValue + 1;
    }

    private static SatDefaultPhase[] swigValues = {
      FALSE, TRUE, JEROSLOW_WANG, RANDOM_INITIAL_PHASE,
    };

    @SuppressWarnings("unused")
    private static int swigNext = 0;

    private final int swigValue;
    private final String swigName;
  }
}
