// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static org.sosy_lab.java_smt.basicimpl.FormulaCreator.escapeName;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.EnumerationFormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;

@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractEnumerationFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFuncDecl>
    implements EnumerationFormulaManager {

  /** The class 'EnumType' is just a plain internal value-holding class. */
  protected class EnumType {
    private final EnumerationFormulaType enumerationFormulaType;
    private final TType nativeType;
    private final ImmutableMap<String, TFormulaInfo> constants;

    public EnumType(
        EnumerationFormulaType pEnumerationFormulaType,
        TType pNativeType,
        ImmutableMap<String, TFormulaInfo> pConstants) {
      enumerationFormulaType = pEnumerationFormulaType;
      nativeType = pNativeType;
      constants = pConstants;
    }

    public EnumerationFormulaType getEnumerationFormulaType() {
      return enumerationFormulaType;
    }

    public boolean hasConstants(String name) {
      return constants.containsKey(name);
    }
  }

  protected final Map<String, EnumType> enumerations = new LinkedHashMap<>();

  protected AbstractEnumerationFormulaManager(
      FormulaCreator<TFormulaInfo, TType, TEnv, TFuncDecl> pFormulaCreator) {
    super(pFormulaCreator);
  }

  private EnumerationFormula wrap(TFormulaInfo pTerm) {
    return getFormulaCreator().encapsulateEnumeration(pTerm);
  }

  private void checkSameEnumerationType(EnumerationFormula pF1, EnumerationFormula pF2) {
    final FormulaType<?> type1 = formulaCreator.getFormulaType(pF1);
    final FormulaType<?> type2 = formulaCreator.getFormulaType(pF2);
    checkArgument(type1 instanceof EnumerationFormulaType);
    checkArgument(type2 instanceof EnumerationFormulaType);
    checkArgument(
        type1.equals(type2),
        "Can't compare element of type %s with element of type %s.",
        type1,
        type2);
  }

  @Override
  public EnumerationFormulaType declareEnumeration(String pName, Set<String> pElementNames) {
    return declareEnumerationImpl(
        escapeName(pName),
        ImmutableSet.copyOf(Iterables.transform(pElementNames, FormulaCreator::escapeName)));
  }

  protected EnumerationFormulaType declareEnumerationImpl(String pName, Set<String> pElementNames) {
    final EnumerationFormulaType type = FormulaType.getEnumerationType(pName, pElementNames);
    EnumType existingType = enumerations.get(pName);
    if (existingType == null) {
      enumerations.put(pName, declareEnumeration0(type));
    } else {
      Preconditions.checkArgument(
          type.equals(existingType.getEnumerationFormulaType()),
          "Enumeration type '%s' is already declared as '%s'.",
          type,
          existingType.getEnumerationFormulaType());
    }
    return type;
  }

  protected abstract EnumType declareEnumeration0(EnumerationFormulaType pType);

  @Override
  public EnumerationFormula makeConstant(String pName, EnumerationFormulaType pType) {
    Preconditions.checkArgument(
        pType.getElements().contains(pName),
        "Constant '%s' is not available in the enumeration type '%s'",
        pName,
        pType);
    return wrap(makeConstantImpl(pName, pType));
  }

  protected TFormulaInfo makeConstantImpl(String pName, EnumerationFormulaType pType) {
    return checkNotNull(enumerations.get(pType.getName()).constants.get(pName));
  }

  @Override
  public EnumerationFormula makeVariable(String pVar, EnumerationFormulaType pType) {
    return wrap(makeVariableImpl(escapeName(pVar), pType));
  }

  protected TFormulaInfo makeVariableImpl(String pVar, EnumerationFormulaType pType) {
    return getFormulaCreator().makeVariable(enumerations.get(pType.getName()).nativeType, pVar);
  }

  @Override
  public BooleanFormula equivalence(EnumerationFormula pF1, EnumerationFormula pF2) {
    this.checkSameEnumerationType(pF1, pF2);
    return wrapBool(equivalenceImpl(extractInfo(pF1), extractInfo(pF2)));
  }

  protected abstract TFormulaInfo equivalenceImpl(TFormulaInfo pF1, TFormulaInfo pF2);
}
