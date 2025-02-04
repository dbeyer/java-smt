// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.Lists;
import java.util.Arrays;
import java.util.List;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.UFManager;

/**
 * This class simplifies the implementation of the FunctionFormulaManager by converting the types to
 * the solver specific type.
 *
 * @param <TFormulaInfo> The solver specific type.
 * @param <TFunctionDecl> The solver specific type of declarations of any function application
 * @param <TType> The solver specific type of formula-types.
 */
@SuppressWarnings("ClassTypeParameterName")
public abstract class AbstractUFManager<TFormulaInfo, TFunctionDecl, TType, TEnv>
    extends AbstractBaseFormulaManager<TFormulaInfo, TType, TEnv, TFunctionDecl>
    implements UFManager {

  protected AbstractUFManager(FormulaCreator<TFormulaInfo, TType, TEnv, TFunctionDecl> pCreator) {
    super(pCreator);
  }

  @Override
  public final <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, List<FormulaType<?>> pArgTypes) {
    List<TType> argTypes = Lists.transform(pArgTypes, this::toSolverType);
    return FunctionDeclarationImpl.of(
        pName,
        FunctionDeclarationKind.UF,
        pArgTypes,
        pReturnType,
        formulaCreator.declareUFImpl(
            FormulaCreator.escapeName(pName), toSolverType(pReturnType), argTypes));
  }

  @Override
  public <T extends Formula> FunctionDeclaration<T> declareUF(
      String pName, FormulaType<T> pReturnType, FormulaType<?>... pArgs) {
    return declareUF(pName, pReturnType, Arrays.asList(pArgs));
  }

  @Override
  public <T extends Formula> T callUF(FunctionDeclaration<T> funcType, Formula... args) {
    return formulaCreator.callFunction(funcType, Arrays.asList(args));
  }

  @Override
  public final <T extends Formula> T callUF(
      FunctionDeclaration<T> pFunc, List<? extends Formula> pArgs) {
    return formulaCreator.callFunction(pFunc, pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, List<Formula> pArgs) {
    List<FormulaType<?>> argTypes = Lists.transform(pArgs, getFormulaCreator()::getFormulaType);
    FunctionDeclaration<T> func = declareUF(name, pReturnType, argTypes);
    return callUF(func, pArgs);
  }

  @Override
  public <T extends Formula> T declareAndCallUF(
      String name, FormulaType<T> pReturnType, Formula... pArgs) {
    return declareAndCallUF(name, pReturnType, Arrays.asList(pArgs));
  }
}
