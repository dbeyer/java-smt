// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.TruthJUnit.assume;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.ImmutableList;
import com.google.common.truth.Truth;
import java.util.List;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.ExpectedFormulaVisitor;

public class UFManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  private static final ImmutableList<String> VALID_NAMES = ImmutableList.of("Func", "(Func)");

  @Test
  public void testDeclareAndCallUFWithInt() throws SolverException, InterruptedException {
    requireIntegers();

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula value = imgr.makeNumber(1234);

    for (String name : VALID_NAMES) {
      Formula f =
          fmgr.declareAndCallUF(
              name, FormulaType.IntegerType, ImmutableList.of(imgr.makeNumber(1)));
      FunctionDeclaration<?> declaration = getDeclaration(f);
      Truth.assertThat(declaration.getName()).isEqualTo(name);

      Formula f2 = mgr.makeApplication(declaration, imgr.makeNumber(1));
      Truth.assertThat(f2).isEqualTo(f);

      assertThatFormula(imgr.equal(value, x))
          .implies(
              imgr.equal(
                  (IntegerFormula) mgr.makeApplication(declaration, value),
                  (IntegerFormula) mgr.makeApplication(declaration, x)));
    }
  }

  @Test
  public void testDeclareAndCallUFWithRational() throws SolverException, InterruptedException {
    requireRationals();

    RationalFormula x = rmgr.makeVariable("x");
    RationalFormula value = rmgr.makeNumber(0.5);

    for (String name : VALID_NAMES) {
      Formula f =
          fmgr.declareAndCallUF(
              name, FormulaType.RationalType, ImmutableList.of(rmgr.makeNumber(1.5)));
      FunctionDeclaration<?> declaration = getDeclaration(f);
      Truth.assertThat(declaration.getName()).isEqualTo(name);

      Formula f2 = mgr.makeApplication(declaration, rmgr.makeNumber(1.5));
      Truth.assertThat(f2).isEqualTo(f);

      assertThatFormula(rmgr.equal(value, x))
          .implies(
              rmgr.equal(
                  (RationalFormula) mgr.makeApplication(declaration, value),
                  (RationalFormula) mgr.makeApplication(declaration, x)));
    }
  }

  @Test
  public void testDeclareAndCallUFWithIntAndRational()
      throws SolverException, InterruptedException {

    // INFO: OpenSMT does not support casting from real to int
    assume()
        .withMessage("Solver %s does not support mixed integer-real artihmetic ", solverToUse())
        .that(solver)
        .isNotEqualTo(Solvers.OPENSMT);

    requireIntegers();
    requireRationals();

    IntegerFormula x = imgr.makeVariable("x");
    IntegerFormula value = imgr.makeNumber(1234);

    for (String name : VALID_NAMES) {
      Formula f =
          fmgr.declareAndCallUF(
              name, FormulaType.RationalType, ImmutableList.of(rmgr.makeNumber(1)));
      FunctionDeclaration<?> declaration = getDeclaration(f);
      Truth.assertThat(declaration.getName()).isEqualTo(name);

      Formula f2 = mgr.makeApplication(declaration, imgr.makeNumber(1));
      switch (solverToUse()) {
        case CVC5:
        case SMTINTERPOL:
        case Z3:
          // some solvers have an explicit cast for the parameter
          Truth.assertThat(f2).isNotEqualTo(f);
          List<Formula> args = getArguments(f2);
          Truth.assertThat(args).hasSize(1);
          FunctionDeclaration<?> cast = getDeclaration(args.get(0));
          Truth.assertThat(cast.getName()).isEqualTo("to_real");
          Truth.assertThat(cast.getKind()).isEqualTo(FunctionDeclarationKind.TO_REAL);
          List<Formula> castedValues = getArguments(args.get(0));
          Truth.assertThat(castedValues).hasSize(1);
          Truth.assertThat(castedValues.get(0).toString()).isEqualTo("1");
          break;
        default:
          Truth.assertThat(f2).isEqualTo(f);
      }

      assertThatFormula(rmgr.equal(value, x))
          .implies(
              rmgr.equal(
                  (RationalFormula) mgr.makeApplication(declaration, value),
                  (RationalFormula) mgr.makeApplication(declaration, x)));
    }
  }

  @Test
  public void testDeclareAndCallUFWithIncompatibleTypesIntVsRational() {
    requireIntegers();
    requireRationals();

    for (String name : VALID_NAMES) {
      FunctionDeclaration<?> declaration =
          fmgr.declareUF(name, FormulaType.IntegerType, ImmutableList.of(FormulaType.IntegerType));

      assertThrows(
          IllegalArgumentException.class,
          () -> mgr.makeApplication(declaration, rmgr.makeNumber(2.88)));
      assertThrows(
          IllegalArgumentException.class,
          () -> mgr.makeApplication(declaration, rmgr.makeNumber(0.001)));
      assertThrows(
          IllegalArgumentException.class,
          () -> mgr.makeApplication(declaration, rmgr.makeNumber(-2.88)));
    }
  }

  @Test
  public void testDeclareAndCallUFWithIncompatibleTypesIntVsBool() {
    requireIntegers();

    for (String name : VALID_NAMES) {
      FunctionDeclaration<?> declaration =
          fmgr.declareUF(name, FormulaType.IntegerType, ImmutableList.of(FormulaType.IntegerType));
      assertThrows(
          IllegalArgumentException.class, () -> mgr.makeApplication(declaration, bmgr.makeTrue()));
    }
  }

  @Test
  public void testDeclareAndCallUFWithIncompatibleTypesBoolVsInt() {
    requireIntegers();
    requireBooleanArgument();

    for (String name : VALID_NAMES) {
      FunctionDeclaration<?> declaration =
          fmgr.declareUF(name, FormulaType.IntegerType, ImmutableList.of(FormulaType.BooleanType));
      assertThrows(
          IllegalArgumentException.class,
          () -> mgr.makeApplication(declaration, imgr.makeNumber(1)));
    }
  }

  @Test
  public void testDeclareAndCallUFWithIncompatibleTypesBV4VsBool() {
    requireBitvectors();

    for (String name : VALID_NAMES) {
      FunctionDeclaration<?> declaration =
          fmgr.declareUF(
              name,
              FormulaType.getBitvectorTypeWithSize(4),
              ImmutableList.of(FormulaType.getBitvectorTypeWithSize(4)));
      assertThrows(
          IllegalArgumentException.class, () -> mgr.makeApplication(declaration, bmgr.makeTrue()));
      assertThrows(
          IllegalArgumentException.class,
          () -> mgr.makeApplication(declaration, bvmgr.makeBitvector(8, 8)));
    }
  }

  @Test
  public void testDeclareAndCallUFWithIncompatibleTypesBV4VsInt() {
    requireBitvectors();
    requireIntegers();

    for (String name : VALID_NAMES) {
      FunctionDeclaration<?> declaration =
          fmgr.declareUF(
              name,
              FormulaType.getBitvectorTypeWithSize(4),
              ImmutableList.of(FormulaType.getBitvectorTypeWithSize(4)));
      assertThrows(
          IllegalArgumentException.class,
          () -> mgr.makeApplication(declaration, imgr.makeNumber(123)));
    }
  }

  @Test
  public void testDeclareAndCallUFWithIncompatibleTypesBV4VsRational() {
    requireBitvectors();
    requireRationals();

    for (String name : VALID_NAMES) {
      FunctionDeclaration<?> declaration =
          fmgr.declareUF(
              name,
              FormulaType.getBitvectorTypeWithSize(4),
              ImmutableList.of(FormulaType.getBitvectorTypeWithSize(4)));
      assertThrows(
          IllegalArgumentException.class,
          () -> mgr.makeApplication(declaration, rmgr.makeNumber(1.234)));
    }
  }

  @Test
  public void testDeclareAndCallUFWithBooleanAndBVTypes() {
    requireBitvectors();

    for (String name : VALID_NAMES) {
      FunctionDeclaration<?> declaration =
          fmgr.declareUF(
              name,
              FormulaType.getBitvectorTypeWithSize(4),
              ImmutableList.of(FormulaType.getBitvectorTypeWithSize(1)));
      assertThrows(
          IllegalArgumentException.class, () -> mgr.makeApplication(declaration, bmgr.makeTrue()));
    }
  }

  @Test
  public void testDeclareAndCallUFWithBv() {
    requireBitvectors();
    for (String name : VALID_NAMES) {
      Formula f =
          fmgr.declareAndCallUF(
              name,
              FormulaType.getBitvectorTypeWithSize(4),
              ImmutableList.of(bvmgr.makeBitvector(4, 1)));
      FunctionDeclaration<?> declaration = getDeclaration(f);
      Truth.assertThat(declaration.getName()).isEqualTo(name);
      Formula f2 = mgr.makeApplication(declaration, bvmgr.makeBitvector(4, 1));
      Truth.assertThat(f2).isEqualTo(f);
    }
  }

  @Test
  public void testDeclareAndCallUFWithTypedArgs() {
    requireBooleanArgument();
    createAndCallUF("fooBool1", FormulaType.BooleanType, bmgr.makeTrue());
    createAndCallUF("fooBool2", FormulaType.BooleanType, bmgr.makeTrue(), bmgr.makeTrue());
    requireIntegers();
    createAndCallUF(
        "fooBool3", FormulaType.IntegerType, bmgr.makeTrue(), bmgr.makeTrue(), bmgr.makeTrue());

    createAndCallUF("fooInt1", FormulaType.IntegerType, imgr.makeNumber(2));
    createAndCallUF("fooInt2", FormulaType.IntegerType, imgr.makeNumber(1), imgr.makeNumber(2));
    createAndCallUF(
        "fooInt3",
        FormulaType.BooleanType,
        imgr.makeNumber(1),
        imgr.makeNumber(2),
        imgr.makeNumber(3));

    createAndCallUF("fooMixed1", FormulaType.IntegerType, bmgr.makeTrue(), imgr.makeNumber(2));
    createAndCallUF(
        "fooMixed2", FormulaType.IntegerType, bmgr.makeTrue(), bmgr.makeTrue(), imgr.makeNumber(2));
    createAndCallUF(
        "fooMixed3", FormulaType.BooleanType, bmgr.makeTrue(), imgr.makeNumber(2), bmgr.makeTrue());
  }

  @Test
  public void testDeclareAndCallUFWithRationalArgs() {
    requireRationals();
    createAndCallUF("fooRat1", FormulaType.RationalType, rmgr.makeNumber(2.5));
    createAndCallUF("fooRat2", FormulaType.IntegerType, rmgr.makeNumber(1.5), rmgr.makeNumber(2.5));
    requireBooleanArgument();
    createAndCallUF(
        "fooMixed3",
        FormulaType.BooleanType,
        bmgr.makeTrue(),
        imgr.makeNumber(2),
        rmgr.makeNumber(3.33));
  }

  @Test
  public void testDeclareAndCallUFWithBVArgs() {
    requireBitvectors();
    requireIntegers();
    createAndCallUF("fooBV1", FormulaType.getBitvectorTypeWithSize(5), bvmgr.makeBitvector(3, 3L));
    requireBooleanArgument();
    createAndCallUF(
        "fooMixedBV1",
        FormulaType.getBitvectorTypeWithSize(5),
        bmgr.makeTrue(),
        imgr.makeNumber(2),
        bvmgr.makeBitvector(3, 3L));
    createAndCallUF(
        "fooMixedBV2",
        FormulaType.BooleanType,
        bmgr.makeTrue(),
        imgr.makeNumber(2),
        bvmgr.makeBitvector(3, 3L));
  }

  private void requireBooleanArgument() {
    assume()
        .withMessage("Solver %s does not support boolean arguments", solverToUse())
        .that(solver)
        .isNoneOf(Solvers.MATHSAT5, Solvers.PRINCESS);
  }

  /** utility method: create an UF from given arguments and return type and calls it. */
  private void createAndCallUF(
      String name, FormulaType<? extends Formula> retType, Formula... args) {
    Formula f = fmgr.declareAndCallUF(name, retType, args);
    FunctionDeclaration<?> declaration = getDeclaration(f);
    Truth.assertThat(declaration.getName()).isEqualTo(name);
    Formula f2 = mgr.makeApplication(declaration, args);
    Truth.assertThat(f2).isEqualTo(f);
  }

  private FunctionDeclaration<?> getDeclaration(Formula pFormula) {
    assume()
        .withMessage("Solver %s does not support visiters", solverToUse())
        .that(solver)
        .isNotEqualTo(Solvers.BOOLECTOR);
    return mgr.visit(
        pFormula,
        new ExpectedFormulaVisitor<>() {
          @Override
          public FunctionDeclaration<?> visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
            return functionDeclaration;
          }
        });
  }

  private List<Formula> getArguments(Formula pFormula) {
    assume()
        .withMessage("Solver %s does not support visiters", solverToUse())
        .that(solver)
        .isNotEqualTo(Solvers.BOOLECTOR);
    return mgr.visit(
        pFormula,
        new ExpectedFormulaVisitor<>() {
          @Override
          public List<Formula> visitFunction(
              Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
            return args;
          }
        });
  }
}
