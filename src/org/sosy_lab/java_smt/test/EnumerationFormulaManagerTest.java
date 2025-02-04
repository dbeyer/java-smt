// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static junit.framework.TestCase.assertEquals;
import static org.junit.Assert.assertThrows;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.EnumerationFormula;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType.EnumerationFormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.TraversalProcess;

public class EnumerationFormulaManagerTest extends SolverBasedTest0.ParameterizedSolverBasedTest0 {

  @Before
  public void init() {
    requireEnumeration();
  }

  @Test
  public void testEnumerationDeclaration() {
    Set<String> colors = Sets.newHashSet("Blue", "White");
    EnumerationFormulaType colorType = emgr.declareEnumeration("Color", "Blue", "White");
    assertEquals("Color", colorType.getName());
    assertEquals(colors, colorType.getElements());

    Set<String> shapes = Sets.newHashSet("Circle", "Square", "Triangle");
    EnumerationFormulaType shapeType = emgr.declareEnumeration("Shape", shapes);
    assertEquals("Shape", shapeType.getName());
    assertEquals(shapes, shapeType.getElements());

    assertThat(colors).isNotEqualTo(shapes);
  }

  @Test
  public void testType() {
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorM", "Blue", "White");
    EnumerationFormula blue = emgr.makeConstant("Blue", colorType);
    EnumerationFormula varColor = emgr.makeVariable("varColor", colorType);

    assertEquals(colorType, mgr.getFormulaType(blue));
    assertEquals(colorType, mgr.getFormulaType(varColor));
  }

  @Test
  public void testRepeatedEnumerationDeclaration() {
    Set<String> colors = Sets.newHashSet("Blue", "White");
    Set<String> otherColors = Sets.newHashSet("Blue", "White", "Red");
    EnumerationFormulaType colorType = emgr.declareEnumeration("Color", colors);

    // same type again is allowed
    EnumerationFormulaType identicalColorType = emgr.declareEnumeration("Color", colors);
    assertEquals("Color", identicalColorType.getName());
    assertEquals(colors, identicalColorType.getElements());
    assertEquals(colorType, identicalColorType);

    // distinct type with same name is not allowed
    assertThrows(
        IllegalArgumentException.class, () -> emgr.declareEnumeration("Color", otherColors));

    if (solverToUse() == Solvers.MATHSAT5) {
      assertThrows(
          IllegalArgumentException.class, () -> emgr.declareEnumeration("SameColor", colors));
    } else {
      // different type with same elements is allowed
      EnumerationFormulaType sameColorType = emgr.declareEnumeration("SameColor", colors);
      assertEquals("SameColor", sameColorType.getName());
      assertEquals(colors, sameColorType.getElements());

      // different type with same elements is allowed
      EnumerationFormulaType otherColorType = emgr.declareEnumeration("OtherColor", otherColors);
      assertThat(otherColorType.getName()).isEqualTo("OtherColor");
      assertThat(otherColorType.getElements()).isEqualTo(otherColors);
    }
  }

  @Test
  public void testTooManyDistinctValues() throws SolverException, InterruptedException {
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorA", "Blue", "White");
    EnumerationFormula color1 = emgr.makeVariable("first", colorType);
    EnumerationFormula color2 = emgr.makeVariable("second", colorType);
    EnumerationFormula color3 = emgr.makeVariable("third", colorType);

    // there are two colors, so there can be two distinct assignments.
    assertThatFormula(bmgr.not(emgr.equivalence(color1, color2))).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(color2, color3))).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(color3, color1))).isSatisfiable();

    // there are only two colors, so there can not be three distinct assignments.
    assertThatFormula(
            bmgr.and(
                bmgr.not(emgr.equivalence(color1, color2)),
                bmgr.not(emgr.equivalence(color2, color3)),
                bmgr.not(emgr.equivalence(color3, color1))))
        .isUnsatisfiable();
  }

  @Test
  public void testConstants() throws SolverException, InterruptedException {
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorB", "Blue", "White");
    EnumerationFormula blue = emgr.makeConstant("Blue", colorType);
    EnumerationFormula white = emgr.makeConstant("White", colorType);
    EnumerationFormula var = emgr.makeVariable("var", colorType);

    assertThatFormula(emgr.equivalence(blue, var)).isSatisfiable();
    assertThatFormula(emgr.equivalence(white, var)).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(blue, var))).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(white, var))).isSatisfiable();
    assertThatFormula(bmgr.not(emgr.equivalence(blue, white))).isSatisfiable();

    // there are only two colors, so is no third option.
    assertThatFormula(
            bmgr.or(bmgr.not(emgr.equivalence(blue, var)), bmgr.not(emgr.equivalence(white, var))))
        .isSatisfiable();
    assertThatFormula(bmgr.or(emgr.equivalence(blue, var), emgr.equivalence(white, var)))
        .isSatisfiable();
    assertThatFormula(
            bmgr.and(bmgr.not(emgr.equivalence(blue, var)), bmgr.not(emgr.equivalence(white, var))))
        .isUnsatisfiable();
    assertThatFormula(bmgr.and(emgr.equivalence(blue, var), emgr.equivalence(white, var)))
        .isUnsatisfiable();
  }

  @Test
  public void testIncompatibleEnumeration() {
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorC", "Blue", "White");
    EnumerationFormulaType shapeType =
        emgr.declareEnumeration("ShapeC", "Circle", "Rectangle", "Triangle");

    EnumerationFormula blue = emgr.makeConstant("Blue", colorType);
    EnumerationFormula varColor = emgr.makeVariable("varColor", colorType);

    EnumerationFormula circle = emgr.makeConstant("Circle", shapeType);
    EnumerationFormula varShape = emgr.makeVariable("varShape", shapeType);

    assertThrows(IllegalArgumentException.class, () -> emgr.equivalence(blue, varShape));
    assertThrows(IllegalArgumentException.class, () -> emgr.equivalence(circle, varColor));
    assertThrows(IllegalArgumentException.class, () -> emgr.equivalence(varColor, varShape));
    assertThrows(IllegalArgumentException.class, () -> emgr.equivalence(blue, circle));
  }

  private static class ConstantsVisitor extends DefaultFormulaVisitor<TraversalProcess> {

    final Set<String> constants = new HashSet<>();
    final Set<FunctionDeclarationKind> functions = new HashSet<>();

    @Override
    protected TraversalProcess visitDefault(Formula f) {
      return TraversalProcess.CONTINUE;
    }

    @Override
    public TraversalProcess visitConstant(Formula f, Object value) {
      constants.add((String) value);
      return visitDefault(f);
    }

    @Override
    public TraversalProcess visitFunction(
        Formula f, List<Formula> args, FunctionDeclaration<?> functionDeclaration) {
      functions.add(functionDeclaration.getKind());
      return visitDefault(f);
    }
  }

  @Test
  public void testVisitor() {
    requireVisitor();

    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorC", "Blue", "White");
    EnumerationFormula blue = emgr.makeConstant("Blue", colorType);
    EnumerationFormula varColor = emgr.makeVariable("varColor", colorType);
    BooleanFormula eq = emgr.equivalence(blue, varColor);

    assertThat(mgr.extractVariables(varColor)).containsExactly("varColor", varColor);
    assertThat(mgr.extractVariables(eq)).containsExactly("varColor", varColor);
    assertThat(mgr.extractVariablesAndUFs(varColor)).containsExactly("varColor", varColor);
    assertThat(mgr.extractVariablesAndUFs(eq)).containsExactly("varColor", varColor);

    ConstantsVisitor visitor1 = new ConstantsVisitor();
    mgr.visitRecursively(blue, visitor1);
    assertThat(visitor1.functions).isEmpty();
    assertThat(visitor1.constants).containsExactly("Blue");

    ConstantsVisitor visitor2 = new ConstantsVisitor();
    mgr.visitRecursively(eq, visitor2);
    assertThat(visitor2.functions).containsExactly(FunctionDeclarationKind.EQ);
    assertThat(visitor2.constants).containsExactly("Blue");
  }

  @Test
  public void testModel() throws SolverException, InterruptedException {
    EnumerationFormulaType colorType = emgr.declareEnumeration("ColorM", "Blue", "White");
    EnumerationFormula blue = emgr.makeConstant("Blue", colorType);
    EnumerationFormula white = emgr.makeConstant("White", colorType);
    EnumerationFormula varColor = emgr.makeVariable("varColor", colorType);

    EnumerationFormulaType shapeType =
        emgr.declareEnumeration("ShapeM", "Circle", "Reactangle", "Triangle");
    EnumerationFormula triangle = emgr.makeConstant("Triangle", shapeType);
    EnumerationFormula varShape = emgr.makeVariable("varShape", shapeType);

    evaluateInModel(
        emgr.equivalence(blue, varColor),
        varColor,
        Lists.newArrayList("Blue"),
        Lists.newArrayList(blue));

    evaluateInModel(
        bmgr.not(emgr.equivalence(blue, varColor)),
        varColor,
        Lists.newArrayList("White"),
        Lists.newArrayList(white));

    evaluateInModel(
        bmgr.and(emgr.equivalence(blue, varColor), emgr.equivalence(triangle, varShape)),
        varColor,
        Lists.newArrayList("Blue"),
        Lists.newArrayList(blue));

    evaluateInModel(
        bmgr.and(emgr.equivalence(blue, varColor), emgr.equivalence(triangle, varShape)),
        varShape,
        Lists.newArrayList("Triangle"),
        Lists.newArrayList(triangle));
  }
}
