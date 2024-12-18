// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.api;

import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import java.util.List;
import java.util.Objects;

/**
 * This class provides a model with concrete evaluations for symbols and formulas from the
 * satisfiable solver environment.
 *
 * <p>This class is an extensions of {@link Evaluator} and provides more features:
 *
 * <ul>
 *   <li>a listing of model assignments, i.e., the user can iterate over all available symbols and
 *       their assignments,
 *   <li>a guaranteed availability even after applying any operation on the original prover stack, i
 *       .e., the model instance stays constant and remains valid for one given satisfiable prover
 *       environment.
 * </ul>
 */
public interface Model extends Evaluator, AutoCloseable {

  /**
   * Build a list of assignments for all values present in the model. The list stays valid after
   * closing the model.
   *
   * <p>The list includes value assignments for...
   *
   * <ul>
   *   <li>all relevant free variables of simple type. If a variable is irrelevant for
   *       satisfiability, it can be <code>null</code> or missing in the iteration.
   *   <li>(nested) arrays with all accesses. If an array access is applied within a quantified
   *       context, some value assignments can be missing in the iteration. Please use a direct
   *       evaluation query to get the evaluation in such a case.
   *   <li>uninterpreted functions with all applications. If an uninterpreted function is applied
   *       within a quantified context, some value assignments can be missing in the iteration.
   *       Please use a direct evaluation query to get the evaluation in such a case.
   * </ul>
   */
  ImmutableList<ValueAssignment> asList() throws InterruptedException, SolverException;

  /**
   * Pretty-printing of the model values.
   *
   * <p>Please only use this method for debugging and not for retrieving relevant information about
   * the model. The returned model representation is not intended for further usage like parsing,
   * because we do not guarantee any specific format, e.g., for arrays and uninterpreted functions,
   * and we allow the SMT solver to include arbitrary additional information about the current
   * solver state, e.g., any available symbol in the solver, even from other provers, and temporary
   * internal symbols.
   */
  @Override
  String toString();

  /**
   * Free resources associated with this model (existing {@link ValueAssignment} instances stay
   * valid, but {@link #evaluate(Formula)} etc. must not be called again).
   */
  @Override
  void close();

  final class ValueAssignment {

    /**
     * the key should be of simple formula-type (Boolean/Integer/Rational/BitVector).
     *
     * <p>For UFs we use the application of the UF with arguments.
     *
     * <p>For arrays we use the selection-statement with an index. We do not support Array theory as
     * {@link #value} during a model evaluation, but we provide assignments like <code>
     * select(arr, 12) := 34</code> where <code>arr</code> itself is a plain symbol (without an
     * explicit const- or zero-based initialization, as done by some SMT solvers).
     */
    private final Formula keyFormula;

    /** the value should be of simple formula-type (Boolean/Integer/Rational/BitVector). */
    private final Formula valueFormula;

    /** the equality of key and value. */
    private final BooleanFormula formula;

    /** the key should be boolean or numeral (Rational/Double/BigInteger/Long/Integer). */
    private final Object value;

    /**
     * arguments can have any type. We would prefer numerals (like value), but we also allow
     * Formulas.
     *
     * <p>For UFs we use the arguments.
     *
     * <p>For arrays we use the index of a selection or an empty list for wildcard-selection, if the
     * whole array is filled with a constant value. In the latter case any additionally given
     * array-assignment overrides the wildcard-selection for the given index. Example: "arr=0,
     * arr[2]=3" corresponds to an array {0,0,3,0,...}.
     */
    private final ImmutableList<Object> argumentsInterpretation;

    /**
     * The name should be a 'useful' identifier for the current assignment.
     *
     * <p>For UFs we use their name without parameters. Parameters are given as {@link
     * #argumentsInterpretation}.
     *
     * <p>For arrays we use the name without any index. The index is given as {@link
     * #argumentsInterpretation}, if required.
     */
    private final String name;

    public ValueAssignment(
        Formula keyFormula,
        Formula valueFormula,
        BooleanFormula formula,
        String name,
        Object value,
        List<?> argumentInterpretation) {

      this.keyFormula = Preconditions.checkNotNull(keyFormula);
      this.valueFormula = Preconditions.checkNotNull(valueFormula);
      this.formula = Preconditions.checkNotNull(formula);
      this.name = Preconditions.checkNotNull(name);
      this.value = Preconditions.checkNotNull(value);
      this.argumentsInterpretation = ImmutableList.copyOf(argumentInterpretation);
    }

    /** The formula AST which is assigned a given value. */
    public Formula getKey() {
      return keyFormula;
    }

    /** The formula AST which is assigned to a given key. */
    public Formula getValueAsFormula() {
      return valueFormula;
    }

    /** The formula AST representing the equality of key and value. */
    public BooleanFormula getAssignmentAsFormula() {
      return formula;
    }

    /** Variable name for variables, function name for UFs, and array name for arrays. */
    public String getName() {
      return name;
    }

    /**
     * Value: see the {@link #evaluate} methods for the possible types.
     *
     * <p>We return only values that can be used in Java, i.e., boolean or numeral values
     * (Rational/Double/BigInteger/Long/Integer).
     */
    public Object getValue() {
      return value;
    }

    /** Interpretation assigned for function arguments. Empty for variables. */
    public ImmutableList<Object> getArgumentsInterpretation() {
      return argumentsInterpretation;
    }

    public boolean isFunction() {
      return !argumentsInterpretation.isEmpty();
    }

    public int getArity() {
      return argumentsInterpretation.size();
    }

    public Object getArgInterpretation(int i) {
      assert i < getArity();
      return argumentsInterpretation.get(i);
    }

    @Override
    public String toString() {
      StringBuilder sb = new StringBuilder().append(name);
      if (!argumentsInterpretation.isEmpty()) {
        sb.append('(');
        Joiner.on(", ").appendTo(sb, argumentsInterpretation);
        sb.append(')');
      }
      return sb.append(": ").append(value).toString();
    }

    @Override
    public boolean equals(Object o) {
      if (o == this) {
        return true;
      }
      if (!(o instanceof ValueAssignment)) {
        return false;
      }
      ValueAssignment other = (ValueAssignment) o;

      // "Key" is purposefully not included in the comparison,
      // name and arguments should be sufficient.
      return name.equals(other.name)
          && value.equals(other.value)
          && argumentsInterpretation.equals(other.argumentsInterpretation);
    }

    @Override
    public int hashCode() {
      return Objects.hash(name, argumentsInterpretation, value);
    }
  }
}
