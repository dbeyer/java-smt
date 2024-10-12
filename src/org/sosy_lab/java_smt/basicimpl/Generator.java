// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2024 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.basicimpl;

import java.io.IOException;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;
import org.sosy_lab.java_smt.api.BooleanFormula;

/**
 * Assembles the final SMT-LIB2 constraint from the FormulaEnvironment objects generated by the
 * individual Generators.
 */
// TODO Rewrite Generator as a delegate. Or at least make the methods non-static.
// TODO How to split up this class to support multiple provers per context?
public class Generator {
  private Generator() {}

  /** collects assembled SMT-LIB2, its value will be written to Out.smt2. */
  private static StringBuilder lines = new StringBuilder();

  /** holds FunctionEnvironment for each operation that has been executed. */
  private static final List<FunctionEnvironment> executedAggregator = new ArrayList<>();

  /**
   * holds FunctionEnvironment for each variable or function that needs to be declared or defined in
   * SMT-LIB2.
   */
  private static final List<FunctionEnvironment> registeredVariables = new ArrayList<>();

  /** Used to determine what kind of SMT-LIB2 string needs to be assembled. */
  public enum Keyword {
    DIRECT,
    SKIP,
    BOOL,
    INT,
    REAL,
    BITVEC,
    UFFUN,
    ARRAY
  }

  private static boolean loggingEnabled = false;

  // TODO Add an option to set the output path. Better yet, just return the String
  private static final String file = "Out.smt2";

  public static StringBuilder getLines() {
    return lines;
  }

  public static List<FunctionEnvironment> getExecutedAggregator() {
    return executedAggregator;
  }

  public static List<FunctionEnvironment> getRegisteredVariables() {
    return registeredVariables;
  }

  protected static void writeToFile(String line, String fileName) throws IOException {
    try {
      try (Writer fileWriter =
          Files.newBufferedWriter(Path.of(fileName), Charset.defaultCharset())) {
        fileWriter.write(line);
        fileWriter.flush();
      }
    } catch (GeneratorException e) {
      throw new GeneratorException("Could not write to file");
    }
  }

  public static boolean isLoggingEnabled() {
    return loggingEnabled;
  }

  public static void setIsLoggingEnabled(boolean pIsLoggingEnabled) {
    loggingEnabled = pIsLoggingEnabled;
  }

  /**
   * Recursively evaluates a Formula to SMT-LIB2, stops when input is a String.
   *
   * @param constraint Formula or String that is translated to SMT-LIB2
   * @return SMT-LIB2 String that is equivalent to Formula or String input
   */
  protected static String evaluateRecursive(Object constraint) {
    if (constraint instanceof String) {
      return (String) constraint;
    } else {
      Optional<FunctionEnvironment> methodToEvaluate =
          executedAggregator.stream().filter(x -> x.getResult().equals(constraint)).findFirst();
      if (methodToEvaluate.isPresent()
          && !methodToEvaluate.orElseThrow().expressionType.equals(Keyword.DIRECT)) {
        registeredVariables.add(methodToEvaluate.orElseThrow());
      }
      List<Object> evaluatedInputs = new ArrayList<>();
      for (Object value : Objects.requireNonNull(methodToEvaluate).orElseThrow().getInputParams()) {
        String evaluatedInput = evaluateRecursive(value);
        evaluatedInputs.add(evaluatedInput);
      }
      return methodToEvaluate.orElseThrow().getFunctionToString().apply(evaluatedInputs);
    }
  }

  /**
   * This method will assemble a valid SMT-LIB2 String from any given JavaSMT constraint and append
   * it to the StringBuilder 'lines'.
   *
   * @param constraint JavaSMT constraint of type BooleanFormula that will be interpreted as
   *     SMT-LIB2
   */
  public static void assembleConstraint(BooleanFormula constraint) {
    String result = evaluateRecursive(constraint);
    List<FunctionEnvironment> uniqueRegisteredValues =
        registeredVariables.stream().distinct().collect(Collectors.toList());
    String command = "(assert ";
    for (FunctionEnvironment variable : uniqueRegisteredValues) {
      if (variable.expressionType.equals(Keyword.BOOL)) {
        String newEntry = "(declare-const " + variable.inputParams.get(0) + " Bool)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.INT)) {
        String newEntry = "(declare-const " + variable.inputParams.get(0) + " Int)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.REAL)) {
        String newEntry = "(declare-const " + variable.inputParams.get(0) + " Real)\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.BITVEC)) {
        String newEntry =
            "(declare-const "
                + variable.inputParams.get(0)
                + " (_ BitVec "
                + variable.bitVecLength
                + "))\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.ARRAY)) {
        String newEntry =
            "(declare-const "
                + variable.inputParams.get(0)
                + " (Array "
                + variable.arrayIndexType
                + " "
                + variable.arrayValueType
                + "))"
                + "\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
      if (variable.expressionType.equals(Keyword.UFFUN)) {
        String newEntry =
            "(declare-fun "
                + variable.ufName
                + " "
                + variable.ufInputType
                + " "
                + variable.ufOutputType
                + ")"
                + "\n";
        if (lines.indexOf(newEntry) == -1) {
          lines.append(newEntry);
        }
      }
    }
    String smtlib2Result = command + result + ")\n";
    lines.append(smtlib2Result);
  }

  protected static void logPop() {
    lines.append("(pop 1)\n");
  }

  protected static void logPush() {
    lines.append("(push 1)\n");
  }

  /**
   * Adds commands for generating an SMT-LIB2 model and exiting the solver to StringBuilder 'lines'
   * and writes the value of 'lines' into a file named 'Out.smt2'.
   *
   * @throws IOException if writing to file failed
   */
  public static void dumpSMTLIB2() throws IOException {
    String endSMTLIB2 = "(check-sat)\n(get-model)\n(exit)";
    lines.append(endSMTLIB2);
    writeToFile(String.valueOf(lines), file);
    // TODO This deletes the old output. What happens if the method is called twice?
    lines.delete(0, lines.length() - 1);
  }

  public static String getSMTLIB2String() {
    String endSMTLIB2 = "(check-sat)\n(get-model)\n(exit)";
    // FIXME Should we really add this to lines?
    lines.append(endSMTLIB2);
    return "(set-logic AUFLIRA)\n" + lines;
  }

  public static void resetGenerator() {
    lines = new StringBuilder();
    executedAggregator.clear();
    registeredVariables.clear();
  }
}
