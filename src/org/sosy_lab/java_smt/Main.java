package org.sosy_lab.java_smt;/*
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

import ap.Prover;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import javax.script.ScriptEngine;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.*;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.*;
import java.io.*;
import org.sosy_lab.java_smt.utils.Generators.Generator;
import org.sosy_lab.java_smt.utils.Generators.UniversalModel;
import org.sosy_lab.java_smt.utils.Parsers.*;

public class Main {
  public static void main(String[] args)
      throws InvalidConfigurationException, InterruptedException, IOException, SolverException {
    String[] cmdLineArguments = new String[1];
    cmdLineArguments[0] = "--solver.generateSMTLIB2=true";
    Configuration config = Configuration.fromCmdLineArguments(cmdLineArguments);
    LogManager logger = BasicLogManager.create(config);
    ShutdownManager shutdown = ShutdownManager.create();
    SolverContext context =
        SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
            Solvers.MATHSAT5);
    FormulaManager fmgr = context.getFormulaManager();
    BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
    IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
    BitvectorFormulaManager bimgr = fmgr.getBitvectorFormulaManager();
    UFManager umgr =  fmgr.getUFManager();

    BooleanFormula actualFormula = bmgr.makeVariable("a");



    try (ProverEnvironment prover =
             context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
      prover.addConstraint(actualFormula);

      boolean isUnsat = prover.isUnsat();
      if (!isUnsat) {
        Model model = prover.getModel();
        //Object value = model.evaluate(expectedFormula);
        //System.out.println(value);

      }
      Generator.dumpSMTLIB2();
    } catch (SolverException e) {
      throw new RuntimeException(e);
    }
  }
}