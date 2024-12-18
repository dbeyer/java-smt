// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.test;

import static com.google.common.truth.Truth.assertThat;
import static com.google.common.truth.Truth.assertWithMessage;
import static com.google.common.truth.TruthJUnit.assume;

import com.google.common.collect.ImmutableMap;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReferenceArray;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.ConfigurationBuilder;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.common.rationals.Rational;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BasicProverEnvironment;
import org.sosy_lab.java_smt.api.BitvectorFormulaManager;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment;
import org.sosy_lab.java_smt.api.OptimizationProverEnvironment.OptStatus;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import org.sosy_lab.java_smt.test.SolverBasedTest0.ParameterizedSolverBasedTest0;

@SuppressWarnings("resource")
@RunWith(Parameterized.class)
public class SolverConcurrencyTest {

  private static final int NUMBER_OF_THREADS = 4;
  private static final int TIMEOUT_SECONDS = 30;

  /**
   * As some Solvers are slower/faster, we choose an appropriate number of formulas to solve here.
   */
  private static final ImmutableMap<Solvers, Integer> INTEGER_FORMULA_GEN =
      ImmutableMap.of(
          Solvers.SMTINTERPOL,
          8,
          Solvers.CVC4,
          12,
          Solvers.MATHSAT5,
          12,
          Solvers.PRINCESS,
          8,
          Solvers.Z3,
          12);

  private static final ImmutableMap<Solvers, Integer> BITVECTOR_FORMULA_GEN =
      ImmutableMap.of(
          Solvers.BOOLECTOR,
          50,
          Solvers.CVC4,
          7,
          Solvers.MATHSAT5,
          50,
          Solvers.PRINCESS,
          5,
          Solvers.Z3,
          40);

  @Parameters(name = "{0}")
  public static Object[] getAllSolvers() {
    return ParameterizedSolverBasedTest0.getAllSolvers();
  }

  @Parameter(0)
  public Solvers solver;

  protected Solvers solverToUse() {
    return solver;
  }

  /**
   * If UnsatisfiedLinkError (wrapped in InvalidConfigurationException) is thrown, abort the test.
   * On some systems (like Windows), some solvers are not available.
   */
  @Before
  public void checkThatSolverIsAvailable() throws InvalidConfigurationException {
    initSolver().close();

    if (System.getProperty("os.name").toLowerCase(Locale.getDefault()).startsWith("win")) {
      assume()
          .withMessage("MathSAT5 is not reentant on Windows")
          .that(solver)
          .isNotEqualTo(Solvers.MATHSAT5);
    }
  }

  private void requireConcurrentMultipleStackSupport() {
    assume()
        .withMessage("Solver does not support concurrent solving in multiple stacks")
        .that(solver)
        .isNoneOf(
            Solvers.SMTINTERPOL,
            Solvers.BITWUZLA,
            Solvers.BOOLECTOR,
            Solvers.OPENSMT, // INFO: OpenSMT does not support concurrent stacks
            Solvers.MATHSAT5,
            Solvers.Z3,
            Solvers.PRINCESS,
            Solvers.YICES2,
            Solvers.CVC5);
  }

  private void requireIntegers() {
    assume()
        .withMessage("Solver does not support integers")
        .that(solver)
        .isNoneOf(Solvers.BOOLECTOR, Solvers.YICES2, Solvers.BITWUZLA);
  }

  private void requireBitvectors() {
    assume()
        .withMessage("Solver does not support bitvectors")
        .that(solver)
        .isNoneOf(Solvers.SMTINTERPOL, Solvers.YICES2, Solvers.OPENSMT);
  }

  private void requireOptimization() {
    assume()
        .withMessage("Solver does not support optimization")
        .that(solver)
        .isNoneOf(
            Solvers.SMTINTERPOL,
            Solvers.BOOLECTOR,
            Solvers.PRINCESS,
            Solvers.CVC4,
            Solvers.CVC5,
            Solvers.YICES2,
            Solvers.BITWUZLA,
            Solvers.OPENSMT);
  }

  /**
   * Test concurrency of integers (while every thread creates its unique context on its own
   * concurrently).
   */
  @Test
  public void testIntConcurrencyWithConcurrentContext() {
    requireIntegers();
    assertConcurrency(
        "testIntConcurrencyWithConcurrentContext",
        () -> {
          SolverContext context = initSolver();
          intConcurrencyTest(context);
          closeSolver(context);
        });
  }

  /**
   * Test concurrency of bitvectors (while every thread creates its unique context on its own
   * concurrently).
   */
  @Test
  public void testBvConcurrencyWithConcurrentContext() {
    requireBitvectors();
    assertConcurrency(
        "testBvConcurrencyWithConcurrentContext",
        () -> {
          SolverContext context = initSolver();
          bvConcurrencyTest(context);
          closeSolver(context);
        });
  }

  /**
   * Create 1 context and all managers + some basic formulas (e.g. true, false). Then, test basic
   * checks (isFalse(), isTrue()) und usage of these managers in a different thread. This failed for
   * a solver in the past, even when all other tests in this class worked!
   */
  @Test
  public void testConcurrencyWithConcurrentManagers() throws InvalidConfigurationException {
    ConcurrentLinkedQueue<ContextAndFormula> contextAndFormulaList = new ConcurrentLinkedQueue<>();
    SolverContext context = initSolver();
    FormulaManager mgr = context.getFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
    BooleanFormula tru = bmgr.makeTrue();
    BooleanFormula fls = bmgr.makeFalse();
    contextAndFormulaList.add(new ContextAndFormula(context, tru));
    contextAndFormulaList.add(new ContextAndFormula(context, fls));
    BooleanFormula var = bmgr.makeVariable("var");
    BooleanFormula trueFormula = bmgr.not(bmgr.and(var, bmgr.not(var)));
    BooleanFormula falseFormula = bmgr.and(var, bmgr.not(var));
    contextAndFormulaList.add(new ContextAndFormula(context, trueFormula));
    contextAndFormulaList.add(new ContextAndFormula(context, falseFormula));
    // Check that its correctly true/false in the manager
    checkBooleanFormulas(bmgr, tru, fls, trueFormula, falseFormula);

    assertConcurrency(
        "testManagerUsageInDifferentThreads",
        () -> {
          ContextAndFormula[] ctxAndFormulas =
              contextAndFormulaList.toArray(new ContextAndFormula[0]);
          SolverContext threadContext = ctxAndFormulas[0].getContext();
          FormulaManager threadMgr = threadContext.getFormulaManager();
          BooleanFormulaManager threadBmgr = threadMgr.getBooleanFormulaManager();
          BooleanFormula threadTrue = ctxAndFormulas[0].getFormula();
          BooleanFormula threadFalse = ctxAndFormulas[1].getFormula();
          BooleanFormula threadTrueFormula = ctxAndFormulas[2].getFormula();
          BooleanFormula threadFalseFormula = ctxAndFormulas[3].getFormula();

          checkBooleanFormulas(
              threadBmgr, threadTrue, threadFalse, threadTrueFormula, threadFalseFormula);
        });
  }

  /*
   * Check the entered BooleanFormulas in the BooleanFormulaManager for true/false.
   */
  private void checkBooleanFormulas(
      BooleanFormulaManager pBmgr,
      BooleanFormula pTru,
      BooleanFormula pFls,
      BooleanFormula pTrueFormula,
      BooleanFormula pFalseFormula) {
    assertThat(pBmgr.isFalse(pTru)).isFalse();
    assertThat(pBmgr.isTrue(pTru)).isTrue();

    assertThat(pBmgr.isFalse(pFls)).isTrue();
    assertThat(pBmgr.isTrue(pFls)).isFalse();

    assertThat(pBmgr.isFalse(pTrueFormula)).isFalse();

    assertThat(pBmgr.isTrue(pFalseFormula)).isFalse();
  }

  /** Helperclass to pack a SolverContext together with a Formula. */
  private static class ContextAndFormula {
    private final SolverContext context;
    private final BooleanFormula formula;

    private ContextAndFormula(SolverContext context, BooleanFormula formula) {
      this.context = context;
      this.formula = formula;
    }

    SolverContext getContext() {
      return context;
    }

    BooleanFormula getFormula() {
      return formula;
    }
  }

  /**
   * Test translation of formulas used on distinct contexts to a new, unrelated context. Every
   * thread creates a context, generates a formula, those are collected and handed back to the main
   * thread where they are translated to the main-thread context, anded and asserted.
   */
  @Test
  public void testFormulaTranslationWithConcurrentContexts()
      throws InvalidConfigurationException, InterruptedException, SolverException {
    requireIntegers();
    // CVC4 does not support parsing and therefore no translation.
    // Princess has a wierd bug
    // TODO: Look into the Princess problem
    assume()
        .withMessage("Solver does not support translation of formulas")
        .that(solver)
        .isNoneOf(Solvers.CVC4, Solvers.PRINCESS, Solvers.CVC5);

    ConcurrentLinkedQueue<ContextAndFormula> contextAndFormulaList = new ConcurrentLinkedQueue<>();

    assertConcurrency(
        "testFormulaTranslationWithConcurrentContexts",
        () -> {
          SolverContext context = initSolver();
          FormulaManager mgr = context.getFormulaManager();
          IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
          BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
          HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
          BooleanFormula threadFormula = gen.generate(INTEGER_FORMULA_GEN.getOrDefault(solver, 9));
          // We need to know the context from which the formula was created
          contextAndFormulaList.add(new ContextAndFormula(context, threadFormula));
        });

    assertThat(contextAndFormulaList).hasSize(NUMBER_OF_THREADS);
    SolverContext context = initSolver();
    FormulaManager mgr = context.getFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
    List<BooleanFormula> translatedFormulas = new ArrayList<>();

    for (ContextAndFormula currentContAndForm : contextAndFormulaList) {
      SolverContext threadedContext = currentContAndForm.getContext();
      BooleanFormula threadedFormula = currentContAndForm.getFormula();
      BooleanFormula translatedFormula =
          mgr.translateFrom(threadedFormula, threadedContext.getFormulaManager());
      translatedFormulas.add(translatedFormula);
      threadedContext.close();
    }
    assertThat(translatedFormulas).hasSize(NUMBER_OF_THREADS);
    BooleanFormula finalFormula = bmgr.and(translatedFormulas);
    try (BasicProverEnvironment<?> stack = context.newProverEnvironment()) {
      stack.push(finalFormula);

      assertWithMessage(
              "Test testFormulaTranslationWithConcurrentContexts() failed isUnsat() in the main"
                  + " thread.")
          .that(stack.isUnsat())
          .isTrue();
    }
  }

  /** Test concurrency with already present and unique context per thread. */
  @SuppressWarnings("resource")
  @Test
  public void testIntConcurrencyWithoutConcurrentContext() throws InvalidConfigurationException {
    requireIntegers();

    assume()
        .withMessage("Solver does not support concurrency without concurrent context.")
        .that(solver)
        .isNotEqualTo(Solvers.CVC5);

    ConcurrentLinkedQueue<SolverContext> contextList = new ConcurrentLinkedQueue<>();
    // Initialize contexts before using them in the threads
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      contextList.add(initSolver());
    }
    assertConcurrency(
        "testIntConcurrencyWithoutConcurrentContext",
        () -> {
          SolverContext context = contextList.poll();
          intConcurrencyTest(context);
          closeSolver(context);
        });
  }

  /** Test concurrency with already present and unique context per thread. */
  @SuppressWarnings("resource")
  @Test
  public void testBvConcurrencyWithoutConcurrentContext() throws InvalidConfigurationException {
    requireBitvectors();

    assume()
        .withMessage("Solver does not support concurrency without concurrent context.")
        .that(solver)
        .isNotEqualTo(Solvers.CVC5);

    ConcurrentLinkedQueue<SolverContext> contextList = new ConcurrentLinkedQueue<>();
    // Initialize contexts before using them in the threads
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      contextList.add(initSolver());
    }
    assertConcurrency(
        "testBvConcurrencyWithoutConcurrentContext",
        () -> {
          SolverContext context = contextList.poll();
          bvConcurrencyTest(context);
          closeSolver(context);
        });
  }

  @Test
  public void testConcurrentOptimization() {
    requireOptimization();

    assume()
        .withMessage("Solver does support optimization, but is not yet reentrant.")
        .that(solver)
        .isNotEqualTo(Solvers.MATHSAT5);

    assertConcurrency(
        "testConcurrentOptimization",
        () -> {
          SolverContext context = initSolver("solver.mathsat5.loadOptimathsat5", "true");
          optimizationTest(context);
          closeSolver(context);
        });
  }

  /**
   * Test solving of large formula on concurrent stacks in one context (Stacks are not created in
   * the Threads).
   */
  @Test
  public void testConcurrentIntegerStack()
      throws InvalidConfigurationException, InterruptedException, SolverException {
    requireIntegers();
    requireConcurrentMultipleStackSupport();
    SolverContext context = initSolver();
    FormulaManager mgr = context.getFormulaManager();
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);

    ConcurrentLinkedQueue<BasicProverEnvironment<?>> proverList = new ConcurrentLinkedQueue<>();
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      BooleanFormula instance = gen.generate(INTEGER_FORMULA_GEN.getOrDefault(solver, 9));
      BasicProverEnvironment<?> pe = context.newProverEnvironment();
      pe.push(instance);
      proverList.add(pe);
    }
    assertConcurrency(
        "testConcurrentStack",
        () -> {
          BasicProverEnvironment<?> stack = proverList.poll();
          assertWithMessage("Solver %s failed a concurrency test", solverToUse())
              .that(stack.isUnsat())
              .isTrue();
        });
    closeSolver(context);
  }

  /**
   * Test solving of large formula on concurrent stacks in one context (Stacks are not created in
   * the Threads).
   */
  @Test
  public void testConcurrentBitvectorStack()
      throws InvalidConfigurationException, InterruptedException, SolverException {
    requireBitvectors();
    requireConcurrentMultipleStackSupport();
    SolverContext context = initSolver();
    FormulaManager mgr = context.getFormulaManager();
    BitvectorFormulaManager bvmgr = mgr.getBitvectorFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);

    ConcurrentLinkedQueue<BasicProverEnvironment<?>> proverList = new ConcurrentLinkedQueue<>();
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      BooleanFormula instance = gen.generate(INTEGER_FORMULA_GEN.getOrDefault(solver, 9));
      BasicProverEnvironment<?> pe = context.newProverEnvironment();
      pe.push(instance);
      proverList.add(pe);
    }
    assertConcurrency(
        "testConcurrentStack",
        () -> {
          BasicProverEnvironment<?> stack = proverList.poll();
          assertWithMessage("Solver %s failed a concurrency test", solverToUse())
              .that(stack.isUnsat())
              .isTrue();
        });
    closeSolver(context);
  }

  /**
   * Uses HardBitvectorFormulaGenerator for longer test-cases to assess concurrency problems. Length
   * is very solver depended, so make sure you choose an appropriate number for the used solver.
   * Make sure to not call this method with a SolverContext that does not support bitvectors! (No
   * requireBitvector() because the exceptionList would collect it and throw an exception failing
   * the test!).
   *
   * @param context used context for the test-thread (Do not reuse contexts!)
   */
  private void bvConcurrencyTest(SolverContext context)
      throws SolverException, InterruptedException {
    FormulaManager mgr = context.getFormulaManager();
    BitvectorFormulaManager bvmgr = mgr.getBitvectorFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();

    HardBitvectorFormulaGenerator gen = new HardBitvectorFormulaGenerator(bvmgr, bmgr);
    BooleanFormula instance = gen.generate(BITVECTOR_FORMULA_GEN.getOrDefault(solver, 9));
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(instance);
      assertWithMessage("Solver %s failed a concurrency test", solverToUse())
          .that(pe.isUnsat())
          .isTrue();
    }
  }

  /**
   * Uses HardIntegerFormulaGenerator for longer test-cases to assess concurrency problems. Length
   * is very solver depended, so make sure you choose an appropriate number for the used solver.
   * Make sure to not call this method with a SolverContext that does not support integers! (No
   * requireIntegers() because the exceptionList would collect it and throw an exception failing the
   * test!).
   *
   * @param context used context for the test-thread (Do not reuse contexts unless you know what you
   *     are doing!)
   */
  private void intConcurrencyTest(SolverContext context)
      throws SolverException, InterruptedException {
    FormulaManager mgr = context.getFormulaManager();
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();

    HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
    BooleanFormula instance = gen.generate(INTEGER_FORMULA_GEN.getOrDefault(solver, 9));
    try (BasicProverEnvironment<?> pe = context.newProverEnvironment()) {
      pe.push(instance);
      assertWithMessage("Solver %s failed a concurrency test", solverToUse())
          .that(pe.isUnsat())
          .isTrue();
    }
  }

  /**
   * Test that starts multiple threads that solve several problems such that they tend to not finish
   * at the same time. Once a problem finishes, the formula is then send to another thread (with the
   * context) and the sending thread starts solving a new problem (either send to it, or by
   * generating a new one). The thread that just got the formula + context translates the formula
   * into its own context once its finished (and send its formula to another context) and starts
   * solving the formula it got send. This test is supposed to show the feasability of translating
   * formulas with contexts in (concurrent) use.
   */
  @Test
  public void continuousRunningThreadFormulaTransferTranslateTest() {
    requireIntegers();
    // CVC4 does not support parsing and therefore no translation.
    // Princess has a wierd bug
    // TODO: Look into the Princess problem
    assume()
        .withMessage("Solver does not support translation of formulas")
        .that(solver)
        .isNoneOf(Solvers.CVC4, Solvers.CVC5, Solvers.PRINCESS);

    // This is fine! We might access this more than once at a time,
    // but that gives only access to the bucket, which is threadsafe.
    AtomicReferenceArray<BlockingQueue<ContextAndFormula>> bucketQueue =
        new AtomicReferenceArray<>(NUMBER_OF_THREADS);

    // Init as many buckets as there are threads; each bucket generates an initial formula (such
    // that they are differently hard to solve) depending on the uniqueId
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      BlockingQueue<ContextAndFormula> bucket = new LinkedBlockingQueue<>(NUMBER_OF_THREADS);
      bucketQueue.set(i, bucket);
    }

    // Bind unique IDs to each thread with a (threadsafe) unique ID generator
    final UniqueIdGenerator idGenerator = new UniqueIdGenerator();

    // Take the formula from the bucket of itself, solve it, once solved give the formula to the
    // bucket of the next thread (have a counter for in which bucket we transferred the formula and
    // +1 the counter)
    assertConcurrency(
        "continuousRunningThreadFormulaTransferTranslateTest",
        () -> {
          // Start the threads such that they each get a unqiue id
          final int id = idGenerator.getFreshId();
          int nextBucket = (id + 1) % NUMBER_OF_THREADS;
          final BlockingQueue<ContextAndFormula> ownBucket = bucketQueue.get(id);
          SolverContext context = initSolver();
          FormulaManager mgr = context.getFormulaManager();
          IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
          BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
          HardIntegerFormulaGenerator gen = new HardIntegerFormulaGenerator(imgr, bmgr);
          BooleanFormula threadFormula =
              gen.generate(INTEGER_FORMULA_GEN.getOrDefault(solver, 9) - id);
          try (BasicProverEnvironment<?> stack = context.newProverEnvironment()) {
            // Repeat till the bucket counter reaches itself again
            while (nextBucket != id) {
              stack.push(threadFormula);

              assertWithMessage(
                      "Test continuousRunningThreadFormulaTransferTranslateTest() "
                          + "failed isUnsat() in thread with id: "
                          + id
                          + ".")
                  .that(stack.isUnsat())
                  .isTrue();

              // Take another formula from its own bucket or wait for one.
              bucketQueue.get(nextBucket).add(new ContextAndFormula(context, threadFormula));

              // Translate the formula into its own context and start solving
              ContextAndFormula newFormulaAndContext = ownBucket.take();
              threadFormula =
                  mgr.translateFrom(
                      newFormulaAndContext.getFormula(),
                      newFormulaAndContext.getContext().getFormulaManager());

              nextBucket = (nextBucket + 1) % NUMBER_OF_THREADS;
            }
          }
        });
  }

  // As optimization is not used much at the moment this small test is ok
  private void optimizationTest(SolverContext context)
      throws InterruptedException, SolverException {
    FormulaManager mgr = context.getFormulaManager();
    IntegerFormulaManager imgr = mgr.getIntegerFormulaManager();
    BooleanFormulaManager bmgr = mgr.getBooleanFormulaManager();
    try (OptimizationProverEnvironment prover =
        context.newOptimizationProverEnvironment(ProverOptions.GENERATE_MODELS)) {

      IntegerFormula x = imgr.makeVariable("x");
      IntegerFormula y = imgr.makeVariable("y");
      IntegerFormula obj = imgr.makeVariable("obj");

      prover.addConstraint(
          bmgr.and(
              imgr.lessOrEquals(x, imgr.makeNumber(10)),
              imgr.lessOrEquals(y, imgr.makeNumber(15)),
              imgr.equal(obj, imgr.add(x, y)),
              imgr.greaterOrEquals(imgr.subtract(x, y), imgr.makeNumber(1))));
      int handle = prover.maximize(obj);

      // Maximize for x.
      OptStatus response = prover.check();
      assertThat(response).isEqualTo(OptStatus.OPT);

      // Check the value.
      assertThat(prover.upper(handle, Rational.ZERO)).hasValue(Rational.ofString("19"));

      try (Model model = prover.getModel()) {
        BigInteger xValue = model.evaluate(x);
        BigInteger objValue = model.evaluate(obj);
        BigInteger yValue = model.evaluate(y);

        assertThat(objValue).isEqualTo(BigInteger.valueOf(19));
        assertThat(xValue).isEqualTo(BigInteger.valueOf(10));
        assertThat(yValue).isEqualTo(BigInteger.valueOf(9));
      }
    }
  }

  /**
   * Creates and returns a completely new SolverContext for the currently used solver (We need this
   * to get more than one Context in 1 method in a controlled way).
   *
   * @param additionalOptions a list of pairs (key, value) for creating a new solver context.
   * @return new and unique SolverContext for current solver (Parameter(0))
   */
  private SolverContext initSolver(String... additionalOptions)
      throws InvalidConfigurationException {
    try {
      ConfigurationBuilder options =
          Configuration.builder().setOption("solver.solver", solverToUse().toString());
      for (int i = 0; i < additionalOptions.length; i += 2) {
        options.setOption(additionalOptions[i], additionalOptions[i + 1]);
      }
      Configuration config = options.build();
      LogManager logger = LogManager.createTestLogManager();
      ShutdownNotifier shutdownNotifier = ShutdownManager.create().getNotifier();

      SolverContextFactory factory = new SolverContextFactory(config, logger, shutdownNotifier);
      return factory.generateContext();
    } catch (InvalidConfigurationException e) {
      assume()
          .withMessage(e.getMessage())
          .that(e)
          .hasCauseThat()
          .isNotInstanceOf(UnsatisfiedLinkError.class);
      throw e;
    }
  }

  private void closeSolver(SolverContext context) {
    if (context != null) {
      context.close();
    }
  }

  /**
   * Synchronizes start and stop of a concurrency test with NUMBER_OF_THREADS threads. This method
   * will make sure that all exceptions are collected and assessed at the end, as well as stop the
   * execution after TIMEOUT_SECONDS seconds in case of a deadlock or long calculation.
   *
   * @param runnable A Runnable to be tested, make sure that it can be executed several times in
   *     parallel, i.e. no internal state except the solver itself.
   * @param testName Name of the test for accurate error messages
   */
  private static void assertConcurrency(String testName, Run runnable) {
    final ExecutorService threadPool = Executors.newFixedThreadPool(NUMBER_OF_THREADS);
    final List<Throwable> exceptionsList = Collections.synchronizedList(new ArrayList<>());

    // Waits for all threads to be started
    final CountDownLatch allExecutorThreadsReady = new CountDownLatch(NUMBER_OF_THREADS);
    // Syncs start of tests after all threads are already created
    final CountDownLatch afterInitBlocker = new CountDownLatch(1);
    // Syncs end of tests (And prevents Deadlocks in test-threads etc.)
    final CountDownLatch allDone = new CountDownLatch(NUMBER_OF_THREADS);
    for (int i = 0; i < NUMBER_OF_THREADS; i++) {
      @SuppressWarnings("unused")
      Future<?> future =
          threadPool.submit(
              () -> {
                allExecutorThreadsReady.countDown();
                try {
                  afterInitBlocker.await();
                  runnable.run();
                } catch (Throwable e) {
                  exceptionsList.add(e);
                } finally {
                  allDone.countDown();
                }
              });
    }
    try {
      assertWithMessage("Timeout initializing the Threads for " + testName)
          .that(allExecutorThreadsReady.await(NUMBER_OF_THREADS * 20, TimeUnit.MILLISECONDS))
          .isTrue();
      afterInitBlocker.countDown();
      assertWithMessage("Timeout in " + testName)
          .that(allDone.await(TIMEOUT_SECONDS, TimeUnit.SECONDS))
          .isTrue();
    } catch (Throwable e) {
      exceptionsList.add(e);
    } finally {
      threadPool.shutdownNow();
    }
    var exceptionMessages =
        exceptionsList.stream()
            .map(
                ex ->
                    String.format(
                        "%s (%s): %s",
                        ex.getClass(), ex.getMessage(), Arrays.toString(ex.getStackTrace())));
    assertWithMessage("Test %s failed with exception(s): %s", testName, exceptionMessages)
        .that(exceptionsList)
        .isEmpty();
  }

  /** just a small lambda-compatible interface. */
  private interface Run {
    void run() throws SolverException, InterruptedException, InvalidConfigurationException;
  }
}
