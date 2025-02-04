// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static com.google.common.base.Preconditions.checkArgument;
import static scala.collection.JavaConverters.asJava;
import static scala.collection.JavaConverters.collectionAsScalaIterableConverter;

import ap.api.SimpleAPI;
import ap.parameters.GlobalSettings;
import ap.parser.BooleanCompactifier;
import ap.parser.Environment.EnvironmentException;
import ap.parser.IAtom;
import ap.parser.IConstant;
import ap.parser.IExpression;
import ap.parser.IFormula;
import ap.parser.IFunApp;
import ap.parser.IFunction;
import ap.parser.IIntFormula;
import ap.parser.IPlus;
import ap.parser.ITerm;
import ap.parser.ITermITE;
import ap.parser.ITimes;
import ap.parser.Parser2InputAbsy.TranslationException;
import ap.parser.PartialEvaluator;
import ap.parser.SMTLineariser;
import ap.parser.SMTParser2InputAbsy.SMTFunctionType;
import ap.parser.SMTTypes.SMTType;
import ap.terfor.ConstantTerm;
import ap.terfor.preds.Predicate;
import ap.theories.arrays.ExtArray;
import ap.theories.arrays.ExtArray.ArraySort;
import ap.theories.bitvectors.ModuloArithmetic;
import ap.theories.rationals.Rationals$;
import ap.theories.strings.StringTheory;
import ap.types.Sort;
import ap.types.Sort$;
import ap.types.Sort.MultipleValueBool$;
import ap.util.Debug;
import com.google.common.base.Joiner;
import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import com.google.common.io.Files;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Collectors;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.sosy_lab.common.Appender;
import org.sosy_lab.common.Appenders;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.FileOption;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.configuration.Option;
import org.sosy_lab.common.configuration.Options;
import org.sosy_lab.common.io.PathCounterTemplate;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.basicimpl.FormulaCreator;
import ostrich.OFlags;
import ostrich.OstrichStringTheory;
import scala.Tuple2;
import scala.Tuple4;
import scala.collection.immutable.Seq;

/**
 * This is a Wrapper around Princess. This Wrapper allows to set a logfile for all Smt-Queries
 * (default "princess.###.smt2"). It also manages the "shared variables": each variable is declared
 * for all stacks.
 */
@Options(prefix = "solver.princess")
class PrincessEnvironment {

  @Option(
      secure = true,
      description =
          "The number of atoms a term has to have before"
              + " it gets abbreviated if there are more identical terms.")
  private int minAtomsForAbbreviation = 100;

  @Option(
      secure = true,
      description =
          "Enable additional assertion checks within Princess. "
              + "The main usage is debugging. This option can cause a performance overhead.")
  private boolean enableAssertions = false;

  public static final Sort BOOL_SORT = Sort$.MODULE$.Bool();
  public static final Sort INTEGER_SORT = Sort.Integer$.MODULE$;
  public static final Sort NAT_SORT = Sort.Nat$.MODULE$;

  static final StringTheory stringTheory =
      new OstrichStringTheory(
          toSeq(new ArrayList<>()),
          new OFlags(
              /* OFlag default values:
               * -- Pre-image specific options
               * eagerAutomataOperations : false,
               * measureTimes            : false,
               * useLength               : OFlags.LengthOptions.Auto,
               * useParikhConstraints    : true,
               * minimizeAutomata        : false,
               * forwardPropagation      : false,
               * backwardPropagation     : true,
               * nielsenSplitter         : true,
               * regexTranslator         : OFlags.RegexTranslator.Hybrid,
               */
              OFlags.$lessinit$greater$default$1(),
              OFlags.$lessinit$greater$default$2(),
              OFlags.$lessinit$greater$default$3(),
              OFlags.$lessinit$greater$default$4(),
              OFlags.$lessinit$greater$default$5(),
              OFlags.$lessinit$greater$default$6(),
              OFlags.$lessinit$greater$default$7(),
              OFlags.$lessinit$greater$default$8(),
              OFlags.$lessinit$greater$default$9(),
              /* -- Options for the cost-enriched-automata solver
               * ceaBackend              : OFlags.CEABackend.Unary,
               * useCostEnriched         : false,
               * debug                   : false,
               * underApprox             : true,
               * underApproxBound        : 15,
               * simplifyAut             : true
               */
              OFlags.$lessinit$greater$default$10(),
              OFlags.$lessinit$greater$default$11(),
              OFlags.$lessinit$greater$default$12(),
              OFlags.$lessinit$greater$default$13(),
              OFlags.$lessinit$greater$default$14(),
              OFlags.$lessinit$greater$default$15()));
  public static final Sort STRING_SORT = stringTheory.StringSort();
  public static final Sort REGEX_SORT = stringTheory.RegexSort();

  static Rationals$ rationalTheory = Rationals$.MODULE$;
  public static final Sort FRACTION_SORT = rationalTheory.dom();

  @Option(secure = true, description = "log all queries as Princess-specific Scala code")
  private boolean logAllQueriesAsScala = false;

  @Option(secure = true, description = "file for Princess-specific dump of queries as Scala code")
  @FileOption(FileOption.Type.OUTPUT_FILE)
  private PathCounterTemplate logAllQueriesAsScalaFile =
      PathCounterTemplate.ofFormatString("princess-query-%03d-");

  /**
   * cache for variables, because they do not implement equals() and hashCode(), so we need to have
   * the same objects.
   */
  private final Map<String, IFormula> boolVariablesCache = new HashMap<>();

  private final Map<String, ITerm> sortedVariablesCache = new HashMap<>();

  private final Map<String, IFunction> functionsCache = new HashMap<>();

  private final int randomSeed;
  private final @Nullable PathCounterTemplate basicLogfile;
  private final ShutdownNotifier shutdownNotifier;

  /**
   * The wrapped API is the first created API. It will never be used outside this class and never be
   * closed. If a variable is declared, it is declared in the first api, then copied into all
   * registered APIs. Each API has its own stack for formulas.
   */
  private final SimpleAPI api;

  private final List<PrincessAbstractProver<?>> registeredProvers = new ArrayList<>();

  PrincessEnvironment(
      Configuration config,
      @Nullable final PathCounterTemplate pBasicLogfile,
      ShutdownNotifier pShutdownNotifier,
      final int pRandomSeed)
      throws InvalidConfigurationException {
    config.inject(this);

    basicLogfile = pBasicLogfile;
    shutdownNotifier = pShutdownNotifier;
    randomSeed = pRandomSeed;

    // this api is only used local in this environment, no need for interpolation
    api = getNewApi(false);
  }

  /**
   * This method returns a new prover, that is registered in this environment. All variables are
   * shared in all registered APIs.
   */
  PrincessAbstractProver<?> getNewProver(
      boolean useForInterpolation,
      PrincessFormulaManager mgr,
      PrincessFormulaCreator creator,
      Set<ProverOptions> pOptions) {

    SimpleAPI newApi =
        getNewApi(useForInterpolation || pOptions.contains(ProverOptions.GENERATE_UNSAT_CORE));

    // add all symbols, that are available until now
    boolVariablesCache.values().forEach(newApi::addBooleanVariable);
    sortedVariablesCache.values().forEach(newApi::addConstant);
    functionsCache.values().forEach(newApi::addFunction);

    PrincessAbstractProver<?> prover;
    if (useForInterpolation) {
      prover = new PrincessInterpolatingProver(mgr, creator, newApi, shutdownNotifier, pOptions);
    } else {
      prover = new PrincessTheoremProver(mgr, creator, newApi, shutdownNotifier, pOptions);
    }
    registeredProvers.add(prover);
    return prover;
  }

  @SuppressFBWarnings("NP_NULL_ON_SOME_PATH_FROM_RETURN_VALUE")
  private SimpleAPI getNewApi(boolean constructProofs) {
    File directory = null;
    String smtDumpBasename = null;
    String scalaDumpBasename = null;

    if (basicLogfile != null) {
      Path logPath = basicLogfile.getFreshPath();
      directory = getAbsoluteParent(logPath);
      smtDumpBasename = logPath.getFileName().toString();
      if (Files.getFileExtension(smtDumpBasename).equals("smt2")) {
        // Princess adds .smt2 anyway
        smtDumpBasename = Files.getNameWithoutExtension(smtDumpBasename);
      }
      smtDumpBasename += "-";
    }

    if (logAllQueriesAsScala && logAllQueriesAsScalaFile != null) {
      Path logPath = logAllQueriesAsScalaFile.getFreshPath();
      if (directory == null) {
        directory = getAbsoluteParent(logPath);
      }
      scalaDumpBasename = logPath.getFileName().toString();
    }

    Debug.enableAllAssertions(enableAssertions);

    final SimpleAPI newApi =
        SimpleAPI.apply(
            enableAssertions, // enableAssert, see above
            false, // no sanitiseNames, because variable names may contain chars like "@" and ":".
            smtDumpBasename != null, // dumpSMT
            smtDumpBasename, // smtDumpBasename
            scalaDumpBasename != null, // dumpScala
            scalaDumpBasename, // scalaDumpBasename
            directory, // dumpDirectory
            SimpleAPI.apply$default$8(), // tightFunctionScopes
            SimpleAPI.apply$default$9(), // genTotalityAxioms
            new scala.Some<>(randomSeed), // randomSeed
            GlobalSettings.DEFAULT());

    if (constructProofs) { // needed for interpolation and unsat cores
      newApi.setConstructProofs(true);
    }

    return newApi;
  }

  private File getAbsoluteParent(Path path) {
    return Optional.ofNullable(path.getParent()).orElse(Path.of(".")).toAbsolutePath().toFile();
  }

  int getMinAtomsForAbbreviation() {
    return minAtomsForAbbreviation;
  }

  void unregisterStack(PrincessAbstractProver<?> stack) {
    Preconditions.checkState(
        registeredProvers.contains(stack), "cannot unregister stack, it is not registered");
    registeredProvers.remove(stack);
  }

  /** unregister and close all stacks. */
  void close() {
    for (PrincessAbstractProver<?> prover : ImmutableList.copyOf(registeredProvers)) {
      prover.close();
    }
    api.shutDown();
    api.reset();
    Preconditions.checkState(registeredProvers.isEmpty());
  }

  public List<? extends IExpression> parseStringToTerms(String s, PrincessFormulaCreator creator) {

    Tuple4<
            Seq<IFormula>,
            scala.collection.immutable.Map<IFunction, SMTFunctionType>,
            scala.collection.immutable.Map<ConstantTerm, SMTType>,
            scala.collection.immutable.Map<Predicate, SMTFunctionType>>
        parserResult;

    try {
      parserResult = extractFromSTMLIB(s);
    } catch (TranslationException | EnvironmentException nested) {
      throw new IllegalArgumentException(nested);
    }

    final List<IFormula> formulas = asJava(parserResult._1());

    // Check that all user defined function, constant and predicate symbols have valid names
    for (IFunction f : asJava(parserResult._2().keySet())) {
      checkArgument(FormulaCreator.isValidName(FormulaCreator.dequote(f.name())));
    }
    for (ConstantTerm c : asJava(parserResult._3()).keySet()) {
      checkArgument(FormulaCreator.isValidName(FormulaCreator.dequote(c.name())));
    }
    for (Predicate p : asJava(parserResult._4()).keySet()) {
      checkArgument(FormulaCreator.isValidName(FormulaCreator.dequote(p.name())));
    }

    ImmutableSet.Builder<IExpression> declaredFunctions = ImmutableSet.builder();
    for (IExpression f : formulas) {
      declaredFunctions.addAll(creator.extractVariablesAndUFs(f, true).values());
    }
    for (IExpression var : declaredFunctions.build()) {
      if (var instanceof IConstant) {
        sortedVariablesCache.put(((IConstant) var).c().name(), (ITerm) var);
        addSymbol((IConstant) var);
      } else if (var instanceof IAtom) {
        boolVariablesCache.put(((IAtom) var).pred().name(), (IFormula) var);
        addSymbol((IAtom) var);
      } else if (var instanceof IFunApp) {
        IFunction fun = ((IFunApp) var).fun();
        functionsCache.put(fun.name(), fun);
        addFunction(fun);
      }
    }
    return formulas;
  }

  /**
   * Parse a SMTLIB query and returns a triple of the asserted formulas, the defined functions and
   * symbols.
   *
   * @throws EnvironmentException from Princess when the parsing fails
   * @throws TranslationException from Princess when the parsing fails due to type mismatch
   */
  /* EnvironmentException is not unused, but the Java compiler does not like Scala. */
  @SuppressWarnings("unused")
  private Tuple4<
          Seq<IFormula>,
          scala.collection.immutable.Map<IFunction, SMTFunctionType>,
          scala.collection.immutable.Map<ConstantTerm, SMTType>,
          scala.collection.immutable.Map<Predicate, SMTFunctionType>>
      extractFromSTMLIB(String s) throws EnvironmentException, TranslationException {
    // replace let-terms and function definitions by their full term.
    final boolean fullyInlineLetsAndFunctions = true;
    return api.extractSMTLIBAssertionsSymbols(new StringReader(s), fullyInlineLetsAndFunctions);
  }

  /**
   * Utility helper method to hide a checked exception as RuntimeException.
   *
   * <p>The generic E simulates a RuntimeException at compile time and lets us throw the correct
   * Exception at run time.
   */
  @SuppressWarnings("unchecked")
  @SuppressFBWarnings("THROWS_METHOD_THROWS_CLAUSE_THROWABLE")
  private static <E extends Throwable> void throwCheckedAsUnchecked(Throwable e) throws E {
    throw (E) e;
  }

  /**
   * This method dumps a formula as SMTLIB2.
   *
   * <p>We avoid redundant sub-formulas by replacing them with abbreviations. The replacement is
   * done "once" when calling this method.
   *
   * <p>We return an {@link Appender} to avoid storing larger Strings in memory. We sort the symbols
   * and abbreviations for the export only "on demand".
   */
  public String dumpFormula(IFormula formula, final PrincessFormulaCreator creator)
      throws IOException {
    // remove redundant expressions
    // TODO do we want to remove redundancy completely (as checked in the unit
    // tests (SolverFormulaIOTest class)) or do we want to remove redundancy up
    // to the point we do it for formulas that should be asserted
    Tuple2<IExpression, scala.collection.immutable.Map<IExpression, IExpression>> tuple =
        api.abbrevSharedExpressionsWithMap(formula, 1);
    final IExpression lettedFormula = tuple._1();
    final Map<IExpression, IExpression> abbrevMap = asJava(tuple._2());

    StringBuilder builder = new StringBuilder();
    new Appenders.AbstractAppender() {
      @Override
      public void appendTo(Appendable out) throws IOException {
        try {
          appendTo0(out);
        } catch (scala.MatchError e) {
          // exception might be thrown in case of interrupt, then we wrap it in an interrupt.
          if (shutdownNotifier.shouldShutdown()) {
            InterruptedException interrupt = new InterruptedException();
            interrupt.addSuppressed(e);
            throwCheckedAsUnchecked(interrupt);
          } else {
            // simply re-throw exception
            throw e;
          }
        }
      }

      private void appendTo0(Appendable out) throws IOException {
        Set<IExpression> allVars =
            new LinkedHashSet<>(creator.extractVariablesAndUFs(lettedFormula, true).values());

        // We use TreeMaps for deterministic/alphabetic ordering.
        // For abbreviations, we use the ordering, but dump nested abbreviations/dependencies first.
        Map<String, IExpression> symbols = new TreeMap<>();
        Map<String, IFunApp> ufs = new TreeMap<>();
        Map<String, IExpression> usedAbbrevs = new TreeMap<>();

        collectAllSymbolsAndAbbreviations(allVars, symbols, ufs, usedAbbrevs);

        // declare normal symbols
        for (Entry<String, IExpression> symbol : symbols.entrySet()) {
          out.append(
              String.format(
                  "(declare-fun %s () %s)%n",
                  SMTLineariser.quoteIdentifier(symbol.getKey()),
                  getFormulaType(symbol.getValue()).toSMTLIBString()));
        }

        // declare UFs
        for (Entry<String, IFunApp> function : ufs.entrySet()) {
          List<String> argSorts =
              Lists.transform(
                  asJava(function.getValue().args()), a -> getFormulaType(a).toSMTLIBString());
          out.append(
              String.format(
                  "(declare-fun %s (%s) %s)%n",
                  SMTLineariser.quoteIdentifier(function.getKey()),
                  Joiner.on(" ").join(argSorts),
                  getFormulaType(function.getValue()).toSMTLIBString()));
        }

        // now every symbol from the formula or from abbreviations are declared,
        // let's add the abbreviations, too.
        for (String abbrev : getOrderedAbbreviations(usedAbbrevs)) {
          IExpression abbrevFormula = usedAbbrevs.get(abbrev);
          IExpression fullFormula = abbrevMap.get(abbrevFormula);
          out.append(
              String.format(
                  "(define-fun %s () %s %s)%n",
                  SMTLineariser.quoteIdentifier(abbrev),
                  getFormulaType(fullFormula).toSMTLIBString(),
                  SMTLineariser.asString(fullFormula)));
        }

        // now add the final assert
        out.append("(assert ").append(SMTLineariser.asString(lettedFormula)).append(')');
      }

      /**
       * determine all used symbols and all used abbreviations by traversing the abbreviations
       * transitively.
       *
       * @param allVars will be updated with further symbols and UFs.
       * @param symbols will be updated with all found symbols.
       * @param ufs will be updated with all found UFs.
       * @param abbrevs will be updated with all found abbreviations.
       */
      private void collectAllSymbolsAndAbbreviations(
          final Set<IExpression> allVars,
          final Map<String, IExpression> symbols,
          final Map<String, IFunApp> ufs,
          final Map<String, IExpression> abbrevs) {
        final Deque<IExpression> waitlistSymbols = new ArrayDeque<>(allVars);
        final Set<String> seenSymbols = new HashSet<>();
        while (!waitlistSymbols.isEmpty()) {
          IExpression var = waitlistSymbols.poll();
          String name = getName(var);

          // we don't want to declare variables twice
          if (!seenSymbols.add(name)) {
            continue;
          }

          if (isAbbreviation(var)) {
            Preconditions.checkState(!abbrevs.containsKey(name));
            abbrevs.put(name, var);
            // for abbreviations, we go deeper and analyse the abbreviated formula.
            Set<IExpression> varsFromAbbrev = getVariablesFromAbbreviation(var);
            Sets.difference(varsFromAbbrev, allVars).forEach(waitlistSymbols::push);
            allVars.addAll(varsFromAbbrev);
          } else if (var instanceof IFunApp) {
            Preconditions.checkState(!ufs.containsKey(name));
            ufs.put(name, (IFunApp) var);
          } else {
            Preconditions.checkState(!symbols.containsKey(name));
            symbols.put(name, var);
          }
        }
      }

      /**
       * Abbreviations can be nested, and thus we need to sort them. The returned list (or iterable)
       * contains each used abbreviation exactly once. Abbreviations with no dependencies come
       * first, more complex ones later.
       */
      private Iterable<String> getOrderedAbbreviations(Map<String, IExpression> usedAbbrevs) {
        ArrayDeque<String> waitlist = new ArrayDeque<>(usedAbbrevs.keySet());
        Set<String> orderedAbbreviations = new LinkedHashSet<>();
        while (!waitlist.isEmpty()) {
          String abbrev = waitlist.removeFirst();
          boolean allDependenciesFinished = true;
          for (IExpression var : getVariablesFromAbbreviation(usedAbbrevs.get(abbrev))) {
            String name = getName(var);
            if (isAbbreviation(var)) {
              if (!orderedAbbreviations.contains(name)) {
                allDependenciesFinished = false;
                waitlist.addLast(name); // part 1: add dependency for later
              }
            }
          }
          if (allDependenciesFinished) {
            orderedAbbreviations.add(abbrev);
          } else {
            waitlist.addLast(abbrev); // part 2: add again for later
          }
        }
        return orderedAbbreviations;
      }

      private boolean isAbbreviation(IExpression symbol) {
        return abbrevMap.containsKey(symbol);
      }

      private Set<IExpression> getVariablesFromAbbreviation(IExpression var) {
        return ImmutableSet.copyOf(
            creator.extractVariablesAndUFs(abbrevMap.get(var), true).values());
      }
    }.appendTo(builder);

    return builder.toString();
  }

  private static String getName(IExpression var) {
    if (var instanceof IAtom) {
      return ((IAtom) var).pred().name();
    } else if (var instanceof IConstant) {
      return var.toString();
    } else if (var instanceof IFunApp) {
      String fullStr = ((IFunApp) var).fun().toString();
      return fullStr.substring(0, fullStr.indexOf('/'));
    } else if (var instanceof IIntFormula) {
      return getName(((IIntFormula) var).t());
    }

    throw new IllegalArgumentException("The given parameter is no variable or function");
  }

  static FormulaType<?> getFormulaType(IExpression pFormula) {
    // TODO: We could use Sort.sortof() here, but it sometimes returns `integer` even though the
    //  term is rational. We should figure out why and then open a new issue for this.
    if (pFormula instanceof IFormula) {
      return FormulaType.BooleanType;
    } else if (pFormula instanceof ITimes) {
      // coeff is always INT, lets check the subterm.
      ITimes times = (ITimes) pFormula;
      return getFormulaType(times.subterm());
    } else if (pFormula instanceof IPlus) {
      IPlus plus = (IPlus) pFormula;
      FormulaType<?> t1 = getFormulaType(plus.t1());
      FormulaType<?> t2 = getFormulaType(plus.t2());
      return mergeFormulaTypes(t1, t2);
    } else if (pFormula instanceof ITermITE) {
      ITermITE plus = (ITermITE) pFormula;
      FormulaType<?> t1 = getFormulaType(plus.left());
      FormulaType<?> t2 = getFormulaType(plus.right());
      return mergeFormulaTypes(t1, t2);
    } else {
      final Sort sort = Sort$.MODULE$.sortOf((ITerm) pFormula);
      try {
        return getFormulaTypeFromSort(sort);
      } catch (IllegalArgumentException e) {
        // add more info about the formula, then rethrow
        throw new IllegalArgumentException(
            String.format(
                "Unknown formula type '%s' of sort '%s' for formula '%s'.",
                pFormula.getClass(), sort.toString(), pFormula),
            e);
      }
    }
  }

  /**
   * Merge INTEGER and RATIONAL type or INTEGER and BITVECTOR and return the more general type. The
   * ordering is: RATIONAL > INTEGER > BITVECTOR.
   *
   * @throws IllegalArgumentException for any other type.
   */
  private static FormulaType<?> mergeFormulaTypes(FormulaType<?> type1, FormulaType<?> type2) {
    if ((type1.isIntegerType() || type1.isRationalType())
        && (type2.isIntegerType() || type2.isRationalType())) {
      return type1.isRationalType() ? type1 : type2;
    }
    if ((type1.isIntegerType() || type1.isBitvectorType())
        && (type2.isIntegerType() || type2.isBitvectorType())) {
      return type1.isIntegerType() ? type1 : type2;
    }
    throw new IllegalArgumentException(
        String.format("Types %s and %s can not be merged.", type1, type2));
  }

  private static FormulaType<?> getFormulaTypeFromSort(final Sort sort) {
    if (sort == PrincessEnvironment.BOOL_SORT) {
      return FormulaType.BooleanType;
    } else if (sort == PrincessEnvironment.INTEGER_SORT || sort == PrincessEnvironment.NAT_SORT) {
      return FormulaType.IntegerType;
    } else if (sort == PrincessEnvironment.FRACTION_SORT) {
      return FormulaType.RationalType;
    } else if (sort == PrincessEnvironment.STRING_SORT) {
      return FormulaType.StringType;
    } else if (sort == PrincessEnvironment.REGEX_SORT) {
      return FormulaType.RegexType;
    } else if (sort instanceof ArraySort) {
      Seq<Sort> indexSorts = ((ArraySort) sort).theory().indexSorts();
      Sort elementSort = ((ArraySort) sort).theory().objSort();
      assert indexSorts.iterator().size() == 1 : "unexpected index type in Array type:" + sort;
      // assert indexSorts.size() == 1; // TODO Eclipse does not like simpler code.
      return FormulaType.getArrayType(
          getFormulaTypeFromSort(indexSorts.iterator().next()), // get single index-sort
          getFormulaTypeFromSort(elementSort));
    } else if (sort instanceof MultipleValueBool$) {
      return FormulaType.BooleanType;
    } else {
      scala.Option<Object> bitWidth = getBitWidth(sort);
      if (bitWidth.isDefined()) {
        return FormulaType.getBitvectorTypeWithSize((Integer) bitWidth.get());
      }
    }
    throw new IllegalArgumentException(
        String.format("Unknown formula type '%s' for sort '%s'.", sort.getClass(), sort));
  }

  static scala.Option<Object> getBitWidth(final Sort sort) {
    scala.Option<Object> bitWidth = ModuloArithmetic.UnsignedBVSort$.MODULE$.unapply(sort);
    if (!bitWidth.isDefined()) {
      bitWidth = ModuloArithmetic.SignedBVSort$.MODULE$.unapply(sort);
    }
    return bitWidth;
  }

  public IExpression makeVariable(Sort type, String varname) {
    if (type == BOOL_SORT) {
      if (boolVariablesCache.containsKey(varname)) {
        return boolVariablesCache.get(varname);
      } else {
        IFormula var = api.createBooleanVariable(varname);
        addSymbol(var);
        boolVariablesCache.put(varname, var);
        return var;
      }
    } else {
      if (sortedVariablesCache.containsKey(varname)) {
        return sortedVariablesCache.get(varname);
      } else {
        ITerm var = api.createConstant(varname, type);
        addSymbol(var);
        sortedVariablesCache.put(varname, var);
        return var;
      }
    }
  }

  /** This function declares a new functionSymbol with the given argument types and result. */
  public IFunction declareFun(String name, Sort returnType, List<Sort> args) {
    if (functionsCache.containsKey(name)) {
      return functionsCache.get(name);
    } else {
      IFunction funcDecl =
          api.createFunction(
              name, toSeq(args), returnType, false, SimpleAPI.FunctionalityMode$.MODULE$.Full());
      addFunction(funcDecl);
      functionsCache.put(name, funcDecl);
      return funcDecl;
    }
  }

  public ITerm makeSelect(ITerm array, ITerm index) {
    List<ITerm> args = ImmutableList.of(array, index);
    ArraySort arraySort = (ArraySort) Sort$.MODULE$.sortOf(array);
    return new IFunApp(arraySort.theory().select(), toSeq(args));
  }

  public ITerm makeStore(ITerm array, ITerm index, ITerm value) {
    List<ITerm> args = ImmutableList.of(array, index, value);
    ArraySort arraySort = (ArraySort) Sort$.MODULE$.sortOf(array);
    return new IFunApp(arraySort.theory().store(), toSeq(args));
  }

  public ITerm makeConstArray(ArraySort arraySort, ITerm elseTerm) {
    // return new IFunApp(arraySort.theory().const(), elseTerm); // I love Scala! So simple! ;-)

    // Scala uses keywords that are illegal in Java. Thus, we use reflection to access the method.
    // TODO we should contact the developers of Princess and ask for a renaming.
    final IFunction constArrayOp;
    try {
      Method constMethod = ExtArray.class.getMethod("const");
      constArrayOp = (IFunction) constMethod.invoke(arraySort.theory());
    } catch (IllegalAccessException | NoSuchMethodException | InvocationTargetException exception) {
      throw new RuntimeException(exception);
    }

    return new IFunApp(constArrayOp, toSeq(ImmutableList.of(elseTerm)));
  }

  public boolean hasArrayType(IExpression exp) {
    if (exp instanceof ITerm) {
      final ITerm t = (ITerm) exp;
      return Sort$.MODULE$.sortOf(t) instanceof ArraySort;
    } else {
      return false;
    }
  }

  public IFormula elimQuantifiers(IFormula formula) {
    return api.simplify(formula);
  }

  private void addSymbol(IFormula symbol) {
    for (PrincessAbstractProver<?> prover : registeredProvers) {
      prover.addSymbol(symbol);
    }
  }

  private void addSymbol(ITerm symbol) {
    for (PrincessAbstractProver<?> prover : registeredProvers) {
      prover.addSymbol(symbol);
    }
  }

  private void addFunction(IFunction funcDecl) {
    for (PrincessAbstractProver<?> prover : registeredProvers) {
      prover.addSymbol(funcDecl);
    }
  }

  static <T> Seq<T> toSeq(List<T> list) {
    return collectionAsScalaIterableConverter(list).asScala().toSeq();
  }

  static Seq<ITerm> toITermSeq(List<IExpression> exprs) {
    return PrincessEnvironment.toSeq(
        exprs.stream().map(e -> (ITerm) e).collect(Collectors.toList()));
  }

  static Seq<ITerm> toITermSeq(IExpression... exprs) {
    return toITermSeq(Arrays.asList(exprs));
  }

  IExpression simplify(IExpression f) {
    // TODO this method is not tested, check it!
    if (f instanceof IFormula) {
      f = BooleanCompactifier.apply((IFormula) f);
    }
    return PartialEvaluator.apply(f);
  }
}
