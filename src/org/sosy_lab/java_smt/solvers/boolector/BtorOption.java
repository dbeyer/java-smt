// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// This file is based on "btortypes.h" from Boolector.
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
// SPDX-FileCopyrightText: 2015-2020 Mathias Preiner
// SPDX-FileCopyrightText: 2016 Armin Biere
// SPDX-FileCopyrightText: 2016-2020 Aina Niemetz
//
// SPDX-License-Identifier: MIT AND Apache-2.0

package org.sosy_lab.java_smt.solvers.boolector;

/** We keep this synchronized with "btortypes.h". */
public enum BtorOption {
  BTOR_OPT_MODEL_GEN,
  BTOR_OPT_INCREMENTAL,
  BTOR_OPT_INCREMENTAL_SMT1,
  BTOR_OPT_INPUT_FORMAT,
  BTOR_OPT_OUTPUT_NUMBER_FORMAT,
  BTOR_OPT_OUTPUT_FORMAT,
  BTOR_OPT_ENGINE,
  BTOR_OPT_SAT_ENGINE,
  BTOR_OPT_AUTO_CLEANUP,
  BTOR_OPT_PRETTY_PRINT,
  BTOR_OPT_EXIT_CODES,
  BTOR_OPT_SEED,
  BTOR_OPT_VERBOSITY,
  BTOR_OPT_LOGLEVEL,
  BTOR_OPT_REWRITE_LEVEL,
  BTOR_OPT_SKELETON_PREPROC,
  BTOR_OPT_ACKERMANN,
  BTOR_OPT_BETA_REDUCE,
  BTOR_OPT_ELIMINATE_SLICES,
  BTOR_OPT_VAR_SUBST,
  BTOR_OPT_UCOPT,
  BTOR_OPT_MERGE_LAMBDAS,
  BTOR_OPT_EXTRACT_LAMBDAS,
  BTOR_OPT_NORMALIZE,
  BTOR_OPT_NORMALIZE_ADD,
  BTOR_OPT_FUN_PREPROP,
  BTOR_OPT_FUN_PRESLS,
  BTOR_OPT_FUN_DUAL_PROP,
  BTOR_OPT_FUN_DUAL_PROP_QSORT,
  BTOR_OPT_FUN_JUST,
  BTOR_OPT_FUN_JUST_HEURISTIC,
  BTOR_OPT_FUN_LAZY_SYNTHESIZE,
  BTOR_OPT_FUN_EAGER_LEMMAS,
  BTOR_OPT_FUN_STORE_LAMBDAS,
  BTOR_OPT_PRINT_DIMACS,
  BTOR_OPT_SLS_NFLIPS,
  BTOR_OPT_SLS_STRATEGY,
  BTOR_OPT_SLS_JUST,
  BTOR_OPT_SLS_MOVE_GW,
  BTOR_OPT_SLS_MOVE_RANGE,
  BTOR_OPT_SLS_MOVE_SEGMENT,
  BTOR_OPT_SLS_MOVE_RAND_WALK,
  BTOR_OPT_SLS_PROB_MOVE_RAND_WALK,
  BTOR_OPT_SLS_MOVE_RAND_ALL,
  BTOR_OPT_SLS_MOVE_RAND_RANGE,
  BTOR_OPT_SLS_MOVE_PROP,
  BTOR_OPT_SLS_MOVE_PROP_N_PROP,
  BTOR_OPT_SLS_MOVE_PROP_N_SLS,
  BTOR_OPT_SLS_MOVE_PROP_FORCE_RW,
  BTOR_OPT_SLS_MOVE_INC_MOVE_TEST,
  BTOR_OPT_SLS_USE_RESTARTS,
  BTOR_OPT_SLS_USE_BANDIT,
  BTOR_OPT_PROP_NPROPS,
  BTOR_OPT_PROP_USE_RESTARTS,
  BTOR_OPT_PROP_USE_BANDIT,
  BTOR_OPT_PROP_PATH_SEL,
  BTOR_OPT_PROP_PROB_USE_INV_VALUE,
  BTOR_OPT_PROP_PROB_FLIP_COND,
  BTOR_OPT_PROP_PROB_FLIP_COND_CONST,
  BTOR_OPT_PROP_FLIP_COND_CONST_DELTA,
  BTOR_OPT_PROP_FLIP_COND_CONST_NPATHSEL,
  BTOR_OPT_PROP_PROB_SLICE_KEEP_DC,
  BTOR_OPT_PROP_PROB_CONC_FLIP,
  BTOR_OPT_PROP_PROB_SLICE_FLIP,
  BTOR_OPT_PROP_PROB_EQ_FLIP,
  BTOR_OPT_PROP_PROB_AND_FLIP,
  BTOR_OPT_PROP_NO_MOVE_ON_CONFLICT,
  BTOR_OPT_AIGPROP_USE_RESTARTS,
  BTOR_OPT_AIGPROP_USE_BANDIT,
  BTOR_OPT_QUANT_SYNTH,
  BTOR_OPT_QUANT_DUAL_SOLVER,
  BTOR_OPT_QUANT_SYNTH_LIMIT,
  BTOR_OPT_QUANT_SYNTH_QI,
  BTOR_OPT_QUANT_DER,
  BTOR_OPT_QUANT_CER,
  BTOR_OPT_QUANT_MINISCOPE,
  BTOR_OPT_SORT_EXP,
  BTOR_OPT_SORT_AIG,
  BTOR_OPT_SORT_AIGVEC,
  BTOR_OPT_AUTO_CLEANUP_INTERNAL,
  BTOR_OPT_SIMPLIFY_CONSTRAINTS,
  BTOR_OPT_CHK_FAILED_ASSUMPTIONS,
  BTOR_OPT_CHK_MODEL,
  BTOR_OPT_CHK_UNCONSTRAINED,
  BTOR_OPT_PARSE_INTERACTIVE,
  BTOR_OPT_SAT_ENGINE_LGL_FORK,
  BTOR_OPT_SAT_ENGINE_CADICAL_FREEZE,
  BTOR_OPT_SAT_ENGINE_N_THREADS,
  BTOR_OPT_SIMP_NORMAMLIZE_ADDERS,
  BTOR_OPT_DECLSORT_BV_WIDTH,
  BTOR_OPT_QUANT_SYNTH_ITE_COMPLETE,
  BTOR_OPT_QUANT_FIXSYNTH,
  BTOR_OPT_RW_ZERO_LOWER_SLICE,
  BTOR_OPT_NONDESTR_SUBST;

  private static class EnumIndexCounter {
    private static int nextValue = 0;
  }

  private final int value;

  BtorOption() {
    value = EnumIndexCounter.nextValue++;
  }

  public final int getValue() {
    return value;
  }

  @Override
  public String toString() {
    return name() + "(" + getValue() + ")";
  }
}
