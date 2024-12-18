// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2023 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.opensmt;

import static org.sosy_lab.common.collect.Collections3.elementAndList;

import com.google.common.base.Preconditions;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.basicimpl.AbstractModel;
import org.sosy_lab.java_smt.solvers.opensmt.api.Logic;
import org.sosy_lab.java_smt.solvers.opensmt.api.Model;
import org.sosy_lab.java_smt.solvers.opensmt.api.PTRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.SymRef;
import org.sosy_lab.java_smt.solvers.opensmt.api.Symbol;
import org.sosy_lab.java_smt.solvers.opensmt.api.TemplateFunction;
import org.sosy_lab.java_smt.solvers.opensmt.api.VectorPTRef;

public class OpenSmtModel extends AbstractModel<PTRef, SRef, Logic> {

  private final Logic osmtLogic;
  private final Model osmtModel;

  private final ImmutableList<ValueAssignment> model;

  OpenSmtModel(
      OpenSmtAbstractProver<?> pProver,
      OpenSmtFormulaCreator pCreator,
      Collection<PTRef> pAssertedTerms) {
    super(pProver, pCreator);

    osmtLogic = pCreator.getEnv();
    osmtModel = pProver.getOsmtSolver().getModel();

    // We need to generate and save this at construction time as OpenSMT has no functionality to
    // give a persistent reference to the model. If the SMT engine is used somewhere else, the
    // values we get out of it might change!
    model = generateModel(pCreator, pAssertedTerms);
  }

  private ImmutableList<ValueAssignment> generateModel(
      OpenSmtFormulaCreator pCreator, Collection<PTRef> pAssertedTerms) {
    Map<String, PTRef> userDeclarations = new LinkedHashMap<>();
    for (PTRef asserted : pAssertedTerms) {
      userDeclarations.putAll(creator.extractVariablesAndUFs(asserted, true));
    }

    ImmutableList.Builder<ValueAssignment> builder = ImmutableList.builder();

    for (PTRef term : userDeclarations.values()) {
      SymRef ref = osmtLogic.getSymRef(term);
      Symbol sym = osmtLogic.getSym(ref);

      int numArgs = sym.size() - 1;
      SRef sort = sym.rsort();

      if (osmtLogic.isArraySort(sort)) {
        // INFO: Disable model generation if arrays are used
        // https://github.com/usi-verification-and-security/opensmt/issues/630
        throw new UnsupportedOperationException(
            "OpenSMT does not support model generation when arrays are used");
      }

      if (numArgs == 0) {
        PTRef key = osmtLogic.mkVar(sort, osmtLogic.getSymName(ref));
        PTRef value = osmtModel.evaluate(key);
        builder.add(getValueAssignment(pCreator, key, value, ref, ImmutableList.of()));
      } else {
        TemplateFunction tf = osmtModel.getDefinition(ref);

        for (List<PTRef> path : unfold(numArgs, tf.getBody())) {
          List<PTRef> args = path.subList(0, numArgs);
          PTRef key = osmtLogic.insertTerm(ref, new VectorPTRef(args));
          PTRef value = path.get(numArgs);
          builder.add(getValueAssignment(pCreator, key, value, ref, args));
        }
      }
    }
    return builder.build();
  }

  private ValueAssignment getValueAssignment(
      OpenSmtFormulaCreator pCreator, PTRef key, PTRef value, SymRef ref, List<PTRef> args) {
    return new ValueAssignment(
        pCreator.encapsulate(key),
        pCreator.encapsulate(value),
        pCreator.encapsulateBoolean(osmtLogic.mkEq(key, value)),
        osmtLogic.getSymName(ref),
        pCreator.convertValue(value),
        Lists.transform(args, pCreator::convertValue));
  }

  @Override
  public PTRef evalImpl(PTRef f) {
    Preconditions.checkState(!isClosed());
    Map<String, PTRef> userDeclarations = creator.extractVariablesAndUFs(f, true);

    // FIXME: rewrite to use checkCompatibility from AbstractProver

    for (PTRef term : userDeclarations.values()) {
      SRef sort = osmtLogic.getSortRef(term);
      if (osmtLogic.isArraySort(sort)) {
        // INFO: Disable model generation if arrays are used
        // https://github.com/usi-verification-and-security/opensmt/issues/630
        throw new UnsupportedOperationException(
            "OpenSMT does not support model generation when arrays are used");
      }
    }
    return osmtModel.evaluate(f);
  }

  /**
   * OpenSMT represents uninterpreted functions as nested ite statements.
   *
   * <p>For example:
   *
   * <pre>
   * (define-fun g ((x1 Int) (x2 Int)) Int
   *   (ite (= 5 x1) (ite (= 3 x2) 2 (ite (= 1 x2) 2 0)) 0))
   * </pre>
   *
   * <p>We use unfold() to extract an array of value tuples from such a definition.
   */
  private List<List<PTRef>> unfold(int numArgs, PTRef body) {
    List<List<PTRef>> unwrapped = new ArrayList<>();

    if (osmtLogic.isIte(body)) {
      PTRef sub0 = osmtLogic.getPterm(body).at(0);
      PTRef sub1 = osmtLogic.getPterm(body).at(1);
      PTRef sub2 = osmtLogic.getPterm(body).at(2);

      PTRef sub00 = osmtLogic.getPterm(sub0).at(0);
      PTRef sub01 = osmtLogic.getPterm(sub0).at(1);

      PTRef value = osmtLogic.isVar(sub00) ? sub01 : sub00;

      for (List<PTRef> nested : unfold(numArgs - 1, sub1)) {
        List<PTRef> prefixed = elementAndList(value, nested);
        unwrapped.add(prefixed);
      }
      unwrapped.addAll(unfold(numArgs, sub2));
    }

    if (numArgs == 0) {
      unwrapped.add(ImmutableList.of(body));
    }
    return unwrapped;
  }

  @Override
  public ImmutableList<ValueAssignment> asList() {
    return model;
  }
}
