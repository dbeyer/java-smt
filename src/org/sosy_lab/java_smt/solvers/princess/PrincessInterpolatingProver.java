// This file is part of JavaSMT,
// an API wrapper for a collection of SMT solvers:
// https://github.com/sosy-lab/java-smt
//
// SPDX-FileCopyrightText: 2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

package org.sosy_lab.java_smt.solvers.princess;

import static scala.collection.JavaConverters.asJava;
import static scala.collection.JavaConverters.asScala;

import ap.SimpleAPI;
import ap.basetypes.Tree;
import ap.parser.IBoolLit;
import ap.parser.IExpression;
import ap.parser.IFormula;
import com.google.common.base.Preconditions;
import com.google.common.collect.FluentIterable;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterables;
import com.google.common.graph.Traverser;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.common.ShutdownNotifier;
import org.sosy_lab.common.UniqueIdGenerator;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.InterpolatingProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;
import scala.collection.Seq;
import scala.collection.mutable.ArrayBuffer;

class PrincessInterpolatingProver extends PrincessAbstractProver<Integer, Integer>
    implements InterpolatingProverEnvironment<Integer> {

  private final Map<Integer, IFormula> annotatedTerms = new HashMap<>(); // Collection of termNames
  private static final UniqueIdGenerator counter = new UniqueIdGenerator(); // for different indices

  PrincessInterpolatingProver(
      PrincessFormulaManager pMgr,
      PrincessFormulaCreator creator,
      SimpleAPI pApi,
      ShutdownNotifier pShutdownNotifier,
      Set<ProverOptions> pOptions) {
    super(pMgr, creator, pApi, pShutdownNotifier, pOptions);
  }

  @Override
  public void pop() {
    Preconditions.checkState(!closed);
    assertedFormulas.peek().forEach(annotatedTerms::remove);
    super.pop();
  }

  @Override
  public Integer addConstraint(BooleanFormula f) {
    Preconditions.checkState(!closed);
    int termIndex = counter.getFreshId();
    IFormula t = (IFormula) mgr.extractInfo(f);

    // set partition number and add formula
    api.setPartitionNumber(termIndex);
    addConstraint0(t);

    // reset partition number to magic number -1,
    // which represents formulae belonging to all partitions.
    api.setPartitionNumber(-1);

    assertedFormulas.peek().add(termIndex);
    annotatedTerms.put(termIndex, t);
    return termIndex;
  }

  @Override
  protected Iterable<IExpression> getAssertedFormulas() {
    return FluentIterable.concat(assertedFormulas).transform(annotatedTerms::get);
  }

  @Override
  public BooleanFormula getInterpolant(Collection<Integer> pTermNamesOfA) throws SolverException {
    Preconditions.checkState(!closed);
    Set<Integer> indexesOfA = ImmutableSet.copyOf(pTermNamesOfA);

    // calc difference: termNamesOfB := assertedFormulas - termNamesOfA
    Set<Integer> indexesOfB =
        annotatedTerms.keySet().stream()
            .filter(f -> !indexesOfA.contains(f))
            .collect(ImmutableSet.toImmutableSet());

    // get interpolant of groups
    List<BooleanFormula> itp = getSeqInterpolants(ImmutableList.of(indexesOfA, indexesOfB));
    assert itp.size() == 1; // 2 groups -> 1 interpolant

    return itp.get(0);
  }

  @Override
  public List<BooleanFormula> getSeqInterpolants(
      final List<? extends Collection<Integer>> partitions) throws SolverException {
    Preconditions.checkState(!closed);
    Preconditions.checkArgument(
        !partitions.isEmpty(), "at least one partition should be available.");

    // convert to needed data-structure
    final ArrayBuffer<scala.collection.immutable.Set<Object>> args = new ArrayBuffer<>();
    for (Collection<Integer> partition : partitions) {
      args.$plus$eq(asScala(partition).toSet());
    }

    // do the hard work
    final Seq<IFormula> itps;
    try {
      itps = api.getInterpolants(args.toSeq(), api.getInterpolants$default$2());
    } catch (StackOverflowError e) {
      // Princess is recursive and thus produces stack overflows on large formulas.
      // Princess itself also catches StackOverflowError and returns "OutOfMemory" in checkSat(),
      // so we can do the same for getInterpolants().
      throw new SolverException(
          "Princess ran out of stack memory, try increasing the stack size.", e);
    }

    assert itps.length() == partitions.size() - 1
        : "There should be (n-1) interpolants for n partitions";

    // convert data-structure back
    // TODO check that interpolants do not contain abbreviations we did not introduce ourselves
    final List<BooleanFormula> result = new ArrayList<>();
    for (final IFormula itp : asJava(itps)) {
      result.add(mgr.encapsulateBooleanFormula(itp));
    }
    return result;
  }

  @Override
  public List<BooleanFormula> getTreeInterpolants(
      List<? extends Collection<Integer>> partitionedFormulas, int[] startOfSubTree)
      throws SolverException {
    Preconditions.checkState(!closed);
    assert InterpolatingProverEnvironment.checkTreeStructure(
        partitionedFormulas.size(), startOfSubTree);

    // reconstruct the trees from the labels in post-order
    final Deque<Tree<scala.collection.immutable.Set<Object>>> stack = new ArrayDeque<>();
    final Deque<Integer> subtreeStarts = new ArrayDeque<>();

    for (int i = 0; i < partitionedFormulas.size(); ++i) {
      Preconditions.checkState(stack.size() == subtreeStarts.size());
      int start = startOfSubTree[i];
      ArrayBuffer<Tree<scala.collection.immutable.Set<Object>>> children = new ArrayBuffer<>();
      // while-loop: inner node -> merge children
      // otherwise:  leaf-node  -> start new subtree, no children
      while (!subtreeStarts.isEmpty() && start <= subtreeStarts.peek()) {
        subtreeStarts.pop();
        children.$plus$eq(stack.pop());
      }
      subtreeStarts.push(start);
      stack.push(new Tree<>(asScala(partitionedFormulas.get(i)).toSet(), children.toList()));
    }

    Preconditions.checkState(subtreeStarts.peek() == 0, "subtree of root should start at 0.");
    Tree<scala.collection.immutable.Set<Object>> root = stack.pop();
    Preconditions.checkState(stack.isEmpty(), "root should be last element in stack.");

    final Tree<IFormula> itps;
    try {
      itps = api.getTreeInterpolant(root, api.getTreeInterpolant$default$2());
    } catch (StackOverflowError e) {
      // Princess is recursive and thus produces stack overflows on large formulas.
      // Princess itself also catches StackOverflowError and returns "OutOfMemory" in checkSat(),
      // so we can do the same for getInterpolants().
      throw new SolverException(
          "Princess ran out of stack memory, try increasing the stack size.", e);
    }

    List<BooleanFormula> result = tree2List(itps);
    assert result.size() == startOfSubTree.length - 1;
    return result;
  }

  /** returns a post-order iteration of the tree. */
  private List<BooleanFormula> tree2List(Tree<IFormula> tree) {
    List<BooleanFormula> lst =
        FluentIterable.from(
                Traverser.<Tree<IFormula>>forTree(node -> asJava(node.children()))
                    .depthFirstPostOrder(tree))
            .transform(node -> mgr.encapsulateBooleanFormula(node.d()))
            .toList();
    // root of interpolation tree is false, and we have to remove it.
    assert Iterables.getLast(lst).equals(mgr.encapsulateBooleanFormula(new IBoolLit(false)));
    return lst.subList(0, lst.size() - 1);
  }
}
