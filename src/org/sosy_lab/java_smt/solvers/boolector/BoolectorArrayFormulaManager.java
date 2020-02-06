/*
 *  JavaSMT is an API wrapper for a collection of SMT solvers.
 *  This file is part of JavaSMT.
 *
 *  Copyright (C) 2007-2019  Dirk Beyer
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
package org.sosy_lab.java_smt.solvers.boolector;

import static com.google.common.base.Preconditions.checkArgument;

import com.google.common.collect.Table;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FormulaType.BitvectorType;
import org.sosy_lab.java_smt.basicimpl.AbstractArrayFormulaManager;

public class BoolectorArrayFormulaManager
    extends AbstractArrayFormulaManager<Long, Long, Long, Long> {

  private final long btor;
  private final Table<String, Long, Long> nameFormulaCache;

  BoolectorArrayFormulaManager(BoolectorFormulaCreator pCreator) {
    super(pCreator);
    this.btor = pCreator.getEnv();
    this.nameFormulaCache = pCreator.getCache();
  }

  // pIndex should be a bitVector
  @Override
  protected Long select(Long pArray, Long pIndex) {
    return BtorJNI.boolector_read(btor, pArray, pIndex);
  }

  // pIndex and pValue should be bitVectors
  @Override
  protected Long store(Long pArray, Long pIndex, Long pValue) {
    return BtorJNI.boolector_write(btor, pArray, pIndex, pValue);
  }

  @Override
  @SuppressWarnings("MethodTypeParameterName")
  protected <TI extends Formula, TE extends Formula> Long internalMakeArray(
      String name, FormulaType<TI> pIndexType, FormulaType<TE> pElementType) {
    checkArgument(
        pIndexType.isBitvectorType() && pElementType.isBitvectorType(),
        "Boolector supports bitvector arrays only.");
    BitvectorType indexType = (BitvectorType) pIndexType;
    BitvectorType elementType = (BitvectorType) pElementType;
    final long indexSort = BtorJNI.boolector_bitvec_sort(btor, indexType.getSize());
    final long elementSort = BtorJNI.boolector_bitvec_sort(btor, elementType.getSize());
    final long arraySort = BtorJNI.boolector_array_sort(btor, indexSort, elementSort);
    Long maybeFormula = nameFormulaCache.get(name, arraySort);
    if (maybeFormula != null) {
      return maybeFormula;
    }
    if (nameFormulaCache.containsRow(name)) {
      throw new IllegalArgumentException("Symbol already used: " + name);
    }
    final long array = BtorJNI.boolector_array(btor, arraySort, name);
    nameFormulaCache.put(name, arraySort, array);
    return array;
  }

  @Override
  protected Long equivalence(Long pArray1, Long pArray2) {
    return BtorJNI.boolector_eq(btor, pArray1, pArray2);
  }
}
