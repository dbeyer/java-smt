/*
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
package org.sosy_lab.java_smt.basicimpl;

import com.google.common.collect.testing.ListTestSuiteBuilder;
import com.google.common.collect.testing.TestStringListGenerator;
import com.google.common.collect.testing.features.CollectionFeature;
import com.google.common.collect.testing.features.CollectionSize;
import java.util.List;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class LongArrayBackedListTest extends TestCase {

  private static final TestStringListGenerator listGenerator =
      new TestStringListGenerator() {

        @Override
        protected List<String> create(final String[] pElements) {
          long[] backingArray = new long[pElements.length];
          for (int i = 0; i < backingArray.length; i++) {
            backingArray[i] = i;
          }
          return new LongArrayBackedList<>(backingArray) {
            @Override
            protected String convert(long pE) {
              return pElements[(int) pE];
            }
          };
        }
      };

  public static junit.framework.Test suite() {
    TestSuite suite = new TestSuite();

    suite.addTest(
        ListTestSuiteBuilder.using(listGenerator)
            .named("LongArrayBackedListList")
            .withFeatures(
                CollectionFeature.KNOWN_ORDER,
                CollectionFeature.ALLOWS_NULL_VALUES,
                CollectionSize.ANY)
            .createTestSuite());

    return suite;
  }
}
