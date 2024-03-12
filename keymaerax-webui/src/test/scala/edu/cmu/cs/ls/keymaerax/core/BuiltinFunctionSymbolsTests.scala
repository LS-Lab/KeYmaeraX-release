/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

/** @author Nathan Fulton */
@UsualTest
class BuiltinFunctionSymbolsTests extends TacticTestBase {
  "max" should "be an interpreted function symbol for QE" in withMathematica { _ =>
    val f = "max(1, 2) = 2".asFormula
    val t = TactixLibrary.QE
    proveBy(f, t) shouldBe Symbol("proved")
  }

  it should "work in counter-example generation" in withMathematica { tool =>
    val f = "max(a, 0) = a".asFormula
    val counterExample = tool.findCounterExample(f)
    counterExample shouldBe Symbol("nonEmpty")
    val Number(n) = counterExample.head("a".asVariable)
    n.toInt should be < 0
  }
}
