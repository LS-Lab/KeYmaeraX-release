/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import edu.cmu.cs.ls.keymaerax.tools.Z3

/**
  * @author Nathan Fulton
  */
@UsualTest
class BuiltinFunctionSymbolsTests extends TacticTestBase {
  "max" should "be an interpreted function symbol for QE" in { withMathematica(implicit qeTool => {
    val f = "max(1, 2) = 2".asFormula
    val t = TactixLibrary.QE
    proveBy(f,t) shouldBe 'proved
  })}

  ignore should "work in counter-example generation" in { withMathematica(implicit qeTool => {
    val f = "max(a, 0) = a".asFormula
//    val counterExample = qeTool.findCounterExample(f)
    val counterExample = new Z3().findCounterExample(f)
    counterExample shouldBe 'nonEmpty
    println(counterExample.last("a".asVariable))
  })}
}
