/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.SequentialInterpreter
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.{ArithmeticSimplification, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Provable

/**
  * @author Nathan Fulton
  */
class ArithmeticSimplificationTests extends TacticTestBase {
  "Aggresive Simplifier" should "simplify x=1,y=1 ==> x=1 to x=1 ==> x=1" in {withMathematica(implicit qeTool => {
    val tactic = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) & ArithmeticSimplification.aggressivelySimplifyArith
    val result = proveBy("x=1 & y=1 -> x=1".asFormula, tactic)
    result.subgoals(0).ante shouldBe result.subgoals(0).succ
  })}

  "replaceTransform" should "work in the antecedent" in withMathematica { tool =>
    proveBy("t<=ep & v>=0 & x>=x_0+v*ep -> x>=x_0+v*t".asFormula,
      prop & replaceTransform("ep".asTerm, "t".asTerm)(-3) & closeId) shouldBe 'proved
  }

  it should "work in the succedent" in withMathematica { tool =>
    proveBy("t<=ep & v>=0 & x>=x_0+v*ep -> a<5 | x>=x_0+v*t | b<7".asFormula,
      prop & replaceTransform("t".asTerm, "ep".asTerm)(2) & closeId) shouldBe 'proved
  }
}
