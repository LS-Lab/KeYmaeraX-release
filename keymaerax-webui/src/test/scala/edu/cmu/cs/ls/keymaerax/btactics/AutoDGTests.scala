/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Completeness tests for DGauto tactic.
  * @author Nathan Fulton
  */
class AutoDGTests extends TacticTestBase {
  "autoDG" should "prove x>0 -> [{x'=-x}]x>0" in withMathematica(qeTool => {
    val f = "x>0 -> [{x'=-x}]x>0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.DGauto(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x>1 -> [{x'=-x}]x>0" in withMathematica(qeTool => {
    val f = "x>1 -> [{x'=-x}]x>0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.DGauto(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 is an equillibrium point of x'=x" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroEquilibrium(1)
    proveBy(f,t) shouldBe 'proved
  })

}
