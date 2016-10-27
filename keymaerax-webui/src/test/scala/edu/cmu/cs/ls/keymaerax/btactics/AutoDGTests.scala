/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Tests for DGauto tactic.
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

  "dgZeroEquillibrium" should "prove x=0 is an equillibrium point of x'=x" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroEquilibrium(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 -> [{x'=x^2}]x=0" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x^2}]x=0".asFormula
    val t =  TactixLibrary.implyR(1) & DifferentialTactics.dgZeroEquilibrium(1)
    proveBy(f,t) shouldBe 'proved
  })



  "x=0 & n>0 -> [{x'=x^n}]x=0" should "prove by custom tactic" in withMathematica(qeTool => {
    import TactixLibrary._
    import DifferentialTactics.{DA, diffInd}
    val t = implyR(1) & DA("y' = (-x^(n-1)/2)*y".asDifferentialProgram, "x*y^2=0&y>0".asFormula)(1) <(
      TactixLibrary.QE,
      implyR(1) & boxAnd(1) & andR(1) <(
        DifferentialTactics.diffInd()(1) & QE,
        DA("z' = (x^(n-1)/4) * z".asDifferentialProgram, "y*z^2 = 1".asFormula)(1) <(
          QE,
          implyR(1) & diffInd()(1) & QE
        )
      )
    )
    val f = "x=0 & n>0 -> [{x'=x^n}]x=0".asFormula
    this.proveBy(f,t) shouldBe 'proved
  })
}
