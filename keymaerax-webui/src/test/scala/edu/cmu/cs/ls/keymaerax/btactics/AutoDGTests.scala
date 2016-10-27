/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core.Lemma
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
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

  //@todo There are two bugs here.
  //@todo BUG 1 in DGAuto -- this test case fails whenever the optional "useAt" strategy is removed from dgZero.
  //@todo BUG 2 in useAt -- should match on the correct side.
  it should "prove x=0 & n>0 -> [{x'=c*x^n}]x=0" in withMathematica((qeTool => {
    val f = "x=0 & n>0 -> [{x'=c*x^n}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZero(1)
    proveBy(f,t) shouldBe 'proved
  }))

  "dgZeroEquilibrium" should "prove x=0 is an eq point of x'=3*x^1" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=3*x^1}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZero(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 is an eq point of x'=x" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZero(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 -> [{x'=1*x^2}]x=0" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=1*x^2}]x=0".asFormula
    val t =  TactixLibrary.implyR(1) & DifferentialTactics.dgZero(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 -> [{x'=x^2}]x=0" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x^2}]x=0".asFormula
    val t =  TactixLibrary.implyR(1) & DifferentialTactics.dgZero(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 -> [{x'=5*x^2}]x=0" in withMathematica((qeTool => {
    val f = "x=0 -> [{x'=5*x^2}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZero(1)
  }))

  "x=0 & n>0 -> [{x'=c*x^n}]x=0" should "prove by custom tactic" in withMathematica(qeTool => {
    import TactixLibrary._
    import DifferentialTactics.{DA, diffInd}
    val t = implyR(1) & DA("y' = ( (-c*x^(n-1)) / 2)*y".asDifferentialProgram, "x*y^2=0&y>0".asFormula)(1) <(
      TactixLibrary.QE,
      implyR(1) & boxAnd(1) & andR(1) <(
        DifferentialTactics.diffInd()(1) & QE,
        DA("z' = (c*x^(n-1)/4) * z".asDifferentialProgram, "y*z^2 = 1".asFormula)(1) <(
          QE,
          implyR(1) & diffInd()(1) & QE
        )
      )
    )
    val f = "x=0 & n>0 -> [{x'=c*x^n}]x=0".asFormula
    val result = this.proveBy(f,t)
    result shouldBe 'proved

  })
}
