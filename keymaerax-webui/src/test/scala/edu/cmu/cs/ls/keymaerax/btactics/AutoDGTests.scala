/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.core._
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
  ignore should "prove x=0 & n>0 -> [{x'=c*x^n}]x=0" in withMathematica((qeTool => {
    val f = "x=0 & n>0 -> [{x'=c*x^n}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroMonomial(1)
    proveBy(f,t) shouldBe 'proved
  }))

  "dgZeroMonomial" should "prove x=0 is an eq point of x'=3*x^1" ignore withMathematica(qeTool => {
    val f = "x=0 -> [{x'=3*x^1}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroMonomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 is an eq point of x'=x" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroMonomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 -> [{x'=1*x^2}]x=0" ignore withMathematica(qeTool => {
    val f = "x=0 -> [{x'=1*x^2}]x=0".asFormula
    val t =  TactixLibrary.implyR(1) & DifferentialTactics.dgZeroMonomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 -> [{x'=x^2}]x=0" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x^2}]x=0".asFormula
    val t =  TactixLibrary.implyR(1) & DifferentialTactics.dgZeroMonomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 -> [{x'=5*x^2}]x=0" ignore withMathematica((qeTool => {
    val f = "x=0 -> [{x'=5*x^2}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroMonomial(1)
    proveBy(f,t) shouldBe 'proved
  }))

  "dgZeroPolynomial" should "prove x=0 -> [{x'=x+x}]x=0" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x+x}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroPolynomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove  x=0 -> [{x'=c*x^2+d*x^5}]x=0" in withMathematica(qeTool => {
    val f = " x=0 -> [{x'=c*x^2+d*x^5}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroPolynomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove  x=0 -> [{x'=c*x^2+d*x^5+e*x^20}]x=0" in withMathematica(qeTool => {
    val f = " x=0 -> [{x'=c*x^2+d*x^5+e*x^20}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroPolynomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x=0 -> [{x'=c*x+d*x^2+e*x^3}]x=0" in withMathematica(qeTool => {
    val f = "x=0 -> [{x'=c*x+d*x^2+e*x^3}]x=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroPolynomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  it should "prove x>=0 -> [{x'=c*x+d*x^2+e*x^3}]x>=0" ignore withMathematica(qeTool => {
    val f = "x>=0 -> [{x'=c*x+d*x^2+e*x^3}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & DifferentialTactics.dgZeroPolynomial(1)
    proveBy(f,t) shouldBe 'proved //@todo actually not sure dgZeroPolynomialDerivative is the right tactic for this.
  })

  it should "prove x=0 -> [{x'=x^2}]x=0" ignore withMathematica(qeTool => {
    val f = "x=0 -> [{x'=x^2}]x=0".asFormula
    val t =  TactixLibrary.implyR(1) & DifferentialTactics.dgZeroPolynomial(1)
    proveBy(f,t) shouldBe 'proved
  })

  /** @note please leave this here, because it's the "clear exposition of main idea" version of dgZero. */
  "canonical x=0 & n>0 -> [{x'=c*x^n}]x=0" should "prove by custom tactic" in withMathematica { _ =>
    import TactixLibrary._
    import DifferentialTactics.{DA, diffInd}
    val t = implyR(1) & DA("y' = ( (-c*x^(n-1)) / 2)*y".asDifferentialProgram, "x*y^2=0&y>0".asFormula)(1) &
      boxAnd(1, 0::Nil) & DifferentialTactics.diffInd()(1, 0::0::Nil) &
      DA("z' = (c*x^(n-1)/4) * z".asDifferentialProgram, "y*z^2 = 1".asFormula)(1, 0::1::Nil) &
      diffInd()(1, 0::1::0::Nil) & QE
    val f = "x=0 & n>0 -> [{x'=c*x^n}]x=0".asFormula
    val result = this.proveBy(f,t)
    result shouldBe 'proved
  }


  //region helper methods

  "TacticHelper.transformMonomial" should "work" in {
    val result = TacticHelper.transformMonomials("2*x^2 + 3*x^3".asTerm, (t:Term) => t match {
      case Times(coeff, Power(v,exp)) => Times(coeff, Power(v, Minus(exp, Number(1))))
    })

    println(result)
  }

  //endregion
}
