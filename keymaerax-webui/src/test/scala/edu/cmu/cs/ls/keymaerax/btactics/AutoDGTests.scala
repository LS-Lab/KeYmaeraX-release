/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.TodoTest

/**
  * Tests for DGauto tactic.
  * @author Nathan Fulton
  */
class AutoDGTests extends TacticTestBase {
  "autoDG" should "prove x>0 -> [{x'=-x}]x>0" in withMathematica { _ =>
    proveBy("x>0 ==> [{x'=-x}]x>0".asSequent, DifferentialTactics.DGauto(1)) shouldBe Symbol("proved")
  }

  it should "prove x>1 -> [{x'=-x}]x>0" in withMathematica { _ =>
    proveBy("x>1 ==> [{x'=-x}]x>0".asSequent, DifferentialTactics.DGauto(1)) shouldBe Symbol("proved")
  }

  "autoDbxDG" should "prove x=0 is an eq point of x'=3*x^1" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=3*x^1}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: prove x=0 & n>0 -> [{x'=c*x^n}]x=0" taggedAs TodoTest in withMathematica { _ =>
    proveBy("x=0 & n>0 ==> [{x'=c*x^n}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove x=0 is an eq point of x'=x" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=x}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove x=0 -> [{x'=1*x^2}]x=0" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=1*x^2}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove x=0 -> [{x'=x^2}]x=0" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=x^2}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove x=0 -> [{x'=5*x^2}]x=0" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=5*x^2}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove x=0 -> [{x'=x+x}]x=0" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=x+x}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove  x=0 -> [{x'=c*x^2+d*x^5}]x=0" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=c*x^2+d*x^5}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove  x=0 -> [{x'=c*x^2+d*x^5+e*x^20}]x=0" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=c*x^2+d*x^5+e*x^20}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove x=0 -> [{x'=c*x+d*x^2+e*x^3}]x=0" in withMathematica { _ =>
    proveBy("x=0 ==> [{x'=c*x+d*x^2+e*x^3}]x=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  it should "prove x>=0 -> [{x'=c*x+d*x^2+e*x^3}]x>=0" in withMathematica { _ =>
    proveBy("x>=0 ==> [{x'=c*x+d*x^2+e*x^3}]x>=0".asSequent, DifferentialTactics.dgDbxAuto(1)) shouldBe Symbol("proved")
  }

  /** @note please leave this here, because it's the "clear exposition of main idea" version of dgZero. */
  "canonical x=0 & n>0 -> [{x'=c*x^n}]x=0" should "prove by custom tactic" in withMathematica { _ =>
    import TactixLibrary.{dG, boxAnd, dI, QE}
    val t = dG("y' = ( (-c*x^(n-1)) / 2)*y".asDifferentialProgram, Some("x*y^2=0&y>0".asFormula))(1) &
      boxAnd(1, 0::Nil) & DifferentialTactics.diffInd()(1, 0::0::Nil) &
      dG("z' = (c*x^(n-1)/4) * z".asDifferentialProgram, Some("y*z^2 = 1".asFormula))(1, 0::1::Nil) &
      dI()(1, 0::1::0::Nil) & QE
    proveBy("x=0 & n>0 ==> [{x'=c*x^n}]x=0".asSequent, t) shouldBe Symbol("proved")
  }

  //region helper methods

  "TacticHelper.transformMonomial" should "work" in withTactics {
    TacticHelper.transformMonomials("2*x^2 + 3*x^3".asTerm, {
      case Times(coeff, Power(v,exp)) => Times(coeff, Power(v, Minus(exp, Number(1))))
      case t => t
    }) shouldBe "2*x^(2-1) + 3*x^(3-1)".asTerm
  }

  //endregion
}
