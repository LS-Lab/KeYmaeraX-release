/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{BelleThrowable, Find}
import org.keymaerax.infrastruct.AntePosition
import org.keymaerax.parser.StringConverter._
import org.keymaerax.tags.SummaryTest

import org.scalatest.LoneElement._

/** Tests [[org.keymaerax.bellerophon.PositionLocator]] */
@SummaryTest
class LocateTests extends TacticTestBase {

  "'L" should "locate the sole applicable formula in antecedent" in withTactics {
    proveBy("x>0 & y>0 ==>".asSequent, TactixLibrary.andL(Symbol("L"))).subgoals.loneElement shouldBe
      "x>0, y>0 ==>".asSequent
  }

  it should "locate the first applicable formula in antecedent" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL(Symbol("L"))).subgoals.loneElement shouldBe
      "a=2, b=3 & c=4, x>0, y>0 ==>".asSequent
  }

  it should "locate the first applicable formula after start in antecedent" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL(Find.FindLAfter(None, AntePosition(3))))
      .subgoals
      .loneElement shouldBe "a=2, x>0 & y>0, b=3, c=4 ==>".asSequent
  }

  it should "locate the first applicable formula of a specific shape" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL(Find.FindLPlain("b=3 & c=4".asFormula)))
      .subgoals
      .loneElement shouldBe "a=2, x>0 & y>0, b=3, c=4 ==>".asSequent
  }

  it should "throw an exception if no applicable position can be found" in withTactics {
    val e = intercept[BelleThrowable] { proveBy("a=2, x>0 | y>0 ==>".asSequent, TactixLibrary.andL(Symbol("L"))) }
    e.getMessage should
      include("Not found: locator 'L\nof position tactic andL('L)\ndoes not match anywhere in antecedent")
  }

  it should "work with dependent position tactics" in withTactics {
    proveBy("x>0 & y>0 ==>".asSequent, TactixLibrary.step(Symbol("L"))).subgoals.loneElement shouldBe
      "x>0, y>0 ==>".asSequent
  }

  it should "find formulas by shape" in withTactics {
    proveBy("a=2&b=3, x>0 & y>0 ==>".asSequent, TactixLibrary.andL(Symbol("L"), "x>0 & y>0".asFormula))
      .subgoals
      .loneElement shouldBe "a=2&b=3, x>0, y>0 ==>".asSequent
  }

  it should "find terms by shape" in withTactics {
    proveBy("abs(x)>0 ==>".asSequent, TactixLibrary.abs(Symbol("L"), "abs(x)".asTerm)).subgoals.loneElement shouldBe
      "abs_>0, x>=0&abs_=x|x<0&abs_=-x ==>".asSequent
  }

  "'R" should "locate the sole applicable formula in succedent" in withTactics {
    proveBy("==> x>0 | y>0".asSequent, TactixLibrary.orR(Symbol("R"))).subgoals.loneElement shouldBe
      "==> x>0, y>0".asSequent
  }

  it should "locate the first applicable formula in antecedent" in withTactics {
    proveBy("==> a=2, x>0 | y>0, b=3 | c=4".asSequent, TactixLibrary.orR(Symbol("R"))).subgoals.loneElement shouldBe
      "==> a=2, b=3 | c=4, x>0, y>0".asSequent
  }

  it should "throw an exception if no applicable position can be found" in withTactics {
    val e = intercept[BelleThrowable] { proveBy("==> a=2, x>0 & y>0".asSequent, TactixLibrary.orR(Symbol("R"))) }
    e.getMessage should
      include("Not found: locator 'R\nof position tactic orR('R)\ndoes not match anywhere in succedent")
  }

  it should "work with dependent position tactics" in withTactics {
    proveBy("==> [?x>0;]x>0".asSequent, TactixLibrary.step(Symbol("R"))).subgoals.loneElement shouldBe
      "==> x>0 -> x>0".asSequent
  }

  it should "find formulas by shape" in withTactics {
    proveBy("==> a=2|b=3, x>0 | y>0".asSequent, TactixLibrary.orR(Symbol("R"), "x>0 | y>0".asFormula))
      .subgoals
      .loneElement shouldBe "==> a=2|b=3, x>0, y>0".asSequent
  }

  it should "find terms by shape" in withTactics {
    proveBy("==> abs(x)>0".asSequent, TactixLibrary.abs(Symbol("R"), "abs(x)".asTerm)).subgoals.loneElement shouldBe
      "x>=0&abs_=x|x < 0&abs_=-x ==> abs_>0".asSequent
  }

  "'_" should "locate the sole applicable formula in sequent" in withTactics {
    proveBy("==> x>0 | y>0".asSequent, TactixLibrary.orR(Symbol("_"))).subgoals.loneElement shouldBe
      "==> x>0, y>0".asSequent
  }

  it should "locate the first applicable formula" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL(Symbol("_"))).subgoals.loneElement shouldBe
      "a=2, b=3 & c=4, x>0, y>0 ==>".asSequent
  }

  it should "throw an exception if no applicable position can be found" in withTactics {
    val e = intercept[BelleThrowable] { proveBy("==> a=2, x>0 & y>0".asSequent, TactixLibrary.orR(Symbol("_"))) }
    e.getMessage should
      include("Not found: locator 'R\nof position tactic orR('R)\ndoes not match anywhere in succedent")
  }

  "'Llast" should "apply on last formula in antecedent" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL(Symbol("Llast")))
      .subgoals
      .loneElement shouldBe "a=2, x>0 & y>0, b=3, c=4 ==>".asSequent
  }

}
