package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleThrowable, Find}
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.infrastruct.AntePosition
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest

import scala.collection.immutable

import org.scalatest.LoneElement._

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.bellerophon.PositionLocator]]
 */
@SummaryTest
class LocateTests extends TacticTestBase {

  "'L" should "locate the sole applicable formula in antecedent" in withTactics {
    proveBy("x>0 & y>0 ==>".asSequent, TactixLibrary.andL('L)).subgoals.loneElement shouldBe "x>0, y>0 ==>".asSequent
  }

  it should "locate the first applicable formula in antecedent" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL('L)).subgoals.
      loneElement shouldBe "a=2, b=3 & c=4, x>0, y>0 ==>".asSequent
  }

  it should "locate the first applicable formula after start in antecedent" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL(Find.FindLAfter(None, AntePosition(3)))).subgoals.
      loneElement shouldBe "a=2, x>0 & y>0, b=3, c=4 ==>".asSequent
  }

  it should "locate the first applicable formula of a specific shape" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent,
      TactixLibrary.andL(Find.FindLPlain("b=3 & c=4".asFormula))).subgoals.
      loneElement shouldBe "a=2, x>0 & y>0, b=3, c=4 ==>".asSequent
  }

  it should "throw an exception if no applicable position can be found" in withTactics {
    val e = intercept[BelleThrowable] { proveBy("a=2, x>0 | y>0 ==>".asSequent, TactixLibrary.andL('L)) }
    e.getMessage should include ("Position tactic andL('L) is not applicable anywhere in antecedent")
  }

  it should "work with dependent position tactics" in withTactics {
    proveBy("x>0 & y>0 ==>".asSequent, TactixLibrary.step('L)).subgoals.loneElement shouldBe "x>0, y>0 ==>".asSequent
  }

  it should "find formulas by shape" in withTactics {
    proveBy("a=2&b=3, x>0 & y>0 ==>".asSequent, TactixLibrary.andL('L, "x>0 & y>0".asFormula)).subgoals.
      loneElement shouldBe "a=2&b=3, x>0, y>0 ==>".asSequent
  }

  it should "find terms by shape" in withTactics {
    proveBy("abs(x)>0 ==>".asSequent, TactixLibrary.abs('L, "abs(x)".asTerm)).subgoals.
      loneElement shouldBe "abs_>0, x>=0&abs_=x|x<0&abs_=-x ==>".asSequent
  }

  "'R" should "locate the sole applicable formula in succedent" in withTactics {
    proveBy("==> x>0 | y>0".asSequent, TactixLibrary.orR('R)).subgoals.loneElement shouldBe "==> x>0, y>0".asSequent
  }

  it should "locate the first applicable formula in antecedent" in withTactics {
    proveBy("==> a=2, x>0 | y>0, b=3 | c=4".asSequent, TactixLibrary.orR('R)).subgoals.
      loneElement shouldBe "==> a=2, b=3 | c=4, x>0, y>0".asSequent
  }

  it should "throw an exception if no applicable position can be found" in withTactics {
    val e = intercept[BelleThrowable] { proveBy("==> a=2, x>0 & y>0".asSequent, TactixLibrary.orR('R)) }
    e.getMessage should include ("Position tactic orR('R) is not applicable anywhere in succedent")
  }

  it should "work with dependent position tactics" in withTactics {
    proveBy("==> [?x>0;]x>0".asSequent, TactixLibrary.step('R)).subgoals.loneElement shouldBe "==> x>0 -> x>0".asSequent
  }

  it should "find formulas by shape" in withTactics {
    proveBy("==> a=2|b=3, x>0 | y>0".asSequent, TactixLibrary.orR('R, "x>0 | y>0".asFormula)).subgoals.
      loneElement shouldBe "==> a=2|b=3, x>0, y>0".asSequent
  }

  it should "find terms by shape" in withTactics {
    proveBy("==> abs(x)>0".asSequent, TactixLibrary.abs('R, "abs(x)".asTerm)).subgoals.
      loneElement shouldBe "x>=0&abs_=x|x < 0&abs_=-x ==> abs_>0".asSequent
  }

  "'_" should "locate the sole applicable formula in sequent" in withTactics {
    proveBy("==> x>0 | y>0".asSequent, TactixLibrary.orR('_)).subgoals.loneElement shouldBe "==> x>0, y>0".asSequent
  }

  it should "locate the first applicable formula" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL('_)).subgoals.
      loneElement shouldBe "a=2, b=3 & c=4, x>0, y>0 ==>".asSequent
  }

  it should "throw an exception if no applicable position can be found" in withTactics {
    val e = intercept[BelleThrowable] { proveBy("==> a=2, x>0 & y>0".asSequent, TactixLibrary.orR('_)) }
    e.getMessage should include ("Position tactic orR('R) is not applicable anywhere in succedent")
  }

  "'Llast" should "apply on last formula in antecedent" in withTactics {
    proveBy("a=2, x>0 & y>0, b=3 & c=4 ==>".asSequent, TactixLibrary.andL('Llast)).subgoals.
      loneElement shouldBe "a=2, x>0 & y>0, b=3, c=4 ==>".asSequent
  }

}
