package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.IntervalArithmeticV2._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.collection.immutable._

/** Tests for Interval Arithmetic
  * @author Fabian Immler
  */
class IntervalArithmeticV2Tests extends TacticTestBase  {

  "proveBounds" should "pick up all kinds of constraints" in withMathematica { qeTool =>
    val assms = IndexedSeq("a = 0", "1 = b", "2 < c", "c < 3", "d <= 4", "5 <= d", "e >= 6", "7 >= e", "f > 8", "9 > f") map (_.asFormula)
    val (lowers, uppers) = proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap())("0".asTerm)
    ("a,b,c,d,e,f" split(',')).toList.map(_.asTerm).forall(t => lowers.isDefinedAt(t) && uppers.isDefinedAt(t)) shouldBe true
  }

  "proveBounds" should "pick up all kinds of non-numbers" in withMathematica { qeTool =>
    val assms = IndexedSeq("0 <= f(x)", "f(x) <= 1", "0 <= x", "x <= 1", "0 <= c()", "c() <= 1") map (_.asFormula)
    val (lowers, uppers) = proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap())("0".asTerm)
    ("f(x),x,c()" split(',')).toList.map(_.asTerm).forall(t => lowers.isDefinedAt(t) && uppers.isDefinedAt(t)) shouldBe true
  }

  val seq0 = ("0 <= a, a <= 3, 2 <= b, b <= 4, 3 <= c, c <= 7 ==>" +
    "(a*b+c*a^4*b^7+a^5*c^7)+(a + 2*b)^5+(0.123456*a*c + (42*a + 17*b + 0.001 * c)^9)+" +
    "(a^7*b^6+c^9*a^6*b^5+a^4*c^8)<=38945*10^16").asSequent

  "seq0" should "prove with interval arithmetic" in withMathematica { _ =>
    val res = proveBy(seq0, intervalCut(1, 0::Nil) & closeId)
    res shouldBe 'proved
  }

  "seq0" should "prove I don't know how slow with QE" in withMathematica { _ =>
    val res = proveBy(seq0, QE)
    res shouldBe 'proved
  }

  val seq1 = ("0 <= a, a <= 3, 2 <= b, b <= 4, 3 <= c, c <= 7 ==>" +
    "(a*b+c*a^4*b^7+a^5*c^7)*(a + 2*b)^5*(0.123456*a*c + (42*a + 17*b + 0.001 * c)^9)*" +
    "(a^7*b^6+c^9*a^6*b^5+a^4*c^8)<=39577*10^43").asSequent

  "seq1" should "prove with interval arithmetic" in withMathematica { _ =>
    val res = proveBy(seq1, intervalCut(1, 0::Nil) & closeId)
    res shouldBe 'proved
  }

  "seq1" should "prove I don't know how slow with QE" in withMathematica { _ =>
    val res = proveBy(seq1, QE)
    res shouldBe 'proved
  }
}
