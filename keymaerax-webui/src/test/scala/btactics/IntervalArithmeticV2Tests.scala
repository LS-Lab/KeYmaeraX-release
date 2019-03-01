package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.IntervalArithmeticV2._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.collection.immutable._

/** Tests for Interval Arithmetic
  * @author Fabian Immler
  */
class IntervalArithmeticV2Tests extends TacticTestBase  {

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
