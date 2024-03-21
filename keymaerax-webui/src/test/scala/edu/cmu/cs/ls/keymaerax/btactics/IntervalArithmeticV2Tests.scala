/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics.IntervalArithmeticV2._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Neg, Plus, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tagobjects.SlowTest
import org.scalatest.LoneElement._

import scala.collection.immutable._

/**
 * Tests for Interval Arithmetic
 * @author
 *   Fabian Immler
 */
object IntervalArithmeticV2Tests {
  def timing[B](s: String)(f: () => B): B = {
    val tic = System.nanoTime()
    val res = f()
    val toc = System.nanoTime()
    System.out.println("Timing for " + s + ": " + (toc - tic) / 1000000000.0 + "s")
    res
  }
}

class IntervalArithmeticV2Tests extends TacticTestBase {

  "proveBounds" should "pick up all kinds of constraints" in withMathematica { qeTool =>
    val assms =
      IndexedSeq("a = 0", "1 = b", "2 < c", "c < 3", "d <= 4", "5 <= d", "e >= 6", "7 >= e", "f > 8", "9 > f") map
        (_.asFormula)
    val (lowers, uppers) = proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap(), Map())(List("0".asTerm))
    ("a,b,c,d,e,f" split (','))
      .toList
      .map(_.asTerm)
      .forall(t => lowers.isDefinedAt(t) && uppers.isDefinedAt(t)) shouldBe true
  }

  it should "pick up all kinds of non-numbers" in withMathematica { qeTool =>
    val assms = IndexedSeq("0 <= f(x)", "f(x) <= 1", "0 <= x", "x <= 1", "0 <= c()", "c() <= 1") map (_.asFormula)
    val (lowers, uppers) = proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap(), Map())(List("0".asTerm))
    ("f(x),x,c()" split (',')).toList.map(_.asTerm).forall(t => lowers.isDefinedAt(t) && uppers.isDefinedAt(t)) shouldBe
      true
  }

  it should "pick up numeric constraints" in withMathematica { qeTool =>
    val assms = IndexedSeq("1 + 2 <= x", "x <= 4*5") map (_.asFormula)
    val (lowers, uppers) = proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap(), Map())(List("0".asTerm))
    val x = "x".asVariable
    lowers.isDefinedAt(x) shouldBe true
  }

  it should "pick up interpreted functions in constraints" in withMathematica { qeTool =>
    val assms = IndexedSeq("min(1, 2) <= x", "x <= max(4,5)") map (_.asFormula)
    val (lowers, uppers) = proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap(), Map())(List("0".asTerm))
    val x = "x".asVariable
    lowers.isDefinedAt(x) shouldBe true
  }

  it should "compute bounds given by interpreted functions" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val assms = IndexedSeq("min(1, 2) <= x", "x <= max(4,5)", "max(1, 2) <= y", "y <= min(4,5)") map (_.asFormula)
      val (lowers, uppers) = proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap(), Map())(List("x + y".asTerm))
      val x = "x".asVariable
      lowers(x) shouldBe Symbol("proved")
      lowers(x).conclusion.ante shouldBe assms
      lowers(x).conclusion.succ.loneElement shouldBe "min(1,2)<=x".asFormula
      uppers(x) shouldBe Symbol("proved")
      uppers(x).conclusion.ante shouldBe assms
      uppers(x).conclusion.succ.loneElement shouldBe "x <= max(4, 5)".asFormula
    }
  }

  it should "compute with interpreted functions" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val assms = IndexedSeq("1 <= x", "x <= 2", "3 <= y", "y <= 5") map (_.asFormula)
      val t = "min(x, y) + max(x, y)".asTerm
      val (lowers, uppers) = proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap(), Map())(List(t))
      lowers(t) shouldBe Symbol("proved")
      lowers(t).conclusion.ante shouldBe assms
      lowers(t).conclusion.succ.loneElement shouldBe "4*10^0<=min((x,y))+max((x,y))".asFormula
      uppers(t) shouldBe Symbol("proved")
      uppers(t).conclusion.ante shouldBe assms
      uppers(t).conclusion.succ.loneElement shouldBe "min((x,y))+max((x,y))<=7*10^0".asFormula
    }
  }

  it should "work with a precomputed static single assignment form" in withMathematica { qeTool =>
    val assms = IndexedSeq("0 <= a", "a <= 1", "2<=b", "b<=3") map (_.asFormula)
    val ssa = new StaticSingleAssignmentExpression("(a*b + a*b)*(a*b + a*b)+a*b*b+a*(a*b)".asTerm)
    val (lowers, uppers) =
      proveBounds(5)(qeTool)(assms)(true)(BoundMap(), BoundMap(), ssa.unfoldMap)(List(ssa.expression))
    println(lowers)
    println(uppers)
  }

  val xyz_bounds = IndexedSeq("(-10) <= f(x)", "f(x) <= 1", "(-3) <= x", "x <= (-1)", "2 <= c()", "c() <= 4")
    .map(_.asFormula)

  "intervalCutTerms" should "work with all supported operations" in withMathematica { _ =>
    val res = proveBy(
      Sequent(
        xyz_bounds,
        IndexedSeq(
          ("-13<=x+f(x) & x+f(x)<=0 &" + "-3<=x*f(x) & x*f(x)<=30 &" + "-7<=x-c() & x-c()<=-3 &" +
            "-1<=-f(x) & -f(x)<=10 &" + "-10<=f(x)/x^2 & f(x)/x^2<=1 &" + "0<=f(x)^2 & f(x)^2<=100 &" +
            "1<=x^2 & x^2<=9 &" + "4<=c()^2 & c()^2<=16 &" + "-1000<=f(x)^3 & f(x)^3<=1 &" + "-27<=x^3 & x^3<=-1 &" +
            "8<=c()^3 & c()^3<=64 &" + "25*10^(-2)<=c()^(-1) & c()^(-1)<=5*10^(-1) &" +
            "625*10^(-4)<=c()^(-2) & c()^(-2)<=25*10^(-2) &" + "15625*10^(-6)<=c()^(-3) & c()^(-3)<=125*10^(-3) &" +
            "1<=c()^0 & c()^0<=1 &" + "1<=x^0 & x^0<=1 &" + "-1<=x^(-1) & x^(-1)<=(-33333)*10^(-5) &" +
            "11111*10^(-5)<=x^(-2) & x^(-2)<=1 &" + "-1<=x^(-3) & x^(-3)<=(-37037)*10^(-6)").asFormula
        ),
      ),
      intervalCutTerms(Seq(
        "x+f(x)".asTerm,
        "x*f(x)".asTerm,
        "x - c()".asTerm,
        "-f(x)".asTerm,
        "f(x)/(x^2)".asTerm,
        "f(x)^2".asTerm,
        "x^2".asTerm,
        "c()^2".asTerm,
        "f(x)^3".asTerm,
        "x^3".asTerm,
        "c()^3".asTerm,
        "c()^0".asTerm,
        "c()^(-1)".asTerm,
        "c()^(-2)".asTerm,
        "c()^(-3)".asTerm,
        "x^0".asTerm,
        "x^(-1)".asTerm,
        "x^(-2)".asTerm,
        "x^(-3)".asTerm,
      )) & SimplifierV3.fullSimpTac() & prop,
    )
    res shouldBe Symbol("proved")
  }

  "intervalCut" should "cut in bounds for the term at the given Position" in withMathematica { qeTool =>
    proveBy("0<=a,a<=1,4<=b, b<=10 ==> a*b <= 15".asSequent, intervalCut(1, 0 :: Nil)).subgoals shouldBe
      (IndexedSeq("0<=a, a<=1, 4<=b, b<=10, 0*10^0<=a*b, a*b<=10*10^0  ==>  a*b<=15".asSequent))
  }

  val seq0 =
    ("0 <= a, a <= 3, 2 <= b, b <= 4, 3 <= c, c <= 7 ==>" +
      "(a*b+c*a^4*b^7+a^5*c^7)+(a + 2*b)^5+(0.123456*a*c + (42*a + 17*b + 0.001 * c)^9)+" +
      "(a^7*b^6+c^9*a^6*b^5+a^4*c^8)<=38945*10^16").asSequent

  "seq0" should "prove with interval arithmetic" in withMathematica { _ =>
    val res = proveBy(seq0, intervalCut(1, 0 :: Nil) & id)
    res shouldBe Symbol("proved")
  }

  val seq1 =
    ("0 <= a, a <= 3, 2 <= b, b <= 4, 3 <= c, c <= 7 ==>" +
      "(a*b+c*a^4*b^7+a^5*c^7)*(a + 2*b)^5*(0.123456*a*c + (42*a + 17*b + 0.001 * c)^9)*" +
      "(a^7*b^6+c^9*a^6*b^5+a^4*c^8)<=39577*10^43").asSequent

  "seq1" should "prove with interval arithmetic" in withMathematica { _ =>
    val res = proveBy(seq1, intervalCut(1, 0 :: Nil) & id)
    res shouldBe Symbol("proved")
  }

  it should "work with non-constant numerical bounds" in withMathematica { _ =>
    proveBy(
      "1/3<=x, x<=5*10^(-1)==>66666*10^(-5)<=2*x&2*x<=10*10^(-1)".asSequent,
      intervalCutTerms(Seq("2*x".asTerm)) & prop,
    ) shouldBe Symbol("proved")
  }

  it should "cut bounds for all terms" in withMathematica { _ =>
    val res = proveBy("0<=x,x<=1,4<=y,y<=5==>P(x+y)&Q{x*y>=0}&x<y".asSequent, intervalCut(1))
    res.subgoals.loneElement.ante shouldBe
      ((("0<=x,x<=1,4<=y,y<=5,4*10^0<=x+y,x+y<=6*10^0,0*10^0<=x*y,x*y<=5*10^0,0<=0,0<=0,0<=x,x<=1,4<=y,y<=5")
        .split(',')
        .map(_.asFormula)).toVector)
  }

  ignore should "prove seq0 I don't know how slow with QE" in withMathematica { _ =>
    val res = proveBy(seq0, QE)
    res shouldBe Symbol("proved")
  }

  ignore should "prove seq1 I don't know how slow with QE" in withMathematica { _ =>
    val res = proveBy(seq1, QE)
    res shouldBe Symbol("proved")
  }

  val seq2 =
    ("0 <= x, x <= 1, 2 <= y, y <= 4, 0 <= z, z <= 1, 2 <= a, a <= 4, 2 <= b, b <= 4, 2 <= c, c <= 4, 2 <= d, d <= 4, 2 <= e, e <= 4, 2 <= f, f <= 4, 2 <= g, g <= 4, 2 <= h, h <= 4," +
      "0 <= i, i <= 1, 2 <= j, j <= 4, 0 <= k, k <= 1, 2 <= l, l <= 4, 2 <= m, m <= 4, 2 <= n, n <= 4, 2 <= o, o <= 4, 2 <= p, p <= 4, 2 <= q, q <= 4, 2 <= r, r <= 4, 2 <= s, s <= 4" +
      "==>" + "a*b+c*d*(e+f*g*h+x*y*z + i*j*k*(l + (m*n*(o + (p*q - r*s))))) <= 17808*10^0").asSequent

  "intervalArithmetic" should "prove Comparisons in succedent" in withMathematica { _ =>
    proveBy("0<=a,a<=1,2<=b,b<=5 ==> a*b - a <= 5".asSequent, intervalArithmetic) shouldBe Symbol("proved")
    proveBy("0<=a,a<=1,2<=b,b<=5 ==> a*b - a < 6".asSequent, intervalArithmetic) shouldBe Symbol("proved")
    proveBy("0<=a,a<=1,2<=b,b<=5 ==> a*b - a >= -1".asSequent, intervalArithmetic) shouldBe Symbol("proved")
    proveBy("0<=a,a<=1,2<=b,b<=5 ==> a*b - a > -2".asSequent, intervalArithmetic) shouldBe Symbol("proved")

    proveBy("0<=a,a<=1,2<=b,b<=5 ==> 5 >= a*b - a".asSequent, intervalArithmetic) shouldBe Symbol("proved")
    proveBy("0<=a,a<=1,2<=b,b<=5 ==> 6 > a*b - a".asSequent, intervalArithmetic) shouldBe Symbol("proved")
    proveBy("0<=a,a<=1,2<=b,b<=5 ==> -1 <= a*b - a".asSequent, intervalArithmetic) shouldBe Symbol("proved")
    proveBy("0<=a,a<=1,2<=b,b<=5 ==> -2 < a*b - a".asSequent, intervalArithmetic) shouldBe Symbol("proved")
  }

  it should "prove powers of 0" in withMathematica { _ =>
    proveBy(
      "-2 <= a, a <= -1, b = 1, 1 <= c, c <= 2 ==> a^0 = 1 & b^0 = 1 & c^0 = 1".asSequent,
      intervalArithmetic,
    ) shouldBe Symbol("proved")
  }

  "intervalArithmetic" should "cooperate with prop" in withMathematica { _ =>
    proveBy("(0<=a&a<=1&2<=b&b<=5)->(-2 < a*b - a & a*b - a <= 5)".asFormula, prop & OnAll(intervalArithmetic)) shouldBe
      Symbol("proved")
  }

  "IA subgoal for low order TM" should "prove #1" in withMathematica { _ =>
    val seq =
      "t_0=0, I1() < 0.00000000010, -0.00000000010 < I1(), -0.00000000010 < I0(), I0() < 0.00000000010, y0() < 1, -1 < y0(), -1 < x0(), x0() < 1, x_0=1+x0()+y0()+I0(), y_0=0.1+0.5*x0()-y0()+I1(), t_0<=0.02, 0<=t, t<=0.02, -335074577049867*10^(-16) < rem0, rem0 < 332987591698456*10^(-16), -165372880199332*10^(-15) < rem1, rem1 < 164937953442280*10^(-15)\n  ==>  (-83268644009967/50000000000000+-1*rem1+-1/2*x0()+y0())*1<=0"
        .asSequent
    val res = proveBy(seq, intervalArithmetic)
    res shouldBe Symbol("proved")
  }
  "IA subgoal for low order TM" should "prove #2" in withMathematica { _ =>
    val seq =
      "t_0=0, I1() < 0.00000000010, -0.00000000010 < I1(), -0.00000000010 < I0(), I0() < 0.00000000010, y0() < 1, -1 < y0(), -1 < x0(), x0() < 1, x_0=1+x0()+y0()+I0(), y_0=0.1+0.5*x0()-y0()+I1(), t_0<=0.02, 0<=t, t<=0.02, -335074577049867*10^(-16) < rem0, rem0 < 332987591698456*10^(-16), -165372880199332*10^(-15) < rem1, rem1 < 164937953442280*10^(-15)\n  ==>  (-41623448836057/25000000000000+rem1+1/2*x0()+-1*y0())*1<=0"
        .asSequent
    val res = proveBy(seq, intervalArithmetic)
    res shouldBe Symbol("proved")
  }
  "IA subgoal for low order TM" should "prove #3" in withMathematica { _ =>
    val seq =
      "t_0=0, I1() < 0.00000000010, -0.00000000010 < I1(), -0.00000000010 < I0(), I0() < 0.00000000010, y0() < 1, -1 < y0(), -1 < x0(), x0() < 1, x_0=1+x0()+y0()+I0(), y_0=0.1+0.5*x0()-y0()+I1(), t_0<=0.02, 0<=t, t<=0.02, -335074577049867*10^(-16) < rem0, rem0 < 332987591698456*10^(-16), -165372880199332*10^(-15) < rem1, rem1 < 164937953442280*10^(-15)\n  ==>  (-102521876236019/12500000000000+rem0^2+2*x0()+2*y0()+(x0()+y0())^2+2*rem0*(1+x0()+y0()))*1+(-55915715877171/12500000000000+11/5*rem0+11/5*x0()+11/5*y0())*t^1+-1/500000000000000*t^2<=0\n"
        .asSequent
    val res = proveBy(seq, intervalArithmetic)
    res shouldBe Symbol("proved")
  }
  "IA subgoal for low order TM" should "prove #4" in withMathematica { _ =>
    val seq =
      "t_0=0, I1() < 0.00000000010, -0.00000000010 < I1(), -0.00000000010 < I0(), I0() < 0.00000000010, y0() < 1, -1 < y0(), -1 < x0(), x0() < 1, x_0=1+x0()+y0()+I0(), y_0=0.1+0.5*x0()-y0()+I1(), t_0<=0.02, 0<=t, t<=0.02, -335074577049867*10^(-16) < rem0, rem0 < 332987591698456*10^(-16), -165372880199332*10^(-15) < rem1, rem1 < 164937953442280*10^(-15)\n  ==>  (-410108025149723/50000000000000+-1*rem0^2+-2*x0()+-2*y0()+-1*(x0()+y0())^2+-2*rem0*(1+x0()+y0()))*1+(-223685820347549/50000000000000+-11/5*rem0+-11/5*x0()+-11/5*y0())*t^1+-1/1000000000000000*t^2<=0"
        .asSequent
    val res = proveBy(seq, intervalArithmetic)
    res shouldBe Symbol("proved")
  }
  "IA with disjunction" should "prove" in withMathematica { _ =>
    val seq = "-1 <= x , x <= 1 ==> x+x <= 1, x*x <= 1, x - x <= 1".asSequent
    val res = proveBy(seq, intervalArithmetic)
    res shouldBe Symbol("proved")
  }
  "IA preproc" should "preprocess" in withMathematica { _ =>
    val res = proveBy(
      ("(x > 0 & (x <= 0 | x < 0 -> x >0 ) <-> (x = 0 | x >= 0)) <->" +
        "!(x > 0 & (x <= 0 | x < 0 -> x >0 ) <-> (x = 0 | x >= 0))").asFormula,
      intervalArithmeticPreproc(1),
    )
    res.subgoals.loneElement.succ.loneElement shouldBe
      ("((x>0&(x>0&x>=0|x>0))&(x<=0&x>=0|x>=0)|(x<=0|(x<=0|x<0)&x<=0)&(x<0|x>0)&x<0)&" +
        "((x>0&(x>0&x>=0|x>0))&(x<0|x>0)&x<0|(x<=0|(x<=0|x<0)&x<=0)&(x<=0&x>=0|x>=0))|" +
        "((x>0&(x>0&x>=0|x>0))&(x<0|x>0)&x<0|(x<=0|(x<=0|x<0)&x<=0)&(x<=0&x>=0|x>=0))&" +
        "((x>0&(x>0&x>=0|x>0))&(x<=0&x>=0|x>=0)|(x<=0|(x<=0|x<0)&x<=0)&(x<0|x>0)&x<0)").asFormula
  }
  it should "prove" in withMathematica { _ =>
    val seq = "0 <= x, x <= 1, -1 <= y, y <= 2 ==> (x < -1 -> y >= 0)".asSequent
    val res = proveBy(seq, intervalArithmetic)
    res shouldBe Symbol("proved")
  }

  "intervalCut" should "be fast" in withMathematica { _ =>
    IntervalArithmeticV2Tests.timing("intervalCut")(() => proveBy(seq2, intervalCut(1, 0 :: Nil) & prop & done))
    IntervalArithmeticV2Tests.timing("intervalCut (again)")(() => proveBy(seq2, intervalCut(1, 0 :: Nil) & prop & done))
    IntervalArithmeticV2Tests.timing("intervalCut (again)")(() => proveBy(seq2, intervalCut(1, 0 :: Nil) & prop & done))
  }
  "Slow.intervalArithmetic" should "be slow" taggedAs SlowTest in withMathematica { _ =>
    IntervalArithmeticV2Tests.timing("intervalArithmetic")(() => proveBy(seq2, Slow.intervalArithmetic & done))
    IntervalArithmeticV2Tests.timing("intervalArithmetic (again)")(() => proveBy(seq2, Slow.intervalArithmetic & done))
    IntervalArithmeticV2Tests.timing("intervalArithmetic (again)")(() => proveBy(seq2, Slow.intervalArithmetic & done))
  }

  "proveBinop" should "prove binary operations" in withMathematica { qeTool =>
    val (res, _, _) = IntervalArithmeticV2
      .proveBinop(qeTool)(10)(IndexedSeq())(Plus)("0.1".asTerm, "0.3".asTerm)("0.4".asTerm, "0.8".asTerm)
    res shouldBe Symbol("proved")
    res.conclusion.succ.loneElement shouldBe
      "\\forall i1_ \\forall i2_ (0.1<=i1_&i1_<=0.3&0.4<=i2_&i2_<=0.8->5*10^(-1)<=i1_+i2_&i1_+i2_<=11*10^(-1))"
        .asFormula
  }

  "proveUnop" should "prove unary operations" in withMathematica { qeTool =>
    val (res, _, _) = IntervalArithmeticV2.proveUnop(qeTool)(10)(IndexedSeq())(Neg)("0.1".asTerm, "0.3".asTerm)
    res shouldBe Symbol("proved")
    res.conclusion.succ.loneElement shouldBe
      "\\forall i1_ (0.1<=i1_&i1_<=0.3->(-3)*10^(-1)<=-i1_&-i1_<=(-1)*10^(-1))".asFormula
  }

  "SSAMap" should "extract subterms" in withMathematica { _ =>
    val fml = "a*b >= a*b".asFormula
    val pp = new KeYmaeraXPrettierPrinter(120)
    val ssa = new StaticSingleAssignmentExpression(fml)
    ssa.expression shouldBe "ssa2_ >= ssa2_".asFormula
    ssa.unfoldMap shouldBe Map(
      "ssa0_".asVariable -> "a".asTerm,
      "ssa1_".asVariable -> "b".asTerm,
      "ssa2_".asVariable -> "ssa0_*ssa1_".asTerm,
    )
  }

}
