/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.OnAll
import org.keymaerax.btactics.PolynomialArithV2._
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.core._
import org.keymaerax.parser.StringConverter._
import org.keymaerax.tags.SlowTest

import scala.collection.immutable._

/** Created by yongkiat on 11/27/16. */
@SlowTest
class WitnessArithTests extends TacticTestBase {

  /* Diff. Invariant arithmetic examples */
  "InvariantArith" should "solve Lecture 10 DI arithmetic" in withMathematica { qeTool =>
    // All of these prove by normalizing both sides to 0 = 0
    // L10 Example 1
    val i1 = "v^2 + w^2 = r()^2 -> [{v'=w,w'=-v}] v^2+w^2 = r()^2"
    // L10 Example 11
    val i2 = "x^2+x^3-y^2 - c() = 0 -> [{x'=-2*y,y'=-2*x-3*x^2}] x^2+x^3-y^2 - c() = 0"
    // L10 Example 12
    val i3 =
      "x^4*y^2 + x^2*y^4-3*x^2*y^2+1= c()-> [{x'=2*x^4*y+4*x^2*y^3-6*x^2*y , y'=-4*x^3*y^2-2*x*y^4+6*x*y^2}]x^4*y^2 + x^2*y^4-3*x^2*y^2+1=c()"
    val i4 = "x^4+y^4 = 0 -> [{x'=4*y^3,y'=-4*x^3}]x^4+y^4 = 0"
    // L10 Exercises (6,7,8,9)
    val i5 = "x*y=c() -> [{x'=-x,y'=y,z'=-z}]x*y=c()"
    val i6 = "x^2+4*x*y-2*y^3 -y =1 -> [{x'=-1+4*x-6*y^2,y'=-2*x-4*y}]x^2+4*x*y-2*y^3 -y =1 "
    val i7 = "x^2+y^3/3 = c() -> [{x'=y^2,y'=-2*x}]x^2+y^3/3 = c()"
    val i8 =
      "(u^2 + v^2 + A()*x^2+B()*y^2)/2 + x^2*y - 1/3 * eps()*y^3 = 0 -> [{x'=u,y'=v,u'=-A()*x-2*x*y,v'=-B()*y+eps()*y^2-x^2}](u^2 + v^2 + A()*x^2+B()*y^2)/2 + x^2*y - 1/3 *eps()*y^3 = 0 "

    val problems = List(i1, i2, i3, i4, i5, i6, i7, i8).map(_.asFormula)

    val tactic = implyR(1) &
      dI(Symbol("diffInd"))(1) <
      (
        QE, // QE just for reflexivity, no problem
        chase(1) &
          // Much slower
          // PolynomialArith.normaliseAt(1, 0 :: Nil) &
          // PolynomialArith.normaliseAt(1, 1 :: Nil) &
          normalizeAt(1, 0 :: Nil) & normalizeAt(1, 1 :: Nil) & cohideR(1) & byUS(Ax.equalReflexive),
      )

    val res = problems.map(proveBy(_, tactic))
    res.forall(_.isProved) shouldBe true
  }

  it should "solve Lecture 11 odd order dynamics (Example 11.4)" in withMathematica { qeTool =>
    val i = "x^2 >= 2 -> [{x'=x^5+7*x^3+2*x}] x^2 >= 2".asFormula
    val tactic = implyR(1) &
      dI(Symbol("diffInd"))(1) <
      (
        QE, // QE just for reflexivity, no problem
        chase(1) & SOSSolve.sos(),
      )
    val res = proveBy(i, tactic)
    println(res)
    res shouldBe Symbol("proved")
  }

  it should "solve Lecture 11 even order dynamics (Example 11.5)" in withMathematica { qeTool =>
    val i = "x^3 >= 2 -> [{x'=x^4+6*x^2+5}] x^3 >= 2".asFormula
    val tactic = implyR(1) &
      dI(Symbol("diffInd"))(1) <
      (
        QE, // QE just for reflexivity, no problem
        chase(1) & OnAll(SOSSolve.sos()),
      )
    val res = proveBy(i, tactic)
    println(res)
    res shouldBe Symbol("proved")
  }

  it should "solve Lecture 11 DI arithmetic (conjuncts)" in withMathematica { qeTool =>
    val i =
      "v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2 -> [{v'=w,w'=-v}] (v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2)".asFormula

    // val insts = List((0,"1".asTerm),(1,"3*wit__0^2*x^2".asTerm))

    val tactic = implyR(1) & DebuggingTactics.print("Entering diff ind") &
      dI(Symbol("diffInd"))(1) <
      (
        QE, // QE just for reflexivity, no problem
        DebuggingTactics.print("Before chase") & chase(1) & SOSSolve.sos(),
      )

    val res = proveBy(i, tactic)
    println(res)
    res shouldBe Symbol("proved")
  }

  it should "solve Lecture 11 DI quartic dynamics (Example 11.7)" in withMathematica { qeTool =>
    val i = "x^3 >= -1 & a() >= 0 -> [{x'=(x-3)^4 +a()}] x^3 >= -1".asFormula

    val tactic = implyR(1) & DebuggingTactics.print("Entering diff ind") &
      dI(Symbol("diffInd"))(1) <
      (
        QE, // QE just for reflexivity, no problem
        DebuggingTactics.print("Before chase") & chase(1) & SOSSolve.sos(),
      )

    val res = proveBy(i, tactic)
    println(res)
    res shouldBe Symbol("proved")
  }

  it should "solve Lecture 11 DI damped oscillator" in withMathematica { qeTool =>
    val i = "w()^2*x^2 + y^2 <= c()^2 -> [{x'=y,y'=-w()^2*x-2*d()*w()*y & (w()>=0 & d()>=0)}]w()^2*x^2 + y^2 <= c()^2"
      .asFormula

    val tactic = implyR(1) &
      dI(Symbol("diffInd"))(1) <
      (
        QE, // QE just for reflexivity, no problem
        chase(1) & SOSSolve.sos(),
      )

    val res = proveBy(i, tactic)
    println(res)
    res shouldBe Symbol("proved")
  }

  // todo: hard
  it should "prove a nasty arithmetic problem from L4Q2" in withMathematica { qeTool =>
    val antes = IndexedSeq(
      "minr>0",
      "buffer>0",
      "trackr>=minr",
      "(tx-x)^2+(ty-y)^2=trackr^2",
      "(tx-rx)^2+(ty-ry)^2>=(buffer+trackr)^2",
    ).map(_.asFormula)
    val succ = IndexedSeq("(x-rx)^2+(y-ry)^2>=buffer^2".asFormula)

//    val linear = List((5,"trackr","wit_^2 + minr","1"),(2,"buffer","wit__1^2","1"),(2,"minr","wit__2^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
//    val witness = List(("4","wit_*wit__0*wit__1"),("4","wit__2*wit__0*wit__1"),("2","wit__0*wit__3"),("4","-ty*x + tx*y + ty*rx - y*rx - tx*ry + x*ry"),("4","wit_*wit__1*wit__3"),("4","wit__2*wit__1*wit__3"),("4","wit_^2*wit__0 + wit__2^2*wit__0"),("1","wit__3^2")).map( s => (s._1.asTerm,s._2.asTerm))
//    // The first inequation is used here
//    val ineq = List(0)
//    //The default basis isn't anywhere near to a groebner basis...
//    val insts = Some(List((0,"-2*tx*x - x^2 - 2*ty*y - y^2 + 2*tx*rx + 4*x*rx - 3*rx^2 + 2*ty*ry + 4*y*ry - 3*ry^2 - 2*wit_^2*wit__1^2 - 2*wit__2^2*wit__1^2 - wit__1^4 - wit__3^2"), (1," 4*wit_^4 + 8*wit_^2*wit__2^2 + 4*wit__2^4 + 4*wit_^2*wit__1^2 + 4*wit__2^2*wit__1^2 + 2*wit__3^2"), (2," 2*tx*x - 3*x^2 + 2*ty*y - 3*y^2 - 2*tx*rx + 4*x*rx - rx^2 - 2*ty*ry + 4*y*ry - ry^2 + 2*wit_^2*wit__1^2 + 2*wit__2^2*wit__1^2 + wit__1^4 + wit__3^2")).map (s => (s._1,s._2.asTerm)))

    val res = proveBy(Sequent(antes, succ), SOSSolve.sos())

    println(res)
    res shouldBe Symbol("proved")
  }

  "PolynomialArith" should "prove JH's example using special case witness (g=1)" in withMathematica { qeTool =>
    // One direction of the quadratic formula (non-zeroness of determinants)
    val antes = IndexedSeq("a*x^2 + b*x + c=0").map(_.asFormula)
    val succ = IndexedSeq("b^2-4*a*c >= 0").map(_.asFormula)

    val res = proveBy(Sequent(antes, succ), SOSSolve.sos())
    println(res)
    res shouldBe Symbol("proved")
  }

  it should "prove more JH examples (1)" in withMathematica { qeTool =>
    val antes = IndexedSeq("0<=a", "0<=b", "0<=c", "c*(2*a+b)^3/27 <= x").map(_.asFormula)
    val succ = IndexedSeq("c*a^2*b <=x").map(_.asFormula)

    val res = proveBy(Sequent(antes, succ), SOSSolve.sos())
    println(res)
    res shouldBe Symbol("proved")
  }

  it should "prove more JH examples (2)" in withMathematica { qeTool =>
    val antes = IndexedSeq("1<=t", "t<=1").map(_.asFormula)
    val succ = IndexedSeq("0<=1+r^2-2*r*t").map(_.asFormula)

    val res = proveBy(Sequent(antes, succ), SOSSolve.sos())
    println(res)
    res shouldBe Symbol("proved")
  }

  // todo: hard
  it should "prove more JH examples (3)" in withMathematica { qeTool =>
    val antes = IndexedSeq("a*a+a*b-b*b>=0", "2*a+b>=0", "c*c+c*d-d*d<=0", "d>=0").map(_.asFormula)
    val succ = IndexedSeq("a*d+c*b+b*d>=0").map(_.asFormula)
    //    val ineq = List(0)
    //    val linear = List((3,"a","1/2*wit__3^2 - 1/2*b","2"),(1,"d","wit__1^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    //    val witness = List(("1","wit__0*wit__1*wit__3"),("1/5","wit__3^2*wit__2"),("1/5","2*c*wit_ + wit__1^2*wit_")).map( s => (s._1.asTerm,s._2.asTerm))
    //    val insts = Some(List((0,"wit__1^2*wit__3^2"),(1,"-1/5*wit__3^4"),(2,"1/5*wit__1^4 + 4/5*c*wit__1^2 + 4/5*c^2")).map (s => (s._1,s._2.asTerm)))

    val res = proveBy(Sequent(antes, succ), SOSSolve.sos())
    println(res)
    res shouldBe Symbol("proved")
  }

  // todo: hard
  it should "prove more JH examples (4)" in withMathematica { qeTool =>
    // Same as (3), but >= changed to >, Harrison reports that this is harder for his implementation
    val antes = IndexedSeq("a*a+a*b-b*b>0", "2*a+b>0", "c*c+c*d-d*d<=0", "d>0").map(_.asFormula)
    val succ = IndexedSeq("a*d+c*b+b*d>=0").map(_.asFormula)
    //    val ineq = List(0)
    //    val linear = List((2,"a","1/2*wit__2^2 - 1/2*b","2"),(1,"d","wit__1^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    //    val witness = List(("1","wit__0*wit__1*wit__2"),("1/5","wit__2^2*wit_"),("1/5","2*c*wit__3 + wit__1^2*wit__3")).map( s => (s._1.asTerm,s._2.asTerm))
    //    val insts = Some(List((0,"wit__1^2*wit__2^2"),(1,"1/5*wit__1^4 + 4/5*c*wit__1^2 + 4/5*c^2"),(2,"-1/5*wit__2^4")).map (s => (s._1,s._2.asTerm)))

    val res = proveBy(Sequent(antes, succ), SOSSolve.sos())
    println(res)
    res shouldBe Symbol("proved")
  }

  it should "prove RWV example with SOS" in withMathematica { qeTool =>
    val antes = IndexedSeq("x - y -1*a^2", "z-b^2", "z*(y-x)*c^2-1").map(t => Equal(t.asTerm, Number(0)))
    val seq = Sequent(antes, IndexedSeq())

    val pr = proveBy(seq, SOSSolve.sos())
    pr shouldBe Symbol("proved")
  }

  // todo: hard
  it should "prove non-negativity of the Motzkin polynomial" in withMathematica { qeTool =>
    // Standard example used in many SOS papers
    val antes = IndexedSeq()
    val succ = IndexedSeq("x1^6+x2^4*x3^2+x2^2*x3^4-3*x1^2*x2^2*x3^2>=0").map(_.asFormula)
    //    val ineq = List(0)
    //    val witness = List(("1","wit_*x1^3"),("1","-9/14*wit_*x1^2*x3 + wit_*x2^2*x3"),("1","-9/14*wit_*x1^2*x2 + wit_*x2*x3^2"),("3/7","x1^4*x2*x3 - 1/2*x1^2*x2^3*x3 - 1/2*x1^2*x2*x3^3"),("3/7","-x1^5*x2 + x1*x2^3*x3^2"),("3/7","-x1^5*x3 + x1*x2^2*x3^3"),("9/28","-x1^2*x2^3*x3 + x1^2*x2*x3^3"),("3/196","wit_*x1^2*x3"),("3/196","wit_*x1^2*x2")).map( s => (s._1.asTerm,s._2.asTerm))

    val res = proveBy(Sequent(antes, succ), SOSSolve.sos())
    res shouldBe Symbol("proved")
  }

  it should "prove JH examples from Monniaux & Corbineau, ITP'11" in withMathematica { qeTool =>
    val problems = List(
      Sequent(
        IndexedSeq("0<=x", "0<=y", "0<=z", "x*y*z=1").map(_.asFormula),
        IndexedSeq("x+y+z <= (x^2 * z + y^2 * x + z^2 * y)").map(_.asFormula),
      ),
      // The positive squares heuristic doesn't work for this one
      // Sequent(IndexedSeq("0<=x","0<=y","0<=z").map(_.asFormula),IndexedSeq("(x^2 * z + y^2 * x + z^2 * y)^3 <= ((x * y * z)^2 * (x + y + z)^3)").map(_.asFormula)),
      Sequent(
        IndexedSeq("(a^2 = (k^2 + 1) * b^2)", "1<=k", "1<=a", "1<=b").map(_.asFormula),
        IndexedSeq("(a - k * b) < b").map(_.asFormula),
      ),
    )
    val ineq = List(0)
    val witness = List(
      ("1", "wit_*x1^3"),
      ("1", "-9/14*wit_*x1^2*x3 + wit_*x2^2*x3"),
      ("1", "-9/14*wit_*x1^2*x2 + wit_*x2*x3^2"),
      ("3/7", "x1^4*x2*x3 - 1/2*x1^2*x2^3*x3 - 1/2*x1^2*x2*x3^3"),
      ("3/7", "-x1^5*x2 + x1*x2^3*x3^2"),
      ("3/7", "-x1^5*x3 + x1*x2^2*x3^3"),
      ("9/28", "-x1^2*x2^3*x3 + x1^2*x2*x3^3"),
      ("3/196", "wit_*x1^2*x3"),
      ("3/196", "wit_*x1^2*x2"),
    ).map(s => (s._1.asTerm, s._2.asTerm))

    val res = problems.map(s => proveBy(s, SOSSolve.sos())) // & genWitnessTac(ineq,witness))

    println(res)
    res.map(pr => pr shouldBe Symbol("proved"))
  }

  it should "Solve a bunch of arithmetic questions" in withMathematica { qeTool =>
    val problems = List(
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&d_0>=v_0*(ep_0-t_0)&ep_0>=0&t_0>=0&V_0>=0&ep_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0&t_0<=ep_0->t_0>=0&v_0>=0&d_0>=v_0*(ep_0-t_0))",
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&d_0>=v_0*(ep_0-t_0)&ep_0>=0&t_0>=0&V_0>=0&ep_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0&t_0<=ep_0->\\forall t (t<=ep_0->1>=0&0>=0&-v_0>=v_0*(0-1)))",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->0<=ep_0)",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->0<=V_0)",
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&ep_0>=0&V_0>=0&ep_0>=0&d_0>=v_0*(ep_0-t_0)&t_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0->(d_0>=V_0*ep_0->\\forall v (0<=v&v<=V_0->d_0>=v*(ep_0-0)&0>=0&0<=ep_0&0<=v&v<=V_0))&d_0>=0*(ep_0-0)&0>=0&0<=ep_0&0<=0&0<=V_0)",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->d_0>=0*(ep_0-0))",
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&ep_0>=0&V_0>=0&ep_0>=0&d_0>=v_0*(ep_0-t_0)&t_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0->d_0>=0)",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->0<=0)",
      "\\forall ep_0 \\forall d_0 \\forall V_0 (d_0>=0&V_0>=0&ep_0>=0&V_0>=0&ep_0>=0->0>=0)",
      "\\forall v_0 \\forall t_0 \\forall ep_0 \\forall d_0 \\forall V_0 (V_0>=0&ep_0>=0&V_0>=0&ep_0>=0&0<=v_0&v_0<=V_0&t_0<=ep_0&t_0>=0&v_0>=0&d_0>=v_0*(ep_0-t_0)->d_0>=v_0*(ep_0-t_0)&t_0>=0&t_0<=ep_0&0<=v_0&v_0<=V_0)",
    ).map(_.asFormula)

    val res = problems.map(s => proveBy(s, SOSSolve.sos()))

    println(res)
    res.map(pr => pr shouldBe Symbol("proved"))
  }

  it should "prove a inequality" in withMathematica { _ =>
    val pr = proveBy("a > 0 & b > 0 -> a*x^2+b*y^2 >= 0".asFormula, SOSSolve.sos())
    println(pr)
    pr shouldBe Symbol("proved")
  }
}
