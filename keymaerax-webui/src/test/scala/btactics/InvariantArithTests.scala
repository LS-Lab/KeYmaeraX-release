package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.SlowTest

import scala.collection.immutable._

/**
  * Invariant arithmetic examples
  * From Lectures 10/11
  * Created by yongkiat on 2/3/16.
  */
@edu.cmu.cs.ls.keymaerax.tags.SlowTest
class InvariantArithTests extends TacticTestBase {


  "InvariantArith" should "solve Lecture 10 DI arithmetic" in withMathematica { qeTool =>
    //All of these prove by normalizing both sides to 0 = 0
    //L10 Example 1
    val i1 = "v^2 + w^2 = r()^2 -> [{v'=w,w'=-v}] v^2+w^2 = r()^2"
    //L10 Example 11
    val i2 = "x^2+x^3-y^2 - c() = 0 -> [{x'=-2*y,y'=-2*x-3*x^2}] x^2+x^3-y^2 - c() = 0"
    //L10 Example 12
    val i3 = "x^4*y^2 + x^2*y^4-3*x^2*y^2+1= c()-> [{x'=2*x^4*y+4*x^2*y^3-6*x^2*y , y'=-4*x^3*y^2-2*x*y^4+6*x*y^2}]x^4*y^2 + x^2*y^4-3*x^2*y^2+1=c()"
    val i4 = "x^4+y^4 = 0 -> [{x'=4*y^3,y'=-4*x^3}]x^4+y^4 = 0"
    //L10 Exercises (6,7,8,9)
    val i5 = "x*y=c() -> [{x'=-x,y'=y,z'=-z}]x*y=c()"
    val i6 = "x^2+4*x*y-2*y^3 -y =1 -> [{x'=-1+4*x-6*y^2,y'=-2*x-4*y}]x^2+4*x*y-2*y^3 -y =1 "
    val i7 = "x^2+y^3/3 = c() -> [{x'=y^2,y'=-2*x}]x^2+y^3/3 = c()"
    val i8 = "(u^2 + v^2 + A()*x^2+B()*y^2)/2 + x^2*y - 1/3 * eps()*y^3 = 0 -> [{x'=u,y'=v,u'=-A()*x-2*x*y,v'=-B()*y+eps()*y^2-x^2}](u^2 + v^2 + A()*x^2+B()*y^2)/2 + x^2*y - 1/3 *eps()*y^3 = 0 "

    val problems = List(i1,i2,i3,i4,i5,i6,i7,i8).map(_.asFormula)

    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        normaliseAt(1, 0 :: Nil) &
        normaliseAt(1, 1 :: Nil) & cohideR(1) & byUS(Ax.equalReflexive)
      )

    val res = problems.map(proveBy(_, tactic))
    res.forall(_.isProved) shouldBe true
  }

  "InvariantArith" should "solve Lecture 11 DI arithmetic (fig 11.5)" in withMathematica { qeTool =>
    val i = "1/3 <= 5 * x^2 -> [{x'=x^3}] 1/3 <= 5 * x^2".asFormula
    //No linear elimination
    val witness = List(("10","wit__0*x^2")).map( s => (s._1.asTerm,s._2.asTerm))
    // The first inequation is used here
    val ineq = List(0)
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal &
        genWitnessTac(ineq,witness)
      )
    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 odd order dynamics (Example 11.4)" in withMathematica { qeTool =>
    val i = "x^2 >= 2 -> [{x'=x^5+7*x^3+2*x}] x^2 >= 2".asFormula
    val witness = List(("2","wit__0*x^3 + 7/5*wit__0*x"),("42/5","wit__0*x^2"),("2/25","wit__0*x")).map( s => (s._1.asTerm,s._2.asTerm))
    val ineq = List(0)
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal &
        genWitnessTac(ineq,witness)
      )
    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 even order dynamics (Example 11.5)" in withMathematica { qeTool =>
    val i = "x^3 >= 2 -> [{x'=x^4+6*x^2+5}] x^3 >= 2".asFormula
    val witness = List(("3","wit__0*x^3 + 20/9*wit__0*x"),("14/3","wit__0*x^2"),("5/27","wit__0*x")).map( s => (s._1.asTerm,s._2.asTerm))
    val ineq = List(0)
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal &
        genWitnessTac(ineq,witness)
      )
    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI arithmetic (conjuncts)" in withMathematica { qeTool =>
    val i = "v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2 -> [{v'=w,w'=-v}] (v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2)".asFormula

    //val insts = List((0,"1".asTerm),(1,"3*wit__0^2*x^2".asTerm))

    val tactic = implyR(1) & DebuggingTactics.print("Entering diff ind") & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      DebuggingTactics.print("Before chase") &
        chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal &
        OnAll(genWitnessTac(List(0),List())) // Trivial because the inequation says 0 = 0
      )

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI quartic dynamics (Example 11.7)" in withMathematica { qeTool =>
    val i = "x^3 >= -1 & a() >= 0 -> [{x'=(x-3)^4 +a()}] x^3 >= -1".asFormula

    val ineq = List(0)
    val linear = List((1,"a()","wit__1^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("3"," wit__0*x^3 - 6*wit__0*x^2 + 9*wit__0*x"),("3","wit__0*wit__1*x")).map( s => (s._1.asTerm,s._2.asTerm))
    //val insts = List((0,"1".asTerm),(1,"3*wit__0^2*x^2".asTerm))

    val tactic = implyR(1) & DebuggingTactics.print("Entering diff ind") & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      DebuggingTactics.print("Before chase") &
        chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal & linearElim(linear) & genWitnessTac(ineq,witness)
      )

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI damped oscillator" in withMathematica { qeTool =>
    val i = "w()^2*x^2 + y^2 <= c()^2 -> [{x'=y,y'=-w()^2*x-2*d()*w()*y & (w()>=0 & d()>=0)}]w()^2*x^2 + y^2 <= c()^2".asFormula

    val ineq = List(0)
    val linear = List((1,"d()","wit__1^2","1"),(1,"w()","wit__2^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("4","wit__0*y*wit__3*wit__4")).map( s => (s._1.asTerm,s._2.asTerm))

    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith2) &
        printGoal & linearElim(linear) & genWitnessTac(ineq,witness))

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "prove a nasty arithmetic problem from L4Q2" taggedAs SlowTest in withMathematica { qeTool =>
    val antes = IndexedSeq("minr>0","buffer>0","trackr>=minr","(tx-x)^2+(ty-y)^2=trackr^2","(tx-rx)^2+(ty-ry)^2>=(buffer+trackr)^2").map(_.asFormula)
    val succ = IndexedSeq("(x-rx)^2+(y-ry)^2>=buffer^2".asFormula)

    val linear = List((5,"trackr","wit_^2 + minr","1"),(2,"buffer","wit__1^2","1"),(2,"minr","wit__2^2","1")).map( s => (s._1,s._2.asTerm,s._3.asTerm,s._4.asTerm))
    val witness = List(("4","wit_*wit__0*wit__1"),("4","wit__2*wit__0*wit__1"),("2","wit__0*wit__3"),("4","-ty*x + tx*y + ty*rx - y*rx - tx*ry + x*ry"),("4","wit_*wit__1*wit__3"),("4","wit__2*wit__1*wit__3"),("4","wit_^2*wit__0 + wit__2^2*wit__0"),("1","wit__3^2")).map( s => (s._1.asTerm,s._2.asTerm))
    // The first inequation is used here
    val ineq = List(0)
    //The default basis isn't anywhere near to a groebner basis...
    val insts = Some(List((0,"-2*tx*x - x^2 - 2*ty*y - y^2 + 2*tx*rx + 4*x*rx - 3*rx^2 + 2*ty*ry + 4*y*ry - 3*ry^2 - 2*wit_^2*wit__1^2 - 2*wit__2^2*wit__1^2 - wit__1^4 - wit__3^2"), (1," 4*wit_^4 + 8*wit_^2*wit__2^2 + 4*wit__2^4 + 4*wit_^2*wit__1^2 + 4*wit__2^2*wit__1^2 + 2*wit__3^2"), (2," 2*tx*x - 3*x^2 + 2*ty*y - 3*y^2 - 2*tx*rx + 4*x*rx - rx^2 - 2*ty*ry + 4*y*ry - ry^2 + 2*wit_^2*wit__1^2 + 2*wit__2^2*wit__1^2 + wit__1^4 + wit__3^2")).map (s => (s._1,s._2.asTerm)))

    val tactic = prepareArith2 & DebuggingTactics.print("after") &
      printGoal & linearElim(linear) & genWitnessTac(ineq,witness,insts)

    val res = proveBy(Sequent(antes,succ), tactic)

    res shouldBe 'proved
  }

}
