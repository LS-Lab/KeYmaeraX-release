package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Invariant arithmetic examples
  * From Lectures 10/11
  * Created by yongkiat on 2/3/16.
  */
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
        normaliseAt(1, 1 :: Nil) & cohideR(1) & byUS("= reflexive")
      )

    val res = problems.map(proveBy(_, tactic))
    res.forall(_.isProved) shouldBe true
  }

  "InvariantArith" should "solve Lecture 11 DI arithmetic (fig 11.5)" in withMathematica { qeTool =>
    val i = "1/3 <= 5 * x^2 -> [{x'=x^3}] 1/3 <= 5 * x^2".asFormula
    val witness = List(("10","wit__0*x^2")).map( s => (s._1.asTerm,s._2.asTerm))
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Problem") &
        witnessTac(witness)
        //Note: this gives the conditions 0-15*(2*x^(2-1)*x^3))*z__0^2-1=0, 1-15*x_0^2+z_^2=0
        //However, these two polynomials are actually disjoint, so we could try to prove a contradiction from either
        //No need to consider both at once
        //TODO: optimization - can split input polynomial systems into disjoint systems
      )
    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 odd order dynamics (Example 11.4)" in withMathematica { qeTool =>
    val i = "x^2 >= 2 -> [{x'=x^5+7*x^3+2*x}] x^2 >= 2".asFormula
    //val witness = List(("10","wit__0*x^2")).map( s => (s._1.asTerm,s._2.asTerm))
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Problem") &
        nil //witnessTac(witness)
      )
    //This has an SDP solution with the default heuristic, but the coeffcient appears to be an irrational sq root??
    val res = proveBy(i, tactic)
    println(res)
    //res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 even order dynamics (Example 11.5)" in withMathematica { qeTool =>
    val i = "x^3 >= 2 -> [{x'=x^4+6*x^2+5}] x^3 >= 2".asFormula
    //val witness = List(("10","wit__0*x^2")).map( s => (s._1.asTerm,s._2.asTerm))
    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Problem") &
        nil //witnessTac(witness)
      )
    //This has an SDP solution with the default heuristic, but the coeffcients appear to be irrational sq roots??
    val res = proveBy(i, tactic)
    println(res)
    //res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI arithmetic (conjuncts)" in withMathematica { qeTool =>
    val i = "v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2 -> [{v'=w,w'=-v}] (v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2)".asFormula

    //val insts = List((0,"1".asTerm),(1,"3*wit__0^2*x^2".asTerm))

    val tactic = implyR(1) & DebuggingTactics.print("Entering diff ind") & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      DebuggingTactics.print("Before chase") &
        chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Before witness") &
        OnAll(witnessTac(List())) //The witnesses are just 1 because the groebner basis contains -1
      )

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI quartic dynamics (Example 11.7)" in withMathematica { qeTool =>
    val i = "x^3 >= -1 & a() >= 0 -> [{x'=(x-3)^4 +a()}] x^3 >= -1".asFormula

    val witness = List(("3"," wit__0*x^3 - 6*wit__0*x^2 + 9*wit__0*x"),("3","wit__0*wit__1*x")).map( s => (s._1.asTerm,s._2.asTerm))
    //val insts = List((0,"1".asTerm),(1,"3*wit__0^2*x^2".asTerm))

    val tactic = implyR(1) & DebuggingTactics.print("Entering diff ind") & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      DebuggingTactics.print("Before chase") &
        chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Before witness") &
        witnessTac(witness)
      )

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

  "InvariantArith" should "solve Lecture 11 DI damped oscillator" in withMathematica { qeTool =>
    val i = "w()^2*x^2 + y^2 <= c()^2 -> [{x'=y,y'=-w()^2*x-2*d()*w()*y & (w()>=0 & d()>=0)}]w()^2*x^2 + y^2 <= c()^2".asFormula

    val witness = List(("4","wit__0*wit__1*y*wit__4")).map( s => (s._1.asTerm,s._2.asTerm))

    val tactic = implyR(1) & dI('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("Before normalizing") &  prop &
        OnAll(prepareArith) &
        DebuggingTactics.print("Problem") &
        witnessTac(witness))

    val res = proveBy(i, tactic)
    res shouldBe 'proved
  }

}
