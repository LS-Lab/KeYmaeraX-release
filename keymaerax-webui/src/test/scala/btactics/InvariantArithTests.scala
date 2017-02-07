package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

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
    //TODO: handle divisors properly, these examples have the fractions multiplied out by hand
    //Idea: separate tactic that walks arithmetic goal, multiplies by all the divisors and emits subgoals to prove that the divisors are all non-zero
    //Also, Exercise 8 has a typo [x->y] in the x^3 (I think?)
    val i7 = "3*x^2+y^3 = 3*c() -> [{x'=y^2,y'=-2*x}]3*x^2+y^3 = 3*c()"
    val i8 = "3*(u^2 + v^2 + A()*x^2+B()*y^2) + 6*x^2*y - 2*eps()*y^3 = 0 -> [{x'=u,y'=v,u'=-A()*x-2*x*y,v'=-B()*y+eps()*y^2-x^2}]3*(u^2 + v^2 + A()*x^2+B()*y^2) + 6*x^2*y - 2*eps()*y^3 = 0 "

    val problems = List(i1,i2,i3,i4,i5,i6,i7,i8).map(_.asFormula)

    val tactic = implyR(1) & diffInd('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        normaliseAt(1, 0 :: Nil) &
        normaliseAt(1, 1 :: Nil) & cohideR(1) & byUS("= reflexive")
      )

    val res = problems.map(proveBy(_, tactic))
    res.forall(_.isProved) shouldBe true
  }

  "InvariantArith" should "solve Lecture 11 DI arithmetic" in withMathematica { qeTool =>
    //L11 Example 9
    val i1 = "1 <= 15 * x^2 -> [{x'=x^3}] 1 <= 15 * x^2" //Note: requires even power reasoning 0 <= 30 * x^4
    //L11 Example 10
    val i2 = "v^2 + w^2 <= r()^2 -> [{v'=w,w'=-v}] v^2+w^2 <= r()^2" // 0 <= 0
    //L11 Example 11/15
    val i3 = "w()^2*x^2 + y^2 <= c()^2 -> [{x'=y,y'=-w()^2*x-2*d()*w()*y & (w()>=0 & d()>=0)}]w()^2*x^2 + y^2 <= c()^2"
    //Note: Requires a few reasoning steps: d() >= 0, w >= 0 by assumptions, y^2 >= 0 by R, -4 * K <= 0 <-> K >= 0
    //L11 Example (conjuncts)
    val i4 = "v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2 -> [{v'=w,w'=-v}] (v^2 + w^2 <= r()^2 & v^2 + w^2 >= r()^2)" // 0 <= 0 & 0 >= 0
    //L11 Example 14
    val i5 = "x^3 >= -1 -> [{x'=(x-3)^4 +a & a >= 0}] x^3 >= -1"
    // Note: expanding out and normalizing the polynomial is a bad idea here (perhaps there should be multiple heuristic tactics)
    // it was 3*x^(3-1) * ((x-3)^4 + a) >= 0 (where a >= 0)

    val problems = List(i1,i2,i3,i4,i5).map(_.asFormula)

    val tactic = implyR(1) & diffInd('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) & prop &
        DebuggingTactics.print("Before normalizing") &
        OnAll(normaliseAt(1, 0 :: Nil) &
        normaliseAt(1, 1 :: Nil)) //& cohideR(1) //& byUS("= reflexive")
      )

    val res = problems.map(proveBy(_, tactic))
    println(res)
//    res.forall(_.isProved) shouldBe true
  }

  "InvariantArith" should "workspace" in withMathematica { qeTool =>
    //val i3 = "w()^2*x^2 + y^2 <= c()^2 -> [{x'=y,y'=-w()^2*x-2*d()*w()*y & (w()>=0 & d()>=0)}]w()^2*x^2 + y^2 <= c()^2"
    //Essential arithmetic (ineq flipped by hand for now):
    val antes = IndexedSeq("c()^2>=w()^2*x_0^2+y_0^2","w()>=0","d()>=0","w()>=0","d()>=0").map(_.asFormula)
    val succ = IndexedSeq("0>=0+-4*(1*y^2*d()^1*w()^1)").map(_.asFormula)

    val tactic =
      normAnte //Only normalize the antecedents

    val res = proveBy(Sequent(antes,succ),tactic)

    val rhs = res.subgoals(0).sub(SuccPosition(1,1::Nil)).get.asInstanceOf[Term]
    val lhs = res.subgoals(0).ante.map(f => f.sub(PosInExpr(0::Nil)).get.asInstanceOf[Term]).toList

    println(lhs,rhs)

    val wit_norm = normalise(rhs,true)._1
    val ctx_norm = lhs.map( t=> normalise(t,true)._1)
    println(wit_norm,ctx_norm)
    println(reduction(ctx_norm,wit_norm))
    //Problem: the fresh z^2 are dominating over the other terms in the standard reduction sequence
    //Idea: probably play with the elimination order somehow? But the fresh variables are hard to eliminate (non-groebner)...

    println(res)
    //    res.forall(_.isProved) shouldBe true
  }

}
