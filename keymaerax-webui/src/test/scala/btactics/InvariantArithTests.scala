package btactics

import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Invariant arithmetic examples
  * From Lectures 10/11
  * Created by yongkiat on 2/3/16.
  */
class InvariantArithTests extends TacticTestBase {


  "InvariantArith" should "solve DI arithmetic" in withMathematica { qeTool =>
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
    //TODO: Broken because of constant A(),B() coefficients
    //Polynomial arithmetic probably has to treat these as variables
    val i8 = "3*(u^2 + v^2 + A()*x^2+B()*y^2) + 6*x^2*y - 2*eps()*y^3 = 0 -> [{x'=u,y'=v,u'=-A()*x-2*x*y,v'=-B()*y+eps()*y^2-x^2}]3*(u^2 + v^2 + A()*x^2+B()*y^2) + 6*x^2*y - 2*eps()*y^3 = 0 "

    val problems = List(i1,i2,i3,i4,i5,i6,i7).map(_.asFormula)

    val tactic = implyR(1) & diffInd('diffInd)(1) < (QE, //QE just for reflexivity, no problem
      chase(1) &
        DebuggingTactics.print("foo") &
        normaliseAt(1, 0 :: Nil) &
        normaliseAt(1, 1 :: Nil) & cohideR(1) & byUS("= reflexive")
      )

    val res = problems.map(proveBy(_, tactic))
    res.forall(_.isProved) shouldBe true
  }

}
