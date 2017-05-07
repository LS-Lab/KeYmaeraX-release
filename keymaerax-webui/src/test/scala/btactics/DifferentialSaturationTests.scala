package btactics

import edu.cmu.cs.ls.keymaerax.btactics.DifferentialSaturation._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXProblemParser}
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable._
import scala.collection.mutable.ListBuffer

/**
  * Differential Saturation examples
  */
class DifferentialSaturationTests extends TacticTestBase {

  "DiffSat" should "generate parametric candidates" in withMathematica { qeTool =>
    val vars = List("x","y","z").map(_.asVariable)
    parametricCand(vars,3,0)._1 shouldBe "a__9*(x^2*1)+(a__8*(x^1*(y^1*1))+(a__7*(x^1*(z^1*1))+(a__6*(x^1*1)+(a__5*(y^2*1)+(a__4*(y^1*(z^1*1))+(a__3*(y^1*1)+(a__2*(z^2*1)+(a__1*(z^1*1)+(a__0*1+0)))))))))".asTerm
  }

  "DiffSat" should "solve for parameters" in withMathematica { qeTool =>
    val p = "{x1'=d1,x2'=d2,d1'=-w*d2,d2'=w*d1,t'=1 & true}".asProgram.asInstanceOf[ODESystem]
    val (w::d1::d2::x1::x2::Nil) = List("w","d1","d2","x1","x2").map(_.asVariable)
    val ode = p.ode
    val dom = p.constraint
    //No non-trivial invariants
    parametricInvariants(ode,dom,List(List(w)),3)

    parametricInvariants(ode,dom,List(List(w,d1,d2)),3)
//    val param = parametricCand(vars,2,0)
//    val trm = simplifiedLieDerivative(ode,param._1)
//    val fml = diffClosure(ode,Imply(dom,GreaterEqual(trm,Number(0))))
//    println(guessInstantiation(fml,param._2))
  }

}
