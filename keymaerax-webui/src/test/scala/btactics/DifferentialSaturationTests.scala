package btactics

import edu.cmu.cs.ls.keymaerax.btactics.DifferentialSaturation._
import edu.cmu.cs.ls.keymaerax.btactics.DependencyAnalysis._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable._

/**
  * Differential Saturation examples
  */
class DifferentialSaturationTests extends TacticTestBase {

  "DiffSat" should "generate parametric candidates" in withMathematica { qeTool =>
    val vars = List("x","y","z").map(_.asVariable)
    parametricCand(vars,3,0)._1 shouldBe "a__9*(x^2*1)+(a__8*(x^1*(y^1*1))+(a__7*(x^1*(z^1*1))+(a__6*(x^1*1)+(a__5*(y^2*1)+(a__4*(y^1*(z^1*1))+(a__3*(y^1*1)+(a__2*(z^2*1)+(a__1*(z^1*1)+(a__0*1+0)))))))))".asTerm
  }

  "DiffSat" should "find a rotation DI" in withMathematica { qeTool =>
    val p = "{v'=a*w,w'=-v}".asProgram.asInstanceOf[ODESystem]
    val ode = p.ode
    val dom = p.constraint

    val adjs = analyseODEVars(p,false)
    val ls = bfsSCC(adjs)

    val invs = ls.map( p => parametricInvariants(ode, List(dom), p.map(s=>s.toList), 4, false,Some(qeTool)))
    invs.length shouldBe 1
    invs.head._1.map(s => s._1) should contain only "a__0+a__5*(v^2+a*w^2)".asTerm
  }

  //Note: mathematica's simplification tool is non deterministic???
  "DiffSat" should "find invariants for linear movement" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    //This system needs a time variable in order to find interesting invariants
    val p = "{x'=v,v'=a,t'=1 &v>=0}".asProgram.asInstanceOf[ODESystem]
    val ode = p.ode
    val dom = p.constraint

    val adjs = analyseODEVars(p,false)
    val ls = bfsSCC(adjs)

    val invs = ls.map( p => parametricInvariants(ode, List(dom), p.map(s=>s.toList), 4, false,Some(qeTool)))

    invs.length shouldBe 1
    invs.head._1.map(s => s._1) should contain only ("a__0+a__2*(-1*a*t+v)".asTerm,"a__4+a^2*a__9*t^2+1/2*a*t*(-2*a__7+a__5*t+-4*a__9*v)+v*(a__7+-1*a__5*t+a__9*v)+a__5*x".asTerm)
    //todo: this fails to find the second invariant when saturating
  }

  "DiffSat" should "saturate taylor series" in withMathematica { qeTool =>

    val p = "{x' = x, t' = 1}".asProgram.asInstanceOf[ODESystem]
    val ode = p.ode
    val dom = p.constraint

    val adjs = analyseODEVars(p,false)
    //There is more than one scc, so we also try all the variables together at the end
    val ls = bfsSCC(adjs).flatten.map(l => l.toList) ++ List(odevars(p).toList)

    val invs = parametricInvariants(ode, List(dom), ls, 4, true,Some(qeTool))
    invs._2.map(s => s._1) should contain only ("a__0+t".asTerm,"a__2+x^2".asTerm)
  }

  //Note: mathematica's simplification tool is non deterministic???
  "DiffSat" should "solve for parameters" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val p = ("{x1'=d1,x2'=d2,d1'=-w*d2,d2'=w*d1,t'=1 & true}").asProgram.asInstanceOf[ODESystem]
    val ode = p.ode
    val dom = p.constraint

    val adjs = analyseODEVars(p,false)
    //There is more than one scc, so we also try all the variables together at the end
    val ls = bfsSCC(adjs).flatten.map(l => l.toList) ++ List(odevars(p).toList)

    val invs = parametricInvariants(ode, List(dom), ls, 4, true,Some(qeTool))
    invs._1.map(s => s._1) should contain only ("a__0+a__2*(d1^2+d2^2)".asTerm,"a__6+a__9*(d2+-1*w*x1)+a__7*(d1+w*x2)".asTerm,"a__11+a__12*(d1+w*x2)+1/2*(2*a__17*d2+2*a__20*d2^2+2*a__24*d2*x1+-2*a__17*w*x1+-1*a__24*w*x1^2+-2*d1*(a__24+2*a__20*w)*x2+-1*w*(a__24+2*a__20*w)*x2^2+2*a__18*(d2+-1*w*x1)*(d1+w*x2)+2*a__13*(d1+w*x2)^2)".asTerm)

    //Note that the second one is already implied by one of the equational ones
    invs._2.map(s=>s._1) should contain only ("a__26+t".asTerm,"a__28+a__31*d2+t+-1*a__31*w*x1+a__29*(d1+w*x2)".asTerm)
  }

  // Mathematica PQE returns false for this
  "foo" should "fix weird pqe" in withMathematica { qeTool =>
    val fml = "\\forall x \\forall v \\forall t (v>=0->a__5+2*a__6*t+v*(a__11+a__7+a__8*t+a__12*v)=0)".asFormula
    val pr1 = proveBy(fml,partialQE)
    println(pr1)
  }



}
