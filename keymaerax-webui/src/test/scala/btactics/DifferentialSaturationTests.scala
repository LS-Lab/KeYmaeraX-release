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

  "DiffSat" should "find invariants for linear movement" in withMathematica { qeTool =>
    //This system needs a time variable in order to find interesting invariants
    //todo: PQE doesn't work well when A() is replaced with a variable
    val p = "{x'=v,v'=A(),t'=1 &v>=0}".asProgram.asInstanceOf[ODESystem]
    val ode = p.ode
    val dom = p.constraint

    val adjs = analyseODEVars(p,false)
    val ls = bfsSCC(adjs)

    val invs = ls.map( p => parametricInvariants(ode, List(dom), p.map(s=>s.toList), 4, false,Some(qeTool)))

    invs.length shouldBe 1
    invs.head._1.map(s => s._1) should contain only "a__0+a__2*(-1*A()*t+v)".asTerm
    //todo: this invariant is v = v_0 + a *t
    //can't seem to find x = x_0 + v_0 t + a/2 * t^2 with current approach
  }

  "DiffSat" should "saturate taylor series" in withMathematica { qeTool =>

    val p = "{x' = x, t' = 1}".asProgram.asInstanceOf[ODESystem]
    val ode = p.ode
    val dom = p.constraint

    val adjs = analyseODEVars(p,false)
    //There is more than one scc, so we also try all the variables together at the end
    val ls = bfsSCC(adjs).flatten.map(l => l.toList) ++ List(odevars(p).toList)

    val invs = parametricInvariants(ode, List(dom), ls, 4, true,Some(qeTool))
    println(invs)
  }


  "DiffSat" should "solve for parameters" in withMathematica { qeTool =>
    val p = ("{x1'=d1,x2'=d2,d1'=-w*d2,d2'=w*d1,t'=1," +
              "y1'=e1,y2'=e2,e1'=-p*e2,e2'=p*e1,s'=1 & true}").asProgram.asInstanceOf[ODESystem]
    val ode = p.ode
    val dom = p.constraint

    val adjs = analyseODEVars(p,false)
    //There is more than one scc, so we also try all the variables together at the end
    val ls = bfsSCC(adjs).flatten.map(l => l.toList) ++ List(odevars(p).toList)

    val invs = parametricInvariants(ode, List(dom), ls, 4, true,Some(qeTool))
    println(invs)
  }

  // Mathematica PQE returns false for this
  "foo" should "fix weird pqe" in withMathematica { qeTool =>
    val fml = "\\forall x \\forall v \\forall t (v>=0&a__0+a__3*(-1*a*t+v)=0->a__5+2*a__6*t+v*(a__11+a__7+a__8*t+a__12*v)=0)".asFormula
    val pr1 = proveBy(fml,partialQE)
    println(pr1)
  }



}
