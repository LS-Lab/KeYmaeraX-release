/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{PosInExpr, ProveAs, SuccPosition, TheType}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.AxiomaticODESolver._
import edu.cmu.cs.ls.keymaerax.core.{ODESystem, Provable, SeqPos, SuccPos}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory

/**
  * @author Nathan Fulton
  */
class AxiomaticODESolverTests extends TacticTestBase {
  import DifferentialHelper._
  import Augmentors._
  import TacticFactory._

  //region stand-along integrator

  "Integrator.apply" should "world on x'=v, v'=a" in {
    val initialConds = conditionsToValues(extractInitialConditions(None)("x=1&v=2&a=3&t=0".asFormula))
    val system = "{x'=v,v'=a, t'=1}".asProgram.asInstanceOf[ODESystem]
    val result = Integrator.apply(initialConds, system)
    println(result.mkString(","))
  }
  //endregion


  //region integration tests

  "axiomatic ode solver" should "work!" in withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=0 -> [{x'=v,v'=a}]x^3>=1".asFormula
    val t = TactixLibrary.implyR(1) & apply(qeTool)(1)
    val result = proveBy(f, t)
    println(result.prettyString)
  })

  //endregion


  //region unit tests

  //@todo exists monotone
  "setupTimeVar" should "work when time exists" in {
    val system = "[{x'=v}]1=1".asFormula
    val tactic = addTimeVarIfNecessary
    val result = proveBy(system, tactic(SuccPosition(1, 0::Nil)))
    loneSucc(result) shouldBe "[{x'=v,kyxtime'=0*kyxtime+1&true}]1=1".asFormula
  }

  "cutInSolns" should "solve x'=y,t'=1" in {withMathematica(implicit qeTool => {
    val f = "x=0&y=0&t=0 -> [{x'=y, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) &  AxiomaticODESolver.cutInSoln(qeTool)(1)
    loneSucc(proveBy(f,t)) shouldBe "[{x'=y,t'=1&true&x=y*t+0}]x>=0".asFormula
  })}

  //@todo fix this -- we need to produce 1*t+0 as the recurrence for x. Also, rename recurrence!
  it should "solve single time dependent eqn" ignore {withMathematica(implicit qeTool => {
    val f = "x=0&y=0&t=0 -> [{x'=t, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) &  AxiomaticODESolver.cutInSoln(qeTool)(1).*@(TheType())
    println(proveBy(f,t))
//    loneSucc(proveBy(f,t)) shouldBe "[{x'=y,t'=1&true&x=0*t+0}]x>=0".asFormula
  })}

  //@todo I think we need to actually saturate cutInSolns because otherwise we don't include enough domain constraint stuff???
  it should "solve double integrator" in {withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}]x>=0".asFormula
    val t =
      TactixLibrary.implyR(1) &
      AxiomaticODESolver.cutInSoln(qeTool)(1) &
      AxiomaticODESolver.cutInSoln(qeTool)(1)
    println(proveBy(f,t))
  })}

  //endregion

  "axiomatic ode solver" should "solve double integrator" in {withMathematica(implicit qeTool => {
    val f = "x=1&v=2&a=3&t=0 -> [{x'=v,v'=a, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & AxiomaticODESolver(qeTool)(1)
    println(proveBy(f,t))
  })}


  //region proveAs construct

  "proveAs" should "prove as" in {
    val f = "P() -> P()".asFormula
    val t = ProveAs("piffp", f, TactixLibrary.implyR(1) & TactixLibrary.close) & HilbertCalculus.lazyUseAt("piffp")(1)
    proveBy(f,t) shouldBe 'proved
  }

  it should "work in simplifyPostCondition" in {withMathematica(implicit qeTool => {
    val f = "[{x'=1}](x=22 -> x>0)".asFormula
    val t = simplifyPostCondition(qeTool)(1)
    proveBy(f,t) shouldBe "[{x'=1&true}]22>0".asFormula
  })}

  //endregion


  //region inverse diff cut missing around.

  "inverse diff cut" should "work" in { withMathematica(implicit qeTool => {
//    val fwd = "blah" by ((p: Provable, s: SuccPosition) => {
//      HilbertCalculus.useFor("DC differential cut")(s)(p)
//    })

    val f = "v=0&a=0&x=0&t=0 -> [{x'=v, v'=a, t'=1 &true&v=0*t+0}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) & inverseDiffCut(qeTool)(1)

    println(proveBy(f,t).prettyString)
  })}

  //endregion

}
