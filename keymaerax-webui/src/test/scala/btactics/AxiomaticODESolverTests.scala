/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{SuccPosition, TheType}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.AxiomaticODESolver._

/**
  * @author Nathan Fulton
  */
class AxiomaticODESolverTests extends TacticTestBase {
//  import Augmentors._

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //region unit tests
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //@todo exists monotone
  "setupTimeVar" should "work when time exists" ignore {
    val system = "[{x'=v}]1=1".asFormula
    val tactic = addTimeVarIfNecessary
    val result = proveBy(system, tactic(SuccPosition(1, 0::Nil)))
    println(result.prettyString)
  }

  "cutInSolns" should "solve x'=y,t'=1" in {withMathematica(implicit qeTool => {
    val f = "x=0&y=0 -> [{x'=y, t'=1}]x>=0".asFormula
    val t = TactixLibrary.implyR(1) &  AxiomaticODESolver.cutInSoln(qeTool)(1)
    loneSucc(proveBy(f,t)) shouldBe "[{x'=y,t'=1&true&x=0*t+0}]x>=0".asFormula
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

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //region comprehensive tests
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //endregion


}
