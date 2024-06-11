/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider
import edu.cmu.cs.ls.keymaerax.core.{
  And,
  BaseVariable,
  Equal,
  Formula,
  FuncOf,
  Function,
  Number,
  Real,
  StaticSemantics,
  Term,
  True,
  Unit,
  Variable,
}
import edu.cmu.cs.ls.keymaerax.hydra.responses.tools.SimulationResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, RegisteredOnlyRequest, Response, UserProofRequest}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}

import scala.collection.immutable.List

class SimulationRequest(
    db: DBAbstraction,
    userId: String,
    proofId: String,
    nodeId: String,
    initial: Formula,
    stateRelation: Formula,
    steps: Int,
    n: Int,
    stepDuration: Number,
) extends UserProofRequest(db, userId, proofId) with RegisteredOnlyRequest {
  override protected def doResultingResponse(): Response = {
    def replaceFuncs(fml: Formula) = ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          // TODO: check if still correct
          case FuncOf(Function(name, idx, Unit, Real, None), _) => Right(BaseVariable(name, idx))
          case _ => Left(None)
        }
      },
      fml,
    )

    ToolProvider.simulationTool() match {
      case Some(s) =>
        val varsStateRelation = replaceFuncs(stateRelation).get
        val varsInitial = replaceFuncs(initial).get
        val timedStateRelation = varsStateRelation.replaceFree(Variable("t_"), stepDuration)

        // preserve initial values of unmodified variables
        val vars = StaticSemantics.freeVars(timedStateRelation).toSet
        val modifiedVars = vars.flatMap(v =>
          if (v.name.startsWith("pre")) List(v, Variable(v.name.stripPrefix("pre"), v.index)) else List.empty
        )
        val unmodified = (vars -- modifiedVars)
          .map(v => Equal(v, Variable("pre" + v.name, v.index)))
          .reduceOption(And)
          .getOrElse(True)

        val simulation = s.simulate(varsInitial, And(unmodified, timedStateRelation), steps, n)

        val samples = 100
        // downselect to 100 samples, otherwise JS library plot is illegible
        val visualize = simulation.map(s => {
          val ratio = s.size / samples
          if (ratio > 1) s.grouped(ratio).map(_.head).toList else s
        })

        new SimulationResponse(visualize, steps / samples, stepDuration)
      case _ => new ErrorResponse("No simulation tool configured, please setup Mathematica")
    }
  }
}
