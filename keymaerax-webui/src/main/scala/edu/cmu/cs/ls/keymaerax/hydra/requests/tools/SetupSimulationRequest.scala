/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.btactics.{Ax, AxIndex, TacticHelper, TactixLibrary, ToolProvider}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core.{
  And,
  Assign,
  BaseVariable,
  Box,
  Compose,
  Diamond,
  DifferentialSymbol,
  Equal,
  Expression,
  Formula,
  Imply,
  Loop,
  NamedSymbol,
  ODESystem,
  Program,
  Real,
  StaticSemantics,
  Term,
  Test,
  True,
  Variable,
}
import edu.cmu.cs.ls.keymaerax.hydra.responses.tools.SetupSimulationResponse
import edu.cmu.cs.ls.keymaerax.hydra.{
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  RegisteredOnlyRequest,
  Response,
  UserProofRequest,
}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.{ExpressionAugmentor, SequentAugmentor}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, FormulaTools, PosInExpr}
import edu.cmu.cs.ls.keymaerax.tools.ToolException
import edu.cmu.cs.ls.keymaerax.utils.EulerIntegrationCompiler

import scala.collection.immutable.{List, Map, Nil, Set}

class SetupSimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with RegisteredOnlyRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(node) =>
        // @note not a tactic because we don't want to change the proof tree just by simulating
        val sequent = node.goal.get
        val defs = node.proof.info.defs(db)
        val fml = defs.exhaustiveSubst(sequent.toFormula)
        if (ToolProvider.odeTool().isDefined) fml match {
          case Imply(initial, b @ Box(prg, _)) =>
            // all symbols because we need frame constraints for constants
            val vars = (StaticSemantics.symbols(prg) ++ StaticSemantics.symbols(initial))
              .filter(_.isInstanceOf[BaseVariable])
            val Box(prgPre, _) = vars
              .foldLeft[Formula](b)((b, v) => b.replaceAll(v, Variable("pre" + v.name, v.index, v.sort)))
            val stateRelEqs = vars
              .map(v => Equal(v.asInstanceOf[Term], Variable("pre" + v.name, v.index, v.sort)))
              .reduceRightOption(And)
              .getOrElse(True)
            val simSpec = Diamond(solveODEs(prgPre), stateRelEqs)
            new SetupSimulationResponse(addNonDetInitials(initial, vars), transform(simSpec)) :: Nil
          case _ => new ErrorResponse("Simulation only supported for formulas of the form initial -> [program]safe") ::
              Nil
        }
        else new ErrorResponse("No simulation tool available, please configure Mathematica") :: Nil
    }
  }

  private def addNonDetInitials(initial: Formula, vars: Set[NamedSymbol]): Formula = {
    val nonDetInitials = vars -- StaticSemantics.freeVars(initial).symbols
    nonDetInitials.foldLeft(initial)((f, v) => And(f, Equal(v.asInstanceOf[Term], v.asInstanceOf[Term])))
  }

  private def transform(simSpec: Diamond): Formula = {
    val stateRelation = TactixLibrary.proveBy(
      simSpec,
      TactixLibrary.chase(
        3,
        3,
        (e: Expression) =>
          e match {
            // no equational assignments
            case Box(Assign(_, _), _) => Ax.assignbAxiom :: Ax.assignbup :: Nil
            case Diamond(Assign(_, _), _) => Ax.assigndAxiom :: Ax.assigndup :: Nil
            // remove loops
            case Diamond(Loop(_), _) => Ax.loopApproxd :: Nil
            // @note: do nothing, should be gone already
            case Diamond(ODESystem(_, _), _) => Nil
            case _ => AxIndex.axiomsFor(e)
          },
      )(Symbol("R")),
    )
    assert(
      stateRelation.subgoals.size == 1 && stateRelation.subgoals.head.ante.isEmpty &&
        stateRelation.subgoals.head.succ.size == 1,
      "Simulation expected to result in a single formula",
    )
    stateRelation.subgoals.head.succ.head
  }

  private def solveODEs(prg: Program): Program = ExpressionTraversal
    .traverse(
      new ExpressionTraversalFunction() {
        override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
          case sys @ ODESystem(_, evoldomain) => Right(Compose(Test(evoldomain), solve(sys)))
          case _ => Left(None)
        }
      },
      prg,
    )
    .get

  private def solve(sys: ODESystem): Program = {
    val iv: Map[Variable, Variable] = DifferentialHelper
      .getPrimedVariables(sys.ode)
      .map(v => v -> Variable(v.name + "0", v.index, v.sort))
      .toMap
    val time: Variable = Variable("t_", None, Real)
    try {
      val solution = ToolProvider.odeTool().get.odeSolve(sys.ode, time, iv).get
      val flatSolution = FormulaTools
        .conjuncts(solution)
        .sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size)
      Compose(
        // @store initial values
        iv.map({ case (v, i) => Assign(i, v) }).reduceRightOption(Compose).getOrElse(Test(True)),
        Compose(
          flatSolution
            .map({ case Equal(v: Variable, r) => Assign(v, r) })
            .reduceRightOption(Compose)
            .getOrElse(Test(True)),
          Test(sys.constraint),
        ),
      )
    } catch {
      case _: ToolException =>
        val prg = new EulerIntegrationCompiler()(sys)
        // introduce variables for differential symbols (prepare for ModelPlex), replace step with t_
        val dotted = StaticSemantics
          .symbols(prg)
          .filter(_.isInstanceOf[DifferentialSymbol])
          .foldLeft(prg)({ case (prg, v) =>
            prg.replaceAll(v, TacticHelper.freshNamedSymbol(Variable(v.name + "dot", v.index), sys))
          })
        val stepVar = StaticSemantics.freeVars(dotted).toSet.filter(_.name == "step").maxBy(_.index)
        dotted.replaceAll(stepVar, time)
    }
  }
}
