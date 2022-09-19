/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.modelplex

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, TacticAssertionError, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, ModelPlex, ModelPlexConjecture, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.codegen.{CControllerGenerator, CGenerator, CMonitorGenerator, CodeGenerator, PythonGenerator, PythonMonitorGenerator}
import edu.cmu.cs.ls.keymaerax.core.{AssignAny, BaseVariable, Box, Choice, Compose, Formula, Imply, NamedSymbol, Not, ODESystem, Program, StaticSemantics, Test, True, Variable}
import edu.cmu.cs.ls.keymaerax.hydra.responses.modelplex.{ModelPlexArtifactResponse, ModelPlexCCodeResponse, ModelPlexMonitorResponse, ModelPlexSandboxResponse}
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, ModelPOJO, RegisteredOnlyRequest, Response, UserRequest}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, KeYmaeraXArchivePrinter, ParsedArchiveEntry, PrettierPrintFormatProvider}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.{List, ListMap, Map, Nil, Set}

class ModelPlexRequest(db: DBAbstraction, userId: String, modelId: String, artifact: String, monitorKind: String,
                       monitorShape: String, conditionKind: String,
                       additionalVars: List[String]) extends UserRequest(userId, _ => true) with RegisteredOnlyRequest {
  def resultingResponses(): List[Response]  = {
    val model = db.getModel(modelId)
    val modelFml = ModelPlex.normalizeInputFormula(ArchiveParser.parseAsExpandedFormula(model.keyFile))
    val vars: Set[BaseVariable] = (StaticSemantics.boundVars(modelFml).symbols ++ additionalVars.map(_.asVariable)).
      filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])

    artifact match {
      case "controller" => createController(model, modelFml, vars)
      case "monitor" => createMonitor(model, modelFml, vars)
      case "sandbox" => createSandbox(model, modelFml, vars)
    }
  }

  private def extractController(prg: Program): Program = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = prg match {
        case ODESystem(_, q) => Right(Test(q))
        case _ => Left(None)
      }
    }, prg).get
  }

  private def createController(model: ModelPOJO, modelFml: Formula, vars: Set[BaseVariable]): List[Response] = modelFml match {
    case Imply(init, Box(prg, _)) => conditionKind match {
      case "dL" => new ModelPlexArtifactResponse(model, extractController(prg)) :: Nil
      case "C" =>
        val controller = (new CGenerator(new CControllerGenerator(model.defs), init, model.defs))(prg, vars, CodeGenerator.getInputs(prg))
        val code =
          s"""${controller._1}
             |${controller._2}
             |
             |int main() {
             |  /* control loop stub */
             |  parameters params; /* set system parameters, e.g., = { .A=1.0 }; */
             |  while (true) {
             |    state current; /* read sensor values, e.g., = { .x=0.0 }; */
             |    state input;   /* resolve non-deterministic assignments, e.g., = { .x=0.5 }; */
             |    state post = ctrlStep(current, params, input);
             |    /* hand post actuator set values to actuators */
             |  }
             |  return 0;
             |}
             |""".stripMargin

        new ModelPlexCCodeResponse(model, code) :: Nil
      case c => new ErrorResponse("Unknown output format '" + c + "'; please use one of ['dL'|'C']") :: Nil
    }
    case _ => new ErrorResponse("Unsupported shape, expected assumptions -> [{ctrl;ode}*]safe, but got " + modelFml.prettyString) :: Nil
  }

  private def createSandbox(model: ModelPOJO, modelFml: Formula, stateVars: Set[BaseVariable]): List[Response] = modelFml match {
    case Imply(init, Box(prg, _)) =>
      createMonitorCondition(modelFml, stateVars, ListMap.empty) match {
        case Left((monitorConjecture, monitorCond, _)) =>
          def fresh(v: Variable, postfix: String): Variable = BaseVariable(v.name + postfix, v.index, v.sort)

          val fallback = extractController(prg)
          conditionKind match {
            case "dL" =>
              val ctrlVars = StaticSemantics.boundVars(fallback).toSet
              val ctrl = ctrlVars.map(v => AssignAny(fresh(v, "post"))).reduceRightOption(Compose).getOrElse(Test(True))
              val sandbox = Compose(ctrl, Choice(Test(monitorCond), Compose(Test(Not(monitorCond)), fallback)))
              new ModelPlexSandboxResponse(model, monitorConjecture, sandbox) :: Nil
            case "C" =>
              val ctrlInputs = CodeGenerator.getInputs(monitorCond)
              val ctrlMonitorCode = (new CGenerator(new CMonitorGenerator('resist, model.defs), init, model.defs))(monitorCond, stateVars, ctrlInputs, "Monitor")
              val inputs = CodeGenerator.getInputs(prg)
              val fallbackCode = new CControllerGenerator(model.defs)(prg, stateVars, inputs)
              val declarations = ctrlMonitorCode._1.trim
              val monitorCode = ctrlMonitorCode._2.trim

              val sandbox =
                s"""$declarations
                   |${fallbackCode._1}
                   |${fallbackCode._2}
                   |$monitorCode
                   |
                   |state ctrl(state curr, const parameters* const params, const input* const in) {
                   |  /* controller implementation stub: modify curr to return actuator set values */
                   |  return curr;
                   |}
                   |
                   |int main() {
                   |  /* control loop stub */
                   |  parameters params; /* set system parameters, e.g., = { .A=1.0 }; */
                   |  while (true) {
                   |    state current; /* read sensor values, e.g., = { .x=0.2 }; */
                   |    input in;   /* resolve non-deterministic assignments in the model */
                   |    state post = monitoredCtrl(current, &params, &in, &ctrl, &ctrlStep);
                   |    /* hand post actuator set values to actuators */
                   |  }
                   |  return 0;
                   |}
                   |""".stripMargin

              new ModelPlexCCodeResponse(model, sandbox) :: Nil
            case c => new ErrorResponse("Unknown output format '" + c + "'; please use one of ['dL'|'C']") :: Nil
          }
        case Right(e) => e :: Nil
      }
    case _ => new ErrorResponse("Unsupported shape, expected assumptions -> [{ctrl;ode}*]safe, but got " + modelFml.prettyString) :: Nil
  }

  /** Synthesizes a ModelPlex monitor formula over variables `vars` from the model `modelFml`.
   * Returns the monitor conjecture together with the synthesized monitor, or an error. */
  private def createMonitorCondition(modelFml: Formula, vars: Set[BaseVariable],
                                     unobservable: ListMap[NamedSymbol, Option[Formula]]): Either[(Formula, Formula, BelleExpr), ErrorResponse] = {
    val ModelPlexConjecture(_, modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(modelFml, vars.toList.sorted[NamedSymbol], unobservable)

    val mx = ModelPlex.mxSynthesize(monitorKind) &
      //@todo unobservable symbols tactic argument not yet serializable
      //ModelPlex.mxAutoInstantiate(assumptions, unobservable.keySet.toList, Some(ModelPlex.mxSimplify)) &
      ModelPlex.mxAutoInstantiate(assumptions) &
      ModelPlex.mxFormatShape(monitorShape)

    val monitorCond = try {
      TactixLibrary.proveBy(modelplexInput, mx)
    } catch {
      case ex: TacticInapplicableFailure =>
        return Right(new ErrorResponse("Unable to synthesize monitor (missing feature), because \n" + ex.getMessage))
      case ex: TacticAssertionError =>
        return Right(new ErrorResponse("ModelPlex failed: expected unique result, but \n" + ex.getMessage))
    }

    Left(modelplexInput, monitorCond.subgoals.head.succ.head, mx)
  }

  private def createMonitor(model: ModelPOJO, modelFml: Formula, vars: Set[BaseVariable]): List[Response] = {
    val Imply(init, Box(prg, _)) = modelFml
    createMonitorCondition(modelFml, vars, ListMap.empty) match {
      case Left((modelplexConjecture, monitorFml, synthesizeTactic)) =>
        conditionKind match {
          case "dL" =>
            val monitorProof = TactixLibrary.implyR(1) & synthesizeTactic &
              TactixLibrary.prop & DebuggingTactics.done("Monitor proof")
            val mxProof = TactixLibrary.proveBy(Imply(monitorFml, modelplexConjecture), monitorProof)
            val entry = ParsedArchiveEntry(model.name + " ModelPlex Monitor", "theorem",
              "",
              mxProof.conclusion.succ.head.prettyString, Declaration(Map.empty),
              mxProof.conclusion.succ.head,
              ("ModelPlex Monitor Proof", BellePrettyPrinter(monitorProof), monitorProof) :: Nil,
              Nil, Map.empty)
            new ModelPlexMonitorResponse(model, monitorFml, new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))(entry)) :: Nil
          case "C" =>
            val inputs = CodeGenerator.getInputs(prg)
            val monitor = (new CGenerator(new CMonitorGenerator('resist, model.defs), init, model.defs))(monitorFml, vars, inputs, model.name)
            val code =
              s"""${monitor._1}
                 |${monitor._2}
                 |
                 |int main() {
                 |  /* sandbox stub, select 'sandbox' to auto-generate */
                 |  parameters params; /* set parameter values, e.g., = { .A=1.0 }; */
                 |  while (true) {
                 |    state pre; /* read sensor values, e.g., = { .x=0.0 }; */
                 |    state post; /* run controller */
                 |    if (!monitorSatisfied(pre,post,params)) post = post; /* replace with fallback control output */
                 |    /* hand post actuator set values to actuators */
                 |  }
                 |  return 0;
                 |}
                 |""".stripMargin

            new ModelPlexCCodeResponse(model, code) :: Nil
          case "Python" =>
            val inputs = CodeGenerator.getInputs(prg)
            val monitor = (new PythonGenerator(new PythonMonitorGenerator('min, model.defs), init, model.defs))(monitorFml, vars, inputs, model.name)
            val code =
              s"""${monitor._1}
                 |${monitor._2}""".stripMargin

            new ModelPlexCCodeResponse(model, code) :: Nil
        }
      case Right(e) => e :: Nil
    }
  }
}