/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.modelplex

import org.keymaerax.btactics.{ModelPlex, ModelPlexConjecture, SimplifierV3, TactixLibrary, ToolProvider}
import org.keymaerax.core.{
  And,
  BaseVariable,
  Formula,
  FuncOf,
  Function,
  Imply,
  NamedSymbol,
  Not,
  Number,
  Real,
  StaticSemantics,
  Term,
  True,
  Unit,
  Variable,
}
import org.keymaerax.hydra.responses.modelplex.TestSynthesisResponse
import org.keymaerax.hydra.{DBAbstraction, ErrorResponse, RegisteredOnlyRequest, Response, UserRequest}
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.parser.ArchiveParser
import org.keymaerax.tools.ToolException
import org.keymaerax.tools.ext.{Mathematica, TestSynthesis}

import scala.collection.immutable.{List, ListMap, Map, Nil}

class TestSynthesisRequest(
    db: DBAbstraction,
    userId: String,
    modelId: String,
    monitorKind: String,
    testKinds: Map[String, Boolean],
    amount: Int,
    timeout: Option[Int],
) extends UserRequest(userId, _ => true) with RegisteredOnlyRequest {
  def resultingResponse(): Response = {
    logger.debug("Got Test Synthesis Request")
    val model = db.getModel(modelId)
    val modelFml = ArchiveParser.parseAsFormula(model.keyFile)
    val vars = StaticSemantics.boundVars(modelFml).symbols.filter(_.isInstanceOf[BaseVariable]).toList
    val unobservable = ListMap.empty[NamedSymbol, Option[Formula]]
    val ModelPlexConjecture(_, modelplexInput, assumptions) = ModelPlex
      .createMonitorSpecificationConjecture(modelFml, vars, unobservable)
    val monitorCond = (monitorKind, ToolProvider.simplifierTool()) match {
      case ("controller", tool) =>
        val foResult = TactixLibrary.proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
        try {
          TactixLibrary.proveBy(
            foResult.subgoals.head,
            ModelPlex
              .optimizationOneWithSearch(tool, assumptions, unobservable.keySet.toList, Some(ModelPlex.mxSimplify))(1),
          )
        } catch { case _: Throwable => foResult }
      case ("model", tool) => TactixLibrary.proveBy(
          modelplexInput,
          ModelPlex.modelMonitorByChase(1) &
            SimplifierV3.simpTac(Nil, SimplifierV3.defaultFaxs, SimplifierV3.arithBaseIndex)(1) &
            ModelPlex
              .optimizationOneWithSearch(tool, assumptions, unobservable.keySet.toList, Some(ModelPlex.mxSimplify))(1),
        )
    }

    def variance(vals: Map[Term, Term]): Number = {
      val (pre, post) = vals.partition({ case (v, _) => v.isInstanceOf[BaseVariable] })
      val postByPre: Map[Term, BigDecimal] = post.map({
        case (FuncOf(Function(name, idx, Unit, Real, _), _), Number(value)) if name.endsWith("post") =>
          Variable(name.substring(0, name.length - "post".length), idx) -> value
        case (v, Number(value)) => v -> value
      })
      Number(
        pre
          .map({
            case (v, Number(value)) if postByPre.contains(v) => (value - postByPre(v)) * (value - postByPre(v))
            case _ => BigDecimal(0)
          })
          .sum
      )
    }

    val Imply(True, cond) = monitorCond.subgoals.head.toFormula

    val assumptionsCond = assumptions.reduceOption(And).getOrElse(True)
    val testSpecs: List[(String, Formula)] = testKinds
      .map({
        case ("compliant", true) => Some("compliant" -> cond)
        case ("incompliant", true) => Some("incompliant" -> Not(cond))
        case _ => None
      })
      .filter(_.isDefined)
      .map(c => c.get._1 -> And(assumptionsCond, c.get._2))
      .toList

    val metric = ModelPlex.toMetric(cond)
    ToolProvider.cexTool() match {
      case Some(tool: Mathematica) =>
        val synth = new TestSynthesis(tool)
        // val testCases = synth.synthesizeTestConfig(testCondition, amount, timeout)
        val testCases = testSpecs.map(ts => ts._1 -> synth.synthesizeTestConfig(ts._2, amount, timeout))
        val tcSmVar = testCases.map(tc =>
          tc._1 ->
            tc._2
              .map(tcconfig =>
                (
                  tcconfig,
                  // @note tcconfig (through findInstance) may contain values that later lead to problems (e.g., division by 0)
                  try { Some(synth.synthesizeSafetyMarginCheck(metric, tcconfig)) }
                  catch { case _: ToolException => None },
                  variance(tcconfig),
                )
              )
        )
        new TestSynthesisResponse(model, metric, tcSmVar)
      case None => new ErrorResponse("Test case synthesis failed, missing Mathematica")
    }
  }
}
