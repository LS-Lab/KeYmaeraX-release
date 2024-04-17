/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.{Find, Fixed, PositionLocator}
import edu.cmu.cs.ls.keymaerax.btactics.AxIndex
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import edu.cmu.cs.ls.keymaerax.btactics.macros.{
  ArgInfo,
  AxiomDisplayInfo,
  AxiomInfo,
  DerivationInfo,
  FormulaArg,
  InputAxiomDisplayInfo,
  ListArg,
  ProvableInfo,
  RuleDisplayInfo,
  SequentDisplay,
  SimpleDisplayInfo,
  TacticDisplayInfo,
}
import edu.cmu.cs.ls.keymaerax.core.Expression
import edu.cmu.cs.ls.keymaerax.hydra.{RequestHelper, Response}
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, SuccPosition}
import spray.json.{JsArray, JsBoolean, JsNull, JsNumber, JsObject, JsString, JsValue}

import scala.util.Try

case class ApplicableAxiomsResponse(
    derivationInfos: List[(DerivationInfo, Option[DerivationInfo])],
    suggestedInput: Map[ArgInfo, Expression],
    topLevel: Boolean,
    suggestedPosition: Option[PositionLocator] = None,
) extends Response {
  def inputJson(input: ArgInfo): JsValue = {
    (suggestedInput.get(input), input) match {
      case (Some(e), FormulaArg(name, _)) =>
        JsObject("type" -> JsString(input.sort), "param" -> JsString(name), "value" -> JsString(e.prettyString))
      case (_, ListArg(ai)) => // @todo suggested input for Formula*
        JsObject("type" -> JsString(input.sort), "elementType" -> JsString(ai.sort), "param" -> JsString(ai.name))
      case _ => JsObject("type" -> JsString(input.sort), "param" -> JsString(input.name))
    }
  }

  def inputsJson(info: List[ArgInfo]): JsArray = {
    info match {
      case Nil => JsArray()
      case inputs => JsArray(inputs.map(inputJson): _*)
    }
  }

  private def helpJson(codeName: String): JsString = {
    val helpResource = getClass.getResourceAsStream(s"/help/axiomsrules/$codeName-help.html")
    if (helpResource == null) JsString("")
    else JsString(scala.io.Source.fromInputStream(helpResource)(scala.io.Codec.UTF8).mkString)
  }

  def axiomJson(info: DerivationInfo): JsObject = {
    val formulaText = (info, info.display) match {
      case (_, di: AxiomDisplayInfo) => di.displayFormula
      case (_, di: InputAxiomDisplayInfo) => di.displayFormula
      case (info: AxiomInfo, _) => info.formula.prettyString
    }
    JsObject(
      "type" -> JsString("axiom"),
      "formula" -> JsString(formulaText),
      "codeName" -> JsString(info.codeName),
      "canonicalName" -> JsString(info.canonicalName),
      "longName" -> JsString(info.display.nameLong),
      "defaultKeyPos" ->
        (info match {
          case pi: ProvableInfo =>
            val key = AxIndex.axiomIndex(pi)._1
            JsString(key.pos.mkString("."))
          case _ => JsString("0")
        }),
      "displayInfoParts" ->
        (info match {
          case pi: ProvableInfo => RequestHelper.jsonDisplayInfoComponents(pi)
          case _ => JsNull
        }),
      "input" -> inputsJson(info.inputs),
      "help" -> helpJson(info.codeName),
    )
  }

  def tacticJson(info: DerivationInfo): JsObject = {
    JsObject(
      "type" -> JsString("tactic"),
      "expansible" -> JsBoolean(info.revealInternalSteps),
      "input" -> inputsJson(info.inputs),
      "help" -> helpJson(info.codeName),
    )
  }

  def sequentJson(sequent: SequentDisplay): JsValue = {
    val json = JsObject(
      "ante" -> JsArray(sequent.ante.map(JsString(_)): _*),
      "succ" -> JsArray(sequent.succ.map(JsString(_)): _*),
      "isClosed" -> JsBoolean(sequent.isClosed),
    )
    json
  }

  def ruleJson(
      info: DerivationInfo,
      conclusion: SequentDisplay,
      premises: List[SequentDisplay],
      inputGenerator: Option[String],
  ): JsObject = {
    val conclusionJson = sequentJson(conclusion)
    val premisesJson = JsArray(premises.map(sequentJson): _*)
    JsObject(
      "type" -> JsString("sequentrule"),
      "expansible" -> JsBoolean(info.revealInternalSteps),
      "conclusion" -> conclusionJson,
      "premise" -> premisesJson,
      "input" -> inputsJson(info.inputs),
      "inputGenerator" -> inputGenerator.map(JsString(_)).getOrElse(JsNull),
      "help" -> helpJson(info.codeName),
    )
  }

  def derivationJson(derivationInfo: DerivationInfo): JsObject = {
    val derivation = derivationInfo match {
      case info: AxiomInfo => axiomJson(info)
      case info: DerivationInfo => (info, info.display) match {
          case (_, _: SimpleDisplayInfo) => tacticJson(info)
          case (pi: DerivationInfo, _: AxiomDisplayInfo) => axiomJson(pi)
          case (pi: DerivationInfo, _: InputAxiomDisplayInfo) =>
            axiomJson(pi) // @todo usually those have tactics with RuleDisplayInfo
          case (_, di: RuleDisplayInfo) =>
            ruleJson(info, di.conclusion, di.premises, if (di.inputGenerator.isEmpty) None else Some(di.inputGenerator))
          case (_, di: TacticDisplayInfo) =>
            if (topLevel) ruleJson(
              info,
              di.conclusion,
              di.premises,
              if (di.inputGenerator.isEmpty) None else Some(di.inputGenerator),
            )
            else ruleJson(
              info,
              di.ctxConclusion,
              di.ctxPremises,
              if (di.inputGenerator.isEmpty) None else Some(di.inputGenerator),
            )
          case (_, _: AxiomDisplayInfo | _: InputAxiomDisplayInfo) => throw new IllegalArgumentException(
              s"Unexpected derivation info $derivationInfo displays as axiom but is not AxiomInfo"
            )
        }
    }
    JsObject(
      "id" -> new JsString(derivationInfo.codeName),
      "name" -> new JsString(derivationInfo.display.name),
      "asciiName" -> new JsString(derivationInfo.display.nameAscii),
      "codeName" -> new JsString(derivationInfo.codeName),
      "longName" -> new JsString(derivationInfo.display.nameLong),
      "displayLevel" -> new JsString(derivationInfo.displayLevel.name),
      "numPositionArgs" -> new JsNumber(derivationInfo.numPositionArgs),
      "derivation" -> derivation,
    )
  }

  private def posJson(pos: Option[PositionLocator]): JsValue = pos match {
    case Some(Fixed(p, _, _)) => new JsString(p.toString)
    case Some(Find(_, _, _: AntePosition, _, _)) => new JsString("L")
    case Some(Find(_, _, _: SuccPosition, _, _)) => new JsString("R")
    case _ => JsNull
  }

  def derivationJson(info: (DerivationInfo, Option[DerivationInfo])): JsObject = info._2 match {
    case Some(comfort) => JsObject(
        "standardDerivation" -> derivationJson(info._1),
        "comfortDerivation" -> derivationJson(comfort),
        "positionSuggestion" -> posJson(suggestedPosition),
      )
    case None =>
      JsObject("standardDerivation" -> derivationJson(info._1), "positionSuggestion" -> posJson(suggestedPosition))
  }

  def getJson: JsValue =
    JsArray(derivationInfos.map(i => Try(derivationJson(i)).toOption).filter(_.isDefined).map(_.get): _*)
}
