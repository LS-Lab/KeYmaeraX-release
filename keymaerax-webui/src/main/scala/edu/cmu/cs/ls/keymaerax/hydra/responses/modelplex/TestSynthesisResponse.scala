/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.modelplex

import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Formula, FuncOf, Function, Nothing, Number, Real, Term, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.hydra.{ModelPOJO, Response, UIKeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import spray.json.{JsArray, JsNumber, JsObject, JsString, JsValue}

class TestSynthesisResponse(model: ModelPOJO, metric: Formula,
                            //@todo class: List[(SeriesName, List[(Var->Val, SafetyMargin, Variance)])]
                            testCases: List[(String, List[(Map[Term, Term], Option[Number], Number)])]) extends Response {
  private val fmlHtml = JsString(UIKeYmaeraXPrettyPrinter("", plainText=false)(metric))
  private val fmlString = JsString(UIKeYmaeraXPrettyPrinter("", plainText=true)(metric))
  private val fmlPlainString = JsString(KeYmaeraXPrettyPrinter(metric))

  private val minRadius = 5  // minimum radius of bubbles even when all pre are equal to their post
  private val maxRadius = 30 // maximum radius of bubbles even when wildly different values

  private val Number(maxVariance) = testCases.flatMap(_._2).maxBy(_._3.value)._3

  private def radius(n: BigDecimal): BigDecimal =
    if (maxVariance > 0) minRadius + (maxRadius-minRadius)*(n/maxVariance)
    else minRadius

  private def scatterData(tc: List[(Map[Term, Term], Option[Number], Number)]) = JsArray(tc.zipWithIndex.map(
    { case ((_, safetyMargin, Number(variance)), idx) => JsObject(
      "x" -> JsNumber(idx),
      "y" -> (safetyMargin match { case Some(Number(sm)) => JsNumber(sm) case None => JsNumber(-1) }),
      "r" -> JsNumber(radius(variance))
    ) }):_*)

  // pre/post/labels/series
  private def prePostVals(vals: Map[Term, Term]): (JsArray, JsArray, JsArray, JsArray) = {
    val (pre, post) = vals.partition({ case (v, _) => v.isInstanceOf[BaseVariable] })
    val preByPost: Map[Term, Term] = post.map({
      case (post@FuncOf(Function(name, idx, Unit, Real, _), _), _) if name.endsWith("post") =>
        post -> Variable(name.substring(0, name.length-"post".length), idx)
      case (v, _) => v -> v
    })
    val preJson = pre.map({ case (v, Number(value)) => JsObject("v" -> JsString(v.prettyString), "val" -> JsNumber(value)) })
    val postJson = post.map({ case (v, Number(value)) => JsObject("v" -> JsString(preByPost(v).prettyString), "val" -> JsNumber(value)) })
    val sortedKeys = pre.keys.toList.sortBy(_.prettyString)
    val labels = sortedKeys.map(v => JsString(v.prettyString))
    val preSeries = sortedKeys.map(k => pre.get(k) match { case Some(Number(v)) => JsNumber(v) })
    val postSeries = sortedKeys.map({ case k@BaseVariable(n, i, _) =>
      post.get(FuncOf(Function(n + "post", i, Unit, Real), Nothing)) match {
        case Some(Number(v)) => JsNumber(v)
        case None => pre.get(k) match { case Some(Number(v)) => JsNumber(v) } //@note constants
      }
    })
    (JsArray(preJson.toVector), JsArray(postJson.toVector), JsArray(labels.toVector),
      JsArray(JsArray(preSeries.toVector), JsArray(postSeries.toVector)))
  }

  private def seriesData(data: List[(Map[Term, Term], Option[Number], Number)]): JsArray = JsArray(data.zipWithIndex.map({
    case ((vals: Map[Term, Term], safetyMargin, Number(variance)), idx) =>
      val (preVals, postVals, labels, series) = prePostVals(vals)
      JsObject(
        "name" -> JsString(""+idx),
        "safetyMargin" -> (safetyMargin match { case Some(Number(sm)) => JsNumber(sm) case None => JsNumber(-1) }),
        "variance" -> JsNumber(variance),
        "pre" -> preVals,
        "post" -> postVals,
        "labels" -> labels,
        "seriesData" -> series
      )
  }):_*)

  def getJson: JsValue = JsObject(
    "modelid" -> JsString(model.modelId.toString),
    "metric" -> JsObject(
      "html" -> fmlHtml,
      "string" -> fmlString,
      "plainString" -> fmlPlainString
    ),
    "plot" -> JsObject(
      "data" -> JsArray(testCases.map({ case (_, tc) => scatterData(tc) }):_*),
      "series" -> JsArray(testCases.map({ case (name, _) => JsString(name) }):_*),
      "labels" -> JsArray(JsString("Case"), JsString("Safety Margin"), JsString("Variance"))
    ),
    "caseInfos" -> JsArray(testCases.map({ case (name, data) => JsObject("series" -> JsString(name), "data" -> seriesData(data)) }):_*)
  )
}