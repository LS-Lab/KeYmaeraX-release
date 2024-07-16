/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.models

import org.keymaerax.btactics.SwitchedSystems._
import org.keymaerax.core.{
  Choice,
  Compose,
  Equal,
  FuncOf,
  Function,
  GreaterEqual,
  LessEqual,
  Nothing,
  ODESystem,
  Real,
  StaticSemantics,
  Term,
  Test,
  True,
  Unit,
}
import org.keymaerax.hydra._
import org.keymaerax.hydra.responses.models.GetControlledStabilityTemplateResponse
import org.keymaerax.parser.Parser
import org.keymaerax.parser.StringConverter.StringToStringConverter
import spray.json.DefaultJsonProtocol._
import spray.json.JsArray

import scala.annotation.nowarn
import scala.collection.immutable.{::, List, Nil}

class CreateControlledStabilityTemplateRequest(
    userId: String,
    code: String,
    switchingKind: String,
    specKind: List[String],
    vertices: JsArray,
    subGraphs: JsArray,
    transitions: JsArray,
) extends UserRequest(userId, _ => true) with ReadRequest {
  @nowarn("msg=match may not be exhaustive")
  override def resultingResponse(): Response = {
    val mode = "mode".asVariable
    def modeOf(s: String): Term = FuncOf(Function(s, None, Unit, Real), Nothing)

    val transitionsByVertex = transitions
      .elements
      .toList
      .map(_.asJsObject)
      .map(t => {
        val ttext = t.fields("text").convertTo[String]
        (
          t.fields("start").convertTo[String],
          (t.fields("end").convertTo[String], if (ttext.isEmpty) Test(True) else Parser.parser.programParser(ttext)),
        )
      })
      .groupBy(_._1)
      .map({ case (k, v) => k -> v.map(_._2) })

    val subgraphIds = subGraphs.elements.map(_.asJsObject).map(s => s.fields("id").convertTo[String])
    val modes = vertices.elements.map(_.asJsObject).filter(v => !subgraphIds.contains(v.fields("id").convertTo[String]))

    val (odes, init) = modes
      .map(m => {
        val mid = m.fields("id").convertTo[String]
        val prg = m.fields("text").convertTo[String].trim match {
          case "" => Test(True)
          case s => Parser.parser.programParser("{" + s + "}")
        }
        (mid, prg, transitionsByVertex.getOrElse(mid, List.empty))
      })
      .toList
      .
      // @note ignore subgraphs and other nodes without ODEs
      filter({ case (_, prg, _) => !StaticSemantics.freeVars(prg).isInfinite })
      .partition(_._2.isInstanceOf[ODESystem])

    if (init.length <= 1) {
      val initPrg = init
        .headOption
        .flatMap({ case (n, prg, _) =>
          val initTransitions = transitionsByVertex(n)
            .flatMap({
              case (d, Test(True)) => if (odes.exists(_._1 == d)) Some(Test(Equal(mode, modeOf(d)))) else None
              case (d, tp) => if (odes.exists(_._1 == d)) Some(Compose(Test(Equal(mode, modeOf(d))), tp)) else Some(tp)
            })
            .reduceRightOption(Choice)
          prg match {
            case Test(True) => initTransitions
            case _ => Some(initTransitions.map(Compose(prg, _)).getOrElse(prg))
          }
        })
      val c: SwitchedSystem = switchingKind match {
        case "autonomous" => StateDependent(odes.map({ case (_, o: ODESystem, _) => o }))
        case "timed" =>
          if (init.nonEmpty) {
            throw new IllegalArgumentException("Initialization not supported in timed switching template")
          } else {
            val time = subgraphIds
              .find(_.startsWith("Timed"))
              .flatMap(_.split(":").toList match {
                case _ :: t :: Nil => Some(t)
                case _ => None
              })
              .getOrElse("t_")
              .asVariable

            val modes = odes.map({ case (n, ODESystem(ode, q), transitions) =>
              val tBound = q match {
                case True => None
                case LessEqual(l, r) if l == time => Some(r)
                case _ => throw new IllegalArgumentException(
                    "Only time guards of the shape " + time +
                      "<=T allowed as evolution domain constraints in timed switching template"
                  )
              }
              val boundedTransitions = transitions.map({
                case (d, Test(True)) => (d, None)
                case (d, Test(GreaterEqual(l, r))) if l == time => (d, Some(r))
                case (_, _) => throw new IllegalArgumentException(
                    "Only time guards of the shape " + time + ">=T allowed on transitions in timed switching template"
                  )
              })
              (n, ode, tBound, boundedTransitions)
            })

            Timed(modes, "mode".asVariable, time)
          }
        case "guarded" =>
          if (init.nonEmpty) {
            throw new IllegalArgumentException("Initialization not supported in guarded switching template")
          } else {
            val modes = odes.map({ case (n, o: ODESystem, transitions) =>
              val guardedTransitions = transitions.map({
                case (d, Test(p)) => (d, p)
                case (_, _) => throw new IllegalArgumentException("Only tests allowed on transitions in guarded mode")
              })
              (n, o, guardedTransitions)
            })
            Guarded(modes, "mode".asVariable)
          }
        case "controlled" => Controlled(initPrg, odes.map({ case (n, o: ODESystem, t) => (n, o, t) }), mode)
      }
      new GetControlledStabilityTemplateResponse(code, c, specKind)
    } else {
      new ErrorResponse("At most 1 initialization node expected, but got nodes " + init.map(_._1).mkString(","))
    }
  }
}
