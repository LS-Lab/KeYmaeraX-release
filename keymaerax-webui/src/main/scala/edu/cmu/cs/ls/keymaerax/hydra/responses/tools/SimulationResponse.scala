/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.tools

import edu.cmu.cs.ls.keymaerax.core.{NamedSymbol, Number}
import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsArray, JsNumber, JsObject, JsString}

import scala.collection.mutable.ListBuffer

class SimulationResponse(simulation: List[List[Map[NamedSymbol, Number]]], steps: Int, stepDuration: Number)
    extends Response {
  def getJson: JsObject = {
    val seriesList = simulation.map(convertToDataSeries)
    JsObject(
      "varNames" -> JsArray(seriesList.head.map(_._1).map(name => JsString(name.prettyString)).toVector),
      "ticks" ->
        JsArray(seriesList.head.head._2.indices.map(i => JsString((i * steps * stepDuration.value).toString)).toVector),
      "lineStates" -> JsArray(
        seriesList
          .map(series =>
            JsArray(series.map({ case (_, vs) => JsArray(vs.map(v => JsNumber(v.value)).toVector) }).toVector)
          )
          .toVector
      ),
      "radarStates" -> JsArray(
        simulation
          .map(run =>
            JsArray(run.map(state => JsArray(state.map({ case (_, v) => JsNumber(v.value) }).toVector)).toVector)
          )
          .toVector
      ),
    )
  }

  def convertToDataSeries(sim: List[Map[NamedSymbol, Number]]): List[(NamedSymbol, List[Number])] = {
    // convert to data series
    val dataSeries: Map[NamedSymbol, ListBuffer[Number]] = sim.head.keySet.map(_ -> ListBuffer[Number]()).toMap
    sim.foreach(state =>
      state.foreach({ case (n, v) =>
        dataSeries.getOrElse(n, throw new IllegalStateException("Unexpected data series " + n)) += v
      })
    )
    dataSeries.view.mapValues(_.toList).toList
  }
}
