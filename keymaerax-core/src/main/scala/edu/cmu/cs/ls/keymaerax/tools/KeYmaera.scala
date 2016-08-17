/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.PrettyPrinter

import scala.collection.immutable.Map

/**
 * The KeYmaera X tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 * @todo Rename to KeYmaeraX to avoid confusion.
 */
object KeYmaera extends ToolBase("KeYmaera") {
  override def init(config : Map[String,String]) = {
    //@todo moved this initialization outside the core. Is this the right place?
    PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter)
    //PrettyPrinter.setPrinter(new edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXWeightedPrettyPrinter)
    initialized = true
  }

  override def restart() = {}

  override def shutdown() = {
    PrettyPrinter.setPrinter(e => e.getClass.getName)
    initialized = false
  }
}
