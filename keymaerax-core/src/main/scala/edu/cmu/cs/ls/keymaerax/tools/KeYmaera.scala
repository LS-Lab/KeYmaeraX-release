/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.PrettyPrinter

import scala.collection.immutable.Map

/**
 * The KeYmaera tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 * @todo Rename to KeYmaeraX to avoid confusion.
 */
object KeYmaera extends ToolBase("KeYmaera") {
  override def init(config : Map[String,String]) = {
    super.init(config);
    //@todo moved this initialization outside the core. Is this the right place?
    PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter)

  }

}
