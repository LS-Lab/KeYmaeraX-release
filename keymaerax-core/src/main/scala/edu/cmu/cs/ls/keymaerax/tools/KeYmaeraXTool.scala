/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.PrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser

import scala.collection.immutable.Map

/**
 * The KeYmaera X tool, initializes the pretty printer.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 */
object KeYmaeraXTool extends Tool {
  /** @inheritdoc */
  override val name: String = "KeYmaera"

  /** Indicates whether the tool is initialized. */
  private var initialized = false

  /** @inheritdoc */
  override def init(config: Map[String,String]): Unit = {
    if (KeYmaeraXParser.LAX_MODE)
      //@note Careful, this disables contract checking in printing!
      PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXNoContractPrettyPrinter.pp)
    else
      PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter.pp)
    //PrettyPrinter.setPrinter(new edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXWeightedPrettyPrinter)
    initialized = true
  }

  /** @inheritdoc */
  override def restart(): Unit = { }

  /** @inheritdoc */
  override def shutdown(): Unit = {
    PrettyPrinter.setPrinter(e => e.getClass.getName)
    initialized = false
  }

  /** @inheritdoc */
  override def isInitialized: Boolean = initialized

  /** @inheritdoc */
  override def cancel(): Boolean = true
}
