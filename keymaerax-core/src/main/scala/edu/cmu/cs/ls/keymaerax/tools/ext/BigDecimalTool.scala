/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.{BigDecimalQETool, ToolBase, ToolOperationManagement}

import scala.collection.immutable.Map

/**
  * Big decimal quantifier elimination tool for tactics, forwards to [[BigDecimalQETool]].
  * @author Stefan Mitsch
  */
final class BigDecimalTool extends ToolBase("BigDecimalTool") with QETacticTool with ToolOperationManagement {

  /** @inheritdoc */
  override def init(config: Map[String,String]): Unit = { initialized=true }

  /** @inheritdoc */
  override def restart(): Unit = {}

  /** @inheritdoc */
  override def shutdown(): Unit = {}

  /** @inheritdoc */
  override def cancel(): Boolean = true

  /** @inheritdoc */
  override def qe(formula: Formula): Lemma = {
    require(isInitialized, "Z3 needs to be initialized before use")
    ProvableSig.proveArithmetic(BigDecimalQETool, formula)
  }

  /** @inheritdoc */
  override def setOperationTimeout(timeout: Int): Unit = {}

  /** @inheritdoc */
  override def getOperationTimeout: Int = -1

  /** @inheritdoc */
  override def getAvailableWorkers: Int = 1
}
