/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tools.ext

import org.keymaerax.core._
import org.keymaerax.lemma.Lemma
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tools.qe.BigDecimalQETool
import org.keymaerax.tools.{Tool, ToolExecutionException, ToolOperationManagement}

/**
 * Big decimal quantifier elimination tool for tactics, forwards to [[BigDecimalQETool]].
 * @author
 *   Stefan Mitsch
 */
final class BigDecimalTool extends Tool with QETacticTool with ToolOperationManagement {

  /** @inheritdoc */
  override val name: String = "BigDecimalTool"

  /** @inheritdoc */
  override def restart(): Unit = {}

  /** @inheritdoc */
  override def shutdown(): Unit = {}

  /** @inheritdoc */
  override def isInitialized: Boolean = true

  /** @inheritdoc */
  override def cancel(): Boolean = true

  /** @inheritdoc */
  override def qe(formula: Formula): Lemma = {
    require(isInitialized, "BigDecimalTool needs to be initialized before use")
    ProvableSig.proveArithmeticLemma(BigDecimalQETool, formula)
  }

  /** @inheritdoc */
  override def qe(g: Goal, continueOnFalse: Boolean): (Goal, Formula) = g match {
    case Atom(fml) =>
      val Sequent(IndexedSeq(), IndexedSeq(Equiv(_, result))) = qe(fml).fact.conclusion
      g -> result
    case _ => throw ToolExecutionException("BigDecimalQETool supports only atom goals")
  }

  /** @inheritdoc */
  override def setOperationTimeout(timeout: Int): Unit = {}

  /** @inheritdoc */
  override def getOperationTimeout: Int = -1

  /** @inheritdoc */
  override def getAvailableWorkers: Int = 1
}
