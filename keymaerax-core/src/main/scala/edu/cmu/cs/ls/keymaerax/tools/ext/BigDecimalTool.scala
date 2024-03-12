/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import edu.cmu.cs.ls.keymaerax.tools.{Tool, ToolExecutionException, ToolOperationManagement}

import scala.collection.immutable.Map

/**
 * Big decimal quantifier elimination tool for tactics, forwards to [[BigDecimalQETool]].
 * @author
 *   Stefan Mitsch
 */
final class BigDecimalTool extends Tool with QETacticTool with ToolOperationManagement {

  /** @inheritdoc */
  override val name: String = "BigDecimalTool"

  /** @inheritdoc */
  override def init(config: Map[String, String]): Unit = {}

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
