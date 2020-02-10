/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.qe.Z3QETool
import edu.cmu.cs.ls.keymaerax.tools.{Tool, ToolOperationManagement}

import scala.collection.immutable.Map

/**
  * Z3 quantifier elimination tool for tactics.
  *
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.Z3ToolProvider]] to obtain instances of Z3 that are properly initialized
  *      and installed/updated.
  * @author Stefan Mitsch
  */
final class Z3 extends Tool with QETacticTool with ToolOperationManagement {
  /** @inheritdoc */
  override val name: String = "Z3"

  /** The Z3 QE tool. */
  private val z3: Z3QETool = new Z3QETool()

  /** @inheritdoc */
  override def init(config: Map[String,String]): Unit = z3.init(config)

  /** @inheritdoc */
  override def isInitialized: Boolean = z3.isInitialized

  /** @inheritdoc */
  override def restart(): Unit = z3.restart()

  /** @inheritdoc */
  override def shutdown(): Unit = z3.shutdown()

  /** @inheritdoc */
  override def cancel(): Boolean = z3.cancel()

  /** @inheritdoc */
  override def qe(formula: Formula): Lemma = {
    require(isInitialized, "Z3 needs to be initialized before use")
    ProvableSig.proveArithmetic(z3, formula)
  }

  /** @inheritdoc */
  override def setOperationTimeout(timeout: Int): Unit = z3.setOperationTimeout(timeout)

  /** @inheritdoc */
  override def getOperationTimeout: Int = z3.getOperationTimeout

  /** @inheritdoc */
  override def getAvailableWorkers: Int = 1
}
