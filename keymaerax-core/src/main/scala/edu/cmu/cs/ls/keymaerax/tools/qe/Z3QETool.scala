/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/** @note Code Review: 2016-08-02 */
package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.tools.{Tool, ToolOperationManagement}

/**
 * Z3 trusted quantifier elimination tool.
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.btactics.Z3ToolProvider]] to obtain instances of Z3 that are properly initialized and
 *   installed/updated. Created by smitsch on 4/27/15.
 * @author
 *   Ran Ji
 * @author
 *   Stefan Mitsch
 */
final class Z3QETool extends Tool with QETool with ToolOperationManagement {
  // Z3 is a trusted tool. Do not extend this class with other tool interfaces. Extend ext.Z3 instead.

  /** @inheritdoc */
  override val name: String = "Z3QETool"

  /* The solver instance */
  private var z3: Z3Solver = _

  def init(config: ToolConfiguration): Unit = { z3 = new Z3Solver(config.z3Path.get, DefaultSMTConverter) }

  /** @inheritdoc */
  override def restart(): Unit = cancel()

  /** @inheritdoc */
  override def shutdown(): Unit = {
    cancel()
    z3 = null
  }

  /** @inheritdoc */
  override def isInitialized: Boolean = z3 != null

  /** @inheritdoc */
  override def cancel(): Boolean = z3 == null || z3.cancel()

  /** @inheritdoc */
  override def quantifierElimination(formula: Formula): Formula = {
    require(isInitialized, "Z3 needs to be initialized before use")
    z3.qe(formula)
  }

  /** @inheritdoc */
  override def setOperationTimeout(timeout: Int): Unit = z3.setOperationTimeout(timeout)

  /** @inheritdoc */
  override def getOperationTimeout: Int = z3.getOperationTimeout

  /** @inheritdoc */
  override def getAvailableWorkers: Int = 1
}
