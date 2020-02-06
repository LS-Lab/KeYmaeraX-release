/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.Map

/**
 * Z3 trusted quantifier elimination tool.
 *
 * Created by smitsch on 4/27/15.
 * @author Ran Ji
 * @author Stefan Mitsch
 */
final class Z3 extends ToolBase("Z3") with QETool with ToolOperationManagement {
  // Z3 is a trusted tool. Do not extend this class with other tool interfaces.
  private val z3 = new Z3Solver

  /** @inheritdoc */
  override def init(config: Map[String,String]): Unit = { initialized = true }

  /** @inheritdoc */
  override def restart(): Unit = { initialized = true }

  /** @inheritdoc */
  override def shutdown(): Unit = { initialized = false }

  /** @inheritdoc */
  override def cancel(): Boolean = z3.cancel()

  /** @inheritdoc */
  override def qeEvidence(formula: Formula): (Formula, Evidence) = {
    require(isInitialized, "Z3 needs to be initialized before use")
    z3.qeEvidence(formula)
  }

  /** @inheritdoc */
  override def setOperationTimeout(timeout: Int): Unit = z3.setOperationTimeout(timeout)

  /** @inheritdoc */
  override def getOperationTimeout: Int = z3.getOperationTimeout

  /** @inheritdoc */
  override def getAvailableWorkers: Int = 1
}
