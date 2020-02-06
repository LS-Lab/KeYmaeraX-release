/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.{DefaultSMTConverter, ToolBase}

import scala.collection.immutable.Map

/**
  * Polya quantifier elimination tool.
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.PolyaToolProvider]] to obtain instances of Polya that are properly
  *     initialized and installed/updated.
  * @author Ran Ji
  * @author Stefan Mitsch
  */
class Polya extends ToolBase("Polya") with QETool {
  private var polya: PolyaSolver = _

  /** @inheritdoc */
  override def init(config: Map[String,String]): Unit = {
    polya = new PolyaSolver(config("polyaPath"), DefaultSMTConverter)
    initialized = true
  }

  /** @inheritdoc */
  override def qeEvidence(formula: Formula): (Formula, Evidence) = {
    require(isInitialized, "Polya needs to be initialized before use")
    polya.qe(formula)
  }

  /** @inheritdoc */
  override def restart(): Unit = {}

  /** @inheritdoc */
  override def shutdown(): Unit = {
    initialized = false
  }
}
