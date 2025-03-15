/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import fastparse.JavaWhitespace._
import fastparse._
import org.keymaerax.GlobalState
import org.keymaerax.core.Formula
import org.keymaerax.parser.DLParser.parseException

import scala.collection.immutable._

/**
 * Parse an axiom string to a list of named formulas that are to be used as axioms in a theory.
 * @author
 *   Andre Platzer
 * @see
 *   [[KeYmaeraXAxiomParser]]
 */
object DLAxiomParser extends (String => List[(String, Formula)]) {

  /**
   * Parse an axiom string into a list of named axioms.
   * @param input
   *   The contents of the axiom file.
   * @return
   *   A list of named axioms occurring in the string.
   */
  def apply(input: String): List[(String, Formula)] = axiomParser(input)

  private val axiomParser: String => List[(String, Formula)] = input => {
    fastparse.parse(input, implicit p => axiomList) match {
      case Parsed.Success(value, _) => value
      case f: Parsed.Failure => throw parseException(f).inContext("<AxiomBase>")
    }
  }

  /** axiom: Parses a dL axiom. */
  def axiom[$: P]: P[(String, Formula)] = P("Axiom" ~ GlobalState.parser.string ~ formula ~ "End.")

  /** axiom: Parses a dL axiom. */
  def axiomList[$: P]: P[List[(String, Formula)]] = P(Start ~ axiom.rep(1) ~ End).map(_.toList)

  /** formula: Parses a dL formula via [[DLParser.formula]]. */
  private def formula[$: P]: P[Formula] = GlobalState.parser.formula
}
