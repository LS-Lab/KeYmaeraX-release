/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.DLParser.parseException
import fastparse.JavaWhitespace._
import fastparse._

import scala.collection.immutable._

/**
 * Parse an axiom string to a list of named formulas that are to be used as axioms in a theory.
 * @author
 *   Andre Platzer
 * @see
 *   [[KeYmaeraXAxiomParser]]
 */
object DLAxiomParser extends (String => List[(String, Formula)]) {
  import DLParser.string
  private val checkAgainst: Option[String => List[(String, Formula)]] = Some(KeYmaeraXAxiomParser)

  /**
   * Parse an axiom string into a list of named axioms.
   * @param input
   *   The contents of the axiom file.
   * @return
   *   A list of named axioms occurring in the string.
   */
  def apply(input: String): List[(String, Formula)] = axiomParser(input)

  private val axiomParser: String => List[(String, Formula)] = input => {
    val newres = fastparse.parse(input, axiomList(_)) match {
      case Parsed.Success(value, _) => Right(value)
      case f: Parsed.Failure => Left(parseException(f).inContext("<AxiomBase>"))
    }
    checkAgainst match {
      case Some(p) =>
        val oldres =
          try { Right(p(input)) }
          catch { case e: Throwable => Left(e) }
        if (oldres != newres && (oldres.isRight || newres.isRight)) {
          println(s"Axiom parser disagreement: `$input`")
          println(s"KYXParser:\n${oldres match {
              case Left(x) => x.toString
              case Right(x) => x.toString
            }}")
          println(s"DLParser:\n${newres match {
              case Left(x) => x.toString
              case Right(x) => x.toString
            }}")
        }
      case None => // nothing to do
    }
    newres match {
      case Left(e) => throw e
      case Right(res) => res
    }
  }

  /** axiom: Parses a dL axiom. */
  def axiom[$: P]: P[(String, Formula)] = P("Axiom" ~ string ~ formula ~ "End.")

  /** axiom: Parses a dL axiom. */
  def axiomList[$: P]: P[List[(String, Formula)]] = P(Start ~ axiom.rep(1) ~ End).map(_.toList)

  /** formula: Parses a dL formula via [[DLParser.formula]]. */
  private def formula[$: P]: P[Formula] = DLParser.formula
}
