/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Formula
import fastparse._
import JavaWhitespace._
import edu.cmu.cs.ls.keymaerax.parser.DLParser.parseException

import scala.collection.immutable._

/**
  * Parse an axiom string to a list of named formulas that are to be used as axioms in a theory.
  * @author Andre Platzer
  * @see [[KeYmaeraXAxiomParser]]
  */
object DLAxiomParser extends (String => List[(String,Formula)]) {
  import DLParser.string

  /**
    * Parse an axiom string into a list of named axioms.
    * @param input The contents of the axiom file.
    * @return A list of named axioms occurring in the string.
    */
  def apply(input: String) : List[(String,Formula)] = axiomParser(input)


  private val axiomParser: String => List[(String,Formula)] = input => fastparse.parse(input, axiomList(_)) match {
    case Parsed.Success(value, index) => value
    case f: Parsed.Failure => throw parseException(f).inContext("<AxiomBase>"/*input*/)
  }


  /** axiom: Parses a dL axiom. */
  def axiom[_: P]: P[(String,Formula)] = P( "Axiom" ~ string ~ formula ~ "End.")

  /** axiom: Parses a dL axiom. */
  def axiomList[_: P]: P[List[(String,Formula)]] = P( Start ~ axiom.rep(1) ~ End ).map(_.toList)

  /** formula: Parses a dL formula via [[DLParser.formula]]. */
  private def formula[_: P]: P[Formula] = DLParser.formula
}
