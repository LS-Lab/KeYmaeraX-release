/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent}

/** Parses sequents of the form ```ante_1, ante_2, ..., ante_n ==> succ_1, ..., succ_n```. */
object SequentParser {

  private val FML_SPLITTER = ",(?!(([^{]*})|([^(]*\\))|([^\\[]*\\])))" // splits at , except inside {}, (), []
  /** Converts to a list of formulas (formulas comma-separated in input). */
  def parseFormulaList(s: String): List[Formula] =
    s.split(FML_SPLITTER).filter(_.nonEmpty).map(Parser.parser.formulaParser).toList

  /** Parses `s` as a sequent. */
  def parseSequent(s: String): Sequent = {
    val turnStileIdx = s.indexOf(TURNSTILE.img)
    if (turnStileIdx >= 0) {
      val (ante, succ) = s.splitAt(turnStileIdx)
      Sequent(
        parseFormulaList(ante.trim).toIndexedSeq,
        parseFormulaList(succ.stripPrefix(TURNSTILE.img).trim).toIndexedSeq)
    } else throw new IllegalArgumentException("String " + s + " is not a sequent (must contain turnstile ==>)")
  }

}
