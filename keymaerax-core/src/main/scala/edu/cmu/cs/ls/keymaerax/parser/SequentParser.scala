/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent}

/** Parses sequents of the form ```ante_1, ante_2, ..., ante_n ==> succ_1, ..., succ_n```. */
object SequentParser {

  // splits at , except inside {}, (), [], but gets it wrong with nested parentheses, e.g., f(g(),h())
  private val FML_SPLITTER = ",(?!(([^{]*})|([^(]*\\))|([^\\[]*\\])))"

  /** Converts to a list of formulas (formulas comma-separated in input). */
  def parseFormulaList(s: String): List[Formula] = {
    val (fmls, unparseable) = s
      .split(FML_SPLITTER)
      .foldLeft[(List[Formula], String)](List.empty, "")({ case ((fmls, acc), next) =>
        val fmlCandidate = acc + (if (acc.nonEmpty) "," else "") + next
        try { (fmls :+ Parser.parser.formulaParser(fmlCandidate), "") }
        catch { case _: ParseException => (fmls, fmlCandidate) }
      })
    if (unparseable.nonEmpty) List(Parser.parser.formulaParser(unparseable)) // @note will throw ParseException
    else fmls
  }

  // s.split(FML_SPLITTER).filter(_.nonEmpty).map(Parser.parser.formulaParser).toList

  /** Parses `s` as a sequent. */
  def parseSequent(s: String): Sequent = {
    val turnStileIdx = s.indexOf(TURNSTILE.img)
    if (turnStileIdx >= 0) {
      val (ante, succ) = s.splitAt(turnStileIdx)
      Sequent(
        parseFormulaList(ante.trim).toIndexedSeq,
        parseFormulaList(succ.stripPrefix(TURNSTILE.img).trim).toIndexedSeq,
      )
    } else throw new IllegalArgumentException("String " + s + " is not a sequent (must contain turnstile ==>)")
  }

}
