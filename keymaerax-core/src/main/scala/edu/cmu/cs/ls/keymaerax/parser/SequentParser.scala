/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent}

/** Parses sequents of the form ```ante_1, ante_2, ..., ante_n ==> succ_1, ..., succ_n```. */
object SequentParser {

  /** Splits a formula at comma (which may split prematurely inside ODEs, interpreted functions/predicates).
    * If a split failed to parse, merge it with the next formula and try again because it might have been split
    * incorrectly e.g. max(a,b) would be incorrectly split */
  private def smartFmlSplit(acc: String,ls: List[String]): List[Formula] = ls match {
    case Nil =>
      if (acc != "") List(Parser.parser.formulaParser(acc))
      else Nil
    case l::lss =>
      if (l == "") smartFmlSplit(acc,lss)
      else {
        try {
          Parser.parser.formulaParser(acc + l) :: smartFmlSplit("", lss)
        } catch {
          case _: ParseException => smartFmlSplit(acc + l + ",", lss)
        }
      }
  }

  /** Parses `s` as a sequent. */
  def parseSequent(s: String): Sequent = {
    val splitter = ",(?![^{]*})"
    val turnStileIdx = s.indexOf(TURNSTILE.img)
    val ante::succ::Nil =
      if (turnStileIdx >= 0) {
        val (ante, succ) = s.splitAt(turnStileIdx)
        List(
          ante.trim.split(splitter).filter(_.nonEmpty).toList,
          succ.trim.stripPrefix(TURNSTILE.img).trim.split(splitter).filter(_.nonEmpty).toList)
      } else throw new IllegalArgumentException("String " + s + " is not a sequent (must contain turnstile ==>)")
    Sequent(
      smartFmlSplit("",ante).toIndexedSeq,
      smartFmlSplit("",succ).toIndexedSeq
    )
  }

}
