/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

/**
 * Render a sequent as a list of antecedent UI strings and a list of succedent UI strings.
 *
 * @param isClosed
 *   true to indicate that this sequent is closed so (*) star.
 */
case class DisplaySequent(ante: List[String], succ: List[String], isClosed: Boolean = false)

case object DisplaySequent {

  /**
   * Parse a [[DisplaySequent]] from a string. The sequent can either be the string `"*"`, indicating a branch being
   * closed, or `"<antes> |- <succs>"`, or just `"<succs>"`. Both `<antes>` and `<succs>` are a comma-separated list of
   * one or more formulas.
   */
  def parse(sequent: String): DisplaySequent = {
    if (sequent.trim == "*") return DisplaySequent(Nil, Nil, isClosed = true)

    sequent.split("\\|-").toList match {
      case List(succ) =>
        val succs = if (succ.trim.isEmpty) Nil else succ.split(",").map(_.trim).toList
        require(succs.forall(_.nonEmpty), "succedents must contain non-whitespace characters")
        DisplaySequent(Nil, succs)

      case List(ante, succ) =>
        val antes = if (ante.trim.isEmpty) Nil else ante.split(",").map(_.trim).toList
        val succs = if (succ.trim.isEmpty) Nil else succ.split(",").map(_.trim).toList
        require(antes.forall(_.nonEmpty), "antecedents must contain non-whitespace characters")
        require(succs.forall(_.nonEmpty), "succedents must contain non-whitespace characters")
        DisplaySequent(antes, succs)

      case _ => throw new IllegalArgumentException("sequent must contain at most one |-")
    }
  }

  /** Parse a list of [[DisplaySequent]]s separated by `;;`. */
  def parseMany(sequents: String): List[DisplaySequent] = {
    if (sequents.trim.isEmpty) return Nil
    sequents.split(";;").map(parse).toList
  }
}
