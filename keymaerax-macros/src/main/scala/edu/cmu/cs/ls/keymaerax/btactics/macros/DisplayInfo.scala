/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.macros

// TODO Convert into enum after updating to Scala 3
/** Where to display an axiom/rule/tactic in the user interface. */
sealed trait DisplayLevel

/** Don't display in UI at all. */
case object DisplayLevelInternal extends DisplayLevel

/** Only display when searching for it in browse. */
case object DisplayLevelBrowse extends DisplayLevel

/** Like [[DisplayLevelInternal]] but also display in top level menu. */
case object DisplayLevelMenu extends DisplayLevel

/** Like [[DisplayLevelMenu]] but also pop up in context menu. */
case object DisplayLevelAll extends DisplayLevel

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

/** UI display information on how to render an axiom, rule, or tactic application */
sealed trait DisplayInfo {

  /** Short name used in the UI. May contain whitespace, unicode, HTML. */
  def name: String

  /** ASCII-only version of [[name]]. */
  def nameAscii: String
  require(nameAscii.codePoints().allMatch(c => 0x20 <= c && c <= 0x7e), "nameAscii must only be printable ASCII")

  /** Descriptive long name used in some menus in the user interface. Should be a short, grammatical English phrase. */
  def nameLong: String

  /** Where to display an axiom/rule/tactic in the user interface. */
  def level: DisplayLevel
}

/** The bare minimum to classify as a [[DisplayInfo]]. */
case class SimpleDisplayInfo(name: String, nameAscii: String, nameLong: String, level: DisplayLevel) extends DisplayInfo

/** Render a rule with a name as a conclusion and list of premises. */
case class RuleDisplayInfo(
    name: String,
    nameAscii: String,
    nameLong: String,
    level: DisplayLevel,
    conclusion: DisplaySequent,
    premises: List[DisplaySequent],
    inputGenerator: String,
) extends DisplayInfo

/**
 * Render a tactic either top-level as rule with a name as a conclusion and list of premises, or in context with a
 * different conclusion and list of premises.
 */
case class TacticDisplayInfo(
    name: String,
    nameAscii: String,
    nameLong: String,
    level: DisplayLevel,
    conclusion: DisplaySequent,
    premises: List[DisplaySequent],
    ctxConclusion: DisplaySequent,
    ctxPremises: List[DisplaySequent],
    inputGenerator: String,
) extends DisplayInfo

/** Render an axiom with a name as a UI string for the formula. */
case class AxiomDisplayInfo(name: String, nameAscii: String, nameLong: String, level: DisplayLevel, formula: String)
    extends DisplayInfo

/** Render an axiom that has a name and a UI string formula but needs a list of inputs filled in first. */
case class InputAxiomDisplayInfo(
    name: String,
    nameAscii: String,
    nameLong: String,
    level: DisplayLevel,
    formula: String,
    input: List[ArgInfo],
) extends DisplayInfo
