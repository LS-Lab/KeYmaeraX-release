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
 * @param isClosed
 *   true to indicate that this sequent is closed so (*) star.
 */
case class SequentDisplay(ante: List[String], succ: List[String], isClosed: Boolean = false)

/** UI display information on how to render an axiom, rule, or tactic application */
sealed trait DisplayInfo {

  /** Short name used in the UI. May contain whitespace, unicode, HTML. */
  def name: String

  /** ASCII-only version of [[name]]. */
  def nameAscii: String
  require(nameAscii.codePoints().allMatch(c => 0x20 <= c && c <= 0x7e), "nameAscii must only be printable ASCII")

  /** Descriptive long name used in some menus in the user interface. Should be a short, grammatical English phrase. */
  def nameLong: String
}

/** The bare minimum to classify as a [[DisplayInfo]]. */
case class SimpleDisplayInfo(name: String, nameAscii: String, nameLong: String) extends DisplayInfo

/** Render a rule with a name as a conclusion and list of premises. */
case class RuleDisplayInfo(
    name: String,
    nameAscii: String,
    nameLong: String,
    conclusion: SequentDisplay,
    premises: List[SequentDisplay],
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
    conclusion: SequentDisplay,
    premises: List[SequentDisplay],
    ctxConclusion: SequentDisplay,
    ctxPremises: List[SequentDisplay],
    inputGenerator: String,
) extends DisplayInfo

/** Render an axiom with a name as a UI string for the formula. */
case class AxiomDisplayInfo(name: String, nameAscii: String, nameLong: String, displayFormula: String)
    extends DisplayInfo

/** Render an axiom that has a name and a UI string formula but needs a list of inputs filled in first. */
case class InputAxiomDisplayInfo(
    name: String,
    nameAscii: String,
    nameLong: String,
    displayFormula: String,
    input: List[ArgInfo],
) extends DisplayInfo
