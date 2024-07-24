/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

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
    inputGenerator: Option[String],
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
    inputGenerator: Option[String],
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
