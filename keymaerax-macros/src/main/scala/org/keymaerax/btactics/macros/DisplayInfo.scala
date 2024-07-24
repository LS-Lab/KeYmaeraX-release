/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

case class DisplayNames(
    /** Short name used in the UI. May contain whitespace, unicode, HTML. */
    name: String,

    /** ASCII-only version of [[name]]. */
    nameAscii: String,

    /**
     * Descriptive long name used in some menus in the user interface. Should be a short, grammatical English phrase.
     */
    nameLong: String,
) {
  require(!name.isBlank, "name must not be blank")
  require(!nameAscii.isBlank, "name must not be blank")
  require(!nameLong.isBlank, "name must not be blank")
  require(nameAscii.codePoints().allMatch(c => 0x20 <= c && c <= 0x7e), "nameAscii must only be printable ASCII")
}

object DisplayNames {

  /** Create a [[DisplayNames]], checking for possible human mistakes in the process. */
  def createWithChecks(
      name: String,
      nameAscii: Option[String] = None,
      nameLong: Option[String] = None,
  ): DisplayNames = {
    require(!nameAscii.contains(name), "redundant nameAscii")
    require(!nameLong.contains(name), "redundant nameLong")
    DisplayNames(name = name, nameAscii = nameAscii.getOrElse(name), nameLong = nameLong.getOrElse(name))
  }

  def singleName(name: String): DisplayNames = DisplayNames(name = name, nameAscii = name, nameLong = name)
}

/** UI display information on how to render an axiom, rule, or tactic application */
sealed trait DisplayInfo {
  val names: DisplayNames

  /** Where to display an axiom/rule/tactic in the user interface. */
  val level: DisplayLevel
}

/** The bare minimum to classify as a [[DisplayInfo]]. */
case class SimpleDisplayInfo(names: DisplayNames, level: DisplayLevel) extends DisplayInfo

/** Render a rule with a name as a conclusion and list of premises. */
case class RuleDisplayInfo(
    names: DisplayNames,
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
    names: DisplayNames,
    level: DisplayLevel,
    conclusion: DisplaySequent,
    premises: List[DisplaySequent],
    ctxConclusion: DisplaySequent,
    ctxPremises: List[DisplaySequent],
    inputGenerator: Option[String],
) extends DisplayInfo

/** Render an axiom with a name as a UI string for the formula. */
case class AxiomDisplayInfo(names: DisplayNames, level: DisplayLevel, formula: String) extends DisplayInfo

/** Render an axiom that has a name and a UI string formula but needs a list of inputs filled in first. */
case class InputAxiomDisplayInfo(names: DisplayNames, level: DisplayLevel, formula: String, input: List[ArgInfo])
    extends DisplayInfo
