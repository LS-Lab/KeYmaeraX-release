/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

// TODO Convert into enum after updating to Scala 3
/** Where to display an axiom/rule/tactic in the user interface. */
sealed trait DisplayLevel

object DisplayLevel {

  /** Don't display in UI at all. */
  case object Internal extends DisplayLevel

  /** Only display when searching for it in browse. */
  case object Browse extends DisplayLevel

  /** Like [[Internal]] but also display in top level menu. */
  case object Menu extends DisplayLevel

  /** Like [[Menu]] but also pop up in context menu. */
  case object All extends DisplayLevel
}
