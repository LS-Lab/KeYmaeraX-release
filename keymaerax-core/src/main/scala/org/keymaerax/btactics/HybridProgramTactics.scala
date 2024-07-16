/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{BelleExpr, DependentPositionTactic}
import org.keymaerax.btactics.macros.Tactic
import org.keymaerax.core._
import org.keymaerax.infrastruct.Position

import scala.annotation.nowarn
import scala.reflect.runtime.universe

/**
 * Implementation: Tactics for manipulating box/diamond properties about hybrid programs.
 *
 * @author
 *   Nathan Fulton
 */
private object HybridProgramTactics extends TacticProvider {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) =
    (HybridProgramTactics.getClass, universe.typeOf[HybridProgramTactics.type])

  import TacticFactory._
  import org.keymaerax.infrastruct.Augmentors._

  /** Decomposes a question of the form `{a ++ b ++ c}; plant` into `a;plant`, `b;plant`, `c;plant`. */
  @Tactic(
    name = "decomposeController",
    displayName = Some("Decompose Controller"),
    displayPremises = "[a][c]P; ...; [b][c]P",
    displayConclusion = "[{a ++ ... ++ b}; c] P",
  )
  val decomposeController: DependentPositionTactic = anon((pos: Position, s: Sequent) => {
    s(pos) match {
      case Box(Compose(ctrl, plant), phi) => decomposeChoices(ctrl, pos)
      case Diamond(_, _) => throw new Exception("Diamond not spported by decomposeController")
      case _ => ???
    }
  })

  @nowarn("msg=match may not be exhaustive")
  private def decomposeChoices(ctrl: Program, pos: Position): BelleExpr = ctrl match {
    case Compose(l, r) => TactixLibrary.composeb(pos) & decomposeChoices(l, pos)
    case Choice(l, r) => {
      TactixLibrary.choiceb(pos) & TactixLibrary.andR(1) < (decomposeChoices(l, pos), decomposeChoices(r, pos))
    }
  }

}
