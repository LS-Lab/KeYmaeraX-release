/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, Position}
import edu.cmu.cs.ls.keymaerax.core._

/**
  * Tactics for manipulating box/diamond properties about hybrid programs.
  *
  * @author Nathan Fulton
  */
object HybridProgramTactics {
  import TacticFactory._
  import Augmentors._

  /**
    * Decomposes a question of the form {a ++ b ++ c}; plant into a;plant , b;plant , c;plant
    */
  def decomposeController = "decomposeController" by ((pos: Position, s:Sequent) => {
    s(pos) match {
      case Box(Compose(ctrl, plant), phi) => decomposeChoices(ctrl, pos)
      case Diamond(_,_) => throw new Exception("Diamond not spported by decomposeController")
      case _ => ???
    }
  })

  private def decomposeChoices(ctrl: Program, pos: Position): BelleExpr = ctrl match {
    case Compose(l,r) => TactixLibrary.composeb(pos) & decomposeChoices(l, pos)
    case Choice(l,r) => {
      TactixLibrary.choiceb(pos) & TactixLibrary.andR(1) <(
        decomposeChoices(l, pos)
        ,
        decomposeChoices(r, pos)
      )
    }
  }

}
