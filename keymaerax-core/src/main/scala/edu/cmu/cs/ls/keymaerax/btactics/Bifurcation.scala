package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, IllFormedTacticApplicationException, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.core.{Formula, ODESystem, Sequent}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.Position

/** Implements a bifurcation-based proof search technique for the dynamic logic of ODEs. */
object Bifurcation {
  type BifurcationTool = ODESystem => Set[Formula]

  /** Identifies a bifurcation of a system of differential equations; each formula describes one "side" of the bifurcation.
    * @TODO  */
  val bifurcationTool : BifurcationTool = (ode : ODESystem) => {
    Set()
  }

  /** Performs a sequence of cuts and executes `onCut` on each of the new branches. */
  private def nestedCuts(onCut : BelleExpr, cuts : Seq[Formula]) : BelleExpr =
    cuts match {
      case next :: tail => {
        TactixLibrary.cut(next) <(
          onCut
          ,
          nestedCuts(onCut, tail)
        )
      }
      case Nil => onCut
    }

  /** Splits the proof using the [[bifurcationTool]] and does nothing on each of the branches. */
  val biSplit = "biSplit" by ((pos: Position, seq: Sequent) => {
    val odes = seq.sub(pos) match {
      case s : ODESystem => s
      case Some(e) => throw new TacticInapplicableFailure("biSplit only applicable to ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    nestedCuts(TactixLibrary.nil, bifurcationTool(odes).toSeq)
  })

  /** Splits the proof using the [[bifurcationTool]] and runs [[TactixLibrary.ODE]] on each of the remaining branches. */
  val biSplitAuto = "biSplitAuto" by ((pos: Position, seq: Sequent) => {
    val odes = seq.sub(pos) match {
      case s : ODESystem => s
      case Some(e) => throw new TacticInapplicableFailure("biSplitAuto only applicable to ODEs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }

    nestedCuts(TactixLibrary.ODE(pos), bifurcationTool(odes).toSeq)
  })
}
