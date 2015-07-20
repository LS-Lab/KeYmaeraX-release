import edu.cmu.cs.ls.keymaerax.core.{And, Sequent}
import edu.cmu.cs.ls.keymaerax.tactics.Position
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{Tactic, PositionTactic}

//package edu.cmu.cs.ls.keymaerax.tactics
//
//import edu.cmu.cs.ls.keymaerax.core._
//import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{LabelBranch, ConstructionTactic, Tactic, PositionTactic}
//import edu.cmu.cs.ls.keymaerax.tools.Tool
//
/**
 * Created by nfulton on 7/16/15.
 */
object NLib {
  def canonizeConjunction : PositionTactic = new PositionTactic("Canonize Conjunction") {
    override def applies(s: Sequent, p: Position): Boolean = S(p) match {
      case And(_,_) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = ???
  }
//  def SequentToImplication : Tactic = ???
}
