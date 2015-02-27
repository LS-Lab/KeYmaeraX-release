package edu.cmu.cs.ls.keymaera.tacticsinterface

import edu.cmu.cs.ls.keymaera.core.Formula
import edu.cmu.cs.ls.keymaera.tactics.{Tactics, TacticLibrary}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{PositionTactic, Tactic}

/**
 * These are tactics which are exposed to the tactics interface.
 *
 * All methods which take arguments must take a single argument of type Option[Formula].
 * For example, debugT isn't currently supported.
 *
 * Created by nfulton on 2/26/15.
 */
object ExposedTacticsLibrary {
  // Utility Tactics
  def NilT : Tactic = Tactics.NilT

  // The Sequent Calculus
  def cutT(inv : Option[Formula]) : Tactic = TacticLibrary.cutT(inv)
  def AxiomCloseT : Tactic = TacticLibrary.AxiomCloseT
}
