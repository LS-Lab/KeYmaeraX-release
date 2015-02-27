package edu.cmu.cs.ls.keymaera.tacticsinterface

import edu.cmu.cs.ls.keymaera.tactics.{Tactics, TacticLibrary}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{PositionTactic, Tactic}

/**
 * These are tactics which are exposed to the tactics interface.
 * Created by nfulton on 2/26/15.
 */
object ExposedTacticsLibrary {
  // Utility Tactics
  def NilT : Tactic = Tactics.NilT

  // sections go here...
  def AxiomCloseT : Tactic = TacticLibrary.AxiomCloseT
}
