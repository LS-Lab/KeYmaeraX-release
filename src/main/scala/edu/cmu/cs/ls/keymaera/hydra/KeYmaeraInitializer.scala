package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{Tactic, PositionTactic}

/**
 * Created by smitsch on 11/10/14.
 */
class KeYmaeraInitializer(db : DBAbstraction) {
  def initialize() {
    initTactic("keymaera.default", "TacticLibrary.default", TacticKind.Tactic, TacticLibrary.default)
    initTactic("keymaera.step", "TacticLibrary.step", TacticKind.PositionTactic, TacticLibrary.step)

    // TODO add all step tactics
    initTactic("keymaera.imply-left", "TacticLibrary.ImplyLeftT", TacticKind.PositionTactic, TacticLibrary.ImplyLeftT)
    initTactic("keymaera.and-left", "TacticLibrary.AndLeftT", TacticKind.PositionTactic, TacticLibrary.AndLeftT)
  }

  private def initTactic(name : String, className : String, kind : TacticKind.Value, /* Remove when reflection works */ t : AnyRef) = {
    val tactic = db.getTacticByName(name) match {
      case Some(t) => t
      case None => val id = db.createTactic(name, className, kind); db.getTactic(id)
    }
    // TODO reflection
    // TODO get rid of singletons
    (tactic.kind, t) match {
      case (TacticKind.Tactic, t : Tactic) => KeYmaeraInterface.addTactic(tactic.tacticId, t)
      case (TacticKind.PositionTactic, t : PositionTactic) => KeYmaeraInterface.addPositionTactic(tactic.tacticId, t)
      case _ => throw new IllegalArgumentException("Tactic kind " + tactic.kind.toString() + " and type " + t.getClass.toString + " do not match")
    }
  }
}
