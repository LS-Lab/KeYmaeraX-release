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

    initTactic("dl.and-left", "TacticLibrary.AndLeftT", TacticKind.PositionTactic, TacticLibrary.AndLeftT)
    initTactic("dl.and-right", "TacticLibrary.AndRightT", TacticKind.PositionTactic, TacticLibrary.AndRightT)
    initTactic("dl.or-left", "TacticLibrary.OrLeftT", TacticKind.PositionTactic, TacticLibrary.OrLeftT)
    initTactic("dl.or-right", "TacticLibrary.OrRightT", TacticKind.PositionTactic, TacticLibrary.OrRightT)
    initTactic("dl.imply-left", "TacticLibrary.ImplyLeftT", TacticKind.PositionTactic, TacticLibrary.ImplyLeftT)
    initTactic("dl.imply-right", "TacticLibrary.ImplyRightT", TacticKind.PositionTactic, TacticLibrary.ImplyRightT)
    initTactic("dl.equiv-left", "TacticLibrary.EquivLeftT", TacticKind.PositionTactic, TacticLibrary.EquivLeftT)
    initTactic("dl.equiv-right", "TacticLibrary.EquivRightT", TacticKind.PositionTactic, TacticLibrary.EquivRightT)
    initTactic("dl.not-left", "TacticLibrary.NotLeftT", TacticKind.PositionTactic, TacticLibrary.NotLeftT)
    initTactic("dl.not-right", "TacticLibrary.NotRightT", TacticKind.PositionTactic, TacticLibrary.NotRightT)
    initTactic("dl.hide", "TacticLibrary.hideT", TacticKind.PositionTactic, TacticLibrary.hideT)
    initTactic("dl.cohide", "TacticLibrary.cohideT", TacticKind.PositionTactic, TacticLibrary.cohideT)
    initTactic("dl.close-true", "TacticLibrary.CloseTrueT", TacticKind.PositionTactic, TacticLibrary.CloseTrueT)
    initTactic("dl.close-false", "TacticLibrary.CloseFalseT", TacticKind.PositionTactic, TacticLibrary.CloseFalseT)
    initTactic("dl.skolemize", "TacticLibrary.skolemizeT", TacticKind.PositionTactic, TacticLibrary.skolemizeT)

    initTactic("dl.box-assign", "TacticLibrary.boxAssignT", TacticKind.PositionTactic, TacticLibrary.boxAssignT)
    initTactic("dl.box-choice", "TacticLibrary.boxChoiceT", TacticKind.PositionTactic, TacticLibrary.boxChoiceT)
    initTactic("dl.box-induction", "TacticLibrary.boxInductionT", TacticKind.PositionTactic, TacticLibrary.boxInductionT)
    initTactic("dl.box-ndetassign", "TacticLibrary.boxNDetAssignT", TacticKind.PositionTactic, TacticLibrary.boxNDetAssign)
    initTactic("dl.box-seq", "TacticLibrary.boxSeqT", TacticKind.PositionTactic, TacticLibrary.boxSeqT)
    initTactic("dl.box-test", "TacticLibrary.boxTestT", TacticKind.PositionTactic, TacticLibrary.boxTestT)
  }

  private def initTactic(name : String, className : String, kind : TacticKind.Value, /* Remove when reflection works */ tInst : AnyRef) = {
    val tactic = db.getTacticByName(name) match {
      case Some(t) => t
      case None =>
        val id = db.createTactic(name, className, kind);
        db.getTactic(id) match {
          case Some(t) => t
          case None => throw new IllegalStateException("Unable to insert tactic " + name + " into the database")
        }
    }
    // TODO reflection
    // TODO get rid of singletons
    (tactic.kind, tInst) match {
      case (TacticKind.Tactic, t : Tactic) => KeYmaeraInterface.addTactic(tactic.tacticId, t)
      case (TacticKind.PositionTactic, t : PositionTactic) => KeYmaeraInterface.addPositionTactic(tactic.tacticId, t)
      case _ => throw new IllegalArgumentException("Tactic kind " + tactic.kind.toString() + " and type " + tInst.getClass.toString + " do not match")
    }
  }
}
