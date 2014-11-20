package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface
import edu.cmu.cs.ls.keymaera.core.Formula
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{Tactic, PositionTactic}

/**
 * Initializes KeYmaera and its database.
 * @param db The database access.
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

    initInputPositionTactic("dl.induction", "TacticLibrary.inductionT", TacticKind.PositionTactic, TacticLibrary.inductionT _)
  }

  private def initTactic(name : String, className : String, kind : TacticKind.Value, t : Tactic) = {
    val tactic = getOrCreateTactic(name, className, kind)
    KeYmaeraInterface.addTactic(tactic.tacticId, t)
  }
  private def initTactic(name : String, className : String, kind : TacticKind.Value, t : PositionTactic) = {
    val tactic = getOrCreateTactic(name, className, kind)
    KeYmaeraInterface.addPositionTactic(tactic.tacticId, t)
  }
  private def initInputTactic(name : String, className : String, kind : TacticKind.Value,
                         tGen : (Option[Formula]) => Tactic) = {
    val tactic = getOrCreateTactic(name, className, kind)
    KeYmaeraInterface.addTactic(tactic.tacticId, tGen)
  }
  private def initInputPositionTactic(name : String, className : String, kind : TacticKind.Value,
                         tGen : (Option[Formula]) => PositionTactic) = {
    val tactic = getOrCreateTactic(name, className, kind)
    KeYmaeraInterface.addPositionTactic(tactic.tacticId, tGen)
  }

  private def getOrCreateTactic(name: String, className: String, kind: TacticKind.Value): TacticPOJO = {
    db.getTacticByName(name) match {
      case Some(t) => t
      case None =>
        val id = db.createTactic(name, className, kind)
        db.getTactic(id) match {
          case Some(t) => t
          case None => throw new IllegalStateException("Unable to insert tactic " + name + " into the database")
        }
    }
  }
}
