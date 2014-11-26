package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface
import edu.cmu.cs.ls.keymaera.core.Formula
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{Tactic, PositionTactic}

import scala.reflect.runtime.universe.TypeTag

/**
 * Initializes KeYmaera and its database.
 * @param db The database access.
 */
class KeYmaeraInitializer(db : DBAbstraction) {
  def initialize() {
    initTactic("keymaera.default", "TacticLibrary.default", TacticKind.Tactic, TacticLibrary.default)
    initTactic("keymaera.defaultNoArith", "TacticLibrary.defaultNoArith", TacticKind.Tactic, TacticLibrary.defaultNoArith)
    initTactic("keymaera.step", "TacticLibrary.step", TacticKind.PositionTactic, TacticLibrary.step)
    initTactic("keymaera.propositional", "TacticLibrary.propositional", TacticKind.Tactic, TacticLibrary.propositional)
    initTactic("keymaera.arithmetic", "TacticLibrary.arithmeticT", TacticKind.Tactic, TacticLibrary.arithmeticT)
    initTactic("dl.axiomclose", "TacticLibrary.AxiomCloseT", TacticKind.Tactic, TacticLibrary.AxiomCloseT)

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
    initTactic("dl.close-true", "TacticLibrary.CloseTrueT", TacticKind.PositionTactic, TacticLibrary.CloseTrueT)
    initTactic("dl.close-false", "TacticLibrary.CloseFalseT", TacticKind.PositionTactic, TacticLibrary.CloseFalseT)
    initTactic("dl.close", "TacticLibrary.CloseT", TacticKind.PositionTactic, TacticLibrary.closeT)
    initTactic("dl.skolemize", "TacticLibrary.skolemizeT", TacticKind.PositionTactic, TacticLibrary.skolemizeT)
    initTactic("dl.abstraction", "TacticLibrary.abstractionT", TacticKind.PositionTactic, TacticLibrary.abstractionT)

    initTactic("dl.box-assign", "TacticLibrary.boxAssignT", TacticKind.PositionTactic, TacticLibrary.boxAssignT)
    initTactic("dl.box-choice", "TacticLibrary.boxChoiceT", TacticKind.PositionTactic, TacticLibrary.boxChoiceT)
    initTactic("dl.box-induction", "TacticLibrary.boxInductionT", TacticKind.PositionTactic, TacticLibrary.boxInductionT)
    initTactic("dl.box-ndetassign", "TacticLibrary.boxNDetAssignT", TacticKind.PositionTactic, TacticLibrary.boxNDetAssign)
    initTactic("dl.box-seq", "TacticLibrary.boxSeqT", TacticKind.PositionTactic, TacticLibrary.boxSeqT)
    initTactic("dl.box-test", "TacticLibrary.boxTestT", TacticKind.PositionTactic, TacticLibrary.boxTestT)

    initInputTactic[Option[Formula]]("dl.cut", "TacticLibrary.cutT", TacticKind.InputTactic, TacticLibrary.cutT)
    initInputTactic("dl.qe", "TacticLibrary.quantifierEliminationT", TacticKind.InputTactic, TacticLibrary.quantifierEliminationT)
    initInputTactic("dl.equalityRewriting", "TacticLibrary.equalityRewriting", TacticKind.InputTactic, TacticLibrary.equalityRewriting _)
//    initInputTactic("dl.axiom", "TacticLibrary.axiomT", TacticKind.InputTactic, TacticLibrary.axiomT)
    initInputPositionTactic("dl.induction", "TacticLibrary.inductionT", TacticKind.PositionTactic, TacticLibrary.inductionT)
    initInputPositionTactic("dl.equalityRewritingLeft", "TacticLibrary.equalityRewritingLeft", TacticKind.InputPositionTactic, TacticLibrary.equalityRewritingLeft)
    initInputPositionTactic("dl.equalityRewritingRight", "TacticLibrary.equalityRewritingRight", TacticKind.InputPositionTactic, TacticLibrary.equalityRewritingRight)
//    initInputPositionTactic[Variable,Expr]("dl.instantiate", "TacticLibrary.instantiateT", TacticKind.PositionTactic, TacticLibrary.instantiateT)
  }

  private def initTactic(name : String, className : String, kind : TacticKind.Value, t : Tactic) = {
    val tactic = getOrCreateTactic(name, className, kind)
    KeYmaeraInterface.addTactic(tactic.tacticId, t)
  }
  private def initTactic(name : String, className : String, kind : TacticKind.Value, t : PositionTactic) = {
    val tactic = getOrCreateTactic(name, className, kind)
    KeYmaeraInterface.addPositionTactic(tactic.tacticId, t)
  }
  private def initInputTactic[T](name : String, className : String, kind : TacticKind.Value,
                         tGen : T => Tactic)(implicit m : TypeTag[T]) = {
    val tactic = getOrCreateTactic(name, className, kind)
    KeYmaeraInterface.addTactic(tactic.tacticId, tGen)
  }
  private def initInputTactic[T,U,V](name : String, className : String, kind : TacticKind.Value,
                                 tGen : (T,U,V) => Tactic)(implicit m : TypeTag[T], n : TypeTag[U], o : TypeTag[V]) = {
    val tactic = getOrCreateTactic(name, className, kind)
    KeYmaeraInterface.addTactic(tactic.tacticId, tGen)
  }
  private def initInputPositionTactic[T](name : String, className : String, kind : TacticKind.Value,
                         tGen : T => PositionTactic)(implicit m : TypeTag[T]) = {
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
