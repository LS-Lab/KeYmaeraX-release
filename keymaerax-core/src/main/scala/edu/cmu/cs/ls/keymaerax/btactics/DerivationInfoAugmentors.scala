package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{AppliedBuiltinTwoPositionTactic, AppliedPositionTactic, BelleExpr, DependentPositionTactic, NamedBelleExpr}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.macros._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.HashMap

object DerivationInfoAugmentors {
  def byPosition (name: String, expr: (Position, Sequent) => BelleExpr): DependentPositionTactic = name by expr

  /** Locally embed single string names into SimpleDisplayInfo. */
  implicit def displayInfo(name: String): SimpleDisplayInfo = {
    SimpleDisplayInfo(name, name)
  }

  /** Locally embed pair string names into SimpleDisplayInfo distinguishing UI name from plain ASCII name. */
  implicit def displayInfo(pair: (String, String)): SimpleDisplayInfo = SimpleDisplayInfo(pair._1, pair._2)

  /** Locally embed pair of list of strings into SequentDisplayInfo. */
  implicit def sequentDisplay(succAcc: (List[String], List[String])): SequentDisplay = {
    SequentDisplay(succAcc._1, succAcc._2)
  }

  /** Locally embed pair of list of strings with boolean into SequentDisplayInfo with info on whether closing. */
  implicit def sequentDisplay(succAccClosed: (List[String], List[String], Boolean)): SequentDisplay = {
    SequentDisplay(succAccClosed._1, succAccClosed._2, succAccClosed._3)
  }

  implicit class DerivationInfoAugmentor(val di: DerivationInfo) {
    def belleExpr: Any = di match {
      // useAt will just ask a ProvableInfo for its provable
      case pi: ProvableInfo => di.codeName by ((pos:Position, seq:Sequent) => HilbertCalculus.useAt(pi) (pos))
      case ti: TacticInfo => ti.theExpr (())
    }

  }

  implicit class ProvableInfoAugmentor(val pi: ProvableInfo) {
    def provable: ProvableSig = {
      pi match {
        case cai: CoreAxiomInfo => ProvableSig.axioms(cai.canonicalName)
        case cari: AxiomaticRuleInfo => ProvableSig.rules(cari.canonicalName)
        case dai: DerivedAxiomInfo => Ax.derivedAxiomOrRule(dai.canonicalName)
        case dari: DerivedRuleInfo => Ax.derivedAxiomOrRule(dari.canonicalName)
      }
    }

    def formula: Formula = {
      pi match {
        case dai: DerivedAxiomInfo => Ax.derivedAxiomOrRule(dai.canonicalName).conclusion.succ.head
        case cai: CoreAxiomInfo =>
          ProvableSig.axiom.get(pi.canonicalName) match {
            case Some(fml) => fml
            case None => throw new AxiomNotFoundException("No formula for core axiom " + pi.canonicalName)
          }
      }
    }
  }

  implicit class AxiomInfoAugmentor(val ai: AxiomInfo) {
    def key: PosInExpr = PosInExpr(ai.theKey)
    def recursor: List[PosInExpr] = ai.theRecursor.map(PosInExpr(_))
  }

  implicit class StorableInfoAugmentor(val si: StorableInfo) {
    def lemma: Lemma = si.theLemma.asInstanceOf[Lemma]
  }
}
