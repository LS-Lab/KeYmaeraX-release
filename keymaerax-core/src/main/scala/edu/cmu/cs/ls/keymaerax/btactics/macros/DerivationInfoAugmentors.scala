package edu.cmu.cs.ls.keymaerax.btactics.macros

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma._
import edu.cmu.cs.ls.keymaerax.pt._

import scala.language.implicitConversions

object DerivationInfoAugmentors {
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
    def by(name: String, t: (Position, Sequent) => BelleExpr): DependentPositionTactic = new DependentPositionTactic(name) {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = {
          require(pos.isIndexDefined(sequent), "Cannot apply at undefined position " + pos + " in sequent " + sequent)
          t(pos, sequent)
        }
      }
    }

    def belleExpr: Any = di match {
      // useAt will just ask a ProvableInfo for its provable
      case pi: ProvableInfo =>  HilbertCalculus.useAt(pi)
      case ti: TacticInfo => ti.theExpr (())
    }

  }

  implicit class ProvableInfoAugmentor(val pi: ProvableInfo) {
    val derivedAxiomDB: LemmaDB = LemmaDBFactory.lemmaDB
    def derivedAxiomOrRule(name: String): ProvableSig = {
      val lemmaName = DerivationInfo(name) match {
        case si: StorableInfo => si.storedName
        case _ => throw new IllegalArgumentException(s"Axiom or rule $name is not storable")
      }
      require(derivedAxiomDB.contains(lemmaName), "Lemma " + lemmaName + " should already exist in the derived axioms database.\n" +
        "Follow configuration instructions after restarting KeYmaera X with\n  java -jar keymaerax.jar")
      derivedAxiomDB.get(lemmaName).getOrElse(throw new IllegalArgumentException("Lemma " + lemmaName + " for derived axiom/rule " + name + " should have been added already")).fact
    }

    // Compute provable corresponding to ProvableInfo if necessary, and cache the provable.
    def provable: ProvableSig = {
      pi.theProvable match {
        case Some(provable) => provable.asInstanceOf[ProvableSig]
        case None =>
          val provable = pi match {
            case cai: CoreAxiomInfo => ProvableSig.axioms(cai.canonicalName)
            case cari: AxiomaticRuleInfo => ProvableSig.rules(cari.canonicalName)
            case dai: DerivedAxiomInfo => derivedAxiomOrRule(dai.canonicalName)
            case dari: DerivedRuleInfo => derivedAxiomOrRule(dari.canonicalName)
              //TODO: maybe replace DiffAxiomInfo stuff?
              /*case diffai: DifferentialAxiomInfo => ElidingProvable(Provable.implicitFuncAxiom(
              diffai.funcOf.asInstanceOf[FuncOf].func,
              diffai.diff.asInstanceOf[Term]))*/
          }
          pi.theProvable = Some(provable)
          provable
      }
    }

    // Compute and cache formula
    def formula: Formula = {
      pi.theFormula match {
        case Some(formula) => formula.asInstanceOf[Formula]
        case None =>
          val formula = pi match {
            case dai: DerivedAxiomInfo => derivedAxiomOrRule(dai.canonicalName).conclusion.succ.head
            case _: CoreAxiomInfo =>
              ProvableSig.axiom.get(pi.canonicalName) match {
                case Some(fml) => fml
                case None => throw AxiomNotFoundException("No formula for core axiom " + pi.canonicalName)
              }
          }
          pi.theFormula = Some(formula)
          formula
      }
    }
  }

  implicit class AxiomInfoAugmentor(val ai: AxiomInfo) {
    def key: PosInExpr = PosInExpr(ai.theKey)
    def recursor: List[PosInExpr] = ai.theRecursor.map(PosInExpr(_))
  }

  implicit class StorableInfoAugmentor(val si: StorableInfo) {
    def lemma: Lemma = si.getLemma.asInstanceOf[Lemma]
  }
}
