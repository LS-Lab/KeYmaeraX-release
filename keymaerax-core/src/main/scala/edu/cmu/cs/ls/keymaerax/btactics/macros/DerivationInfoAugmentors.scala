/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.macros

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma._
import edu.cmu.cs.ls.keymaerax.pt._

import scala.language.implicitConversions

object DerivationInfoAugmentors {
  implicit class DerivationInfoAugmentor(val di: DerivationInfo) {
    def belleExpr: Any = di match {
      // useAt will just ask a ProvableInfo for its provable
      case pi: ProvableInfo => HilbertCalculus.useAt(pi)
      case ti: TacticInfo => ti.theExpr(())
    }
  }

  implicit class ProvableInfoAugmentor(val pi: ProvableInfo) {
    val derivedAxiomDB: LemmaDB = LemmaDBFactory.lemmaDB
    def derivedAxiomOrRule(name: String): ProvableSig = {
      val lemmaName = DerivationInfo(name) match {
        case si: StorableInfo => si.storedName
        case _ => throw new IllegalArgumentException(s"Axiom or rule $name is not storable")
      }
      require(
        derivedAxiomDB.contains(lemmaName),
        "Lemma " + lemmaName + " should already exist in the derived axioms database.\n" +
          "Follow configuration instructions after restarting KeYmaera X with\n  java -jar keymaerax.jar",
      )
      derivedAxiomDB
        .get(lemmaName)
        .getOrElse(
          throw new IllegalArgumentException(
            "Lemma " + lemmaName + " for derived axiom/rule " + name + " should have been added already"
          )
        )
        .fact
    }

    /** Compute provable corresponding to ProvableInfo if necessary, and cache the provable. */
    def provable: ProvableSig = {
      pi.theProvable match {
        case Some(provable) => provable.asInstanceOf[ProvableSig]
        case None =>
          val provable = pi match {
            case cai: CoreAxiomInfo => ProvableSig.axioms(cai.canonicalName)
            case cari: AxiomaticRuleInfo => ProvableSig.rules(cari.canonicalName)
            case dai: DerivedAxiomInfo => derivedAxiomOrRule(dai.canonicalName)
            case dari: DerivedRuleInfo => derivedAxiomOrRule(dari.canonicalName)
            // TODO: maybe replace DiffAxiomInfo stuff?
            /*case diffai: DifferentialAxiomInfo => ElidingProvable(Provable.implicitFuncAxiom(
              diffai.funcOf.asInstanceOf[FuncOf].func,
              diffai.diff.asInstanceOf[Term]))*/
          }
          pi.theProvable = Some(provable)
          provable
      }
    }

    /** Compute and cache formula. */
    def formula: Formula = {
      pi.theFormula match {
        case Some(formula) => formula.asInstanceOf[Formula]
        case None =>
          val formula = pi match {
            case dai: DerivedAxiomInfo => derivedAxiomOrRule(dai.canonicalName).conclusion.succ.head
            case _: CoreAxiomInfo => ProvableSig.axiom.get(pi.canonicalName) match {
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
