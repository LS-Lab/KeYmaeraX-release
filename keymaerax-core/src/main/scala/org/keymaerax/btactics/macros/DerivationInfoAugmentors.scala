/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

import org.keymaerax.btactics._
import org.keymaerax.core._
import org.keymaerax.infrastruct._
import org.keymaerax.lemma._
import org.keymaerax.pt._

import scala.annotation.nowarn
import scala.language.implicitConversions

object DerivationInfoAugmentors {
  implicit class DerivationInfoAugmentor(val di: DerivationInfo) {
    @nowarn("msg=match may not be exhaustive")
    def belleExpr: Any = di match {
      // useAt will just ask a ProvableInfo for its provable
      case pi: ProvableInfo => HilbertCalculus.useAt(pi)
      case ti: TacticInfo => ti.theExpr(())
    }
  }

  implicit class ProvableInfoAugmentor(val pi: ProvableInfo) {
    val derivedAxiomDB: LemmaDB = LemmaDBFactory.lemmaDB
    def derivedAxiomOrRule(info: DerivationInfo): ProvableSig = {
      val lemmaName = info match {
        case si: StorableInfo => si.storedName
        case _ => throw new IllegalArgumentException(s"Axiom or rule ${info.canonicalName} is not storable")
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
            s"Lemma $lemmaName for derived axiom/rule ${info.canonicalName} should have been added already"
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
            case dai: DerivedAxiomInfo => derivedAxiomOrRule(dai)
            case dari: DerivedRuleInfo => derivedAxiomOrRule(dari)
          }
          pi.theProvable = Some(provable)
          provable
      }
    }

    /** Compute and cache formula. */
    @nowarn("msg=match may not be exhaustive")
    def formula: Formula = {
      pi.theFormula match {
        case Some(formula) => formula.asInstanceOf[Formula]
        case None =>
          val formula = pi match {
            case dai: DerivedAxiomInfo => derivedAxiomOrRule(dai).conclusion.succ.head
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
