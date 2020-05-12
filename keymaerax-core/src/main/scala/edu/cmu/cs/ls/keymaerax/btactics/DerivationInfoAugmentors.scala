package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{AppliedBuiltinTwoPositionTactic, AppliedPositionTactic, BelleExpr, NamedBelleExpr}
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.macros._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.HashMap

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
    def belleExpr: Any = di match {
      case theExpr => ??? //theExpr.asInstanceOf[Unit => BelleExpr] ()
    }

  }

  implicit class ProvableInfoAugmentor(val pi: ProvableInfo) {
    def provable: ProvableSig = {
      // @TODO: PRovableSig for all derived stuff
      // @TODO: Continue here
      println("All axioms: " + ProvableSig.axioms)
      println("Key: " + pi.canonicalName)
      try {
        ProvableSig.axioms(pi.canonicalName)
      } catch {
        case e: Throwable =>
          ProvableSig.rules(pi.canonicalName)
      }
    }

    def formula: Formula = {
      ProvableSig.axiom.get(pi.canonicalName) match {
        case Some(fml) => fml
        case None => throw new AxiomNotFoundException("No formula for core axiom " + pi.canonicalName)
      }
      // @TODO: Move all commented stuff to core
      //def belleExpr = codeName by ((pos:Position, seq:Sequent) => expr ()(pos))
    }
  }
}
