package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.macros._
import DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, LazySequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.{boxMonotone, derivedRule}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{boxTrue, byUS, cut, hide, useAt}
import edu.cmu.cs.ls.keymaerax.core.{AssignAny, Box, Real, Sequent, True, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable
import scala.collection.immutable.Nil

/**
  * Created by bbohrer on 12/28/15.
  */
@SummaryTest
@UsualTest
class AxiomInfoTests extends FlatSpec with Matchers with BeforeAndAfterEach {
 "Axiom Info" should "exist for all axioms" in {
   try {
     println("a: " )
     DerivationInfoRegistry.init
     println("b: " )
     val seq = Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("\\forall x_ p_(||)".asFormula))
     val expr = useAt("[:*] assign nondet", PosInExpr(1::Nil))(1) &
       cut(Box(AssignAny(Variable("x_",None,Real)), True)) <(
         byUS(boxMonotone) & hide(-1)
         ,
         hide(1) & boxTrue(1)
       )
     val res2 = LazySequentialInterpreter()(expr, BelleProvable(ProvableSig.startProof(seq)))
     println("got: " + res2)
     //proveBy

     //val _ = DerivedAxioms.allGeneralize
     DerivedAxioms.prepopulateDerivedLemmaDatabase
     println(DerivationInfo.allInfo.length)
     val da = DerivedAxioms.allDual_y
     val aiea = DerivedAxioms.assignbImpliesExistsAxiom
     println(DerivationInfo.allInfo.length)
     ProvableSig.axiom.keys.forall({ case axiomName => AxiomInfo(axiomName); true }) shouldBe true
   } catch {
     case e:AxiomNotFoundException =>
       println("Test failed: Axiom not implemented: " + e.axiomName)
       throw e
   }
 }
}
