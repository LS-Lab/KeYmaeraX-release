/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms._
import DerivedAxioms.abs

import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.ApplyRule
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica, Tool}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.ProvabilityTestHelper

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Tests provability of the derived axioms.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms]]
 */
class DerivedAxiomsTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }


  private def check(lemma: Lemma): Sequent = {
    println(lemma.name.get + "\n" + lemma.fact.conclusion)
    lemma.fact.isProved shouldBe true
    useToClose(lemma)
    lemma.fact.conclusion
  }

  private def useToClose(lemma: Lemma): Unit = {
    val rootNode = Provable.startProof(lemma.fact.conclusion)
    rootNode(lemma.fact, 0).isProved shouldBe true
  }

  private def check(lem: ApplyRule[LookupLemma]): Sequent = {
    val lemma = lem.rule.lemma
    println(lemma.name.get + "\n" + lemma.fact.conclusion)
    lemma.fact.isProved shouldBe true
    useToClose(lem)
    lemma.fact.conclusion
  }

  private def useToClose(lem: ApplyRule[LookupLemma]): Unit = {
    val rootNode = new RootNode(lem.rule.lemma.fact.conclusion)
    //@todo what/howto ensure it's been initialized already
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(lem, rootNode))
    rootNode.isClosed() shouldBe true
    rootNode.isProved() shouldBe true
  }

  "Derived Axioms" should "prove <-> reflexive" in {check(equivReflexiveAxiom)}
  it should "prove !!" in {check(doubleNegationAxiom)}
  it should "prove exists dual" in {check(existsDualAxiom)}
  it should "prove vacuous exists" in {check(vacuousExistsAxiom)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetAxiom)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetAxiom)}
  it should "prove \\forall->\\exists" in {check(forallThenExistsAxiom)}
  it should "prove abs" in {check(abs)}
  it should "prove y-variant of all dual" in {check(dummyallDualAxiom)}
  it should "prove y-variant of all dual 2" in {check(dummyallDualAxiom2)}
  it should "prove y-variant of exists dual" in {check(dummyexistsDualAxiom)}
  it should "prove +0' dummy" in {check(dummyDplus0)}
  it should "prove +*' reduce dummy" in {check(dummyDplustimesreduceAxiom)}
  it should "prove +*' expand dummy" in {check(dummyDplustimesexpandAxiom)}

  "Derived Axiom Tactics" should "prove <-> reflexive" in {check(equivReflexiveT)}
  it should "prove !!" in {check(doubleNegationT)}
  it should "prove exists dual" in {check(existsDualT)}
  it should "prove vacuous exists" in {check(vacuousExistsT)}
  it should "prove V[:*] vacuous assign nondet" in {check(vacuousBoxAssignNondetT)}
  it should "prove V<:*> vacuous assign nondet" in {check(vacuousDiamondAssignNondetT)}
  it should "prove abs" in {check(abs)}


  lazy val dummyexistsDualAxiom = derivedAxiom("exists dual dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!\\forall y (!p(y))) <-> \\exists y p(y)".asFormula)),
    useAt("all dual", PosInExpr(1::Nil))(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val dummyallDualAxiom = derivedAxiom("all dual dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!\\exists y (!p(y))) <-> \\forall y p(y)".asFormula)),
    byUS("all dual")
  )

  lazy val dummyallDualAxiom2 = derivedAxiom("all dual dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!\\exists y (!q(y))) <-> \\forall y q(y)".asFormula)),
    byUS("all dual")
  )

  lazy val dummyDplus0 = derivedAxiom("+id' dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(f(??) + 0)' = (f(??)') + (0')".asFormula)),
    useAt("+' derive sum", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
      byUS("= reflexive")
  )

  lazy val dummyDplustimesreduceAxiom = derivedAxiom("+*' reduce dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(f(??) + (g(??)*h(??)))' = (f(??)') + ((g(??)')*h(??) + g(??)*(h(??)'))".asFormula)),
    useAt("*' derive product", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
      useAt("+' derive sum", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
      byUS("= reflexive")
  )

  lazy val dummyDplustimesexpandAxiom = derivedAxiom("+*' expand dummy",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(f(??) + (g(??)*h(??)))' = (f(??)') + ((g(??)')*h(??) + g(??)*(h(??)'))".asFormula)),
    useAt("+' derive sum")(SuccPosition(0, 0::Nil)) &
    useAt("*' derive product")(SuccPosition(0, 0::1::Nil)) &
      byUS("= reflexive")
  )
}
