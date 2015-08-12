/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.tactics.{TacticWrapper, Tactics, RootNode}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.ApplyRule
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica, Tool}
import testHelper.ProvabilityTestHelper

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Tests provability of the derived axioms.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms]]
 */
class DerivedAxiomsTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig
  var math: Tool with QETool = null

  override def beforeEach() = {
    KeYmaera.init(Map()) //@todo how to do this really?
    math = new Mathematica
    math.init(mathematicaConfig)
  }

  override def afterEach() = {
    math.shutdown()
    math = null
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

  "Derived Axioms" should "prove !!" in {check(doubleNegationAxiom)}
  //@todo check(existsDualAxiom)

  it should "prove abs" in {check(abs)}

}
