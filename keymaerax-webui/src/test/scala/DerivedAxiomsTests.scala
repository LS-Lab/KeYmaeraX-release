/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

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


  private def check(lemma: Lemma): Sequent = {
    println(lemma.name.get + "\n" + lemma.fact.conclusion)
    lemma.fact.isProved shouldBe true
    lemma.fact.conclusion
  }

  "Derived Axioms" should "prove" in {
    check(doubleNegationAxiom)
    //@todo check(existsDualAxiom)
  }

}
