/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.{FlatSpec, Matchers}

/** Created by nfulton on 6/12/15. */
class KeYmaeraXAxiomParserTests extends FlatSpec with Matchers {
  "Axiom parser" should "parse a formula inside an axiom box" in {
    val input = """
                  |Axiom "This is an axiom"
                  | 1 = 1
                  |End.
                  |
                  |Axiom "This is another = axiom"
                  | x=x
                  |End.
      """.stripMargin
    val axioms = KeYmaeraXAxiomParser(input)
    axioms.head._1 should be("This is an axiom")
    axioms.head._2 should be(Equal(Number(1), Number(1)))
    axioms(1)._1 should be("This is another = axiom")
    axioms(1)._2 should be(Equal(Variable("x"), Variable("x")))
  }

  it should "parse the actual axiom file" in { ProvableSig.axiom }

  private val p = Function("p", None, Real, Bool)
  private val x = Variable("x", None, Real)
  private val t = FuncOf(Function("t", None, Unit, Real), Nothing)

  it should "parse all instantiate (found failure case)" in {
    val input = """Axiom /*\\foralli */ "all instantiate"
                  |  (\forall x p(x)) -> p(t())
                  |End.""".stripMargin
    val axioms = KeYmaeraXAxiomParser(input)
    axioms.length shouldBe 1
    axioms.head._1 shouldBe "all instantiate"

    axioms.head._2 shouldBe Imply(Forall(x :: Nil, PredOf(p, x)), PredOf(p, t))
  }
}
