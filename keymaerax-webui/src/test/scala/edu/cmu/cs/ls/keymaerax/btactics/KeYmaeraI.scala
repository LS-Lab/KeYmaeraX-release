/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.NamedTactic
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * @author Nathan Fulton
  */
class KeYmaeraI extends TacticTestBase {
  "existsL" should "work" in {
    val t = SequentCalculus.implyR(1) & SequentCalculus.existsL(-1)
    val f = "(\\exists x (x=x)) -> true".asFormula
    proveBy(f, t)
  }

  "allR" should "work" in {
    val t = SequentCalculus.allR(1) & SequentCalculus.implyR(1) & SequentCalculus.close
    val f = "(\\forall x (p(x)->p(x)))".asFormula
    proveBy(f, t) shouldBe 'proved
  }


  "KeYmaeraI" should "prove hw 5.3" in {
    val f = "A() & ( (A() -> B()) | (A() -> C()) ) -> B() | C()".asFormula
    val t = BelleParser(
      """
        |implyR(1) & andL(-1) & orL(-2) <(
        |  implyL(-2) <(
        |    close,
        |    orR1(1) & close
        |  ),
        |  implyL(-2) <(
        |    close,
        |    orR2(1) & close
        |  )
        |)
      """.stripMargin
    )
    proveBy(f, t) shouldBe 'proved
  }

  it should "print prop" in {
    println(BellePrettyPrinter(TactixLibrary.prop))
  }

  it should "prove true" in {
    val f = "true".asFormula
    val t = BelleParser("close")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove false" in {
    val f = "false -> false".asFormula
    val t = BelleParser("implyR(1) & close")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove by id" in {
    val f = "P() -> P()".asFormula
    val t = BelleParser("implyR(1) & close")
    proveBy(f,t) shouldBe 'proved
  }

  it should "extract cut" in {
    val input = "cut({`1=1`})"
    val t = BelleParser(input)
    BellePrettyPrinter(t) shouldBe input
  }

  it should "prove p() -> p() by prop" in {
    val f = "p() -> p()".asFormula
    val t = BelleParser("prop")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove true by prop" in {
    val f = "true".asFormula
    val t = BelleParser("prop")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove false by custom tactic" in {
    val f = "false -> p()".asFormula
    val t = TactixLibrary.implyR('R) & (TactixLibrary.closeId | TactixLibrary.closeT('R) | TactixLibrary.closeF('L))
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove false by prop" in {
    val f = "false -> p()".asFormula
    val t = BelleParser("prop")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove p() -> p() | q() by prop" in {
    val f = "p() -> p() | q()".asFormula
    val t = BelleParser("prop")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove p() -> q() | p() by prop" in {
    val f = "p() -> q() | p()".asFormula
    val t = BelleParser("prop")
    proveBy(f,t) shouldBe 'proved
  }

  it should "prove (p() <-> true) <-> p() by custom tactic" in {
    val f = "(p() <-> true) <-> p()".asFormula
    val t = BelleParser(
      """
        |equivR(1) & <(
        |   equivL(-1) & andL(-1) & implyL(-2) &<(close, close)
        |   ,
        |   equivR(1) <(close, close)
        |)
      """.stripMargin)

    val result = proveBy(f,t)
    result shouldBe 'proved
  }

  it should "prove (p() <-> true) <-> p() by prop" in {
    val f = "(p() <-> true) <-> p()".asFormula
    val t = BelleParser("prop")

    val result = proveBy(f,t)
    result shouldBe 'proved
  }

}
