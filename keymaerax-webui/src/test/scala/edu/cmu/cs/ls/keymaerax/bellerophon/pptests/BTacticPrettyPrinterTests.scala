/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon.{ReflectiveExpressionBuilder, SaturateTactic}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import edu.cmu.cs.ls.keymaerax.btactics.{FixedGenerator, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

import scala.language.postfixOps

/**
 * Tests BelleExpr pretty printing, for expected string representation plus roundtrip identity with parser.
 * @author
 *   Nathan Fulton
 * @author
 *   Stefan Mitsch
 */
@UsualTest
class BTacticPrettyPrinterTests extends TacticTestBase {
  private val parser =
    new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _))

  private def roundTrip(tactic: String) = {
    val parsed = parser(tactic)
    val printed = BellePrettyPrinter(parsed)
    printed shouldBe tactic
    parser(printed) shouldBe parsed
  }

  // @note this test case points out something that's kind-of a problem with our current setup -- print(parse(x)) != x even if parse(print(x)) = x.
  // In order to get the actually correct behavior we would need DerivedAxiomInfo to be a bidirectional map and then we would need to always prefer that map's
  // names over the actual tactic that was created at the end of the day.
  "built-in printer" should "print a built-in expr" in withTactics { roundTrip("nil") }

  it should "print e(1)" in withTactics { roundTrip("andR(1)") }

  it should "print e('L)" in withTactics { roundTrip("andR('L)") }

  it should "print e('R)" in withTactics { roundTrip("andR('R)") }

  "seq printer" should "print e ; e" in withTactics { roundTrip("nil ; nil") }

  it should "print e ; e ; e" in withTactics { roundTrip("nil ; nil ; nil") }

  it should "print e | e" in withTactics { roundTrip("nil | nil") }

  "doall" should "print e ; doall(e)" in withTactics { roundTrip("andR(1) ; doall(andL(1))") }

  "transform" should "print with formula" in withTactics {
    val tactic = TactixLibrary.transform("x>0".asFormula)(1)
    BellePrettyPrinter(tactic) shouldBe "transform(\"x>0\", 1)"
    roundTrip("transform(\"x>0\", 1)")
  }

  "Applied position tactics" should "print position" in withTactics {
    val tactic = TactixLibrary.implyR(1)
    BellePrettyPrinter(tactic) shouldBe "implyR(1)"
    roundTrip("implyR(1)")
  }

  "Applied position with input tactics" should "print input and position" in withTactics {
    val tactic = TactixLibrary.loop("x>0".asFormula)(1)
    BellePrettyPrinter(tactic) shouldBe "loop(\"x>0\", 1)"
    roundTrip("loop(\"x>0\", 1)")
  }

  "Input tactic" should "print list input" in withTactics {
    val tactic = TactixLibrary.dC("x>0".asFormula :: "x>2".asFormula :: Nil)(1)
    BellePrettyPrinter(tactic) shouldBe "dC(\"x>0::x>2::nil\", 1)"
    roundTrip("dC(\"x>0::x>2::nil\", 1)")
  }

  it should "print empty list input" in withTactics {
    val tactic = TactixLibrary.dC(Nil)(1)
    BellePrettyPrinter(tactic) shouldBe "dC(\"nil\", 1)"
    roundTrip("dC(\"nil\", 1)")
  }

  "useLemmaAt" should "print key correctly" in withTactics {
    BellePrettyPrinter(TactixLibrary.useLemmaAt("the lemma", None)(1)) shouldBe "useLemmaAt(\"the lemma\", 1)"
    roundTrip("useLemmaAt(\"the lemma\", 1)")
    BellePrettyPrinter(TactixLibrary.useLemmaAt("the lemma", Some(PosInExpr(1 :: Nil)))(1)) shouldBe
      "useLemmaAt(\"the lemma\", \".1\", 1)"
    roundTrip("useLemmaAt(\"the lemma\", \".1\", 1)")
  }

  "Operator precedence" should "bind saturate * stronger than ;" in withTactics { roundTrip("implyR(1) ; andL('L)*") }

  it should "parenthesize ; in saturate *" in withTactics { roundTrip("(implyR(1) ; andL('L))*") }

  it should "bind repeat *times stronger than ;" in withTactics { roundTrip("implyR(1) ; andL('L)*2") }

  it should "parenthesize partial" in withTactics { roundTrip("implyR(1) ; (andL(1) partial)") }

  it should "parenthesize tactic combinators" in withTactics {
    parser(BellePrettyPrinter(SaturateTactic(TactixLibrary.alphaRule))) shouldBe SaturateTactic(TactixLibrary.alphaRule)
  }

  "Position locator" should "be printed correctly" in withTactics {
    val tactic = parser("""andTrue(2.1.1=="x=2&true")""")
    tactic.prettyString shouldBe """andTrue(2.1.1=="x=2&true")"""
  }
}
