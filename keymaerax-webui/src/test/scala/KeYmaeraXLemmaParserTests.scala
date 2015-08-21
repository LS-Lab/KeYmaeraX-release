/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.core.ToolEvidence
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLemmaParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{FlatSpec, Matchers}

/**
 * Created by smitsch on 8/12/15.
 * @author Stefan Mitsch
 */
class KeYmaeraXLemmaParserTests extends FlatSpec with Matchers {
  "Lemma parser" should "parse a formula inside a lemma box" in {
    val qq = "\"\"\"\""
    val input =
      // uses $qq to generate quadruple " because \" doesn't work inside """ """ strings
      s"""
        |Lemma "This is a lemma".
        |  [x:=2;]x>0
        |End.
        |
        |Tool.
        |  name ${qq}KeYmaera X$qq
        |  input $qq[x:=2;]x>0$qq
        |  tactic ${qq}import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic
        |import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
        |
        |class Example1Tactic extends (() => Tactic) {
        |
        |  def apply() = {
        |    ls(implyR) & la(andL) & ls(diffSolve) & ls(implyR) & QE
        |  }
        |}
        |
        |new Example1Tactic$qq
        |  proof $qq$qq
        |End.
      """.stripMargin
    val (name, formula, evidence) = KeYmaeraXLemmaParser(input)

    name shouldBe Some("This is a lemma")
    formula shouldBe "[x:=2;]x>0".asFormula
    evidence shouldBe new ToolEvidence(Map(
      "name" -> "KeYmaera X",
      "input" -> "[x:=2;]x>0",
      "tactic" ->
        """import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic
          |import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
          |
          |class Example1Tactic extends (() => Tactic) {
          |
          |  def apply() = {
          |    ls(implyR) & la(andL) & ls(diffSolve) & ls(implyR) & QE
          |  }
          |}
          |
          |new Example1Tactic""".stripMargin,
      "proof" -> ""))
  }

  it should "parse a lemma without name correctly" in {
    val qq = "\"\"\"\""
    val input =
    // uses $qq to generate quadruple " because \" doesn't work inside """ """ strings
      s"""
         |Lemma "".
         |  2>0 <-> true
         |End.
         |
         |Tool.
         |  name ${qq}Mathematica$qq
         |  input ${qq}2>0$qq
         |  output ${qq}true$qq
         |End.
      """.stripMargin
    val (name, formula, evidence) = KeYmaeraXLemmaParser(input)

    name shouldBe None
    formula shouldBe "2>0 <-> true".asFormula
    evidence shouldBe new ToolEvidence(Map(
      "name" -> "Mathematica",
      "input" -> "2>0",
      "output" -> "true"))
  }
}
