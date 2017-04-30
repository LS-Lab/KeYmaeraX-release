/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{DotTerm, Number, Plus, Real, Times, Unit}
import org.scalatest.{FlatSpec, Matchers}

/**
 * @author Nathan Fulton
 */
class ExampleProblems extends FlatSpec with Matchers {
  "parser line messages" should "be properly offset" in {
    val f =
      """|   ProgramVariables.
        |   R x. R y. R z.
        |   End.
        |   Problem.
        |   (x*x*y >= 0 & x >= 0 & z >= x)
        |   ->
        |   [
        |   {x := 2x; y := 2y;}
        |  ]
        | (x*y >= 0)
        |End.""".stripMargin

    val ex = the [ParseException] thrownBy KeYmaeraXProblemParser(f)
    ex.found shouldBe """x (ID("x"))"""
    ex.expect shouldBe "Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term"
    ex.loc.begin.line shouldBe 8
    ex.loc.begin.column shouldBe 11
  }

  it should "be properly offset in another example" in {
    val f =
      """ ProgramVariables.
        |
        |   R x. R y. R z.
        |
        |   End.
        |
        |   Problem.
        |
        |   (x*x*y >= 0 & x >= 0 & z >= x)
        |
        |   ->
        |
        |   [
        |
        |   {x := 2x; y := 2y;}
        |
        |  ]
        |
        | (x*y >= 0)
        |
        |End.""".stripMargin

    val ex = the [ParseException] thrownBy KeYmaeraXProblemParser.parseAsProblemOrFormula(f)
    ex.found shouldBe """x (ID("x"))"""
    ex.expect shouldBe "Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term"
    ex.loc.begin.line shouldBe 15
    ex.loc.begin.column shouldBe 11
  }

  it should "work from file input" in {
    val f = " ProgramVariables.\n\n   R x. R y. R z. \n\n   End.  \n\n   Problem.\n\n   (x*x*y >= 0 & x >= 0 & z >= x) \n\n   -> \n\n   [\n\n   {x := 2x; y := 2y;}\n\n  ]\n\n (x*y >= 0)\n\nEnd."

    val ex = the [ParseException] thrownBy KeYmaeraXProblemParser.parseAsProblemOrFormula(f)
    ex.found shouldBe """x (ID("x"))"""
    ex.expect shouldBe "Multiplication in KeYmaera X requires an explicit * symbol. E.g. 2*term"
    ex.loc.begin.line shouldBe 15
    ex.loc.begin.column shouldBe 11
  }

  "The Parser" should "parse a simple file" in {
    val theProblem =
      """
        |ProgramVariables.
        |  R x.
        |  R y.
        |End.
        |Functions.
        |  R f(R, B).
        |  R g(B).
        |End.
        |Problem.
        |  x > 0 ->
        |  [
        |   x := x + 1;
        |  ] x > 0
        |End.
      """.stripMargin

    val result = KeYmaeraXProblemParser(theProblem)
    result shouldBe KeYmaeraXParser("""  x > 0 ->
                                      |  [
                                      |   x := x + 1;
                                      |  ] x > 0""".stripMargin)
  }

  it should "parse x>0 -> \\exists d [{x'=d}]x>0" in {
    val problem = "x>0 -> \\exists d [{x'=d}]x>0"
    val declProblem =
      s"""
        |ProgramVariables.
        |  R x.
        |End.
        |
        |Problem.
        |  $problem
        |End.
      """.stripMargin

    KeYmaeraXProblemParser(declProblem) shouldBe KeYmaeraXParser(problem)
  }

  "Interpretation parser" should "parse simple function declarations" in {
    val problem =
      """
        |Functions.
        |  R f() = (5).
        |End.
        |
        |Problem.
        |  f()>3
        |End.
      """.stripMargin

    val (decls, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    decls should have size 1
    decls should contain key ("f", None)
    decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Unit
      codomain shouldBe Real
      interpretation shouldBe Number(5)
    }
    formula shouldBe KeYmaeraXParser("5>3")
  }

  it should "parse function declarations with one parameter" in {
    val problem =
      """
        |Functions.
        |  R f(R) = (5 + .*.).
        |End.
        |
        |Problem.
        |  f(4)>3
        |End.
      """.stripMargin

    val (decls, formula) = KeYmaeraXProblemParser.parseProblem(problem)
    decls should have size 1
    decls should contain key ("f", None)
    decls(("f", None)) match { case (Some(domain), codomain, Some(interpretation), _) =>
      domain shouldBe Real
      codomain shouldBe Real
      interpretation shouldBe Plus(Number(5), Times(DotTerm(Real), DotTerm(Real)))
    }
    formula shouldBe KeYmaeraXParser("5+4*4>3")
  }
}
