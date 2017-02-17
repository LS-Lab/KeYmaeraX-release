/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import org.scalatest.{Matchers, FlatSpec}

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
    val result = try {
      KeYmaeraXProblemParser(f)
      assert(false, "Should've thrown an error.")
    } catch {
      case e : ParseException => {
        e.loc.begin.line shouldBe 8
        e.loc.begin.column shouldBe 11
      }
    }

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
    val result = try {
      KeYmaeraXProblemParser.parseAsProblemOrFormula(f)
      assert(false, "Should've thrown an error.")
    } catch {
      case e : ParseException => {
        println(e)
        e.loc.begin.line shouldBe 15
        e.loc.begin.column shouldBe 11
      }
    }

  }

  it should "work from file input" in {
    val f = " ProgramVariables.\n\n   R x. R y. R z. \n\n   End.  \n\n   Problem.\n\n   (x*x*y >= 0 & x >= 0 & z >= x) \n\n   -> \n\n   [\n\n   {x := 2x; y := 2y;}\n\n  ]\n\n (x*y >= 0)\n\nEnd."

    val result = try {
      KeYmaeraXProblemParser.parseAsProblemOrFormula(f)
      assert(false, "Should've thrown an error.")
    } catch {
      case e : ParseException => {
        println(e)
        e.loc.begin.line shouldBe 15
        e.loc.begin.column shouldBe 11
      }
    }

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
    val theProblem =
      """
        |ProgramVariables.
        |  R x.
        |End.
        |
        |Problem.
        |  x>0 -> \exists d [{x'=d}]x>0
        |End.
      """.stripMargin

    val result = KeYmaeraXProblemParser(theProblem)
  }
}
