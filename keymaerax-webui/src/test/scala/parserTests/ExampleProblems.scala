/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package parserTests

import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import org.scalatest.{Matchers, FlatSpec}

/**
 * Created by nfulton on 6/18/15.
 */
class ExampleProblems extends FlatSpec with Matchers {
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
}
