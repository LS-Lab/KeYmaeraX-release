/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon.parser

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/** @author Nathan Fulton */
class BelleLexerTests extends AnyFlatSpec with Matchers {
  val testCases = List(
    ("nil", List(IDENT("nil"))),
    ("nil & nil", List(IDENT("nil"), DEPRECATED_SEQ_COMBINATOR, IDENT("nil"))),
    ("nil ; nil", List(IDENT("nil"), SEQ_COMBINATOR, IDENT("nil"))),
    ("nil | nil", List(IDENT("nil"), EITHER_COMBINATOR, IDENT("nil"))),
    ("(nil | nil)*", List(OPEN_PAREN, IDENT("nil"), EITHER_COMBINATOR, IDENT("nil"), CLOSE_PAREN, KLEENE_STAR)),
    ("cut({`1=1`})", List(IDENT("cut"), OPEN_PAREN, EXPRESSION("{`1=1`}", "{`" -> "`}"), CLOSE_PAREN)),
    ("implyR(-1)", List(IDENT("implyR"), OPEN_PAREN, ABSOLUTE_POSITION("-1"), CLOSE_PAREN)),
    (
      "diffCut({`1=1`}, 1)",
      List(
        IDENT("diffCut"),
        OPEN_PAREN,
        EXPRESSION("{`1=1`}", "{`" -> "`}"),
        COMMA,
        ABSOLUTE_POSITION("1"),
        CLOSE_PAREN,
      ),
    ),
    (
      "andR(1) <(QE, QE)",
      List(
        IDENT("andR"),
        OPEN_PAREN,
        ABSOLUTE_POSITION("1"),
        CLOSE_PAREN,
        BRANCH_COMBINATOR,
        OPEN_PAREN,
        IDENT("QE"),
        COMMA,
        IDENT("QE"),
        CLOSE_PAREN,
      ),
    ),
    ("QE partial", List(IDENT("QE"), PARTIAL)),
    ("partial(QE)", List(PARTIAL, OPEN_PAREN, IDENT("QE"), CLOSE_PAREN)),
    (
      "USMatch({`p() -> q()`} => implyR(1))",
      List(
        US_MATCH,
        OPEN_PAREN,
        EXPRESSION("{`p() -> q()`}", "{`" -> "`}"),
        RIGHT_ARROW,
        IDENT("implyR"),
        OPEN_PAREN,
        ABSOLUTE_POSITION("1"),
        CLOSE_PAREN,
        CLOSE_PAREN,
      ),
    ),
  )

  testCases.foreach(testCase => {
    val expectedTerminalList = testCase._2 :+ EOF
    testCase._1 should "lex to the appropriate terminal list" in {
      val resultingTerminalList = BelleLexer(testCase._1).map(_.terminal)
      // Note: if we don't have an expected terminal list then we're just testing that thing thing lexes.
      if (expectedTerminalList.nonEmpty) resultingTerminalList shouldBe expectedTerminalList
    }
  })
}
