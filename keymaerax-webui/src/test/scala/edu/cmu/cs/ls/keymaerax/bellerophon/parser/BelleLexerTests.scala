package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import org.scalatest.{FlatSpec, Matchers}

/**
  * @author Nathan Fulton
  */
class BelleLexerTests extends FlatSpec with Matchers {
  val testCases = {
    ("nil", List(IDENT("nil"))) ::
    ("nil & nil", List(IDENT("nil"), DEPRECATED_SEQ_COMBINATOR, IDENT("nil"))) ::
    ("nil ; nil", List(IDENT("nil"), SEQ_COMBINATOR, IDENT("nil"))) ::
    ("nil | nil", List(IDENT("nil"), EITHER_COMBINATOR, IDENT("nil"))) ::
    ("(nil | nil)*", OPEN_PAREN :: IDENT("nil") :: EITHER_COMBINATOR :: IDENT("nil") :: CLOSE_PAREN :: KLEENE_STAR :: Nil) ::
    ("cut({`1=1`})", IDENT("cut") :: OPEN_PAREN :: EXPRESSION("{`1=1`}") :: CLOSE_PAREN :: Nil) ::
    ("implyR(-1)", IDENT("implyR") :: OPEN_PAREN :: ABSOLUTE_POSITION("-1") :: CLOSE_PAREN :: Nil) ::
    ("diffCut({`1=1`}, 1)", IDENT("diffCut") :: OPEN_PAREN :: EXPRESSION("{`1=1`}") :: COMMA :: ABSOLUTE_POSITION("1") :: CLOSE_PAREN :: Nil) ::
    ("andR(1) <(QE, QE)", IDENT("andR") :: OPEN_PAREN :: ABSOLUTE_POSITION("1") :: CLOSE_PAREN :: BRANCH_COMBINATOR :: OPEN_PAREN :: IDENT("QE") :: COMMA :: IDENT("QE") :: CLOSE_PAREN :: Nil) ::
    ("QE partial", IDENT("QE") :: PARTIAL :: Nil) ::
    ("partial(QE)", PARTIAL :: OPEN_PAREN :: IDENT("QE") :: CLOSE_PAREN :: Nil) ::
    ("USMatch({`p() -> q()`} => implyR(1))", US_MATCH :: OPEN_PAREN :: EXPRESSION("{`p() -> q()`}") :: RIGHT_ARROW :: IDENT("implyR") :: OPEN_PAREN :: ABSOLUTE_POSITION("1") :: CLOSE_PAREN :: CLOSE_PAREN :: Nil) ::
    Nil
  }

  testCases.foreach(testCase => {
    val expectedTerminalList = testCase._2 :+ EOF
    testCase._1 should "lex to the appropriate terminal list" in {
      val resultingTerminalList = BelleLexer(testCase._1).map(_.terminal)
      //Note: if we don't have an expected terminal list then we're just testing that thing thing lexes.
      if(expectedTerminalList nonEmpty) resultingTerminalList shouldBe expectedTerminalList
    }
  })
}
