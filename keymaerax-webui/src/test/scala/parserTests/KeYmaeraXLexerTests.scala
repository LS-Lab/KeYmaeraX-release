package parserTests

import edu.cmu.cs.ls.keymaerax.parser._
import org.scalatest.{FlatSpec, Matchers}

/**
 * These are white space processing tests and location munging tests. All tests that don't care
 * about white space or location munging and that produce a parsable stream should be added
 * to PrelexedParserTests instead.
 * Created by nfulton on 6/10/15.
 */
class KeYmaeraXLexerTests extends FlatSpec with Matchers {
  "Lexer" should "Handle spaces correctly" in {
    val input = "   ("
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(LPAREN, Region(1, 4, 1, 4))
  }

  it should "Handle no spaces correctly" in {
    val input = ")"
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(RPAREN, Region(1, 1, 1, 1))
  }

  it should "Handle empty string correctly" in {
    val input = ""
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(EOF, UnknownLocation)
  }

  it should "Handle newlines correctly" in {
    val input =
      """
        |   (""".stripMargin
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(LPAREN, Region(2, 4, 2, 4))
  }

  it should "parse forall" in {
    val input = "\\forall"
    KeYmaeraXLexer(input).length shouldBe 2 //forall and EOS.
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(FORALL, Region(1,1,1,7))
  }

  it should "parse forall 2 times" in {
    val input = """\forall \forall"""
    KeYmaeraXLexer(input).length shouldBe 3 //forall and EOS.
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(FORALL, Region(1,1,1,7))
    KeYmaeraXLexer(input).tail.head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(FORALL, Region(1,9,1,15))
  }

  it should "parse an identifier" in {
    val input = "input"
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(IDENT("input"), Region(1,1,1,5))
  }

  it should "parse an identifier -- checking length is ok" in {
    val input = "thisisalongvariablename"
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(IDENT("thisisalongvariablename"), Region(1,1,1,input.length))
  }


  it should "parse an integer" in {
    val n = "99"
    KeYmaeraXLexer(n).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(NUMBER(n), Region(1,1,1,n.length))
  }

  it should "parse an number" in {
    val n = "99.999"
    KeYmaeraXLexer(n).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(NUMBER(n), Region(1,1,1,n.length))
  }

  it should "parse a single comment" in {
    val n = "/*an identifier*/x"
    KeYmaeraXLexer(n).head.tok shouldBe(IDENT("x"))
  }

  it should "parse a multi-line comment" in {
    val n =
      """
        |/*
        | * This is a comment.
        | */
        | x
      """.stripMargin
    KeYmaeraXLexer(n).head.tok shouldBe(IDENT("x"))
  }

}
