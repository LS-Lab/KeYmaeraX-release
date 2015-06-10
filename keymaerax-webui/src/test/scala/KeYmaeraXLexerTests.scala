import edu.cmu.cs.ls.keymaerax.parser.{RPAREN, KeYmaeraXLexer, Region, LPAREN, EOS}
import org.scalatest.{Matchers, FlatSpec}

/**
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
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(EOS, Region(1,1,1,1))
  }

  it should "Handle newlines correctly" in {
    val input =
      """
        |   (""".stripMargin
    KeYmaeraXLexer(input).head shouldBe edu.cmu.cs.ls.keymaerax.parser.Token(LPAREN, Region(2, 4, 2, 4))
  }

}
