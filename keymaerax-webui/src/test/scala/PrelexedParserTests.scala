import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser._
import org.scalatest.{PrivateMethodTester, Matchers, FlatSpec}

/**
 * Tests the parser on manually lexed inputs
 * @author aplatzer
 */
class PrelexedParserTests extends FlatSpec with Matchers with PrivateMethodTester {
  val parser = KeYmaeraXParser

  val p0 = PredOf(Function("p",None,Unit,Bool),Nothing)
  val q0 = PredOf(Function("q",None,Unit,Bool),Nothing)
  val r0 = PredOf(Function("r",None,Unit,Bool),Nothing)

  def toStream(input: Terminal*): List[Token] = input.toList.map (t=>Token(t, UnknownLocation)) :+ Token(EOF)

  "After lexing the parser" should "parse x+y*z" in {
    parser.parse(toStream(IDENT("x"), PLUS, IDENT("y"), STAR, IDENT("z"))) should be
      Plus(Variable("x"), Times(Variable("y"), Variable("z")))
  }

  it should "parse x*y+z" in {
    parser.parse(toStream(IDENT("x"), STAR, IDENT("y"), PLUS, IDENT("z"))) should be
    Plus(Times(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse (x*y)+z" in {
    parser.parse(toStream(LPARENS, IDENT("x"), STAR, IDENT("y"), RPARENS, PLUS, IDENT("z"))) should be
    Plus(Times(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse x*(y+z)" in {
    parser.parse(toStream(IDENT("x"), STAR, LPARENS, IDENT("y"), PLUS, IDENT("z"), RPARENS)) should be
    Times(Variable("x"), Plus(Variable("y"), Variable("z")))
  }

  it should "parse x+y-z" in {
    parser.parse(toStream(IDENT("x"), PLUS, IDENT("y"), MINUS, IDENT("z"))) should be
    Plus(Variable("x"), Minus(Variable("y"), Variable("z")))
  }

  it should "parse x-y+z" in {
    parser.parse(toStream(IDENT("x"), MINUS, IDENT("y"), PLUS, IDENT("z"))) should be
    Plus(Minus(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse x-(y+z)" in {
    parser.parse(toStream(IDENT("x"), MINUS, LPARENS, IDENT("y"), PLUS, IDENT("z"), RPARENS)) should be
    Minus(Variable("x"), Minus(Variable("y"), Variable("z")))
  }

  ignore should "parse p&q|r" in {
    parser.parse(toStream(IDENT("p"), AND, IDENT("q"), OR, IDENT("r"))) should be
    Or(And(p0, q0), r0)
  }

  it should "parse x>0 & y<1 | z>=2" in {
    parser.parse(toStream(IDENT("x"), RDIA, NUMBER("0"), AND, IDENT("y"), LDIA, NUMBER("1"), OR, IDENT("z"), GREATEREQ, NUMBER("2"))) should be
    Or(And(Greater(Variable("x"), Number(0)), Less(Variable("y"),Number(1))), GreaterEqual(Variable("z"), Number(2)))
  }

  it should "parse x:=y+1;++z:=0;" in {
    parser.parse(toStream(IDENT("x"), ASSIGN, IDENT("y"), PLUS, NUMBER("1"), COMPOSE, CHOICE, IDENT("z"), ASSIGN, NUMBER("0"))) should be
    Choice(Assign(Variable("x"), Plus(Variable("y"),Number(1))), Assign(Variable("z"), Number(0)))
  }
}
