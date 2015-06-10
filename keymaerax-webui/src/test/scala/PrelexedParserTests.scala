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

  val f0 = FuncOf(Function("f",None,Unit,Real),Nothing)
  val g0 = FuncOf(Function("g",None,Unit,Real),Nothing)
  val h0 = FuncOf(Function("h",None,Unit,Real),Nothing)

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
    parser.parse(toStream(LPAREN, IDENT("x"), STAR, IDENT("y"), RPAREN, PLUS, IDENT("z"))) should be
    Plus(Times(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse x*(y+z)" in {
    parser.parse(toStream(IDENT("x"), STAR, LPAREN, IDENT("y"), PLUS, IDENT("z"), RPAREN)) should be
    Times(Variable("x"), Plus(Variable("y"), Variable("z")))
  }

  it should "parse -x" in {
    parser.parse(toStream(MINUS, IDENT("x"))) should be
    Neg(Variable("x"))
  }

  it should "parse x+y-z" in {
    parser.parse(toStream(IDENT("x"), PLUS, IDENT("y"), MINUS, IDENT("z"))) should be
    Plus(Variable("x"), Minus(Variable("y"), Variable("z")))
  }

  it should "parse x-y" in {
    parser.parse(toStream(IDENT("x"), MINUS, IDENT("y"))) should be
    Minus(Variable("x"), Variable("y"))
  }

  it should "parse x+-y" in {
    parser.parse(toStream(IDENT("x"), PLUS, MINUS, IDENT("y"))) should be
    Plus(Variable("x"), Neg(Variable("y")))
  }

  it should "parse -x+y" in {
    parser.parse(toStream(MINUS, IDENT("x"), PLUS, IDENT("y"))) should be
    Plus(Neg(Variable("x")), Variable("y"))
  }

  it should "parse -x-y" in {
    parser.parse(toStream(MINUS, IDENT("x"), MINUS, IDENT("y"))) should be
    Minus(Neg(Variable("x")), Variable("y"))
  }

  it should "parse x*-y" in {
    parser.parse(toStream(IDENT("x"), STAR, MINUS, IDENT("y"))) should be
    Times(Variable("x"), Neg(Variable("y")))
  }

  it should "parse -x*y" in {
    parser.parse(toStream(MINUS, IDENT("x"), STAR, IDENT("y"))) should be
    Times(Neg(Variable("x")), Variable("y"))
  }

  it should "parse x-y+z" in {
    parser.parse(toStream(IDENT("x"), MINUS, IDENT("y"), PLUS, IDENT("z"))) should be
    Plus(Minus(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse x-(y+z)" in {
    parser.parse(toStream(IDENT("x"), MINUS, LPAREN, IDENT("y"), PLUS, IDENT("z"), RPAREN)) should be
    Minus(Variable("x"), Minus(Variable("y"), Variable("z")))
  }

  it should "parse x-y*z+a*b" in {
    parser.parse(toStream(IDENT("x"), MINUS, IDENT("y"), STAR, IDENT("z"), PLUS, IDENT("a"), PLUS, IDENT("b"))) should be
    Plus(Minus(Variable("x"), Times(Variable("y"), Variable("z"))), Times(Variable("a"), Variable("b")))
  }

  it should "parse x-y+z*a/b^c" in {
    parser.parse(toStream(IDENT("x"), MINUS, IDENT("y"), PLUS, IDENT("z"), STAR, IDENT("a"), SLASH, IDENT("b"), POWER, IDENT("c"))) should be
    Plus(Minus(Variable("x"), Variable("y")), Times(Variable("z"), Divide(Variable("a"), Power(Variable("b"), Variable("c")))))
  }

  it should "parse p()&q()|r()" in {
    parser.parse(toStream(IDENT("p"), LPAREN, RPAREN, AND, IDENT("q"), LPAREN, RPAREN, OR, IDENT("r"), LPAREN, RPAREN)) should be
    Or(And(p0, q0), r0)
  }

  it should "parse f()>0&g()<=2|r()<1" in {
    parser.parse(toStream(IDENT("p"), LPAREN, RPAREN, RDIA, NUMBER("0"), AND, IDENT("g"), LPAREN, RPAREN, LESSEQ, NUMBER("2"), OR, IDENT("r"), LPAREN, RPAREN, LDIA, NUMBER("1"))) should be
    Or(And(Greater(f0, Number(0)), LessEqual(g0, Number(2))), Less(h0, Number(1)))
  }

  it should "parse f()>0&g(x)<=2|r()<1" in {
    parser.parse(toStream(IDENT("p"), LPAREN, RPAREN, RDIA, NUMBER("0"), AND, IDENT("g"), LPAREN, IDENT("x"), RPAREN, LESSEQ, NUMBER("2"), OR, IDENT("r"), LPAREN, RPAREN, LDIA, NUMBER("1"))) should be
    Or(And(Greater(f0, Number(0)), LessEqual(FuncOf(Function("g",None,Real,Real),Variable("x")), Number(2))), Less(h0, Number(1)))
  }

  it should "parse x>0 & y<1 | z>=2" in {
    parser.parse(toStream(IDENT("x"), RDIA, NUMBER("0"), AND, IDENT("y"), LDIA, NUMBER("1"), OR, IDENT("z"), GREATEREQ, NUMBER("2"))) should be
    Or(And(Greater(Variable("x"), Number(0)), Less(Variable("y"),Number(1))), GreaterEqual(Variable("z"), Number(2)))
  }

  it should "parse x:=y+1;++z:=0;" in {
    if (OpSpec.statementSemicolon) parser.parse(toStream(IDENT("x"), ASSIGN, IDENT("y"), PLUS, NUMBER("1"), SEMI, CHOICE, IDENT("z"), ASSIGN, NUMBER("0"), SEMI)) should be
    Choice(Assign(Variable("x"), Plus(Variable("y"),Number(1))), Assign(Variable("z"), Number(0)))
  }

  it should "parse x:=y+1;z:=0" in {
    if (!OpSpec.statementSemicolon) parser.parse(toStream(IDENT("x"), ASSIGN, IDENT("y"), PLUS, NUMBER("1"), SEMI, IDENT("z"), ASSIGN, NUMBER("0"))) should be
    Compose(Assign(Variable("x"), Plus(Variable("y"),Number(1))), Assign(Variable("z"), Number(0)))
  }

  it should "parse x:=y+1;z:=0;" in {
    if (OpSpec.statementSemicolon) parser.parse(toStream(IDENT("x"), ASSIGN, IDENT("y"), PLUS, NUMBER("1"), SEMI, IDENT("z"), ASSIGN, NUMBER("0"), SEMI)) should be
    Compose(Assign(Variable("x"), Plus(Variable("y"),Number(1))), Assign(Variable("z"), Number(0)))
  }

  it should "parse x-y'+z" in {
    parser.parse(toStream(IDENT("x"), MINUS, IDENT("y"), PRIME, PLUS, IDENT("z"))) should be
    Plus(Minus(Variable("x"), DifferentialSymbol(Variable("y"))), Variable("z"))
  }

  it should "parse x-(y)'+z" in {
    parser.parse(toStream(IDENT("x"), MINUS, LPAREN, IDENT("y"), RPAREN, PRIME, PLUS, IDENT("z"))) should be
    Plus(Minus(Variable("x"), Differential(Variable("y"))), Variable("z"))
  }

  it should "parse (x-y)'+z" in {
    parser.parse(toStream(IDENT("x"), MINUS, LPAREN, IDENT("y"), RPAREN, PRIME, PLUS, IDENT("z"))) should be
    Plus(Differential(Minus(Variable("x"), Variable("y"))), Variable("z"))
  }

  it should "parse [x:=y+1]x>=0" in {
    if (!OpSpec.statementSemicolon) parser.parse(toStream(LBOX, IDENT("x"), ASSIGN, IDENT("y"), PLUS, NUMBER("1"), RBOX, IDENT("x"), GREATEREQ, NUMBER("0"))) should be
    Box(Assign(Variable("x"), Plus(Variable("y"),Number(1))), GreaterEqual(Variable("x"), Number(0)))
  }

  it should "parse [x:=y+1;]x>=0" in {
    if (OpSpec.statementSemicolon)  parser.parse(toStream(LBOX, IDENT("x"), ASSIGN, IDENT("y"), PLUS, NUMBER("1"), SEMI, RBOX, IDENT("x"), GREATEREQ, NUMBER("0"))) should be
    Box(Assign(Variable("x"), Plus(Variable("y"),Number(1))), GreaterEqual(Variable("x"), Number(0)))
  }

  // pathetic cases

  "After lexing pathetic input the parser"  should "parse (((p())))&q()" in {
    parser.parse(toStream(LPAREN, LPAREN, LPAREN, IDENT("p"), LPAREN, RPAREN, RPAREN, RPAREN, RPAREN, AND, IDENT("q"), LPAREN, RPAREN)) should be
    And(p0, q0)
  }

  it should "parse p()&(((q())))" in {
    parser.parse(toStream(IDENT("p"), LPAREN, RPAREN, AND, LPAREN, LPAREN, LPAREN, IDENT("q"), LPAREN, RPAREN, RPAREN, RPAREN, RPAREN)) should be
    And(p0, q0)
  }

  it should "parse (((f())))+g()>=0" in {
    parser.parse(toStream(LPAREN, LPAREN, LPAREN, IDENT("p"), LPAREN, RPAREN, RPAREN, RPAREN, RPAREN, AND, IDENT("q"), LPAREN, RPAREN)) should be
    GreaterEqual(Plus(f0, g0), Number(0))
  }

  it should "parse 0<=f()+(((q())))" in {
    parser.parse(toStream(IDENT("p"), LPAREN, RPAREN, AND, LPAREN, LPAREN, LPAREN, IDENT("q"), LPAREN, RPAREN, RPAREN, RPAREN, RPAREN)) should be
    LessEqual(Number(0), Plus(f0, g0))
  }

  it should "refuse to default when trying to parse p()" in {
    a [ParseException] should be thrownBy parser.parse(toStream(IDENT("p"), LPAREN, RPAREN))
  }

  it should "parse f()>0" in {
    parser.parse(toStream(IDENT("f"), LPAREN, RPAREN, RDIA, NUMBER("0"))) should be
    Greater(f0, Number(0))
  }
}
