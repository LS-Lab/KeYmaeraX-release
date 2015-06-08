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

  "After lexing the parser" should "parse x+y*z" in {
    parser.parse(List(IDENT("x"), OPERATOR("+"), IDENT("y"), OPERATOR("*"), IDENT("z"), EOF)) should be
      Plus(Variable("x"), Times(Variable("y"), Variable("z")))
  }

  it should "parse x*y+z" in {
    parser.parse(List(IDENT("x"), OPERATOR("*"), IDENT("y"), OPERATOR("+"), IDENT("z"), EOF)) should be
    Plus(Times(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse (x*y)+z" in {
    parser.parse(List(LPARENS, IDENT("x"), OPERATOR("*"), IDENT("y"), RPARENS, OPERATOR("+"), IDENT("z"), EOF)) should be
    Plus(Times(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse x*(y+z)" in {
    parser.parse(List(IDENT("x"), OPERATOR("*"), LPARENS, IDENT("y"), OPERATOR("+"), IDENT("z"), RPARENS, EOF)) should be
    Times(Variable("x"), Plus(Variable("y"), Variable("z")))
  }

  it should "parse x+y-z" in {
    parser.parse(List(IDENT("x"), OPERATOR("+"), IDENT("y"), OPERATOR("-"), IDENT("z"), EOF)) should be
    Plus(Variable("x"), Minus(Variable("y"), Variable("z")))
  }

  it should "parse x-y+z" in {
    parser.parse(List(IDENT("x"), OPERATOR("-"), IDENT("y"), OPERATOR("+"), IDENT("z"), EOF)) should be
    Plus(Minus(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse x-(y+z)" in {
    parser.parse(List(IDENT("x"), OPERATOR("-"), LPARENS, IDENT("y"), OPERATOR("+"), IDENT("z"), RPARENS, EOF)) should be
    Minus(Variable("x"), Minus(Variable("y"), Variable("z")))
  }

  ignore should "parse p&q|r" in {
    parser.parse(List(IDENT("p"), OPERATOR("&"), IDENT("q"), OPERATOR("|"), IDENT("r"), EOF)) should be
    Or(And(p0, q0), r0)
  }

  it should "parse x>0 & y<1 | z>=2" in {
    parser.parse(List(IDENT("x"), OPERATOR(">"), NUMBER("0"), OPERATOR("&"), IDENT("y"), OPERATOR("<"), NUMBER("1"), OPERATOR("|"), IDENT("z"), OPERATOR(">="), NUMBER("2"), EOF)) should be
    Or(And(Greater(Variable("x"), Number(0)), Less(Variable("y"),Number(1))), GreaterEqual(Variable("z"), Number(2)))
  }

  it should "parse x:=y+1;++z:=0;" in {
    parser.parse(List(IDENT("x"), OPERATOR(":="), IDENT("y"), OPERATOR("+"), NUMBER("1"), OPERATOR(";"), OPERATOR("++"), IDENT("z"), OPERATOR(":="), NUMBER("0"), EOF)) should be
    Choice(Assign(Variable("x"), Plus(Variable("y"),Number(1))), Assign(Variable("z"), Number(0)))
  }
}
