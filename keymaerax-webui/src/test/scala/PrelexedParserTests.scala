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
  
  "After lexing the parser" should "parse x+y*z" in {
    parser.parse(List(IDENT("x"), OPERATOR("+"), IDENT("y"), OPERATOR("*"), IDENT("z"), EOF)) should be
      Plus(Variable("x"), Times(Variable("y"), Variable("z")))
  }

  it should "parse x*y+z" in {
    parser.parse(List(IDENT("x"), OPERATOR("*"), IDENT("y"), OPERATOR("+"), IDENT("z"), EOF)) should be
    Plus(Times(Variable("x"), Variable("y")), Variable("z"))
  }

  it should "parse x+y-z" in {
    parser.parse(List(IDENT("x"), OPERATOR("+"), IDENT("y"), OPERATOR("-"), IDENT("z"), EOF)) should be
    Plus(Variable("x"), Minus(Variable("y"), Variable("z")))
  }

  it should "parse x-y+z" in {
    parser.parse(List(IDENT("x"), OPERATOR("-"), IDENT("y"), OPERATOR("+"), IDENT("z"), EOF)) should be
    Plus(Minus(Variable("x"), Variable("y")), Variable("z"))
  }
}
