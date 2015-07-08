package edu.cmu.cs.ls.keymaerax.parser

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser._
import org.scalatest.{PrivateMethodTester, Matchers, FlatSpec}

import test.RandomFormula

/**
 * Tests the parser on pairs of strings that are expected to parse the same.
 * @author aplatzer
 */
class PairParserTests extends FlatSpec with Matchers {
  val pp = KeYmaeraXPrettyPrinter
  val parser = KeYmaeraXParser

  def parseShouldBe(input: String, expr: Expression) = {
    val parse = parser(input)
    if (!(parse == expr)) {
      println("Reparsing" +
        "\nInput:      " + input +
        "\nParsed:     " + parse + " @ " + parse.getClass.getSimpleName +
        "\nExpression: " + KeYmaeraXPrettyPrinter.fullPrinter(parse))
      parse shouldBe expr
    }
  }

  "The parser" should "parse table of string pairs as expected" in {
    for ((s1, s2) <- expectedParse) {
      println("input 1: " + s1 + "\ninput 2: " + s2)
      if (s2 == unparseable) {
        a[ParseException] should be thrownBy parser(s1)
      } else {
        val p1 = parser(s1)
        val p2 = parser(s2)
        p1 shouldBe p2
        pp(p1) shouldBe pp(p2)
      }
    }
  }

  /** A special swearing string indicating that the other string cannot be parsed. */
  private val unparseable: String = "@#%@*!!!"
  /** Left string is expected to parse like the right string parses, or not at all if right==unparseable */
  private val expectedParse /*: List[Pair[String,String]]*/ = List(
    ("x+y+z","(x+y)+z"),
    ("x-y+z","(x-y)+z"),
    ("x+y-z","(x+y)-z"),
    ("x-y-z","(x-y)-z"),
    //("x++y", unparseable),  //@todo if statementSemicolon
    ("x*y+z","(x*y)+z"),
    ("x*y-z","(x*y)-z"),
    ("x+y*z","x+(y*z)"),
    ("x-y*z","x-(y*z)"),
    ("x**y", unparseable),
    ("x/y+z","(x/y)+z"),
    ("x/y-z","(x/y)-z"),
    ("x+y/z","x+(y/z)"),
    ("x-y/z","x-(y/z)"),
    ("x*y*z","(x*y)*z"),
    ("x*y/z","(x*y)/z"),
    ("x/y/z","(x/y)/z"),
    ("x/y*z","(x/y)*z"),
    ("x//y", unparseable),

    ("x+y^z","x+(y^z)"),
    ("x-y^z","x-(y^z)"),
    ("x^y+z","(x^y)+z"),
    ("x^y-z","(x^y)-z"),
    ("x^y*z","(x^y)*z"),
    ("x^y/z","(x^y)/z"),
    ("x*y^z","x*(y^z)"),
    ("x/y^z","x/(y^z)"),
    ("x^^y", unparseable),

    ("x+y+z","(x+y)+z"),
    ("x-y-z","(x-y)-z"),
    ("x*y*z","(x*y)*z"),
    ("x/y/z","(x/y)/z"),
    ("x^y^z","x^(y^z)"),

    // unary minus
    ("-x+y+z","((-x)+y)+z"),
    ("-x-y+z","((-x)-y)+z"),
    ("x+-y-z","(x+(-y))-z"),
    ("x- -y-z","(x-(-y))-z"),
    ("x+y- -z","(x+y)-(-z)"),
    ("x-y- -z","(x-y)-(-z)"),
    ("-x*y+z","((-x)*y)+z"),
    ("x*-y-z","(x*(-y))-z"),
    ("x+y*-z","x+(y*(-z))"),
    ("x-y*-z","x-(y*(-z))"),
    ("-x/y+z","((-x)/y)+z"),
    ("x/-y-z","(x/(-y))-z"),
    ("-x+y/z","(-x)+(y/z)"),
    ("x-y/-z","x-(y/(-z))"),
    ("-x*y*z","((-x)*y)*z"),
    ("x*-y/z","(x*(-y))/z"),
    ("x/y/-z","(x/y)/(-z)"),
    ("x/y*-z","(x/y)*(-z)"),
    ("x*-/y", unparseable),

    ("-x+y^z","(-x)+(y^z)"),
    ("-x-y^z","(-x)-(y^z)"),
    ("x^-y+z","(x^(-y))+z"),
    ("x^-y-z","(x^(-y))-z"),
    ("x^y+-z","(x^y)+(-z)"),
    ("x^y- -z","(x^y)-(-z)"),

    ("x+-y+z","(x+(-y))+z"),
    ("x- -y-z","(x-(-y))-z"),
    ("x*-y*z","(x*(-y))*z"),
    ("x/-y/z","(x/(-y))/z"),
    ("x^-y^z","x^((-y)^z)")
  )
}
