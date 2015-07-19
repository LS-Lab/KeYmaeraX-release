/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
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
    // from doc/dL-grammar.md
    ("x-y-z","(x-y)-z"),
    ("x^2^4", "x^(2^4)"),
    ("p()->q()->r()", "p()->(q()->r())"),
    ("x:=1;x:=2;x:=3;", "x:=1;{x:=2;x:=3;}"),
    ("[x:=1;x:=2;x:=3;]x=3", "[x:=1;{x:=2;x:=3;}]x=3"),

    // reasonably systematic
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
    ("x^-y^z","x^((-y)^z)"),

    ("\\forall x p(x)&q(x)", "(\\forall x p(x))&q(x)"),
    ("\\forall x p(x)|q(x)", "(\\forall x p(x))|q(x)"),
    ("\\forall x p(x)->q(x)", "(\\forall x p(x))->q(x)"),
    ("\\forall x p(x)<->q(x)", "(\\forall x p(x))<->q(x)"),

    ("\\exists x p(x)&q(x)", "(\\exists x p(x))&q(x)"),
    ("\\exists x p(x)|q(x)", "(\\exists x p(x))|q(x)"),
    ("\\exists x p(x)->q(x)", "(\\exists x p(x))->q(x)"),
    ("\\exists x p(x)<->q(x)", "(\\exists x p(x))<->q(x)"),

    ("\\forall x x>=0&x<0", "(\\forall x (x>=0))&(x<0)"),
    ("\\forall x x>=0|x<0", "(\\forall x (x>=0))|(x<0)"),
    ("\\forall x x>=0->x<0", "(\\forall x (x>=0))->(x<0)"),
    ("\\forall x x>=0<->x<0", "(\\forall x (x>=0))<->(x<0)"),

    ("\\exists x x>=0&x<0", "(\\exists x (x>=0))&(x<0)"),
    ("\\exists x x>=0|x<0", "(\\exists x (x>=0))|(x<0)"),
    ("\\exists x x>=0->x<0", "(\\exists x (x>=0))->(x<0)"),
    ("\\exists x x>=0<->x<0", "(\\exists x (x>=0))<->(x<0)"),
    ("\\forall \\forall", unparseable),
    ("\\exists \\exists", unparseable),
    ("\\forall \\exists", unparseable),
    ("\\exists \\forall", unparseable),

    ("[x:=x+1;] p(x)&q(x)", "([x:=x+1;] p(x))&q(x)"),
    ("[x:=x+1;] p(x)|q(x)", "([x:=x+1;] p(x))|q(x)"),
    ("[x:=x+1;] p(x)->q(x)", "([x:=x+1;] p(x))->q(x)"),
    ("[x:=x+1;] p(x)<->q(x)", "([x:=x+1;] p(x))<->q(x)"),

    ("<x:=x+1;> p(x)&q(x)", "(<x:=x+1;> p(x))&q(x)"),
    ("<x:=x+1;> p(x)|q(x)", "(<x:=x+1;> p(x))|q(x)"),
    ("<x:=x+1;> p(x)->q(x)", "(<x:=x+1;> p(x))->q(x)"),
    ("<x:=x+1;> p(x)<->q(x)", "(<x:=x+1;> p(x))<->q(x)"),

    ("[x:=x+1;] x>=0&x<0", "([x:=x+1;] (x>=0))&(x<0)"),
    ("[x:=x+1;] x>=0|x<0", "([x:=x+1;] (x>=0))|(x<0)"),
    ("[x:=x+1;] x>=0->x<0", "([x:=x+1;] (x>=0))->(x<0)"),
    ("[x:=x+1;] x>=0<->x<0", "([x:=x+1;] (x>=0))<->(x<0)"),

    ("<x:=x+1;> x>=0&x<0", "(<x:=x+1;> (x>=0))&(x<0)"),
    ("<x:=x+1;> x>=0|x<0", "(<x:=x+1;> (x>=0))|(x<0)"),
    ("<x:=x+1;> x>=0->x<0", "(<x:=x+1;> (x>=0))->(x<0)"),
    ("<x:=x+1;> x>=0<->x<0", "(<x:=x+1;> (x>=0))<->(x<0)"),

    ("<x:=x+1;>[x:=x+1;]", unparseable),

    ("[{x'=1}] p(x)&q(x)", "([{x'=1}] p(x))&q(x)"),
    ("[{x'=1}] p(x)|q(x)", "([{x'=1}] p(x))|q(x)"),
    ("[{x'=1}] p(x)->q(x)", "([{x'=1}] p(x))->q(x)"),
    ("[{x'=1}] p(x)<->q(x)", "([{x'=1}] p(x))<->q(x)"),

    ("<{x'=1}> p(x)&q(x)", "(<{x'=1}> p(x))&q(x)"),
    ("<{x'=1}> p(x)|q(x)", "(<{x'=1}> p(x))|q(x)"),
    ("<{x'=1}> p(x)->q(x)", "(<{x'=1}> p(x))->q(x)"),
    ("<{x'=1}> p(x)<->q(x)", "(<{x'=1}> p(x))<->q(x)"),

    ("[{x'=1}] x>=0&x<0", "([{x'=1}] (x>=0))&(x<0)"),
    ("[{x'=1}] x>=0|x<0", "([{x'=1}] (x>=0))|(x<0)"),
    ("[{x'=1}] x>=0->x<0", "([{x'=1}] (x>=0))->(x<0)"),
    ("[{x'=1}] x>=0<->x<0", "([{x'=1}] (x>=0))<->(x<0)"),

    ("<{x'=1}> x>=0&x<0", "(<{x'=1}> (x>=0))&(x<0)"),
    ("<{x'=1}> x>=0|x<0", "(<{x'=1}> (x>=0))|(x<0)"),
    ("<{x'=1}> x>=0->x<0", "(<{x'=1}> (x>=0))->(x<0)"),
    ("<{x'=1}> x>=0<->x<0", "(<{x'=1}> (x>=0))<->(x<0)"),

    ("<{x'=1}>[{x'=1}]true", "<{x'=1}>([{x'=1}](true))"),
    ("<{x'=1}>[{x'=1}]", unparseable),

    ("\\forall p(x())","\\forall p (x())"),   //@todo not a great test on string level


    ("x:=1;x:=2;++x:=3;", "{x:=1;x:=2;}++{x:=3;}"),
    ("[x:=1;x:=2;++x:=3;]x>=5", "[{x:=1;x:=2;}++{x:=3;}]x>=5"),
    ("<x:=1;x:=2;++x:=3;>x>5", "<{x:=1;x:=2;}++{x:=3;}>x>5"),
    ("x:=1;++x:=2;x:=3;", "x:=1;++{x:=2;x:=3;}"),
    ("[x:=1;++x:=2;x:=3;]x^2>4", "[x:=1;++{x:=2;x:=3;}]x^2>4"),
    ("<x:=1;++x:=2;x:=3;>x^2>4", "<x:=1;++{x:=2;x:=3;}>x^2>4"),
    ("x:=1;?x>0&x^2>5;{x'=5}", "x:=1;{?((x>0)&((x^2)>5));{x'=5}}"),
    ("[x:=1;?x>0&x^2>5;{x'=5}]x+y>99", "[x:=1;{?((x>0)&((x^2)>5));{x'=5}}]x+y>99"),
    ("<x:=1;?x>0&x^2>5;{x'=5}>x+y>99", "<x:=1;{?((x>0)&((x^2)>5));{x'=5}}>x+y>99"),
    ("x:=1;?x<0&x^2>5;{x'=5}", "x:=1;{?((x<0)&((x^2)>5));{x'=5}}"),
    ("[x:=1;?x<0&x^2>5;{x'=5}]x+y>99", "[x:=1;{?((x<0)&((x^2)>5));{x'=5}}]x+y>99"),
    ("<x:=1;?x<0&x^2>5;{x'=5}>x+y>99", "<x:=1;{?((x<0)&((x^2)>5));{x'=5}}>x+y>99"),
    ("x:=1;++x:=2;++x:=3;", "x:=1;++{x:=2;++x:=3;}"),
    ("[x:=1;++x:=2;++x:=3;]x>5", "[x:=1;++{x:=2;++x:=3;}]x>5"),
    ("<x:=1;++x:=2;++x:=3;>x>5", "<x:=1;++{x:=2;++x:=3;}>x>5"),

    // nested modalities within programs
    ("<x:=1;?<x:=2;>x>1;>x>5", "<x:=1;?(<x:=2;>(x>1));>(x>5)"),
    ("[x:=1;?<x:=2;>x>1;]x>5", "[x:=1;?(<x:=2;>(x>1));](x>5)"),
    ("<x:=1;?<{x'=2}>x>1;>x>5", "<x:=1;?(<{x'=2}>(x>1));>(x>5)"),
    ("[x:=1;?<{x'=2}>x>1;]x>5", "[x:=1;?(<{x'=2}>(x>1));](x>5)"),
    ("[?[?[?q();]p();]r();]s()", "[?([?([?(q());]p());]r());]s()"),
    ("[?<?[?q();]p();>r();]s()", "[?(<?([?(q());]p());>r());]s()"),
    ("<?<?<?q();>p();>r();>s()", "<?(<?(<?(q());>p());>r());>s()"),
    ("[?<?[?q();]p();>r();]s()", "[?(<?([?(q());]p());>r());]s()"),
    ("<?[?<?q();>p();]r();>s()", "<?([?(<?(q());>p());]r());>s()"),

    // Converted from ParserParenTests:

    // unary operator binds stronger than binary operator
    ("! p > 0 & p < 5", "(!(p>0)) & (p<5)"),
      ("! p = 0 & p = 5", "(!(p=0)) & (p=5)") ,
      ("! p > 0 | p < 5", "(!(p>0)) | (p<5)") ,
      ("! p > 0 -> p > 5", "(!(p>0)) -> (p>5)") ,
      ("! p > 0 <-> p > 5", "(!(p>0)) <-> (p>5)") ,
      // quantifiers do not bind logical connectives but do bind inequalities.
      ("! \\forall x x > 0 | p < 5", "(!(\\forall x x>0)) | (p<5)") ,
      ("! \\exists x x > 0 | p < 5", "(!(\\exists x x>0)) | (p<5)") ,
      ("! \\forall x [p:=x;]p >= x | p < 5", "(!(\\forall x ([p:=x;](p>=x)))) | (p<5)") ,
      // quantifiers with multiple variables
      //("\\forall x, y . (y > x -> y > x)", "\\forall x, y . (y > x -> y > x)") ,
      //("\\exists y, x . (y > x -> y > x)", "\\exists y, x . (y > x -> y > x)") ,
      // modalities do not bind logical connectives.
      ("[p:=1;] p>0 & p < 1", "([p:=1;](p>0)) & (p<1)") ,
      ("[p:=1;] p>0 | p < 1", "([p:=1;](p>0)) | (p<1)") ,
      ("[p:=1;] p>0 -> p < 1", "([p:=1;](p>0)) -> (p<1)") ,
      ("<p:=1;> p>0 & p < 1", "(<p:=1;>(p>0)) & (p<1)") ,
      ("<p:=1;> p>0 | p < 1", "(<p:=1;>(p>0)) | (p<1)") ,
      ("<p:=1;> p>0 -> p < 1", "(<p:=1;>(p>0)) -> (p<1)") ,
      ("\\forall x x > 2 & a()", "(\\forall x (x > 2)) & a()") ,
      ("\\forall x x > 2 | a()", "(\\forall x (x > 2)) | a()") ,
      ("\\forall x x > 2 -> a()", "(\\forall x (x > 2)) -> a()") ,
      ("\\forall x x > 2 <-> a()", "(\\forall x (x > 2)) <-> a()") ,
      ("\\exists x x > 2 & a()", "(\\exists x (x > 2)) & a()") ,
      ("\\exists x x > 2 | a()", "(\\exists x (x > 2)) | a()") ,
      ("\\exists x x > 2 -> a()", "(\\exists x (x > 2)) -> a()") ,
      ("\\exists x x > 2 <-> a()", "(\\exists x (x > 2)) <-> a()") ,
      //nested modalities
      ("< p:=1; > <p:=2; > p>0", "<p:=1;>(<p:=2;>p>0)") ,
      ("[ p:=1; ] <p:=2; > p>0", "[p:=1;](<p:=2;>p>0)") ,
      ("< p:=1; > [p:=2; ] p>0", "<p:=1;>([p:=2;]p>0)") ,
      //[], <>, \forall, \exists magic.
      ("\\forall x [x:=1;]<x:=2;>x>0","\\forall x ([x:=1;]<x:=2;>(x>0))") ,
      ("\\exists x [x:=1;]<x:=2;>x>0","\\exists x ([x:=1;]<x:=2;>(x>0))") ,
      ("[p:=0;]\\forall x [x:=p;] \\exists y [q := x + y; ] q > 0", "[p:=0;](\\forall  x [x:=p;] (\\exists y [q := x + y; ] q > 0))") ,
      // <> vs >.
      ("< ?p>q; > p > 1", "<?(p > q);>(p>1)") ,
      ("[ ?p>q; ] p > 1", "[?(p > q);](p>1)") ,
      ("< ?a(); ++ ?a(); > a()", "< {?a();} ++ {?a();} > a()") ,
      //arith.
      ("p + q * r = s", "p + (q * r) = s") ,
      ("p * q + r = s", "(p * q) + r = s") ,
      ("p - q * r = s", "p - (q * r) = s") ,
      ("p * q - r = s", "(p * q) - r = s") ,
      ("-p + q = s", "(-p) + q = s") ,
      ("p - q - s = 0", "(p-q) - s = 0") ,
      ("p^2 >= 0", "(p^2) >= 0") ,
      ("p^2 + q^2 = s^2", "(p^2) + (q^2) = (s^2)") ,
      ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0") ,
      ("1^2 + 3^2 = s^2", "(1^2) + (3^2) = (s^2)") ,
      ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0"),
      // implicit {} either assumed correctly or rejected
      ("[ p:=1; p:=2; ++ p:=3;] p>0", "[ {p:=1; p:=2;} ++ p:=3;] p>0") ,
      ("[ p:=1; ++ p:=2; p:=3;] p>0", "[ p:=1; ++ {p:=2; p:=3;}] p>0") ,
      ("[ p:=1; p:=2; {p:=3;}*] p>0", "[ p:=1; p:=2; {{p:=3;}*}] p>0") ,
      ("[ p:=1; p:=2; ++ {p:=3;}*] p>0", "[ {p:=1; p:=2;} ++ {{p:=3;}*}] p>0"),

    ("[{x'=1,y'=2,z'=3}]x>0", "[{x'=1,{y'=2,z'=3}}]x>0"),
    ("[{x'=1,y'=2,z'=3&x<5}]x>0", "[{x'=1,{y'=2,z'=3}&x<5}]x>0"),

    //("x() -> [x:=x(x);]x()>x(x,x())", unparseable) //@todo if !LAX

    ("true", "true"),
    ("false", "false")
  )
}
