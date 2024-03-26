/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.UIKeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalatest.BeforeAndAfterAll
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.prop.TableDrivenPropertyChecks._

import scala.collection.immutable
import scala.collection.immutable._

/**
 * Tests the parser on pairs of strings that are expected to parse the same.
 *
 * @author
 *   Andre Platzer
 */
@SummaryTest
class PairParserTests extends AnyFlatSpec with Matchers with BeforeAndAfterAll {
  Configuration.setConfiguration(FileConfiguration)

  private val pp = KeYmaeraXPrettyPrinter
  private lazy val parser = ArchiveParser.exprParser

  private val uipp = if (true) None else Some(new UIKeYmaeraXPrettyPrinter("-7", true))

  override def beforeAll(): Unit = {
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "false",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName,
    ))
  }

  override def afterAll(): Unit = { KeYmaeraXTool.shutdown() }

  private def parseShouldBe(input: String, expr: Expression) = {
    parser.setAnnotationListener((_, _) => {})
    val parse = parser(input)
    if (!(parse == expr)) {
      println(
        "Reparsing" + "\nInput:      " + input + "\nParsed:     " + parse + " @ " + parse.getClass.getSimpleName +
          "\nExpression: " + pp.fullPrinter(parse)
      )
      parse shouldBe expr
    }
  }

  /**
   * `true` has unary negation `-` bind weakly like binary subtraction. `false` has unary negation `-` bind strong just
   * shy of power `^`.
   */
  private val weakNeg: Boolean = Parser.weakNeg

  /**
   * `true` when negative numbers are picked out specially, e.g. `-2*x` is `(-2)*x`. `false` when negative numbers are
   * handled like unary `-`.
   */
  private val numNeg: Boolean = Parser.numNeg

  /** A special swearing string indicating that the other string cannot be parsed. */
  private val unparseable: String = "@#%@*!!!"

  /** Term cases: Left string is expected to parse like the right string parses, or not at all if right==unparseable */
  private val expectedParseTerm: immutable.List[(String, String)] = List(
    // ("x*-y/z", "x*(-(y/z))"),
    ("-x+y", "(-x)+y"),
    ("-x-y", "(-x)-y"),
    ("-x*y", if (!weakNeg) "(-x)*y" else "-(x*y)"),
    ("-x/y", if (!weakNeg) "(-x)/y" else "-(x/y)"),
    ("-x^y", "-(x^y)"),
    ("x+-y", "x+(-y)"),
    ("x--y", "x-(-y)"),
    ("x*-y", "x*(-y)"),
    ("x/-y", "x/(-y)"),
    ("x^-y", "x^(-y)"),
    ("x*-y+z", "(x*(-y))+z"),
    ("x*-y*z", if (!weakNeg) "(x*(-y))*z" else "x*(-(y*z))"),
    ("x*-y*-z*2", if (!weakNeg) "((x*(-y))*(-z))*2" else "x*(-(y*(-z*2)))"),
    ("x*(-y)*(-z)*2", "((x*(-y))*(-z))*2"),
    ("x*(-y)*-z*2", if (!weakNeg) "((x*(-y))*(-z))*2" else "(x*(-y))*(-(z*2))"),
    ("x*-y*(-z)*2", if (!weakNeg) "((x*(-y))*(-z))*2" else "x*(-((y*(-z))*2))"),
    ("x*-y/z", if (!weakNeg) "(x*(-y))/z" else "x*(-(y/z))"),
    ("x-y", "(x)-(y)"),
    ("x+-y", "x+(-y)"),
    ("x^-y/z", "(x^(-y))/z"),
    ("x*z/5az", unparseable),
    ("x+y-a/b+9*x-5abacus", unparseable),
    ("x+y-a/b+9*x-5+", unparseable),
    ("x+y-a/b+9*x-5)", unparseable),
    ("x+y-a/b+(9*x-5", unparseable),
    // from doc/dL-grammar.md or crucially important
    ("x-y-z", "(x-y)-z"),
    ("x/y/z", "(x/y)/z"),
    ("x*22", "x*(22)"),
    ("x*(-22)", "x*(-22)"),
    ("x^22", "x^(22)"),
    ("x^2^4", "x^(2^4)"),
    ("-x^2", "-(x^2)"),

    // full table
    // unary meets unary
    ("-x'", "-(x')"),
    ("-(x)'", "-((x)')"),
    // unary meets binary left
    ("-x+y", "(-x)+y"),
    ("-x-y", "(-x)-y"),
    ("-x*y", if (!weakNeg) "(-x)*y" else "-(x*y)"),
    ("-x/y", if (!weakNeg) "(-x)/y" else "-(x/y)"),
    ("-x^y", "-(x^y)"),
    ("-(2^4)", "-(2^4)"),
    ("- 2^4", "-(2^4)"),
    ("(-2)^4", "(-2)^4"),
    ("(- 2)^4", "(- 2)^4"),
    ("-2^4", "-2^4"),
    ("-2^4", "-(2^4)"),
    // unary meets binary right
    ("x+-y", "x+(-y)"),
    ("x--y", "x-(-y)"),
    ("x*-y", "x*(-y)"),
    ("x/-y", "x/(-y)"),
    ("x^-y", "x^(-y)"),
    // unary meets binary left
    ("x'+y", "(x')+y"),
    ("x'-y", "(x')-y"),
    ("x'*y", "(x')*y"),
    ("x'/y", "(x')/y"),
    ("x'^y", "(x')^y"),
    // unary meets binary right
    ("x+y'", "x+(y')"),
    ("x-y'", "x-(y')"),
    ("x*y'", "x*(y')"),
    ("x/y'", "x/(y')"),
    ("x^y'", "x^(y')"),

    // binary meets binary from left
    ("x+y+z", "(x+y)+z"),
    ("x+y-z", "(x+y)-z"),
    ("x+y*z", "x+(y*z)"),
    ("x+y/z", "x+(y/z)"),
    ("x+y^z", "x+(y^z)"),
    // binary meets binary from right
    ("x+y+z", "(x+y)+z"),
    ("x-y+z", "(x-y)+z"),
    ("x*y+z", "(x*y)+z"),
    ("x/y+z", "(x/y)+z"),
    ("x^y+z", "(x^y)+z"),
    // binary meets binary from left
    ("x-y+z", "(x-y)+z"),
    ("x-y-z", "(x-y)-z"),
    ("x-y*z", "x-(y*z)"),
    ("x-y/z", "x-(y/z)"),
    ("x-y^z", "x-(y^z)"),
    // binary meets binary from right
    ("x+y-z", "(x+y)-z"),
    ("x-y-z", "(x-y)-z"),
    ("x*y-z", "(x*y)-z"),
    ("x/y-z", "(x/y)-z"),
    ("x^y-z", "(x^y)-z"),
    // binary meets binary from left
    ("x*y+z", "(x*y)+z"),
    ("x*y-z", "(x*y)-z"),
    ("x*y*z", "(x*y)*z"),
    ("x*y/z", "(x*y)/z"),
    ("x*y^z", "x*(y^z)"),
    // binary meets binary from right
    ("x+y*z", "x+(y*z)"),
    ("x-y*z", "x-(y*z)"),
    ("x*y*z", "(x*y)*z"),
    ("x/y*z", "(x/y)*z"),
    ("x^y*z", "(x^y)*z"),
    // binary meets binary from left
    ("x/y+z", "(x/y)+z"),
    ("x/y-z", "(x/y)-z"),
    ("x/y*z", "(x/y)*z"),
    ("x/y/z", "(x/y)/z"),
    ("x/y^z", "x/(y^z)"),
    // binary meets binary from right
    ("x+y/z", "x+(y/z)"),
    ("x-y/z", "x-(y/z)"),
    ("x*y/z", "(x*y)/z"),
    ("x/y/z", "(x/y)/z"),
    ("x^y/z", "(x^y)/z"),
    // binary meets binary from left
    ("x^y+z", "(x^y)+z"),
    ("x^y-z", "(x^y)-z"),
    ("x^y*z", "(x^y)*z"),
    ("x^y/z", "(x^y)/z"),
    ("x^y^z", "x^(y^z)"),
    // binary meets binary from right
    ("x+y^z", "x+(y^z)"),
    ("x-y^z", "x-(y^z)"),
    ("x*y^z", "x*(y^z)"),
    ("x/y^z", "x/(y^z)"),
    ("x^y^z", "x^(y^z)"),
    ("-x^y^z", "-(x^(y^z))"),

    // reasonably systematic
    ("x+y+z", "(x+y)+z"),
    ("x-y+z", "(x-y)+z"),
    ("x+y-z", "(x+y)-z"),
    ("x-y-z", "(x-y)-z"),
    // ("x++y", unparseable),  //@todo if statementSemicolon
    ("x*y+z", "(x*y)+z"),
    ("x*y-z", "(x*y)-z"),
    ("x+y*z", "x+(y*z)"),
    ("x-y*z", "x-(y*z)"),
    ("x**y", unparseable),
    ("x/y+z", "(x/y)+z"),
    ("x/y-z", "(x/y)-z"),
    ("x+y/z", "x+(y/z)"),
    ("x-y/z", "x-(y/z)"),
    ("x*y*z", "(x*y)*z"),
    ("x*y/z", "(x*y)/z"),
    ("x/y/z", "(x/y)/z"),
    ("x/y*z", "(x/y)*z"),
    ("x//y", unparseable),
    ("x+y^z", "x+(y^z)"),
    ("x-y^z", "x-(y^z)"),
    ("x^y+z", "(x^y)+z"),
    ("x^y-z", "(x^y)-z"),
    ("x^y*z", "(x^y)*z"),
    ("x^y/z", "(x^y)/z"),
    ("x*y^z", "x*(y^z)"),
    ("x/y^z", "x/(y^z)"),
    ("x^^y", unparseable),
    ("x+y+z", "(x+y)+z"),
    ("x-y-z", "(x-y)-z"),
    ("x*y*z", "(x*y)*z"),
    ("x/y/z", "(x/y)/z"),
    ("x^y^z", "x^(y^z)"),

    // unary minus
    ("-x+y+z", "((-x)+y)+z"),
    ("-x-y+z", "((-x)-y)+z"),
    ("x+-y-z", "(x+(-y))-z"),
    ("x- -y-z", "(x-(-y))-z"),
    ("x+y- -z", "(x+y)-(-z)"),
    ("x-y- -z", "(x-y)-(-z)"),
    ("-x*y+z", if (!weakNeg) "((-x)*y)+z" else "(-(x*y))+z"),
    ("x*-y-z", "(x*(-y))-z"),
    ("x+y*-z", "x+(y*(-z))"),
    ("x-y*-z", "x-(y*(-z))"),
    ("-x/y+z", if (!weakNeg) "((-x)/y)+z" else "(-(x/y))+z"),
    ("x/-y-z", "(x/(-y))-z"),
    ("-x+y/z", "(-x)+(y/z)"),
    ("x-y/-z", "x-(y/(-z))"),
    ("-x*y*z", if (!weakNeg) "((-x)*y)*z" else "-((x*y)*z)"),
    ("x*-y/z", if (!weakNeg) "(x*(-y))/z" else "x*(-(y/z))"), // subtle  (x*(-y))/z
    ("x/y/-z", "(x/y)/(-z)"),
    ("x/y*-z", "(x/y)*(-z)"),
    ("x/-y*z", "(x/-y)*z"),
    ("x/-y_0*z", "(x/-(y_0))*z"),
    ("x/-f()*z", "(x/-(f()))*z"),
    ("x*-/y", unparseable),
    ("-x+y^z", "(-x)+(y^z)"),
    ("-x-y^z", "(-x)-(y^z)"),
    ("x^-y+z", "(x^(-y))+z"),
    ("x^-y-z", "(x^(-y))-z"),
    ("x^y+-z", "(x^y)+(-z)"),
    ("x^y- -z", "(x^y)-(-z)"),

    // more unary minus
    ("x+-y+z", "(x+(-y))+z"),
    ("x- -y-z", "(x-(-y))-z"),
    ("x-y- -z", "(x-y)-(-z)"),
    ("x- -y- -z", "(x-(-y))-(-z)"),
    ("-x- -y- -z", "((-x)-(-y))-(-z)"),
    ("x*-y*z", if (!weakNeg) "(x*(-y))*z" else "x*(-(y*z))"), // subtle (x*(-y))*z
    ("-x*y*z", if (!weakNeg) "((-x)*y)*z" else "-((x*y)*z)"), // subtle ((-x)*y)*z
    ("x*y*-z", "(x*y)*(-z)"),

    // primes
    ("x'+y+z", "(x'+y)+z"),
    ("x+y'+z", "(x+(y'))+z"),
    ("x+y+z'", "(x+y)+(z')"),
    ("x'-y-z", "(x'-y)-z"),
    ("x-y'-z", "(x-(y'))-z"),
    ("x-y-z'", "(x-y)-(z')"),
    ("x'*y*z", "(x'*y)*z"),
    ("x*y'*z", "(x*(y'))*z"),
    ("x*y*z'", "(x*y)*(z')"),
    ("x/-y/z", if (!weakNeg) "(x/(-y))/z" else "x/(-(y/z))"), // subtle "(x/(-y))/z"
    ("x^-y^z", "x^(-(y^z))"),
    ("-x'", "-(x')"),
    ("2'", unparseable),
    ("x+y'", "x+(y')"),
    ("x-y'", "x-(y')"),
    ("x*y'", "x*(y')"),
    ("x/y'", "x/(y')"),
    ("x^2^4'", unparseable),
    ("x^y'", "x^(y')"),
    ("x^2'", unparseable),
    ("(0)'", "(0)'"),
    ("(-0)'", "(-(0))'"),

    // more tests

    ("-x^2", "-(x^2)"),
    ("-x^1", "-(x^1)"),
    ("y+x^2", "y+(x^2)"),
    ("y-x^2", "y-(x^2)"),
    ("y*x^2", "y*(x^2)"),
    ("y/x^2", "y/(x^2)"),
    ("-x*y", if (!weakNeg) "(-x)*y" else "-(x*y)"),
    ("-x*y", if (!weakNeg) "(-x)*y" else "-(x*y)"),
//    ("-3*y", "(-3)*y"), //@note subtle "-(3*y)"),
//    ("-5*(y-z)", "(-5)*(y-z)"), // subtle "-(5*(y-z))"),
    ("-2-3", if (numNeg) "(-2)-(3)" else "(-(2))-(3)"),
//    ("-2*-3", "(-2)*(-3)"),  // subtle "-(2*(-(3)))"),
    ("-2^-3", if (numNeg) "-(2^(-3))" else "-(2^(-(3)))"), // subtle NOT "(-2)^(-3)"
    ("(-8)", "(-8)"),
    (
      "-2*a",
      if (weakNeg && numNeg) unparseable else if (numNeg) "(-2)*a" else if (weakNeg) "-(2*a)" else "(- 2)*a",
    ), // subtle -(2*a)"),
    (
      "-0*a",
      if (weakNeg && numNeg) unparseable else if (numNeg) "(-0)*a" else if (weakNeg) "-(0*a)" else "(- 0)*a",
    ), // subtle "-(0*a)"),
    ("a-3*b", "a-(3*b)"),
    ("-2-3*b", if (numNeg) "(-2)-(3*b)" else "-(2)-(3*b)"),
//    ("-2+-3*b", "(-2)+((-3)*b)"),
    ("-(5*x)", "-(5*x)"),
    ("-(5+x)", "-(5+x)"),
    ("-(5-x)", "-(5-x)"),

    // tuples
//    ("(x,y)", "(x,y)"),
//    ("(x,y,z)", "(x,(y,z))"),
//    ("(a,b,c,d,e)", "(a,(b,(c,(d,e))))"),
//    ("(x,(y,z),a)", "(x,((y,z),a))"),
//    ("((x,y),z,a)", "((x,y),(z,a))"),

    ("a+2*b", "a+(2*b)"),
    ("a+2b+1", unparseable),
    ("a+f(b+1)", "a+(f((b+1)))"),
    ("a+2(b+1)", unparseable),
    ("a+2b+1", unparseable),
    ("x_", "x_"),
    ("x_'", "x_'"),
    ("x_'+1", "x_'+1"),
    ("z2'^4", "(z2')^(4)"),
    (
      "(0)'-0+0*z4*(((z4'^3/z4'/gg()*-83)^2-(0)'-(-45)'-z1)/15)^4",
      "((0)'-0)+(0*z4)*(((((((((((z4')^3)/(z4'))/gg())*(-(83)))^2)-(0)')-((-45)'))-z1)/15)^4)",
    ),
    ("-(2)", "-(2)"),
    ("-(2)", "-(2)"),
    ("(-2)", "(-2)"),
    ("- 2", "-(2)"),
    ("(- 2)", "-(2)"),
    ("-3+x", if (!numNeg) "(-(3))+x" else "(-3)+x"),
    ("-2*x", if (weakNeg && !numNeg) "-(2*x)" else if (!weakNeg && !numNeg) "(- 2)*x" else "(-2)*x"),
    ("-1*x", if (weakNeg && !numNeg) "-(1*x)" else if (!weakNeg && !numNeg) "(- 1)*x" else "(-1)*x"),
    ("-10*x", if (weakNeg && !numNeg) "-(10*x)" else if (!weakNeg && !numNeg) "(- 10)*x" else "(-10)*x"),
    ("0-2*x", "0-(2*x)"),
    ("5'", unparseable),
    ("-5'", unparseable),
    ("2/-3", if (weakNeg || !numNeg) "2/(-(3))" else "2/(-3)"),
    ("2/-3*4", if (weakNeg || !numNeg) "(2/(-(3)))*4" else "(2/(-3))*4)"),
    ("abs(-3)", if (!numNeg) "abs(-(3))" else "abs((-3))"),
    ("001", "1"),
    ("000001", "1"),
    ("00", "0"),
    ("-0", if (numNeg) "0" else "-(0)"),
    ("(-0)", "0"),
    ("m_0", "m_0"),
    // ("m_00", "m_0"),   // @subtle...
    ("m_00", unparseable), // @subtle...
    ("x", "x"),
  )

  /**
   * Formula cases: Left string is expected to parse like the right string parses, or not at all if right==unparseable
   */
  private val expectedParseFormula: immutable.List[(String, String)] = List(
    ("p()->q()->r()", "p()->(q()->r())"),
    // @todo bad error message ("(p() <-> q()) <- (q() -> p()')", "((p()) <-> (q())) <- ((q()) -> ((p())'))"),

    ("-(x+5)^2+9>=7 & y>5 -> [x:=1;]x>=1", "((((-(x+5)^2)+9)>=7) & (y>5)) -> ([x:=1;](x>=1))"),
    ("[x:=1;x:=2;x:=3;]x=3", "[x:=1;{x:=2;x:=3;}]x=3"),
    ("[x:=1;++x:=2;++x:=3;]x=3", "[x:=1;++{x:=2;++x:=3;}]x=3"),
    ("p()->q()<->r()", "(p()->q())<->r()"),
    ("p()<->q()->r()", "p()<->(q()->r())"),
    ("p()->q()<->r()", "(p()->q())<->r()"),
    ("p()<->q()<-r()", unparseable), // could be read as p()<->(q() < -r())

    // prop meet table
    ("p()&q()&r()", "p()&(q()&r())"),
    ("p()&q()|r()", "(p()&q())|r()"),
    ("p()&q()->r()", "(p()&q())->r()"),
    ("p()&q()<->r()", "(p()&q())<->r()"),
    ("!p()&q()", "(!p())&q()"),
    ("p()&q()&r()", "p()&(q()&r())"),
    ("p()|q()&r()", "p()|(q()&r())"),
    ("p()->q()&r()", "p()->(q()&r())"),
    ("p()<->q()&r()", "p()<->(q()&r())"),
    ("p()&!q()", "p()&(!q())"),
    ("p()|q()&r()", "p()|(q()&r())"),
    ("p()|q()|r()", "p()|(q()|r())"),
    ("p()|q()->r()", "(p()|q())->r()"),
    ("p()|q()<->r()", "(p()|q())<->r()"),
    ("!p()|q()", "(!p())|q()"),
    ("p()&q()|r()", "(p()&q())|r()"),
    ("p()|q()|r()", "p()|(q()|r())"),
    ("p()->q()|r()", "p()->(q()|r())"),
    ("p()<->q()|r()", "p()<->(q()|r())"),
    ("p()|!q()", "p()|(!q())"),
    ("p()->q()&r()", "p()->(q()&r())"),
    ("p()->q()|r()", "p()->(q()|r())"),
    ("p()->q()->r()", "p()->(q()->r())"),
    ("p()->q()<->r()", "(p()->q())<->r()"),
    ("!p()->q()", "(!p())->q()"),
    ("p()&q()->r()", "(p()&q())->r()"),
    ("p()|q()->r()", "(p()|q())->r()"),
    ("p()->q()->r()", "p()->(q()->r())"),
    ("p()<->q()->r()", "p()<->(q()->r())"),
    ("p()->!q()", "p()->(!q())"),
    ("p()<->q()&r()", "p()<->(q()&r())"),
    ("p()<->q()|r()", "p()<->(q()|r())"),
    ("p()<->q()->r()", "p()<->(q()->r())"),
    ("p()<->q()<->r()", unparseable),
    ("!p()<->q()", "(!p())<->q()"),
    ("p()&q()<->r()", "(p()&q())<->r()"),
    ("p()|q()<->r()", "(p()|q())<->r()"),
    ("p()<->q()->r()", "p()<->(q()->r())"),
    ("p()<->q()<->r()", unparseable),
    ("p()<->!q()", "p()<->(!q())"),
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
    ("\\forallx (x>0)", unparseable),
    ("\\forallx(x>0)", unparseable),
    ("\\forallx1>0", unparseable),
    ("\\existsx (x>0)", unparseable),
    ("\\existsx(x>0)", unparseable),
    ("\\existsx1>0", unparseable),
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
    ("\\forall p(x())", "\\forall p (x())"), // @todo not a great test on string level
    ("\\forall x p(x)", "\\forall x (p(x))"),
    ("\\for all x p(x)", unparseable),
    ("\\ex ists x p(x)", unparseable),
    ("\\exist s x p(x)", unparseable),
    ("[x:=1;x:=2;++x:=3;]x>=5", "[{x:=1;x:=2;}++{x:=3;}]x>=5"),
    ("<x:=1;x:=2;++x:=3;>x>5", "<{x:=1;x:=2;}++{x:=3;}>x>5"),
    ("[x:=1;++x:=2;x:=3;]x^2>4", "[x:=1;++{x:=2;x:=3;}]x^2>4"),
    ("<x:=1;++x:=2;x:=3;>x^2>4", "<x:=1;++{x:=2;x:=3;}>x^2>4"),
    ("[x:=1;++x:=2;++x:=3;]x>5", "[x:=1;++{x:=2;++x:=3;}]x>5"),
    ("<x:=1;++x:=2;++x:=3;>x>5", "<x:=1;++{x:=2;++x:=3;}>x>5"),
    ("[x:=1;?x>0&x^2>5;{x'=5}]x+y>99", "[x:=1;{?((x>0)&((x^2)>5));{x'=5}}]x+y>99"),
    ("<x:=1;?x>0&x^2>5;{x'=5}>x+y>99", "<x:=1;{?((x>0)&((x^2)>5));{x'=5}}>x+y>99"),
    ("[x:=1;?x<0&x^2>5;{x'=5}]x+y>99", "[x:=1;{?((x<0)&((x^2)>5));{x'=5}}]x+y>99"),
    ("<x:=1;?x<0&x^2>5;{x'=5}>x+y>99", "<x:=1;{?((x<0)&((x^2)>5));{x'=5}}>x+y>99"),

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
    ("! p = 0 & p = 5", "(!(p=0)) & (p=5)"),
    ("! p > 0 | p < 5", "(!(p>0)) | (p<5)"),
    ("! p > 0 -> p > 5", "(!(p>0)) -> (p>5)"),
    ("! p > 0 <-> p > 5", "(!(p>0)) <-> (p>5)"),
    // quantifiers do not bind logical connectives but do bind inequalities.
    ("! \\forall x x > 0 | p < 5", "(!(\\forall x x>0)) | (p<5)"),
    ("! \\exists x x > 0 | p < 5", "(!(\\exists x x>0)) | (p<5)"),
    ("! \\forall x [p:=x;]p >= x | p < 5", "(!(\\forall x ([p:=x;](p>=x)))) | (p<5)"),
    // quantifiers with multiple variables
    // ("\\forall x, y . (y > x -> y > x)", "\\forall x, y . (y > x -> y > x)") ,
    // ("\\exists y, x . (y > x -> y > x)", "\\exists y, x . (y > x -> y > x)") ,
    // modalities do not bind logical connectives.
    ("[p:=1;] p>0 & p < 1", "([p:=1;](p>0)) & (p<1)"),
    ("[p:=1;] p>0 | p < 1", "([p:=1;](p>0)) | (p<1)"),
    ("[p:=1;] p>0 -> p < 1", "([p:=1;](p>0)) -> (p<1)"),
    ("<p:=1;> p>0 & p < 1", "(<p:=1;>(p>0)) & (p<1)"),
    ("<p:=1;> p>0 | p < 1", "(<p:=1;>(p>0)) | (p<1)"),
    ("<p:=1;> p>0 -> p < 1", "(<p:=1;>(p>0)) -> (p<1)"),
    ("\\forall x x > 2 & a()", "(\\forall x (x > 2)) & a()"),
    ("\\forall x x > 2 | a()", "(\\forall x (x > 2)) | a()"),
    ("\\forall x x > 2 -> a()", "(\\forall x (x > 2)) -> a()"),
    ("\\forall x x > 2 <-> a()", "(\\forall x (x > 2)) <-> a()"),
    ("\\exists x x > 2 & a()", "(\\exists x (x > 2)) & a()"),
    ("\\exists x x > 2 | a()", "(\\exists x (x > 2)) | a()"),
    ("\\exists x x > 2 -> a()", "(\\exists x (x > 2)) -> a()"),
    ("\\exists x x > 2 <-> a()", "(\\exists x (x > 2)) <-> a()"),
    // nested modalities
    ("< p:=1; > <p:=2; > p>0", "<p:=1;>(<p:=2;>p>0)"),
    ("[ p:=1; ] <p:=2; > p>0", "[p:=1;](<p:=2;>p>0)"),
    ("< p:=1; > [p:=2; ] p>0", "<p:=1;>([p:=2;]p>0)"),
    // [], <>, \forall, \exists magic.
    ("\\forall x [x:=1;]<x:=2;>x>0", "\\forall x ([x:=1;]<x:=2;>(x>0))"),
    ("\\exists x [x:=1;]<x:=2;>x>0", "\\exists x ([x:=1;]<x:=2;>(x>0))"),
    (
      "[p:=0;]\\forall x [x:=p;] \\exists y [q := x + y; ] q > 0",
      "[p:=0;](\\forall  x [x:=p;] (\\exists y [q := x + y; ] q > 0))",
    ),
    // <> vs >.
    ("< ?p>q; > p > 1", "<?(p > q);>(p>1)"),
    ("[ ?p>q; ] p > 1", "[?(p > q);](p>1)"),
    ("< ?a(); ++ ?a(); > a()", "< {?a();} ++ {?a();} > a()"),
    // arith.
    ("p + q * r = s", "p + (q * r) = s"),
    ("p * q + r = s", "(p * q) + r = s"),
    ("p - q * r = s", "p - (q * r) = s"),
    ("p * q - r = s", "(p * q) - r = s"),
    ("-p + q = s", "(-p) + q = s"),
    ("p - q - s = 0", "(p-q) - s = 0"),
    ("p^2 >= 0", "(p^2) >= 0"),
    ("p^2 + q^2 = s^2", "(p^2) + (q^2) = (s^2)"),
    ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0"),
    ("1^2 + 3^2 = s^2", "(1^2) + (3^2) = (s^2)"),
    ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0"),
    // implicit {} either assumed correctly or rejected
    ("[ p:=1; p:=2; ++ p:=3;] p>0", "[ {p:=1; p:=2;} ++ p:=3;] p>0"),
    ("[ p:=1; ++ p:=2; p:=3;] p>0", "[ p:=1; ++ {p:=2; p:=3;}] p>0"),
    ("[ p:=1; p:=2; {p:=3;}*] p>0", "[ p:=1; p:=2; {{p:=3;}*}] p>0"),
    ("[ p:=1; p:=2; ++ {p:=3;}*] p>0", "[ {p:=1; p:=2;} ++ {{p:=3;}*}] p>0"),

    // ("x() -> [x:=x(x);]x()>x(x,x())", unparseable) //@todo if !LAX

    // more tests

    ("p(x)>0->[x:=0;{x'=2}x:=x+1;\n{y'=x&\nx<   2}]x<=5", "p(x)>0->[x:=0;{{x'=2}{x:=x+1;{y'=x&(x<2)}}}](x<=5)"),
    (
      "abs(f()) = g() <->  f()>=0 & g()=f() | f()<=0 & g()=-f()",
      "(abs(f()) = g()) <->  ((f()>=0 & g()=f()) | (f()<=0 & g()=-f()))",
    ),
    (
      "max(f(),g())=h()<->f()>=g()&h()=f()|f()<=g()&h()=g()",
      "(max(f(),g())=h()) <-> ((f()>=g() & h()=f()) | (f()<=g() & h()=g()))",
    ),
    (
      "max(f(), g()) = h() <-> f()>=g() & h()=f() | f()<=g() & h()=g()",
      "(max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<=g() & h()=g()))",
    ),
    ("-(5*x)<=0", "-(5*x)<=0"),
    ("m_0<=1", "(m_0)<=1"),
//    ("-0*m/a<=0*(tl-to)", "(((-0)*(m))/(a))<=0*(tl-to)"), // subtle "-(((0)*(min_0))/(a))<=0*(tl-to)"),
    ("-o*m/a<=0*(tl-to)", if (weakNeg) "-((o*m)/(a))<=0*(tl-to)" else "(((-o)*m)/(a))<=0*(tl-to)"),
    ("-o*m_0/a<=0*(tl-to)", if (weakNeg) "-((o*(m_0))/(a))<=0*(tl-to)" else "((-o)*m_0)/a<=0*(tl-to)"),
    ("-o*min_0/a<=0*(tl-to)", if (weakNeg) "-((o*(min_0))/(a))<=0*(tl-to)" else "((-o)*min_0)/a<=0*(tl-to)"),
    ("-(0*min_0/a)<=0*(tl-to)", "-((0*(min_0))/(a))<=0*(tl-to)"),
    ("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;} ]x>=1", unparseable),
    ("x + y*z + 3*(x+y)  >=  3+x+7", "((x+(y*z))+(3*(x+y)))>=((3+x)+7)"),
    (
      "x + y*z + 3*(x+y) >= 3+x+7  &  x+1 < 2   ->   x^2 >= (x-1)^2  |  5 > 1",
      "((((x+(y*z))+(3*(x+y)))>=((3+x)+7))&((x+1)<2))->((x^2)>=(((x-1)^2))|(5>1))",
    ),
    (
      "2 + 3*x >= 2   ->   [{x:=x+1; x:=2*x;   ++  x:=0;}*] 3*x >= 0",
      "((2+(3*x))>=2)->([{{x:=(x+1);x:=(2*x);}++{x:=0;}}*]((3*x)>=0))",
    ),
    ("p()<-q()", unparseable), // could be read as p() < -q()
    ("p()< -q()", "(p()) < (-(q()))"),
    ("true", "true"),
    ("false", "false"),

    // @note hybrid games
    ("<{x:=x+1;{x'=1}^@ ++ x:=x-1;}*>(0<=x&x<1)", "<{x:=x+1;{x'=1}^@ ++ x:=x-1;}*> (0<=x&x<1)"),
    ("<{{x:=x+1;{x'=1}^@ ++ x:=x-1;}^@}*^@>(0<=x&x<1)", "<{{{{x:=x+1;{{x'=1}^@}} ++ {x:=x-1;}}^@}*}^@> (0<=x&x<1)"),

    // random
    ("!([{{z1:=0;}*}*]true)'", "!(([{{z1:=0;}*}*](true))')"),
    (
      "<{{?true;{?true;++?true;}++{?true;}*?true;}++{z2:=0;++?true;?true;}?true;}*>[?true;{{?true;?true;}*++z2:=z3';}][z3:=*;]true",
      "<{{{{?true;}{{?true;}++{?true;}}}++{{{?true;}*}{?true;}}}++{{{z2:=0;}++{{?true;}{?true;}}}{?true;}}}*>([{?true;}{{{{?true;}{?true;}}*}++{z2:=z3';}}]([z3:=*;](true)))",
    ),
    // ("?0=(96*(z7+(z5-22+z2-((0*((((z3+-1+(0/0-(0)'))/(z6+0))'^0)'*69))')')'+(0)'))^4+z2;", "?(0=((96*(z7+(z5-22+z2-((0*((((z3+-1+(0/0-(0)'))/(z6+0))'^0)'*69))')')'+(0)'))^4+z2));"),
    (
      "\\exists z2 \\exists z4 <{z2:=*;}*>z2*17+0!=51^2",
      "\\exists z2 (\\exists z4 (<{z2:=*;}*>(((z2*17)+0)!=(51^2))))",
    ),
    (
      "[z3:=*;{{?true;++?true;}*z3:=z3;}{{?true;++?true;}*++{z2:=z2;}*}]<?[z1:=(0)';]PP{\\forall z3 true};>\\exists z2 \\forall z3 [?true;++?true;]<?true;>true",
      "[{z3:=*;}{{{{{?true;}++{?true;}}*}{z3:=z3;}}{{{{?true;}++{?true;}}*}++{{z2:=z2;}*}}}](<?[z1:=(0)';](PP{\\forall z3 (true)});>(\\exists z2 (\\forall z3 ([{?true;}++{?true;}](<?true;>(true))))))",
    ),
    ("(x)'=16", "((x)')=16"),
    ("(f())'=16", "((f())')=16"),
    ("(f(x))'=16", "((f(x))')=16"),
    ("\\exists z1 p()", "\\exists z1 (p())"),
    ("\\exists z1 gg()>=0", "\\exists z1 ((gg())>=0)"),
    ("\\exists z1 gg()+f()>=0", "\\exists z1 ((gg()+f())>=0)"),
    ("\\exists z1 (gg())'>=0", "\\exists z1 (((gg())')>=0)"),
    ("\\exists z1 (gg())'>=(0)'/(0)'", "\\exists z1 ((gg())'>=(((0)')/((0)')))"),
    (
      "\\forall z2 (gg())'+96+((ff(z3')+(gg()^0*82)')*(gg())'-0) < 0",
      "\\forall z2 ((((gg())')+96+((ff(z3')+((gg()^0)*82)')*((gg())')-0)) < 0)",
    ),
    ("[x:=0;]p()", "[x:=0;](p())"),
    ("[x:=0;]f()=16", "[x:=0;]((f())=16)"),
    ("<x:=0;>f()=16", "<x:=0;>((f())=16)"),
    ("[x:=0;](f())=16", "[x:=0;]((f())=16)"),
    ("<x:=0;>(f())=16", "<x:=0;>((f())=16)"),
    ("[x:=0;](f(x))=16", "[x:=0;]((f(x))=16)"),
    ("<x:=0;>(f(x))=16", "<x:=0;>((f(x))=16)"),
    ("[x:=0;](f(x))'=16", "[x:=0;](((f(x))')=16)"),
    ("<x:=0;>(f(x))'=16", "<x:=0;>(((f(x))')=16)"),
    (
      "\\exists z5 (z1'^5 < z1'<->\\exists z3 <?true;>\\exists z7 (gg())'^4>0-z2')",
      "\\exists z5 ((((z1')^5) < z1') <-> (\\exists z3 (<?true;>(\\exists z7 ((((gg())')^4)>(0-(z2')))))))",
    ),
    (
      "[{{?true;?true;}{?true;++?true;}}?true|true;](ff(0))'=16",
      "[{{?true;?true;}{?true;++?true;}}?(true|true);]((ff(0))'=16)",
    ),
    // ("{?true;}*++{z3'=45&true}++{{{z1:=-85/-94;++?true;{{?true;++z5:=*;}++z6:=*;}}++{{{{?true;++z2:=*;}*++z3:=*;}{{{{{{z7'=0&false}z1:=*;}?0*0*(0+0)<=z6;++z7:=*;++?[{?true;}*?true;?true;][{?true;}*][?true;]true;}++z4:=pp(-58);}{z5:=z5;}*z6:=((0--25)*z4')';}{{{z5:=((0)')';}*++?true;++{{z4'=0*0&\\exists z6 true}++{z7'=0,z3'=0&true}{?true;++?true;}}*}++z5:=pp(96);}*}{{{?true;}*++{{z3'=0&\\exists z2 <?true|true;>\\forall z7 [?true;]true}}*}*}*}{{{?true;}*}*++{{{{?true;++z6:=*;++?!true;}++{z7:=(0^5)^3+(0+0)^3;}*}++{{z4:=*;++?true;}*}*{{z6:=*;}*}*}{{?false;++{{?true;++?true;}{?true;++?true;}}?true;{?true;++?true;}++z4:=qq();}{z1:=z1;{{?true;}*z4:=0;++{?true;++?true;}++?true;?true;}}{{?true;}*++?true;{?true;}*}*}*}{{z1'=0&!\\forall z3 \\forall z6 ((true)')'}?<{?true;{?true;}*++{?true;++?true;}++?true;?true;}?true;>\\exists z1 <z4:=z4;{?true;++?true;}>-91!=0+0;}?true;}?[{{z1:=(z1)'^1;++?true;++{z3'=0,z2'=0&PP{true}}{?true;?true;++?true;++?true;}*}{{{{?true;}*?true;?true;}*{{{?true;}*}*}*++?true;}++{{z1'=0&\\forall z4 true}++z4:=z2';}{z3'=z4&true}++z6:=0;++{{?true;++?true;}++{?true;}*}++{{?true;}*}*}}*]\\forall z6 \\exists z4 \\exists z6 \\forall z1 \\forall z2 ((true|true)&z5'>=z2');++{{z5:=*;++{?\\forall z4 <?true;><{{z3:=z3;}*}*>((\\forall z3 true)'|<{?true;}*>qq());}*}*++?\\forall z5 0+0--20^0*72<=-49;}{z7:=*;}*}{{{z3:=0-z4-((z2)')'*z6';++{z5'=79&<{{{?true;}*++{{?<?true;>true;{?true;?true;++?true;?true;}}*}*}++?true;z4:=pp(0*0+0/0)+-29;}++{z7:=*;++{{?<?true;>true;}*{?true;++?true;}*{?true;++?true;}?true;}{{?true;{?true;}*++{{?true;}*}*}++{z6'=0&true}?true;?true;++{?true;++?true;}*}}?true;{?true;?true;++?true;}>true}}++{{{{{{{{z7:=0;}*}*}*++{?true;}*}*++{{{{?true;}*++?true;?true;}++?true;}++?<z3:=z3;>(true<->true);}*++{{{?true;}*z3:=z3;}{?true;}*{?true;}*}*?true;}++{{{?true;++{z6:=0;}*{z2:=*;++{?true;}*}}?true;{{?true;?true;++{?true;}*}++{?true;?true;}*}}{?true;{{?true;++?true;}*++?false;}}?true;}z6:=*;}++?true;}{{{{{{z1:=*;}*}*}*{?true;++z4:=0+0;}*++z4:=z7^1;{z5:=18;++z7:=z5';}}{{z4:=*;}*}*++{{{{{?true;++?true;}++{?true;}*}++{?true;?true;}*}{?true;++?true;}*{?true;++?true;}?true;?true;++{z7'=0&[z6:=0;]\\exists z4 true}++{?true;++?true;}*{?true;++?true;++?true;}}++{?0>=0;{z7'=0,z2'=0&0 < 0}++{{?true;}*++?true;++?true;}++?true;}z6:=*;}?<{{?0<=0;}*}*>true;}++{{{{{z6'=1&0 < -43}}*}*}*++{{?true;?true;}*?true;}*{{?true;?true;}*++?true;++?true;?true;}{?true;}*++{z1:=*;}*++?true;}*}}*}++z7:=*;}}{?true;}*}*{{?\\exists z5 pp(z1/-74+((-4)')'/0);++{{{{{{{{{?true;++?true;}?true;?true;++{{?true;}*}*}++{?true;?true;}z4:=0;++{?true;?true;}*}*z2:=z3';z5:=*;++{{z6:=*;++{{?true;}*}*}*++{{?true;++?true;}*}*++{z2'=0&[?true;]true|<?true;>true}}{{{{?true;++?true;}z5:=*;}{z3:=0;}*}z4:=*;++{?true;?true;++z5:=0;}*++z4:=0+0;{z5:=*;++?true;}}}{{z2:=*;}*++z7:=0;}}{{{{{{z7'=0&true}++{?true;}*}?true;}{z3:=0;++?true;}}?true;}*++?true;}z2:=z2;}*++z5:=*;++{{{z1:=(75)'^1;}*++{{z7:=*;++{z5:=z5;}*++z7:=0-0;}{{z3:=z3;}*{{z7'=0&true}++?true;}}{{{z6'=0&true}}*}*}{{{z3'=0/0+0/0&!true}}*}*}{?true;++?\\exists z1 <{?true;++?true;}{?true;++?true;}++?true;>0*0-(0-0)!=z4';}}z3:=z3;}{?true;}*}*}*}*}*","{?true;}*++{z3'=45&true}++{{{z1:=-85/-94;++?true;{{?true;++z5:=*;}++z6:=*;}}++{{{{?true;++z2:=*;}*++z3:=*;}{{{{{{z7'=0&false}z1:=*;}?0*0*(0+0)<=z6;++z7:=*;++?[{?true;}*?true;?true;][{?true;}*][?true;]true;}++z4:=pp(-58);}{z5:=z5;}*z6:=((0--25)*z4')';}{{{z5:=((0)')';}*++?true;++{{z4'=0*0&\\exists z6 true}++{z7'=0,z3'=0&true}{?true;++?true;}}*}++z5:=pp(96);}*}{{{?true;}*++{{z3'=0&\\exists z2 <?true|true;>\\forall z7 [?true;]true}}*}*}*}{{{?true;}*}*++{{{{?true;++z6:=*;++?!true;}++{z7:=(0^5)^3+(0+0)^3;}*}++{{z4:=*;++?true;}*}*{{z6:=*;}*}*}{{?false;++{{?true;++?true;}{?true;++?true;}}?true;{?true;++?true;}++z4:=qq();}{z1:=z1;{{?true;}*z4:=0;++{?true;++?true;}++?true;?true;}}{{?true;}*++?true;{?true;}*}*}*}{{z1'=0&!\\forall z3 \\forall z6 ((true)')'}?<{?true;{?true;}*++{?true;++?true;}++?true;?true;}?true;>\\exists z1 <z4:=z4;{?true;++?true;}>-91!=0+0;}?true;}?[{{z1:=(z1)'^1;++?true;++{z3'=0,z2'=0&PP{true}}{?true;?true;++?true;++?true;}*}{{{{?true;}*?true;?true;}*{{{?true;}*}*}*++?true;}++{{z1'=0&\\forall z4 true}++z4:=z2';}{z3'=z4&true}++z6:=0;++{{?true;++?true;}++{?true;}*}++{{?true;}*}*}}*]\\forall z6 \\exists z4 \\exists z6 \\forall z1 \\forall z2 ((true|true)&z5'>=z2');++{{z5:=*;++{?\\forall z4 <?true;><{{z3:=z3;}*}*>((\\forall z3 true)'|<{?true;}*>qq());}*}*++?\\forall z5 0+0--20^0*72<=-49;}{z7:=*;}*}{{{z3:=0-z4-((z2)')'*z6';++{z5'=79&<{{{?true;}*++{{?<?true;>true;{?true;?true;++?true;?true;}}*}*}++?true;z4:=pp(0*0+0/0)+-29;}++{z7:=*;++{{?<?true;>true;}*{?true;++?true;}*{?true;++?true;}?true;}{{?true;{?true;}*++{{?true;}*}*}++{z6'=0&true}?true;?true;++{?true;++?true;}*}}?true;{?true;?true;++?true;}>true}}++{{{{{{{{z7:=0;}*}*}*++{?true;}*}*++{{{{?true;}*++?true;?true;}++?true;}++?<z3:=z3;>(true<->true);}*++{{{?true;}*z3:=z3;}{?true;}*{?true;}*}*?true;}++{{{?true;++{z6:=0;}*{z2:=*;++{?true;}*}}?true;{{?true;?true;++{?true;}*}++{?true;?true;}*}}{?true;{{?true;++?true;}*++?false;}}?true;}z6:=*;}++?true;}{{{{{{z1:=*;}*}*}*{?true;++z4:=0+0;}*++z4:=z7^1;{z5:=18;++z7:=z5';}}{{z4:=*;}*}*++{{{{{?true;++?true;}++{?true;}*}++{?true;?true;}*}{?true;++?true;}*{?true;++?true;}?true;?true;++{z7'=0&[z6:=0;]\\exists z4 true}++{?true;++?true;}*{?true;++?true;++?true;}}++{?0>=0;{z7'=0,z2'=0&0 < 0}++{{?true;}*++?true;++?true;}++?true;}z6:=*;}?<{{?0<=0;}*}*>true;}++{{{{{z6'=1&0 < -43}}*}*}*++{{?true;?true;}*?true;}*{{?true;?true;}*++?true;++?true;?true;}{?true;}*++{z1:=*;}*++?true;}*}}*}++z7:=*;}}{?true;}*}*{{?\\exists z5 pp(z1/-74+((-4)')'/0);++{{{{{{{{{?true;++?true;}?true;?true;++{{?true;}*}*}++{?true;?true;}z4:=0;++{?true;?true;}*}*z2:=z3';z5:=*;++{{z6:=*;++{{?true;}*}*}*++{{?true;++?true;}*}*++{z2'=0&[?true;]true|<?true;>true}}{{{{?true;++?true;}z5:=*;}{z3:=0;}*}z4:=*;++{?true;?true;++z5:=0;}*++z4:=0+0;{z5:=*;++?true;}}}{{z2:=*;}*++z7:=0;}}{{{{{{z7'=0&true}++{?true;}*}?true;}{z3:=0;++?true;}}?true;}*++?true;}z2:=z2;}*++z5:=*;++{{{z1:=(75)'^1;}*++{{z7:=*;++{z5:=z5;}*++z7:=0-0;}{{z3:=z3;}*{{z7'=0&true}++?true;}}{{{z6'=0&true}}*}*}{{{z3'=0/0+0/0&!true}}*}*}{?true;++?\\exists z1 <{?true;++?true;}{?true;++?true;}++?true;>0*0-(0-0)!=z4';}}z3:=z3;}{?true;}*}*}*}*}*"),
    ("-69=0", "-69=0"),
    ("\\forall z3 <{?true;++z3:=z3;}*>-67>=1", "\\forall z3 (<{{?true;}++{z3:=z3;}}*>((-(67))>=1))"),
    ("P{z'=1}", "(P{((z')=1)})"),
    ("\\exists x P{z'=1}", "\\exists x (P{((z')=1)})"),
    ("(z4*z7)^2+z5'^3*z5'<=56", "((z4*z7)^2)+(((z5')^3)*(z5'))<=56"),
    // @todo add unambiguous brackets
    // ("[{z5'=0&0/z5!=z2'+((z1*z2)'-z7)}]([{{{z7:=z7;?true;++z4:=0+(z6/(0+30/42-(85-64))^4)'-z4';}{?false;{{{z2:=z2;{{z7'=0&<z2:=*;>qq()}++z2:=z2;}{z7:=*;++z7:=z7;}*}{{z5'=0,z3'=0-(0+(0+0)+2)-38&<{z2:=z3;}*>true}}*}z4:=*;}z4:=gg()/(-35-((z3+0*0)*0+ff(z1'))*0)*(0-26/(gg()/z3'))+-87;}{{z7:=*;z7:=*;z7:=z1--92;}*++{{?true;z2:=*;}*{{z3:=*;++{z4'=0&86+0=z2+z2}}++z7:=z3/((gg()+(0*0)^3)/((0-0)*(0)'*-16)-77);}*}*}}*++{?true;}*{?true;++{z6'=0&[{?true;}*]\\exists z3 PP{z1'=z5}}}*}*](!(\\forall z1 (38*z6-4)/(91+0)-0 < (z5+80+(z3-0))*-28/0+z3->true)'|\\forall z7 \\exists z7 \\forall z3 [z1:=z1;++{z7'=0&<z1:=*;++{z4:=*;++z5:=*;++z6:=*;}{?<{z4'=0&true}>(true&true);++?z7'>0-0;}*++{{?\\exists z6 true;}*{{?true;}*}*?true;}*++{z4:=*;{{?true;++?true;}++?true;?true;}*}*><{?true;++{{{?true;?true;}*}*}*{{?true;?true;}?true;++?true;z7:=z7;}{?true;?true;++{?true;}*}*}++{{z3:=-11;{{?true;}*++{?true;}*}++z7:=z7;}z1:=*;}{{z5:=0/0-z1';++?(0)'=0-0;}++z3:=z3;}><{{?true;}*{?\\forall z2 0<=0;}*}*>\\forall z5 \\forall z6 (true)'}?true;](73)'<=ff(z3+-66))&(\\exists z3 <{z5:=*;?true;++?true;}{{z5:=*;++{z1'=0&17+z3 < ((0*61)^1)'}{z4:=*;{{z2:=24;++{{?true;}*++?true;++?true;}++z5:=*;++{?true;}*}{{z3'=74&[?true;++?true;]true}}*++z5:=*;}?0>z3'*0/(-71*z7');?true;++z1:=z3'+0;}}++{z2:=(ff(z1))';++z6:=-46;}?true;++{{z5:=0;}*}*}*++{{z5'=63/0&\\exists z7 true}++z5:=*;z1:=*;}{z7:=z2';++{z6:=z7^5*(z4/0);++{{{{?true;}*++{{?true;z2:=z2;++{?true;++?true;}{?true;++?true;}}++{{?true;++?true;}*}*}++{z7'=0&0^5-(0+0) < -70}}++{{?true;{?true;}*++{{?true;++?true;}?true;?true;}*}++{?true;?true;++?true;}{{?true;}*++?true;?true;}++?true;++{z2'=0-0&\\forall z7 true}}*}++{?true;++{{z6'=0,z5'=0,z2'=0&[{?true;}*]<?true;>true}{{z2'=0&true}?true;?true;}*}*}{z5:=*;}*z4:=*;{{?true;++?true;?true;}{{z5'=0&true}}*++{?true;?true;}*++{{?true;}*}*}}++{{{{{{?true;}*}*++z6:=z6;}*}*++z3:=*;}{{{z5'=0&true}++z4:=0;}*{{z6'=0,z1'=0&true}?true;}*++{{z2:=0;}*}*++{{?true;}*}*{?true;}*{?true;}*}*}*}*++z3:=*;}>qq()|<{{?<?0 < 0*ff(z4')*(ff((z4'+z6-z4')*((z4)'+z3')+z4)/(0+ff(0+0)*(75/z1')/0+0+z6'));++{z6:=z6;}*>\\exists z7 qq();}*}*>[?true;](pp(gg())&<?true;>57<=z3)))", "[{z5'=0&0/z5!=z2'+((z1*z2)'-z7)}]([{{{z7:=z7;?true;++z4:=0+(z6/(0+30/42-(85-64))^4)'-z4';}{?false;{{{z2:=z2;{{z7'=0&<z2:=*;>qq()}++z2:=z2;}{z7:=*;++z7:=z7;}*}{{z5'=0,z3'=0-(0+(0+0)+2)-38&<{z2:=z3;}*>true}}*}z4:=*;}z4:=gg()/(-35-((z3+0*0)*0+ff(z1'))*0)*(0-26/(gg()/z3'))+-87;}{{z7:=*;z7:=*;z7:=z1--92;}*++{{?true;z2:=*;}*{{z3:=*;++{z4'=0&86+0=z2+z2}}++z7:=z3/((gg()+(0*0)^3)/((0-0)*(0)'*-16)-77);}*}*}}*++{?true;}*{?true;++{z6'=0&[{?true;}*]\\exists z3 PP{z1'=z5}}}*}*](!(\\forall z1 (38*z6-4)/(91+0)-0 < (z5+80+(z3-0))*-28/0+z3->true)'|\\forall z7 \\exists z7 \\forall z3 [z1:=z1;++{z7'=0&<z1:=*;++{z4:=*;++z5:=*;++z6:=*;}{?<{z4'=0&true}>(true&true);++?z7'>0-0;}*++{{?\\exists z6 true;}*{{?true;}*}*?true;}*++{z4:=*;{{?true;++?true;}++?true;?true;}*}*><{?true;++{{{?true;?true;}*}*}*{{?true;?true;}?true;++?true;z7:=z7;}{?true;?true;++{?true;}*}*}++{{z3:=-11;{{?true;}*++{?true;}*}++z7:=z7;}z1:=*;}{{z5:=0/0-z1';++?(0)'=0-0;}++z3:=z3;}><{{?true;}*{?\\forall z2 0<=0;}*}*>\\forall z5 \\forall z6 (true)'}?true;](73)'<=ff(z3+-66))&(\\exists z3 <{z5:=*;?true;++?true;}{{z5:=*;++{z1'=0&17+z3 < ((0*61)^1)'}{z4:=*;{{z2:=24;++{{?true;}*++?true;++?true;}++z5:=*;++{?true;}*}{{z3'=74&[?true;++?true;]true}}*++z5:=*;}?0>z3'*0/(-71*z7');?true;++z1:=z3'+0;}}++{z2:=(ff(z1))';++z6:=-46;}?true;++{{z5:=0;}*}*}*++{{z5'=63/0&\\exists z7 true}++z5:=*;z1:=*;}{z7:=z2';++{z6:=z7^5*(z4/0);++{{{{?true;}*++{{?true;z2:=z2;++{?true;++?true;}{?true;++?true;}}++{{?true;++?true;}*}*}++{z7'=0&0^5-(0+0) < -70}}++{{?true;{?true;}*++{{?true;++?true;}?true;?true;}*}++{?true;?true;++?true;}{{?true;}*++?true;?true;}++?true;++{z2'=0-0&\\forall z7 true}}*}++{?true;++{{z6'=0,z5'=0,z2'=0&[{?true;}*]<?true;>true}{{z2'=0&true}?true;?true;}*}*}{z5:=*;}*z4:=*;{{?true;++?true;?true;}{{z5'=0&true}}*++{?true;?true;}*++{{?true;}*}*}}++{{{{{{?true;}*}*++z6:=z6;}*}*++z3:=*;}{{{z5'=0&true}++z4:=0;}*{{z6'=0,z1'=0&true}?true;}*++{{z2:=0;}*}*++{{?true;}*}*{?true;}*{?true;}*}*}*}*++z3:=*;}>qq()|<{{?<?0 < 0*ff(z4')*(ff((z4'+z6-z4')*((z4)'+z3')+z4)/(0+ff(0+0)*(75/z1')/0+0+z6'));++{z6:=z6;}*>\\exists z7 qq();}*}*>[?true;](pp(gg())&<?true;>57<=z3)))"),
    //    ("[{z5'=0&0/z5!=z2+((z1*z2)-z7)}]([{{{z7:=z7;?true;++z4:=0+(z6/(0+30/42-(85-64))^4)'-z4';}{?false;{{{z2:=z2;{{z7'=0&<z2:=*;>qq()}++z2:=z2;}{z7:=*;++z7:=z7;}*}{{z5'=0,z3'=0-(0+(0+0)+2)-38&<{z2:=z3;}*>true}}*}z4:=*;}z4:=gg()/(-35-((z3+0*0)*0+ff(z1'))*0)*(0-26/(gg()/z3'))+-87;}{{z7:=*;z7:=*;z7:=z1--92;}*++{{?true;z2:=*;}*{{z3:=*;++{z4'=0&86+0=z2+z2}}++z7:=z3/((gg()+(0*0)^3)/((0-0)*(0)'*-16)-77);}*}*}}*++{?true;}*{?true;++{z6'=0&[{?true;}*]\\exists z3 PP{z1'=z5}}}*}*](!(\\forall z1 (38*z6-4)/(91+0)-0 < (z5+80+(z3-0))*-28/0+z3->true)'|\\forall z7 \\exists z7 \\forall z3 [z1:=z1;++{z7'=0&<z1:=*;++{z4:=*;++z5:=*;++z6:=*;}{?<{z4'=0&true}>(true&true);++?z7'>0-0;}*++{{?\\exists z6 true;}*{{?true;}*}*?true;}*++{z4:=*;{{?true;++?true;}++?true;?true;}*}*><{?true;++{{{?true;?true;}*}*}*{{?true;?true;}?true;++?true;z7:=z7;}{?true;?true;++{?true;}*}*}++{{z3:=-11;{{?true;}*++{?true;}*}++z7:=z7;}z1:=*;}{{z5:=0/0-z1';++?(0)'=0-0;}++z3:=z3;}><{{?true;}*{?\\forall z2 0<=0;}*}*>\\forall z5 \\forall z6 (true)'}?true;](73)'<=ff(z3+-66))&(\\exists z3 <{z5:=*;?true;++?true;}{{z5:=*;++{z1'=0&17+z3 < ((0*61)^1)}{z4:=*;{{z2:=24;++{{?true;}*++?true;++?true;}++z5:=*;++{?true;}*}{{z3'=74&[?true;++?true;]true}}*++z5:=*;}?0>z3'*0/(-71*z7');?true;++z1:=z3'+0;}}++{z2:=(ff(z1))';++z6:=-46;}?true;++{{z5:=0;}*}*}*++{{z5'=63/0&\\exists z7 true}++z5:=*;z1:=*;}{z7:=z2';++{z6:=z7^5*(z4/0);++{{{{?true;}*++{{?true;z2:=z2;++{?true;++?true;}{?true;++?true;}}++{{?true;++?true;}*}*}++{z7'=0&0^5-(0+0) < -70}}++{{?true;{?true;}*++{{?true;++?true;}?true;?true;}*}++{?true;?true;++?true;}{{?true;}*++?true;?true;}++?true;++{z2'=0-0&\\forall z7 true}}*}++{?true;++{{z6'=0,z5'=0,z2'=0&[{?true;}*]<?true;>true}{{z2'=0&true}?true;?true;}*}*}{z5:=*;}*z4:=*;{{?true;++?true;?true;}{{z5'=0&true}}*++{?true;?true;}*++{{?true;}*}*}}++{{{{{{?true;}*}*++z6:=z6;}*}*++z3:=*;}{{{z5'=0&true}++z4:=0;}*{{z6'=0,z1'=0&true}?true;}*++{{z2:=0;}*}*++{{?true;}*}*{?true;}*{?true;}*}*}*}*++z3:=*;}>qq()|<{{?<?0 < 0*ff(z4')*(ff((z4'+z6-z4')*((z4)'+z3')+z4)/(0+ff(0+0)*(75/z1')/0+0+z6'));++{z6:=z6;}*>\\exists z7 qq();}*}*>[?true;](pp(gg())&<?true;>57<=z3)))", "[{z5'=0&0/z5!=z2+((z1*z2)-z7)}]([{{{z7:=z7;?true;++z4:=0+(z6/(0+30/42-(85-64))^4)'-z4';}{?false;{{{z2:=z2;{{z7'=0&<z2:=*;>qq()}++z2:=z2;}{z7:=*;++z7:=z7;}*}{{z5'=0,z3'=0-(0+(0+0)+2)-38&<{z2:=z3;}*>true}}*}z4:=*;}z4:=gg()/(-35-((z3+0*0)*0+ff(z1'))*0)*(0-26/(gg()/z3'))+-87;}{{z7:=*;z7:=*;z7:=z1--92;}*++{{?true;z2:=*;}*{{z3:=*;++{z4'=0&86+0=z2+z2}}++z7:=z3/((gg()+(0*0)^3)/((0-0)*(0)'*-16)-77);}*}*}}*++{?true;}*{?true;++{z6'=0&[{?true;}*]\\exists z3 PP{z1'=z5}}}*}*](!(\\forall z1 (38*z6-4)/(91+0)-0 < (z5+80+(z3-0))*-28/0+z3->true)'|\\forall z7 \\exists z7 \\forall z3 [z1:=z1;++{z7'=0&<z1:=*;++{z4:=*;++z5:=*;++z6:=*;}{?<{z4'=0&true}>(true&true);++?z7'>0-0;}*++{{?\\exists z6 true;}*{{?true;}*}*?true;}*++{z4:=*;{{?true;++?true;}++?true;?true;}*}*><{?true;++{{{?true;?true;}*}*}*{{?true;?true;}?true;++?true;z7:=z7;}{?true;?true;++{?true;}*}*}++{{z3:=-11;{{?true;}*++{?true;}*}++z7:=z7;}z1:=*;}{{z5:=0/0-z1';++?(0)'=0-0;}++z3:=z3;}><{{?true;}*{?\\forall z2 0<=0;}*}*>\\forall z5 \\forall z6 (true)'}?true;](73)'<=ff(z3+-66))&(\\exists z3 <{z5:=*;?true;++?true;}{{z5:=*;++{z1'=0&17+z3 < ((0*61)^1)}{z4:=*;{{z2:=24;++{{?true;}*++?true;++?true;}++z5:=*;++{?true;}*}{{z3'=74&[?true;++?true;]true}}*++z5:=*;}?0>z3'*0/(-71*z7');?true;++z1:=z3'+0;}}++{z2:=(ff(z1))';++z6:=-46;}?true;++{{z5:=0;}*}*}*++{{z5'=63/0&\\exists z7 true}++z5:=*;z1:=*;}{z7:=z2';++{z6:=z7^5*(z4/0);++{{{{?true;}*++{{?true;z2:=z2;++{?true;++?true;}{?true;++?true;}}++{{?true;++?true;}*}*}++{z7'=0&0^5-(0+0) < -70}}++{{?true;{?true;}*++{{?true;++?true;}?true;?true;}*}++{?true;?true;++?true;}{{?true;}*++?true;?true;}++?true;++{z2'=0-0&\\forall z7 true}}*}++{?true;++{{z6'=0,z5'=0,z2'=0&[{?true;}*]<?true;>true}{{z2'=0&true}?true;?true;}*}*}{z5:=*;}*z4:=*;{{?true;++?true;?true;}{{z5'=0&true}}*++{?true;?true;}*++{{?true;}*}*}}++{{{{{{?true;}*}*++z6:=z6;}*}*++z3:=*;}{{{z5'=0&true}++z4:=0;}*{{z6'=0,z1'=0&true}?true;}*++{{z2:=0;}*}*++{{?true;}*}*{?true;}*{?true;}*}*}*}*++z3:=*;}>qq()|<{{?<?0 < 0*ff(z4')*(ff((z4'+z6-z4')*((z4)'+z3')+z4)/(0+ff(0+0)*(75/z1')/0+0+z6'));++{z6:=z6;}*>\\exists z7 qq();}*}*>[?true;](pp(gg())&<?true;>57<=z3)))"),
    ("[{x:=x+1;}*@invariant(x>=1)]x>=0", "[{x:=x+1;}*@invariant(x>=1)](x>=0)"),
    ("[{x:=x+1;}*@invariant(J(x))]x>=0", "[{x:=x+1;}*@invariant(J(x))](x>=0)"),
    (
      "(x!=m & (b>0 & v<10)) -> [{{?false; ++ a:=-b;};{x'=v,v'=a}}*]v<11",
      "     x!=m & b>0 & v<10\n-> [\n    {\n     {  ?false;\n     ++ a:=-b;\n     };\n     {x'=v,v'=a}\n    }*\n   ](v<11)",
    ),
    (
      "(x!=m & (b>0 & v<10)) -> [{{?false; ++ a:=-b;};{x'=v,v'=a}}*@invariant(J(v))]v<11",
      "     x!=m & b>0 & v<10\n-> [\n    {\n     {  ?false;\n     ++ a:=-b;\n     };\n     {x'=v,v'=a}\n    }*@invariant(J(v))\n   ](v<11)",
    ),
    // ("<{?[z1:=(80*(47*(0+z4)))'-gg();++{z1:=(51)';}*][{?true;?true;}*++{{z3:=-91;}*++?true;}*]true;}*{{{?true;++{z6'=0&[{{{{z1:=*;}*}*}*++?true;}*++{{z5:=z5;++z4:=z2*ff(4);{{?true;{?true;++?true;?true;++z1:=z1;}}?true;{{{?true;}*}*}*}*}?\\exists z4 z6'*96/z5^2>=z5'-63&(true<-><{{?true;}*++{?true;}*}{{?true;}*++z1:=0;}>true);z5:=0;{z1:=(((0-0)*48)^5)';++z5:=*;}}*{z6:=0;}*]97!=ff(0)/0+(gg()--76)}}++?<z4:=z4;++{{z1'=0&\\forall z5 (true|17*z3^1*(z7+-23)*(z1'+(ff(-26)-(0*0*0+35)))>(80/z7)^0)}}*>[?\\exists z4 \\forall z4 qq();]\\forall z3 (true&(<?false;{{z6'=0,z5'=0&!(true->true)->\\exists z4 (true&true)}++{{?true;?true;}*}*{z6'=0^4&0>0}{?true;++?true;}?true;?true;}><z3:=4^2;>(<{?true;++z6:=*;}*><?true;>PP{[?true;]true}->true)&(\\forall z4 true|(31+(22*(0-0)-(0+0)*30))^2>((0/z4)^2)^1))')&true;}*}*>-3=z7'", "<{{?[{z1:=(((80)*((47)*((0)+(z4))))')-(gg());}++{{z1:=(51)';}*}]([{{{?true;}{?true;}}*}++{{{{z3:=-91;}*}++{?true;}}*}](true));}*}{{{{{?true;}++{{z6'=0&[{{{{{{z1:=*;}*}*}*}++{?true;}}*}++{{{{{z5:=z5;}++{{z4:=(z2)*(ff(4));}{{{{?true;}{{?true;}++{{{?true;}{?true;}}++{z1:=z1;}}}}{{?true;}{{{{?true;}*}*}*}}}*}}}{{?(\\exists z4 ((((z6')*(96))/((z5)^(2)))>=((z5')-(63))))&((true)<->(<{{{?true;}*}++{{?true;}*}}{{{?true;}*}++{z1:=0;}}>(true)));}{{z5:=0;}{{z1:=((((0)-(0))*(48))^(5))';}++{z5:=*;}}}}}*}{{z6:=0;}*}}]((97)!=(((ff(0))/(0))+((gg())-(-76))))}}}++{?(<{z4:=z4;}++{{{z1'=0&\\forall z5 ((true)|(((((17)*((z3)^(1)))*((z7)+(-23)))*((z1')+((ff(-26))-((((0)*(0))*(0))+(35)))))>(((80)/(z7))^(0))))}}*}>([?\\exists z4 (\\forall z4 (qq()));](\\forall z3 ((true)&(((<{?false;}{{{{z6'=0},{z5'=0}&(!((true)->(true)))->(\\exists z4 ((true)&(true)))}}++{{{{{?true;}{?true;}}*}*}{{{z6'=(0)^(4)&(0)>(0)}}{{{?true;}++{?true;}}{{?true;}{?true;}}}}}}>(<z3:=(4)^(2);>((<{{?true;}++{z6:=*;}}*>(<?true;>(PP{[?true;](true)})))->(true))))&((\\forall z4 (true))|((((31)+(((22)*((0)-(0)))-(((0)+(0))*(30))))^(2))>((((0)/(z4))^(2))^(1)))))')))))&(true);}}*}*}>((-3)=(z7'))"),
    (
      "<z3:=*;>[?true;][?true;]\\exists z3 (<{?true;++?true;}*{?true;?true;}?true;?true;>ff(0^2)!=z2'^2|(\\exists z3 (true&true)|(0)'>=0*0)&z2' < -63^2)",
      "<z3:=*;>[?true;][?true;]\\exists z3 (<{?true;++?true;}*{?true;?true;}?true;?true;>ff(0^2)!=z2'^2|(\\exists z3 (true&true)|(0)'>=0*0)&z2' < -63^2)",
    ),
    ("[x:=0;](f())=16", "[x:=0;](((f()))=16)"),
    ("[x:=0;](f(x))=16", "[x:=0;](((f(x)))=16)"),
    ("[x:=0;](f())'=16", "[x:=0;](((f())')=16)"),
    ("[x:=0;](f(x))'=16", "[x:=0;](((f(x))')=16)"),
    ("<x:=0;>(f(x))'=16", "<x:=0;>(((f(x))')=16)"),
    (
      "[{{?true;?true;}{?true;++?true;}}?true|true;](ff(0))'=16",
      "[{{?true;?true;}{?true;++?true;}}?(true|true);]((ff(0))'=16)",
    ),
    // ("{?true;}*++{z3'=45&true}++{{{z1:=-85/-94;++?true;{{?true;++z5:=*;}++z6:=*;}}++{{{{?true;++z2:=*;}*++z3:=*;}{{{{{{z7'=0&false}z1:=*;}?0*0*(0+0)<=z6;++z7:=*;++?[{?true;}*?true;?true;][{?true;}*][?true;]true;}++z4:=pp(-58);}{z5:=z5;}*z6:=((0--25)*z4')';}{{{z5:=((0)')';}*++?true;++{{z4'=0*0&\\exists z6 true}++{z7'=0,z3'=0&true}{?true;++?true;}}*}++z5:=pp(96);}*}{{{?true;}*++{{z3'=0&\\exists z2 <?true|true;>\\forall z7 [?true;]true}}*}*}*}{{{?true;}*}*++{{{{?true;++z6:=*;++?!true;}++{z7:=(0^5)^3+(0+0)^3;}*}++{{z4:=*;++?true;}*}*{{z6:=*;}*}*}{{?false;++{{?true;++?true;}{?true;++?true;}}?true;{?true;++?true;}++z4:=qq();}{z1:=z1;{{?true;}*z4:=0;++{?true;++?true;}++?true;?true;}}{{?true;}*++?true;{?true;}*}*}*}{{z1'=0&!\\forall z3 \\forall z6 ((true)')'}?<{?true;{?true;}*++{?true;++?true;}++?true;?true;}?true;>\\exists z1 <z4:=z4;{?true;++?true;}>-91!=0+0;}?true;}?[{{z1:=(z1)'^1;++?true;++{z3'=0,z2'=0&PP{true}}{?true;?true;++?true;++?true;}*}{{{{?true;}*?true;?true;}*{{{?true;}*}*}*++?true;}++{{z1'=0&\\forall z4 true}++z4:=z2';}{z3'=z4&true}++z6:=0;++{{?true;++?true;}++{?true;}*}++{{?true;}*}*}}*]\\forall z6 \\exists z4 \\exists z6 \\forall z1 \\forall z2 ((true|true)&z5'>=z2');++{{z5:=*;++{?\\forall z4 <?true;><{{z3:=z3;}*}*>((\\forall z3 true)'|<{?true;}*>qq());}*}*++?\\forall z5 0+0--20^0*72<=-49;}{z7:=*;}*}{{{z3:=0-z4-((z2)')'*z6';++{z5'=79&<{{{?true;}*++{{?<?true;>true;{?true;?true;++?true;?true;}}*}*}++?true;z4:=pp(0*0+0/0)+-29;}++{z7:=*;++{{?<?true;>true;}*{?true;++?true;}*{?true;++?true;}?true;}{{?true;{?true;}*++{{?true;}*}*}++{z6'=0&true}?true;?true;++{?true;++?true;}*}}?true;{?true;?true;++?true;}>true}}++{{{{{{{{z7:=0;}*}*}*++{?true;}*}*++{{{{?true;}*++?true;?true;}++?true;}++?<z3:=z3;>(true<->true);}*++{{{?true;}*z3:=z3;}{?true;}*{?true;}*}*?true;}++{{{?true;++{z6:=0;}*{z2:=*;++{?true;}*}}?true;{{?true;?true;++{?true;}*}++{?true;?true;}*}}{?true;{{?true;++?true;}*++?false;}}?true;}z6:=*;}++?true;}{{{{{{z1:=*;}*}*}*{?true;++z4:=0+0;}*++z4:=z7^1;{z5:=18;++z7:=z5';}}{{z4:=*;}*}*++{{{{{?true;++?true;}++{?true;}*}++{?true;?true;}*}{?true;++?true;}*{?true;++?true;}?true;?true;++{z7'=0&[z6:=0;]\\exists z4 true}++{?true;++?true;}*{?true;++?true;++?true;}}++{?0>=0;{z7'=0,z2'=0&0 < 0}++{{?true;}*++?true;++?true;}++?true;}z6:=*;}?<{{?0<=0;}*}*>true;}++{{{{{z6'=1&0 < -43}}*}*}*++{{?true;?true;}*?true;}*{{?true;?true;}*++?true;++?true;?true;}{?true;}*++{z1:=*;}*++?true;}*}}*}++z7:=*;}}{?true;}*}*{{?\\exists z5 pp(z1/-74+((-4)')'/0);++{{{{{{{{{?true;++?true;}?true;?true;++{{?true;}*}*}++{?true;?true;}z4:=0;++{?true;?true;}*}*z2:=z3';z5:=*;++{{z6:=*;++{{?true;}*}*}*++{{?true;++?true;}*}*++{z2'=0&[?true;]true|<?true;>true}}{{{{?true;++?true;}z5:=*;}{z3:=0;}*}z4:=*;++{?true;?true;++z5:=0;}*++z4:=0+0;{z5:=*;++?true;}}}{{z2:=*;}*++z7:=0;}}{{{{{{z7'=0&true}++{?true;}*}?true;}{z3:=0;++?true;}}?true;}*++?true;}z2:=z2;}*++z5:=*;++{{{z1:=(75)'^1;}*++{{z7:=*;++{z5:=z5;}*++z7:=0-0;}{{z3:=z3;}*{{z7'=0&true}++?true;}}{{{z6'=0&true}}*}*}{{{z3'=0/0+0/0&!true}}*}*}{?true;++?\\exists z1 <{?true;++?true;}{?true;++?true;}++?true;>0*0-(0-0)!=z4';}}z3:=z3;}{?true;}*}*}*}*}*","{?true;}*++{z3'=45&true}++{{{z1:=-85/-94;++?true;{{?true;++z5:=*;}++z6:=*;}}++{{{{?true;++z2:=*;}*++z3:=*;}{{{{{{z7'=0&false}z1:=*;}?0*0*(0+0)<=z6;++z7:=*;++?[{?true;}*?true;?true;][{?true;}*][?true;]true;}++z4:=pp(-58);}{z5:=z5;}*z6:=((0--25)*z4')';}{{{z5:=((0)')';}*++?true;++{{z4'=0*0&\\exists z6 true}++{z7'=0,z3'=0&true}{?true;++?true;}}*}++z5:=pp(96);}*}{{{?true;}*++{{z3'=0&\\exists z2 <?true|true;>\\forall z7 [?true;]true}}*}*}*}{{{?true;}*}*++{{{{?true;++z6:=*;++?!true;}++{z7:=(0^5)^3+(0+0)^3;}*}++{{z4:=*;++?true;}*}*{{z6:=*;}*}*}{{?false;++{{?true;++?true;}{?true;++?true;}}?true;{?true;++?true;}++z4:=qq();}{z1:=z1;{{?true;}*z4:=0;++{?true;++?true;}++?true;?true;}}{{?true;}*++?true;{?true;}*}*}*}{{z1'=0&!\\forall z3 \\forall z6 ((true)')'}?<{?true;{?true;}*++{?true;++?true;}++?true;?true;}?true;>\\exists z1 <z4:=z4;{?true;++?true;}>-91!=0+0;}?true;}?[{{z1:=(z1)'^1;++?true;++{z3'=0,z2'=0&PP{true}}{?true;?true;++?true;++?true;}*}{{{{?true;}*?true;?true;}*{{{?true;}*}*}*++?true;}++{{z1'=0&\\forall z4 true}++z4:=z2';}{z3'=z4&true}++z6:=0;++{{?true;++?true;}++{?true;}*}++{{?true;}*}*}}*]\\forall z6 \\exists z4 \\exists z6 \\forall z1 \\forall z2 ((true|true)&z5'>=z2');++{{z5:=*;++{?\\forall z4 <?true;><{{z3:=z3;}*}*>((\\forall z3 true)'|<{?true;}*>qq());}*}*++?\\forall z5 0+0--20^0*72<=-49;}{z7:=*;}*}{{{z3:=0-z4-((z2)')'*z6';++{z5'=79&<{{{?true;}*++{{?<?true;>true;{?true;?true;++?true;?true;}}*}*}++?true;z4:=pp(0*0+0/0)+-29;}++{z7:=*;++{{?<?true;>true;}*{?true;++?true;}*{?true;++?true;}?true;}{{?true;{?true;}*++{{?true;}*}*}++{z6'=0&true}?true;?true;++{?true;++?true;}*}}?true;{?true;?true;++?true;}>true}}++{{{{{{{{z7:=0;}*}*}*++{?true;}*}*++{{{{?true;}*++?true;?true;}++?true;}++?<z3:=z3;>(true<->true);}*++{{{?true;}*z3:=z3;}{?true;}*{?true;}*}*?true;}++{{{?true;++{z6:=0;}*{z2:=*;++{?true;}*}}?true;{{?true;?true;++{?true;}*}++{?true;?true;}*}}{?true;{{?true;++?true;}*++?false;}}?true;}z6:=*;}++?true;}{{{{{{z1:=*;}*}*}*{?true;++z4:=0+0;}*++z4:=z7^1;{z5:=18;++z7:=z5';}}{{z4:=*;}*}*++{{{{{?true;++?true;}++{?true;}*}++{?true;?true;}*}{?true;++?true;}*{?true;++?true;}?true;?true;++{z7'=0&[z6:=0;]\\exists z4 true}++{?true;++?true;}*{?true;++?true;++?true;}}++{?0>=0;{z7'=0,z2'=0&0 < 0}++{{?true;}*++?true;++?true;}++?true;}z6:=*;}?<{{?0<=0;}*}*>true;}++{{{{{z6'=1&0 < -43}}*}*}*++{{?true;?true;}*?true;}*{{?true;?true;}*++?true;++?true;?true;}{?true;}*++{z1:=*;}*++?true;}*}}*}++z7:=*;}}{?true;}*}*{{?\\exists z5 pp(z1/-74+((-4)')'/0);++{{{{{{{{{?true;++?true;}?true;?true;++{{?true;}*}*}++{?true;?true;}z4:=0;++{?true;?true;}*}*z2:=z3';z5:=*;++{{z6:=*;++{{?true;}*}*}*++{{?true;++?true;}*}*++{z2'=0&[?true;]true|<?true;>true}}{{{{?true;++?true;}z5:=*;}{z3:=0;}*}z4:=*;++{?true;?true;++z5:=0;}*++z4:=0+0;{z5:=*;++?true;}}}{{z2:=*;}*++z7:=0;}}{{{{{{z7'=0&true}++{?true;}*}?true;}{z3:=0;++?true;}}?true;}*++?true;}z2:=z2;}*++z5:=*;++{{{z1:=(75)'^1;}*++{{z7:=*;++{z5:=z5;}*++z7:=0-0;}{{z3:=z3;}*{{z7'=0&true}++?true;}}{{{z6'=0&true}}*}*}{{{z3'=0/0+0/0&!true}}*}*}{?true;++?\\exists z1 <{?true;++?true;}{?true;++?true;}++?true;>0*0-(0-0)!=z4';}}z3:=z3;}{?true;}*}*}*}*}*"),

    ("[{x:=x+1;}*@invariant(x>=1)]x>=0", "[{x:=x+1;}*@invariant(x>=1)](x>=0)"),
    ("[x:=0;](f())=16", "[x:=0;](((f()))=16)"),
    ("z3>=((-63))'", "z3>=((-63))'"),
    ("z3>=(-(63))'", "z3>=(-(63))'"),
    ("z3>=(-63)'", "z3>=(-(63))'"),
    ("z3>=((-63))'", "z3>=((-63))'"),
    (
      "((18)'!=58-z2'&[z2':=(-57);]1>=(-86)<->(\\forall z2 1/1>=z3<->1<=1*1-z3'))<->-(26)'*z1>0",
      if (weakNeg)
        "((18)'!=58-(z2')&[z2':=(-57);](1>=(-86))<->((\\forall z2 ((1/1)>=z3))<->(1<=(1*1)-(z3'))))<->(-(((26)')*z1))>0"
      else
        "((18)'!=58-(z2')&[z2':=(-57);](1>=(-86))<->((\\forall z2 ((1/1)>=z3))<->(1<=(1*1)-(z3'))))<->(-((26)'))*z1>0",
    ),
    ("[x:=*;]x^2>=0", "[x := * ;] x^2>=0"), // issue #171 space within random assignments
    ("[x:=*;]x^2>=0", "[x:= * ;] x^2>=0"),
    ("[x:=*;]x^2>=0", "[x:=* ;] x^2>=0"),
    ("[x:=*;]x^2>=0", "[x :=* ;] x^2>=0"),
    ("[x:=*;]x^2>=0", "[x := *;] x^2>=0"),
    ("[x:=*;]x^2>=0", "[x :=*;] x^2>=0"),
    ("x=f()", "x=f()"),
    ("x=f(||)", "x=f(||)"),
    ("x'=f()", "(x')=f()"),
    ("x'=f(||)", "(x')=f(||)"),
    ("[{x'=f()}]p() <-> [{x'=f()}][x':=f();]p()", "([{x'=f()}]p()) <-> ([{x'=f()}]([x':=f();]p()))"),
    ("[{x'=f()}]p(||) <-> [{x'=f()}][x':=f();]p(||)", "([{x'=f()}]p(||)) <-> ([{x'=f()}]([x':=f();]p(||)))"),
    (
      "[{x'=f(||)}]p(||) <-> [{x'=f(||)}][x':=f(||);]p(||)",
      "([{x'=f(||)}]p(||)) <-> ([{x'=f(||)}]([x':=f(||);]p(||)))",
    ),
    (
      "[{x'=f(||)&q(||)}]p(||) <-> [{x'=f(||)&q(||)}][x':=f(||);]p(||)",
      "([{x'=f(||)&q(||)}]p(||)) <-> ([{x'=f(||)&q(||)}]([x':=f(||);]p(||)))",
    ),
    (
      "[{x'=f(||),c&q(||)}]p(||) <-> [{c,x'=f(||)&q(||)}][x':=f(||);]p(||)",
      "([{x'=f(||),c&q(||)}]p(||)) <-> ([{c,x'=f(||)&q(||)}]([x':=f(||);]p(||)))",
    ),
    (
      "[{x_'=f(||),c&q(||)}]p(||) <-> [{c,x_'=f(||)&q(||)}][x_':=f(||);]p(||)",
      "([{x_'=f(||),c&q(||)}]p(||)) <-> ([{c,x_'=f(||)&q(||)}]([x_':=f(||);]p(||)))",
    ),
    ("(p() <-> q()) <- (q() -> q()&p())", "(p() <-> q()) <- (q() -> (q()&p()))"),
    ("(p() <-> q()) <- (q() -> q()&p())", "(q() -> (q()&p())) -> (p() <-> q())"),
    ("(p(||) <-> q(||)) <- (q(||) -> q(||)&p(||))", "(p(||) <-> q(||)) <- (q(||) -> (q(||)&p(||)))"),
    ("[{c}]p(|y|) <-> \\exists y [{c}]p(|y|)", "([{c}]p(|y|)) <-> (\\exists y ([{c}]p(|y|)))"),
    ("[{c{||}}]p(|y|) <-> \\exists y [{c{||}}]p(|y|)", "([{c{||}}]p(|y|)) <-> (\\exists y ([{c{||}}]p(|y|)))"),
    ("[{c{|y|}}]p(|y|) <-> \\exists y [{c{|y|}}]p(|y|)", "([{c{|y|}}]p(|y|)) <-> (\\exists y ([{c{|y|}}]p(|y|)))"),
    (
      "[{c{|y|}}]p(|y_|) <-> \\exists y_ [{c{|y|}}]p(|y_|)",
      "([{c{|y|}}]p(|y_|)) <-> (\\exists y_ ([{c{|y|}}]p(|y_|)))",
    ),
    (
      "[{c{|y_|}}]p(|y_|) <-> \\exists y_ [{c{|y_|}}]p(|y_|)",
      "([{c{|y_|}}]p(|y_|)) <-> (\\exists y_ ([{c{|y_|}}]p(|y_|)))",
    ),
    (
      "[{c{|y_|}}]p(|y_|) <-> \\exists y_ [{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)}]p(|y_|)",
      "([{c{|y_|}}]p(|y_|)) <-> (\\exists y_ ([{c{|y_|},y_'=((a(|y_|)*y_)+b(|y_|))}]p(|y_|)))",
    ),
    (
      "[{c{|y_|}&q(|y_|)}]p(|y_|) <-> \\exists y_ [{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}]p(|y_|)",
      "([{c{|y_|}&q(|y_|)}]p(|y_|)) <-> (\\exists y_ ([{c{|y_|},y_'=((a(|y_|)*y_)+b(|y_|))&q(|y_|)}]p(|y_|)))",
    ),
    (
      "([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}]((p(||))'))",
      "(([{c&q(||)}]p(||)) <-> ([?q(||);]p(||))) <- ((q(||)) -> ([{c&q(||)}](((p(||))'))))",
    ),
    // @todo unparseable is ok but bad error ("([{c}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c}](p(||)'))", "(([{c}]p(||)) <-> ([?q(||);]p(||))) <- ((q(||)) -> ([{c}]((p(||)'))))"),
    // @todo unparseable is ok but bad error ("([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}](p(||)'))", "(([{c&q(||)}]p(||)) <-> ([?q(||);]p(||))) <- ((q(||)) -> ([{c&q(||)}](((p(||))'))))"),

    // extra braces within ODEs ....
//    ("v>=0&A()>0->[{x'=v,v'=A()&true}]v>=0", "(v>=0&A()>0)->[{{x'=v,v'=A()}&true}](v>=0)"),
//    ("[{x'=1,y'=2,z'=3}]x>0", "[{x'=1,{y'=2,z'=3}}]x>0"),
//    ("[{x'=1,y'=2,z'=3&x<5}]x>0", "[{x'=1,{y'=2,z'=3}&x<5}]x>0"),

    // multiline tests
    ("p()<->q() &\nx>0 &\ny<2", "(p()) <-> (q()&((x>0)&(y<2)))"),
    ("p()<->q() &\nx>0 &&\ny<2", unparseable),
    ("p()<->q()<->r()", unparseable),
    ("p()<-q()<-r()", unparseable), // could be read as (p() < (-q())) <- r()
    ("p()->q()<-r()", unparseable), // could be read as p() -> (q() < (- r()))
    ("p()<-q()->r()", unparseable), // could be read as (p() < (-q())) -> r()

  )

  /**
   * Program cases: Left string is expected to parse like the right string parses, or not at all if right==unparseable
   */
  private val expectedParseProgram: immutable.List[(String, String)] = List(
    ("x:=x+1;", "x:=(x+1);"),
    ("x:=2*x;", "x:=(2*x);"),
    ("x:=2*x+1;", "x:=((2*x)+1);"),
    ("x:=1+2*x;", "x:=(1+(2*x));"),
    ("(x+1):=x;", unparseable),
    ("x:=1;x:=2;", "x:=1;x:=2;"),
    ("x:=1;x:=2;x:=3;", "x:=1;{x:=2;x:=3;}"),
    ("x:=1;++x:=2;++x:=3;", "x:=1;++{x:=2;++x:=3;}"),
    ("x:=1;x:=2;++x:=3;", "{x:=1;x:=2;}++{x:=3;}"),
    ("x:=1;++x:=2;x:=3;", "x:=1;++{x:=2;x:=3;}"),
    ("x:=1;++x:=2;++x:=3;", "x:=1;++{x:=2;++x:=3;}"),
    ("x:=1;x:=2;++x:=3;x:=4;", "{x:=1;x:=2;}++{x:=3;x:=4;}"),
    ("x:=1;x:=2;++x:=3;++x:=4;", "{x:=1;x:=2;}++{x:=3;++x:=4;}"),
    ("x:=1;++x:=2;x:=3;++x:=4;", "x:=1;++{{x:=2;x:=3;}++x:=4;}"),
    ("x:=1;++x:=2;++x:=3;x:=4;", "x:=1;++{x:=2;++{x:=3;x:=4;}}"),
    ("x:=1;?x>0&x^2>5;{x'=5}", "x:=1;{?((x>0)&((x^2)>5));{x'=5}}"),
    ("x:=1;?x<0&x^2>5;{x'=5}", "x:=1;{?((x<0)&((x^2)>5));{x'=5}}"),
    ("x:=1;?x>0&x^2>5;{x'=5&true}", "x:=1;{?((x>0)&((x^2)>5));{x'=5&true}}"),
    ("x:=y';", "x:=(y');"),
    ("x':=y;", "x':=y;"),
    ("x':=y';", "x':=(y');"),
    ("?\\exists z2 qq();", "?(\\exists z2 (qq()));"),
    ("?true->\\exists z2 qq();", "?(true->(\\exists z2 (qq())));"),
    ("?[z2:=*;]true->\\exists z2 qq();", "?(([z2:=*;]true)->(\\exists z2 qq()));"),
    ("?[z2:=*;]\\exists z1 true->\\exists z2 qq();", "?([z2:=*;](\\exists z1 (true))->(\\exists z2 (qq())));"),

    // games
    ("{x:=x+1;}^@", "{x:=x+1;}^@"),
    ("{x'=1}^@", "{x'=1}^@"),
    ("{x:=1;++x:=2;}^@", "{x:=1;++x:=2;}^@"),
    ("{x:=x+1;{x'=1}^@ ++ x:=x-1;}*", "{{x:=(x+1);{{x'=1}^@}} ++ {x:=x-1;}}*"),

    // if-then-else special elaboration form(
    ("if (x > 0) {x := 1;} else {x := 2;}", "{?(x>0); x:=1;}++{?(!(x>0)); x:=2;}"),
    ("if(x>0) {x:=1;}else {x:=2;}", "if (x > 0) {x := 1;} else {x := 2;}"),
    ("if (x > 0) {x := 1; y := 2;} else {x := 2; y:=1;}", "{?(x>0); {x:=1; y := 2;}}++{?(!(x>0)); {x:=2;y:=1;}}"),

    // should have dangling else problem as in C
    ("if (x > 0)  {x := 1;} else {x := 2;} y := 2;", "{if (x > 0) { x := 1; }else {x := 2;} }y := 2;"),
    ("if (x > 0)  {x := 1;} else {x := 2;} y := 2;", "{{?(x>0); x:=1;}++{?(!(x>0)); x:=2;}} y := 2;"),
    // should choose nearest if to match the dangling else as in C
    ("if (y^2=1) {if (x > 0) { x := 1;} else {x := 2;}}", "if (y^2=1) {if (x > 0)  {x := 1;} else {x := 2;}}"),
    (
      "if (y^2=1) {if (x > 0) { x := 1;} else {x := 2;}} y := 2;",
      "{if (y^2=1) {if (x > 0) { x := 1;} else {x := 2;}}} y := 2;",
    ),
    // should allow nested if-then-else
    (
      "if (y^2=1) {if (x > 0) { x := 1;} else {x := 2;}} else {z:=0;}",
      "if (y^2=1) {if (x > 0) { x := 1;} else {x := 2;}} else {z:=0;}",
    ),
    (
      "if (y^2=1) {if (x > 0) { x := 1;} else {x := 2;}} else {z:=0;} y := 2;",
      "{if (y^2=1) {if (x > 0) { x := 1;} else {x := 2;}} else {z:=0;}} y := 2;",
    ),
    // should allow fancy if-then-else conditions
    ("if ([x:=x+1;]x>0) {x:=x+1;} else {x:=1;}", "{?([x:=x+1;]x>0); x:=x+1;} ++ {?(![x:=x+1;]x>0); x:=1;}"),
    ("if (<x:=x+1;>x>0) {x:=x+1;} else {x:=1;}", "{?(<x:=x+1;>(x>0)); x:=x+1;} ++ {?(!<x:=x+1;>(x>0)); x:=1;}"),
    ("if (x > 0)  x := 1; y := 2; else {x := 2;}", unparseable),
  )

  /** Left string is expected to parse like the right string parses, or not at all if right==unparseable */
  private val expectedParseExpression: immutable.List[(String, String)] = expectedParseTerm ++ expectedParseFormula ++
    expectedParseProgram

  "The parser" should "parse table of string pairs as expected" in { pairParse(expectedParseExpression, parser) }

  it should "term parse table of string pairs as expected" in {
    pairParse(expectedParseTerm, s => { val r = parser.termParser(s); r shouldBe a[Term]; r })
  }

  it should "formula parse table of string pairs as expected" in {
    pairParse(expectedParseFormula, s => { val r = parser.formulaParser(s); r shouldBe a[Formula]; r })
  }

  it should "program parse table of string pairs as expected" in {
    pairParse(expectedParseProgram, s => { val r = parser.programParser(s); r shouldBe a[Program]; r })
  }

  def pairParse(expected: List[(String, String)], parser: String => Expression): Unit = {
    forEvery(Table(("Input", "Expected"), expected: _*))({ (s1, s2) =>
      println("\ninput:    " + s1)
      if (s2 == unparseable) {
        // ParseExceptions and CoreExceptions and AssertionErrors are simply all allowed.
        a[Throwable] should be thrownBy parser(s1)
      } else {
        val p1 = parser(s1)
        println("parsed:   " + pp(p1))
        println("which is: " + pp.fullPrinter(p1))
        println("versus:   " + s2)
        val p2 = parser(s2)
        println("read as:  " + pp(p2))
        println("which is: " + pp.fullPrinter(p2))
        p1 shouldBe p2
        println("parsing of print")
        parser(pp(p1)) shouldBe parser(pp(p2))
        pp(p1) shouldBe pp(p2)
        if (uipp.isDefined) println(uipp.get(p1))
      }
    })
  }

  "Reparsing Pretty-printed Expressions" should "reparse (-2)" in { reparse(Number(BigDecimal("-2"))) }
  it should "reparse (-2)*x" in { reparse(Times(Number(BigDecimal("-2")), Variable("x"))) }
  it should "reparse -(2*x)" in { reparse(Neg(Times(Number(BigDecimal("2")), Variable("x")))) }
  it should "reparse -2^4" in { reparse(Neg(Power(Number(BigDecimal("2")), Number(BigDecimal("4"))))) }
  it should "reparse (-2)^4" in { reparse(Power(Number(BigDecimal("-2")), Number(BigDecimal("4")))) }
  it should "reparse (- 2)^4" in { reparse(Power(Neg(Number(BigDecimal("2"))), Number(BigDecimal("4")))) }
  it should "reparse -(2^4)" in { reparse(Neg(Power(Number(BigDecimal("2")), Number(BigDecimal("4"))))) }
  it should "reparse (-2)^(-4)" in { reparse(Power(Number(BigDecimal("-2")), Number(BigDecimal("-4")))) }
  it should "reparse (- 2)^(-4)" in { reparse(Power(Neg(Number(BigDecimal("2"))), Number(BigDecimal("-4")))) }
  it should "reparse (- 2)^(- 4)" in { reparse(Power(Neg(Number(BigDecimal("2"))), Neg(Number(BigDecimal("4"))))) }
  it should "reparse (-2)^(- 4)" in { reparse(Power(Number(BigDecimal("-2")), Neg(Number(BigDecimal("4"))))) }
  it should "reparse -(2^(-4))" in { reparse(Neg(Power(Number(BigDecimal("2")), Number(BigDecimal("-4"))))) }

  private def reparse(e: Expression): Unit = {
    val printed = pp.stringify(e)
    println("Expression: " + printed)
    val full = pp.fullPrinter(e)
    println("Fullform:   " + full)
    parseShouldBe(full, e)
    println("Reparsing:  " + printed)
    parseShouldBe(printed, e)
    println("Fullparse:  " + pp.fullPrinter(parser(printed)))
  }

  //  "Parser" should "accept or throw parse errors for primes in primes" in {
//    a[ParseException] shouldBe thrownBy(parser("(x')'"))
//    a[ParseException] shouldBe thrownBy(parser("(x'+y)'"))
//    a[ParseException] shouldBe thrownBy(parser("(x'+y>=0)'"))
//    a[ParseException] shouldBe thrownBy(parser("([{x'=1}]x>=0)'"))
//    a[ParseException] shouldBe thrownBy(parser("([x':=1]x>=0)'"))
//  }
}
