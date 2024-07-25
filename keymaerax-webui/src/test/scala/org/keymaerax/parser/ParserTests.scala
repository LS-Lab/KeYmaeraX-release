/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.core._
import org.keymaerax.parser.ParseExceptionMatchers.{mention, pointAt}
import org.keymaerax.parser.StringConverter._
import org.keymaerax.tagobjects.TodoTest
import org.keymaerax.tools.KeYmaeraXTool
import org.keymaerax.{Configuration, FileConfiguration}
import org.scalamock.scalatest.MockFactory
import org.scalatest.Inside._
import org.scalatest.LoneElement._
import org.scalatest.OptionValues._
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach}

import scala.collection.immutable._
import scala.io.Source

class ParserTests extends AnyFlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll with MockFactory {
  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(interpreter = KeYmaeraXTool.InterpreterChoice.LazySequential, initDerivationInfoRegistry = false)
  }
  override def afterEach(): Unit = { Parser.parser.setAnnotationListener((_, _) => {}) }

  // type declaration header for tests
  def makeInput(program: String): String = s"""
                                              |ArchiveEntry "Test"
                                              |Definitions Bool a, b, c; End.
                                              |ProgramVariables Real p, q, r, s, r_0; End.
                                              |Problem $program End.
                                              |End.""".stripMargin

  private val x = Variable("x", None, Real)
  private val y = Variable("y", None, Real)

  "The problem parser" should "reject strings containing non-ASCII characters" in {
    def input(s: String) = s"""
                              |ArchiveEntry "Test"
                              |ProgramVariables Real x; End.
                              |Problem [x := $s;]x > 3 End.
                              |End.
      """.stripMargin
    ArchiveParser.parser(input("1")) // the problem should be exactly the fact that we pass in some unicode.
    a[Exception] shouldBe thrownBy(ArchiveParser.parser("\\u03C0"))
  }

  it should "parse nullary predicate definitions" in {
    val input = """
                  |ArchiveEntry "Test"
                  |Definitions
                  |  Bool J() <-> 1>=0;
                  |End.
                  |ProgramVariables
                  |  Real x;
                  |End.
                  |Problem
                  |  J() -> [{x:=x+1;}*@invariant(J())]J()
                  |End.
                  |End.
    """.stripMargin
    val entry = ArchiveParser.parser(input).loneElement
    entry.defs.decls(Name("J", None)).interpretation.toOption.value.value shouldBe "1>=0".asFormula
    entry.model shouldBe "J() -> [{x:=x+1;}*]J()".asFormula
  }

  it should "parse unary predicate definitions" in {
    val input = """
                  |ArchiveEntry "Test"
                  |Definitions
                  |  Bool J(Real x) <-> x>=0;
                  |End.
                  |ProgramVariables
                  |  Real x;
                  |End.
                  |Problem
                  |  J(x) -> [{x:=x+1;}*@invariant(J(x))]J(x)
                  |End.
                  |End.
    """.stripMargin
    val entry = ArchiveParser.parser(input).loneElement
    inside(entry.defs.decls(Name("J", None))) { case Signature(domain, sort, argNames, expr, _) =>
      domain.value shouldBe Real
      sort shouldBe Bool
      argNames shouldBe Some((Name("x", None), Real) :: Nil)
      expr.toOption.value.value shouldBe "x>=0".asFormula
    }
    entry.model shouldBe "J(x) -> [{x:=x+1;}*]J(x)".asFormula
  }

  it should "parse binary predicate definitions" in {
    val input = """
                  |ArchiveEntry "Test"
                  |Definitions
                  |  Bool J(Real x, Real y) <-> x>=y;
                  |End.
                  |ProgramVariables
                  |  Real x, y;
                  |End.
                  |Problem
                  |  J(x,y) -> [{x:=x+1;}*@invariant(J(x,y))]J(x,y)
                  |End.
                  |End.
    """.stripMargin
    val entry = ArchiveParser.parser(input).loneElement
    inside(entry.defs.decls(Name("J", None))) { case Signature(domain, sort, argNames, expr, _) =>
      domain.value shouldBe Tuple(Real, Real)
      sort shouldBe Bool
      argNames shouldBe Some((Name("x", None), Real) :: (Name("y", None), Real) :: Nil)
      expr.toOption.value.value shouldBe "x>=y".asFormula
    }
    entry.model shouldBe "J(x,y) -> [{x:=x+1;}*]J(x,y)".asFormula
  }

  it should "parse program definitions" in {
    val input = """
                  |ArchiveEntry "Test"
                  |Definitions
                  |  HP prg ::= { x:=x+1; };
                  |End.
                  |ProgramVariables
                  |  Real x;
                  |End.
                  |Problem
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                  |End.
    """.stripMargin
    val entry = ArchiveParser.parser(input).loneElement
    inside(entry.defs.decls(Name("prg", None))) { case Signature(domain, sort, argNames, expr, _) =>
      domain.value shouldBe Unit
      sort shouldBe Trafo
      argNames shouldBe Symbol("empty")
      expr.toOption.value.value shouldBe "x:=x+1;".asProgram
    }
    entry.model shouldBe "x>=0 -> [{prg{|^@|};}*]x>=0".asFormula
  }

  it should "report useful message on missing semicolon in program variable declaration" in {
    val input = """ArchiveEntry "Test"
                  |ProgramVariables
                  |  Real x
                  |End.
                  |Problem
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                  |End.
                """.stripMargin

    val ex = the[ParseException] thrownBy ArchiveParser.parser(input)

    ex should pointAt(4, 1)
    ex should mention("ProgramVariables")
    ex.expect should include(",")
    ex.expect should include(";")
  }

  it should "report useful message on missing semicolon in function definitions" in {
    val input = """ArchiveEntry "Test"
                  |Definitions
                  |  Real func() = 4
                  |End.
                  |ProgramVariables
                  |  Real x;
                  |End.
                  |Problem
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                  |End.
                """.stripMargin
    the[ParseException] thrownBy ArchiveParser.parser(input) should
      (have message
        """4:1 Unexpected token in definition
          |Found:    End at 4:1 to 4:3
          |Expected: ;
          |      or: <FollowsExpression>""".stripMargin or have message
        """4:1 Error parsing definitions at 2:1
          |Found:    "End." at 4:1
          |Expected: ("^" | "*" | "/" | "+" | "-" | ";")
          |Hint: Try ("^" | "*" | "/" | "+" | "-" | ";")""".stripMargin)
  }

  it should "report useful message on missing semicolon in program definitions" in {
    val input = """ArchiveEntry "Test"
                  |Definitions
                  |  HP prg ::= { x:=x+1; }
                  |End.
                  |ProgramVariables
                  |  Real x;
                  |End.
                  |Problem
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                  |End.
                """.stripMargin
    the[ParseException] thrownBy ArchiveParser.parser(input) should
      (have message
        """4:1 Unexpected token in program definition
          |Found:    End at 4:1 to 4:3
          |Expected: ::=
          |      or: ;""".stripMargin or have message
        """4:1 Error parsing progDef at 3:3
          |Found:    "End." at 4:1
          |Expected: ";"
          |Hint: Try ";"""".stripMargin)
  }

  it should "report useful message on missing braces in program definitions" in {
    val input = """ArchiveEntry "Test"
                  |Definitions
                  |  HP prg ::= x:=x+1;
                  |End.
                  |ProgramVariables
                  |  Real x;
                  |End.
                  |Problem
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                  |End.
                """.stripMargin
    the[ParseException] thrownBy ArchiveParser.parser(input) should
      (have message
        """3:14 Missing program definition start delimiter
          |Found:    ID("x") at 3:14
          |Expected: {""".stripMargin or have message
        """3:14 Error parsing progDef at 3:3
          |Found:    "x:=x+1;" at 3:14
          |Expected: "{"
          |Hint: Try "{"""".stripMargin)
  }

  "The Parser" should "place implicit parens correctly (a.k.a. resolve abiguities correctly)" in {
    val equalPairs =
      // unary operator binds stronger than binary operator
      ("! p > 0 & p < 5", "(!(p>0)) & (p<5)") ::
        ("! p = 0 & p = 5", "(!(p=0)) & (p=5)") ::
        ("! p > 0 | p < 5", "(!(p>0)) | (p<5)") ::
        ("! p > 0 -> p > 5", "(!(p>0)) -> (p>5)") ::
        ("! p > 0 <-> p > 5", "(!(p>0)) <-> (p>5)") ::
        // quantifiers do not bind logical connectives but do bind inequalities.
        ("! \\forall x x > 0 | p < 5", "(!(\\forall x x>0)) | (p<5)") ::
        ("! \\exists x x > 0 | p < 5", "(!(\\exists x x>0)) | (p<5)") ::
        ("! \\forall x [p:=x;]p >= x | p < 5", "(!(\\forall x ([p:=x;](p>=x)))) | (p<5)") ::
        // quantifiers with multiple variables
//      ("\\forall x, y . (y > x -> y > x)", "\\forall x, y . (y > x -> y > x)") ::
//      ("\\exists y, x . (y > x -> y > x)", "\\exists y, x . (y > x -> y > x)") ::
        // modalities do not bind logical connectives.
        ("[p:=1;] p>0 & p < 1", "([p:=1;](p>0)) & (p<1)") ::
        ("[p:=1;] p>0 | p < 1", "([p:=1;](p>0)) | (p<1)") ::
        ("[p:=1;] p>0 -> p < 1", "([p:=1;](p>0)) -> (p<1)") ::
        ("<p:=1;> p>0 & p < 1", "(<p:=1;>(p>0)) & (p<1)") ::
        ("<p:=1;> p>0 | p < 1", "(<p:=1;>(p>0)) | (p<1)") ::
        ("<p:=1;> p>0 -> p < 1", "(<p:=1;>(p>0)) -> (p<1)") ::
        ("\\forall x x > 2 & a < 0", "(\\forall x (x > 2)) & a < 0") ::
        ("\\forall x x > 2 | a < 0", "(\\forall x (x > 2)) | a < 0") ::
        ("\\forall x x > 2 -> a < 0", "(\\forall x (x > 2)) -> a < 0") ::
        ("\\forall x x > 2 <-> a < 0", "(\\forall x (x > 2)) <-> a < 0") ::
        ("\\exists x x > 2 & a < 0", "(\\exists x (x > 2)) & a < 0") ::
        ("\\exists x x > 2 | a < 0", "(\\exists x (x > 2)) | a < 0") ::
        ("\\exists x x > 2 -> a < 0", "(\\exists x (x > 2)) -> a < 0") ::
        ("\\exists x x > 2 <-> a < 0", "(\\exists x (x > 2)) <-> a < 0") ::
        // nested modalities
        ("< p:=1; > <p:=2; > p>0", "<p:=1;>(<p:=2;>p>0)") ::
        ("[ p:=1; ] <p:=2; > p>0", "[p:=1;](<p:=2;>p>0)") ::
        ("< p:=1; > [p:=2; ] p>0", "<p:=1;>([p:=2;]p>0)") ::
        // [], <>, \forall, \exists magic.
        ("\\forall x [x:=1;]<x:=2;>x>0", "\\forall x ([x:=1;]<x:=2;>(x>0))") ::
        ("\\exists x [x:=1;]<x:=2;>x>0", "\\exists x ([x:=1;]<x:=2;>(x>0))") ::
        (
          "[p:=0;]\\forall x [x:=p;] \\exists y [q := x + y; ] q > 0",
          "[p:=0;](\\forall x [x:=p;] (\\exists y [q := x + y; ] q > 0))",
        ) ::
        // <> vs >.
        ("< ?p>q; > p > 1", "<?(p > q);>(p>1)") ::
        ("[ ?p>q; ] p > 1", "[?(p > q);](p>1)") ::
        ("< ?a < 0; ++ ?a < 0; > a < 0", "< {?a < 0;} ++ {?a < 0;} > a < 0") ::
        // arith.
        ("p + q * r = s", "p + (q * r) = s") ::
        ("p * q + r = s", "(p * q) + r = s") ::
        ("p - q * r = s", "p - (q * r) = s") ::
        ("p * q - r = s", "(p * q) - r = s") ::
        ("-p + q = s", "(-p) + q = s") ::
        ("p - q - s = 0", "(p-q) - s = 0") ::
        ("p^2 >= 0", "(p^2) >= 0") ::
        ("p^2 + q^2 = s^2", "(p^2) + (q^2) = (s^2)") ::
        ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0") ::
        ("1^2 + 3^2 = s^2", "(1^2) + (3^2) = (s^2)") ::
        ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0") ::
        // implicit {} either assumed correctly or rejected
        ("[ p:=1; p:=2; ++ p:=3;] p>0", "[ {p:=1; p:=2;} ++ p:=3;] p>0") ::
        ("[ p:=1; ++ p:=2; p:=3;] p>0", "[ p:=1; ++ {p:=2; p:=3;}] p>0") ::
        ("[ p:=1; p:=2; {p:=3;}*] p>0", "[ p:=1; p:=2; {{p:=3;}*}] p>0") ::
        ("[ p:=1; p:=2; ++ {p:=3;}*] p>0", "[ {p:=1; p:=2;} ++ {{p:=3;}*}] p>0") :: Nil

    for (pair <- equalPairs) {
      val left: Expression = Parser(pair._1)
      val right: Expression = Parser(pair._2)
      left should be(right)
    }
  }

  it should "parse (demonic) choices" in {
    Parser("a;++b;") shouldBe Choice(ProgramConst("a"), ProgramConst("b"))
    Parser("a; ∪ b;") shouldBe Parser("a;++b;")
    Parser("{a;^@++b;^@}^@") shouldBe Dual(Choice(Dual(ProgramConst("a")), Dual(ProgramConst("b"))))
    Parser("a;--b;") shouldBe Parser("{a;^@++b;^@}^@")
    Parser("a; ∩ b;") shouldBe Parser("a;--b;")
  }

  it should "parse precedence consistently" in {
    Parser("a;b;++c;") shouldBe Choice(Compose(ProgramConst("a"), ProgramConst("b")), ProgramConst("c"))
    Parser("a;b; ∩ c;") shouldBe
      Dual(Choice(Dual(Compose(ProgramConst("a"), ProgramConst("b"))), Dual(ProgramConst("c"))))
    Parser("a;b;--c;") shouldBe Parser("a;b; ∩ c;")
  }

  it should "parse (demonic) loops" in {
    Parser("{a;}*") shouldBe Loop(ProgramConst("a"))
    Parser("{{a;^@}*}^@") shouldBe Dual(Loop(Dual(ProgramConst("a"))))
    Parser("{a;}×") shouldBe Parser("{{a;^@}*}^@")
  }

  it should "parse (demonic) tests" in {
    Parser("?P();") shouldBe Test(PredOf(Function("P", None, Unit, Bool), Nothing))
    Parser("?P();^@") shouldBe Dual(Test(PredOf(Function("P", None, Unit, Bool), Nothing)))
  }

  it should "parse (demonic) ODEs" in {
    Parser("x'=v") shouldBe Equal(DifferentialSymbol(Variable("x")), Variable("v"))
    Parser("x'=v & x>=0") shouldBe
      And(Equal(DifferentialSymbol(Variable("x")), Variable("v")), GreaterEqual(Variable("x"), Number(0)))
    Parser("{x'=v}") shouldBe ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Variable("v")))
    Parser("{x'=v & x>=0}") shouldBe
      ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Variable("v")), GreaterEqual(Variable("x"), Number(0)))
    Parser("{x'=v}^@") shouldBe Dual(ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Variable("v"))))
    Parser("{{x'=v}}") shouldBe Parser("{x'=v}")
    Parser("{{x'=v & x>=0}}") shouldBe Parser("{x'=v & x>=0}")
    Parser("{{x'=v}^@}") shouldBe Parser("{x'=v}^@")
    Parser("{{x'=v}}^@") shouldBe Parser("{x'=v}^@")
  }

  it should "parse program constants" in {
    Parser("a;") shouldBe ProgramConst("a")
    Parser("a{|^@|};") shouldBe SystemConst("a")
    Parser("{a;b;}*") shouldBe Loop(Compose(ProgramConst("a"), ProgramConst("b")))
    Parser("{a;{d;}*b;{c;}*}*") shouldBe Loop(
      Compose(ProgramConst("a"), Compose(Loop(ProgramConst("d")), Compose(ProgramConst("b"), Loop(ProgramConst("c")))))
    )
    Parser("{a;{d;}*b;{{c}}*}*") shouldBe Loop(Compose(
      ProgramConst("a"),
      Compose(Loop(ProgramConst("d")), Compose(ProgramConst("b"), Loop(ODESystem(DifferentialProgramConst("c"))))),
    ))
  }

  it should "parse implicit functions" in {
    Parser("exp<<<{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)>>(x)") shouldBe
      FuncOf(InterpretedSymbols.expF, Variable("x"))
    Parser(
      "exp<<<{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)>>( (x+exp<<<{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)>>(y)) )"
    ) shouldBe FuncOf(InterpretedSymbols.expF, Plus(Variable("x"), FuncOf(InterpretedSymbols.expF, Variable("y"))))
  }

  it should "generate legible error messages for program consts" in {
    the[ParseException] thrownBy Parser("{a;b}*") should
      (have message
        """1:6 Syntax error. Expression b is not a program: change to b; for a program constant, or to {b} for a differential program constant.
          |Found:    * at 1:6
          |Expected: """.stripMargin or have message
        """1:4 Error parsing program at 1:1
          |Found:    "b}*" at 1:4
          |Expected: ("^@" | ";" | systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | "}")
          |Hint: Try ("^@" | ";" | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | "}")""".stripMargin)

    the[ParseException] thrownBy Parser("{a;{d;}*b;{c}*}*") should
      (have message
        """1:12 Unexpected token cannot be parsed
          |Found:    {c}* at 1:12 to 1:14
          |Expected: {c;}* (loop of program constant)
          |      or: {{c}}* (loop of differential program constant)""".stripMargin or have message
        """1:14 Error parsing program at 1:1
          |Found:    "*}*" at 1:14
          |Expected: ("@invariant" | "@variant" | "^@" | ";" | systemSymbol | programSymbol | variable | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | "}")
          |Hint: Try ("@invariant" | "@variant" | "^@" | ";" | [a-zA-Z] | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | "}")"""
          .stripMargin)

    the[ParseException] thrownBy Parser("{a;{c;}*b}*") should
      (have message
        """1:11 Syntax error. Expression b is not a program: change to b; for a program constant, or to {b} for a differential program constant.
          |Found:    * at 1:11
          |Expected: """.stripMargin or have message
        """1:9 Error parsing program at 1:1
          |Found:    "b}*" at 1:9
          |Expected: ("@invariant" | "@variant" | "^@" | ";" | systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | "}")
          |Hint: Try ("@invariant" | "@variant" | "^@" | ";" | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | "}")"""
          .stripMargin)

    the[ParseException] thrownBy Parser("(A1 & A2) -> {sys} B1 & B2") should
      (have message
        """1:15 Unexpected token cannot be parsed
          |Found:    {sys} at 1:15 to 1:17
          |Expected: [{sys}]
          |      or: <{sys}>""".stripMargin or have message
        """1:14 Error parsing formula at 1:1
          |Found:    "{sys} B1 &" at 1:14
          |Expected: ("true" | "false" | "\\forall" | "\\exists" | "∀" | "∃" | "[" | "<" | "!" | predicational | "⎵" | "__________" | comparison | ident | "(")
          |Hint: Try ("true" | "false" | "\\forall" | "\\exists" | "∀" | "∃" | "[" | "<" | "!" | [a-zA-Z] | "⎵" | "__________" | "(" | [0-9] | "." | "•" | "-")"""
          .stripMargin)

    // @note {sys} is an ODESystem with differential program constant sys and doesn't require ;
    the[ParseException] thrownBy Parser("A1;{sys}B1") should
      (have message
        """1:11 Unexpected token cannot be parsed
          |Found:    <EOF> at 1:11 to EOF$
          |Expected: ;""".stripMargin or have message
        """1:9 Error parsing fullExpression at 1:1
          |Found:    "B1" at 1:9
          |Expected: ("@invariant" | "@variant" | "^@" | ";" | systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | end-of-input)
          |Hint: Try ("@invariant" | "@variant" | "^@" | ";" | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | end-of-input)"""
          .stripMargin)

    the[ParseException] thrownBy Parser("(A1 -> {sys} B1) & (A2 -> {sys} B2)") should
      (have message
        // @todo not great yet
        // parsing fails on &, but
        // parser l. 730ff case r :+ Expr(t1, sl) :+ (optok1@Token(tok:OPERATOR,_)) :+ Expr(t2, el)
        // needs to be permissive to support implicit parentheses (e.g., allows stack "p>0 & q" because "<=4" might follow)
        // and additionally elaboration of term A1 to a predicate happens only after the right-hand side of -> is a formula
        """1:18 Operator -> at 1:5 to 1:6 may connect non-matching kinds: A1->{sys} (Term->Program)
          |Found:    & at 1:18
          |Expected: """.stripMargin or have message
        // better, but still not pointing to the missing ; after sys
        """1:8 Error parsing formula at 1:2
          |Found:    "{sys} B1) " at 1:8
          |Expected: ("true" | "false" | "\\forall" | "\\exists" | "∀" | "∃" | "[" | "<" | "!" | predicational | "⎵" | "__________" | comparison | ident | "(")
          |Hint: Try ("true" | "false" | "\\forall" | "\\exists" | "∀" | "∃" | "[" | "<" | "!" | [a-zA-Z] | "⎵" | "__________" | "(" | [0-9] | "." | "•" | "-")"""
          .stripMargin)

    the[ParseException] thrownBy Parser("[sense][ctrl;plant;]x>y") should
      (have message
        """1:7 Unexpected token cannot be parsed
          |Found:    ] at 1:7
          |Expected: ;""".stripMargin or have message
        """1:2 Error parsing program at 1:2
          |Found:    "sense][ctr" at 1:2
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)

    the[ParseException] thrownBy Parser("[sense;][ctrl;plant]x>y") should
      (have message
        """1:20 Unexpected token cannot be parsed
          |Found:    ] at 1:20
          |Expected: ;""".stripMargin or have message
        """1:15 Error parsing formula at 1:1
          |Found:    "plant]x>y" at 1:15
          |Expected: ("^@" | ";" | systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | "]")
          |Hint: Try ("^@" | ";" | "?" | "if" | "{" | "__________" | "++" | "∪" | "--" | "∩" | "]")""".stripMargin)
  }

  it should "now swallow parse exceptions when parsing sequents" in {
    the[ParseException] thrownBy "==> [x'=:=2*y;][y':=-4*x;]4*(2*x*x')+2*(2*y*y')=0".asSequent should
      (have message
        """1:5 Missing right-hand side x'=
          |Found:    := at 1:5 to 1:6
          |Expected: $$$T""".stripMargin or have message
        """1:6 Error parsing program at 1:6
          |Found:    "x'=:=2*y;]" at 1:6
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)
  }

  it should "be the case that r_0 becomes Variable(r, Some(0), Real)" in {
    Parser("r_0 > 0") should be(Greater(Variable("r", Some(0), Real), Number(0)))
  }

  it should "fail to parse bad input" in {
    val badInputs = "\\forall x x > 2 > 3" :: Nil

    for (badInput <- badInputs) { a[Exception] should be thrownBy { Parser(makeInput(badInput)) } }
  }

  it should "parse quantified differential symbols" in {
    val xp = DifferentialSymbol(Variable("x"))
    Parser("\\forall x' x'>=0") shouldBe Forall(xp :: Nil, GreaterEqual(xp, Number(0)))
    Parser("\\exists x' x'>=0") shouldBe Exists(xp :: Nil, GreaterEqual(xp, Number(0)))
  }

  it should "parse all positive examples" in {
    val files = "abs.key" :: "dia.key" :: "ETCS-essentials.key" :: "ETCS-essentials-loopinv.key" :: "ETCS-safety.key" ::
      "forall.key" :: "functions.key" :: "jdq2.key" :: "passivesafety.key" :: "sections.key" :: "semicolons.key" ::
      "test.key" :: "unity.key" :: Nil

    forEvery(Table(("filename"), files: _*))({ fn =>
      val src = Source.fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/positive/" + fn)).mkString
      ArchiveParser.parser(src) // test fails on exception.
    })
  }

  it should "parse predicates using functions" in {
    val src = Source
      .fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/positive/functions.key"))
      .mkString
    ArchiveParser.parser(src)
  }

  it should "not parse any negative examples" in {
    val files =
      (
        "finishparse.key",
        """<somewhere> assertion failed: Cannot elaborate:
          |  Symbol x used with inconsistent kinds x:Trafo,x:Real
          |Found:    <unknown> at <somewhere>
          |Expected: <unknown>""".stripMargin,
        """<somewhere> assertion failed: Cannot elaborate:
          |  Symbol x used with inconsistent kinds x:Trafo,x:Real
          |Found:    <unknown> at <somewhere>
          |Expected: <unknown>""".stripMargin,
      ) ::
        (
          "scolon1.key",
          "8:10 Unexpected token cannot be parsed\nFound:    > at 8:10",
          "8:10 Error parsing program at 8:5\nFound:    \"> = 0\"",
        ) ::
        (
          "scolon2.key",
          "8:12 Unexpected token cannot be parsed\nFound:    = at 8:12",
          "8:10 Error parsing program at 8:5\nFound:    \"> = 0\"",
        ) ::
        (
          "scolon3.key",
          "8:12 Unexpected token cannot be parsed\nFound:    > at 8:12",
          "8:5 Error parsing program at 8:5\nFound:    \"a' = 0 > =\"",
        ) :: Nil
    // ("UndeclaredVariables.key", "TODO") :: Nil //@note not yet caught (LAX?)

    forEvery(Table(("filename", "msg1", "msg2"), files: _*))({ (fn, m1, m2) =>
      val src = Source.fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/negative/" + fn)).mkString
      val ex = the[ParseException] thrownBy ArchiveParser.parser(src)
      ex.getMessage should (startWith(m1) or startWith(m2))
    })
  }

  it should "elaborate variables to function in type analysis" in {
    val input = """ArchiveEntry "Test"
                  |Definitions Real A; End.
                  |ProgramVariables Real x; End.
                  |Problem A>=0 -> [x:=A;]x>=0 End.
                  |End.
      """.stripMargin

    val fml = ArchiveParser.parser(input).loneElement.model
    val x = Variable("x")
    val a = FuncOf(Function("A", None, Unit, Real), Nothing)
    fml shouldBe Imply(GreaterEqual(a, Number(0)), Box(Assign(x, a), GreaterEqual(x, Number(0))))
  }

  it should "not elaborate bound variables to functions in type analysis" in {
    val input = """ArchiveEntry "Test"
                  |Definitions Real A; End.
                  |ProgramVariables Real x; End.
                  |Problem A>=0 -> [x:=A;A:=2;]x>=0 End.
                  |End.
      """.stripMargin

    the[ParseException] thrownBy ArchiveParser.parser(input) should have message
      """<somewhere> Unable to elaborate to function symbols: Elaboration tried replacing A in literal bound occurrence inside A>=0->[x:=A;A:=2;]x>=0
        |Found:    <unknown> at <somewhere>
        |Expected: <unknown>""".stripMargin
  }

  /*
   *@TODO setup pretty-printer so that it can be parsed again.
  it should "parse pretty-prints of random formulas" in {
	  val rand = RandomFormula

      for(i <- 1 to 5) {
        val left : Expr = rand.nextFormula(10)
        val print : String = KeYmaeraPrettyPrinter.stringify(left)
        val right : Expr = parser.runParser(print)
        left should be (right)
      }
    }
  }
   */

  it should "parse if-then-else" in {
    Parser
      .parser
      .programParser(
        """
          |if (x>0) { x:=x; }
          |else { x:=-x; }
      """.stripMargin
      ) shouldBe Choice(
      Compose(Test("x>0".asFormula), Assign("x".asVariable, "x".asVariable)),
      Compose(Test("!x>0".asFormula), Assign("x".asVariable, Neg("x".asVariable))),
    )
  }

  it should "report missing opening bracket after else" in {
    the[ParseException] thrownBy
      Parser
        .parser
        .programParser(
          """
            |if (x>0) { x:=x; }
            |else if (x<0) { x:=-x; }
            |else { x:=7; }
      """.stripMargin
        ) should
      (have message
        """3:6 Unexpected token cannot be parsed
          |Found:    if at 3:6 to 3:7
          |Expected: {""".stripMargin or have message
        """3:6 Error parsing program at 2:1
          |Found:    "if (x<0) {" at 3:6
          |Expected: "{"
          |Hint: Try "{"""".stripMargin)
  }

  it should "parse a comma-separated list of expressions" in {
    Parser.parseExpressionList("x>=0,y>=0,z") shouldBe List("x>=0".asFormula, "y>=0".asFormula, "z".asTerm)
    Parser.parseExpressionList("f(x,y)") shouldBe List("f(x,y)".asTerm)
    Parser.parseExpressionList("f(x,(y,z))") shouldBe List("f(x,(y,z))".asTerm)
    Parser.parseExpressionList("x=1,f(x,(y,z)),g(a,b),z") shouldBe
      List("x=1".asFormula, "f(x,(y,z))".asTerm, "g(a,b)".asTerm, "z".asTerm)
    Parser.parseExpressionList("[{x'=y,y'=z}]x>=0") shouldBe List("[{x'=y,y'=z}]x>=0".asFormula)
    Parser.parseExpressionList("[{x'=y,y'=f(x,y)}]P(x,z)") shouldBe List("[{x'=y,y'=f(x,y)}]P(x,z)".asFormula)
    Parser.parseExpressionList(
      "[{x'=y,y'=f(x,y) & <{x'=4,t'=1}>x>=2*g(x,t)}]P(x,z) -> [{x'=-3,y'=-2};?P(x,y,z);]x>=2, x>=2"
    ) shouldBe List(
      "[{x'=y,y'=f(x,y) & <{x'=4,t'=1}>x>=2*g(x,t)}]P(x,z) -> [{x'=-3,y'=-2};?P(x,y,z);]x>=2".asFormula,
      "x>=2".asFormula,
    )
  }

  it should "fail for imbalanced parentheses in lists of expressions" in {
    the[ParseException] thrownBy Parser.parseExpressionList("f(x,y") should
      (
        // KeYmaeraX parser error
        (pointAt(1, 2) and mention("Imbalanced parenthesis"))

        // DLParser error
        or pointAt(1, 1)
      )

    the[ParseException] thrownBy Parser.parseExpressionList("f(x,y, x>=2") should
      (
        // KeYmaeraX parser error
        (pointAt(1, 12) and mention("Operator COMMA$ expects a Term but got the Formula x>=2"))

        // DLParser error
        or pointAt(1, 1)
      )
  }

  "Annotation parsing" should "populate easy loop annotations" in {
    val input = "x>=2 -> [{x:=x+1;}*@invariant(x>=1)]x>=0"
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=1".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    Parser(input)
  }

  it should "add () to functions used as variables" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real y(); End. ProgramVariables Real x; End. Problem x>=y+2 -> [{x:=x+1;}*@invariant(x>=y+1)]x>=y End. End."
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    ArchiveParser.parser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  it should "report functions non-expanded" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real y() = 3+7; End. ProgramVariables Real x; End. Problem x>=y+2 -> [{x:=x+1;}*@invariant(x>=y()+1)]x>=y End. End."
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    ArchiveParser.parser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  it should "report functions non-expanded (2)" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real y() = 3+z(); Real z() = 7; End. ProgramVariables Real x; End. Problem x>=y+2 -> [{x:=x+1;}*@invariant(x>=y()+1)]x>=y End. End."
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    ArchiveParser.parser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  it should "FEATURE_REQUEST: detect cycles when expanding functions recursively to their definition" taggedAs
    TodoTest ignore {
      val input =
        "ArchiveEntry \"Test\" Definitions Real y() = 3+z(); Real z() = 7*y(); End. ProgramVariables Real x; End. Problem x>=y+2 -> [{x:=x+1;}*@invariant(x>=y()+1)]x>=y End. End."
      val listener = mock[(Program, Formula) => Unit]
      (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once()
      Parser.parser.setAnnotationListener(listener)
      ArchiveParser.parser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
    }

  it should "add () and report functions non-expanded" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real y() = 3+7; End. ProgramVariables Real x; End. Problem x>=y+2 -> [{x:=x+1;}*@invariant(x>=y+1)]x>=y End. End."
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    ArchiveParser.parser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  it should "not expand properties to their definition" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Bool init() <-> x>=2; Bool safe(Real x) <-> x=0; End. ProgramVariables Real x; End. Problem init() -> [{x:=x+1;}*]safe(x) End. End."
    val entry = ArchiveParser.parser(input).loneElement
    inside(entry.defs.decls(Name("init", None))) { case Signature(domain, sort, argNames, expr, _) =>
      domain.value shouldBe Unit
      sort shouldBe Bool
      argNames shouldBe Some(Nil)
      expr.toOption.value.value shouldBe "x>=2".asFormula
    }
    inside(entry.defs.decls(Name("safe", None))) { case Signature(domain, sort, argNames, expr, _) =>
      domain.value shouldBe Real
      sort shouldBe Bool
      argNames shouldBe Some((Name("x", None), Real) :: Nil)
      expr.toOption.value.value shouldBe "x=0".asFormula
    }
    entry.model shouldBe "init() -> [{x:=x+1;}*]safe(x)".asFormula
  }

  it should "report properties non-expanded in annotations" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Bool inv() <-> x>=1; End. ProgramVariables Real x; End. Problem x>=2 -> [{x:=x+1;}*@invariant(inv())]x>=0 End. End."
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "inv()".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    ArchiveParser.parser(input).loneElement.model shouldBe "x>=2 -> [{x:=x+1;}*]x>=0".asFormula
  }

  it should "report functions in properties non-expanded" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real y() = 3+7; Bool inv() <-> x>=y(); End. ProgramVariables Real x; End. Problem x>=2 -> [{x:=x+1;}*@invariant(inv())]x>=0 End. End."
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "inv()".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    ArchiveParser.parser(input).loneElement.model shouldBe "x>=2 -> [{x:=x+1;}*]x>=0".asFormula
  }

  it should "add () to functions in properties" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real b; Real y() = 3+b; Bool inv() <-> x>=y(); End. ProgramVariables Real x; End. Problem x>=2 -> [{x:=x+b;}*@invariant(inv())]x>=0 End. End."
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x:=x+b();}*".asProgram, "inv()".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    val entry = ArchiveParser.parser(input).loneElement
    inside(entry.defs.decls(Name("inv", None))) { case Signature(domain, sort, argNames, expr, _) =>
      domain.value shouldBe Unit
      sort shouldBe Bool
      argNames shouldBe Some(Nil)
      expr.toOption.value.value shouldBe "x>=y()".asFormula
    }
    inside(entry.defs.decls(Name("y", None))) { case Signature(domain, sort, argNames, expr, _) =>
      domain.value shouldBe Unit
      sort shouldBe Real
      argNames shouldBe Some(Nil)
      expr.toOption.value.value shouldBe "3+b()".asTerm
    }
    entry.model shouldBe "x>=2 -> [{x:=x+b();}*]x>=0".asFormula
  }

  it should "complain about sort mismatches in function declaration and operator" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real y() <-> 3+7; End. ProgramVariables Real x; End. Problem x>=2 -> x>=0 End. End."
    the[ParseException] thrownBy ArchiveParser.parser(input) should
      (have message
        """1:42 Function must be defined by equality
          |Found:    <-> at 1:42 to 1:44
          |Expected: =""".stripMargin or have message
        """1:49 Error parsing comparator at 1:49
          |Found:    "; End. Pro" at 1:49
          |Expected: ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | "=" | "!=" | "≠" | ">=" | "≥" | ">" | "<=" | "≤" | "<")
          |Hint: Try ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | "=" | "!=" | "≠" | ">=" | "≥" | ">" | "<=" | "≤" | "<")"""
          .stripMargin)
  }

  it should "complain about sort mismatches" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real y() = 3>2; End. ProgramVariables Real x; End. Problem x>=2 -> x>=0 End. End."
    the[ParseException] thrownBy ArchiveParser.parser(input) should
      (have message
        """1:44 Expected a Term but got the Formula 3>2
          |Found:    3>2 at 1:44 to 1:46
          |Expected: Term""".stripMargin or have message
        """1:45 Error parsing definitions at 1:21
          |Found:    ">2; End. P" at 1:45
          |Expected: ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | ";")
          |Hint: Try ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | ";")""".stripMargin)
  }

  it should "complain about non-delimited definitions" in {
    val input =
      "ArchiveEntry \"Test\" Definitions Real y() = (3>2; End. ProgramVariables Real x; End. Problem x>=2 -> x>=0 End. End."
    the[ParseException] thrownBy ArchiveParser.parser(input) should
      (have message
        """1:44 Imbalanced parenthesis
          |Found:    ( at 1:44
          |Expected: """.stripMargin or have message
        """1:46 Error parsing termList at 1:44
          |Found:    ">2; End. P" at 1:46
          |Expected: ([0-9] | "." | ")" | "^" | "*" | "/" | "+" | "-" | ",")
          |Hint: Try ([0-9] | "." | ")" | "^" | "*" | "/" | "+" | "-" | ",")""".stripMargin)
  }

  it should "populate easy ODE annotations" in {
    val input = "x>=2 -> [{x'=1}@invariant(x>=1)]x>=0"
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x'=1}".asProgram, "x>=1".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    Parser(input)
  }

  it should "populate ODE annotations with old(.)" in {
    val input = "x>=2 -> [{x'=1}@invariant(x>=old(x))]x>=0"
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x'=1}".asProgram, "x>=old(x)".asFormula).once()
    Parser.parser.setAnnotationListener(listener)
    Parser(input)
  }

  it should "parse multiple annotations" in {
    val input = "x>=3 -> [{x'=1}@invariant(x>=2, x>=1)]x>=0"
    val listener = mock[(Program, Formula) => Unit]
    inSequence {
      (listener.apply _).expects("{x'=1}".asProgram, "x>=2".asFormula).once()
      (listener.apply _).expects("{x'=1}".asProgram, "x>=1".asFormula).once()
    }
    Parser.parser.setAnnotationListener(listener)
    Parser(input)
  }

  it should "bind annotations strongest" in {
    val input = "x>=3 -> [x:=2; ++ x:=3; {x'=1}@invariant(x>=2)]x>=0"
    val listener = mock[(Program, Formula) => Unit]
    inSequence { (listener.apply _).expects("{x'=1}".asProgram, "x>=2".asFormula).once() }
    Parser.parser.setAnnotationListener(listener)
    Parser(input)
  }

  it should "parse @variant annotation" in {
    val input = "x=0 -> <{x:=x+1;}*@variant(\\exists i i+x>=5)>x>=5"
    val listener = mock[(Program, Formula) => Unit]
    inSequence { (listener.apply _).expects("{x:=x+1;}*".asProgram, "\\exists i i+x>=5".asFormula).once() }
    Parser.parser.setAnnotationListener(listener)
    Parser(input)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Begin ALP Parser tests
  //////////////////////////////////////////////////////////////////////////////

  "The axiom file parser" should "placeholder" in {}

  // @todo adapt file to new parser and to new location of axioms file, which is in source
  // This test case is pointless because basically every other test case will fail in a completely obvious way if the axiom file doesn't parse, and we don't run this one before anyone else, so we're just wasting cycles...
  ignore should "parse all positive axiom examples" in {
    val files = "axioms.key.alp" ::
//      "QE94.alp" ::
//      "QE96.alp" ::
      Nil

    for (testFile <- files) {
      val src = Source
        .fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/positiveALP/" + testFile))
        .mkString
      try {
        KeYmaeraXAxiomParser(src) // test fails on exception.
      } catch { case ex: Exception => fail("Unable to parse " + testFile, ex) }
    }
  }

  // @todo this is a pretty random test case.
//  "The lemma file parser" should "parse all positive axiom examples" in {
//    val files =
//        "QE94.alp" ::
//        "QE96.alp" ::
//        Nil
//
//    for(testFile <- files) {
//      val src = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/positiveALP/" + testFile)).mkString
//      try {
//        KeYmaeraXLemmaParser(src) //test fails on exception.
//      } catch {
//        case ex: Exception => fail("Unable to parse " + testFile, ex)
//      }
//    }
//  }

  "Random test cases from development" should "reduce systems of diffEqs correctly." in {
    "[{x'=y, y'=x}]true".asFormula shouldBe Box(
      ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), y), AtomicODE(DifferentialSymbol(y), x)), True),
      True,
    )
  }

  "String converter" should "parse substitution pair with 0-based dots" in {
    // @note conversion to all 1-based indices also acceptable
    "gt(._0,._1) ~> ._0 > ._1".asSubstitutionPair shouldBe SubstitutionPair(
      PredOf(Function("gt", None, Tuple(Real, Real), Bool, None), Pair(DotTerm(Real, Some(0)), DotTerm(Real, Some(1)))),
      Greater(DotTerm(Real, Some(0)), DotTerm(Real, Some(1))),
    )
  }

  "Sequent parser" should "split formula lists" in {
    SequentParser.parseFormulaList("x=2, y=3, z=4") should contain theSameElementsInOrderAs
      List("x=2".asFormula, "y=3".asFormula, "z=4".asFormula)
    SequentParser.parseFormulaList("f(x,y)=2, g(y)=3, h(z,3*(2+4))=4") should contain theSameElementsInOrderAs
      List("f(x,y)=2".asFormula, "g(y)=3".asFormula, "h(z,3*(2+4))=4".asFormula)
  }
}
