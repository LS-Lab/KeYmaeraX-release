package edu.cmu.cs.ls.keymaerax.parser

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.CustomAssertions.withSafeClue

import org.scalatest._
import org.scalatest.LoneElement._
import org.scalatest.Inside._
import org.scalatest.OptionValues._

import org.scalamock.scalatest.MockFactory

import scala.collection.immutable._

class ParserTests extends FlatSpec with Matchers with BeforeAndAfterEach with MockFactory {
  override def beforeEach(): Unit = { PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp) }
  override def afterEach(): Unit = { KeYmaeraXParser.setAnnotationListener((_, _) => {}) }

  // type declaration header for tests
  def makeInput(program : String) : String = {
    "Functions. B a. B b. B c. End." +
    "ProgramVariables. R p. R q. R r. R s. R r_0. End." +
    "Problem." + program + "\nEnd."
  }

//  val parser = new KeYmaeraParser(false)
//  val alpParser = parser.ProofFileParser
  private val x = Variable("x", None, Real)
  private val y = Variable("y", None, Real)

  "The problem parser" should "reject strings containing non-ASCII characters" in {
    def input(s: String) =
      s"""
        |ProgramVariables.
        |  R x.
        |End.
        |Problem.
        |  [x := $s;]x > 3
        |End.
      """.stripMargin
    KeYmaeraXArchiveParser(input("1")) //the problem should be exactly the fact that we pass in some unicode.
    a [Exception] shouldBe thrownBy(KeYmaeraXArchiveParser("\\u03C0"))
  }

  it should "parse nullary predicate definitions" in {
    val input = """
      |Definitions.
      |  B J() <-> ( 1>=0 ).
      |End.
      |ProgramVariables.
      |  R x.
      |End.
      |Problem.
      |  J() -> [{x:=x+1;}*@invariant(J())]J()
      |End.
    """.stripMargin
    val entry = KeYmaeraXArchiveParser(input).loneElement
    entry.defs.decls(("J", None))._4.value shouldBe "1>=0".asFormula
    entry.model shouldBe "J() -> [{x:=x+1;}*]J()".asFormula
  }

  it should "parse unary predicate definitions" in {
    val input = """
      |Definitions.
      |  B J(R x) <-> ( x>=0 ).
      |End.
      |ProgramVariables.
      |  R x.
      |End.
      |Problem.
      |  J(x) -> [{x:=x+1;}*@invariant(J(x))]J(x)
      |End.
    """.stripMargin
    val entry = KeYmaeraXArchiveParser(input).loneElement
    inside (entry.defs.decls(("J", None))) {
      case (domain, sort, argNames, expr, _) =>
        domain.value shouldBe Real
        sort shouldBe Bool
        argNames shouldBe Some((("x", None), Real) :: Nil)
        expr.value shouldBe ".>=0".asFormula
    }
    entry.model shouldBe "J(x) -> [{x:=x+1;}*]J(x)".asFormula
  }

  it should "parse binary predicate definitions" in {
    val input = """
      |Definitions.
      |  B J(R x, R y) <-> ( x>=y ).
      |End.
      |ProgramVariables.
      |  R x.
      |  R y.
      |End.
      |Problem.
      |  J(x,y) -> [{x:=x+1;}*@invariant(J(x,y))]J(x,y)
      |End.
    """.stripMargin
    val entry = KeYmaeraXArchiveParser(input).loneElement
    inside (entry.defs.decls(("J", None))) {
      case (domain, sort, argNames, expr, _) =>
        domain.value shouldBe Tuple(Real, Real)
        sort shouldBe Bool
        argNames shouldBe Some((("x", None), Real) :: (("y", None), Real) :: Nil)
        expr.value shouldBe "._0>=._1".asFormula
    }
    entry.model shouldBe "J(x,y) -> [{x:=x+1;}*]J(x,y)".asFormula
  }

  it should "parse program definitions" in {
    val input = """
      |Definitions.
      |  HP prg ::= { x:=x+1; }.
      |End.
      |ProgramVariables.
      |  R x.
      |End.
      |Problem.
      |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
      |End.
    """.stripMargin
    val entry = KeYmaeraXArchiveParser(input).loneElement
    inside (entry.defs.decls(("prg", None))) {
      case (domain, sort, argNames, expr, _) =>
        domain.value shouldBe Unit
        sort shouldBe Trafo
        argNames shouldBe 'empty
        expr.value shouldBe "x:=x+1;".asProgram
    }
    entry.model shouldBe "x>=0 -> [{prg;}*]x>=0".asFormula
  }

  it should "report useful message on missing semicolon in program variable declaration" in {
    val input = """ProgramVariables.
                  |  R x
                  |End.
                  |Problem.
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                """.stripMargin
    the [ParseException] thrownBy KeYmaeraXArchiveParser(input) should have message
      """3:1 Unexpected token in ProgramVariables block
        |Found:    End at 3:1 to 3:3
        |Expected: ;
        |      or: ,""".stripMargin
  }

  it should "report useful message on missing semicolon in function definitions" in {
    val input = """Definitions.
                  |  R func() = ( 4 )
                  |End.
                  |ProgramVariables.
                  |  R x.
                  |End.
                  |Problem.
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                """.stripMargin
    the [ParseException] thrownBy KeYmaeraXArchiveParser(input) should have message
      """3:1 Unexpected token in function definition
        |Found:    End at 3:1 to 3:3
        |Expected: =
        |      or: ;""".stripMargin
  }

  it should "report useful message on missing semicolon in program definitions" in {
    val input = """Definitions.
                  |  HP prg ::= { x:=x+1; }
                  |End.
                  |ProgramVariables.
                  |  R x.
                  |End.
                  |Problem.
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                """.stripMargin
    the [ParseException] thrownBy KeYmaeraXArchiveParser(input) should have message
      """3:1 Unexpected token in program definition
        |Found:    End at 3:1 to 3:3
        |Expected: ::=
        |      or: ;""".stripMargin
  }

  it should "report useful message on missing braces in program definitions" in {
    val input = """Definitions.
                  |  HP prg ::= x:=x+1;
                  |End.
                  |ProgramVariables.
                  |  R x.
                  |End.
                  |Problem.
                  |  x>=0 -> [{prg;}*@invariant(x>=0)]x>=0
                  |End.
                """.stripMargin
    the [ParseException] thrownBy KeYmaeraXArchiveParser(input) should have message
      """2:14 Missing program definition start delimiter
        |Found:    ID("x") at 2:14
        |Expected: {""".stripMargin
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
      //nested modalities
      ("< p:=1; > <p:=2; > p>0", "<p:=1;>(<p:=2;>p>0)") ::
      ("[ p:=1; ] <p:=2; > p>0", "[p:=1;](<p:=2;>p>0)") ::
      ("< p:=1; > [p:=2; ] p>0", "<p:=1;>([p:=2;]p>0)") ::
      //[], <>, \forall, \exists magic.
      ("\\forall x [x:=1;]<x:=2;>x>0","\\forall x ([x:=1;]<x:=2;>(x>0))") ::
      ("\\exists x [x:=1;]<x:=2;>x>0","\\exists x ([x:=1;]<x:=2;>(x>0))") ::
      ("[p:=0;]\\forall x [x:=p;] \\exists y [q := x + y; ] q > 0", "[p:=0;](\\forall x [x:=p;] (\\exists y [q := x + y; ] q > 0))") ::
      // <> vs >.
      ("< ?p>q; > p > 1", "<?(p > q);>(p>1)") ::
      ("[ ?p>q; ] p > 1", "[?(p > q);](p>1)") ::
      ("< ?a < 0; ++ ?a < 0; > a < 0", "< {?a < 0;} ++ {?a < 0;} > a < 0") ::
      //arith.
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
      ("p^5 * p^3 * q^2 >= 0", "(p^5) * (p^3) * (q^2) >= 0")::
      // implicit {} either assumed correctly or rejected
      ("[ p:=1; p:=2; ++ p:=3;] p>0", "[ {p:=1; p:=2;} ++ p:=3;] p>0") ::
      ("[ p:=1; ++ p:=2; p:=3;] p>0", "[ p:=1; ++ {p:=2; p:=3;}] p>0") ::
      ("[ p:=1; p:=2; {p:=3;}*] p>0", "[ p:=1; p:=2; {{p:=3;}*}] p>0") ::
      ("[ p:=1; p:=2; ++ {p:=3;}*] p>0", "[ {p:=1; p:=2;} ++ {{p:=3;}*}] p>0") ::
      Nil

    for(pair <- equalPairs) {
      val left : Expression = KeYmaeraXParser(pair._1)
      val right : Expression = KeYmaeraXParser(pair._2)
      left should be (right)
    }
  }

  it should "be the case that r_0 becomes Variable(r, Some(0), Real)" in {
    KeYmaeraXParser("r_0 > 0") should be (Greater(Variable("r", Some(0), Real), Number(0)))
  }

  it should "fail to parse bad input" in {
    val badInputs =
      "\\forall x x > 2 > 3" ::
      Nil

    for(badInput <- badInputs) {
      a [Exception] should be thrownBy {
        KeYmaeraXParser(makeInput(badInput))
      }
    }
  }

  it should "parse all positive examples" in {
    val files =
      "abs.key" ::
      "dia.key" ::
      "ETCS-essentials.key" ::
      "ETCS-essentials-loopinv.key" ::
      "ETCS-safety.key" ::
      "forall.key" ::
      "functions.key" ::
      "jdq2.key" ::
      "passivesafety.key" ::
      "sections.key" ::
      "semicolons.key" ::
      "test.key" ::
      "unity.key" :: Nil

    for(testFile <- files) {
      val src = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/positive/" + testFile)).mkString
      withSafeClue(testFile) {
        KeYmaeraXArchiveParser(src) //test fails on exception.
      }
    }
  }

  it should "parse predicates using functions" in {
    val src = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/positive/functions.key")).mkString
    KeYmaeraXArchiveParser(src)
  }

  it should "not parse any negative examples" in {
    val files =
      ("finishparse.key", """<somewhere> assertion failed: Cannot elaborate:
                            |  Symbol x used with inconsistent kinds x:Trafo,x:Real
                            |Found:    <unknown> at <somewhere>
                            |Expected: <unknown>""".stripMargin) ::
      ("scolon1.key", "6:10 Unexpected token cannot be parsed\nFound:    > at 6:10") ::
      ("scolon2.key", "6:12 Unexpected token cannot be parsed\nFound:    = at 6:12") ::
      ("scolon3.key", "6:12 Unexpected token cannot be parsed\nFound:    > at 6:12") :: Nil
      //("UndeclaredVariables.key", "TODO") :: Nil //@note not yet caught (LAX?)

    for((testFile, message) <- files) {
      val src = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/negative/" + testFile)).mkString
      try {
        KeYmaeraXArchiveParser(src)
        fail("A negative file parsed correctly: " + testFile)
      }
      catch {
        case e: Throwable =>
          withSafeClue(testFile) { e.getMessage should startWith (message) }
      }
    }
  }

  it should "elaborate variables to function in type analysis" in {
    val input =
      """
        |Functions. R A. End.
        |ProgramVariables. R x. End.
        |Problem. A>=0 -> [x:=A;]x>=0 End.
      """.stripMargin

    val fml = KeYmaeraXArchiveParser(input).loneElement.model
    val x = Variable("x")
    val a = FuncOf(Function("A", None, Unit, Real), Nothing)
    fml shouldBe Imply(
      GreaterEqual(a, Number(0)),
      Box(Assign(x, a), GreaterEqual(x, Number(0))))
  }

  it should "not elaborate bound variables to functions in type analysis" in {
    val input =
      """
        |Functions. R A. End.
        |ProgramVariables. R x. End.
        |Problem. A>=0 -> [x:=A;A:=2;]x>=0 End.
      """.stripMargin

    the [ParseException] thrownBy KeYmaeraXArchiveParser(input) should have message
      """<somewhere> assertion failed: Elaboration tried replacing A in literal bound occurrence inside A>=0->[x:=A;A:=2;]x>=0
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
    KeYmaeraXParser.programParser(
      """
        |if (x>0) { x:=x; }
        |else { x:=-x; }
      """.stripMargin) shouldBe Choice(
      Compose(Test("x>0".asFormula), Assign("x".asVariable, "x".asVariable)),
      Compose(Test("!x>0".asFormula), Assign("x".asVariable, Neg("x".asVariable))))
  }

  it should "report missing opening bracket after else" in {
    the [ParseException] thrownBy KeYmaeraXParser.programParser(
      """
        |if (x>0) { x:=x; }
        |else if (x<0) { x:=-x; }
        |else { x:=7; }
      """.stripMargin) should have message """3:6 Unexpected token cannot be parsed
                                             |Found:    if at 3:6 to 3:7
                                             |Expected: {""".stripMargin
  }

  "Annotation parsing" should "populate easy loop annotations" in {
    val input = "x>=2 -> [{x:=x+1;}*@invariant(x>=1)]x>=0"
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=1".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXParser(input)
  }

  it should "add () to functions used as variables" in {
    val input = "Functions. R y(). End. ProgramVariables. R x. End. Problem. x>=y+2 -> [{x:=x+1;}*@invariant(x>=y+1)]x>=y End."
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXArchiveParser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  it should "not expand functions to their definition" in {
    val input = "Functions. R y() = (3+7). End. ProgramVariables. R x. End. Problem. x>=y+2 -> [{x:=x+1;}*@invariant(x>=y()+1)]x>=y End."
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXArchiveParser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  it should "not expand functions recursively to their definition" in {
    val input = "Functions. R y() = (3+z()). R z() = (7). End. ProgramVariables. R x. End. Problem. x>=y+2 -> [{x:=x+1;}*@invariant(x>=y()+1)]x>=y End."
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXArchiveParser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  //@todo
  it should "detect cycles when expanding functions recursively to their definition" ignore {
    val input = "Functions. R y() = (3+z()). R z() = (7*y()). End. ProgramVariables. R x. End. Problem. x>=y+2 -> [{x:=x+1;}*@invariant(x>=y()+1)]x>=y End."
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXArchiveParser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  it should "add () but not expand functions to their definition" in {
    val input = "Functions. R y() = (3+7). End. ProgramVariables. R x. End. Problem. x>=y+2 -> [{x:=x+1;}*@invariant(x>=y+1)]x>=y End."
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "x>=y()+1".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXArchiveParser(input).loneElement.model shouldBe "x>=y()+2 -> [{x:=x+1;}*]x>=y()".asFormula
  }

  it should "not expand properties to their definition" in {
    val input = "Functions. B init() <-> (x>=2). B safe(R) <-> (.>=0). End. ProgramVariables. R x. End. Problem. init() -> [{x:=x+1;}*]safe(x) End."
    val entry = KeYmaeraXArchiveParser(input).loneElement
    inside (entry.defs.decls(("init", None))) {
      case (domain, sort, argNames, expr, _) =>
        domain.value shouldBe Unit
        sort shouldBe Bool
        argNames shouldBe Some(Nil)
        expr.value shouldBe "x>=2".asFormula
    }
    inside (entry.defs.decls(("safe", None))) {
      case (domain, sort, argNames, expr, _) =>
        domain.value shouldBe Real
        sort shouldBe Bool
        argNames shouldBe Some((("\\cdot", Some(0)), Real) :: Nil)
        expr.value shouldBe ".>=0".asFormula
    }
    entry.model shouldBe "init() -> [{x:=x+1;}*]safe(x)".asFormula
  }

  it should "not expand properties to their definition in annotations" in {
    val input = "Functions. B inv() <-> (x>=1). End. ProgramVariables. R x. End. Problem. x>=2 -> [{x:=x+1;}*@invariant(inv())]x>=0 End."
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "inv()".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXArchiveParser(input).loneElement.model shouldBe "x>=2 -> [{x:=x+1;}*]x>=0".asFormula
  }

  it should "not expand functions in properties" in {
    val input = "Functions. R y() = (3+7). B inv() <-> (x>=y()). End. ProgramVariables. R x. End. Problem. x>=2 -> [{x:=x+1;}*@invariant(inv())]x>=0 End."
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+1;}*".asProgram, "inv()".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXArchiveParser(input).loneElement.model shouldBe "x>=2 -> [{x:=x+1;}*]x>=0".asFormula
  }

  it should "add () to functions in properties" in {
    val input = "Functions. R b. R y() = (3+b). B inv() <-> (x>=y()). End. ProgramVariables. R x. End. Problem. x>=2 -> [{x:=x+b;}*@invariant(inv())]x>=0 End."
    val listener = mock[(Program,Formula) => Unit]
    (listener.apply _).expects("{x:=x+b();}*".asProgram, "inv()".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    val entry = KeYmaeraXArchiveParser(input).loneElement
    inside (entry.defs.decls(("inv", None))) {
      case (domain, sort, argNames, expr, _) =>
        domain.value shouldBe Unit
        sort shouldBe Bool
        argNames shouldBe Some(Nil)
        expr.value shouldBe "x>=y()".asFormula
    }
    inside (entry.defs.decls(("y", None))) {
      case (domain, sort, argNames, expr, _) =>
        domain.value shouldBe Unit
        sort shouldBe Real
        argNames shouldBe Some(Nil)
        expr.value shouldBe "3+b()".asTerm
    }
    entry.model shouldBe "x>=2 -> [{x:=x+b();}*]x>=0".asFormula
  }

  it should "complain about sort mismatches in function declaration and operator" in {
    val input = "Functions. R y() <-> (3+7). End. ProgramVariables. R x. End. Problem. x>=2 -> x>=0 End."
    the [ParseException] thrownBy KeYmaeraXArchiveParser(input) should have message
      """1:18 Function must be defined by equality
        |Found:    <-> at 1:18 to 1:20
        |Expected: =""".stripMargin
  }

  it should "complain about sort mismatches" in {
    val input = "Functions. R y() = (3>2). End. ProgramVariables. R x. End. Problem. x>=2 -> x>=0 End."
    the [ParseException] thrownBy KeYmaeraXArchiveParser(input) should have message
      """1:21 Impossible elaboration: Operator PSEUDO$ expects a Term as argument but got the Formula 3>2
        |Found:    3>2) at 1:21 to 1:24
        |Expected: Term""".stripMargin
  }

  it should "complain about non-delimited definitions" in {
    val input = "Functions. R y() = (3>2. End. ProgramVariables. R x. End. Problem. x>=2 -> x>=0 End."
    the [ParseException] thrownBy KeYmaeraXArchiveParser(input) should have message
      """1:20 Unmatched opening parenthesis in function definition
        |unmatched: LPAREN$ at 1:20--1:21
        |Found:    NUM(3) at 1:20 to 1:21
        |Expected: )""".stripMargin
  }

  it should "populate easy ODE annotations" in {
    val input = "x>=2 -> [{x'=1}@invariant(x>=1)]x>=0"
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x'=1}".asProgram, "x>=1".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXParser(input)
  }

  it should "populate ODE annotations with old(.)" in {
    val input = "x>=2 -> [{x'=1}@invariant(x>=old(x))]x>=0"
    val listener = mock[(Program, Formula) => Unit]
    (listener.apply _).expects("{x'=1}".asProgram, "x>=old(x)".asFormula).once
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXParser(input)
  }

  it should "parse multiple annotations" in {
    val input = "x>=3 -> [{x'=1}@invariant(x>=2, x>=1)]x>=0"
    val listener = mock[(Program, Formula) => Unit]
    inSequence {
      (listener.apply _).expects("{x'=1}".asProgram, "x>=2".asFormula).once
      (listener.apply _).expects("{x'=1}".asProgram, "x>=1".asFormula).once
    }
    KeYmaeraXParser.setAnnotationListener(listener)
    KeYmaeraXParser(input)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Begin ALP Parser tests
  //////////////////////////////////////////////////////////////////////////////


  "The axiom file parser" should "placeholder" in {}

  //@todo adapt file to new parser and to new location of axioms file, which is in source
  //This test case is pointless because basically every other test case will fail in a completely obvious way if the axiom file doesn't parse, and we don't run this one before anyone else, so we're just wasting cycles...
  ignore should "parse all positive axiom examples" in {
    val files =
      "axioms.key.alp" ::
//      "QE94.alp" ::
//      "QE96.alp" ::
        Nil

    for(testFile <- files) {
      val src = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/dev/t/parsing/positiveALP/" + testFile)).mkString
      try {
        KeYmaeraXAxiomParser(src) //test fails on exception.
      } catch {
        case ex: Exception => fail("Unable to parse " + testFile, ex)
      }
    }
  }

  //@todo this is a pretty random test case.
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
    "[{x'=y, y'=x}]true".asFormula shouldBe Box(ODESystem(DifferentialProduct(
      AtomicODE(DifferentialSymbol(x), y),
      AtomicODE(DifferentialSymbol(y), x)), True), True)
  }
}
