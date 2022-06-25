package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.KeYmaeraXTestTags.TodoTest

import scala.collection.immutable._

/** More tests for KeYmaeraXParser
 */
class MoreParserTests2 extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll {
  private val x = Variable("x")
  private val y = Variable("y")
  private val z = Variable("z")
  private val v = Variable("v")

  private var parser: Parser = _
  private var pp: PrettyPrinter = _

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "false",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName
    ))
  }

  override def beforeEach(): Unit = {
    parser = Parser.parser
    pp = KeYmaeraXPrettyPrinter
  }

  override def afterEach(): Unit = {
    pp = null
    parser = null
  }

  override def afterAll(): Unit = {
    KeYmaeraXTool.shutdown()
  }

  "The parser" should "parse a*(-b-c)" in {
    val input = "a*(-b-c)"

    val parsed = parser(input)

    parsed shouldBe Times(Variable("a"), Minus(Neg(Variable("b")), Variable("c")))
    parsed.prettyString shouldBe input
  }

  it should "parse \\forall x \\forall y \\forall z (x>y & y>z)" in {
    parser("\\forall x \\forall y \\forall z (x>y & y>z)") should be
    Forall(Seq(z), Forall(Seq(z), Forall(Seq(z),
      And(Greater(x, z), Greater(y, z)))))
  }

  it should "parse \\forall x \\exists y \\exists z (x>y & y>z)" in {
    parser("\\forall x \\exists y \\exists z (x>y & y>z)") should be
    Forall(Seq(z), Exists(Seq(z), Exists(Seq(z),
      And(Greater(x, z), Greater(y, z)))))
  }

  it should "parse \\forall x,y,z (x>y & y>z)" in {
    parser("\\forall x,y,z (x>y & y>z)") should be
    Forall(Seq(x, y, z),
      And(Greater(x, z), Greater(y, z)))
  }

  it should "parse \\forall x,y \\forall s,t (x>y & y>s & s>t)" in {
    parser("\\forall x,y,z (x>y & y>z)") should be
    Forall(Seq(x, z), Forall(Seq(Variable("s"), Variable("t")),
      And(Greater(x, z), Greater(y, z))))
  }

  it should "report missing identifiers in block quantifiers" in {
    the [ParseException] thrownBy parser("\\forall x,y, (x>y)") should
      (have message """1:14 Unexpected token cannot be parsed
                      |Found:    ( at 1:14
                      |Expected: IDENT""".stripMargin
        or have message
        """1:12 Error parsing formula at 1:1
          |Found:    ", (x>y)" at 1:12
          |Expected: ([a-zA-Z0-9] | "_" | "'" | "," ~ variable | "true" | "false" | "\\forall" | "\\exists" | "∀" | "∃" | "[" | "<" | "!" | predicational | "⎵" | "__________" | comparison | ident | "(")
          |Hint: Try ([a-zA-Z0-9] | "_" | "'" | "true" | "false" | "\\forall" | "\\exists" | "∀" | "∃" | "[" | "<" | "!" | [a-zA-Z] | "⎵" | "__________" | "(" | [0-9] | "." | "•" | "-")""".stripMargin)
    the [ParseException] thrownBy parser("\\forall x,y, x>y") should
      (have message """1:15 Unexpected token cannot be parsed
                      |Found:    > at 1:15
                      |Expected: ,
                      |      or: <BeginningOfFormula>""".stripMargin
        or have message
        """1:12 Error parsing formula at 1:1
          |Found:    ", x>y" at 1:12
          |Expected: ([a-zA-Z0-9] | "_" | "'" | "," ~ variable | "true" | "false" | "\\forall" | "\\exists" | "∀" | "∃" | "[" | "<" | "!" | predicational | "⎵" | "__________" | comparison | ident | "(")
          |Hint: Try ([a-zA-Z0-9] | "_" | "'" | "true" | "false" | "\\forall" | "\\exists" | "∀" | "∃" | "[" | "<" | "!" | [a-zA-Z] | "⎵" | "__________" | "(" | [0-9] | "." | "•" | "-")""".stripMargin)
  }

  it should "parse \\exists x,y,z (x>y & y>z)" in {
    parser("\\exists x,y,z (x>y & y>z)") should be
    Exists(Seq(x, y, z),
      And(Greater(x, z), Greater(y, z)))
  }

  it should "parse \\forall v (v>=0&true&0>=0->v=v+0*0)<->true" in {
    val n0 = Number(0)
    parser("\\forall v (v>=0&true&0>=0->v=v+0*0)<->true") should be
    Equiv(Forall(Seq(v), Imply(And(And(GreaterEqual(v, n0), True), GreaterEqual(n0, n0)), Equal(v, Plus(v, Times(n0, n0))))), True)
  }

  it should "parse (\\forall v (v>=0&true&0>=0->v=v+0*0))<->true" in {
    val n0 = Number(0)
    parser("(\\forall v (v>=0&true&0>=0->v=v+0*0))<->true") should be
    Equiv(Forall(Seq(v), Imply(And(And(GreaterEqual(v, n0), True), GreaterEqual(n0, n0)), Equal(v, Plus(v, Times(n0, n0))))), True)
  }

  it should "program parse {x'=5&x>2&x>3} as an ODESystem with one evolution domain constraint" in {
    parser.programParser("{x'=5&x>2&x>3}") shouldBe ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3))))
  }

  it should "program parse x'=5&x>2&x>3 as an ODESystem with one evolution domain constraint (if parsed at all)" in {
    try {
      parser.programParser("x'=5&x>2&x>3") shouldBe ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3))))
    } catch {
      case _: ParseException => // acceptable
    }
  }

  it should "parse x'=5&x>2&x>3 as an equation system" in {
    parser.formulaParser("x'=5&x>2&x>3") shouldBe And(Equal(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3))))
    parser("x'=5&x>2&x>3") shouldBe And(Equal(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3))))
  }

  it should "parse [{x'=5&x>2&x>3}]x>0 as an ODESystem with one evolution domain constraint" in {
    parser("[{x'=5&x>2&x>3}]x>0") shouldBe Box(ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), And(Greater(x, Number(2)), Greater(x, Number(3)))), Greater(x, Number(0)))
  }

  it should "parse [{x'=v}]x=0 as a ODESystem with one ODE" in {
    parser("[{x'=v}]x=0") shouldBe Box(ODESystem(AtomicODE(DifferentialSymbol(x), v), True), Equal(x, Number(0)))
  }

  it should "parse [{x'=v&x<5}]x=0 as a ODESystem with one ODE and evolution domain" in {
    parser("[{x'=v&x<5}]x=0") shouldBe Box(ODESystem(AtomicODE(DifferentialSymbol(x), v), Less(x, Number(5))), Equal(x, Number(0)))
  }

  it should "parse [{x'=v,v'=a}]x=0 as a ODESystem with two ODEs" in {
    parser("[{x'=v,v'=a}]x=0") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), v), AtomicODE(DifferentialSymbol(v), Variable("a"))), True), Equal(x, Number(0)))
  }

  it should "parse [{x'=v,v'=a&x<5}]x=0 as a ODESystem with two ODEs" in {
    parser("[{x'=v,v'=a&x<5}]x=0") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), v), AtomicODE(DifferentialSymbol(v), Variable("a"))), Less(x,Number(5))), Equal(x, Number(0)))
  }


  it should "program parse {{x'=v}}* as a loopy ODESystem with one ODE" in {
    parser.programParser("{{x'=v}}*") shouldBe Loop(ODESystem(AtomicODE(DifferentialSymbol(x), v), True))
  }

  it should "differential program parse" in {
    parser.differentialProgramParser("{x'=1}") shouldBe AtomicODE(DifferentialSymbol(x), Number(1))
  }

  it should "parse [{{x'=v}}*]x=0 as a loopy ODESystem with one ODE" in {
    parser("[{{x'=v}}*]x=0") shouldBe Box(Loop(ODESystem(AtomicODE(DifferentialSymbol(x), v), True)), Equal(x, Number(0)))
  }

  it should "parse [{{x'=v&x<5}}*]x=0 as a loopy ODESystem with one ODE and evolution domain" in {
    parser("[{{x'=v&x<5}}*]x=0") shouldBe Box(Loop(ODESystem(AtomicODE(DifferentialSymbol(x), v), Less(x, Number(5)))), Equal(x, Number(0)))
  }

  it should "parse [{{x'=v,v'=a}}*]x=0 as a loopy ODESystem with two ODEs" in {
    parser("[{{x'=v,v'=a}}*]x=0") shouldBe Box(Loop(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), v), AtomicODE(DifferentialSymbol(v), Variable("a"))), True)), Equal(x, Number(0)))
  }

  it should "parse [{{x'=v,v'=a&x<5}}*]x=0 as a loopy ODESystem with two ODEs" in {
    parser("[{{x'=v,v'=a&x<5}}*]x=0") shouldBe Box(Loop(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), v), AtomicODE(DifferentialSymbol(v), Variable("a"))), Less(x,Number(5)))), Equal(x, Number(0)))
  }

  it should "parse [{x'=1,y'=2};x:=3;]x>=0 as a sequence with ODE first" in {
    parser("[{x'=1,y'=2};x:=3;]x>=0") shouldBe Box(Compose(
      ODESystem(DifferentialProduct(
        AtomicODE(DifferentialSymbol(x), Number(1)),
        AtomicODE(DifferentialSymbol(y), Number(2))
      ), True), Assign(x, Number(3))), GreaterEqual(x, Number(0)))
  }

  it should "refuse ; in ODE-{}" in {
    the [ParseException] thrownBy parser("[{x'=v;v'=2}]x=0") should
      (have message
        """1:7 Unexpected ; in system of ODEs
          |Found:    ; at 1:7
          |Expected: ,""".stripMargin
        or have message
        """1:7 Error parsing program at 1:2
          |Found:    ";v'=2}]x=0" at 1:7
          |Expected: ([a-zA-Z0-9] | "_" | "<<" | termList | space | "'" | "^" | "*" | "/" | "+" | "-" | "," | "&" | "}")
          |Hint: Try ([a-zA-Z0-9] | "_" | "<<" | "(" | "(|" | "'" | "^" | "*" | "/" | "+" | "-" | "," | "&" | "}")""".stripMargin)
  }

  it should "refuse ++ in ODE-{}" in {
    the [ParseException] thrownBy parser("[{x'=v++v'=2}]x=0") should
      (have message
        """1:7 Unexpected ++ in system of ODEs
          |Found:    ++ at 1:7 to 1:8
          |Expected: ,""".stripMargin
        or have message
        """1:8 Error parsing term at 1:6
          |Found:    "+v'=2}]x=0" at 1:8
          |Expected: ("(" | number | dot | function | unitFunctional | variable | termList | "__________" | "-")
          |Hint: Try ("(" | [0-9] | "." | "•" | [a-zA-Z] | "__________" | "-")""".stripMargin)
  }

  it should "refuse ODE 1 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v;]x=0") should
      (have message
        """1:7 ODE without {}
          |Found:    ] at 1:7
          |Expected: }""".stripMargin
        or have message
        """1:2 Error parsing program at 1:2
          |Found:    "x'=v;]x=0" at 1:2
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)
  }

  it should "refuse ODE 2 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v & x>0;]x=0") should
      (have message
        """1:13 ODE without {}
          |Found:    ] at 1:13
          |Expected: }""".stripMargin
        or have message
        """1:2 Error parsing program at 1:2
          |Found:    "x'=v & x>0" at 1:2
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)
  }

  it should "refuse ODE systems 1 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v,v'=3;]x=0") should
      (have message
        """1:11 ODE without {}
          |Found:    ; at 1:11
          |Expected: }""".stripMargin
        or have message
        """1:2 Error parsing program at 1:2
          |Found:    "x'=v,v'=3;" at 1:2
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)
  }

  it should "refuse ODE systems 2 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v,v'=3 & x>0;]x=0") should
      (have message
        """1:17 ODE without {}
          |Found:    ; at 1:17
          |Expected: }""".stripMargin
        or have message
        """1:2 Error parsing program at 1:2
          |Found:    "x'=v,v'=3 " at 1:2
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)
  }

  it should "refuse ODE systems 3 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v,v'=3 ++ {y'=3}]x=0") should
      (have message
        """1:12 ODE without {}
          |Found:    ++ at 1:12 to 1:13
          |Expected: }""".stripMargin
        or have message
        """1:2 Error parsing program at 1:2
          |Found:    "x'=v,v'=3 " at 1:2
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)
  }

  it should "refuse ODE systems 4 without {} in modalities" in {
    the [ParseException] thrownBy parser("[x'=v,v'=3 & x>5 ++ {y'=3}]x=0") should
      (have message
        """1:18 ODE without {}
          |Found:    ++ at 1:18 to 1:19
          |Expected: }""".stripMargin
        or have message
        """1:2 Error parsing program at 1:2
          |Found:    "x'=v,v'=3 " at 1:2
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)
  }

  it should "refuse ODE systems 5 without {} in modalities" in {
    the [ParseException] thrownBy parser("[c,d,x'=f(x)&q(x);]x=0") should
      (have message
        """1:19 ODE without {}
          |Found:    ] at 1:19
          |Expected: }""".stripMargin
        or have message
        """1:2 Error parsing program at 1:2
          |Found:    "c,d,x'=f(x" at 1:2
          |Expected: (systemSymbol | programSymbol | variable ~ ":=" | "?" | "if" | "{" | "__________")
          |Hint: Try ("?" | "if" | "{" | "__________")""".stripMargin)
  }

  it should "refuse primed variables in evolution domain constraint" in {
    the [ParseException] thrownBy parser("[{x'=v,v'=3 & v'>0}]x=0") should
      (have message
        """1:13 No differentials can be used in evolution domain constraints
          |Found:    v'>0 at 1:13 to 1:19
          |Expected: In an evolution domain constraint, instead of the primed variables use their right-hand sides.""".stripMargin
        or have message
        """1:19 Error parsing program at 1:2
          |Found:    "}]x=0" at 1:19
          |Expected: No differentials in evolution domain constraints; instead of the primed variables use their right-hand sides.
          |Hint: Try ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | "&" | "∧" | "|" | "∨" | "->" | "→" | [ \t\r\n] | " <- " | "←" | "<->" | "↔" | No differentials in evolution domain constraints; instead of the primed variables use their right-hand sides.)""".stripMargin)
    the [ParseException] thrownBy parser("[{x'=v,v'=3 & (x+v)'>0}]x=0") should
      (have message
        """1:13 No differentials can be used in evolution domain constraints
          |Found:    (x+v)'>0 at 1:13 to 1:23
          |Expected: In an evolution domain constraint, instead of the primed variables use their right-hand sides.""".stripMargin
        or have message
        """1:23 Error parsing program at 1:2
          |Found:    "}]x=0" at 1:23
          |Expected: No differentials in evolution domain constraints; instead of the primed variables use their right-hand sides.
          |Hint: Try ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | "&" | "∧" | "|" | "∨" | "->" | "→" | [ \t\r\n] | " <- " | "←" | "<->" | "↔" | No differentials in evolution domain constraints; instead of the primed variables use their right-hand sides.)""".stripMargin)
  }

  it should "parse standalone differential symbols" in {
    parser("x'") shouldBe DifferentialSymbol(x)
  }

  it should "parse standalone differentials" in {
    parser("(x')'") shouldBe Differential(DifferentialSymbol(x))
  }

  it should "parse terms with differential symbols" in {
    parser("x'=0") shouldBe Equal(DifferentialSymbol(x), Number(0))
  }

  it should "parse terms with differentials" in {
    parser("(x')'=0") shouldBe Equal(Differential(DifferentialSymbol(x)), Number(0))
  }

  it should "parse postconditions with differential symbols" in {
    parser("<{x'=3}>x'>0") shouldBe Diamond(ODESystem(AtomicODE(DifferentialSymbol(x), Number(3)), True),
      Greater(DifferentialSymbol(x), Number(0)))
  }

  it should "parse +- in x+-y+1>=5" in {
    parser("x+-y+1>=5") shouldBe GreaterEqual(Plus(Plus(x,Neg(y)),Number(1)), Number(5))
  }

  it should "parse -- in x--y+1>=5" in {
    parser("x--y+1>=5") shouldBe GreaterEqual(Plus(Minus(x,Neg(y)),Number(1)), Number(5))
  }

  it should "term parse f() as f(Nothing)" in {
    parser.termParser("f()") shouldBe FuncOf(Function("f",None,Unit,Real), Nothing)
  }

  it should "term parse f(||) as f(Anything)" in {
    parser.termParser("f(||)") shouldBe UnitFunctional("f", AnyArg, Real)
  }

  it should "formula parse p() as p(Nothing)" in {
    parser.formulaParser("p()") shouldBe PredOf(Function("p",None,Unit,Bool), Nothing)
  }

  it should "formula parse p(||) as p(Anything)" in {
    parser.formulaParser("p(||)") shouldBe UnitPredicational("p", AnyArg)
  }

  it should "round trip term parse f() as f(Nothing)" in {
    parser.termParser(parser.termParser("f()").prettyString) shouldBe FuncOf(Function("f",None,Unit,Real), Nothing)
  }

  it should "round trip term parse f(||) as f(Anything)" in {
    parser.termParser(parser.termParser("f(||)").prettyString) shouldBe UnitFunctional("f", AnyArg, Real)
  }

  it should "round trip formula parse p() as p(Nothing)" in {
    parser.formulaParser(parser.formulaParser("p()").prettyString) shouldBe PredOf(Function("p",None,Unit,Bool), Nothing)
  }

  it should "round trip formula parse p(||) as p(Anything)" in {
    parser.formulaParser(parser.formulaParser("p(||)").prettyString) shouldBe UnitPredicational("p", AnyArg)
  }

  it should "FEATURE_REQUEST: round trip parse dot terms" taggedAs TodoTest in {
    parser.termParser(parser.termParser("•").prettyString) shouldBe DotTerm()
    parser.termParser(parser.termParser(".").prettyString) shouldBe DotTerm()
    parser.termParser(parser.termParser("•()").prettyString) shouldBe DotTerm()
    parser.termParser(parser.termParser(".()").prettyString) shouldBe DotTerm()
    parser.termParser(parser.termParser("•(•,•)").prettyString) shouldBe DotTerm(Tuple(Real, Real))
    parser.termParser(parser.termParser(".(.,.)").prettyString) shouldBe DotTerm(Tuple(Real, Real))
    parser.termParser(parser.termParser("•(•,•,•)").prettyString) shouldBe DotTerm(Tuple(Real, Tuple(Real, Real)))
    parser.termParser(parser.termParser(".(.,.,.)").prettyString) shouldBe DotTerm(Tuple(Real, Tuple(Real, Real)))
  }

  it should "FEATURE_REQUEST: round trip parse colored dots" taggedAs TodoTest in {
    parser.termParser(parser.termParser("•_1").prettyString) shouldBe DotTerm(Real, Some(1))
    parser.termParser(parser.termParser("._1").prettyString) shouldBe DotTerm(Real, Some(1))
    parser.termParser(parser.termParser("•_1()").prettyString) shouldBe DotTerm(Real, Some(1))
    parser.termParser(parser.termParser("._1()").prettyString) shouldBe DotTerm(Real, Some(1))
    parser.termParser(parser.termParser("•_1(•,•)").prettyString) shouldBe DotTerm(Tuple(Real, Real), Some(1))
    parser.termParser(parser.termParser("._1(.,.)").prettyString) shouldBe DotTerm(Tuple(Real, Real), Some(1))
    parser.termParser(parser.termParser("•_1(•,•,•)").prettyString) shouldBe DotTerm(Tuple(Real, Tuple(Real, Real)), Some(1))
    parser.termParser(parser.termParser("._1(.,.,.)").prettyString) shouldBe DotTerm(Tuple(Real, Tuple(Real, Real)), Some(1))
  }

  it should "parse a term from an ODE solution (1)" in {
    val t3 = Variable("t", Some(3))
    val B = Variable("B", None)
    val v0 = Variable("v", Some(0))
    parser("-(1)*(v_0+-B*t_3--B/2*t_3)+-t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))") should be
    Plus(
      Times(Neg(Number(1)), Plus(v0, Minus(Times(Neg(B), t3), Times(Divide(Neg(B), Number(2)), t3)))),
      Neg(Times(t3, Minus(Neg(B), Plus(Times(Divide(Minus(Times(Number(0), Number(2)), Times(Neg(B), Number(0))), Power(Number(2), Number(2))), t3), Times(Divide(B, Number(2)), Number(1)))))))
  }

  it should "parse a term from an ODE solution (2)" in {
    val t3 = Variable("t", Some(3))
    val B = Variable("B", None)
    parser("t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))") should be
    Times(t3, Minus(Neg(B), Plus(Times(Divide(Minus(Times(Number(0), Number(2)), Times(Neg(B), Number(0))), Power(Number(2), Number(2))), t3), Times(Divide(Neg(B), Number(2)), Number(1)))))
  }

  it should "parse a robot example" in {
    val t3 = Variable("t", Some(3))
    val B = Variable("B", None)
    val v0 = Variable("v", Some(0))
    val dx0 = Variable("dx", Some(0))
    parser("\\forall V \\forall dx_0 \\forall B \\forall dy_0 \\forall dx \\forall v \\forall yo_0 \\forall x_0 \\forall y_0 \\forall v_0 \\forall r \\forall xo_0 \\forall dy \\forall A \\forall t_3 (v_0+-B*t_3)*dx_0-0 <= 1*(v_0+-B*t_3--B/2*t_3) + t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))") should be
    Forall(Seq(Variable("V")),
      Forall(Seq(Variable("dx", Some(0))),
        Forall(Seq(Variable("B")),
          Forall(Seq(Variable("dy", Some(0))),
            Forall(Seq(Variable("dx")),
              Forall(Seq(Variable("v")),
                Forall(Seq(Variable("yo", Some(0))),
                  Forall(Seq(Variable("x", Some(0))),
                    Forall(Seq(Variable("y", Some(0))),
                      Forall(Seq(Variable("v", Some(0))),
                        Forall(Seq(Variable("r")),
                          Forall(Seq(Variable("xo", Some(0))),
                            Forall(Seq(Variable("dy")),
                              Forall(Seq(Variable("A")),
                                Forall(Seq(Variable("t", Some(3))),
                                  LessEqual(
                                    Minus(Times(Plus(v0, Times(Neg(B), t3)), dx0), Number(0)),
                                    Plus(
                                      Times(Number(1), Plus(v0, Minus(Times(Neg(B), t3), Times(Divide(Neg(B), Number(2)), t3)))),
                                      Times(t3, Minus(Neg(B), Plus(Times(Divide(Minus(Times(Number(0), Number(2)), Times(Neg(B), Number(0))), Power(Number(2), Number(2))), t3), Times(Divide(Neg(B), Number(2)), Number(1))))))
                                  )
                                )))))))))))))))
  }

  it should "parse a long chain of quantifiers" in {
    val parsed = parser("\\forall V \\forall dx_0 \\forall B \\forall dy_0 \\forall dx \\forall v \\forall yo_0 \\forall x_0 \\forall y_0 \\forall v_0 \\forall r \\forall xo_0 \\forall dy \\forall A \\forall t_3 (ep()>0&V>=0&B>0&A>=0&r!=0&v>=0&(v_0=0|(x_0-xo_0>=0->x_0-xo_0>v_0^2/(2*B)+V*(v_0/B))&(x_0-xo_0<=0->xo_0-x_0>v_0^2/(2*B)+V*(v_0/B))|(y_0-yo_0>=0->y_0-yo_0>v_0^2/(2*B)+V*(v_0/B))&(y_0-yo_0<=0->yo_0-y_0>v_0^2/(2*B)+V*(v_0/B)))&r_0()!=0&v_0>=0&dx^2+dy^2=1&dxo()^2+dyo()^2<=V^2&x0_1()=x_0&dx^2+dy^2=1&v_0>=0&dx_0^2+dy_0^2=1&t_3>=0&t_3<=ep()&0>=0&0<=ep()&v_0=v_0+-B*0&v_0+-B*t_3>=0->-(1)*(v_0+-B*t_3--B/2*t_3)+-t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))<=(v_0+-B*t_3)*dx_0-0&(v_0+-B*t_3)*dx_0-0<=1*(v_0+-B*t_3--B/2*t_3)+t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1)))<->true")
    println("Parsed: " + parsed.prettyString)
    parsed.prettyString shouldBe "\\forall V \\forall dx_0 \\forall B \\forall dy_0 \\forall dx \\forall v \\forall yo_0 \\forall x_0 \\forall y_0 \\forall v_0 \\forall r \\forall xo_0 \\forall dy \\forall A \\forall t_3 (ep()>0&V>=0&B>0&A>=0&r!=0&v>=0&(v_0=0|(x_0-xo_0>=0->x_0-xo_0>v_0^2/(2*B)+V*(v_0/B))&(x_0-xo_0<=0->xo_0-x_0>v_0^2/(2*B)+V*(v_0/B))|(y_0-yo_0>=0->y_0-yo_0>v_0^2/(2*B)+V*(v_0/B))&(y_0-yo_0<=0->yo_0-y_0>v_0^2/(2*B)+V*(v_0/B)))&r_0()!=0&v_0>=0&dx^2+dy^2=1&dxo()^2+dyo()^2<=V^2&x0_1()=x_0&dx^2+dy^2=1&v_0>=0&dx_0^2+dy_0^2=1&t_3>=0&t_3<=ep()&0>=0&0<=ep()&v_0=v_0+-B*0&v_0+-B*t_3>=0->-1*(v_0+-B*t_3--B/2*t_3)+-t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1))<=(v_0+-B*t_3)*dx_0-0&(v_0+-B*t_3)*dx_0-0<=1*(v_0+-B*t_3--B/2*t_3)+t_3*(-B-((0*2--B*0)/2^2*t_3+-B/2*1)))<->true"
  }


  "Parsing state-dependents" should "parse (||) AnyArg" in {
    parser("x>2&p(||)") shouldBe And(Greater(x,Number(2)), UnitPredicational("p",AnyArg))
    parser.formulaParser("p(||)") shouldBe UnitPredicational("p",AnyArg)
    parser("5<=f(||)") shouldBe LessEqual(Number(5),UnitFunctional("f",AnyArg,Real))
    parser.termParser("f(||)") shouldBe UnitFunctional("f",AnyArg,Real)
  }

  it should "parse (|x|) Exception taboos" in {
    parser("x>2&p(|x|)") shouldBe And(Greater(x,Number(2)), UnitPredicational("p",Except(x::Nil)))
    parser("x>2&p(|x,y,z|)") shouldBe And(Greater(x,Number(2)), UnitPredicational("p",Except(x::y::z::Nil)))
    parser.formulaParser("p(|x|)") shouldBe UnitPredicational("p",Except(x::Nil))
    parser("5<=f(|x|)") shouldBe LessEqual(Number(5),UnitFunctional("f",Except(x::Nil),Real))
    parser.termParser("f(|x|)") shouldBe UnitFunctional("f",Except(x::Nil),Real)
    parser.termParser("f(|x,y|)") shouldBe UnitFunctional("f",Except(x::y::Nil),Real)
    //@TODO elaborate in lax parsing mode
//    parser("[a{||};]P") shouldBe Box(ProgramConst("a"), UnitPredicational("P", AnyArg))
//    parser("[a{|x|};]P") shouldBe Box(ProgramConst("a", Except(x::Nil)), UnitPredicational("P", AnyArg))
//    parser("[a{|x,y|};]P") shouldBe Box(ProgramConst("a", Except(x::y::Nil)), UnitPredicational("P", AnyArg))
//    parser("[a{|^@|};]P") shouldBe Box(SystemConst("a"), UnitPredicational("P", AnyArg))
//    parser("[a{|^@x|};]P") shouldBe Box(SystemConst("a", Except(x::Nil)), UnitPredicational("P", AnyArg))
//    parser("[a{|^@x,y|};]P") shouldBe Box(SystemConst("a", Except(x::y::Nil)), UnitPredicational("P", AnyArg))
//    parser("[{a{|^@|};}*]P") shouldBe Box(Loop(SystemConst("a")), UnitPredicational("P", AnyArg))
    parser("[{x'=5,c{|x|}}]x>2") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x),Number(5)),
      DifferentialProgramConst("c",Except(x::Nil))), True),
      Greater(x,Number(2)))
    parser("[{z'=5,d{|y|}}]x>2") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(z),Number(5)),
      DifferentialProgramConst("d",Except(y::Nil))), True),
      Greater(x,Number(2)))
    parser("<{x'=5,c{|x|}}>x>2") shouldBe Diamond(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x),Number(5)),
      DifferentialProgramConst("c",Except(x::Nil))), True),
      Greater(x,Number(2)))
    parser("<{z'=5,d{|y|}}>x>2") shouldBe Diamond(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(z),Number(5)),
      DifferentialProgramConst("d",Except(y::Nil))), True),
      Greater(x,Number(2)))
  }

  it should "elaborate uppercase names to unit predicationals and lower case names to nullary predicates in lax mode" in {
    parser("P") shouldBe Variable("P")
    parser("p") shouldBe Variable("p")
    parser("[a;]P(||)") shouldBe Box(ProgramConst("a"), UnitPredicational("P", AnyArg))
    KeYmaeraXParser.laxParser("[a;]P") shouldBe parser("[a;]P(||)")
    the [ParseException] thrownBy KeYmaeraXParser.strictParser("[a;]P") should
      have message """1:6 Expected a Formula but got the Term P
                     |Found:    ] at 1:6 to EOF$
                     |Expected: Formula""".stripMargin
    parser("[a;]p(||)") shouldBe Box(ProgramConst("a"), UnitPredicational("p", AnyArg))
    parser("[a;]p()") shouldBe Box(ProgramConst("a"), PredOf(Function("p", None, Unit, Bool), Nothing))
    KeYmaeraXParser.laxParser("[a;]p") shouldBe parser("[a;]p()")
    the [ParseException] thrownBy KeYmaeraXParser.strictParser("[a;]p") should
      have message """1:6 Expected a Formula but got the Term p
                     |Found:    ] at 1:6 to EOF$
                     |Expected: Formula""".stripMargin
    parser("[a;]P()") shouldBe Box(ProgramConst("a"), PredOf(Function("P", None, Unit, Bool), Nothing))
  }

  it should "parse DG snippets" in {
    parser("[{x'=2,c{|y_|}}]x=99") shouldBe Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x),Number(2)), DifferentialProgramConst("c",Except(Variable("y_")::Nil))), True), Equal(x,Number(99)))
    parser("[{c{|y_|}}]x=99") shouldBe Box(ODESystem(DifferentialProgramConst("c",Except(Variable("y_")::Nil)), True), Equal(x,Number(99)))
    parser("[{c{|y_|}}]p(|y_|)") shouldBe Box(ODESystem(DifferentialProgramConst("c",Except(Variable("y_")::Nil)), True), UnitPredicational("p",Except(Variable("y_")::Nil)))
    parser("[{c{|y_|}&H(|y_|)}]p(|y_|)") shouldBe Box(ODESystem(DifferentialProgramConst("c",Except(Variable("y_")::Nil)), UnitPredicational("H",Except(Variable("y_")::Nil))), UnitPredicational("p",Except(Variable("y_")::Nil)))
  }
}
