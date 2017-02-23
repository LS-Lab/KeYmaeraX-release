package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{FlatSpec, Matchers}

/**
  * Tests the declarations parser.
  * Created by nfulton on 9/1/15.
  */
class DeclsTests extends FlatSpec with Matchers {
  "Declarations parser" should "parse declarations block correctly." in {
    val input =
      """ProgramVariables.
        |R x.
        |R z.
        |R z_0.
        |End.
      """.stripMargin
    val decls = KeYmaeraXDeclarationsParser(KeYmaeraXLexer.inMode(input, ProblemFileMode))._1
    decls.keySet.contains("x", None) shouldBe true
    decls.keySet.contains("z", None) shouldBe true
    decls.keySet.contains("z", Some(0)) shouldBe true
    decls.keys.toList.length shouldBe 3
  }

  it should "parse declarations of z, z_0 as two separate declarations" in {
    val input =
      """ProgramVariables.
        |R x.
        |R z.
        |R z_0.
        |R a.
        |End.
        |Problem.
        |x + z + z_0 = z_0 + z + x
        |End.
      """.stripMargin
    KeYmaeraXProblemParser(input)
  }

  "Problem/Solution Block" should "parse correctly" in {
    val input =
      """
        |Functions.
        |  B A().
        |End.
        |Problem.
        |  !(A() | !A()) -> !!(A() | !A())
        |End.
        |Solution.
        |  implyR(1)
        |End.
      """.stripMargin

    val (problem, solution) = KeYmaeraXProblemParser.parseProblemAndTactic(input)

    println(problem)
    println(solution)
  }

  "function domain" should "parse correctly" in {
    val input =
      """
        |Functions.
        |  B Cimpl(R, R, R).
        |End.
        |Problem.
        |  Cimpl(0,1,2) <-> true
        |End.
      """.stripMargin

    KeYmaeraXProblemParser(input) shouldBe Equiv(
      PredOf(Function("Cimpl", None, Tuple(Real, Tuple(Real, Real)), Bool), Pair(Number(0), Pair(Number(1), Number(2)))),
      True)
  }

  it should "fail to parse when the function application has the wrong assoc" in {
    val input =
      """
        |Functions.
        |  B Cimpl(R, R, R).
        |End.
        |Problem.
        |  Cimpl((0,1),2) <-> true
        |End.
      """.stripMargin

    a [ParseException] shouldBe thrownBy(KeYmaeraXProblemParser(input))
  }

  it should "fail to parse when the function def'n has the wrong assoc" in {
    val input =
      """
        |Functions.
        |  B Cimpl((R, R), R).
        |End.
        |Problem.
        |  Cimpl(0,1,2) <-> true
        |End.
      """.stripMargin

    a [ParseException] shouldBe thrownBy(KeYmaeraXProblemParser(input))
  }

  it should "parse correctly when fully explicit" ignore {
    val input =
      """
        |Functions.
        |  B Cimpl((R, R), R).
        |End.
        |Problem.
        |  Cimpl((0,1),2) <-> true
        |End.
      """.stripMargin

    val input2 =
      """
        |Functions.
        |  B Cimpl(R, (R, R)).
        |End.
        |Problem.
        |  Cimpl(0,(1,2)) <-> true
        |End.
      """.stripMargin

    KeYmaeraXProblemParser(input)
    KeYmaeraXProblemParser(input2)
  }

  "Declarations type analysis" should "elaborate variables to no-arg functions per declaration" in {
    val model = """Functions.
                  |  R b().
                  |  R m().
                  |End.
                  |
                  |ProgramVariables.
                  |  R x.
                  |  R v.
                  |  R a.
                  |End.
                  |
                  |Problem.
                  |  x<=m & b>0 -> [a:=-b; {x'=v,v'=a & v>=0}]x<=m
                  |End.
                  |""".stripMargin
    val m = FuncOf(Function("m", None, Unit, Real), Nothing)
    val b = FuncOf(Function("b", None, Unit, Real), Nothing)
    val x = Variable("x")
    val a = Variable("a")
    val v = Variable("v")
    KeYmaeraXProblemParser(model) shouldBe Imply(
      And(LessEqual(x, m), Greater(b, Number(0))),
      Box(Compose(Assign(a, Neg(b)), ODESystem("{x'=v,v'=a}".asDifferentialProgram, GreaterEqual(v, Number(0)))), LessEqual(x, m)))
  }

  it should "not allow variables refer to functions with parameters" in {
    val model = """Functions.
                  |  R b(R).
                  |  R m(R,R).
                  |End.
                  |
                  |ProgramVariables.
                  |  R x.
                  |  R v.
                  |  R a.
                  |End.
                  |
                  |Problem.
                  |  x<=m & b>0 -> [a:=-b; {x'=v,v'=a & v>=0}]x<=m
                  |End.
                  |""".stripMargin
    a[ParseException] should be thrownBy KeYmaeraXProblemParser(model)
  }

  it should "succeed when ()'s are used." in {
    val model = """Functions.
                  |  R b().
                  |  R m().
                  |End.
                  |
                  |ProgramVariables.
                  |  R x.
                  |  R v.
                  |  R a.
                  |End.
                  |
                  |Problem.
                  |  x<=m() & b()>0 -> [a:=-b(); {x'=v,v'=a & v>=0}]x<=m()
                  |End.
                  |""".stripMargin
    KeYmaeraXProblemParser(model)
  }

  it should "detect and print undeclared symbols" in {
    val model = """Problem. x>0 End."""
    //@todo better location information
    the [ParseException] thrownBy  KeYmaeraXProblemParser(model) should have message
      """<somewhere> type analysis: undefined symbol x with index None
        |Found:    <unknown> at <somewhere>
        |Expected: <unknown>""".stripMargin
  }
}
