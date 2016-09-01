package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.core._

import org.scalatest.{Matchers, FlatSpec}

/**
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

    val problem = KeYmaeraXProblemParser(input)
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

  "Declarations type analysis" should "not allow use of functions as variables" in {
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
    a[ParseException] shouldBe thrownBy(KeYmaeraXProblemParser(model))
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
}
