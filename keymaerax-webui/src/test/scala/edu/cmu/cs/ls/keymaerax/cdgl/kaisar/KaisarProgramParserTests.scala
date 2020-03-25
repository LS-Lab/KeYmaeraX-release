/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
/**
 * Test Kaisar parsing
 * @TODO: The tests don't test much automatically yet, mostly useful to step through in debugger
 * @author Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.TermTactics._
import edu.cmu.cs.ls.keymaerax.parser.RandomParserTests
import edu.cmu.cs.ls.keymaerax.tags._
import fastparse.Parsed.{Failure, Success}
import fastparse._

object AutogeneratedFormulaTests {
  def doParse[T](s: String): Formula = parse(s, ExpressionParser.formula(_)).asInstanceOf[Success[Formula]].value
}
@SlowTest
class AutogeneratedFormulaTests extends RandomParserTests(AutogeneratedFormulaTests.doParse, new RandomFormula(0))

@UsualTest
class KaisarProgramParserTests extends TacticTestBase {
  val ep = ExpressionParser

  def p[T](s: String, parser: P[_] => P[T]): T = parse(s, parser).asInstanceOf[Success[T]].value
  val (vx, vy) = (Variable("x"), Variable("y"))
  val (dx, dy) = (DifferentialSymbol(vx), DifferentialSymbol(vy))

  val at: Function = Function("at", domain = Tuple(Real, Unit), sort = Real, interpreted = true)
  val max: Function = Function("max", domain = Tuple(Real, Real), sort = Real, interpreted = true)
  val min: Function = Function("min", domain = Tuple(Real, Real), sort = Real, interpreted = true)
  val abs: Function = Function("abs", domain = Real, sort = Real, interpreted = true)
  val wild: FuncOf = FuncOf(Function("wild", domain = Unit, sort = Unit, interpreted = true), Nothing)
  val init: FuncOf = FuncOf(Function("init", domain = Unit, sort = Unit, interpreted = true), Nothing)

  // terms
  "term parser" should "parse variable" in {
    p("x", ep.term(_)) shouldBe vx
  }

  it should "parse diff variable" in {
    p("x'", ep.term(_)) shouldBe dx
  }

  it should "parse diffterm" in {
    p("(x + y)'", ep.term(_)) shouldBe Differential(Plus(vx, vy))
  }

  it should "parse number" in {
    val num: Number = p("123.0", ep.term(_)).asInstanceOf[Number]
    num.value shouldBe 123.0
  }

  it should "parse plus" in {
    p("x + y", ep.term(_)) shouldBe Plus(vx, vy)
  }

  it should "parse times" in {
    p("x * y", ep.term(_)) shouldBe Times(vx, vy)
  }

  it should "parse minus" in {
    p("x - y", ep.term(_)) shouldBe Minus(vx, vy)
  }

  it should "parse neg" in {
    p("- y", ep.term(_)) shouldBe Neg(vy)
  }

  it should "parse divide" in {
    p("x / y", ep.term(_)) shouldBe Divide(vx, vy)
  }

  it should "parse special functions" in {
    p("abs(x)", ep.term(_)) shouldBe FuncOf(abs, vx)
    p("max(x, y + x)", ep.term(_)) shouldBe FuncOf(max, Pair(vx, Plus(vy, vx)))
    p("min(x, y + x)", ep.term(_)) shouldBe FuncOf(min, Pair(vx, Plus(vy, vx)))
  }

  it should "parse wildcard" in {
    p("*", ep.term(_)) shouldBe wild
  }

  it should "parse at" in {
    p("x@init", ep.term(_)) shouldBe FuncOf(at, Pair(vx, init))
  }

  it should "parse parens" in {
    p("(x)", ep.term(_)) shouldBe vx
  }

  it should "parse power" in {
    p("x^y", ep.term(_)) shouldBe Power(vx, vy)
  }

  it should "parse compound term" in {
    p("(x + -y ^y) * x/x", ep.term(_)) shouldBe Divide(Times(Plus(vx, Neg(Power(vy,vy))), vx), vx)
  }

  it should "respect order of operations" in {
    p("(x - y)*x/y-x+y+-x^x", ep.term(_)) shouldBe Plus(Plus(Minus(Divide(Times(Minus(vx, vy), vx), vy), vx), vy), Neg(Power(vx, vx)))
  }
  // programs
  "program parser" should "parse assignment" in {
    val asgn = parse("x := x + x;", ep.assign(_))
    val prog = parse("x := x + x;", ep.program(_))
    val x = asgn
    p("x := x + x;", ep.program(_)) shouldBe Assign(vx, Plus(vx, vx))
  }

  it should "parse differential assignment" in {
    p("x' := x + x;", ep.program(_)) shouldBe Assign(dx, Plus(vx, vx))
  }

  it should "parse random assignment" in {
    p("x' := *;", ep.program(_)) shouldBe AssignAny(dx)
  }

  it should "parse singleton ode" in {
    p("x' = 5;", ep.program(_)) shouldBe ODESystem(AtomicODE(dx, Number(5)))
  }

  it should "parse ode product" in {
    p("x' = 5, y' = 2;", ep.program(_)) shouldBe ODESystem(DifferentialProduct(AtomicODE(dx, Number(5)), AtomicODE(dy, Number(2))))
  }

  it should "parse ode with constraint" in {
    p("x' = 5, y' = 2 & x = y;", ep.program(_)) shouldBe ODESystem(DifferentialProduct(AtomicODE(dx, Number(5)), AtomicODE(dy, Number(2))), Equal(vx, vy))
  }

  it should "parse ode with constraint with conjunction" in {
    p("x' = 5, y' = 2 & x = y & y = x;", ep.program(_)) shouldBe ODESystem(DifferentialProduct(AtomicODE(dx, Number(5)), AtomicODE(dy, Number(2))),
      And(Equal(vx, vy), Equal(vy, vx)))
  }

  it should "parse dual" in {
    p("x' =5;^d", ep.program(_)) shouldBe Dual(ODESystem(AtomicODE(dx, Number(5))))
  }

  it should "parse loop" in {
    p("x := 5;*", ep.program(_)) shouldBe Loop(Assign(vx, Number(5)))
  }

  it should "parse compose" in {
    p("x := 5; x:= 2;", ep.program(_)) shouldBe Compose(Assign(vx, Number(5)), Assign(vx, Number(2)))
  }

  it should "parse braces" in {
    p("{x:=1; y:=2;} ++ {y:=5; x:= *;} y:=5; y:=4;", ep.program(_)) shouldBe
      Choice(Compose(Assign(vx, Number(1)), Assign(vy, Number(2)))
        , Compose(Compose(Assign(vy, Number(5)), AssignAny(vx)), Compose(Assign(vy, Number(5)), Assign(vy, Number(4)))))
  }

  it should "parse choice" in {
    p("x:=*; ++ ?x=x;", ep.program(_)) shouldBe Choice(AssignAny(vx), Test(Equal(vx, vx)))
  }

  it should "associate choice" in {
    p("x:=1; ++ x:=2; ++ x:=3;", ep.program(_)) shouldBe Choice(Assign(vx, Number(1)), Choice(Assign(vx, Number(2)), Assign(vx, Number(3))))
  }

  // formulas
  "formula parser" should "parse equal" in {
    p("x=y", ep.formula(_)) shouldBe Equal(vx, vy)
  }

  it should "respect | and & precedence" in {
    p("x=0&y=0 | x=1&y=1", ep.formula(_)) shouldBe Or(And(Equal(vx, Number(0)), Equal(vy, Number(0))), And(Equal(vx, Number(1)),Equal(vy, Number(1))))
  }

  it should "respect [] precedence" in {
    p("x=0 & [x:=1;]x=1 & x=2", ep.formula(_)) shouldBe And(Equal(vx, Number(0)), And(Box(Assign(vx, Number(1)), Equal(vx, Number(1))), Equal(vx, Number(2))))
  }

  it should "respect forall precedence" in {
    p("x=0 & \\forall x x=x & x = 1", ep.formula(_)) shouldBe(And(Equal(vx, Number(0)), And(Forall(List(vx), Equal(vx, vx)), Equal(vx, Number(1)))))
  }

  it should "make imply tighter than equiv" in {
    p("x=0 -> x=1 <-> x=2 -> x=5", ep.formula(_)) shouldBe Equiv(Imply(Equal(vx,Number(0)), Equal(vx, Number(1))), Imply(Equal(vx, Number(2)), Equal(vx, Number(5))))
  }

  it should "parse paren terms" in {
    p("(2) <= (1)", ep.formula(_)) shouldBe LessEqual(Number(2), Number(1))
  }

  it should "parse diffvar 1" in {
    p("20-(1^2/z1-((1)'-z2'))<=1&true", ep.formula(_)) shouldBe
      And(LessEqual(Minus(Number(20), Minus(Divide(Power(Number(1), Number(2)), Variable("z1")), Minus(Differential(Number(1)), DifferentialSymbol(Variable("z2"))))), Number(1)), True)
  }

  it should "parse diffvar 2" in {
    p("\\forall z1 ([z1:=z1;](\\forall z2 (z1')<=(z2')))", ep.formula(_)) shouldBe
      Forall(List(Variable("z1")), Box(Assign(Variable("z1"), Variable("z1")), Forall(List(Variable("z2")), LessEqual(DifferentialSymbol(Variable("z1")), DifferentialSymbol(Variable("z2"))))))
  }

  it should "parse negative literals" in {
    p("-87!=z3*(z1*z1)", ep.formula(_)) shouldBe NotEqual(Number(-87), Times(Variable("z3"), Times(Variable("z1"), Variable("z1"))))
  }

  it should "parse >=" in {
    p("z1>=(-55)'", ep.infixTerminal(_)) shouldBe GreaterEqual(Variable("z1"), Differential(Number(-55)))
  }

  it should "precede * and /" in {
    p("1/2*3", ep.term(_)) shouldBe Times(Divide(Number(1), Number(2)), Number(3))
  }

  it should "parse random example" in {
    val x1 = p("(true)&((z3) <= ((((-23))*((1)))-((-41))))", ep.formula(_))
    val x2 = p("1>=27/(1-1)*(1*1*z2)&z3'>=z2'+z1'|z2<=z3'", ep.formula(_))
    val x3 = p("true&z3<=-23*1--41", ep.formula(_))
    val x4 = p("[{{?([{?(true);}*](<?(true);>(true)));}++{{z3':=((1))*((1));}++{?(true);}}}++{?((true)->((((1)) >= ((1)))&(<?(true);>(true))));}](<?(((z2)^((2))) = (z2));>(!([{{?(true);}*};{{?(true);}++{?(true);}}]([{?(true);}*](<?(true);>(true))))))", ep.formula(_))
    val 2 = 1 + 1
  }

  it should "parse existses" in {
    val x = p("\\forall z2 (\\forall z3 1 < z3*40)'", ep.formula(_))
    println(x)
  }

  "formula error messages" should "exist" in {
    parse("(x <=2 ", ep.formula(_)) match
    {case (s : Success[Formula]) => println("success: " + s)
    case (f: Failure) => println(f.extra.trace())
    }
  }

  "program error messages" should "exist" in {
    parse("x'=2 & x >= ;", ep.program(_)) match
      {case (s : Success[Program]) => println("success: " + s)
       case (f: Failure) => println(f.extra.trace())
    }
   }
}
