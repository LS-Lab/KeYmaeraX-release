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

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.TermTactics._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import fastparse.Parsed.Success
import fastparse._

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

  // @TODO: check
  it should "respect order of operations" in {
    p("(x - y)*x/y-x+y+-x^x", ep.term(_)) shouldBe Minus(Divide(Times(Minus(vx, vy), vx), vy), Plus(Plus(vx, vy), Neg(Power(vx, vx))))
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
}
