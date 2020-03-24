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
  /*def parse[T](input: ParserInputSource,
               parser: P[_] => P[T],
               verboseFailures: Boolean = false,
               startIndex: Int = 0,
               instrument: Instrument = null): Parsed[T] = {*/
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
  // formulas
}
