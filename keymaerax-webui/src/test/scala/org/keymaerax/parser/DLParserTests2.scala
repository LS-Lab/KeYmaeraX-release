/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.core._
import org.keymaerax.tags.UsualTest
import org.scalatest.PrivateMethodTester
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import scala.collection.immutable._

/**
 * Tests the DL parser some more.
 *
 * Originally, this test suite tested [[DLParser]]'s precursor, but when that was deleted, it was migrated over to test
 * [[DLParser]].
 *
 * @author Andre Platzer
 */
@UsualTest
class DLParserTests2 extends AnyFlatSpec with Matchers with PrivateMethodTester {
  val parser = new DLParser
  val pp: KeYmaeraXPrettyPrinter.type = KeYmaeraXPrettyPrinter

  val x: BaseVariable = Variable("x")
  val y: BaseVariable = Variable("y")
  val z: BaseVariable = Variable("z")

  val f0: FuncOf = FuncOf(Function("f", None, Unit, Real), Nothing)
  val g0: FuncOf = FuncOf(Function("g", None, Unit, Real), Nothing)
  val h0: FuncOf = FuncOf(Function("h", None, Unit, Real), Nothing)

  val f: Function = Function("f", None, Real, Real)
  val g: Function = Function("g", None, Real, Real)
  val h: Function = Function("h", None, Real, Real)

  val p0: PredOf = PredOf(Function("p", None, Unit, Bool), Nothing)
  val q0: PredOf = PredOf(Function("q", None, Unit, Bool), Nothing)
  val r0: PredOf = PredOf(Function("r", None, Unit, Bool), Nothing)

  val p: Function = Function("p", None, Real, Bool)
  val q: Function = Function("q", None, Real, Bool)
  val r: Function = Function("r", None, Real, Bool)

  val f2: Function = Function("f", None, Tuple(Real, Real), Real)
  val g2: Function = Function("g", None, Tuple(Real, Real), Real)
  val h2: Function = Function("h", None, Tuple(Real, Real), Real)

  val p2: Function = Function("p", None, Tuple(Real, Real), Bool)
  val q2: Function = Function("q", None, Tuple(Real, Real), Bool)
  val r2: Function = Function("r", None, Tuple(Real, Real), Bool)

  behavior of "DLParser"

  it should "parse addition and multiplication" in {
    parser("x+y*z") shouldBe Plus(Variable("x"), Times(Variable("y"), Variable("z")))
    parser("x*y+z") shouldBe Plus(Times(Variable("x"), Variable("y")), Variable("z"))
    parser("(x*y)+z") shouldBe Plus(Times(Variable("x"), Variable("y")), Variable("z"))
    parser("x*(y+z)") shouldBe Times(Variable("x"), Plus(Variable("y"), Variable("z")))
  }

  it should "parse subtraction" in {
    parser("x-y") shouldBe Minus(Variable("x"), Variable("y"))
    parser("x+y-z") shouldBe Minus(Plus(Variable("x"), Variable("y")), Variable("z"))
    parser("x-y+z") shouldBe Plus(Minus(Variable("x"), Variable("y")), Variable("z"))
    parser("x-y-z") shouldBe Minus(Minus(Variable("x"), Variable("y")), Variable("z"))
    parser("x-(y+z)") shouldBe Minus(Variable("x"), Plus(Variable("y"), Variable("z")))
    parser("x-(y-z)") shouldBe Minus(Variable("x"), Minus(Variable("y"), Variable("z")))
  }

  it should "parse negation" in {
    parser("-x") shouldBe Neg(Variable("x"))

    parser("2*-y") shouldBe Times(Number(2), Neg(Variable("y")))
    parser("-2*y") shouldBe Neg(Times(Number(2), Variable("y")))
    parser("-(2)*y") shouldBe Neg(Times(Number(2), Variable("y")))
    parser("(-2)*y") shouldBe Times(Number(-2), Variable("y"))

    parser("x+-y") shouldBe Plus(Variable("x"), Neg(Variable("y")))
    parser("x--y") shouldBe Minus(Variable("x"), Neg(Variable("y")))
    parser("x*-y") shouldBe Times(Variable("x"), Neg(Variable("y")))
    parser("x/-y") shouldBe Divide(Variable("x"), Neg(Variable("y")))
    parser("x^-y") shouldBe Power(Variable("x"), Neg(Variable("y")))

    parser("-x+y") shouldBe Plus(Neg(Variable("x")), Variable("y"))
    parser("-x-y") shouldBe Minus(Neg(Variable("x")), Variable("y"))
    parser("-x*y") shouldBe Neg(Times(Variable("x"), Variable("y")))
    parser("-x/y") shouldBe Neg(Divide(Variable("x"), Variable("y")))
    parser("-x^y") shouldBe Neg(Power(Variable("x"), Variable("y")))
  }

  it should "parse negative number literals" in {
    parser("-2") shouldBe Neg(Number(2))
    parser("-(2)") shouldBe Neg(Number(2))
    parser("(-2)") shouldBe Number(-2)
    parser("(- 2)") shouldBe Neg(Number(2))
    parser("(-(2))") shouldBe Neg(Number(2))
  }

  it should "parse terms" in {
    parser("f()>0") shouldBe Greater(f0, Number(0))

    parser("x-y*z+a*b") shouldBe
      Plus(Minus(Variable("x"), Times(Variable("y"), Variable("z"))), Times(Variable("a"), Variable("b")))

    parser("x-y+z*a/b^c") shouldBe Plus(
      Minus(Variable("x"), Variable("y")),
      Divide(Times(Variable("z"), Variable("a")), Power(Variable("b"), Variable("c"))),
    )
  }

  it should "parse p()&q()|r()" in { parser("p()&q()|r()") shouldBe Or(And(p0, q0), r0) }

  it should "parse f()>0&g()<=2|r()<1" in {
    parser("f()>0&g()<=2|r()<1") shouldBe Or(
      And(Greater(f0, Number(0)), LessEqual(g0, Number(2))),
      Less(FuncOf(Function("r", None, Unit, Real), Nothing), Number(1)),
    )
  }

  it should "parse f()>0&g(x)<=2|r()<1" in {
    parser("f()>0&g(x)<=2|r()<1") shouldBe Or(
      And(Greater(f0, Number(0)), LessEqual(FuncOf(Function("g", None, Real, Real), Variable("x")), Number(2))),
      Less(FuncOf(Function("r", None, Unit, Real), Nothing), Number(1)),
    )
  }

  it should "parse x>0 & y<1 | z>=2" in {
    parser("x>0 & y<1 | z>=2") shouldBe
      Or(And(Greater(Variable("x"), Number(0)), Less(Variable("y"), Number(1))), GreaterEqual(Variable("z"), Number(2)))
  }

  it should "parse x:=y+1;++z:=0;" in {
    parser("x:=y+1;++z:=0;") shouldBe
      Choice(Assign(Variable("x"), Plus(Variable("y"), Number(1))), Assign(Variable("z"), Number(0)))
  }

  it should "parse x:=y+1;z:=0;" in {
    parser("x:=y+1;z:=0;") shouldBe
      Compose(Assign(Variable("x"), Plus(Variable("y"), Number(1))), Assign(Variable("z"), Number(0)))
  }

  it should "parse x-y'+z" in {
    parser("x-y'+z") shouldBe Plus(Minus(Variable("x"), DifferentialSymbol(Variable("y"))), Variable("z"))
  }

  it should "parse x-(y)'+z" in {
    parser("x-(y)'+z") shouldBe Plus(Minus(Variable("x"), Differential(Variable("y"))), Variable("z"))
  }

  it should "parse (x-y)'+z" in {
    parser("(x-y)'+z") shouldBe Plus(Differential(Minus(Variable("x"), Variable("y"))), Variable("z"))
  }

  it should "parse [x:=y+1;]x>=0" in {
    parser("[x:=y+1;]x>=0") shouldBe
      Box(Assign(Variable("x"), Plus(Variable("y"), Number(1))), GreaterEqual(Variable("x"), Number(0)))
  }

  it should "parse [{x'=y+1}]x>=0" in {
    parser("[{x'=y+1}]x>=0") shouldBe Box(
      ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Plus(Variable("y"), Number(1))), True),
      GreaterEqual(Variable("x"), Number(0)),
    )
  }

  it should "parse [{x'=y+1,y'=5}]x>=0" in {
    parser("[{x'=y+1,y'=5}]x>=0") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Plus(Variable("y"), Number(1))),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(5)),
        ),
        True,
      ),
      GreaterEqual(Variable("x"), Number(0)),
    )
  }

  it should "parse [{x'=1&x>2}]x>=0" in {
    parser("[{x'=1&x>2}]x>=0") shouldBe Box(
      ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(1)), Greater(Variable("x"), Number(2))),
      GreaterEqual(Variable("x"), Number(0)),
    )
  }

  it should "parse [{x'=y+1&x>0}]x>=0" in {
    parser("[{x'=y+1&x>0}]x>=0") shouldBe Box(
      ODESystem(
        AtomicODE(DifferentialSymbol(Variable("x")), Plus(Variable("y"), Number(1))),
        Greater(Variable("x"), Number(0)),
      ),
      GreaterEqual(Variable("x"), Number(0)),
    )
  }

  it should "parse [{x'=y+1,y'=5&x>y}]x>=0" in {
    parser("[{x'=y+1,y'=5&x>y}]x>=0") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Plus(Variable("y"), Number(1))),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(5)),
        ),
        Greater(Variable("x"), Variable("y")),
      ),
      GreaterEqual(Variable("x"), Number(0)),
    )
  }

  it should "parse [a;]x>=0" in {
    parser("[a;]x>=0") shouldBe Box(ProgramConst("a"), GreaterEqual(Variable("x"), Number(0)))
  }

  it should "parse <a;>x>0" in {
    parser("<a;>x>0") shouldBe Diamond(ProgramConst("a"), Greater(Variable("x"), Number(0)))
  }

  it should "parse [a;b;]x>=0" in {
    parser("[a;b;]x>=0") shouldBe
      Box(Compose(ProgramConst("a"), ProgramConst("b")), GreaterEqual(Variable("x"), Number(0)))
  }

  it should "parse [a;]p(x)" in { parser("[a;]p(x)") shouldBe Box(ProgramConst("a"), PredOf(p, Variable("x"))) }

  it should "parse [a;b;]p(x)" in {
    parser("[a;b;]p(x)") shouldBe Box(Compose(ProgramConst("a"), ProgramConst("b")), PredOf(p, Variable("x")))
  }

  it should "parse <a;b;>p(x)" in {
    parser("<a;b;>p(x)") shouldBe Diamond(Compose(ProgramConst("a"), ProgramConst("b")), PredOf(p, Variable("x")))
  }

  it should "parse <a;b;>x>0" in {
    parser("<a;b;>x>0") shouldBe
      Diamond(Compose(ProgramConst("a"), ProgramConst("b")), Greater(Variable("x"), Number(0)))
  }

  it should "parse [a;++b;]x>=0" in {
    parser("[a;++b;]x>=0") shouldBe
      Box(Choice(ProgramConst("a"), ProgramConst("b")), GreaterEqual(Variable("x"), Number(0)))
  }

  it should "parse <a;++b;>x>0" in {
    parser("<a;++b;>x>0") shouldBe
      Diamond(Choice(ProgramConst("a"), ProgramConst("b")), Greater(Variable("x"), Number(0)))
  }

  // pathetic cases

  it should "parse (((p())))&q()" in { parser("(((p())))&q()") shouldBe And(p0, q0) }

  it should "parse p()&(((q())))" in { parser("p()&(((q())))") shouldBe And(p0, q0) }

  it should "parse (((f())))+g()>=0" in { parser("(((f())))+g()>=0") shouldBe GreaterEqual(Plus(f0, g0), Number(0)) }

  it should "parse 0<=f()+(((g())))" in { parser("0<=f()+(((g())))") shouldBe LessEqual(Number(0), Plus(f0, g0)) }

  ignore should "perhaps default to term when trying to parse p()" in {
    parser("p()") shouldBe FuncOf(Function("p", None, Unit, Real), Nothing)
  }

  it should "parse f()>0" in { parser("f()>0") shouldBe Greater(f0, Number(0)) }

  it should "parse -x-y" in { parser("-x-y") shouldBe Minus(Neg(Variable("x")), Variable("y")) }

  it should "parse -x*y" in { parser("-x*y") shouldBe Neg(Times(Variable("x"), Variable("y"))) }

  it should "parse -x/y" in { parser("-x/y") shouldBe Neg(Divide(Variable("x"), Variable("y"))) }

  it should "parse -x^y" in { parser("-x^y") shouldBe Neg(Power(Variable("x"), Variable("y"))) }

  it should "not parse p()+x as a formula" in { a[ParseException] should be thrownBy parser.formulaParser("p()+x") }

  it should "not parse f()&x>0 as a term" in { a[ParseException] should be thrownBy parser.termParser("f()&x>0") }

  it should "parse a term when trying to parse p() as a term" in {
    parser.termParser("p()") shouldBe FuncOf(Function("p", None, Unit, Real), Nothing)
  }

  it should "parse a term when trying to parse p(x) as a term" in {
    parser.termParser("p(x)") shouldBe FuncOf(Function("p", None, Real, Real), Variable("x"))
  }

  it should "parse a formula when trying to parse p() as a formula" in {
    parser.formulaParser("p()") shouldBe PredOf(Function("p", None, Unit, Bool), Nothing)
  }

  it should "parse a formula when trying to parse p(x) as a formula" in {
    parser.formulaParser("p(x)") shouldBe PredOf(Function("p", None, Real, Bool), Variable("x"))
  }

  it should "default to formula when trying to parse x'=5" in {
    parser("x'=5") shouldBe Equal(DifferentialSymbol(Variable("x")), Number(5))
  }

  it should "parse a formula when trying to parse x'=5 as a formula" in {
    parser.formulaParser("x'=5") shouldBe Equal(DifferentialSymbol(Variable("x")), Number(5))
  }

  it should "default to formula when trying to parse x'=5&x>2" in {
    parser("x'=5&x>2") shouldBe
      And(Equal(DifferentialSymbol(Variable("x")), Number(5)), Greater(Variable("x"), Number(2)))
  }

  ignore should "probably not parse a simple program when trying to parse x'=5 as a program" in {
    parser.programParser("x'=5") should not be AtomicODE(DifferentialSymbol(Variable("x")), Number(5))
  }

  it should "perhaps parse an ODESystem program from [x'=5;]p(x) if parsed at all" in {
    try {
      parser("[x'=5;]p(x)") shouldBe
        Box(ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(5)), True), PredOf(p, Variable("x")))
    } catch { case _: ParseException => }
  }

  it should "perhaps parse an ODESystem program from <x'=5;>p(x) if parsed at all" in {
    try {
      parser("<x'=5;>p(x)") shouldBe
        Diamond(ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(5)), True), PredOf(p, Variable("x")))
    } catch { case _: ParseException => }
  }

  it should "parse [{x'=5&x>7}]p(x)" in {
    parser("[{x'=5&x>7}]p(x)") shouldBe Box(
      ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(5)), Greater(Variable("x"), Number(7))),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse [{x'=5,y'=2}]p(x)" in {
    parser("[{x'=5,y'=2}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        True,
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse [{y'=2,x'=5}]p(x)" in {
    parser("[{y'=2,x'=5}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
        ),
        True,
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse [{x'=5,y'=2&x>7}]p(x)" in {
    parser("[{x'=5,y'=2&x>7}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        Greater(Variable("x"), Number(7)),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse long evolution domains [{x'=5,y'=2&x>7->y<2}]p(x)" in {
    parser("[{x'=5,y'=2&x>7->y<2}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        Imply(Greater(Variable("x"), Number(7)), Less(y, Number(2))),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse long evolution domains [{x'=5,y'=2&x>7&y<2}]p(x)" in {
    parser("[{x'=5,y'=2&x>7&y<2}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        And(Greater(Variable("x"), Number(7)), Less(y, Number(2))),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse long evolution domains [{x'=5,y'=2&x>7|y<8}]p(x)" in {
    parser("[{x'=5,y'=2&x>7|y<8}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        Or(Greater(Variable("x"), Number(7)), Less(y, Number(8))),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse differential program constants [{c}]p(x)" in {
    parser("[{c}]p(x)") shouldBe Box(ODESystem(DifferentialProgramConst("c", AnyArg), True), PredOf(p, Variable("x")))
  }

  it should "parse differential program constants [{c&x>7|y<8}]p(x)" in {
    parser("[{c&x>7|y<8}]p(x)") shouldBe Box(
      ODESystem(DifferentialProgramConst("c", AnyArg), Or(Greater(Variable("x"), Number(7)), Less(y, Number(8)))),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse differential program constants [{c,y'=2&x>7|y<8}]p(x)" in {
    parser("[{c,y'=2&x>7|y<8}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          DifferentialProgramConst("c", AnyArg),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        Or(Greater(Variable("x"), Number(7)), Less(y, Number(8))),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse differential program constants [{y'=2,c&x>7|y<8}]p(x)" in {
    parser("[{y'=2,c&x>7|y<8}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
          DifferentialProgramConst("c", AnyArg),
        ),
        Or(Greater(Variable("x"), Number(7)), Less(y, Number(8))),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse !x<5" in { parser("!x<5") shouldBe Not(Less(x, Number(5))) }

  it should "parse !x<=5" in { parser("!x<=5") shouldBe Not(LessEqual(x, Number(5))) }

  it should "parse !x+y<5" in { parser("!x+y<5") shouldBe Not(Less(Plus(x, y), Number(5))) }

  it should "parse !x>=5" in { parser("!x>=5") shouldBe Not(GreaterEqual(x, Number(5))) }

  it should "parse !x>5" in { parser("!x>5") shouldBe Not(Greater(x, Number(5))) }

  it should "parse ?!x>5; as a test of a negation" in {
    parser("?!x>5;") shouldBe Test(Not(Greater(x, Number(5))))
    parser.programParser("?!x>5;") shouldBe Test(Not(Greater(x, Number(5))))
  }

  it should "parse long evolution domains [{x'=5,y'=2&!(x>7)}]p(x)" in {
    parser("[{x'=5,y'=2&!(x>7)}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        Not(Greater(Variable("x"), Number(7))),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse long evolution domains [{x'=5,y'=2&!x>=7}]p(x)" in {
    parser("[{x'=5,y'=2&!x>=7}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        Not(GreaterEqual(Variable("x"), Number(7))),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse long evolution domains [{x'=5,y'=2&!x>7}]p(x)" in {
    parser("[{x'=5,y'=2&!x>7}]p(x)") shouldBe Box(
      ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(2)),
        ),
        Not(Greater(Variable("x"), Number(7))),
      ),
      PredOf(p, Variable("x")),
    )
  }

  it should "parse lexically disambiguated x< -y not as REVIMPLY" in {
    parser("x< -y") shouldBe Less(x, Neg(y))
    parser(pp(Less(x, Neg(y)))) shouldBe Less(x, Neg(y))
  }

  it should "parse [x:=q();]f()->r()+c(x)>0" in {
    parser("[x:=q();]f()->r()+c(x)>0") shouldBe Imply(
      Box(
        Assign(x, FuncOf(Function("q", None, Unit, Real), Nothing)),
        PredOf(Function("f", None, Unit, Bool), Nothing),
      ),
      Greater(
        Plus(FuncOf(Function("r", None, Unit, Real), Nothing), FuncOf(Function("c", None, Real, Real), x)),
        Number(0),
      ),
    )
  }

  it should "parse [x:=q(x);]f(x)->r(x)+c(x)>0" in {
    parser("[x:=q(x);]f(x)->r(x)+c(x)>0") shouldBe Imply(
      Box(Assign(x, FuncOf(Function("q", None, Real, Real), x)), PredOf(Function("f", None, Real, Bool), x)),
      Greater(Plus(FuncOf(Function("r", None, Real, Real), x), FuncOf(Function("c", None, Real, Real), x)), Number(0)),
    )
  }

  it should "parse [x:=q(||);]f(||)->r(||)+c(x)>0" in {
    parser("[x:=q(||);]f(||)->r(||)+c(x)>0") shouldBe Imply(
      Box(Assign(x, UnitFunctional("q", AnyArg, Real)), UnitPredicational("f", AnyArg)),
      Greater(Plus(UnitFunctional("r", AnyArg, Real), FuncOf(Function("c", None, Real, Real), x)), Number(0)),
    )
  }

  it should "parse [x:=q();]f()->g()" in {
    parser("[x:=q();]f()->g()") shouldBe Imply(
      Box(
        Assign(x, FuncOf(Function("q", None, Unit, Real), Nothing)),
        PredOf(Function("f", None, Unit, Bool), Nothing),
      ),
      PredOf(Function("g", None, Unit, Bool), Nothing),
    )
  }

  it should "parse [x:=q(x);]f(x)->g(x)" in {
    parser("[x:=q(x);]f(x)->g(x)") shouldBe Imply(
      Box(Assign(x, FuncOf(Function("q", None, Real, Real), x)), PredOf(Function("f", None, Real, Bool), x)),
      PredOf(Function("g", None, Real, Bool), x),
    )
  }

  it should "parse [x:=q(||);]f(||)->g(||)" in {
    parser("[x:=q(||);]f(||)->g(||)") shouldBe Imply(
      Box(Assign(x, UnitFunctional("q", AnyArg, Real)), UnitPredicational("f", AnyArg)),
      UnitPredicational("g", AnyArg),
    )
  }

  it should "parse \\forall x(y()) not as a function application" in {
    parser("\\forall x(y())") shouldBe Forall(IndexedSeq(x), PredOf(Function("y", None, Unit, Bool), Nothing))
  }

  it should "parse \\forall x(y()+g()>=5) not as a function application" in {
    parser("\\forall x(y()+g()>5)") shouldBe Forall(
      IndexedSeq(x),
      Greater(
        Plus(FuncOf(Function("y", None, Unit, Real), Nothing), FuncOf(Function("g", None, Unit, Real), Nothing)),
        Number(5),
      ),
    )
  }

  ignore should "parse an ODESystem program when trying to parse x'=5 as a program" in {
    parser.programParser("x'=5") shouldBe ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Number(5)), True)
  }

  it should "parse a formula when trying to parse x'=5&x>2 as a formula" in {
    parser.formulaParser("x'=5&x>2") shouldBe
      And(Equal(DifferentialSymbol(Variable("x")), Number(5)), Greater(Variable("x"), Number(2)))
  }

  ignore should "perhaps always parse x'=5,y'=7&x>2 as a program" in {
    parser.programParser("x'=5,y'=7&x>2") shouldBe ODESystem(
      DifferentialProduct(
        AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
        AtomicODE(DifferentialSymbol(Variable("y")), Number(7)),
      ),
      Greater(Variable("x"), Number(2)),
    )
    try {
      parser("x'=5,y'=7&x>2") shouldBe ODESystem(
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
          AtomicODE(DifferentialSymbol(Variable("y")), Number(7)),
        ),
        Greater(Variable("x"), Number(2)),
      )
    } catch { case _: ParseException => }
  }

  it should "always parse {x'=5,y'=7&x>2} as a program" in {
    parser("{x'=5,y'=7&x>2}") shouldBe ODESystem(
      DifferentialProduct(
        AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
        AtomicODE(DifferentialSymbol(Variable("y")), Number(7)),
      ),
      Greater(Variable("x"), Number(2)),
    )
    parser.programParser("{x'=5,y'=7&x>2}") shouldBe ODESystem(
      DifferentialProduct(
        AtomicODE(DifferentialSymbol(Variable("x")), Number(5)),
        AtomicODE(DifferentialSymbol(Variable("y")), Number(7)),
      ),
      Greater(Variable("x"), Number(2)),
    )
  }

  ignore should "not parse x'=5,y'=7&x>2 as a formula" in {
    a[ParseException] should be thrownBy parser.formulaParser("x'=5,y'=7&x>2")
  }

  it should "parse (<a;b;>p(x))&q()" in {
    parser("(<a;b;>p(x))&q()") shouldBe
      And(Diamond(Compose(ProgramConst("a"), ProgramConst("b")), PredOf(p, Variable("x"))), q0)
  }

  it should "parse \\forall x x>=0" in {
    parser("\\forall x x>=0") shouldBe Forall(Seq(Variable("x")), GreaterEqual(Variable("x"), Number(0)))
  }

  it should "parse \\forall x p(x)" in {
    parser("\\forall x p(x)") shouldBe Forall(Seq(Variable("x")), PredOf(p, Variable("x")))
  }

  it should "parse \\forall x x>=0&x<0" in {
    parser("\\forall x x>=0&x<0") shouldBe
      And(Forall(Seq(Variable("x")), GreaterEqual(Variable("x"), Number(0))), Less(Variable("x"), Number(0)))
  }

  it should "parse \\forall x p(x)&q(x)" in {
    parser("\\forall x p(x)&q(x)") shouldBe
      And(Forall(Seq(Variable("x")), PredOf(p, Variable("x"))), PredOf(q, Variable("x")))
  }

  it should "parse" in {
    parser("p(x,y)->f(x,y)>g(x)") shouldBe Imply(PredOf(p2, Pair(x, y)), Greater(FuncOf(f2, Pair(x, y)), FuncOf(g, x)))
  }

  it should "parse type mess p(x,y)->f(x,y)>p(x)" in {
    parser("p(x,y)->f(x,y)>p(x)") shouldBe Imply(
      PredOf(Function("p", None, Tuple(Real, Real), Bool), Pair(x, y)),
      Greater(
        FuncOf(Function("f", None, Tuple(Real, Real), Real), Pair(x, y)),
        FuncOf(Function("p", None, Real, Real), x),
      ),
    )
  }

  it should "parse type mess p(x,y)->!p(x)" in {
    parser("p(x,y)->!p(x)") shouldBe Imply(
      PredOf(Function("p", None, Tuple(Real, Real), Bool, None), Pair(x, y)),
      Not(PredOf(Function("p", None, Real, Bool), x)),
    )
  }

  it should "parse type mess p()->!p(x)" in {
    parser("p()->!p(x)") shouldBe Imply(p0, Not(PredOf(Function("p", None, Real, Bool), x)))
  }

  it should "parse type mess p() -> [x:=p();]true" in {
    parser("p() -> [x:=p();]true") shouldBe
      Imply(p0, Box(Assign(x, FuncOf(Function("p", None, Unit, Real), Nothing)), True))
  }

  it should "parse type mess p() -> [{x'=p()}]true" in {
    parser("p() -> [{x'=p()}]true") shouldBe Imply(
      p0,
      Box(
        ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), FuncOf(Function("p", None, Unit, Real), Nothing)), True),
        True,
      ),
    )
  }

  it should "parse type mess x() -> [x:=x(x);]x()>x(x,x())" in {
    parser("x() -> [x:=x(x);]x()>x(x,x())") shouldBe Imply(
      PredOf(Function("x", None, Unit, Bool), Nothing),
      Box(
        Assign(x, FuncOf(Function("x", None, Real, Real), x)),
        Greater(
          FuncOf(Function("x", None, Unit, Real), Nothing),
          FuncOf(
            Function("x", None, Tuple(Real, Real), Real),
            Pair(x, FuncOf(Function("x", None, Unit, Real), Nothing)),
          ),
        ),
      ),
    )
  }

  "Annotation parser" should "parse x>0 -> [{x:=x+1;}*@invariant(x>0)]x>0" in {
    parser("x>0 -> [{x:=x+1;}*@invariant(x>0)]x>0") shouldBe
      Imply(Greater(x, Number(0)), Box(Loop(Assign(x, Plus(x, Number(1)))), Greater(x, Number(0))))
  }

  it should "parse x>0 -> [{x'=1}@invariant(x>0)]x>0" in {
    parser("x>0 -> [{x'=1}@invariant(x>0)]x>0") shouldBe Imply(
      Greater(x, Number(0)),
      Box(ODESystem(AtomicODE(DifferentialSymbol(x), Number(1)), True), Greater(x, Number(0))),
    )
  }

  it should "parse x>0 -> [{x'=1&x<2}@invariant(x>0)]x>0" in {
    parser("x>0 -> [{x'=1&x<2}@invariant(x>0)]x>0") shouldBe Imply(
      Greater(x, Number(0)),
      Box(ODESystem(AtomicODE(DifferentialSymbol(x), Number(1)), Less(x, Number(2))), Greater(x, Number(0))),
    )
  }

  it should "parse x>0 -> [{x'=1,y'=5&x<2}@invariant(x>0)]x>0" in {
    parser("x>0 -> [{x'=1,y'=5&x<2}@invariant(x>0)]x>0") shouldBe Imply(
      Greater(x, Number(0)),
      Box(
        ODESystem(
          DifferentialProduct(AtomicODE(DifferentialSymbol(x), Number(1)), AtomicODE(DifferentialSymbol(y), Number(5))),
          Less(x, Number(2)),
        ),
        Greater(x, Number(0)),
      ),
    )
  }

  it should "refuse to parse meaningless annotation x>0 -> [x:=5;@invariant(x>0)]x>0" in {
    a[ParseException] should be thrownBy parser("x>0 -> [x:=5;@invariant(x>0)]x>0")
  }

  it should "refuse to parse meaningless annotation x>0 -> [x:=5;x:=2;@invariant(x>0)]x>0" in {
    a[ParseException] should be thrownBy parser("x>0 -> [x:=5;x:=2;@invariant(x>0)]x>0")
  }

  it should "refuse to parse meaningless annotation x>0 -> [{x:=5;x:=2;}@invariant(x>0)]x>0" in {
    a[ParseException] should be thrownBy parser("x>0 -> [{x:=5;x:=2;}@invariant(x>0)]x>0")
  }

  it should "refuse to parse meaningless annotation x>0 -> [{x:=5;++x:=2;}@invariant(x>0)]x>0" in {
    a[ParseException] should be thrownBy parser("x>0 -> [{x:=5;++x:=2;}@invariant(x>0)]x>0")
  }

  it should "refuse to parse meaningless annotation x>0 -> [?x>0;@invariant(x>0)]x>0" in {
    a[ParseException] should be thrownBy parser("x>0 -> [?x>0;@invariant(x>0)]x>0")
  }

  /////////////////////////////////////

  behavior of "Parser documentation"

  it should "compile and run printer 1" in {
    val pp = KeYmaeraXPrettyPrinter
    // "x < -y"
    val fml0 = Less(Variable("x"), Neg(Variable("y")))
    val fml0str = pp(fml0)
    // "true -> [x:=1;]x>=0"
    val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
    val fml1str = pp(fml1)
  }

  it should "compile and run printer 2" in {
    val pp = KeYmaeraXPrettyPrinter
    // "x < -(y)"
    val fml0 = Less(Variable("x"), Neg(Variable("y")))
    val fml0str = pp(fml0)
    // "true -> ([x:=1;](x>=0))"
    val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
    val fml1str = pp(fml1)
  }

  it should "compile and run parser 1" in {
    val fml0 = parser("x!=5")
    val fml1 = parser("x>0 -> [x:=x+1;]x>1")
    val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
  }

  it should "compile and run parser 2" in {
    // formulas
    val fml0 = parser("x!=5")
    val fml1 = parser("x>0 -> [x:=x+1;]x>1")
    val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
    // terms
    val term0 = parser("x+5")
    val term1 = parser("x^2-2*x+7")
    val term2 = parser("x*y/3+(x-1)^2+5*z")
    // programs
    val prog0 = parser("x:=1;")
    val prog1 = parser("x:=1;x:=5;x:=-1;")
    val prog2 = parser("x:=1;{{x'=5}++x:=0;}")
  }

  it should "compile and run formula parser 1" in {
    // the formula parser only accepts formulas
    val parser = (new DLParser).formulaParser
    // formulas
    val fml0 = parser("x!=5")
    val fml1 = parser("x>0 -> [x:=x+1;]x>1")
    val fml2 = parser("x>=0 -> [{x'=2}]x>=0")
    // terms will cause exceptions
    try { parser("x+5") } catch { case e: ParseException => () }
    // programs will cause exceptions
    try { parser("x:=1;") } catch { case e: ParseException => () }
  }

  it should "compile and run parse of print 1" in {
    val pp = KeYmaeraXPrettyPrinter
    val fml = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
    // something like "true -> [x:=1;]x>=0" modulo spacing
    val print = pp(fml)
    val reparse = parser(print)
//    if (fml == reparse) println("Print and reparse successful") else println("Discrepancy")
  }

  it should "compile and run parse of print of parse" in {
    val pp = KeYmaeraXPrettyPrinter
    val input = "x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1"
    val parse = parser(input)
    val print = pp(parse)
  }

  it should "compile and run full print" in {
    val pp = FullPrettyPrinter
    val input = "x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1"
    val parse = parser(input)
    val print = pp(parse)
  }
}
