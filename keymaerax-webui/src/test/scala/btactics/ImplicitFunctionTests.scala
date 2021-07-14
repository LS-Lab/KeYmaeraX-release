/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.ReflectiveExpressionBuilder
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics.dbx
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.{AxIndex, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{DLArchiveParser, InterpretedSymbols}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import org.scalatest.LoneElement.convertToCollectionLoneElementWrapper
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Tests for implicit function definitions & the involved substitutions.
 * @author James Gallicchio
 */
class ImplicitFunctionTests extends TacticTestBase {
  private val parser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))

  private def parse (input: String) = parser.parse(input).loneElement

  "implicit fn oracle" should "return correct axiom for abs" in {
    val absAxiom = Provable.implicitFuncAxiom(InterpretedSymbols.absF)
    absAxiom.conclusion shouldBe Sequent(Vector[Formula](), Vector(Equiv(
      Equal(DotTerm(),FuncOf(InterpretedSymbols.absF, DotTerm(idx=Some(0)))),
      "._0 >= 0 & . = ._0 | ._0 < 0 & . = -._0".asFormula
    )))
  }

  "implicit fn oracle" should "return correct axiom for max" in {
    val maxAxiom = Provable.implicitFuncAxiom(InterpretedSymbols.maxF)
    maxAxiom.conclusion shouldBe Sequent(Vector[Formula](), Vector(Equiv(
      Equal(DotTerm(),FuncOf(InterpretedSymbols.maxF, Pair(DotTerm(idx=Some(0)),DotTerm(idx=Some(1))))),
      "._0 < ._1 & . = ._1 | ._0 >= ._1 & . = ._0".asFormula
    )))
  }

  "DLArchiveParser" should "parse implicit functions correctly" in {
    val input =
      """ArchiveEntry "entry1"
        | ProgramVariables Real y; End.
        | ImplicitDefinitions
        |  Real abs(Real x) = y <-> x >= 0 & y = x | x < 0 & y = -x;
        | End.
        | Problem abs(-1) = 1 End.
        |End.
        |""".stripMargin
    val prog = parse(input)

    // Note this is only equal to InterpretedSymbols.absF because the
    // program's (implicit) definition is syntactically equivalent
    prog.expandedModel shouldBe Equal(FuncOf(InterpretedSymbols.absF, Neg(Number(1))), Number(1))
  }

  "implicit fn axioms" should "substitute against an abbreviation" in withMathematica { _ =>
    val prob = GreaterEqual(FuncOf(InterpretedSymbols.absF,"x".asVariable),Number(0))

    val pvble = proveBy(prob,
      abbrvAll(FuncOf(InterpretedSymbols.absF,Variable("x")),None)
        & useAt(ElidingProvable(Provable.implicitFuncAxiom(InterpretedSymbols.absF)))(-1)
        & QE
    )

    pvble shouldBe 'proved
  }

  val exp = Function(name="exp",domain=Real, sort=Real,
    interp = Some(/* . = exp(._0) <-> */ "\\exists t \\exists e t=0 & e=1 & ((<{t'=1,e'=e}> (t=._0 & e=.)) | (<{t'=-1,e'=-e}> (t=._0 & e=.)))".asFormula))

  "differential defs" should "prove exp differential axiom" in {
    val prob = Equal(Differential(FuncOf(exp,"x".asVariable)),
                      Times(FuncOf(exp,"x".asVariable),Differential("x".asVariable)))
    val pvble = proveBy(prob, skip
      //TODO
    )

    pvble shouldBe 'proved
  }

  it should "prove exp always positive in dL" in {
    val problem = Greater(FuncOf(exp,"x".asVariable), Number(0))

    val pvble = proveBy(problem,
      skip //TODO
    )

    pvble shouldBe 'proved
  }

  val sin = Function(name="sin",domain=Real, sort=Real,
    interp = Some(/* . = sin(._0) <-> */ "\\exists t \\exists s \\exists c t=0 & s=0 & c=1 & ((<{t'=1,s'=c,c'=-s}> (t=._0 & s=.)) | (<{t'=-1,s'=-c,c'=s}> (t=._0 & s=.)))".asFormula))
  val cos = Function(name="cos",domain=Real, sort=Real,
    interp = Some(/* . = cos(._0) <-> */ "\\exists t \\exists s \\exists c t=0 & s=0 & c=1 & ((<{t'=1,s'=c,c'=-s}> (t=._0 & c=.)) | (<{t'=-1,s'=-c,c'=s}> (t=._0 & c=.)))".asFormula))

  it should "prove simple trig lemmas in dL" in withMathematica { _ =>
    val prob = Equal(Plus(Power(FuncOf(sin,"x".asVariable),Number(2)),
                          Power(FuncOf(cos,"x".asVariable),Number(2))),
                      Number(1))
    val pvble = proveBy(prob,
      abbrvAll(FuncOf(sin,"x".asVariable),None)
      & abbrvAll(FuncOf(cos,"x".asVariable),None)
      & useAt(ElidingProvable(Provable.implicitFuncAxiom(sin)))(-1)
      & useAt(ElidingProvable(Provable.implicitFuncAxiom(cos)))(-2)
      //TODO
    )

    pvble shouldBe 'proved
  }


  it should "prove sin differential axiom" in {
    val prob = Equal(Differential(FuncOf(sin,"x".asVariable)),
      Times(FuncOf(cos,"x".asVariable),Differential("x".asVariable)))
    val pvble = proveBy(prob, skip
      //TODO
    )

    pvble shouldBe 'proved
  }

  "kyx2mathematica" should "convert special implicit functions to Mathematica" in withMathematica { _ =>
    //TODO: not sure how this will be set up
  }

  //TODO: substitute uninterpreted for interpreted functions in these tests
  "examples" should "work under assignments and nesting" in withMathematica { _ =>
    val fml = "x =1 -> [x := exp(exp(x)); x:=1; ++ x:= exp(x); ] x > 0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by ODE(1), dI('full)(1), etc.

    pr shouldBe 'proved
  }

  it should "be usable as a loop invariant" in withMathematica { _ =>
    val fml = "x = 0 -> [ {x := x + 1;}* ] exp(x) >= 1".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove using loop with loop invariants like x>=0 or exp(x)>=1

    pr shouldBe 'proved
  }

  it should "work with DI (1)" in withMathematica { _ =>
    val fml = "x =1 -> [{x' = exp(x)}] x > 0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    pr shouldBe 'proved
  }

  it should "work with DI (2)" in withMathematica { _ =>
    val fml = "x>=0&y>=0&z>=0 -> [{x' = exp(y), y' = exp(z), z'=1}] x+y+z>=0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    pr shouldBe 'proved
  }

  it should "work with DI (3)" in withMathematica { _ =>
    val fml = "x=5 -> [{x' = sin(x) + 1}] x>=0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    pr shouldBe 'proved
  }

  it should "model a pendulum" in withMathematica { _ =>
    val fml = "a > 0 & b > 0 & x1 = 1 & x2 = 1 -> [{x1' = x2, x2'= -a*sin(x1) - b*x2}] a*(1-cos(x1))+1/2*x2^2 <= 1/2".asFormula
    val pr = proveBy(fml, skip)
    // end goal: prove something like this or more

    pr shouldBe 'proved
  }
}
