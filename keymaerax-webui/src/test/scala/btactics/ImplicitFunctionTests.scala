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
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, DLArchiveParser, DLParser, InterpretedSymbols, KeYmaeraXArchivePrinter, KeYmaeraXPrettyPrinter, ODEToInterpreted, Parser, PrettierPrintFormatProvider}
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
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
  private val parser = new DLArchiveParser(new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _)))

  private def parse (input: String) = parser.parse(input).loneElement

  "implicit fn oracle" should "return correct axiom for abs" in {
    val absAxiom = Provable.implicitFuncAxiom(InterpretedSymbols.absF)
    absAxiom.conclusion shouldBe Sequent(Vector[Formula](), Vector(Equiv(
      Equal(DotTerm(idx=Some(0)),FuncOf(InterpretedSymbols.absF, DotTerm(idx=Some(1)))),
      "._1 < 0 & ._0 = -(._1) | ._1 >= 0 & ._0 = ._1".asFormula
    )))
  }

  it should "return correct axiom for max" in {
    val maxAxiom = Provable.implicitFuncAxiom(InterpretedSymbols.maxF)
    maxAxiom.conclusion shouldBe Sequent(Vector[Formula](), Vector(Equiv(
      Equal(DotTerm(idx=Some(0)),
        FuncOf(InterpretedSymbols.maxF, Pair(DotTerm(idx=Some(1)),DotTerm(idx=Some(2))))),
      "._1 < ._2 & ._0 = ._2 | ._1 >= ._2 & ._0 = ._1".asFormula
    )))
  }

  "DLArchiveParser" should "parse built-in interpreted functions correctly" in {
    val input =
      """ArchiveEntry "entry1"
        | Problem abs(-1) = 1 End.
        |End.
        |""".stripMargin
    val prog = parse(input)

    prog.model shouldBe Equal(FuncOf(InterpretedSymbols.absF, Neg(Number(1))),Number(1))
  }

  it should "parse inline function interps correctly" in {
    val input =
      """ArchiveEntry "entry1"
        | Problem myAbs<<._1 < 0 & ._0 = -(._1) | ._1 >= 0 & ._0 = ._1>>(-(1)) = 1 End.
        |End.
        |""".stripMargin
    val prog = parse(input)

    prog.model shouldBe Equal(FuncOf(InterpretedSymbols.absF.copy(name="myAbs"),
      Neg(Number(1))),Number(1))
  }

  it should "parse implicit interp definitions correctly" in {
    val input =
      """ArchiveEntry "entry1"
        | ProgramVariables Real y; End.
        | Definitions
        |  implicit Real myAbs(Real x) := y <-> (x < 0 & y = -(x)) | (x >= 0 & y = x);
        | End.
        | Problem myAbs(-1) = 1 End.
        |End.
        |""".stripMargin
    val prog = parse(input)

    // Note this is only equal to InterpretedSymbols.absF because the
    // program's (implicit) definition is syntactically equivalent
    prog.expandedModel shouldBe Equal(FuncOf(InterpretedSymbols.absF.copy(name="myAbs"),
      Neg(Number(1))), Number(1))
  }

  it should "parse implicit ODE definitions correctly" in {
    val input =
      """ArchiveEntry "entry1"
        | Definitions
        |  implicit Real myExp(Real x) :=' {{x:=0;myExp:=1;}; {x'=1,myExp'=myExp}};
        | End.
        | Problem myExp(0) = 1 End.
        |End.
        |""".stripMargin
    val prog = parse(input)

    // Note this is only equal to InterpretedSymbols.expF because the
    // program's (implicit) definition is syntactically equivalent
    prog.expandedModel shouldBe Equal(FuncOf(InterpretedSymbols.expF, Number(0)), Number(1))
  }

  "KYXPrettyPrinter" should "print interpretations" in {
    val input =
      """ArchiveEntry "entry1"
        | Problem myAbs<<(._0 < 0 & . = -(._0)) | (._0 >= 0 & . = ._0)>>(-1) = 1 End.
        |End.
        |""".stripMargin
    val prog = parse(input)

    val printer = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))

    val printed = printer(prog)
    val prog2 = parse(printed)

    prog2.model shouldBe prog.model
  }

  "throwaway" should "fail" in withMathematica { _ =>

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

  "differential defs" should "prove exp differential axiom" in withMathematica { _ =>
    import InterpretedSymbols.expF

    val diffAx = ImplicitDiffAxiom.deriveDiffAxiom(List(expF)).head

    val prob = Equal(Differential(FuncOf(expF,"x".asVariable)),
                      Times(FuncOf(expF,"x".asVariable),Differential("x".asVariable)))
    val pvble = proveBy(prob,
      useAt(diffAx)(1)
    )

    pvble shouldBe 'proved
  }

  it should "prove exp always positive in dL" in {
    val problem = Greater(FuncOf(InterpretedSymbols.expF,"x".asVariable), Number(0))

    val pvble = proveBy(problem,
      skip //TODO
    )

    pvble shouldBe 'proved
  }

  it should "prove simple trig lemmas in dL" in withMathematica { _ =>
    import InterpretedSymbols.{sinF, cosF}

    println(sinF)

    val prob = Equal(Plus(Power(FuncOf(sinF,"x".asVariable),Number(2)),
                          Power(FuncOf(cosF,"x".asVariable),Number(2))),
                      Number(1))
    val pvble = proveBy(prob,
      abbrvAll(FuncOf(sinF,"x".asVariable),None)
      & abbrvAll(FuncOf(cosF,"x".asVariable),None)
      & useAt(ElidingProvable(Provable.implicitFuncAxiom(sinF)))(-1)
      & useAt(ElidingProvable(Provable.implicitFuncAxiom(cosF)))(-2)
      //TODO
    )

    pvble shouldBe 'proved
  }

  it should "prove sin differential axiom" in {
    import InterpretedSymbols.{sinF,cosF}
    val prob = Equal(Differential(FuncOf(sinF,"x".asVariable)),
      Times(FuncOf(cosF,"x".asVariable),Differential("x".asVariable)))
    val pvble = proveBy(prob, skip
      //TODO
    )

    pvble shouldBe 'proved
  }

  "kyx2mathematica" should "convert special implicit functions to Mathematica" in withMathematica { _ =>
    import InterpretedSymbols.expF

    println(Parser.parser.getClass.getSimpleName)

    val pr = proveBy(Equal(
      Times(FuncOf(expF,Number(-1)),FuncOf(expF,Number(1))),
      Number(1)), QE)

    pr shouldBe 'proved
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
