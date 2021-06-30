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

  "implicit fn axioms" should "substitute against an equality" in {
    val pvble = proveBy(
      GreaterEqual(FuncOf(InterpretedSymbols.absF,Variable("x")),Number(0)),
      cut(Equal(FuncOf(InterpretedSymbols.absF, Variable("x")),Variable("y")))
        & useAt(ElidingProvable(Provable.implicitFuncAxiom(InterpretedSymbols.absF)))(1,0::Nil)
    )

    val x = pvble.isProved && (Math.exp(10) > 0)

    x shouldBe true

    pvble shouldBe 'proved
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
    prog.expandedModel shouldBe Equal(FuncOf(InterpretedSymbols.absF, Neg(Number(1))), Number(1))
  }

  /*
  "chase" should "use registered implicit differentials" in {
    val fn = Function("e", None, Real, Real, interpreted = true)
    /* (e(x))' = e(x) * (x)' */
    AxIndex.implFuncDiffs(fn) =
      DifferentialAxiomInfo(
        funcName = "e",
        funcOf = FuncOf(fn, Variable("x")),
        diff = Times(FuncOf(fn, Variable("x")), Differential(Variable("x"))),
        theRecursor = (1::Nil)::Nil
      )
    val fml = markInterpreted(fn, "[y':=1;](e(y))' = e(y)*y'".asFormula)
    println(fml)
    val proof = proveBy(fml, chase(1,1::0::Nil) & chase(1) & byUS(Ax.equalReflexive))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
  }


  "DLparser" should "parse & register implicit function definitions" in {
    val input =
      """ArchiveEntry "entry1"
        | ProgramVariables Real y; End.
        | ImplicitDefinitions
        |  Real exp(Real x) ':= exp(x) * (x)';
        | End.
        | Problem [y':=1;](exp(y))' = exp(y)*y' End.
        |End.
        |""".stripMargin
    val prog = parse(input)
    val fml = markInterpreted(
      Function("exp", None, Real, Real, interpreted = true),
      prog.model.asInstanceOf[Formula])

    val proof = proveBy(fml, chase(1,1::0::Nil) & chase(1) & byUS(Ax.equalReflexive))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
  }

  "examples" should "allow arithmetic over implicit functions" in withMathematica { _ =>
    val input =
      """ArchiveEntry "entry1"
        | ProgramVariables Real y; End.
        | ImplicitDefinitions
        |   Real sin(Real x) ':= cos(x) * (x)';
        |   Real cos(Real x) ':= -sin(x) * (x)';
        | End.
        | Problem sin(y)^2 + cos(y)^2 = 1 -> [{y'=1}] sin(y)^2 + cos(y)^2 = 1 End.
        |End.
        |""".stripMargin
    val prog = parse(input)
    val fml = markInterpreted(
      Function("sin", None, Real, Real, interpreted = true),
      markInterpreted(
        Function("cos", None, Real, Real, interpreted = true),
        prog.model.asInstanceOf[Formula]))

    val proof = proveBy(fml, implyR(1) & dI()(1))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
  }

  it should "prove exp always positive by Mathematica" in withMathematica { _ =>
    // Assumes exp already in the map (hack)
    val fml = markInterpreted(
      Function("exp", None, Real, Real, interpreted = true),
      "exp(x) > 0 -> [{x'=1}] exp(x) > 0".asFormula)

    val proof = proveBy(fml, implyR(1))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
  }

  it should "prove exp always positive within dL" in withMathematica { _ =>
    // Assumes exp already in the map (hack)
    val fml = markInterpreted(
      Function("exp", None, Real, Real, interpreted = true),
      "exp(x) > 0 -> [{x'=1}] exp(x) > 0".asFormula)

    val proof = proveBy(fml, implyR(1) & dbx(Some("1".asTerm))(1))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
  }

  it should "work under assignments and nesting" in withMathematica { _ =>
    val fml = "x =1 -> [x := exp(exp(x)); x:=1; ++ x:= exp(x); ] x > 0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by ODE(1), dI('full)(1), etc.

    //println(pr)
  }

  it should "be usable as a loop invariant" in withMathematica { _ =>
    val fml = "x = 0 -> [ {x := x + 1;}* ] exp(x) >= 1".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove using loop with loop invariants like x>=0 or exp(x)>=1

    //println(pr)
  }

  it should "work with DI (1)" in withMathematica { _ =>
    val fml = "x =1 -> [{x' = exp(x)}] x > 0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    //println(pr)
  }

  it should "work with DI (2)" in withMathematica { _ =>
    val fml = "x>=0&y>=0&z>=0 -> [{x' = exp(y), y' = exp(z), z'=1}] x+y+z>=0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    //println(pr)
  }

  it should "work with DI (3)" in withMathematica { _ =>
    val fml = "x=5 -> [{x' = sin(x) + 1}] x>=0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    //println(pr)
  }

  it should "prove an exponential solution" in withMathematica { _ =>
    val fml = "x=x0 & t=0 -> [{x'=x, t' =1}] x = x0*exp(t)".asFormula
    val pr = proveBy(fml, dbx(Some("1".asTerm))(1))
    // may be provable using ODE(1) or dbx

    //println(pr)
  }

  it should "prove a trig solution" in withMathematica { _ =>
    val fml = "c=1 & s = 0 & t=0 -> [{c'=-s, s'=c, t' =1}] (c=cos(t) & s = sin(t))".asFormula
    val pr = proveBy(fml, skip)
    // may be provable using ODE(1) or dbx

    //println(pr)
  }

  it should "model a pendulum" in withMathematica { _ =>
    val fml = "a > 0 & b > 0 & x1 = 1 & x2 = 1 -> [{x1' = x2, x2'= -a*sin(x1) - b*x2}] a*(1-cos(x1))+1/2*x2^2 <= 1/2".asFormula
    val pr = proveBy(fml, skip)
    // end goal: prove something like this or more

    //println(pr)
  }
*/
}
