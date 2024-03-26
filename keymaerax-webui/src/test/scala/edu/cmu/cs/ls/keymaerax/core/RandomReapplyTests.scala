/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.tagobjects.{SlowTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, CoverageTest}
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

import scala.collection.immutable

/**
 * Tests reapply function of expression data structures for identity after deep copy. Performance test if printing were
 * turned off.
 *
 * @todo
 *   add a test that reapplies with new random formulas/terms as arguments
 * @author
 *   Andre Platzer
 */
@CoverageTest @CheckinTest
class RandomReapplyTests extends AnyFlatSpec with Matchers {
  val randomTrials = 4000
  val randomComplexity = 30
  val rand = new RandomFormula()

  "Crafted expression reapply from ScalaDoc" should "work for UnaryCompositeTerm" in {
    Neg(Number(77)).reapply(Number(99)) shouldBe Neg(Number(99))
    Neg(Variable("x")).reapply(Plus(Number(42), Number(69))) shouldBe Neg(Plus(Number(42), Number(69)))
  }
  it should "work for BinaryCompositeTerm" in {
    Times(Number(7), Variable("v")).reapply(Variable("a"), Number(99)) shouldBe Times(Variable("a"), Number(99))
  }
  it should "work for ComparisonFormula" in {
    GreaterEqual(Number(7), Variable("v")).reapply(Variable("a"), Number(99)) shouldBe
      GreaterEqual(Variable("a"), Number(99))
  }
  it should "work for UnaryCompositeFormula" in {
    Not(GreaterEqual(Variable("x"), Number(0))).reapply(NotEqual(Number(7), Number(9))) shouldBe
      Not(NotEqual(Number(7), Number(9)))
    Not(True).reapply(False) shouldBe Not(False)
  }
  it should "work for BinaryCompositeFormula" in {
    Or(GreaterEqual(Variable("x"), Number(0)), False).reapply(True, NotEqual(Number(7), Number(9))) shouldBe
      Or(True, NotEqual(Number(7), Number(9)))
  }
  it should "work for Quantified" in {
    Forall(immutable.Seq(Variable("x")), PredOf(Function("p", None, Real, Bool), Variable("x")))
      .reapply(immutable.Seq(Variable("y")), PredOf(Function("q", None, Real, Bool), Variable("y"))) shouldBe
      (Forall(immutable.Seq(Variable("y")), PredOf(Function("q", None, Real, Bool), Variable("y"))))
  }
  it should "work for Modality" in {
    Box(ProgramConst("b"), Less(Variable("z"), Number(0))).reapply(
      Compose(ProgramConst("a"), AtomicODE(DifferentialSymbol(Variable("x")), Number(5))),
      GreaterEqual(Variable("x"), Number(2)),
    ) shouldBe Box(
      Compose(ProgramConst("a"), AtomicODE(DifferentialSymbol(Variable("x")), Number(5))),
      GreaterEqual(Variable("x"), Number(2)),
    )
  }
  it should "work for UnaryCompositeProgram" in {
    Loop(ProgramConst("alpha")).reapply(Assign(Variable("x"), Number(42))) shouldBe
      Loop(Assign(Variable("x"), Number(42)))
  }
  it should "work for BinaryCompositeProgram" in {
    Choice(ProgramConst("alpha"), ProgramConst("beta")).reapply(ProgramConst("gamma"), ProgramConst("delta")) shouldBe
      Choice(ProgramConst("gamma"), ProgramConst("delta"))
  }

  "Expression reapply" should // "reapply random formulas identically (checkin)" taggedAs(CheckinTest) in {test(10)}
    // it should "reapply random formulas identically (summary)" taggedAs(SummaryTest) in {test(50)}
    "reapply random formulas identically (usual)" taggedAs UsualTest in { test(1000, 10) }
  it should "reparse pretty-prints of random formulas (slow)" taggedAs SlowTest in { test(randomTrials, 20) }
  it should "reparse pretty-prints of random formulas (prints)" in { testPrint(100, 20) }

  private def test(randomTrials: Int = randomTrials, randomComplexity: Int = randomComplexity) =
    for (i <- 1 to randomTrials) {
      val e = rand.nextFormula(randomComplexity)
      val r = reapplied(e)
      e shouldBe r
    }

  private def testPrint(randomTrials: Int = randomTrials, randomComplexity: Int = randomComplexity) = {
    var pp: Expression => String = PrettyPrinter
    for (i <- 1 to randomTrials) {
      val e = rand.nextFormula(randomComplexity)
      val r = reapplied(e)
      e shouldBe r
    }
    pp = KeYmaeraXPrettyPrinter
    for (i <- 1 to randomTrials) {
      val e = rand.nextFormula(randomComplexity)
      val r = reapplied(e)
      e shouldBe r
    }
  }

  // recursive reapplied call for deep copy

  def reapplied(e: Expression): Expression = e match {
    case t: Term => reapplied(t)
    case f: Formula => reapplied(f)
    case p: Program => reapplied(p)
  }

  def reapplied(term: Term): Term = term match {
    case n: Number => n
    case xp: DifferentialSymbol => DifferentialSymbol(reapplied(xp.x).asInstanceOf[Variable])
    case x: BaseVariable => Variable(x.name, x.index, x.sort)
    case FuncOf(f, t) => FuncOf(f, reapplied(t))
    case f: UnitFunctional => UnitFunctional(f.name, f.space, f.sort)
    case d: DotTerm => d
    case Nothing => Nothing
    // homomorphic cases
    case f: UnaryCompositeTerm => f.reapply(reapplied(f.child))
    case f: BinaryCompositeTerm => f.reapply(reapplied(f.left), reapplied(f.right))
    case _ => throw new IllegalArgumentException("reapplied of term " + term + " of class " + term.getClass)
  }

  def reapplied(formula: Formula): Formula = formula match {
    // base cases
    case True => True
    case False => False
    case DotFormula => DotFormula
    case PredOf(p, t) => PredOf(p, reapplied(t))
    case PredicationalOf(c, t) => PredicationalOf(c, reapplied(t))
    case f: UnitPredicational => UnitPredicational(f.name, f.space)
    // pseudo-homomorphic cases
    case f: ComparisonFormula => f.reapply(reapplied(f.left), reapplied(f.right))
    // homomorphic cases
    case f: UnaryCompositeFormula => f.reapply(reapplied(f.child))
    case f: BinaryCompositeFormula => f.reapply(reapplied(f.left), reapplied(f.right))
    case f: Quantified => f.reapply(f.vars, reapplied(f.child))
    case f: Modal => f.reapply(reapplied(f.program), reapplied(f.child))
    case _ =>
      throw new IllegalArgumentException("reapplied position of formula " + formula + " of class " + formula.getClass)
  }

  def reapplied(program: Program): Program = program match {
    case Assign(x, t) => Assign(reapplied(x).asInstanceOf[Variable], reapplied(t))
    // case DiffAssign(x,t)   => DiffAssign(reapplied(x).asInstanceOf[DifferentialSymbol], reapplied(t))
    case AssignAny(x) => AssignAny(reapplied(x).asInstanceOf[Variable])
    case Test(f) => Test(reapplied(f))
    case ProgramConst(a, s) => ProgramConst(a, s)

    case ODESystem(ode, h) => ODESystem(reapplied(ode).asInstanceOf[DifferentialProgram], reapplied(h))
    case AtomicODE(xp, t) => AtomicODE(reapplied(xp).asInstanceOf[DifferentialSymbol], reapplied(t))
    case DifferentialProduct(a, b) => DifferentialProduct(
        reapplied(a).asInstanceOf[DifferentialProgram],
        reapplied(b).asInstanceOf[DifferentialProgram],
      )
    case DifferentialProgramConst(a, s) => DifferentialProgramConst(a, s)

    // homomorphic cases
    case f: UnaryCompositeProgram => f.reapply(reapplied(f.child))
    case f: BinaryCompositeProgram => f.reapply(reapplied(f.left), reapplied(f.right))
    case _ => throw new IllegalArgumentException("reapplied of program " + program + " of class " + program.getClass)
  }
}
