/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, StaticSemanticsTools}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}

import scala.collection.immutable._
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}

/**
 * Tests reapply function of expression data structures for identity after deep copy.
 * Performance test if printing were turned off.
 * @author Andre Platzer
 */
class RandomReapplyTests extends FlatSpec with Matchers {
  val randomTrials = 40000
  val randomComplexity = 6
  val rand = new RandomFormula()


  "Expression reapply" should "reapply random formulas identically (checkin)" taggedAs(CheckinTest) in {test(10)}
  it should "reapply random formulas identically (summary)" taggedAs(SummaryTest) in {test(50)}
  it should "reapply random formulas identically (usual)" taggedAs(UsualTest) in {test(1000,10)}
  it should "reparse pretty-prints of random formulas (slow)" taggedAs(SlowTest) in {test(randomTrials,20)}

  private def test(randomTrials: Int= randomTrials, randomComplexity: Int = randomComplexity) =
    for (i <- 1 to randomTrials) {
      val e = rand.nextFormula(randomComplexity)
      //println("Random in: " + e)
      val r = reapplied(e)
      //println("Reapplied: " + r)
      e shouldBe r
    }

  // recursive reapplied call for deep copy

  def reapplied(term: Term): Term = term match {
    case n:Number => n
    case x:Variable => Variable(x.name, x.index, x.sort)
    case xp:DifferentialSymbol => DifferentialSymbol(reapplied(xp.x).asInstanceOf[Variable])
    case FuncOf(f,t)     => FuncOf(f, reapplied(t))
    // homomorphic cases
    case f:UnaryCompositeTerm  => f.reapply(reapplied(f.child))
    case f:BinaryCompositeTerm => f.reapply(reapplied(f.left), reapplied(f.right))
    case _ => throw new IllegalArgumentException("reapplied of term " + term + " of class " + term.getClass)
  }

  def reapplied(formula: Formula): Formula = formula match {
    // base cases
    case True => True
    case False => False
    case PredOf(p,t)          => PredOf(p, reapplied(t))
    case PredicationalOf(c,t) => PredicationalOf(c, reapplied(t))
    // pseudo-homomorphic cases
    case f:ComparisonFormula  => f.reapply(reapplied(f.left), reapplied(f.right))
    // homomorphic cases
    case f:UnaryCompositeFormula  => f.reapply(reapplied(f.child))
    case f:BinaryCompositeFormula => f.reapply(reapplied(f.left), reapplied(f.right))
    case f:Quantified             => f.reapply(f.vars, reapplied(f.child))
    case f:Modal                  => f.reapply(reapplied(f.program), reapplied(f.child))
    case _ => throw new IllegalArgumentException("reapplied position of formula " + formula + " of class " + formula.getClass)
  }

  def reapplied(program: Program): Program = program match {
    case Assign(x,t)       => Assign(reapplied(x).asInstanceOf[Variable], reapplied(t))
    case DiffAssign(x,t)   => DiffAssign(reapplied(x).asInstanceOf[DifferentialSymbol], reapplied(t))
    case AssignAny(x)      => AssignAny(reapplied(x).asInstanceOf[Variable])
    case Test(f)           => Test(reapplied(f))
    case ProgramConst(a)   => ProgramConst(a)

    case ODESystem(ode, h) => ODESystem(reapplied(ode).asInstanceOf[DifferentialProgram], reapplied(h))
    case AtomicODE(xp, t)  => AtomicODE(reapplied(xp).asInstanceOf[DifferentialSymbol], reapplied(t))
    case DifferentialProduct(a, b)  => DifferentialProduct(reapplied(a).asInstanceOf[DifferentialProgram], reapplied(b).asInstanceOf[DifferentialProgram])
    case DifferentialProgramConst(a) => DifferentialProgramConst(a)

    // homomorphic cases
    case f:UnaryCompositeProgram  => f.reapply(reapplied(f.child))
    case f:BinaryCompositeProgram => f.reapply(reapplied(f.left), reapplied(f.right))
    case _ => throw new IllegalArgumentException("reapplied of program " + program + " of class " + program.getClass)
  }
}
