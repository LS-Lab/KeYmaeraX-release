/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.macros.{Axiom, AxiomDisplayInfo, AxiomInfo, DifferentialAxiomInfo, DisplayInfo, SimpleDisplayInfo}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement
import org.scalatest.LoneElement._
import org.scalatest.time.SpanSugar._
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, SlowTest, TodoTest}

import scala.collection.immutable._
import scala.language.postfixOps
import scala.reflect.io.File

/**
 * Tests for implicit function definitions & the involved substitutions.
 * @author James Gallicchio
 */
class ImplicitFunctionTests extends TacticTestBase {


  """
  Axiom "exp' derive exp"
  (exp(f(||)))' = f(||)' * exp(f(||))
  End.

  sqrt(2)=a <-> a^2 = 2


  ----
  \forall x \exists e exp(e,x)
  """

  "chase" should "use registered implicit differentials" in withMathematica { _ =>
    val exp = "e(x)".asTerm.asInstanceOf[FuncOf]
    val diff = "e(x)*(x)'".asTerm
    AxIndex.implFuncDiffs(Function("e", None, Real, Real)) =
      DifferentialAxiomInfo(
        funcName = "e",
        funcOf = exp,
        diff = diff,
        theRecursor = (1::Nil)::Nil
      )
    /* (e(x))' = e(x) * (x)' */
    val fml = "[y':=1;](e(y))' = e(y)*y'".asFormula
    val proof = proveBy(fml, chase(1,1::0::Nil) & chase(1) & QE)
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
  }

  "examples" should "allow arithmetic over implicit functions" in withMathematica { _ =>
    val arith1 = "exp(x) > 1".asFormula
    val arith2 = "sin(x)^2 + cos(x)^2 = 1".asFormula

    val pr1 = proveBy(arith1, skip)
    val pr2 = proveBy(arith2, skip)
    // Ideally: prove by QE

    println(pr1)
    println(pr2)
  }

  it should "work under assignments and nesting" in withMathematica { _ =>
    val fml = "x =1 -> [x := exp(exp(x)); x:=1; ++ x:= exp(x); ] x > 0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by ODE(1), dI('full)(1), etc.

    println(pr)
  }

  it should "be usable as a loop invariant" in withMathematica { _ =>
    val fml = "x = 0 -> [ {x := x + 1;}* ] exp(x) >= 1".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove using loop with loop invariants like x>=0 or exp(x)>=1

    println(pr)
  }

  it should "work with DI (1)" in withMathematica { _ =>
    val fml = "x =1 -> [{x' = exp(x)}] x > 0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    println(pr)
  }

  it should "work with DI (2)" in withMathematica { _ =>
    val fml = "x>=0&y>=0&z>=0 -> [{x' = exp(y), y' = exp(z), z'=1}] x+y+z>=0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    println(pr)
  }

  it should "work with DI (3)" in withMathematica { _ =>
    val fml = "x=5 -> [{x' = sin(x) + 1}] x>=0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by dI('full)(1), etc.

    println(pr)
  }

  it should "prove an exponential solution" in withMathematica { _ =>
    val fml = "x=x0 & t=0 -> [{x'=x, t' =1}] x = x0*exp(t)".asFormula
    val pr = proveBy(fml, skip)
    // may be provable using ODE(1) or dbx

    println(pr)
  }

  it should "prove a trig solution" in withMathematica { _ =>
    val fml = "c=1 & s = 0 & t=0 -> [{c'=-s, s'=c, t' =1}] (c=cos(t) & s = sin(t))".asFormula
    val pr = proveBy(fml, skip)
    // may be provable using ODE(1) or dbx

    println(pr)
  }

  it should "model a pendulum" in withMathematica { _ =>
    val fml = "a > 0 & b > 0 & x1 = 1 & x2 = 1 -> [{x1' = x2, x2'= -a*sin(x1) - b*x2}] a*(1-cos(x1))+1/2*x2^2 <= 1/2".asFormula
    val pr = proveBy(fml, skip)
    // end goal: prove something like this or more

    println(pr)
  }

}
