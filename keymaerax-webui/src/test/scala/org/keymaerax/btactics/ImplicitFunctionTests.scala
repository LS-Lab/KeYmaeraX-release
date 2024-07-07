/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.Configuration
import org.keymaerax.bellerophon.ReflectiveExpressionBuilder
import org.keymaerax.bellerophon.parser.{BellePrettyPrinter, DLBelleParser}
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.core._
import org.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import org.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import org.keymaerax.parser.StringConverter._
import org.keymaerax.parser.{
  DLArchiveParser,
  InterpretedSymbols,
  KeYmaeraXArchivePrinter,
  KeYmaeraXPrettyPrinter,
  Parser,
  PrettierPrintFormatProvider,
}
import org.keymaerax.tagobjects.TodoTest
import org.scalatest.LoneElement.convertToCollectionLoneElementWrapper

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Tests for implicit function definitions & the involved substitutions.
 * @author
 *   James Gallicchio
 */
class ImplicitFunctionTests extends TacticTestBase {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
  private val parser = new DLArchiveParser(
    new DLBelleParser(BellePrettyPrinter, ReflectiveExpressionBuilder(_, _, Some(FixedGenerator(List.empty)), _))
  )

  private def parse(input: String) = parser.parse(input).loneElement

  private def renBuiltin(builtin: Function, repl: String): Function = {
    val renBuiltinExp = ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
          case BaseVariable(vn, vi, _) =>
            if (vn == builtin.name && vi == builtin.index) Right(BaseVariable(repl, builtin.index)) else Left(None)
          case _ => Left(None)
        }
      },
      builtin.interp.get,
    )
    builtin.copy(name = repl, interp = renBuiltinExp)
  }

  "DLArchiveParser" should "parse built-in interpreted functions correctly" in {
    val input = """ArchiveEntry "entry1"
                  | Definitions import kyx.math.abs; End.
                  | Problem abs(-1) = 1 End.
                  |End.
                  |""".stripMargin
    val prog = parse(input)

    prog.model shouldBe Equal(FuncOf(InterpretedSymbols.absF, Neg(Number(1))), Number(1))
  }

  it should "parse inline function interps correctly" in {
    val input = """ArchiveEntry "entry1"
                  | Definitions Real myAbs<<._1 < 0 & ._0 = -(._1) | ._1 >= 0 & ._0 = ._1>>(Real x); End.
                  | Problem myAbs(-1) = 1 End.
                  |End.
                  |""".stripMargin
    val prog = parse(input)

    prog.model shouldBe Equal(FuncOf(renBuiltin(InterpretedSymbols.absF, "myAbs"), Neg(Number(1))), Number(1))
  }

  it should "parse implicit ODE definitions correctly" in {
    val input = """ArchiveEntry "entry1"
                  | Definitions
                  |  implicit Real myExp(Real t) = {{t:=0;myExp:=1;}; {t'=1,myExp'=myExp}};
                  | End.
                  | Problem myExp(0) = 1 End.
                  |End.
                  |""".stripMargin
    val prog = parse(input)

    prog.expandedModel shouldBe Equal(FuncOf(renBuiltin(InterpretedSymbols.expF, "myExp"), Number(0)), Number(1))
  }

  "Archive printer" should "print interpretations" in {
    val input = """ArchiveEntry "entry1"
                  | Definitions Real myAbs<<(._1 < 0 & ._0 = -(._1)) | (._1 >= 0 & ._0 = ._1)>>(Real x); End.
                  | Problem myAbs(-1) = 1 End.
                  |End.
                  |""".stripMargin
    val prog = parse(input)

    val printer = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))

    val printed = printer(prog)
    val prog2 = parse(printed)

    prog2.model shouldBe prog.model
  }

  it should "print from implicitly defined interpretation" in {
    val input = """ArchiveEntry "entry1"
                  | Definitions
                  |  implicit Real myExp(Real t) = {{t:=0;myExp:=1;}; {t'=1,myExp'=myExp}};
                  | End.
                  | Problem myExp(0) = 1 End.
                  |End.
                  |""".stripMargin
    val prog = parse(input)

    val printer = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))

    val printed = printer(prog)
    val prog2 = parse(printed)

    prog2.model shouldBe prog.model
  }

  "differential defs" should "prove exp differential axiom" in
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      withMathematica { _ =>
        import InterpretedSymbols.expF

        val diffAx = ImplicitAx.deriveDiffAxiom(List(expF)).head

        val prob = Equal(
          Differential(FuncOf(expF, "x".asVariable)),
          Times(FuncOf(expF, "x".asVariable), Differential("x".asVariable)),
        )

        proveBy(prob, byUS(diffAx)) shouldBe Symbol("proved")
      }
    }

  it should "prove exp always positive in dL" in
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      withMathematica { _ =>
        val problem = Greater(FuncOf(InterpretedSymbols.expF, "x".asVariable), Number(0))
        proveBy(problem, QE) shouldBe Symbol("proved")
      }
    }

  it should "prove sin differential axiom" in withMathematica { _ =>
    import InterpretedSymbols.{cosF, sinF}
    val prob = Equal(
      Differential(FuncOf(sinF, "x".asVariable)),
      Times(FuncOf(cosF, "x".asVariable), Differential("x".asVariable)),
    )
    proveBy(prob, byUS(ImplicitAx.deriveDiffAxiom(List(sinF, cosF)).head)) shouldBe Symbol("proved")
  }

  "kyx2mathematica" should "convert special implicit functions to Mathematica" in
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      withMathematica { _ =>
        import InterpretedSymbols.expF

        val pr = proveBy(Equal(Times(FuncOf(expF, Number(-1)), FuncOf(expF, Number(1))), Number(1)), QE)

        pr shouldBe Symbol("proved")
      }
    }

  "QE" should "not abbreviate interpreted functions known to Mathematica" in
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      withMathematica { _ => proveBy("exp(x)>0".asFormula, QE) shouldBe Symbol("proved") }
    }

  // TODO: substitute uninterpreted for interpreted functions in these tests
  "examples" should "FEATURE_REQUEST: work under assignments and nesting" taggedAs TodoTest in withMathematica { _ =>
    val fml = "x =1 -> [x := exp(exp(x)); x:=1; ++ x:= exp(x); ] x > 0".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove by ODE(1), dI('full)(1), etc.

    pr shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: be usable as a loop invariant" taggedAs TodoTest in withMathematica { _ =>
    val fml = "x = 0 -> [ {x := x + 1;}* ] exp(x) >= 1".asFormula
    val pr = proveBy(fml, skip)
    // Ideally: prove using loop with loop invariants like x>=0 or exp(x)>=1

    pr shouldBe Symbol("proved")
  }

  it should "work with DI (1)" in withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
    withMathematica { _ => proveBy("x =1 ==> [{x' = exp(x)}] x > 0".asSequent, dI()(1)) shouldBe Symbol("proved") }
  }

  it should "work with DI (2)" in withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
    withMathematica { _ =>
      val s = "x>=0&y>=0&z>=0 ==> [{x' = exp(y), y' = exp(z), z'=1}] x+y+z>=0".asSequent
      proveBy(s, dI()(1)) shouldBe Symbol("proved")
    }
  }

  it should "work with DI (3)" in withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
    withMathematica { _ =>
      val s = "x=5 ==> [{x' = sin(x) + 1}] x>=0".asSequent
      proveBy(s, dI()(1)) shouldBe Symbol("proved")
    }
  }

  it should "FEATURE_REQUEST: model a pendulum" taggedAs TodoTest in withMathematica { _ =>
    val fml =
      "a > 0 & b > 0 & x1 = 1 & x2 = 1 -> [{x1' = x2, x2'= -a*sin(x1) - b*x2}] a*(1-cos(x1))+1/2*x2^2 <= 1/2".asFormula
    val pr = proveBy(fml, skip)
    // end goal: prove something like this or more

    pr shouldBe Symbol("proved")
  }
}
