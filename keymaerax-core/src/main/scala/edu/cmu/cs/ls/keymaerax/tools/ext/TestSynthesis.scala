/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.btactics.ModelPlex
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.{KExpr, MExpr}
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec

/**
  * Synthesize test case configurations from ModelPlex formulas.
  * Requires Mathematica.
  *
  * Created by smitsch on 12/6/16.
  *
  * @author Stefan Mitsch
  */
class TestSynthesis(mathematicaTool: Mathematica) extends BaseKeYmaeraMathematicaBridge[Either[KExpr,NamedSymbol]](
  mathematicaTool.link, CEXK2MConverter, CEXM2KConverter) {

  /** Synthesize test configurations of both initial values and expected outcomes satisfying formula `fml`. The values
    * are numeric approximations (avoids Mathematica precision limit issues). */
  def synthesizeTestConfig(fml: Formula, amount: Int = 1, timeout: Option[Int] = None,
                           safetyMargin: Option[(Number,Number)] = None): List[Map[Term, Term]] = {
    val safetyMetric = safetyMargin match {
      case Some((lower, upper)) =>
        val metric = safetyMarginTerm(fml)
        And(LessEqual(lower, metric), LessEqual(metric, upper))
      case None => True
    }

    val cmd = findInstance(And(fml, safetyMetric), amount, timeout)
    println("Execute in Mathematica to search for sunshine test case values (initial+expected): " + cmd)

    def toConfigMap(fml: Formula): Map[Term, Term] = FormulaTools.conjuncts(fml).map({
      case Equal(name: Variable, value) => name -> value
      //case Equal(name: DifferentialSymbol, value) => name -> value
      case Equal(fn: FuncOf, value) => fn -> value
    }).toMap

    run(cmd) match {
      case (_, Left(fml: And)) => toConfigMap(fml) :: Nil
      case (_, Left(fml: Or)) => FormulaTools.disjuncts(fml).map(toConfigMap)
      case (_, Left(False)) => Nil
    }
  }

  /** Synthesize a safety margin check, 0 is the boundary between safe and unsafe, positive values indicate unsafety, negative values safety. */
  def synthesizeSafetyMarginCheck(fml: Formula, vals: Map[Term, Term]): Number = {
    val metricExpr = k2m.convert(Left(safetyMarginTerm(fml)))
    val valsExpr = MathematicaOpSpec.list(vals.map({
      case (k,v) => ExtMathematicaOpSpec.set(
          k2m.convert(Left(k)),
          k2m.convert(Left(v))
        )
      }).toArray:_*)
    val cmd = MathematicaOpSpec.module(valsExpr, metricExpr)
    println("Execute in Mathematica to compute safety margin of test case: " + cmd)
    run(cmd) match {
      case (_, Left(t: Number)) => t
      case (_, Left(Divide(Number(a), Number(b)))) => Number(a/b)
    }
  }

  /** Computes the maximum safety range of fml. */
  def getSafetyRange(fml: Formula): (Number, Number) = {
    val metricExpr = k2m.convert(Left(safetyMarginTerm(fml)))
    val symbols = StaticSemantics.symbols(fml)
    val symbolsExpr = MathematicaOpSpec.list(symbols.map(s => k2m.convert(Right(s))).toArray:_*)
    // minimize for compliant test cases
    //@todo second argument would give values for "safest" test case
    val cmd = ExtMathematicaOpSpec.first(ExtMathematicaOpSpec.nmaximize(metricExpr, symbolsExpr))
    println("Execute in Mathematica to compute safety range: " + cmd)
    run(cmd) match {
      case (_, Left(upper: Number)) => (Number(0), upper)
      case (_, Left(Divide(Number(a), Number(b)))) => (Number(0), Number(a/b))
    }
  }

  /** Safety margin (negated so that positive values mean good). */
  private def safetyMarginTerm(fml: Formula): Term = Neg(ModelPlex.toMetric(fml) match {
    case LessEqual(m, _) => m
    case Less(m, _) => m
  })

  /** Uses FindInstance to search for values that satisfy the formula `fml`. `amount` indicates how many sets. */
  private def findInstance(fml: Formula, amount: Int, timeout: Option[Int]): MExpr = {
    val fi =
      ExtMathematicaOpSpec.findInstance(
        k2m.convert(Left(fml)),
        MathematicaOpSpec.list(
          StaticSemantics.symbols(fml).filter({ case Function(_, _, _, _, interpreted) => !interpreted case _ => true}).
            toList.sorted.map(s => CEXK2MConverter.convert(Right(s))):_*),
        MathematicaOpSpec.reals.op,
        k2m(Left(Number(amount)))
      )
    timeout match {
      case Some(to) => MathematicaOpSpec.timeConstrained(fi, k2m(Left(Number(to))))
      case None => fi
    }
  }

}
