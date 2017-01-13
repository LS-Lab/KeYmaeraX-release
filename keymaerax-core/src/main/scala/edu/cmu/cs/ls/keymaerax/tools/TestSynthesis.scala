/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.btactics.{FormulaTools, ModelPlex}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}

/**
  * Synthesize test case configurations from ModelPlex formulas.
  * Requires Mathematica.
  *
  * Created by smitsch on 12/6/16.
  *
  * @author Stefan Mitsch
  */
class TestSynthesis(mathematicaTool: Mathematica) extends BaseKeYmaeraMathematicaBridge[KExpr](mathematicaTool.link, CEXK2MConverter, CEXM2KConverter) {

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
      case (_, fml: And) => toConfigMap(fml) :: Nil
      case (_, fml: Or) => FormulaTools.disjuncts(fml).map(toConfigMap)
      case (_, False) => Nil
    }
  }

  /** Synthesize a safety margin check, 0 is the boundary between safe and unsafe, positive values indicate unsafety, negative values safety. */
  def synthesizeSafetyMarginCheck(fml: Formula, vals: Map[Term, Term]): Number = {
    val metricExpr = k2m.convert(safetyMarginTerm(fml))
    val valsExpr = new MExpr(MathematicaSymbols.LIST, vals.map({case (k,v) =>
      new MExpr(new MExpr(Expr.SYMBOL, "Set"), Array(k2m.convert(k), k2m.convert(v)))}).toArray)
    val cmd = new MExpr(new MExpr(Expr.SYMBOL, "Module"), Array(valsExpr, metricExpr))
    println("Execute in Mathematica to compute safety margin of test case: " + cmd)
    run(cmd) match {
      case (_, t: Number) => t
    }
  }

  private def numeric(e: MExpr): MExpr = new MExpr(new MExpr(Expr.SYMBOL, "N"), Array(e))

  private def safetyMarginTerm(fml: Formula): Term = ModelPlex.toMetric(fml) match {
    case LessEqual(m, _) => m
    case Less(m, _) => m
  }

  /** Uses FindInstance to search for values that satisfy the formula `fml`. `amount` indicates how many sets. */
  private def findInstance(fml: Formula, amount: Int, timeout: Option[Int]): MExpr = {
    val fi = numeric(new MExpr(new MExpr(Expr.SYMBOL,  "FindInstance"),
      Array(k2m.convert(fml),
        new MExpr(
          MathematicaSymbols.LIST,
          StaticSemantics.symbols(fml).filter({ case Function(_, _, _, _, interpreted) => !interpreted case _ => true}).
            toList.sorted.map(s => CEXK2MConverter.convert(s)).toArray),
        new MExpr(Expr.SYMBOL, "Reals"), k2m(Number(amount)))))

    timeout match {
      case Some(to) => new MExpr(new MExpr(Expr.SYMBOL,  "TimeConstrained"), Array(fi, k2m(Number(to))))
      case None => fi
    }
  }

}
