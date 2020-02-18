/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.ext

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.tools.qe.{BinaryMathOpSpec, LiteralMathOpSpec, NaryMathOpSpec, UnaryMathOpSpec}
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec.symbol

/** Extended Mathematica operator specifications for non-soundness critical tools. */
object ExtMathematicaOpSpec {

  //<editor-fold desc="Literals">

  val generatedParameters = LiteralMathOpSpec(symbol("GeneratedParameters"))

  val monomialOrder = LiteralMathOpSpec(symbol("MonomialOrder"))

  val degreeReverseLexicographic = LiteralMathOpSpec(symbol("DegreeReverseLexicographic"))

  val coefficientDomain = LiteralMathOpSpec(symbol("CoefficientDomain"))

  val rationals = LiteralMathOpSpec(symbol("Rationals"))

  val placeholder = LiteralMathOpSpec(symbol("#"))

  //</editor-fold>

  //<editor-fold desc="Basic datastructures and operations">

  val function = NaryMathOpSpec(symbol("Function"))

  val map = NaryMathOpSpec(symbol("Map"))

  val set = NaryMathOpSpec(symbol("Set"))

  val setDelayed = NaryMathOpSpec(symbol("SetDelayed"))

  val replaceAll = NaryMathOpSpec(symbol("ReplaceAll"))

  val module = NaryMathOpSpec(symbol("Module"))

  val nestList = NaryMathOpSpec(symbol("NestList"))

  val compoundExpression = NaryMathOpSpec(symbol("CompoundExpression"))

  val first = NaryMathOpSpec(symbol("First"))

  //</editor-fold>

  //<editor-fold desc="Arithmetic">

  val findInstance = NaryMathOpSpec(symbol("FindInstance"))

  val solve = NaryMathOpSpec(symbol("Solve"))

  val fullSimplify = BinaryMathOpSpec(symbol("FullSimplify"))

  val polynomialQuotientRemainder = NaryMathOpSpec(symbol("PolynomialQuotientRemainder"))

  val polynomialReduce = NaryMathOpSpec(symbol("PolynomialReduce"))

  val groebnerBasis = NaryMathOpSpec(symbol("GroebnerBasis"))

  val n = NaryMathOpSpec(symbol("N"))

  val nmaximize = BinaryMathOpSpec(symbol("NMaximize"))

  //</editor-fold>

  //<editor-fold desc="Differential equation operations">

  val derivative = UnaryMathOpSpec(symbol("Derivative"))

  val primed = UnaryMathOpSpec(derivative(new Expr(1)))

  def dx(diffSymbol: Expr): UnaryMathOpSpec = UnaryMathOpSpec(diffSymbol)

  val dsolve = NaryMathOpSpec(symbol("DSolve"))

  val d = BinaryMathOpSpec(symbol("D"))


  //</editor-fold>

}
