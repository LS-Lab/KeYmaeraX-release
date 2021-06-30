/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.ext

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.tools.qe.{BinaryMathOpSpec, LiteralMathOpSpec, MathematicaOpSpec, NaryMathOpSpec, UnaryMathOpSpec}
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec.{int, symbol}

/** Extended Mathematica operator specifications for non-soundness critical tools. */
object ExtMathematicaOpSpec {

  //<editor-fold desc="Literals">

  def generatedParameters: LiteralMathOpSpec = LiteralMathOpSpec(symbol("GeneratedParameters"))

  def monomialOrder: LiteralMathOpSpec = LiteralMathOpSpec(symbol("MonomialOrder"))

  def degreeReverseLexicographic: LiteralMathOpSpec = LiteralMathOpSpec(symbol("DegreeReverseLexicographic"))

  def coefficientDomain: LiteralMathOpSpec = LiteralMathOpSpec(symbol("CoefficientDomain"))

  def rationals: LiteralMathOpSpec = LiteralMathOpSpec(symbol("Rationals"))

  def homeDirectory: LiteralMathOpSpec = LiteralMathOpSpec(symbol("$HomeDirectory"))

  def path: LiteralMathOpSpec = LiteralMathOpSpec(symbol("$Path"))

  def infinity: Expr = applyFunc(symbol("DirectedInfinity"))(MathematicaOpSpec.int(1))

  //</editor-fold>

  //<editor-fold desc="Basic datastructures and operations">

  def function: NaryMathOpSpec = NaryMathOpSpec(symbol("Function"))

  def map: NaryMathOpSpec = NaryMathOpSpec(symbol("Map"))

  def set: NaryMathOpSpec = NaryMathOpSpec(symbol("Set"))

  def setDelayed: NaryMathOpSpec = NaryMathOpSpec(symbol("SetDelayed"))

  def replaceAll: NaryMathOpSpec = NaryMathOpSpec(symbol("ReplaceAll"))

  def nestList: NaryMathOpSpec = NaryMathOpSpec(symbol("NestList"))

  def compoundExpression: NaryMathOpSpec = NaryMathOpSpec(symbol("CompoundExpression"))

  def first: NaryMathOpSpec = NaryMathOpSpec(symbol("First"))

  def appendTo: BinaryMathOpSpec = BinaryMathOpSpec(symbol("AppendTo"))

  def fileNameJoin: UnaryMathOpSpec = UnaryMathOpSpec(symbol("FileNameJoin"))

  def setDirectory: UnaryMathOpSpec = UnaryMathOpSpec(symbol("SetDirectory"))

  def needs: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Needs"))

  def applyFunc(fn: Expr): NaryMathOpSpec = NaryMathOpSpec(fn)

  def quiet: NaryMathOpSpec = NaryMathOpSpec(symbol("Quiet"))

  def slot: UnaryMathOpSpec = UnaryMathOpSpec(symbol("Slot"))

  def placeholder: Expr = slot(int(1))

  def mwhile: BinaryMathOpSpec = BinaryMathOpSpec(symbol("While"))

  def part: BinaryMathOpSpec = BinaryMathOpSpec(symbol("Part"))

  def length: UnaryMathOpSpec = UnaryMathOpSpec(symbol("Length"))

  //</editor-fold>

  //<editor-fold desc="Arithmetic">

  def findInstance: NaryMathOpSpec = NaryMathOpSpec(symbol("FindInstance"))

  def solve: NaryMathOpSpec = NaryMathOpSpec(symbol("Solve"))

  def fullSimplify: BinaryMathOpSpec = BinaryMathOpSpec(symbol("FullSimplify"))

  def polynomialQuotientRemainder: NaryMathOpSpec = NaryMathOpSpec(symbol("PolynomialQuotientRemainder"))

  def polynomialReduce: NaryMathOpSpec = NaryMathOpSpec(symbol("PolynomialReduce"))

  def groebnerBasis: NaryMathOpSpec = NaryMathOpSpec(symbol("GroebnerBasis"))

  def n: NaryMathOpSpec = NaryMathOpSpec(symbol("N"))

  def nmaximize: BinaryMathOpSpec = BinaryMathOpSpec(symbol("NMaximize"))

  //</editor-fold>

  //<editor-fold desc="Differential equation operations">

  def derivative: UnaryMathOpSpec = UnaryMathOpSpec(symbol("Derivative"))

  def primed: UnaryMathOpSpec = UnaryMathOpSpec(derivative(new Expr(1)))

  def dx(diffSymbol: Expr): UnaryMathOpSpec = UnaryMathOpSpec(diffSymbol)

  def dsolve: NaryMathOpSpec = NaryMathOpSpec(symbol("DSolve"))

  def d: BinaryMathOpSpec = BinaryMathOpSpec(symbol("D"))

  def dsolveAsymptoticApproximation: NaryMathOpSpec = NaryMathOpSpec(symbol("AsymptoticDSolveValue"))

  //</editor-fold>

}
