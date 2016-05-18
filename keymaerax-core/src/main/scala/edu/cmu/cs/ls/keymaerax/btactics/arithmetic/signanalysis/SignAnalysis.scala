/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis

import edu.cmu.cs.ls.keymaerax.core._

/**
  * Tactics for simplifying arithmetic sub-goals.
  *
  * @author Stefan Mitsch
  */
object SignAnalysis {

  object Sign extends Enumeration {
    type Sign = Value
    val Neg, Neg0, Zero, Pos0, Pos, Unknown = Value

    def plusConverse(s: Sign): Sign = s match {
      case Neg => Pos
      case Neg0 => Pos0
      case Zero => Zero
      case Pos0 => Neg0
      case Pos => Neg
    }

    def timesConverse(s: Sign): Sign = s match {
      case Zero => Unknown
      case Neg0 => Unknown
      case _ => s
    }

    def plus(l: Sign, r: Sign): Sign = (l,r) match {
      case (Zero,_) => r
      case (_,Zero) => l
      case (Unknown,_) => Unknown
      case (_,Unknown) => Unknown
      case (Neg,Neg) => Neg
      case (Neg,Neg0) => Neg
      case (Neg,Pos0) => Unknown
      case (Neg, Pos) => Unknown
      case (Neg0,Neg) => Neg
      case (Neg0,Neg0) => Neg0
      case (Neg0,Pos0) => Unknown
      case (Neg0,Pos) => Unknown
      case (Pos0,Neg) => Unknown
      case (Pos0,Neg0) => Unknown
      case (Pos0,Pos0) => Pos0
      case (Pos0,Pos) => Pos
      case (Pos,Neg) => Unknown
      case (Pos,Neg0) => Unknown
      case (Pos,Pos0) => Pos
      case (Pos,Pos) => Pos
    }

    def minus(l: Sign, r: Sign): Sign = plus(l, plusConverse(r))

    def times(l: Sign, r: Sign): Sign = (l,r) match {
      case (Zero,_) => Zero
      case (_,Zero) => Zero
      case (Unknown,_) => Unknown
      case (_,Unknown) => Unknown
      case (Neg,Neg) => Pos
      case (Neg,Neg0) => Pos0
      case (Neg,Pos0) => Neg0
      case (Neg, Pos) => Neg
      case (Neg0,Neg) => Pos0
      case (Neg0,Neg0) => Pos0
      case (Neg0,Pos0) => Neg0
      case (Neg0,Pos) => Neg0
      case (Pos0,Neg) => Neg0
      case (Pos0,Neg0) => Neg0
      case (Pos0,Pos0) => Pos0
      case (Pos0,Pos) => Pos0
      case (Pos,Neg) => Neg
      case (Pos,Neg0) => Neg0
      case (Pos,Pos0) => Pos0
      case (Pos,Pos) => Pos
    }

    def divide(l: Sign, r: Sign): Sign = (l,r) match {
      case (_, Neg0) => throw new Exception("(Potential) division by 0")
      case (_, Zero) => throw new Exception("Division by 0")
      case (_, Pos0) => throw new Exception("(Potential) division by 0")
      case _ => times(l, timesConverse(r))
    }

    def power(l: Sign, r: Int): Sign = l match {
      case _    if r == 0     => Pos
      case Zero if r != 0     => Zero
      case Neg  if r % 2 == 0 => Pos
      case Neg  if r % 2 != 0 => Neg
      case Neg0 if r % 2 == 0 => Pos0
      case Neg0 if r % 2 != 0 => Neg0
      case Pos0               => Pos0
      case Pos                => Pos
      case Unknown if r % 2 == 0 => Pos
      case Unknown if r % 2 != 0 => Unknown
    }

    def num(n: Number): Sign =
      if (n.value < 0) Neg
      else if (n.value == 0) Zero
      else if (n.value > 0) Pos
      else if (n.value <= 0) Neg0
      else /*if (n.value >= 0)*/ Pos0

    // need a second characterization: directionality, e.g., x<=m means x == '<=' (looking for upper bound)
    // find out in succedent formulas

    // first bootstrap known A>0 on the left
    // then bootstrap directionality on the right
    // then characterize remaining antecedent formulas into useful/useless/don'tknow

    // compute directionality in remaining antecedent formulas

    // analogy: interval arithmetic?

    // maybe feed into Prolog engine?

    // normalize formulas to < and <= and RHS == 0
    def seed(s: Sequent): Map[Term, Sign] = {
      s.ante.filter{ case c: ComparisonFormula => c.left.isInstanceOf[Number] || c.right.isInstanceOf[Number] }.map {
        case Less(l, Number(r))      if r <= 0 => l -> Neg
        case Less(l, Number(r))      if r > 0  => l -> Unknown
        case LessEqual(l, Number(r)) if r <= 0 => l -> Neg0
        case LessEqual(l, Number(r)) if r > 0  => l -> Unknown
        case Equal(l, Number(r))     if r < 0  => l -> Neg
        case Equal(l, Number(r))     if r == 0 => l -> Zero
        case Equal(l, Number(r))     if r > 0  => l -> Pos
        case GreaterEqual(l, Number(r)) if r < 0 => l -> Unknown
        case GreaterEqual(l, Number(r)) if r >= 0  => l -> Pos0
        case Greater(l, Number(r))      if r < 0 => l -> Unknown
        case Greater(l, Number(r))      if r >= 0  => l -> Pos
      }
      null
    }

    def sign(term: Term): Sign = term match {
      // base cases
      case x: Variable => Unknown
      case xp: DifferentialSymbol => Unknown
      case n: Number => num(n)
      case FuncOf(f, arg) => Unknown
      //case Neg(e)       => plusConverse(sign(e))
      case Plus(l, r)   => plus(sign(l), sign(r))
      case Minus(l, r)  => minus(sign(l), sign(r))
      case Times(l, r)  => times(sign(l), sign(r))
      case Divide(l, r) => divide(sign(l), sign(r))
      case Power(l, Number(r))  => power(sign(l), r.intValue()) //@note only works for small exponents
    }

//    def sign(formula: Formula): Sign = formula match {
//      // base cases
//      case Equal(l, r)        => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
//      case NotEqual(l, r)     => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
//
//      case GreaterEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
//      case Greater(l, r)      => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
//      case LessEqual(l, r)    => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
//      case Less(l, r)         => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
//
//      case PredOf(p, arg)     => VCF(fv = freeVars(arg), bv = bottom)
//      case PredicationalOf(p, arg) => VCF(fv = topVarsDiffVars(), bv = topVarsDiffVars())
//      //@note DotFormula is like a reserved zero-parameter Predicational
//      case DotFormula         => VCF(fv = topVarsDiffVars(), bv = topVarsDiffVars())
//
//      //@note except for DifferentialFormula, the following cases are equivalent to f.reapply-style but are left explicit to enforce revisiting this case when data structure changes.
//      // case f:BinaryCompositeFormula => fmlVars(f.left) ++ fmlVars(f.right)
//      // homomorphic cases
//      case Not(g)      => fmlVars(g)
//      case And(l, r)   => fmlVars(l) ++ fmlVars(r)
//      case Or(l, r)    => fmlVars(l) ++ fmlVars(r)
//      case Imply(l, r) => fmlVars(l) ++ fmlVars(r)
//      case Equiv(l, r) => fmlVars(l) ++ fmlVars(r)
//
//      // quantifier binding cases omit bound vars from fv and add bound variables to bf
//      case Forall(vars, g) => val vg = fmlVars(g); VCF(fv = vg.fv -- vars, bv = vg.bv ++ vars)
//      case Exists(vars, g) => val vg = fmlVars(g); VCF(fv = vg.fv -- vars, bv = vg.bv ++ vars)
//
//      // modality bounding cases omit must-bound vars from fv and add (may-)bound vars to bv
//      case Box(p, g)     =>
//        val vp = StaticSemantics(p)
//        val vg = fmlVars(g)
//        VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)
//      case Diamond(p, g) =>
//        val vp = StaticSemantics(p)
//        val vg = fmlVars(g)
//        VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)
//
//      // special cases
//      //@note DifferentialFormula in analogy to Differential
//      case DifferentialFormula(df) =>
//        val vdf = fmlVars(df)
//        VCF(fv = SetLattice.extendToDifferentialSymbols(vdf.fv), bv = vdf.bv)
//
//      case True | False => VCF(fv = bottom, bv = bottom)
//    }
  }

  //endregion
}