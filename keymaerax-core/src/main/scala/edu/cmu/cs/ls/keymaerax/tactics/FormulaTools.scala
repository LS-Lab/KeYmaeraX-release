/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Tactic tools for formula manipulation and extraction.
 * @author aplatzer
 */
object FormulaTools {
  // formula tools

  /**
   * Split a formula into its conjuncts.
   * Without performing clause form or CNF or DNF transformations.
   * @example conjuncts(p() & q() & (r() & (s() | t()&u()))) == List(p(), q(), r(), s()|t()&u())
   */
  def conjuncts(formula: Formula): List[Formula] = formula match {
    case And(p,q) => conjuncts(p) ++ conjuncts(q)
    case f => List(f)
  }

  /**
   * Split a formula into its disjuncts.
   * Without performing clause form or CNF or DNF transformations.
   * @example disjuncts(p() | q() | (r() | (s() & (t()|u())))) == List(p(), q(), r(), s()&(t()|u()))
   */
  def disjuncts(formula: Formula): List[Formula] = formula match {
    case Or(p,q) => disjuncts(p) ++ disjuncts(q)
    case f => List(f)
  }

}
