/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.StaticSemantics._
import edu.cmu.cs.ls.keymaerax.core.SetLattice.bottom
import edu.cmu.cs.ls.keymaerax.core._

/**
 * Additional tools read off from the static semantics for the tactics.
 * @author aplatzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics]]
 */
object StaticSemanticsTools {

  /**
   * The set variables that the top-level operator of this formula is binding itself,
   * so not those variables that are only bound because of operators in subformulas.
   */
  def bindingVars(formula: Formula): SetLattice[NamedSymbol] = formula match {
    // DotFormula is like a reserved Predicational
    case DotFormula => boundVars(DotFormula)
    case PredicationalOf(p, arg) => boundVars(formula)

    // quantifier binding cases omit bound vars from fv and add bound variables to bf
    case f: Quantified => SetLattice[NamedSymbol](f.vars) ensuring (r=> r==boundVars(Forall(f.vars,True)) && r==boundVars(Exists(f.vars,True)))

    // modality bounding cases omit must-bound vars from fv and add (may-)bound vars to bv
    case f: Modal => boundVars(f.program) ensuring (r=> r==boundVars(Box(f.program,True)) && r==boundVars(Diamond(f.program,True)))

    // special cases
    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(df) => boundVars(formula)

    //@note dangerous catch-all but not soundness-critical
    case _ => bottom

  }
  //@todo ensuring(r => !formula.isInstanceOf[BinaryCompositeFormula] || r==boundVars(formula.class.apply(True,True)), "same bound variables as replacing left,right with True)

  /**
   * The set variables that the top-level operator of this formula is binding itself,
   * so not those variables that are only bound because of operators in subprograms.
   */
  def bindingVars(program: Program): SetLattice[NamedSymbol] = program match {
      // base cases
    case a: AtomicProgram => boundVars(a)
    //@note acceptable but slightly dangerous catch-all but not soundness-critical
    case a: CompositeProgram => bottom
  }
  //@todo ensuring(r => !formula.isInstanceOf[BinaryCompositeFormula] || r==boundVars(formula.class.apply(True,True)), "same bound variables as replacing left,right with True)

}
