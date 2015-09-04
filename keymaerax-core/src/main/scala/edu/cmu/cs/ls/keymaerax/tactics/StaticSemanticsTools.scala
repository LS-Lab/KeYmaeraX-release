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
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics]]
 */
object StaticSemanticsTools {

  /**
   * The set of variables that the top-level operator of this formula is binding itself,
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
   * The set of variables that the top-level operator of this program is binding itself,
   * so not those variables that are only bound because of operators in subprograms.
   */
  def bindingVars(program: Program): SetLattice[NamedSymbol] = program match {
    //@note It's the pieces of ODESystems that bind but the scope is the whole ODESystem, which is somewhat like an AtomicProgram
    case a: ODESystem     => boundVars(a)
    // base cases
    case a: AtomicProgram => boundVars(a)
    //@note acceptable but slightly dangerous catch-all but not soundness-critical
    case a: CompositeProgram => bottom
  }
  //@todo ensuring(r => !formula.isInstanceOf[BinaryCompositeFormula] || r==boundVars(formula.class.apply(True,True)), "same bound variables as replacing left,right with True)

  /**
   * The set of variables that, if they occurred at formula(pos) would be bound occurrences,
   * because there was an operator in formula on the path to pos for which it was binding.
   * If an occurrence of a variable at formula(pos) is not boundAt(formula,pos) then it is a free occurrence.
   * @see [[Context.at()]]
   */
  def boundAt(formula: Formula, pos: PosInExpr): SetLattice[NamedSymbol] = if (pos==HereP) bottom else formula match {
    case e:Quantified             if pos.head==0 => bindingVars(e) ++ boundAt(e.child, pos.child)
    case e:Modal                  if pos.head==0 => boundAt(e.program, pos.child)
    case e:Modal                  if pos.head==1 => bindingVars(e) ++ boundAt(e.child, pos.child)
    case e:UnaryCompositeFormula  if pos.head==0 => bindingVars(e) ++ boundAt(e.child, pos.child)
    case e:BinaryCompositeFormula if pos.head==0 => bindingVars(e) ++ boundAt(e.left,  pos.child)
    case e:BinaryCompositeFormula if pos.head==1 => bindingVars(e) ++ boundAt(e.right, pos.child)
    //@note predicationals will bind everything anyhow so no need to descend
    case e:PredicationalOf                       => bindingVars(e)
    //@note term children won't bind anything anyhow so no need to descend
    case e:AtomicFormula                         => bindingVars(e)
    case _ => throw new IllegalArgumentException("boundAt position " + pos + " of formula " + formula + " may not be defined")
  }

  /**
   * The set of variables that, if they occurred at program(pos) would be bound occurrences,
   * because there was an operator in program on the path to pos for which it was binding.
   * If an occurrence of a variable at program(pos) is not boundAt(program,pos) then it is a free occurrence.
   * @see [[Context.at()]]
   */
  def boundAt(program: Program, pos: PosInExpr): SetLattice[NamedSymbol] = if (pos==HereP) bottom else program match {
    //@note differential programs have global scope within the whole DifferentialProgram
    case dp:DifferentialProgram                  => bindingVars(dp)
    case e@ODESystem(ode, h)      if pos.head<=1 => bindingVars(e)
    case e:UnaryCompositeProgram  if pos.head==0 => bindingVars(e) ++ boundAt(e.child, pos.child)
    case e:BinaryCompositeProgram if pos.head==0 => bindingVars(e) ++ boundAt(e.left,  pos.child)
    case e:BinaryCompositeProgram if pos.head==1 => bindingVars(e) ++ boundAt(e.right, pos.child)
    case e@Assign(x,t)            if pos.head==0 => bindingVars(e)
    case e@Assign(x,t)            if pos.head==1 => bottom
    case e@DiffAssign(xp,t)       if pos.head==0 => bindingVars(e)
    case e@DiffAssign(xp,t)       if pos.head==1 => bottom
    //case e:DifferentialProduct    if pos.head==0 => boundAt(e.left,  pos.child)
    //case e:DifferentialProduct    if pos.head==1 => boundAt(e.right,  pos.child)
    //@todo the following would be suboptimal (except for AssignAny,Test,ProgramConst,DifferentialProgramConst)
    case e:AtomicProgram                         => bindingVars(e)
    case _ => throw new IllegalArgumentException("boundAt position " + pos + " of program " + program + " may not be defined")
  }
}
