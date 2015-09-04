/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics.signature

/** Context management, splitting, and extraction tools.
  * @author Andre Platzer
  * @see [[PosInExpr]]
  * @see [[Augmentors]]
  */
object Context {
  /**
   * Split `C{e}=t(pos)` expression t at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `t` and `e` occurs at position pos in `t`
   */
  def at(t: Expression, pos: PosInExpr): (Context[Expression], Expression) = {
    val sp = t match {
      case f: Term => split(f, pos)
      case f: Formula => split(f, pos)
      case f: Program => split(f, pos)
      case f: DifferentialProgram => split(f, pos)
      case _ => ???  // trivial totality on possibly problematic patmats
    }
    (Context(sp._1), sp._2)
  } ensuring(r => r._1(r._2) == t, "Reassembling the expression at that position into the context returns the original formula: " + t + " at " + pos)

  /**
   * Split `C{e}=t(pos)` term t at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `t` and `e` occurs at position pos in `t`
   */
  def at(t: Term, pos: PosInExpr): (Context[Term], Expression) = {
    val sp = split(t, pos)
    (Context(sp._1), sp._2)
  } ensuring(r => r._1(r._2) == t, "Reassembling the expression at that position into the context returns the original formula: " + t + " at " + pos + " gives " + Context(split(t, pos)._1)(split(t, pos)._2) + " in context " + split(t, pos))

  /**
   * Split `C{e}=f(pos)` formula f at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `f` and `e` occurs at position pos in `f`
   */
  def at(f: Formula, pos: PosInExpr): (Context[Formula], Expression) = {
    val sp = split(f, pos)
    (Context(sp._1), sp._2)
  } ensuring(r => r._1(r._2) == f, "Reassembling the expression at that position into the context returns the original formula: " + f + " at " + pos + " gives " + Context(split(f, pos)._1)(split(f, pos)._2) + " in context " + split(f, pos))


  /**
   * Split `C{e}=a(pos)` program `a` at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `a` and `e` occurs at position pos in `a`.
   */
  def at(a: Program, pos: PosInExpr): (Context[Program], Expression) = {
    val sp = split(a, pos)
    (Context(sp._1), sp._2)
  } ensuring(r => r._1(r._2) == a, "Reassembling the expression at that position into the context returns the original formula: " + a + " at " + pos + " gives " + Context(split(a, pos)._1)(split(a, pos)._2) + " in context " + split(a, pos))

  // at implementation

  /** @see [[StaticSemanticsTools.boundAt()]] */
  private def split(term: Term, pos: PosInExpr): (Term, Expression) = if (pos==HereP) (DotTerm,term) else {term match {
    case FuncOf(f,t)     if pos.head==0 => val sp = split(t, pos.child); (FuncOf(f, sp._1), sp._2)
    // homomorphic cases
    case Neg(g)          if pos.head==0 => val sp = split(g, pos.child); (Neg(sp._1), sp._2)
    case Plus(f,g)       if pos.head==0 => val sp = split(f, pos.child); (Plus(sp._1, g), sp._2)
    case Plus(f,g)       if pos.head==1 => val sp = split(g, pos.child); (Plus(f, sp._1), sp._2)
    case Minus(f,g)      if pos.head==0 => val sp = split(f, pos.child); (Minus(sp._1, g), sp._2)
    case Minus(f,g)      if pos.head==1 => val sp = split(g, pos.child); (Minus(f, sp._1), sp._2)
    case Times(f,g)      if pos.head==0 => val sp = split(f, pos.child); (Times(sp._1, g), sp._2)
    case Times(f,g)      if pos.head==1 => val sp = split(g, pos.child); (Times(f, sp._1), sp._2)
    case Divide(f,g)     if pos.head==0 => val sp = split(f, pos.child); (Divide(sp._1, g), sp._2)
    case Divide(f,g)     if pos.head==1 => val sp = split(g, pos.child); (Divide(f, sp._1), sp._2)
    case Power(f,g)      if pos.head==0 => val sp = split(f, pos.child); (Power(sp._1, g), sp._2)
    case Power(f,g)      if pos.head==1 => val sp = split(g, pos.child); (Power(f, sp._1), sp._2)
    case Differential(g) if pos.head==0 => val sp = split(g, pos.child); (Differential(sp._1), sp._2)
    case Pair(f,g)       if pos.head==0 => val sp = split(f, pos.child); (Pair(sp._1, g), sp._2)
    case Pair(f,g)       if pos.head==1 => val sp = split(g, pos.child); (Pair(f, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("split position " + pos + " of term " + term + " may not be defined")
  }} ensuring(r => r._1.getClass == term.getClass, "Context has identical top types " + term + " at " + pos)

  private def split(formula: Formula, pos: PosInExpr): (Formula, Expression) = if (pos==HereP) (DotFormula, formula) else {formula match {
    // base cases
    case PredOf(p,t)          if pos.head==0 => val sp = split(t, pos.child); (PredOf(p, sp._1), sp._2)
    case PredicationalOf(c,t) if pos.head==0 => val sp = split(t, pos.child); (PredicationalOf(c, sp._1), sp._2)
    // pseudo-homomorphic cases
    case Equal(f,g)           if pos.head==0 => val sp = split(f, pos.child); (Equal(sp._1, g), sp._2)
    case Equal(f,g)           if pos.head==1 => val sp = split(g, pos.child); (Equal(f, sp._1), sp._2)
    case NotEqual(f,g)        if pos.head==0 => val sp = split(f, pos.child); (NotEqual(sp._1, g), sp._2)
    case NotEqual(f,g)        if pos.head==1 => val sp = split(g, pos.child); (NotEqual(f, sp._1), sp._2)
    case GreaterEqual(f,g)    if pos.head==0 => val sp = split(f, pos.child); (GreaterEqual(sp._1, g), sp._2)
    case GreaterEqual(f,g)    if pos.head==1 => val sp = split(g, pos.child); (GreaterEqual(f, sp._1), sp._2)
    case Greater(f,g)         if pos.head==0 => val sp = split(f, pos.child); (Greater(sp._1, g), sp._2)
    case Greater(f,g)         if pos.head==1 => val sp = split(g, pos.child); (Greater(f, sp._1), sp._2)
    case LessEqual(f,g)       if pos.head==0 => val sp = split(f, pos.child); (LessEqual(sp._1, g), sp._2)
    case LessEqual(f,g)       if pos.head==1 => val sp = split(g, pos.child); (LessEqual(f, sp._1), sp._2)
    case Less(f,g)            if pos.head==0 => val sp = split(f, pos.child); (Less(sp._1, g), sp._2)
    case Less(f,g)            if pos.head==1 => val sp = split(g, pos.child); (Less(f, sp._1), sp._2)
    // homomorphic cases
    case Not(f)               if pos.head==0 => val sp = split(f, pos.child); (Not(sp._1), sp._2)
    case And(f,g)             if pos.head==0 => val sp = split(f, pos.child); (And(sp._1, g), sp._2)
    case And(f,g)             if pos.head==1 => val sp = split(g, pos.child); (And(f, sp._1), sp._2)
    case Or(f,g)              if pos.head==0 => val sp = split(f, pos.child); (Or(sp._1, g), sp._2)
    case Or(f,g)              if pos.head==1 => val sp = split(g, pos.child); (Or(f, sp._1), sp._2)
    case Imply(f,g)           if pos.head==0 => val sp = split(f, pos.child); (Imply(sp._1, g), sp._2)
    case Imply(f,g)           if pos.head==1 => val sp = split(g, pos.child); (Imply(f, sp._1), sp._2)
    case Equiv(f,g)           if pos.head==0 => val sp = split(f, pos.child); (Equiv(sp._1, g), sp._2)
    case Equiv(f,g)           if pos.head==1 => val sp = split(g, pos.child); (Equiv(f, sp._1), sp._2)
    case Forall(vars, f)      if pos.head==0 => val sp = split(f, pos.child); (Forall(vars, sp._1), sp._2)
    case Exists(vars, f)      if pos.head==0 => val sp = split(f, pos.child); (Exists(vars, sp._1), sp._2)
    case Box(a, g)            if pos.head==0 => val sp = split(a, pos.child); (Box(sp._1, g), sp._2)
    case Box(a, g)            if pos.head==1 => val sp = split(g, pos.child); (Box(a, sp._1), sp._2)
    case Diamond(a, g)        if pos.head==0 => val sp = split(a, pos.child); (Diamond(sp._1, g), sp._2)
    case Diamond(a, g)        if pos.head==1 => val sp = split(g, pos.child); (Diamond(a, sp._1), sp._2)
    case DifferentialFormula(f) if pos.head==0 => val sp = split(f, pos.child); (DifferentialFormula(sp._1), sp._2)
    case _ => throw new IllegalArgumentException("split position " + pos + " of formula " + formula + " may not be defined")
  }} ensuring(r => r._1.getClass == formula.getClass, "Context has identical top types " + formula + " at " + pos)

  //@todo DotProgram would in a sense be the appropriate context
  private val noContext = ProgramConst("noctx")
  private def split(program: Program, pos: PosInExpr): (Program, Expression) = if (pos==HereP) (noContext, program) else {program match {
    case Assign(x,t)       if pos==PosInExpr(0::Nil) => (noContext, x)
    case Assign(x,t)       if pos.head==1 => val sp = split(t, pos.child); (Assign(x,sp._1), sp._2)
    case DiffAssign(xp,t)  if pos==PosInExpr(0::Nil) => (noContext, xp)
    case DiffAssign(xp,t)  if pos.head==1 => val sp = split(t, pos.child); (DiffAssign(xp,sp._1), sp._2)
    case AssignAny(x)      if pos==PosInExpr(0::Nil) => (noContext, x)

    case ODESystem(ode, h) if pos.head==0 => val sp = splitODE(ode, pos.child); (ODESystem(sp._1, h), sp._2)
    case ODESystem(ode, h) if pos.head==1 => val sp = split(h, pos.child); (ODESystem(ode, sp._1), sp._2)

    // homomorphic cases
    case Choice(f,g)       if pos.head==0 => val sp = split(f, pos.child); (Choice(sp._1, g), sp._2)
    case Choice(f,g)       if pos.head==1 => val sp = split(g, pos.child); (Choice(f, sp._1), sp._2)
    case Compose(f,g)      if pos.head==0 => val sp = split(f, pos.child); (Compose(sp._1, g), sp._2)
    case Compose(f,g)      if pos.head==1 => val sp = split(g, pos.child); (Compose(f, sp._1), sp._2)
    case Loop(f)           if pos.head==0 => val sp = split(f, pos.child); (Loop(sp._1), sp._2)
    case Dual(f)           if pos.head==0 => val sp = split(f, pos.child); (Dual(sp._1), sp._2)
    case _ => throw new IllegalArgumentException("split position " + pos + " of program " + program + " may not be defined")
  }} ensuring(r => r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)

  private val noContextD = DifferentialProgramConst("noctx")
  private def splitODE(program: DifferentialProgram, pos: PosInExpr): (DifferentialProgram, Expression) = if (pos==HereP) (noContextD, program) else {program match {
    case AtomicODE(xp,t)          if pos==PosInExpr(0::Nil) => (noContextD, xp)
    case AtomicODE(xp,t)          if pos.head==1 => val sp = split(t, pos.child); (AtomicODE(xp,sp._1), sp._2)
    case DifferentialProduct(l,r) if pos.head==0 => val sp = splitODE(l, pos.child); (DifferentialProduct(sp._1, r), sp._2)
    case DifferentialProduct(l,r) if pos.head==1 => val sp = splitODE(r, pos.child); (DifferentialProduct(l, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("splitODE position " + pos + " of program " + program + " may not be defined")
  }} ensuring(r => r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)
}

/**
 * Convenience wrapper around contexts such as f(.) or p(.) or C{_} etc
 * Created by smitsch on 3/29/15.
 * @author Stefan Mitsch
 */
sealed case class Context[+T <: Expression](ctx: T) {
  // either a term or a formula context, not both
  require(!(signature(ctx).contains(DotFormula) && signature(ctx).contains(DotTerm)), "Contexts are either DotFormula or DotTerm contexts, not both at once: " + ctx)

  /** Return the result of filling the dot placeholder of this context with expression e */
  def apply(e: Expression) = e match {
    case f: Formula => instantiate(f)
    case t: Term => instantiate(t)
  }

  def isFormulaContext = signature(ctx).contains(DotFormula)
  def isTermContext = signature(ctx).contains(DotTerm)

  /**
   * Instantiates the context ctx with the formula withF
   * @param withF The formula to instantiate context ctx with.
   * @return The instantiated context ctx{withF}.
   */
  def instantiate(withF: Formula): Formula = {
    assert(isFormulaContext, "can only instantiate formulas within a formula context " + this)
    val context = Function("dottingC_", None, Bool, Bool)//@TODO eisegesis  should be Function("dottingC_", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype
    USubst(SubstitutionPair(PredicationalOf(context, DotFormula), ctx) :: Nil)(PredicationalOf(context, withF))
  }

  /**
   * Instantiates the context ctx with the term withT
   * @param withT The term to instantiate context ctx with.
   * @return The instantiated context ctx(withT).
   */
  def instantiate(withT: Term): Formula = {
    assert(isTermContext, "can only instantiate terns within a tern context " + this)
    val context = Function("dottingC_", None, Real, Bool)
    USubst(SubstitutionPair(PredOf(context, DotTerm), ctx) :: Nil)(PredOf(context, withT))
  }
}
