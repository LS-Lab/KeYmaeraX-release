/**
* Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.StaticSemantics.signature
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP

import scala.collection.immutable._

/** Context management, position splitting, and extraction tools.
  * Useful for splitting an expression at a position into the subexpression at that position and the remaining context around it.
  * Or for replacing a subexpression by another subexpression at all cost.
  * Or for splitting a position into a formula position and a term position.
  * @example Split a formula at a position into subformula and its context
  *  {{{
  *   val parser = KeYmaeraXParser
  *   val f = parser("x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1")
  *   // split f into context ctx and subformula g such that f is ctx{g}
  *   val (ctx,g) = Context.at(f, PosInExpr(1::1::Nil))
  *   // x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]_
  *   println(ctx)
  *   // x>=1
  *   println(f)
  *   println(f + " is the same as " + ctx(g))
  *  }}}
  * @author Andre Platzer
  * @see [[PosInExpr]]
  * @see [[Augmentors]]
  */
object Context {
  /** `true` gives slower guarded contexts that fail inadmissible term instantiation. `false` gives theoretically fast unguarded replacement contexts that are slow in practice. */
  private[keymaerax] val GUARDED = false
  /** Make a context for expression `ctx` guarded by the protection of uniform substitutions. */
  def apply[T <: Expression](ctx: T): Context[T] = GuardedContext(ctx)

  /** Whether to cross-check implementations */
  private val CROSSCHECK = false
  /** Whether to check split results redundantly */
  private val REDUNDANT = false
  /** Placeholder for programs. Reserved predicational symbol _ for substitutions are unlike ordinary predicational symbols */
  val DotProgram = ProgramConst("DotProgram")
  /** Placeholder for differential programs. Reserved predicational symbol _ for substitutions are unlike ordinary predicational symbols */
  val DotDiffProgram = DifferentialProgramConst("DotDiffProgram",AnyArg)

  /** Subexpression of `t` at the indicated position `pos` or exception if ill-defined position.
    * @ensures sub(t,pos) == at(t,pos)._2
    */
  def sub(t: Expression, pos: PosInExpr): Expression = { part(t, pos) } /*ensures(
    //@note redundant cross-contract consistency checks
    r => !CROSSCHECK || r==at(t, pos)._2, "sub(t,pos)==at(t,pos)._2")*/

  /** Direct unguarded replacement context split */
  private def directAt[T <: Expression](t: T, pos:PosInExpr): (Context[T], Expression) =
    (new ReplacementContext[T](t, pos), sub(t, pos)) ensures(
      //@note redundant cross-contract consistency checks
      r => !CROSSCHECK || {val rat = context(t, pos); r._2==rat._2 && r._1(r._2) == t && Context(rat._1)(rat._2)==t}, "cross-contract consistency")

  /**
   * Split `C{e}=t(pos)` expression t at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `t` and `e` occurs at position pos in `t`
   * (provided that back-substitution is admissible, otherwise a direct replacement in `C` at `pos` to `e` will equal `t`).
   * @ensures at(t,pos)._2 == sub(t,pos)
   */
  def at(t: Expression, pos: PosInExpr): (Context[Expression], Expression) = if (!GUARDED) {
    directAt(t, pos)
  } else {
    val sp = t match {
      case f: Term => {context(f, pos) } ensures( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
      case f: Formula => {context(f, pos) } ensures( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
      case f: DifferentialProgram => {context(f, pos) } ensures( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
      case f: Program => {context(f, pos) } ensures( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
      case _ => ???  // trivial totality on possibly problematic patmats
    }
    (Context(sp._1), sp._2)
  } ensures(r => backsubstitution(r, t, pos), "Reassembling the expression at that position into the context returns the original formula: " + t + " at " + pos)
  //@todo ensures(r => r._2 == sub(t, pos))

  private def context(e: Expression, pos: PosInExpr): (Expression, Expression) = e match {
    case f: Term => context(f, pos)
    case f: Formula => context(f, pos)
    //match order-dependent
    case f: DifferentialProgram => contextODE(f, pos)
    case f: Program => context(f, pos)
    case _ => ???  // trivial totality on possibly problematic patmats
  }

  /**
   * Split `C{e}=t(pos)` term t at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `t` and `e` occurs at position pos in `t`
   * (provided that back-substitution is admissible, otherwise a direct replacement in `C` at `pos` to `e` will equal `t`).
   */
  def at(t: Term, pos: PosInExpr): (Context[Term], Expression) = if (!GUARDED) {
    directAt(t, pos)
  } else {
    val sp = {context(t, pos) } ensures( r => !REDUNDANT || r==split(t,pos), "direct and generic split have same result " + t + " at " + pos)
    (Context(sp._1), sp._2)
  } ensures(r => backsubstitution(r, t, pos), "Reassembling the expression at that position into the context returns the original formula: " + t + " at " + pos + " gives " + Context(split(t, pos)._1)(split(t, pos)._2) + " in context " + split(t, pos))

  /**
   * Split `C{e}=f(pos)` formula f at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `f` and `e` occurs at position pos in `f`
   * (provided that back-substitution is admissible, otherwise a direct replacement in `C` at `pos` to `e` will equal `f`).
   */
  def at(f: Formula, pos: PosInExpr): (Context[Formula], Expression) = if (!GUARDED) {
    directAt(f, pos)
  } else {
    val sp = {context(f,pos) } ensures( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
    (Context(sp._1), sp._2)
  } ensures(r => backsubstitution(r, f, pos), "Reassembling the expression at that position into the context returns the original formula: " + f + " at " + pos + " gives " + Context(split(f, pos)._1)(split(f, pos)._2) + " in context " + split(f, pos))


  /**
   * Split `C{e}=a(pos)` program `a` at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `a` and `e` occurs at position pos in `a`.
   * (provided that back-substitution is admissible, otherwise a direct replacement in `C` at `pos` to `e` will equal `t`).
   */
  def at(a: Program, pos: PosInExpr): (Context[Program], Expression) = if (!GUARDED) {
    directAt(a, pos)
  } else {
    val sp = {context(a, pos) } ensures( r => !REDUNDANT || r==split(a,pos), "direct and generic split have same result " + a + " at " + pos)
    (Context(sp._1), sp._2)
  } ensures(r => backsubstitution(r, a, pos), "Reassembling the expression at that position into the context returns the original formula: " + a + " at " + pos + " gives " + Context(split(a, pos)._1)(split(a, pos)._2) + " in context " + split(a, pos))


  /**
   * Split the given position into formula position and term position within that formula.
   * @return ._1 will be the formula position of the atomic formula around pos and
   *         ._2 will be the term position that pos refers to within that atomic formula.
   * @todo horribly slow implementation by marching from the right and researching from the left.
   *       Trigger at transition to split(Term) would be much faster.
   */
  def splitPos(f: Formula, pos: PosInExpr): (PosInExpr, PosInExpr) = {
    var fPos: List[Int] = pos.pos
    var tPos: List[Int] = Nil
    while (!at(f, PosInExpr(fPos))._1.isFormulaContext) {
      assert(!fPos.isEmpty, "If there is an outer formula context, there'll be a formula context around the position")
      tPos = fPos.last :: tPos
      fPos = fPos.dropRight(1)
    }
    (PosInExpr(fPos),PosInExpr(tPos))
  } ensures(r => r._1 ++ r._2 == pos, "Concatenating split positions retains original position"
    ) ensures(r => at(f,r._1)._1.isFormulaContext && at(at(f,r._1)._2,r._2)._1.isTermContext, "Split into formula and term context")

  // at implementation

  //@note DotProgram does not exist, so no contextual plugins here. Except possibly via noctx substitutions....
  private def backsubstitution(r:(Context[Expression], Expression), t: Expression, pos: PosInExpr): Boolean = {
    if (StaticSemantics.signature(r._1.ctx).intersect(Set(noContext,noContextD)).isEmpty)
      try {
        if (r._1(r._2) == t) {
          if (CROSSCHECK) {
            //@note redundant cross-contract consistency checks
            val rsplit = (new ReplacementContext[Expression](t, pos), sub(t, pos))
            r._2 == rsplit._2 && r._1(r._2) == t && rsplit._1(rsplit._2) == t
          } else {
            true
          }
        } else
          false
      }
      catch {
        // fall-back to rude replacement as a check for whether backsubstitution justifies the context splitting when otherwise non-admissible
        case e: SubstitutionClashException => replaceAt(r._1.ctx, pos, r._2) == t
      }
    else
      // no proper reassemble test for noContext
      true
  }

  // elegant reapply-based context splitting

  /** @see [[StaticSemanticsTools.boundAt()]] for same positions */
  private def context(term: Term, pos: PosInExpr): (Term, Expression) = if (pos==HereP) (DotTerm(term.sort),term) else {term match {
    case FuncOf(f,t)     if pos.head==0 => val sp = context(t, pos.child); (FuncOf(f, sp._1), sp._2)
    // homomorphic cases
    case f:UnaryCompositeTerm  if pos.head==0 => val sp = context(f.child, pos.child); (f.reapply(sp._1), sp._2)
    case f:BinaryCompositeTerm if pos.head==0 => val sp = context(f.left, pos.child); (f.reapply(sp._1, f.right), sp._2)
    case f:BinaryCompositeTerm if pos.head==1 => val sp = context(f.right, pos.child); (f.reapply(f.left, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("split position " + pos + " of term " + term + " may not be defined")
  }} ensures(r => r._1.getClass == term.getClass, "Context has identical top types " + term + " at " + pos)

  private def context(formula: Formula, pos: PosInExpr): (Formula, Expression) = if (pos==HereP) (DotFormula, formula) else {formula match {
    // base cases
    case PredOf(p,t)          if pos.head==0 => val sp = context(t, pos.child); (PredOf(p, sp._1), sp._2)
    case PredicationalOf(c,t) if pos.head==0 => val sp = context(t, pos.child); (PredicationalOf(c, sp._1), sp._2)
    // pseudo-homomorphic cases
    case f:ComparisonFormula  if pos.head==0 => val sp = context(f.left, pos.child); (f.reapply(sp._1, f.right), sp._2)
    case f:ComparisonFormula  if pos.head==1 => val sp = context(f.right, pos.child); (f.reapply(f.left, sp._1), sp._2)
    // homomorphic cases
    case f:UnaryCompositeFormula  if pos.head==0 => val sp = context(f.child, pos.child); (f.reapply(sp._1), sp._2)
    case f:BinaryCompositeFormula if pos.head==0 => val sp = context(f.left, pos.child); (f.reapply(sp._1, f.right), sp._2)
    case f:BinaryCompositeFormula if pos.head==1 => val sp = context(f.right, pos.child); (f.reapply(f.left, sp._1), sp._2)
    case f:Quantified             if pos.head==0 => val sp = context(f.child, pos.child); (f.reapply(f.vars, sp._1), sp._2)
    case f:Modal                  if pos.head==0 => val sp = context(f.program, pos.child); (f.reapply(sp._1, f.child), sp._2)
    case f:Modal                  if pos.head==1 => val sp = context(f.child, pos.child); (f.reapply(f.program, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("split position " + pos + " of formula " + formula + " may not be defined")
  }} ensures(r => r._1.getClass == formula.getClass, "Context has identical top types " + formula + " at " + pos)

  private def context(program: Program, pos: PosInExpr): (Program, Expression) = if (pos==HereP) (DotProgram, program) else {program match {
    case Assign(x,t)       if pos==PosInExpr(0::Nil) => (noContext, x)
    case Assign(x,t)       if pos.head==1 => val sp = context(t, pos.child); (Assign(x,sp._1), sp._2)
    case AssignAny(x)      if pos==PosInExpr(0::Nil) => (noContext, x)
    case Test(f)           if pos.head==0 => val sp = context(f, pos.child); (Test(sp._1), sp._2)

    case ODESystem(ode, h) if pos.head==0 => val sp = contextODE(ode, pos.child); (ODESystem(sp._1, h), sp._2)
    case ODESystem(ode, h) if pos.head==1 => val sp = context(h, pos.child); (ODESystem(ode, sp._1), sp._2)

    // homomorphic cases
    case f:UnaryCompositeProgram  if pos.head==0 => val sp = context(f.child, pos.child); (f.reapply(sp._1), sp._2)
    case f:BinaryCompositeProgram if pos.head==0 => val sp = context(f.left, pos.child); (f.reapply(sp._1, f.right), sp._2)
    case f:BinaryCompositeProgram if pos.head==1 => val sp = context(f.right, pos.child); (f.reapply(f.left, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("split position " + pos + " of program " + program + " may not be defined")
  }} ensures(r => r._1==noContext || r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)

  private def contextODE(program: DifferentialProgram, pos: PosInExpr): (DifferentialProgram, Expression) = if (pos==HereP) (DotDiffProgram, program) else {program match {
    case AtomicODE(xp,t)          if pos==PosInExpr(0::Nil) => (noContextD, xp)
    case AtomicODE(xp,t)          if pos.head==1 => val sp = context(t, pos.child); (AtomicODE(xp,sp._1), sp._2)
    case DifferentialProduct(l,r) if pos.head==0 => val sp = contextODE(l, pos.child); (DifferentialProduct(sp._1, r), sp._2)
    case DifferentialProduct(l,r) if pos.head==1 => val sp = contextODE(r, pos.child); (DifferentialProduct(l, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("contextODE position " + pos + " of program " + program + " may not be defined")
  }} ensures(r => r._1==noContextD || r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)


  // flat subexpression extraction (for performance and context-generality). Just by computation-irrelevance of context(e,pos)._2 since identical code

  private def part(t: Expression, pos: PosInExpr): Expression = t match {
    case f: Term    => part(f, pos)
    case f: Formula => part(f, pos)
    //match order-dependent
    case f: DifferentialProgram => partODE(f, pos)
    case f: Program => part(f, pos)
    case _ => ???  // trivial totality on possibly problematic patmats
  }

  /** @see [[edu.cmu.cs.ls.keymaerax.btactics.StaticSemanticsTools.boundAt()]] for same positions */
  private def part(term: Term, pos: PosInExpr): Term = if (pos==HereP) term else {term match {
    case FuncOf(f,t)     if pos.head==0 => part(t, pos.child)
    // homomorphic cases
    case f:UnaryCompositeTerm  if pos.head==0 => part(f.child, pos.child)
    case f:BinaryCompositeTerm if pos.head==0 => part(f.left, pos.child)
    case f:BinaryCompositeTerm if pos.head==1 => part(f.right, pos.child)
    case _ => throw new IllegalArgumentException("part position " + pos + " of term " + term + " may not be defined")
  }}

  private def part(formula: Formula, pos: PosInExpr): Expression = if (pos==HereP) formula else {formula match {
    // base cases
    case PredOf(p,t)          if pos.head==0 => part(t, pos.child)
    case PredicationalOf(c,t) if pos.head==0 => part(t, pos.child)
    // pseudo-homomorphic cases
    case f:ComparisonFormula  if pos.head==0 => part(f.left, pos.child)
    case f:ComparisonFormula  if pos.head==1 => part(f.right, pos.child)
    // homomorphic cases
    case f:UnaryCompositeFormula  if pos.head==0 => part(f.child, pos.child)
    case f:BinaryCompositeFormula if pos.head==0 => part(f.left, pos.child)
    case f:BinaryCompositeFormula if pos.head==1 => part(f.right, pos.child)
    case f:Quantified             if pos.head==0 => part(f.child, pos.child)
    case f:Modal                  if pos.head==0 => part(f.program, pos.child)
    case f:Modal                  if pos.head==1 => part(f.child, pos.child)
    case _ => throw new IllegalArgumentException("part position " + pos + " of formula " + formula + " may not be defined")
  }}

  private def part(program: Program, pos: PosInExpr): Expression = if (pos==HereP) program else {program match {
    case Assign(x,t)       if pos==PosInExpr(0::Nil) => x
    case Assign(x,t)       if pos.head==1 => part(t, pos.child)
    case AssignAny(x)      if pos==PosInExpr(0::Nil) => x
    case Test(f)           if pos.head==0 => part(f, pos.child)

    case ODESystem(ode, h) if pos.head==0 => partODE(ode, pos.child)
    case ODESystem(ode, h) if pos.head==1 => part(h, pos.child)

    // homomorphic cases
    case f:UnaryCompositeProgram  if pos.head==0 => part(f.child, pos.child)
    case f:BinaryCompositeProgram if pos.head==0 => part(f.left, pos.child)
    case f:BinaryCompositeProgram if pos.head==1 => part(f.right, pos.child)
    case _ => throw new IllegalArgumentException("part position " + pos + " of program " + program + " may not be defined")
  }}

  private def partODE(program: DifferentialProgram, pos: PosInExpr): Expression = if (pos==HereP) program else {program match {
    case AtomicODE(xp,t)          if pos==PosInExpr(0::Nil) => xp
    case AtomicODE(xp,t)          if pos.head==1 => part(t, pos.child)
    case DifferentialProduct(l,r) if pos.head==0 => partODE(l, pos.child)
    case DifferentialProduct(l,r) if pos.head==1 => partODE(r, pos.child)
    case _ => throw new IllegalArgumentException("part position " + pos + " of program " + program + " may not be defined")
  }}


  // direct replacement implementation

  /** Replace within term at position pos by repl
    * @see [[edu.cmu.cs.ls.keymaerax.infrastruct.StaticSemanticsTools.boundAt()]] for same positions */
  def replaceAt(expr: Expression, pos: PosInExpr, repl: Expression): Expression = expr match {
    case f: Term    => replaceAt(f, pos, repl)
    case f: Formula => replaceAt(f, pos, repl)
    //match order-dependent
    case f: DifferentialProgram => replaceAtODE(f, pos, repl)
    case f: Program => replaceAt(f, pos, repl)
    case _ => ???  // trivial totality on possibly problematic patmats
  }

  //private def as[T <: Expression](e: Expression): Option[T] = e match { case t:T => Some(t) case _ => None }
  //private def asFormula(e: Expression): Option[Formula] = e match { case t:Formula => Some(t) case _ => None }
  /** Cast `e` as an expression of type `T` or else fall back to using value `default` instead. */
//  private def asOrElse[T <: Expression](e: Expression, default: => T): T = e match {
//    case t:T => t
//    case _ => default
//  }
  private def asOrElse(e: Expression, default: => Term): Term =
    e match { case t:Term => t case _ => default }
  private def asOrElse(e: Expression, default: => Formula): Formula =
    e match { case t:Formula => t case _ => default }
  private def asOrElse(e: Expression, default: => Program): Program =
    e match { case t:Program => t case _ => default }
  private def asOrElseD(e: Expression, default: => DifferentialProgram): DifferentialProgram =
    e match { case t:DifferentialProgram => t case _ => default }


  /** Replace within term at position pos by repl @see [[StaticSemanticsTools.boundAt()]] for same positions */
  def replaceAt(term: Term, pos: PosInExpr, repl: Expression): Term = if (pos==HereP)
    asOrElse(repl, throw new IllegalArgumentException("replaceAt position " + pos + " of term " + term + " by " + repl + " may not be defined"))
  else term match {
    case FuncOf(f,t)     if pos.head==0 => FuncOf(f, replaceAt(t, pos.child, repl))
    // homomorphic cases
    case f:UnaryCompositeTerm  if pos.head==0 => f.reapply(replaceAt(f.child, pos.child, repl))
    case f:BinaryCompositeTerm if pos.head==0 => f.reapply(replaceAt(f.left, pos.child, repl), f.right)
    case f:BinaryCompositeTerm if pos.head==1 => f.reapply(f.left, replaceAt(f.right, pos.child, repl))
    case _ => throw new IllegalArgumentException("replaceAt position " + pos + " of term " + term + " by " + repl + " may not be defined")
  }

  /** Replace within formula at position pos by repl @see [[StaticSemanticsTools.boundAt()]] for same positions */
  def replaceAt(formula: Formula, pos: PosInExpr, repl: Expression): Formula = if (pos==HereP)
    asOrElse(repl, throw new IllegalArgumentException("replaceAt position " + pos + " of formula " + formula + " by " + repl + " may not be defined"))
  else formula match {
    // base cases
    case PredOf(p,t)          if pos.head==0 => PredOf(p, replaceAt(t, pos.child, repl))
    case PredicationalOf(c,t) if pos.head==0 => PredicationalOf(c, replaceAt(t, pos.child, repl))
    // pseudo-homomorphic cases
    case f:ComparisonFormula  if pos.head==0 => f.reapply(replaceAt(f.left, pos.child, repl), f.right)
    case f:ComparisonFormula  if pos.head==1 => f.reapply(f.left, replaceAt(f.right, pos.child, repl))
    // homomorphic cases
    case f:UnaryCompositeFormula  if pos.head==0 => f.reapply(replaceAt(f.child, pos.child, repl))
    case f:BinaryCompositeFormula if pos.head==0 => f.reapply(replaceAt(f.left, pos.child, repl), f.right)
    case f:BinaryCompositeFormula if pos.head==1 => f.reapply(f.left, replaceAt(f.right, pos.child, repl))
    case f:Quantified             if pos.head==0 => f.reapply(f.vars, replaceAt(f.child, pos.child, repl))
    case f:Modal                  if pos.head==0 => f.reapply(replaceAt(f.program, pos.child, repl), f.child)
    case f:Modal                  if pos.head==1 => f.reapply(f.program, replaceAt(f.child, pos.child, repl))
    case _ => throw new IllegalArgumentException("replaceAt position " + pos + " of formula " + formula + " by " + repl + " may not be defined")
  }

  /** Replace within program at position pos by repl @see [[StaticSemanticsTools.boundAt()]] for same positions */
  def replaceAt(program: Program, pos: PosInExpr, repl:Expression): Program = if (pos==HereP)
    asOrElse(repl, throw new IllegalArgumentException("replaceAt position " + pos + " of program " + program + " by " + repl + " may not be defined"))
  else program match {
    case Assign(x,t)       if pos==PosInExpr(0::Nil) => Assign(repl.asInstanceOf[Variable], t)
    case Assign(x,t)       if pos.head==1 => Assign(x, replaceAt(t, pos.child, repl))
    case AssignAny(x)      if pos==PosInExpr(0::Nil) => AssignAny(repl.asInstanceOf[Variable])
    case Test(f)           if pos.head==0 => Test(replaceAt(f, pos.child, repl))

    case ODESystem(ode, h) if pos.head==0 => ODESystem(replaceAtODE(ode, pos.child, repl), h)
    case ODESystem(ode, h) if pos.head==1 => ODESystem(ode, replaceAt(h, pos.child, repl))

    // homomorphic cases
    case f:UnaryCompositeProgram  if pos.head==0 => f.reapply(replaceAt(f.child, pos.child, repl))
    case f:BinaryCompositeProgram if pos.head==0 => f.reapply(replaceAt(f.left, pos.child, repl), f.right)
    case f:BinaryCompositeProgram if pos.head==1 => f.reapply(f.left, replaceAt(f.right, pos.child, repl))
    case _ => throw new IllegalArgumentException("replaceAt position " + pos + " of program " + program + " by " + repl + " may not be defined")
  }

  private def replaceAtODE(program: DifferentialProgram, pos: PosInExpr, repl:Expression): DifferentialProgram = if (pos==HereP)
    asOrElseD(repl, throw new IllegalArgumentException("replaceAtODE position " + pos + " of program " + program + " by " + repl + " may not be defined"))
  else program match {
    case AtomicODE(xp,t)          if pos==PosInExpr(0::Nil) => AtomicODE(repl.asInstanceOf[DifferentialSymbol], t)
    case AtomicODE(xp,t)          if pos.head==1 => AtomicODE(xp, replaceAt(t, pos.child, repl))
    case DifferentialProduct(l,r) if pos.head==0 => DifferentialProduct(replaceAtODE(l, pos.child, repl), r)
    case DifferentialProduct(l,r) if pos.head==1 => DifferentialProduct(l, replaceAtODE(r, pos.child, repl))
    case _ => throw new IllegalArgumentException("replaceAtODE position " + pos + " of program " + program + " by " + repl + " may not be defined")
  }


  // direct split implementation
  // @note used only for contracts and performance comparison

  /** @see [[StaticSemanticsTools.boundAt()]] */
  private def split(term: Term, pos: PosInExpr): (Term, Expression) = if (pos==HereP) (DotTerm(term.sort),term) else {term match {
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
  }} ensures(r => r._1.getClass == term.getClass, "Context has identical top types " + term + " at " + pos)



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
    //@todo would like to summarize: after adding a reconstructor(BinaryComposite): (Expression,Expression)=>Expression that gives And.apply,Or.apply etc back depending on argument's top.
//    case f:BinaryCompositeFormula if pos.head==0 => val sp = split(f.left, pos.child); (f.type.apply(sp._1, f.right), sp._2)
//    case f:BinaryCompositeFormula if pos.head==1 => val sp = split(f.right, pos.child); (f.type.apply(f.left, sp._1), sp._2)
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
  }} ensures(r => r._1.getClass == formula.getClass, "Context has identical top types " + formula + " at " + pos)

  //@todo DotProgram would in a sense be the appropriate context
  private val noContext = ProgramConst("noctx")
  private def split(program: Program, pos: PosInExpr): (Program, Expression) = if (pos==HereP) (DotProgram, program) else {program match {
    case Assign(x,t)       if pos==PosInExpr(0::Nil) => (noContext, x)
    case Assign(x,t)       if pos.head==1 => val sp = split(t, pos.child); (Assign(x,sp._1), sp._2)
    case AssignAny(x)      if pos==PosInExpr(0::Nil) => (noContext, x)
    case Test(f)           if pos.head==0 => val sp = split(f, pos.child); (Test(sp._1), sp._2)

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
  }} ensures(r => r._1==noContext || r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)

  private val noContextD = DifferentialProgramConst("noctxD",AnyArg)
  private def splitODE(program: DifferentialProgram, pos: PosInExpr): (DifferentialProgram, Expression) = if (pos==HereP) (DotDiffProgram, program) else {program match {
    case AtomicODE(xp,t)          if pos==PosInExpr(0::Nil) => (noContextD, xp)
    case AtomicODE(xp,t)          if pos.head==1 => val sp = split(t, pos.child); (AtomicODE(xp,sp._1), sp._2)
    case DifferentialProduct(l,r) if pos.head==0 => val sp = splitODE(l, pos.child); (DifferentialProduct(sp._1, r), sp._2)
    case DifferentialProduct(l,r) if pos.head==1 => val sp = splitODE(r, pos.child); (DifferentialProduct(l, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("splitODE position " + pos + " of program " + program + " may not be defined")
  }} ensures(r => r._1==noContextD || r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)
}


/**
  * Convenience wrapper around contexts such as f(.) or p(.) or C{_} to make it easy to instantiate their arguments.
  * @example Split a formula at a position into subformula and its context, then instantiate this context with other subformulas:
  *  {{{
  *   val parser = KeYmaeraXParser
  *   val f = parser("x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1")
  *   // split f into context ctx and subformula g such that f is ctx{g}
  *   val (ctx,g) = Context.at(f, PosInExpr(1::1::Nil))
  *   println(f + " is the same as " + ctx(g))
  *   // put another formula h in in place of g
  *   val h = parser("x^2>y")
  *   // x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x^2>y)
  *   val result = ctx(h)
  *   println(result)
  *  }}}
  * @tparam T the type/kind of expression that this context is representing.
  * @author Stefan Mitsch
  * @author Andre Platzer
  */
sealed trait Context[+T <: Expression] extends (Expression => T) {
  import Context.{DotDiffProgram, DotProgram}

  /** the expression of type T representing this context. */
  def ctx: T

  /** Return the result of instantiating this context with argument `e`.
    * That is filling the respective dot placeholder of this context with expression `e`. */
  def apply(e: Expression): T

  /** Return the result of instantiating this context with an argument `c` which is itself again a context. */
  def apply[T2<: Expression](c: Context[T2]): Context[T] = GuardedContext(apply(c.ctx))

  //@todo could turn the following into lazy val for performance space/time tradeoff

  /** True if this context has a DotFormula so expects a formula as argument */
  def isFormulaContext = signature(ctx).contains(DotFormula)

  /** True if this context has a DotTerm so expects a term as argument */
  def isTermContext = signature(ctx).exists(_.isInstanceOf[DotTerm])

  /** True if this context has a DotProgram so expects a program as argument */
  def isProgramContext = signature(ctx).contains(DotProgram)

  /** True if this context has a DotProgram so expects a program as argument */
  def isDifferentialProgramContext = signature(ctx).contains(DotDiffProgram)

  override def toString = "Context{{" + ctx.prettyString + "}}"
}


// implementations

/**
  * An implementation of a context by direct replacement in unguarded ways (even if not admissible).
  * @param replicate the expression of type T representing this context indirectly in the sense that
  *                  instantiation replaces its position dot.
  * @param dot the position within replicate that will be replaced when instantiating this context
  * @tparam T the type/kind of expression that this context is representing.
  * @author Andre Platzer
  * @see [[Context.replaceAt()]]
  * @note ReplacementContexts that differ only in replacee are considered equal.
  */
private class ReplacementContext[+T <: Expression](replicate: T, dot: PosInExpr) extends Context[T] {
  import Context.{DotDiffProgram, DotProgram}
  private lazy val dotty = if (isFormulaContext) DotFormula else if (isTermContext) DotTerm() else if (isProgramContext) DotProgram else DotDiffProgram
  def ctx: T = apply(dotty)

  def apply(e: Expression): T = Context.replaceAt(replicate, dot, e).asInstanceOf[T]

  /** What is replaced by argument (so not part of the context in fact) */
  private lazy val replacee: Expression = Context.at(replicate, dot)._2

  override def isFormulaContext = replacee.kind==FormulaKind

  override def isTermContext = replacee.kind==TermKind

  override def isProgramContext =replacee.kind==ProgramKind

  override def isDifferentialProgramContext = replacee.kind==DifferentialProgramKind

  override def toString = "ReplContext{{" + replicate.prettyString + " at " + dot + "}}"

  override def equals(e: Any): Boolean = e match {
    case a: ReplacementContext[T] => ctx == a.ctx
    case a:GuardedContext[T] if !isTermContext => ctx == a.ctx     //@todo good or bad idea?
    case _ => false
  }

  //@note expensive
  override def hashCode: Int = ctx.hashCode()
}


/**
  * An implementation of a context guarded by the protection of uniform substitutions.
  * @param ctx the expression of type T representing this context
  * @tparam T the type/kind of expression that this context is representing.
  * @author Andre Platzer
  * @see [[USubst]]
  */
private case class GuardedContext[+T <: Expression](ctx: T) extends Context[T] {
  import Context.{DotDiffProgram, DotProgram}
  // either a term or a formula context, not both
  require(!(signature(ctx).contains(DotFormula) && signature(ctx).exists(_.isInstanceOf[DotTerm])), "Contexts are either DotFormula or DotTerm contexts, not both at once: " + ctx)

  /** Return the result of instantiating this context with argument `e`.
    * That is filling the respective dot placeholder of this context with expression `e`. */
  def apply(e: Expression): T = e match {
    case f: Formula => instantiate(f)
    case t: Term => instantiate(t)
    case a: DifferentialProgram if isDifferentialProgramContext => instantiate(a)
    case a: Program => instantiate(a)
  }

  /**
   * Instantiates the context ctx with the formula withF
   * @param withF The formula to instantiate this context ctx with.
   * @return The instantiated context ctx{withF}.
   */
  private def instantiate(withF: Formula): T = {
    assert(!isTermContext, "can only instantiate formulas within a formula context " + this)
    USubst(SubstitutionPair(DotFormula, withF) :: Nil)(ctx).asInstanceOf[T]
  }

  /**
   * Instantiates the context ctx with the term withT
   * @param withT The term to instantiate this context ctx with.
   * @return The instantiated context ctx(withT).
   * @todo this implementation could be generalized using predicationals or replaceAt.
   */
  private def instantiate(withT: Term): T = {
    assert(!isFormulaContext, "can only instantiate terms within a term context " + this)
    USubst(SubstitutionPair(DotTerm(Real), withT) :: Nil)(ctx).asInstanceOf[T]
  }

  /**
   * Instantiates the context ctx with the program withA
   * @param withA The program to instantiate this context ctx with.
   * @return The instantiated context ctx{withA}.
   */
  private def instantiate(withA: Program): T = {
    assert(!isFormulaContext || isTermContext, "can only instantiate programs within a program context " + this)
    if (withA.isInstanceOf[DifferentialProgram] && !withA.isInstanceOf[ODESystem]) //2nd test redundant: ODESystem does not extend DifferentialProgram
      instantiate(withA.asInstanceOf[DifferentialProgram])
    else
      USubst(SubstitutionPair(DotProgram, withA) :: Nil)(ctx).asInstanceOf[T]
  }

  /**
   * Instantiates the context ctx with the program withA
   * @param withA The program to instantiate this context ctx with.
   * @return The instantiated context ctx{withA}.
   */
  private def instantiate(withA: DifferentialProgram): T = {
    assert(!isFormulaContext || isTermContext, "can only instantiate differential programs within a differential program context " + this)
    USubst(SubstitutionPair(DotDiffProgram, withA) :: Nil)(ctx).asInstanceOf[T]
  }

  //@todo good or bad idea?
  override def equals(e: Any): Boolean = e match {
    case a: ReplacementContext[T] if !isTermContext => ctx == a.ctx
    case a: GuardedContext[T] => ctx == a.ctx
    case _ => false
  }

}
