/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics.signature

/** Context management, splitting, and extraction tools.
  * @author Andre Platzer
  * @see [[PosInExpr]]
  * @see [[Augmentors]]
  */
object Context {
  import Reconstructors._

  /** Whether to check split results redundantly */
  private val REDUNDANT = false
  /** Placeholder for programs. Reserved predicational symbol _ for substitutions are unlike ordinary predicational symbols */
  val DotProgram = ProgramConst("DotProgram")
  /** Placeholder for differential programs. Reserved predicational symbol _ for substitutions are unlike ordinary predicational symbols */
  val DotDiffProgram = DifferentialProgramConst("DotDiffProgram")
  /**
   * Split `C{e}=t(pos)` expression t at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `t` and `e` occurs at position pos in `t`
   * (provided that back-substitution is admissible, otherwise a direct replacement in `C` at `pos` to `e` will equal `t`).
   */
  def at(t: Expression, pos: PosInExpr): (Context[Expression], Expression) = {
    val sp = t match {
      case f: Term => {context(f, pos) } ensuring( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
      case f: Formula => {context(f, pos) } ensuring( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
      case f: Program => {context(f, pos) } ensuring( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
      case f: DifferentialProgram => {context(f, pos) } ensuring( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
      case _ => ???  // trivial totality on possibly problematic patmats
    }
    (Context(sp._1), sp._2)
  } ensuring(r => backsubstitution(r, t, pos), "Reassembling the expression at that position into the context returns the original formula: " + t + " at " + pos)

  /**
   * Split `C{e}=t(pos)` term t at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `t` and `e` occurs at position pos in `t`
   * (provided that back-substitution is admissible, otherwise a direct replacement in `C` at `pos` to `e` will equal `t`).
   */
  def at(t: Term, pos: PosInExpr): (Context[Term], Expression) = {
    val sp = {context(t, pos) } ensuring( r => !REDUNDANT || r==split(t,pos), "direct and generic split have same result " + t + " at " + pos)
    (Context(sp._1), sp._2)
  } ensuring(r => backsubstitution(r, t, pos), "Reassembling the expression at that position into the context returns the original formula: " + t + " at " + pos + " gives " + Context(split(t, pos)._1)(split(t, pos)._2) + " in context " + split(t, pos))

  /**
   * Split `C{e}=f(pos)` formula f at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `f` and `e` occurs at position pos in `f`
   * (provided that back-substitution is admissible, otherwise a direct replacement in `C` at `pos` to `e` will equal `t`).
   */
  def at(f: Formula, pos: PosInExpr): (Context[Formula], Expression) = {
    val sp = {context(f,pos) } ensuring( r => !REDUNDANT || r==split(f,pos), "direct and generic split have same result " + f + " at " + pos)
    (Context(sp._1), sp._2)
  } ensuring(r => backsubstitution(r, f, pos), "Reassembling the expression at that position into the context returns the original formula: " + f + " at " + pos + " gives " + Context(split(f, pos)._1)(split(f, pos)._2) + " in context " + split(f, pos))


  /**
   * Split `C{e}=a(pos)` program `a` at position pos into the expression e at that position and the context C within which that expression occurs.
   * Thus `C{e}` will equal the original `a` and `e` occurs at position pos in `a`.
   * (provided that back-substitution is admissible, otherwise a direct replacement in `C` at `pos` to `e` will equal `t`).
   */
  def at(a: Program, pos: PosInExpr): (Context[Program], Expression) = {
    val sp = {context(a, pos) } ensuring( r => !REDUNDANT || r==split(a,pos), "direct and generic split have same result " + a + " at " + pos)
    (Context(sp._1), sp._2)
  } ensuring(r => backsubstitution(r, a, pos), "Reassembling the expression at that position into the context returns the original formula: " + a + " at " + pos + " gives " + Context(split(a, pos)._1)(split(a, pos)._2) + " in context " + split(a, pos))


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
  } ensuring(r => r._1.append(r._2) == pos, "Concatenating split positions retains original position"
    ) ensuring(r => at(f,r._1)._1.isFormulaContext && at(at(f,r._1)._2,r._2)._1.isTermContext, "Split into formula and term context")

  // at implementation

  //@note DotProgram does not exist, so no contextual plugins here. Except possibly via noctx substitutions....
  private def backsubstitution(r:(Context[Expression], Expression), t: Expression, pos: PosInExpr): Boolean = {
    if (StaticSemantics.signature(r._1.ctx).intersect(Set(noContext,noContextD)).isEmpty)
      try {
        r._1(r._2) == t
      }
      catch {
        case e: SubstitutionClashException => replaceAt(r._1.ctx, pos, r._2) == t
      }
    else
      // no proper reassemble test for noContext
      true
  }

  /** @see [[StaticSemanticsTools.boundAt()]] for same positions */
  private def context(term: Term, pos: PosInExpr): (Term, Expression) = if (pos==HereP) (DotTerm,term) else {term match {
    case FuncOf(f,t)     if pos.head==0 => val sp = context(t, pos.child); (FuncOf(f, sp._1), sp._2)
    // homomorphic cases
    case f:UnaryCompositeTerm  if pos.head==0 => val sp = context(f.child, pos.child); (f.reapply(sp._1), sp._2)
    case f:BinaryCompositeTerm if pos.head==0 => val sp = context(f.left, pos.child); (f.reapply(sp._1, f.right), sp._2)
    case f:BinaryCompositeTerm if pos.head==1 => val sp = context(f.right, pos.child); (f.reapply(f.left, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("split position " + pos + " of term " + term + " may not be defined")
  }} ensuring(r => r._1.getClass == term.getClass, "Context has identical top types " + term + " at " + pos)

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
  }} ensuring(r => r._1.getClass == formula.getClass, "Context has identical top types " + formula + " at " + pos)

  private def context(program: Program, pos: PosInExpr): (Program, Expression) = if (pos==HereP) (DotProgram, program) else {program match {
    case Assign(x,t)       if pos==PosInExpr(0::Nil) => (noContext, x)
    case Assign(x,t)       if pos.head==1 => val sp = context(t, pos.child); (Assign(x,sp._1), sp._2)
    case DiffAssign(xp,t)  if pos==PosInExpr(0::Nil) => (noContext, xp)
    case DiffAssign(xp,t)  if pos.head==1 => val sp = context(t, pos.child); (DiffAssign(xp,sp._1), sp._2)
    case AssignAny(x)      if pos==PosInExpr(0::Nil) => (noContext, x)
    case Test(f)           if pos.head==0 => val sp = context(f, pos.child); (Test(sp._1), sp._2)

    case ODESystem(ode, h) if pos.head==0 => val sp = contextODE(ode, pos.child); (ODESystem(sp._1, h), sp._2)
    case ODESystem(ode, h) if pos.head==1 => val sp = context(h, pos.child); (ODESystem(ode, sp._1), sp._2)

    // homomorphic cases
    case f:UnaryCompositeProgram  if pos.head==0 => val sp = context(f.child, pos.child); (f.reapply(sp._1), sp._2)
    case f:BinaryCompositeProgram if pos.head==0 => val sp = context(f.left, pos.child); (f.reapply(sp._1, f.right), sp._2)
    case f:BinaryCompositeProgram if pos.head==1 => val sp = context(f.right, pos.child); (f.reapply(f.left, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("split position " + pos + " of program " + program + " may not be defined")
  }} ensuring(r => r._1==noContext || r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)

  private def contextODE(program: DifferentialProgram, pos: PosInExpr): (DifferentialProgram, Expression) = if (pos==HereP) (DotDiffProgram, program) else {program match {
    case AtomicODE(xp,t)          if pos==PosInExpr(0::Nil) => (noContextD, xp)
    case AtomicODE(xp,t)          if pos.head==1 => val sp = context(t, pos.child); (AtomicODE(xp,sp._1), sp._2)
    case DifferentialProduct(l,r) if pos.head==0 => val sp = contextODE(l, pos.child); (DifferentialProduct(sp._1, r), sp._2)
    case DifferentialProduct(l,r) if pos.head==1 => val sp = contextODE(r, pos.child); (DifferentialProduct(l, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("contextODE position " + pos + " of program " + program + " may not be defined")
  }} ensuring(r => r._1==noContextD || r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)



  /** Replace within term at position pos by repl @see [[StaticSemanticsTools.boundAt()]] for same positions */
  def replaceAt(expr: Expression, pos: PosInExpr, repl: Expression): Expression = expr match {
    case f: Term    => replaceAt(f, pos, repl)
    case f: Formula => replaceAt(f, pos, repl)
    case f: Program => replaceAt(f, pos, repl)
    case _ => ???  // trivial totality on possibly problematic patmats
  }

  /** Replace within term at position pos by repl @see [[StaticSemanticsTools.boundAt()]] for same positions */
  def replaceAt(term: Term, pos: PosInExpr, repl: Expression): Term = if (pos==HereP) repl.asInstanceOf[Term] else term match {
    case FuncOf(f,t)     if pos.head==0 => FuncOf(f, replaceAt(t, pos.child, repl))
    // homomorphic cases
    case f:UnaryCompositeTerm  if pos.head==0 => f.reapply(replaceAt(f.child, pos.child, repl))
    case f:BinaryCompositeTerm if pos.head==0 => f.reapply(replaceAt(f.left, pos.child, repl), f.right)
    case f:BinaryCompositeTerm if pos.head==1 => f.reapply(f.left, replaceAt(f.right, pos.child, repl))
    case _ => throw new IllegalArgumentException("replaceAt position " + pos + " of term " + term + " may not be defined")
  }

  /** Replace within formula at position pos by repl @see [[StaticSemanticsTools.boundAt()]] for same positions */
  def replaceAt(formula: Formula, pos: PosInExpr, repl: Expression): Formula = if (pos==HereP) repl.asInstanceOf[Formula] else formula match {
    // base cases
    case PredOf(p,t)          if pos.head==0 => PredOf(p, replaceAt(t, pos.child, repl))
    case PredicationalOf(c,t) if pos.head==0 => PredicationalOf(c, replaceAt(t, pos.child, repl))
    // pseudo-homomorphic cases
    case f:ComparisonFormula  if pos.head==0 => f.reapply(replaceAt(f.left, pos.child, repl), f.right)
    case f:ComparisonFormula  if pos.head==1 => f.reapply(f.left, replaceAt(f.right, pos.child, repl))
    // homomorphic cases
    case f:UnaryCompositeFormula  if pos.head==0 => f.reapply(replaceAt(f.child, pos.child, repl))
    case f:BinaryCompositeFormula if pos.head==0 => f.reapply(replaceAt(f.left, pos.child, repl), f.right)
    case f:BinaryCompositeFormula if pos.head==1 => f.reapply(f.left, replaceAt(f.left, pos.child, repl))
    case f:Quantified             if pos.head==0 => f.reapply(f.vars, replaceAt(f.child, pos.child, repl))
    case f:Modal                  if pos.head==0 => f.reapply(replaceAt(f.program, pos.child, repl), f.child)
    case f:Modal                  if pos.head==1 => f.reapply(f.program, replaceAt(f.child, pos.child, repl))
    case _ => throw new IllegalArgumentException("replaceAt position " + pos + " of formula " + formula + " may not be defined")
  }

  /** Replace within program at position pos by repl @see [[StaticSemanticsTools.boundAt()]] for same positions */
  def replaceAt(program: Program, pos: PosInExpr, repl:Expression): Program = if (pos==HereP) repl.asInstanceOf[Program] else program match {
    case Assign(x,t)       if pos==PosInExpr(0::Nil) => Assign(repl.asInstanceOf[Variable], t)
    case Assign(x,t)       if pos.head==1 => Assign(x, replaceAt(t, pos.child, repl))
    case DiffAssign(xp,t)  if pos==PosInExpr(0::Nil) => DiffAssign(repl.asInstanceOf[DifferentialSymbol], t)
    case DiffAssign(xp,t)  if pos.head==1 => DiffAssign(xp, replaceAt(t, pos.child, repl))
    case AssignAny(x)      if pos==PosInExpr(0::Nil) => AssignAny(repl.asInstanceOf[Variable])
    case Test(f)           if pos.head==0 => Test(replaceAt(f, pos.child, repl))

    case ODESystem(ode, h) if pos.head==0 => ODESystem(replaceAtODE(ode, pos.child, repl), h)
    case ODESystem(ode, h) if pos.head==1 => ODESystem(ode, replaceAt(h, pos.child, repl))

    // homomorphic cases
    case f:UnaryCompositeProgram  if pos.head==0 => f.reapply(replaceAt(f.child, pos.child, repl))
    case f:BinaryCompositeProgram if pos.head==0 => f.reapply(replaceAt(f.left, pos.child, repl), f.right)
    case f:BinaryCompositeProgram if pos.head==1 => f.reapply(f.left, replaceAt(f.right, pos.child, repl))
    case _ => throw new IllegalArgumentException("replaceAt position " + pos + " of program " + program + " may not be defined")
  }

  private def replaceAtODE(program: DifferentialProgram, pos: PosInExpr, repl:Expression): DifferentialProgram = if (pos==HereP) repl.asInstanceOf[DifferentialProgram] else program match {
    case AtomicODE(xp,t)          if pos==PosInExpr(0::Nil) => AtomicODE(repl.asInstanceOf[DifferentialSymbol], t)
    case AtomicODE(xp,t)          if pos.head==1 => AtomicODE(xp, replaceAt(t, pos.child, repl))
    case DifferentialProduct(l,r) if pos.head==0 => DifferentialProduct(replaceAtODE(l, pos.child, repl), r)
    case DifferentialProduct(l,r) if pos.head==1 => DifferentialProduct(l, replaceAtODE(r, pos.child, repl))
    case _ => throw new IllegalArgumentException("replaceAtODE position " + pos + " of program " + program + " may not be defined")
  }


  // direct split implementation

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
  }} ensuring(r => r._1.getClass == formula.getClass, "Context has identical top types " + formula + " at " + pos)

  //@todo DotProgram would in a sense be the appropriate context
  private val noContext = ProgramConst("noctx")
  private def split(program: Program, pos: PosInExpr): (Program, Expression) = if (pos==HereP) (DotProgram, program) else {program match {
    case Assign(x,t)       if pos==PosInExpr(0::Nil) => (noContext, x)
    case Assign(x,t)       if pos.head==1 => val sp = split(t, pos.child); (Assign(x,sp._1), sp._2)
    case DiffAssign(xp,t)  if pos==PosInExpr(0::Nil) => (noContext, xp)
    case DiffAssign(xp,t)  if pos.head==1 => val sp = split(t, pos.child); (DiffAssign(xp,sp._1), sp._2)
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
  }} ensuring(r => r._1==noContext || r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)

  private val noContextD = DifferentialProgramConst("noctxD")
  private def splitODE(program: DifferentialProgram, pos: PosInExpr): (DifferentialProgram, Expression) = if (pos==HereP) (DotDiffProgram, program) else {program match {
    case AtomicODE(xp,t)          if pos==PosInExpr(0::Nil) => (noContextD, xp)
    case AtomicODE(xp,t)          if pos.head==1 => val sp = split(t, pos.child); (AtomicODE(xp,sp._1), sp._2)
    case DifferentialProduct(l,r) if pos.head==0 => val sp = splitODE(l, pos.child); (DifferentialProduct(sp._1, r), sp._2)
    case DifferentialProduct(l,r) if pos.head==1 => val sp = splitODE(r, pos.child); (DifferentialProduct(l, sp._1), sp._2)
    case _ => throw new IllegalArgumentException("splitODE position " + pos + " of program " + program + " may not be defined")
  }} ensuring(r => r._1==noContextD || r._1.getClass == program.getClass, "Context has identical top types " + program + " at " + pos)
}

/**
 * Convenience wrapper around contexts such as f(.) or p(.) or C{_} etc
 * Created by smitsch on 3/29/15.
 * @author Stefan Mitsch
 */
sealed case class Context[+T <: Expression](ctx: T) {
  import Context.DotProgram
  import Context.DotDiffProgram
  // either a term or a formula context, not both
  require(!(signature(ctx).contains(DotFormula) && signature(ctx).contains(DotTerm)), "Contexts are either DotFormula or DotTerm contexts, not both at once: " + ctx)

  /** Return the result of filling the dot placeholder of this context with expression e */
  //@todo why should this always be a formula?
  def apply(e: Expression): Formula = e match {
    case f: Formula => instantiate(f)
    case t: Term => instantiate(t)
    case a: Program => instantiate(a)
  }

  def apply(c: Context[Formula]): Context[Formula] = new Context(apply(c.ctx))

  /** True if this context has a DotFormula so expects a formula as argument */
  def isFormulaContext = signature(ctx).contains(DotFormula)
  /** True if this context has a DotTerm so expects a term as argument */
  def isTermContext = signature(ctx).contains(DotTerm)
  /** True if this context has a DotProgram so expects a program as argument */
  def isProgramContext = signature(ctx).contains(DotProgram)

  /**
   * Instantiates the context ctx with the formula withF
   * @param withF The formula to instantiate context ctx with.
   * @return The instantiated context ctx{withF}.
   */
  def instantiate(withF: Formula): Formula = {
    assert(!isTermContext, "can only instantiate formulas within a formula context " + this)
    val context = Function("dottingC_", None, Bool, Bool)//@TODO eisegesis  should be Function("dottingC_", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype
    USubst(SubstitutionPair(PredicationalOf(context, DotFormula), ctx) :: Nil)(PredicationalOf(context, withF))
  }

  /**
   * Instantiates the context ctx with the term withT
   * @param withT The term to instantiate context ctx with.
   * @return The instantiated context ctx(withT).
   */
  def instantiate(withT: Term): Formula = {
    assert(!isFormulaContext, "can only instantiate terms within a term context " + this)
    val context = Function("dottingC_", None, Real, Bool)
    USubst(SubstitutionPair(PredOf(context, DotTerm), ctx) :: Nil)(PredOf(context, withT))
  }

  /**
   * Instantiates the context ctx with the program withA
   * @param withA The program to instantiate context ctx with.
   * @return The instantiated context ctx{withA}.
   */
  def instantiate(withA: Program): Formula = {
    assert(!isFormulaContext || isTermContext, "can only instantiate programs within a program context " + this)
    if (withA.isInstanceOf[DifferentialProgram] && !withA.isInstanceOf[ODESystem])
      instantiate(withA.asInstanceOf[DifferentialProgram])
    else
      //@todo why should this be a formula?
      USubst(SubstitutionPair(DotProgram, withA) :: Nil)(ctx).asInstanceOf[Formula]
  }

  /**
   * Instantiates the context ctx with the program withA
   * @param withA The program to instantiate context ctx with.
   * @return The instantiated context ctx{withA}.
   */
  def instantiate(withA: DifferentialProgram): Formula = {
    assert(!isFormulaContext || isTermContext, "can only instantiate differential programs within a differential program context " + this)
    USubst(SubstitutionPair(DotDiffProgram, withA) :: Nil)(ctx) .asInstanceOf[Formula]
  }

  override def toString = "Context{{" + ctx.prettyString + "}}"
}
