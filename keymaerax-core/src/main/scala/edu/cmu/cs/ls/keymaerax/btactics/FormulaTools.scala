/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}

import scala.collection.immutable.List

/**
 * Tactic tools for formula manipulation and extraction.
 * @author Andre Platzer
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

  /**
    * Gets the (unquantified) kernel part of a quantified formula by peeling off quantifiers.
    */
  def kernel(formula: Formula): Formula = formula match {
    case Forall(vars, p) => kernel(p)
    case Exists(vars, p) => kernel(p)
    case p => p
  }

  /** Convert nested pairs to a list of its deassociated non-pair arguments.
    * {{{
    *   Pair->List[Term]
    * }}} */
  def argumentList(term: Term): List[Term] = term match {
    case Pair(a,b) => argumentList(a) ++ argumentList(b)
    case a => List(a)
  }

  /** Convert nested Tuple sorts to a list of its deassociated non-tuple arguments.
    * {{{
    *   Tuple->List[Sort]
    * }}} */
  def sortsList(s: Sort): List[Sort] = s match {
    case Tuple(ls, rs) => sortsList(ls) ++ sortsList(rs)
    case _ => s :: Nil
  }

  /** Negation-normal form transforms such that there are no nested negations and that
    * negated atomic comparisons.
    * Also removes implications/equivalences. */
  def negationNormalForm(formula: Formula): Formula = formula match {
    case formula: AtomicFormula => formula
    case Not(g:AtomicFormula) => g match {
      case Equal(a,b) => NotEqual(a,b)
      case NotEqual(a,b) => Equal(a,b)
      case Greater(a,b) => LessEqual(a,b)
      case GreaterEqual(a,b) => Less(a,b)
      case Less(a,b) => GreaterEqual(a,b)
      case LessEqual(a,b) => Greater(a,b)
    }
    case Not(g:CompositeFormula) => g match {
      case Not(f) => negationNormalForm(f)
      case And(p,q) => Or(negationNormalForm(Not(p)), negationNormalForm(Not(q)))
      case Or(p,q) => And(negationNormalForm(Not(p)), negationNormalForm(Not(q)))
      case Imply(p,q) => And(negationNormalForm(p), negationNormalForm(Not(q)))
      case Equiv(p,q) => Or(
        And(negationNormalForm(p), negationNormalForm(Not(q))),
        And(negationNormalForm(Not(p)), negationNormalForm(q))
      )
    }
    case Imply(p,q) => Or(negationNormalForm(Not(p)), negationNormalForm(q))
    case Equiv(p,q) => Or(
      And(negationNormalForm(p), negationNormalForm(q)),
      And(negationNormalForm(Not(p)), negationNormalForm(Not(q)))
    )
    case f:BinaryCompositeFormula => f.reapply(negationNormalForm(f.left), negationNormalForm(f.right))
    case f:Quantified             => f.reapply(f.vars, negationNormalForm(f.child))
    case f:Modal                  => f.reapply(f.program, negationNormalForm(f.child))
    case _ => throw new IllegalArgumentException("negationNormalForm of formula " + formula + " not implemented")
  }

  /** Read off all atomic subformulas of `formula`.
    * Will not descend into programs to find even further atomic formulas since they are not directly subformulas.
    * @see [[negationNormalForm()]] */
  def atomicFormulas(formula: Formula): List[AtomicFormula] = formula match {
    case formula: AtomicFormula   => List(formula)
    case f:UnaryCompositeFormula  => atomicFormulas(f.child)
    case f:BinaryCompositeFormula => atomicFormulas(f.left) ++ atomicFormulas(f.right)
    case f:Quantified             => atomicFormulas(f.child)
    case f:Modal                  => atomicFormulas(f.child)
    case _ => throw new IllegalArgumentException("atomicFormulas of formula " + formula + " not implemented")
  }

  /**
   * Returns the polarity of the subformula at position pos in formula.
   * @param formula The formula.
   * @param pos The position within formula for which the polarity is searched.
   * @return -1 for negative polarity, 1 for positive polarity, 0 for unknown polarity.
   */
  def polarityAt(formula: Formula, pos: PosInExpr): Int =
    if (pos.pos.isEmpty) 1 else formula match {
      case Not(g) => require(pos.head == 0, "Unary operator must have position head 0, but was " + pos); -polarityAt(g, pos.child)
      case Imply(l, _) if pos.head == 0 => -polarityAt(l, pos.child)
      case Imply(_, r) if pos.head == 1 => polarityAt(r, pos.child)
      case Equiv(_, _) => 0
      case PredicationalOf(_,_) => 0
      case f: UnaryCompositeFormula  => require(pos.head == 0, "Unary operator must have position head 0, but was " + pos); polarityAt(f.child, pos.child)
      case f: BinaryCompositeFormula if pos.head == 0 => polarityAt(f.left, pos.child)
      case f: BinaryCompositeFormula if pos.head == 1 => polarityAt(f.right, pos.child)
      case f: Modal                  if pos.head == 1 => polarityAt(f.child, pos.child)
      case f: Modal                  if pos.head == 0 => println("Polarity within programs not yet implemented " + formula); 0
//      case f: Modal                  => require(pos.head == 1, "Modal operator must have position head 1, but was " + pos); polarityAt(f.child, pos.child)
      case f: Quantified             => require(pos.head == 0, "Quantified must have position head 0, but was " + pos); polarityAt(f.child, pos.child)
    }

  /**
   * Returns a formula with equivalences turned into implications such that the polarity of the subformula at position
   * pos has the specified polarity.
   * Creates a variation of this formula which has equivalences reoriented such that the polarity
   * of the subformula at position pos in the resulting formula will be the desired polarity.
   * @param formula The formula.
   * @param pos The position within formula for which the polarity is supposed to be changed to the desired polarity.
   * @param polarity The desired polarity, must be either 1 (positive polarity) or -1 (negative polarity).
   * @return The formula with equivalences turned into implications.
   */
  def makePolarityAt(formula: Formula, pos: PosInExpr, polarity: Int): Formula = {
    require(polarity == 1 || polarity == -1, "Polarity must be either positive or negative")
    if (pos.pos.isEmpty && polarity == 1) formula
    else if (pos.pos.isEmpty && polarity == -1) Not(formula)
    else formula match {
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity == -1 => Imply(l, r)
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity ==  1 => Imply(r, l)
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity ==  0 => Imply(makePolarityAt(l, pos.child, -polarity), r)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity == -1 => Imply(r, l)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity ==  1 => Imply(l, r)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity ==  0 => Imply(l, makePolarityAt(r, pos.child, polarity))
      case f: UnaryCompositeFormula  => require(pos.head == 0, "Unary operator must have position head 0, but was " + pos); f.reapply(makePolarityAt(f.child, pos.child, polarity))
      case f: BinaryCompositeFormula if pos.head == 0 => f.reapply(makePolarityAt(f.left, pos.child, polarity), f.right)
      case f: BinaryCompositeFormula if pos.head == 1 => f.reapply(f.left, makePolarityAt(f.right, pos.child, polarity))
      case f: Modal                  => require(pos.head == 1, "Modal operator must have position head 1, but was " + pos); f.reapply(f.program, makePolarityAt(f.child, pos.child, polarity))
      case f: Quantified             => require(pos.head == 0, "Quantified must have position head 0, but was " + pos); f.reapply(f.vars, makePolarityAt(f.child, pos.child, polarity))
    }
  }

  /**
   * Returns the first (i.e., left-most) position of subFormula within formula, if any.
   * @param formula The formula to search for containment of subformula.
   * @param subFormula The subformula.
   * @return The first position, or None if subformula is not contained in formula.
   */
  def posOf(formula: Formula, subFormula: Formula): Option[PosInExpr] = {
    var pos: Option[PosInExpr] = None
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
        if (e == subFormula) { pos = Some(p); Left(Some(ExpressionTraversal.stop)) }
        else Left(None)
    }, formula)
    pos
  }

  /** Collects the subpositions of formula that satisfy condition cond. Ordered: reverse depth (deepest first). */
  def posOf(formula: Formula, cond: Expression=>Boolean): List[PosInExpr] = {
    var positions: List[PosInExpr] = Nil
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
        if (cond(e)) { positions = p :: positions; Left(None) } else Left(None)
      override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] =
        if (cond(t)) { positions = p :: positions; Left(None) } else Left(None)
    }, formula)
    positions
  }

  /** Read off the set of all possible singularities coming from divisors or negative powers.
    * @example {{{
    *           singularities("x>5/b+2".asFormula)==Set(b)
    *           singularities("x/y>z/2+8/(a+b) & [x:=a/c;]x+1/(3*d)>5/3".asFormula)==Set(y,a+b,c,3*d)
    * }}}
    */
  def singularities(e: Expression): Set[Term] = e match {
    case t: Term    => singularities(t)
    case f: Formula => singularities(f)
    case p: Program => singularities(p)
  }

  def singularities(term: Term): Set[Term] = term match {
    case Nothing | DotTerm(_) | Number(_) => Set.empty
    case _: Variable     => Set.empty
    case _: UnitFunctional => Set.empty
    case FuncOf(f,t)     => singularities(t)
    // homomorphic cases
    case f:UnaryCompositeTerm  => singularities(f.child)
    case f@Divide(_,Number(n)) if n!=0 => singularities(f.left) ++ singularities(f.right)
    case f:Divide                      => singularities(f.left) ++ singularities(f.right) + f.right
    case f@Power(_,Number(n)) if n>=0  => singularities(f.left) ++ singularities(f.right)
    case f@Power(_,Number(n)) if n<0   => singularities(f.left) ++ singularities(f.right) + f.left
    case f:BinaryCompositeTerm         => singularities(f.left) ++ singularities(f.right)
    case _ => throw new IllegalArgumentException("singularities of term " + term + " not implemented")
  }

  def singularities(formula: Formula): Set[Term] = formula match {
    // base cases
    case True | False         => Set.empty
    case _: UnitPredicational | DotFormula => Set.empty
    case PredOf(p,t)          => singularities(t)
    case PredicationalOf(c,t) => singularities(t)
    // pseudo-homomorphic cases
    case f:ComparisonFormula  => singularities(f.left) ++ singularities(f.right)
    // homomorphic cases
    case f:UnaryCompositeFormula  => singularities(f.child)
    case f:BinaryCompositeFormula => singularities(f.left) ++ singularities(f.right)
    case f:Quantified             => singularities(f.child)
    case f:Modal                  => singularities(f.program) ++ singularities(f.child)
    case _ => throw new IllegalArgumentException("singularities of formula " + formula + " not implemented")
  }

  def singularities(program: Program): Set[Term] = program match {
    case Assign(x,t)       => singularities(t)
    case AssignAny(x)      => Set.empty
    case Test(f)           => singularities(f)
    case ODESystem(ode, h) => singularities(ode) ++ singularities(h)
    // homomorphic cases
    case f:UnaryCompositeProgram  => singularities(f.child)
    case f:BinaryCompositeProgram => singularities(f.left) ++ singularities(f.right)
    case _ => throw new IllegalArgumentException("singularities of program " + program + " not implemented")
  }

  private def singularities(program: DifferentialProgram): Set[Term] = program match {
    case AtomicODE(xp,t)       => singularities(t)
    case _:DifferentialProgramConst => Set.empty
    case f:DifferentialProduct => singularities(f.left) ++ singularities(f.right)
    case _ => throw new IllegalArgumentException("singularities of program " + program + " not implemented")
  }

  /** Check whether given program is dual-free, so a hybrid system and not a proper hybrid game. */
  def dualFree(program: Program): Boolean = program match {
    case a: ProgramConst => false
    case a: SystemConst  => true
    case Assign(x, e)    => true
    case AssignAny(x)    => true
    case Test(f)         => true /* even if f contains duals, since they're different nested games) */
    case ODESystem(a, h) => true /*|| dualFreeODE(a)*/ /* @note Optimized assuming no differential games */
    case Choice(a, b)    => dualFree(a) && dualFree(b)
    case Compose(a, b)   => dualFree(a) && dualFree(b)
    case Loop(a)         => dualFree(a)
    case Dual(a)         => false
  }

}