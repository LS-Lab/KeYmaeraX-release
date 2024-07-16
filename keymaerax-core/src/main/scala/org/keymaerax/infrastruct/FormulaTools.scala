/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.infrastruct

import org.keymaerax.Logging
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.infrastruct.ExpressionTraversal._

import scala.annotation.{nowarn, tailrec}

/**
 * Tactic tools for formula manipulation and extraction.
 * @author
 *   Andre Platzer
 * @author
 *   Nathan Fulton
 */
object FormulaTools extends Logging {

  /**
   * Split a formula into its conjuncts. Without performing clause form or CNF or DNF transformations.
   * @example
   *   {{{
   *   conjuncts(p() & q() & (r() & (s() | t()&u()))) == List(p(), q(), r(), s()|t()&u())
   *   }}}
   */
  def conjuncts(formula: Formula): List[Formula] = formula match {
    case And(p, q) => conjuncts(p) ++ conjuncts(q)
    case f => List(f)
  }

  /** @see conjuncts(formula: Formula) */
  def conjuncts(formulas: List[Formula]): List[Formula] = formulas.flatMap(conjuncts)

  /**
   * Split a formula into its disjuncts. Without performing clause form or CNF or DNF transformations.
   * @example
   *   {{{
   *   disjuncts(p() | q() | (r() | (s() & (t()|u())))) == List(p(), q(), r(), s()&(t()|u()))
   *   }}}
   */
  def disjuncts(formula: Formula): List[Formula] = formula match {
    case Or(p, q) => disjuncts(p) ++ disjuncts(q)
    case f => List(f)
  }

  /** @see disjuncts(formula: Formula) */
  def disjuncts(formulas: List[Formula]): List[Formula] = formulas.flatMap(disjuncts)

  /**
   * Split a formula into `length` left-hand side conjuncts (-1 for exhaustive splitting), keep right-hand side
   * conjunctions (inverse reduce).
   */
  def leftConjuncts(formula: Formula, length: Int = -1): List[Formula] = {
    def leftConjuncts(formula: Formula, length: Int, count: Int): List[Formula] = formula match {
      case And(p, q) if length == -1 || count < length => leftConjuncts(p, length, count + 1) :+ q
      case f => List(f)
    }
    leftConjuncts(formula, length, 1) // @note not splitting is a list of length 1
  }

  /** Reassociates conjunctions and disjunctions into their default right-associative case. */
  def reassociate(fml: Formula): Formula = fml match {
    case Or(l, r) => (disjuncts(l) ++ disjuncts(r)).map(reassociate).reduceRight(Or)
    case And(l, r) => (conjuncts(l) ++ conjuncts(r)).map(reassociate).reduceRight(And)
    case _ => fml
  }

  /** Gets the (unquantified) kernel part of a quantified formula by peeling off quantifiers. */
  @tailrec
  def kernel(formula: Formula): Formula = formula match {
    case Forall(_, p) => kernel(p)
    case Exists(_, p) => kernel(p)
    case p => p
  }

  /**
   * Convert nested pairs to a list of its deassociated non-pair arguments.
   * {{{
   *   Pair->List[Term]
   * }}}
   */
  def argumentList(term: Term): List[Term] = term match {
    case Pair(a, b) => argumentList(a) ++ argumentList(b)
    case a => List(a)
  }

  /**
   * Convert nested Tuple sorts to a list of its deassociated non-tuple arguments.
   * {{{
   *   Tuple->List[Sort]
   * }}}
   */
  def sortsList(s: Sort): List[Sort] = s match {
    case Tuple(ls, rs) => sortsList(ls) ++ sortsList(rs)
    case _ => s :: Nil
  }

  /**
   * Negation-normal form transforms such that there are no nested negations and that negated atomic comparisons. Also
   * removes implications/equivalences.
   */
  def negationNormalForm(formula: Formula): Formula = formula match {
    case formula: AtomicFormula => formula
    case Not(g: AtomicFormula) => g match {
        case Equal(a, b) => NotEqual(a, b)
        case NotEqual(a, b) => Equal(a, b)
        case Greater(a, b) => LessEqual(a, b)
        case GreaterEqual(a, b) => Less(a, b)
        case Less(a, b) => GreaterEqual(a, b)
        case LessEqual(a, b) => Greater(a, b)
        case True => False
        case False => True
        case _: PredOf => formula
        case _ => throw new IllegalArgumentException("negationNormalForm of formula " + formula + " not implemented")
      }
    case Not(g: CompositeFormula) => g match {
        case Not(f) => negationNormalForm(f)
        case And(p, q) => Or(negationNormalForm(Not(p)), negationNormalForm(Not(q)))
        case Or(p, q) => And(negationNormalForm(Not(p)), negationNormalForm(Not(q)))
        case Imply(p, q) => And(negationNormalForm(p), negationNormalForm(Not(q)))
        case Equiv(p, q) => Or(
            And(negationNormalForm(p), negationNormalForm(Not(q))),
            And(negationNormalForm(Not(p)), negationNormalForm(q)),
          )
        case Forall(vs, p) => Exists(vs, negationNormalForm(Not(p)))
        case Exists(vs, p) => Forall(vs, negationNormalForm(Not(p)))
        case Box(prg, p) => Diamond(prg, negationNormalForm(Not(p)))
        case Diamond(prg, p) => Box(prg, negationNormalForm(Not(p)))
        case _ => throw new IllegalArgumentException("negationNormalForm of formula " + formula + " not implemented")
      }
    case Imply(p, q) => Or(negationNormalForm(Not(p)), negationNormalForm(q))
    case Equiv(p, q) =>
      Or(And(negationNormalForm(p), negationNormalForm(q)), And(negationNormalForm(Not(p)), negationNormalForm(Not(q))))
    case f: BinaryCompositeFormula => f.reapply(negationNormalForm(f.left), negationNormalForm(f.right))
    case f: Quantified => f.reapply(f.vars, negationNormalForm(f.child))
    case f: Modal => f.reapply(f.program, negationNormalForm(f.child))
    case _ => throw new IllegalArgumentException("negationNormalForm of formula " + formula + " not implemented")
  }

  /**
   * The element-wise combinations in `l`, e.g., [ [a,b,c], [p,q] ] ==> [ [a,p], [a,q], [b,p], [b,q], [c,p], [c,q] ].
   */
  def combinations(l: List[List[Formula]]): List[List[Formula]] = l match {
    case Nil => List(Nil)
    case head :: tail => for {
        n <- head
        t <- combinations(tail)
      } yield n :: t
  }

  /** Distributes disjunctions over conjunctions, e.g., a&(b|c) ==> a&b | a&c. */
  def distributeOrOverAnd(fml: Formula): Formula = fml match {
    case Or(l, r) =>
      val (conjunctions, others) = (disjuncts(l) ++ disjuncts(r)).partition(_.isInstanceOf[And])
      (disjuncts(conjunctions.map(distributeOrOverAnd)) ++ others).reduceRight(Or)
    case And(l, r) =>
      val (disjunctions, others) = (conjuncts(l) ++ conjuncts(r)).partition(_.isInstanceOf[Or])
      combinations(disjunctions.map(disjunctiveNormalForm).map(disjuncts))
        .map(o => (o ++ others).reduceRight(And))
        .reduceRight(Or)
    case f => f
  }

  /** Turns `fml` into disjunctive normal form. */
  def disjunctiveNormalForm(fml: Formula): Formula = reassociate(distributeOrOverAnd(negationNormalForm(fml)))

  /**
   * Read off all atomic subformulas of `formula`. Will not descend into programs to find even further atomic formulas
   * since they are not directly subformulas.
   * @see
   *   [[negationNormalForm()]]
   */
  def atomicFormulas(formula: Formula): List[AtomicFormula] = formula match {
    case formula: AtomicFormula => List(formula)
    case f: UnaryCompositeFormula => atomicFormulas(f.child)
    case f: BinaryCompositeFormula => atomicFormulas(f.left) ++ atomicFormulas(f.right)
    case f: Quantified => atomicFormulas(f.child)
    case f: Modal => atomicFormulas(f.child)
    case _ => throw new IllegalArgumentException("atomicFormulas of formula " + formula + " not implemented")
  }

  /**
   * Returns the polarity of the subformula at position pos in formula.
   * @param formula
   *   The formula.
   * @param pos
   *   The position within formula for which the polarity is searched.
   * @return
   *   -1 for negative polarity, 1 for positive polarity, 0 for unknown polarity.
   */
  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  def polarityAt(formula: Formula, pos: PosInExpr): Int =
    if (pos.pos.isEmpty) 1
    else formula match {
      case Not(g) =>
        require(pos.head == 0, "Unary operator must have position head 0, but was " + pos); -polarityAt(g, pos.child)
      case Imply(l, _) if pos.head == 0 => -polarityAt(l, pos.child)
      case Imply(_, r) if pos.head == 1 => polarityAt(r, pos.child)
      case Equiv(_, _) => 0
      case PredicationalOf(_, _) => 0
      case f: UnaryCompositeFormula =>
        require(pos.head == 0, "Unary operator must have position head 0, but was " + pos);
        polarityAt(f.child, pos.child)
      case f: BinaryCompositeFormula if pos.head == 0 => polarityAt(f.left, pos.child)
      case f: BinaryCompositeFormula if pos.head == 1 => polarityAt(f.right, pos.child)
      case f: Modal if pos.head == 1 => polarityAt(f.child, pos.child)
      case _: Modal if pos.head == 0 => logger.warn("Polarity within programs not yet implemented " + formula); 0
//      case f: Modal                  => require(pos.head == 1, "Modal operator must have position head 1, but was " + pos); polarityAt(f.child, pos.child)
      case f: Quantified =>
        require(pos.head == 0, "Quantified must have position head 0, but was " + pos); polarityAt(f.child, pos.child)
    }

  /**
   * Returns a formula with equivalences turned into implications such that the polarity of the subformula at position
   * pos has the specified polarity. Creates a variation of this formula which has equivalences reoriented such that the
   * polarity of the subformula at position pos in the resulting formula will be the desired polarity.
   * @param formula
   *   The formula.
   * @param pos
   *   The position within formula for which the polarity is supposed to be changed to the desired polarity.
   * @param polarity
   *   The desired polarity, must be either 1 (positive polarity) or -1 (negative polarity).
   * @return
   *   The formula with equivalences turned into implications.
   */
  @nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
  def makePolarityAt(formula: Formula, pos: PosInExpr, polarity: Int): Formula = {
    require(polarity == 1 || polarity == -1, "Polarity must be either positive or negative")
    if (pos.pos.isEmpty && polarity == 1) formula
    else if (pos.pos.isEmpty && polarity == -1) Not(formula)
    else formula match {
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity == -1 => Imply(l, r)
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity == 1 => Imply(r, l)
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity == 0 =>
        Imply(makePolarityAt(l, pos.child, -polarity), r)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity == -1 => Imply(r, l)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity == 1 => Imply(l, r)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity == 0 =>
        Imply(l, makePolarityAt(r, pos.child, polarity))
      case f: UnaryCompositeFormula =>
        require(pos.head == 0, "Unary operator must have position head 0, but was " + pos);
        f.reapply(makePolarityAt(f.child, pos.child, polarity))
      case f: BinaryCompositeFormula if pos.head == 0 => f.reapply(makePolarityAt(f.left, pos.child, polarity), f.right)
      case f: BinaryCompositeFormula if pos.head == 1 => f.reapply(f.left, makePolarityAt(f.right, pos.child, polarity))
      case f: Modal =>
        require(pos.head == 1, "Modal operator must have position head 1, but was " + pos);
        f.reapply(f.program, makePolarityAt(f.child, pos.child, polarity))
      case f: Quantified =>
        require(pos.head == 0, "Quantified must have position head 0, but was " + pos);
        f.reapply(f.vars, makePolarityAt(f.child, pos.child, polarity))
    }
  }

  /**
   * Returns the first (i.e., left-most) position of `sub` within `expr`, if any.
   * @param expr
   *   The expression to search for containment of `sub`.
   * @param sub
   *   The sub-expression.
   * @return
   *   The first position, or None if `sub` is not contained in `expr`.
   */
  @nowarn("msg=match may not be exhaustive")
  def posOf(expr: Expression, sub: Expression): Option[PosInExpr] = {
    var pos: Option[PosInExpr] = None
    sub match {
      case _: Formula => ExpressionTraversal.traverseExpr(
          new ExpressionTraversalFunction() {
            override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
              if (e == sub) { pos = Some(p); Left(Some(ExpressionTraversal.stop)) }
              else Left(None)
          },
          expr,
        )
      case _: Term => ExpressionTraversal.traverseExpr(
          new ExpressionTraversalFunction() {
            override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
              if (e == sub) { pos = Some(p); Left(Some(ExpressionTraversal.stop)) }
              else Left(None)
          },
          expr,
        )
      case _: Program => ExpressionTraversal.traverseExpr(
          new ExpressionTraversalFunction() {
            override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] =
              if (e == sub) { pos = Some(p); Left(Some(ExpressionTraversal.stop)) }
              else Left(None)
          },
          expr,
        )
    }
    pos
  }

  /** Collects the subpositions of formula that satisfy condition cond. Ordered: reverse depth (deepest first). */
  def posOf(formula: Formula, cond: Expression => Boolean): List[PosInExpr] = {
    var positions: List[PosInExpr] = Nil
    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
          if (cond(e)) { positions = p :: positions; Left(None) }
          else Left(None)
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] =
          if (cond(t)) { positions = p :: positions; Left(None) }
          else Left(None)
      },
      formula,
    )
    positions
  }

  def posOfTerm(term: Term, cond: Term => Boolean): List[PosInExpr] = {
    var positions: List[PosInExpr] = Nil
    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] =
          if (cond(t)) { positions = p :: positions; Left(None) }
          else Left(None)
      },
      term,
    )
    positions
  }

  /** Finds the closest parent to `pos` in `formula` that is a formula. */
  def parentFormulaPos(pos: PosInExpr, fml: Formula): PosInExpr = {
    var result = pos
    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          if (p.isPrefixOf(pos)) {
            result = p
            Left(None)
          } else if (pos.isPrefixOf(p)) { Left(Some(stop)) }
          else { Left(None) }
        }
      },
      fml,
    )
    result
  }

  /**
   * Read off the set of all possible singularities coming from divisors or negative powers.
   * @example
   *   {{{
   *   singularities("x>5/b+2".asFormula)==Set(b)
   *   singularities("x/y>z/2+8/(a+b) & [x:=a/c;]x+1/(3*d)>5/3".asFormula)==Set(y,a+b,c,3*d)
   *   }}}
   */
  @nowarn("msg=match may not be exhaustive")
  def singularities(e: Expression): Set[Term] = e match {
    case t: Term => singularities(t)
    case f: Formula => singularities(f)
    case p: Program => singularities(p)
  }

  def singularities(term: Term): Set[Term] = term match {
    case Nothing | DotTerm(_, _) | Number(_) => Set.empty
    case _: Variable => Set.empty
    case _: UnitFunctional => Set.empty
    case FuncOf(_, t) => singularities(t)
    // homomorphic cases
    case f: UnaryCompositeTerm => singularities(f.child)
    case f @ Divide(_, Number(n)) if n != 0 => singularities(f.left) ++ singularities(f.right)
    case f: Divide => singularities(f.left) ++ singularities(f.right) + f.right
    case f @ Power(_, Number(n)) if n >= 0 => singularities(f.left) ++ singularities(f.right)
    case f @ Power(_, Number(n)) if n < 0 => singularities(f.left) ++ singularities(f.right) + f.left
    case f: BinaryCompositeTerm => singularities(f.left) ++ singularities(f.right)
    case _ => throw new IllegalArgumentException("singularities of term " + term + " not implemented")
  }

  def singularities(formula: Formula): Set[Term] = formula match {
    // base cases
    case True | False => Set.empty
    case _: UnitPredicational | DotFormula => Set.empty
    case PredOf(_, t) => singularities(t)
    case PredicationalOf(_, t) => singularities(t)
    // pseudo-homomorphic cases
    case f: ComparisonFormula => singularities(f.left) ++ singularities(f.right)
    // homomorphic cases
    case f: UnaryCompositeFormula => singularities(f.child)
    case f: BinaryCompositeFormula => singularities(f.left) ++ singularities(f.right)
    case f: Quantified => singularities(f.child)
    case f: Modal => singularities(f.program) ++ singularities(f.child)
    case _ => throw new IllegalArgumentException("singularities of formula " + formula + " not implemented")
  }

  def singularities(program: Program): Set[Term] = program match {
    case Assign(_, t) => singularities(t)
    case AssignAny(_) => Set.empty
    case Test(f) => singularities(f)
    case ODESystem(ode, h) => singularities(ode) ++ singularities(h)
    // homomorphic cases
    case f: UnaryCompositeProgram => singularities(f.child)
    case f: BinaryCompositeProgram => singularities(f.left) ++ singularities(f.right)
    case _ => throw new IllegalArgumentException("singularities of program " + program + " not implemented")
  }

  private def singularities(program: DifferentialProgram): Set[Term] = program match {
    case AtomicODE(_, t) => singularities(t)
    case _: DifferentialProgramConst => Set.empty
    case f: DifferentialProduct => singularities(f.left) ++ singularities(f.right)
    case _ => throw new IllegalArgumentException("singularities of program " + program + " not implemented")
  }

  /**
   * Check whether given program is dual-free, so a hybrid system and not a proper hybrid game.
   * @see
   *   [[SubstitutionPair.dualFree]]
   */
  @nowarn("msg=match may not be exhaustive")
  def dualFree(program: Program): Boolean = program match {
    case _: ProgramConst => false
    case _: SystemConst => true
    case Assign(_, _) => true
    case AssignAny(_) => true
    case Test(_) => true /* even if f contains duals, since they're different nested games) */
    case ODESystem(_, _) => true /*|| dualFreeODE(a)*/ /* @note Optimized assuming no differential games */
    case Choice(a, b) => dualFree(a) && dualFree(b)
    case Compose(a, b) => dualFree(a) && dualFree(b)
    case Loop(a) => dualFree(a)
    case Dual(_) => false
  }

  /** Check whether `fml` is dual-free. */
  def dualFree(fml: Formula): Boolean = allProgramsPass(fml, dualFree)

  /** Check whether `sequent` is dual-free. */
  def dualFree(sequent: Sequent): Boolean = dualFree(sequent.toFormula)

  /** Check whether given `program` contains literal [[Dual]]. */
  def literalDualFree(program: Program): Boolean = program match {
    case Dual(_) => false
    case Choice(a, b) => literalDualFree(a) && literalDualFree(b)
    case Compose(a, b) => literalDualFree(a) && literalDualFree(b)
    case Loop(a) => literalDualFree(a)
    case _ => true
  }

  /** Check whether `fml` contains literal [[Dual]]. */
  def literalDualFree(fml: Formula): Boolean = allProgramsPass(fml, literalDualFree)

  /** Check whether `sequent` contains literal [[Dual]]. */
  def literalDualFree(sequent: Sequent): Boolean = literalDualFree(sequent.toFormula)

  /** Returns true if all programs in `fml` pass the `check`, false otherwise. */
  private def allProgramsPass(fml: Formula, check: Program => Boolean): Boolean = ExpressionTraversal
    .traverse(
      new ExpressionTraversalFunction() {
        override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
          if (check(e)) Left(None) else Left(Some(stop))
        }
      },
      fml,
    )
    .isDefined // @note traversal stops with None if check is violated at some point during the traversal

  /**
   * Returns all terms `b^e` such that e is not a natural number occurring in given formula .
   * @note
   *   This is soundness-critical.
   * @author
   *   Nathan Fulton
   */
  def unnaturalPowers(f: Formula): List[(Term, PosInExpr)] = {
    val problematicExponents = scala.collection.mutable.ListBuffer[(Term, PosInExpr)]()
    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
          case Power(_, Number(n)) if n.isValidInt && n >= 0 => Left(None)
          case Power(base, exp) => problematicExponents += Power(base, exp) -> p; Left(None)
          case _ => Left(None)
        }
      },
      f,
    )
    problematicExponents.toList
  }

  /** Returns a set of variables that are arguments to any application of function 'fn' in the formula `fml`. */
  def argsOf(fn: Function, fml: Formula): Set[Term] = {
    var args = Set[Term]()
    ExpressionTraversal.traverse(
      new ExpressionTraversal.ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
          case FuncOf(mf: Function, t: Term) if mf == fn => args += t; Left(None)
          case _ => Left(None)
        }
      },
      fml,
    )
    args
  }

  /** Returns the formula in negation normal form, strengthened by replacing inequalities with strict inequalities. */
  @nowarn("msg=match may not be exhaustive")
  def interior(fml: Formula): Formula = negationNormalForm(fml) match {
    case LessEqual(a, b) => Less(a, b)
    case GreaterEqual(a, b) => Greater(a, b)
    case _: Greater => fml
    case _: Less => fml
    case And(a, b) => And(interior(a), interior(b))
    case Or(a, b) => Or(interior(a), interior(b))
    case Equal(_, _) => False
    case NotEqual(a, b) => NotEqual(a, b)
    case True => True
    case False => False
  }

  /** Returns the formula in negation normal form, weakened by replacing strict inequalities with inequalities. */
  @nowarn("msg=match may not be exhaustive")
  def closure(fml: Formula): Formula = negationNormalForm(fml) match {
    case Less(a, b) => LessEqual(a, b)
    case Greater(a, b) => GreaterEqual(a, b)
    case _: GreaterEqual => fml
    case _: LessEqual => fml
    case And(a, b) => And(closure(a), closure(b))
    case Or(a, b) => Or(closure(a), closure(b))
    case Equal(a, b) => Equal(a, b)
    case NotEqual(_, _) => True
    case True => True
    case False => False
  }

  /** prepends all-quantifiers over given variables to a formula */
  def quantifyForall(xs: List[Variable], fml: Formula): Formula = xs match {
    case Nil => fml
    case x :: xs => Forall(List(x), quantifyForall(xs, fml))
  }

  /** prepends all-quantifiers over given variables to a formula */
  def quantifyExists(xs: List[Variable], fml: Formula): Formula = xs match {
    case Nil => fml
    case x :: xs => Exists(List(x), quantifyExists(xs, fml))
  }

  /**
   * Difference between symbols in `f` and `g`, returns a tuple of: symbols of f not in g, symbols of g not in f, their
   * union
   */
  def symbolsDiff(f: Formula, g: Formula): (Set[NamedSymbol], Set[NamedSymbol], Set[NamedSymbol]) = {
    if (f == g) (Set.empty[NamedSymbol], Set.empty[NamedSymbol], Set.empty[NamedSymbol])
    else {
      val fs = StaticSemantics.symbols(f)
      val gs = StaticSemantics.symbols(g)
      (fs -- gs, gs -- fs, (fs ++ gs) -- fs.intersect(gs))
    }
  }

  /**
   * Union of pairwise symbol difference in `fs` and `gs`, returns a tuple of: symbols of fs not in gs, symbols of gs
   * not in fs, their union
   */
  def symbolsDiff(fs: Seq[Formula], gs: Seq[Formula]): (Set[NamedSymbol], Set[NamedSymbol], Set[NamedSymbol]) = {
    fs.zip(gs)
      .map({ case (f, g) => symbolsDiff(f, g) })
      .reduce[(Set[NamedSymbol], Set[NamedSymbol], Set[NamedSymbol])]({ case ((a1, b1, c1), (a2, b2, c2)) =>
        (a1 ++ a2, b1 ++ b2, c1 ++ c2)
      })
  }

}
