/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.TacticInapplicableFailure
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr, ExpressionTraversal, Position}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}

import java.util.Date

/**
  * Some commonly useful helper utilities for basic tactic implementations.
  */
object TacticHelper {

  /** Returns a fresh index for `name` in formula `f`. */
  def freshIndexInFormula(name: String, f: Formula): Option[Int] = freshIndexInExpression(name, f)
  /** Returns a fresh index for `name` in program `a`. */
  def freshIndexInProgram(name: String, a: Program): Option[Int] = freshIndexInExpression(name, a)
  /** Returns a fresh index for `name` in Term `t`. */
  def freshIndexInTerm(name: String, t: Term): Option[Int] = freshIndexInExpression(name, t)

  /** Returns a fresh index for `name` in expression `e`. */
  def freshIndexInExpression(name: String, e: Expression): Option[Int] = {
    var maxIdx: Option[Int] = None

    def max(n: NamedSymbol, max: Option[Int]): Option[Int] = {
      if (n.name == name) maxIdx match {
        case Some(i) => Some(Math.max(maxIdx.getOrElse(-1), n.index.getOrElse(-1)))
        case None => Some(n.index.getOrElse(-1))
      }
      else max
    }

    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        maxIdx = e match {
          case PredOf(fn, _)          => max(fn, maxIdx)
          case PredicationalOf(fn, _) => max(fn, maxIdx)
          case p: UnitPredicational   => max(p, maxIdx)
          case d@DotFormula           => max(d, maxIdx)
          case _ => maxIdx
        }
        Left(None)
      }
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        maxIdx = e match {
          case v: Variable       => max(v, maxIdx)
          case FuncOf(fn, _)     => max(fn, maxIdx)
          case d: DotTerm        => max(d, maxIdx)
          case f: UnitFunctional => max(f, maxIdx)
          case _ => maxIdx
        }
        Left(None)
      }
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        maxIdx = e match {
          case c: ProgramConst             => max(c, maxIdx)
          case c: SystemConst              => max(c, maxIdx)
          case c: DifferentialProgramConst => max(c, maxIdx)
          case _ => maxIdx
        }
        Left(None)
      }
    }, e)

    maxIdx.map(_ + 1)
  }


  /** Returns the symbols in `f`. */
  @deprecated("Use StaticSemantics.symbols instead")
  def symbols(f: Formula): Set[NamedSymbol] = StaticSemantics.symbols(f)

  /** Returns the symbols in sequent `s`. */
  @deprecated("Use StaticSemantics.symbols instead")
  def names(s: Sequent): Set[NamedSymbol] = StaticSemantics.symbols(s)

  /** Returns a fresh index for `name` in sequent `s`. */
  def freshIndexInSequent(name: String, s: Sequent): Option[Int] =
    if (s.ante.isEmpty && s.succ.isEmpty) None
    // optimization with fold seems to not makes any difference, not even on huge sequents
    else (s.ante ++ s.succ).map(freshIndexInFormula(name, _)).max

  /** Returns a named symbol with `t.name` and fresh index provided by `freshIndex`.  */
  def freshNamedSymbol[T <: NamedSymbol](t: T, freshIndex: String => Option[Int]): T =
    freshIndex(t.name) match {
      case Some(i) => t match {
        case BaseVariable(vName, _, vSort) => Variable(vName, Some(i), vSort).asInstanceOf[T]
        case DifferentialSymbol(v) => DifferentialSymbol(Variable(v.name, Some(i), v.sort)).asInstanceOf[T]
        case Function(fName, _, fDomain, fSort, false) => Function(fName, Some(i), fDomain, fSort).asInstanceOf[T]
        case DotTerm(s, _) => DotTerm(s, Some(i)).asInstanceOf[T]
        case _ => throw new IllegalArgumentException("Cannot obtain fresh symbol, since " + t.getClass + " does not have index")
      }
      case None => t
    }
  /** Returns a named symbol with name `t.name` and fresh index in formula `f`. */
  def freshNamedSymbol[T <: NamedSymbol](t: T, f: Formula): T = freshNamedSymbol(t, freshIndexInFormula(_, f))
  /** Returns a named symbol with name `t.name` and fresh index in program `a`. */
  def freshNamedSymbol[T <: NamedSymbol](t: T, a: Program): T = freshNamedSymbol(t, freshIndexInProgram(_, a))
  /** Returns a named symbol with name `t.name` and fresh index in sequent `s`. */
  def freshNamedSymbol[T <: NamedSymbol](t: T, s: Sequent): T = freshNamedSymbol(t, freshIndexInSequent(_, s))

  /** Returns a list of formulas that are constants so should get as invariants for free by [[HilbertCalculus.V]]. */
  def propertiesOfConstants(s: Sequent, pos: SeqPos) : List[Formula] = {
    val constants : Set[Variable] = invariantSymbols(s, pos)
    s.ante.filter(f => (StaticSemantics.freeVars(f) -- constants).isEmpty).toList
  } //@todo tests and then use this function to determine which formulas should be added to a loop invariant.

  /** Returns the set of variables we should consider as constant in invariant proofs for the modality located at pos. */
  private def invariantSymbols(s: Sequent, pos: SeqPos) : Set[Variable] = {
    val (program: Program, formula: Formula) = s(pos) match {
      case Box(p,f) => (p,f)
      case Diamond(p,f) => (p,f)
      case _ => assert(false, "s(pos) should hve form [a]p or <a>p.")
    }

    val freeInGamma = s.ante.map(StaticSemantics.freeVars).fold(SetLattice.bottom)(_ ++ _)
    val freeInModality = StaticSemantics.freeVars(s(pos))
    val boundInProgram = StaticSemantics.boundVars(program)

    //@todo not sure about that last term.
    freeInModality.intersect(freeInGamma).intersect(SetLattice.allVars -- boundInProgram).symbols
  }

  /** Returns true iff {{{v^n}}} s.t. n!=0, n!=1 occurs in {{{term}}}*/
  def variableOccursWithExponent(v: Variable, term: Term): Boolean = {
    var occursWithExponent = false
    val fn = new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = asMonomial(t) match {
        case Some((_, x, Some(power))) if power != Number(1) && power != Number(0) && x==v =>
          occursWithExponent = true
          Left(None)
        case _ => Left(None)
      }
    }
    ExpressionTraversal.traverse(fn, term).getOrElse(throw new TacticInapplicableFailure("Could not determine whether this variable occurs with an exponent."))
    occursWithExponent
  }

  /** Transforms monomials in e using the xform function. */
  def transformMonomials(e: Term, xform: Term => Term): Term = {
    val fn = new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, term: Term): Either[Option[StopTraversal], Term] = {
        if(isMonomial(term)) Right(xform(term))
        else Left(None)
      }
    }
    ExpressionTraversal.traverse(fn, e).getOrElse(throw new TacticInapplicableFailure("Expected transformMonomials to succeed."))
  }

  /** Returns monomial iff t is (approximately, locally) a monomial; i.e., has the form {{{coeff(|x|)*x^exp(|x|)}}} where coeff and exp are optional.
    * @return Optional coefficient, variable, optional exponent; or None if this isn't a monomial
    */
  def asMonomial(t: Term): Option[(Option[Term], Variable, Option[Term])] = t match {
    case v: Variable => Some(None, v, None)
    case Times(coeff: Term, v: Variable) if !StaticSemantics.vars(coeff).contains(v) => Some(Some(coeff), v, None)
    case Times(coeff: Term, Power(v:Variable, exp:Term))
      if !StaticSemantics.vars(coeff).contains(v) && !StaticSemantics.vars(exp).contains(v) => Some(Some(coeff), v, Some(exp))
    case _ => None
  }

  def isMonomial(t:Term): Boolean = asMonomial(t).nonEmpty

  /** Computes substitution with position of `name(old)` in sequent `seq` (either `replCandidate` or a previously
    * introduced substitution that is present in `seq`). Returns (repl, replPos, nextReplCandidate). */
  def findSubst(what: Term, replCandidate: Variable, seq: Sequent): (Variable, Option[Position], Variable) = {
    val (repl: Variable, replPos: Option[Position], nextReplCandidate: Variable) = what match {
      case v: Variable =>
        seq.ante.zipWithIndex.find({
          //@note heuristic to avoid new ghosts on repeated name(v) usage
          case (Equal(x0: Variable, x: Variable), _) => v==x && x0.name==x.name
          case _ => false
        }).map[(Variable, Option[Position], Variable)]({ case (Equal(x0: Variable, _), i) => (x0, Some(AntePosition.base0(i)), replCandidate) }).
          getOrElse((TacticHelper.freshNamedSymbol(v, seq), None, replCandidate))
      case _ =>
        seq.ante.zipWithIndex.find({
          //@note heuristic to avoid new ghosts on repeated old(v) usage
          case (Equal(x0: Variable, t: Term), _) => what==t && x0.name == replCandidate.name
          case _ => false
        }).map[(Variable, Option[Position], Variable)]({ case (Equal(x0: Variable, _), i) => (x0, Some(AntePosition.base0(i)), replCandidate) }).
          getOrElse({
            (replCandidate, None, Variable(replCandidate.name, Some(replCandidate.index.getOrElse(-1) + 1)))
          })
    }
    (repl, replPos, nextReplCandidate)
  }

  /** Executes the `task` with timing information printed to stdout. */
  def timed[A](task: => A, msg: String): A = {
    println(msg + "... " + new Date())
    val tic = System.currentTimeMillis()
    val result = task
    val toc = System.currentTimeMillis()
    println("...done (" + ((toc-tic)/1000) + "s)")
    result
  }
}
