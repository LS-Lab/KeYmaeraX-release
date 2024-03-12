/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core._

import scala.annotation.tailrec
import scala.collection.immutable.List
import scala.collection.mutable.ListBuffer

/**
 * If imported, automatically augments core data structures with convenience wrappers for tactic purposes such as
 * subexpression positioning, context splitting, and replacements.
 *
 * @example
 *   To use this implicit augmentation automatically, import it via
 *   {{{
 *   import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
 *   }}}
 *   Then use it as if its methods were part of the data structures
 *   {{{
 *   val parser = KeYmaeraXParser
 *   val f = parser("x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1")
 *   // will obtain the x>=1 part
 *   val someSub = f.sub(PosInExpr(1::1::Nil))
 *   println(someSub)
 *   // construct x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x^2>y
 *   val other = f.replaceAt(PosInExpr(1::1::Nil), parser("x^2>y"))
 *   println(other)
 *   }}}
 * @author
 *   Andre Platzer
 * @see
 *   [[Context]]
 */
object Augmentors {

  /** Indicates that variable `v` cannot be elaborated to a function symbol inside expression `e`. */
  case class ElaborationError(msg: String, v: Variable, e: Expression, ex: Throwable) extends AssertionError(msg, ex)

  /**
   * Augment expressions with additional tactics-only helper functions.
   * @author
   *   Andre Platzer
   */
//  implicit class ExpressionAugmentor(val expr: Expression) {
//  }

  /**
   * Augment terms with additional tactics-only helper functions.
   * @author
   *   Andre Platzer
   */
  implicit class TermAugmentor(val term: Term) {

    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2

    /** Subexpression at indicated position if exists, or None */
    def sub(pos: PosInExpr): Option[Expression] =
      try { Some(Context.sub(term, pos)) }
      catch { case _: IllegalArgumentException => None }

    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Term], Expression) = Context.at(term, pos)

    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Term = Context.replaceAt(term, pos, repl)

    /** Replace all free occurrences of `what` in `term` by `repl`. */
    def replaceFree(what: Term, repl: Term): Term = SubstitutionHelper.replaceFree(term)(what, repl)

    /**
     * Find the first (i.e., left-most) position of a subexpression satisfying `condition`, if any.
     * @param condition
     *   the condition that the subexpression sought for has to satisfy.
     * @return
     *   The first position, or None if no subexpression satisfies `condition`.
     */
    def find(condition: Term => Boolean): Option[(PosInExpr, Term)] = {
      var pos: Option[(PosInExpr, Term)] = None
      ExpressionTraversal.traverse(
        new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
            if (condition(e)) { pos = Some((p, e)); Left(Some(ExpressionTraversal.stop)) }
            else Left(None)
        },
        term,
      )
      pos
    }

    /**
     * Find the first (i.e., left-most) position of the given term `e`, if any.
     * @return
     *   The first position, or None if `e` does not occur.
     */
    def find(e: Term): Option[PosInExpr] = find(t => e == t) match {
      case Some((pos, _)) => Some(pos)
      case None => None
    }

    /** The substitution pair `this~>other`. */
    def ~>(other: Term): SubstitutionPair = SubstitutionPair(term, other)
  }

  /**
   * Augment formulas with additional tactics-only helper functions.
   * @author
   *   Andre Platzer
   */
  implicit class FormulaAugmentor(val fml: Formula) {

    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2

    /** Subexpression at indicated position if exists, or None */
    def sub(pos: PosInExpr): Option[Expression] =
      try { Some(Context.sub(fml, pos)) }
      catch { case _: IllegalArgumentException => None }

    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Formula], Expression) = Context.at(fml, pos)

    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Formula = Context.replaceAt(fml, pos, repl)

    /** Replace all free occurrences of `what` in `fml` by `repl`. */
    def replaceFree(what: Term, repl: Term): Formula = SubstitutionHelper.replaceFree(fml)(what, repl)

    /**
     * Find the first (i.e., left-most) position of a subexpression satisfying `condition`, if any.
     * @param condition
     *   the condition that the subexpression sought for has to satisfy.
     * @return
     *   The first position and the subexpression at that position, or None if no subexpression satisfies `condition`.
     */
    def find(condition: Expression => Boolean): Option[(PosInExpr, Expression)] = {
      var pos: Option[(PosInExpr, Expression)] = None
      ExpressionTraversal.traverse(
        new ExpressionTraversalFunction() {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
            if (condition(e)) { pos = Some((p, e)); Left(Some(ExpressionTraversal.stop)) }
            else Left(None)
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
            if (condition(e)) { pos = Some((p, e)); Left(Some(ExpressionTraversal.stop)) }
            else Left(None)
        },
        fml,
      )
      pos
    }

    /**
     * Find the first (i.e., left-most) position of the given expression `e`, if any.
     * @return
     *   The first position, or None if `e` does not occur.
     */
    def find(e: Term): Option[PosInExpr] = find(t => e == t) match {
      case Some((pos, _)) => Some(pos)
      case None => None
    }

    /**
     * Find the first (i.e., left-most) position of a subformula satisfying `condition`, if any.
     * @param condition
     *   the condition that the subformula sought for has to satisfy.
     * @return
     *   The first position and subformula at that position, or None if no subformula satisfies `condition`.
     */
    def findSubformula(condition: Formula => Boolean): Option[(PosInExpr, Formula)] = {
      var pos: Option[(PosInExpr, Formula)] = None
      ExpressionTraversal.traverse(
        new ExpressionTraversalFunction() {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
            if (condition(e)) { pos = Some((p, e)); Left(Some(ExpressionTraversal.stop)) }
            else Left(None)
        },
        fml,
      )
      pos
    }

    /** Returns true if the formula is FOL, false otherwise. */
    def isFOL: Boolean = {
      var result = true
      ExpressionTraversal.traverse(
        new ExpressionTraversalFunction() {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
            case Box(_, _) => result = false; Left(Some(ExpressionTraversal.stop))
            case Diamond(_, _) => result = false; Left(Some(ExpressionTraversal.stop))
            case _ => Left(None)
          }
        },
        fml,
      )
      result
    }

    /** Indicates whether the formula is FOL without uninterpreted predicate symbols. */
    def isPredicateFreeFOL: Boolean = fml.isFOL &&
      StaticSemantics
        .signature(fml)
        .forall({
          case Function(_, _, _, Bool, None) => false
          case _: PredicationalOf => false
          case _: UnitPredicational => false
          case _ => true
        })

    /** Indicates whether the arguments of uninterpreted functions are free. */
    def isFuncFreeArgsFOL: Boolean = {
      val bv = StaticSemantics.boundVars(fml)
      var result = true
      ExpressionTraversal.traverse(
        new ExpressionTraversalFunction() {
          // isFOL (duplicated here to avoid repeated traversal) + arguments are not bound
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
            case Box(_, _) => result = false; Left(Some(ExpressionTraversal.stop))
            case Diamond(_, _) => result = false; Left(Some(ExpressionTraversal.stop))
            case _ => Left(None)
          }
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
            case FuncOf(Function(_, _, _, _, Some(_)), _) => Left(None) // interpreted function symbols are allowed
            case FuncOf(_, args) if !bv.intersect(StaticSemantics.freeVars(args)).isEmpty =>
              result = false; Left(Some(ExpressionTraversal.stop))
            case _ => Left(None)
          }
        },
        fml,
      )
      result
    }

    /** Returns the universal closure of formula `fml`. */
    def universalClosure: Formula = {
      assert(fml.isFOL, "Universal closure on FOL formulas only")
      StaticSemantics
        .freeVars(fml)
        .toSet[Variable]
        .filter(_.isInstanceOf[BaseVariable])
        .foldLeft(fml)((f, v) => Forall(v :: Nil, f))
    }

    /** The substitution pair `this~>other`. */
    def ~>(repl: Formula): SubstitutionPair = SubstitutionPair(fml, repl)
  }

  /**
   * Augment programs with additional tactics-only helper functions.
   * @author
   *   Andre Platzer
   */
  implicit class ProgramAugmentor(val prog: Program) {

    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2

    /** Subexpression at indicated position if exists, or None */
    def sub(pos: PosInExpr): Option[Expression] =
      try { Some(Context.sub(prog, pos)) }
      catch { case _: IllegalArgumentException => None }

    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Program], Expression) = Context.at(prog, pos)

    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Program = Context.replaceAt(prog, pos, repl)

    /** Replace all free occurrences of what by repl */
    def replaceFree(what: Term, repl: Term): Program = SubstitutionHelper.replaceFree(prog)(what, repl)

    /** The substitution pair `this~>other`. */
    def ~>(repl: Program): SubstitutionPair = SubstitutionPair(prog, repl)
  }

  /**
   * Augment sequent with additional tactics-only helper functions.
   * @author
   *   Andre Platzer
   */
  implicit class SequentAugmentor(val seq: Sequent) {

    /** Subexpression at indicated position */
    def apply(pos: Position): Expression = FormulaAugmentor(seq(pos.top))(pos.inExpr)

    /** Subexpression at indicated position if exists, or None */
    def sub(pos: Position): Option[Expression] =
      if (pos.isIndexDefined(seq)) FormulaAugmentor(seq(pos.top)).sub(pos.inExpr) else None

    /** Split into expression and its *formula* context at the indicated position */
    def at(pos: Position): (Context[Formula], Expression) = FormulaAugmentor(seq(pos.top)).at(pos.inExpr)

    /** Replace at position pos by repl */
    def replaceAt(pos: Position, repl: Expression): Formula = FormulaAugmentor(seq(pos.top)).replaceAt(pos.inExpr, repl)

    /** Replace all free occurrences of `what` in `seq` by `repl`. */
    def replaceFree(what: Term, repl: Term): Sequent = SubstitutionHelper.replaceFree(seq)(what, repl)

    /** Replace all occurrences of `what` in `seq` by `repl`. */
    def replaceAll(what: Expression, repl: Expression): Sequent =
      Sequent(seq.ante.map(_.replaceAll(what, repl)), seq.succ.map(_.replaceAll(what, repl)))
    def replaceAll(repls: Map[Expression, Expression]): Sequent =
      Sequent(seq.ante.map(_.replaceAll(repls)), seq.succ.map(_.replaceAll(repls)))
    def zipAnteWithPositions: List[(Formula, TopAntePosition)] = seq
      .ante
      .zipWithIndex
      .map({ case (f, i) => (f, AntePosition(AntePos(i))) })
      .toList
    def zipSuccWithPositions: List[(Formula, TopSuccPosition)] = seq
      .succ
      .zipWithIndex
      .map({ case (f, i) => (f, SuccPosition(SuccPos(i))) })
      .toList
    def zipWithPositions: List[(Formula, TopPosition)] = zipAnteWithPositions ++ zipSuccWithPositions

    /** Convert a sequent to its equivalent formula `/\antes -> \/succs` */
    def toFormula: Formula = {
      val anteAnd = seq.ante.reduceRightOption(And).getOrElse(True)
      val succOr = seq.succ.reduceRightOption(Or).getOrElse(False)
      // @note don't optimize true-> and ->false, since otherwise we'll have to deal with two special cases
      Imply(anteAnd, succOr)
    }

    /** Returns true if all formulas in the sequent are FOL, false otherwise. */
    def isFOL: Boolean = seq.ante.forall(_.isFOL) && seq.succ.forall(_.isFOL)
    def isPredicateFreeFOL: Boolean = seq.ante.forall(_.isPredicateFreeFOL) && seq.succ.forall(_.isPredicateFreeFOL)
    def isFuncFreeArgsFOL: Boolean = seq.ante.forall(_.isFuncFreeArgsFOL) && seq.succ.forall(_.isFuncFreeArgsFOL)

    /** Returns a copy without the position `pos`. */
    def without(pos: SeqPos): Sequent =
      if (pos.isAnte) Sequent(seq.ante.patch(pos.getIndex, Nil, 1), seq.succ)
      else Sequent(seq.ante, seq.succ.patch(pos.getIndex, Nil, 1))

    def exhaustiveSubst(subst: USubst): Sequent = Sequent(
      seq.ante.map(_.exhaustiveSubst(subst).asInstanceOf[Formula]),
      seq.succ.map(_.exhaustiveSubst(subst).asInstanceOf[Formula]),
    )
  }

  implicit class ExpressionAugmentor[E <: Expression](val e: E) {
    def sub(pos: PosInExpr): Option[Expression] = e match {
      case f: Formula => f.sub(pos)
      case t: Term => t.sub(pos)
      case h: Program => h.sub(pos)
    }

    def replaceAt(pos: PosInExpr, repl: Expression): Expression = e match {
      case f: Formula => f.replaceAt(pos, repl)
      case t: Term => t.replaceAt(pos, repl)
      case h: Program => h.replaceAt(pos, repl)
    }

    def replaceFree(what: Term, repl: Term): E = e match {
      case f: Formula => f.replaceFree(what, repl).asInstanceOf[E]
      case t: Term => t.replaceFree(what, repl).asInstanceOf[E]
      case p: Program => p.replaceFree(what, repl).asInstanceOf[E]
      // Isolated unapplied Function without FuncOf is no term
      case f: Function => f.asInstanceOf[E]
    }

    /**
     * Replace all occurrences of `what` in `e` by `repl`. `what` and `repl` must be of the same kind, either Term,
     * Formula, or Program. Replaces literal occurrences even in places disallowed by uniform substitution (minimal
     * safeguarding to not replace in some obvious invalid places).
     * @throws ClassCastException
     *   When `repl` cannot be cast to the type expected at an occurrence of `what` (e.g., when replacing x with f()
     *   inside x:=y).
     */
    def replaceAll(what: Expression, repl: Expression): E = replaceAll(Map(what -> repl))

    /**
     * Replace all occurrences of `what` in `e` by `repl`. `what` and `repl` must be of the same kind, either Term,
     * Formula, or Program. Replaces literal occurrences even in places disallowed by uniform substitution (minimal
     * safeguarding to not replace in some obvious invalid places).
     * @throws ClassCastException
     *   When `repl` cannot be cast to the type expected at an occurrence of `what` (e.g., when replacing x with f()
     *   inside x:=y).
     */
    def replaceAll(repls: Map[Expression, Expression]): E = {
      require(
        repls.forall({ case (k, v) => k.kind == v.kind }),
        "Replacee and replacement must be of same kind, but got " +
          repls
            .find({ case (what, repl) => what.kind != repl.kind })
            .map({ case (what, repl) => "what.kind=" + what.kind + " and repl.kind=" + repl.kind }),
      )
      // @note Not using StaticSemantics.boundVars, since also replacing past program/ODE constant symbols.
      if (repls.isEmpty) e
      else {
        val trmRepls = repls.filter(_._2.kind == TermKind)
        val fmlRepls = repls.filter(_._2.kind == FormulaKind)
        val prgRepls = repls.filter(_._2.kind == ProgramKind)

        /**
         * Partitions `repls` into those with key in `x` (variable/differential symbol), and those whose key is not in
         * `x`.
         */
        def partitionBF(
            x: Seq[Variable],
            repls: Map[Expression, Expression],
        ): (Map[Expression, Expression], Map[Expression, Expression]) = {
          repls.partition({
            case (k: Variable, _) => x.exists({
                case ds @ DifferentialSymbol(xx) => ds == k || xx == k
                case v => v == k
              })
            case (FuncOf(_, args), _) => !StaticSemantics.freeVars(args).intersect(x.toSet).isEmpty
            case _ => false
          })
        }

        /** Renames variable or differential symbol `what` according to the renaming in `ren`. */
        def rename(what: Variable, ren: Map[Expression, Expression]): Variable = what match {
          case DifferentialSymbol(x) => DifferentialSymbol(ren.getOrElse(x, x).asInstanceOf[Variable])
          case _ => ren.getOrElse(what, what).asInstanceOf[Variable]
        }

        ExpressionTraversal.traverseExpr(
          new ExpressionTraversalFunction() {
            override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = trmRepls.get(t) match {
              case Some(r) => Right(r.asInstanceOf[Term])
              case None => Left(None)
            }

            override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
              fmlRepls.get(f) match {
                case Some(r) => Right(r.asInstanceOf[Formula])
                case None => f match {
                    // do not replace with invalid abbreviations in some obvious places
                    // bound x can be variable or differential symbol
                    case Forall(x, q) =>
                      val (bound, free) = partitionBF(x, trmRepls)
                      val ren = bound.filter({ case (_, v) => v.isInstanceOf[Variable] })
                      Right(Forall(x.map(rename(_, ren)), q.replaceAll(free ++ ren ++ fmlRepls ++ prgRepls)))
                    case Exists(x, q) =>
                      val (bound, free) = partitionBF(x, trmRepls)
                      val ren = bound.filter({ case (_, v) => v.isInstanceOf[Variable] })
                      Right(Exists(x.map(rename(_, ren)), q.replaceAll(free ++ ren ++ fmlRepls ++ prgRepls)))
                    case Box(Assign(x, t), q) =>
                      val (bound, free) = partitionBF(Seq(x), trmRepls)
                      val ren = bound.filter({ case (_, v) => v.isInstanceOf[Variable] })
                      Right(Box(
                        Assign(rename(x, ren), t.replaceAll(ren ++ free)),
                        q.replaceAll(ren ++ free ++ fmlRepls ++ prgRepls),
                      ))
                    case Box(AssignAny(x), q) =>
                      val (bound, free) = partitionBF(Seq(x), trmRepls)
                      val ren = bound.filter({ case (_, v) => v.isInstanceOf[Variable] })
                      Right(Box(AssignAny(rename(x, ren)), q.replaceAll(ren ++ free ++ fmlRepls ++ prgRepls)))
                    case Diamond(Assign(x, t), q) =>
                      val (bound, free) = partitionBF(Seq(x), trmRepls)
                      val ren = bound.filter({ case (_, v) => v.isInstanceOf[Variable] })
                      Right(Diamond(
                        Assign(rename(x, ren), t.replaceAll(ren ++ free)),
                        q.replaceAll(ren ++ free ++ fmlRepls ++ prgRepls),
                      ))
                    case Diamond(AssignAny(x), q) =>
                      val (bound, free) = partitionBF(Seq(x), trmRepls)
                      val ren = bound.filter({ case (_, v) => v.isInstanceOf[Variable] })
                      Right(Diamond(AssignAny(rename(x, ren)), q.replaceAll(ren ++ free ++ fmlRepls ++ prgRepls)))
                    case _ => Left(None)
                  }
              }

            override def preP(q: PosInExpr, a: Program): Either[Option[StopTraversal], Program] =
              prgRepls.get(a) match {
                case Some(r) => Right(r.asInstanceOf[Program])
                case None => Left(None)
              }
          },
          e,
        ) match { case Some(r) => r }
      }
    }

    /** The substitution pair `term~>other` after dottifying `other` to fit arguments of `term`. */
    def ~>>(other: Expression): SubstitutionPair = implicitSubst(other)

    def implicitSubst(other: Expression): SubstitutionPair = {

      /**
       * Converts the atoms of term `t` into DotTerms. Returns a map of (atom -> dot), the accumulated nested terms, and
       * the next unused dot index.
       */
      def findDots(t: Term, idx: Int, dots: Map[Term, DotTerm]): (Map[Term, DotTerm], Term, Int) = t match {
        case Pair(l, r) =>
          val (lDots, lAccDots, lNextIdx) = findDots(l, idx, dots)
          val (rDots, rAccDots, rNextIdx) = findDots(r, lNextIdx, lDots)
          (rDots, Pair(lAccDots, rAccDots), rNextIdx)
        case _ =>
          val dot = DotTerm(t.sort, Some(idx))
          (dots + (t -> dot), dot, idx + 1)
      }

      /** Returns the dots used in expression `e`. */
      def dotsOf(e: Expression): Set[DotTerm] = {
        val dots = scala.collection.mutable.Set[DotTerm]()
        val traverseFn = new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
            case d: DotTerm => dots += d; Left(None)
            case _ => Left(None)
          }
        }
        e match {
          case t: Term => ExpressionTraversal.traverse(traverseFn, t)
          case f: Formula => ExpressionTraversal.traverse(traverseFn, f)
          case p: Program => ExpressionTraversal.traverse(traverseFn, p)
        }
        dots.toSet
      }

      val signature = e match {
        case FuncOf(_, t) => t
        case PredOf(_, t) => t
        // @note programs and system constants do not have arguments
        case _: ProgramConst => Nothing
        case _: SystemConst => Nothing
      }

      val (dots: Map[Term, DotTerm], arg: Term, _) = signature match {
        case Nothing => (Map.empty, Nothing, 0)
        case Pair(_, _) => findDots(signature, 0, Map.empty)
        case _ =>
          val dot = DotTerm(signature.sort, Some(0))
          (Map(signature -> dot), dot, 1)
      }

      val what = e match {
        case FuncOf(fn, _) => FuncOf(fn, arg)
        case PredOf(fn, _) => PredOf(fn, arg)
        case t => t
      }

      val repl = dots.foldLeft(other)({ case (t, (w, r)) => t.replaceFree(w, r) })

      val undeclaredDots = dotsOf(repl) -- dotsOf(arg)
      if (undeclaredDots.nonEmpty) throw new IllegalArgumentException(
        "Function/predicate " + what.prettyString + " defined using undeclared " +
          undeclaredDots.map(_.prettyString).mkString(",")
      )

      SubstitutionPair(what, repl)
    }

    /**
     * Elaborates in `e` variable uses of functions listed in `signature`. Replaces all literal occurrences of
     * [[BaseVariable]] of the same name as a function in `signature`, but ignores all non-[[BaseVariable]] occurrences
     * and ignores all non-function symbols in `signature`. Also elaborates [[FuncOf]] to [[PredOf]] per sort in
     * `signature`.
     */
    def elaborateToFunctions(signature: Set[NamedSymbol]): Expression = {
      def byNameIdx(symbols: Set[NamedSymbol]): Map[(String, Option[Int]), Set[NamedSymbol]] = symbols
        .groupBy(s => (s.name, s.index))
        .filter(_._2.size > 1)

      def assertConsistentKinds(symbols: Set[NamedSymbol], msg: String): Unit = {
        val groups = symbols.groupBy(s => (s.name, s.index)).filter(_._2.size > 1)
        lazy val details = groups
          .map(s =>
            "  Symbol " + s._1._1 + s._1._2.map("_" + _).getOrElse("") + " used with inconsistent kinds " +
              s._2.map(_.fullString).mkString(",")
          )
          .mkString("\n  ")
        assert(groups.isEmpty, msg + ":\n" + details)
      }

      def bySignature(s: NamedSymbol): Boolean = signature.exists({
        case Function(fn, fi, Unit, _, _) => fn == s.name && fi == s.index
        case _ => false
      })

      val elaboratableVars = StaticSemantics
        .symbols(e)
        .map({
          case s @ BaseVariable(name, i, _) => s -> signature.find({
              case Function(fn, fi, Unit, _, _) => fn == name && fi == i
              case _ => false
            })
          case s => s -> None
        })
        .filter(_._2.isDefined)
        .map({ case (v: BaseVariable, Some(f)) => v -> f })

      val fnElaborated = elaboratableVars.foldLeft(e)({ case (e, (v, f: Function)) =>
        // @note avoid elaborating to inconsistent with v, so don't just replace v with f but name/index/sort of v. later checks discover inconsistency with builtin definitions
        val replaced = e.replaceFree(v, FuncOf(Function(v.name, v.index, Unit, v.sort, f.interp), Nothing))
        if (byNameIdx(StaticSemantics.symbols(replaced).filter(bySignature)).isEmpty) replaced else e
      })

      val elaboratableFns = StaticSemantics
        .symbols(fnElaborated)
        .flatMap({
          case fn: Function => signature.find(ns => ns.name == fn.name && ns.index == fn.index) match {
              case Some(ns: Function) => if (ns.domain == fn.domain && ns.sort != fn.sort) Some(fn -> ns) else None
              case _ => None
            }
          case _ => None
        })
        .toMap

      val predFnElaborated = fnElaborated match {
        case f @ FuncOf(fn: Function, c) => elaboratableFns.get(fn).map(PredOf(_, c)).getOrElse(f)
        case p @ PredOf(fn: Function, c) => elaboratableFns.get(fn).map(FuncOf(_, c)).getOrElse(p)
        case e => e
      }

      val elaboratingSymbols = StaticSemantics.symbols(predFnElaborated).filter(bySignature)
      assertConsistentKinds(elaboratingSymbols, "Cannot elaborate")
      val elaboratables = elaboratingSymbols.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])
      val replaced = elaboratables.foldLeft(predFnElaborated)((e, v) =>
        try { e.replaceAll(v, FuncOf(Function(v.name, v.index, Unit, v.sort), Nothing)) }
        catch {
          case ex: ClassCastException => throw ElaborationError(
              "Elaboration tried replacing " + v.prettyString + " in literal bound occurrence inside " + e.prettyString,
              v,
              e,
              ex,
            )
        }
      )
      assertConsistentKinds(
        StaticSemantics.symbols(replaced).filter(bySignature),
        "Elaboration results in inconsistent kinds",
      )
      replaced
    }

    /** Applies substitutions per `substs` exhaustively. */
    def exhaustiveSubst(subst: USubst): Expression = {
      @tailrec
      def exhaustiveSubst(f: Expression): Expression = {
        val fs = subst.apply(f)
        if (fs != f) exhaustiveSubst(fs) else fs
      }
      exhaustiveSubst(e.elaborateToFunctions(subst.subsDefsInput.flatMap(s => StaticSemantics.signature(s.what)).toSet))
    }

    /** Lists all subpositions of expression `e`, categorized by their kind. */
    def listSubPos: List[(Kind, PosInExpr)] = {
      def collector(collected: ListBuffer[(Kind, PosInExpr)]): ExpressionTraversalFunction =
        new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
            collected.append((e.kind, p)); Left(None)
          }
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
            collected.append((e.kind, p)); Left(None)
          }
          override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
            collected.append((e.kind, p)); Left(None)
          }
        }

      val subPositions = ListBuffer.empty[(Kind, PosInExpr)]
      e match {
        case t: Term => ExpressionTraversal.traverse(collector(subPositions), t)
        case f: Formula => ExpressionTraversal.traverse(collector(subPositions), f)
        case p: Program => ExpressionTraversal.traverse(collector(subPositions), p)
      }

      subPositions.toList
    }

    /** Returns all sub-terms of this expression that pass `matcher`. */
    def matchingTerms(matcher: Term => Boolean): List[Term] = {
      val result = scala.collection.mutable.ListBuffer.empty[Term]
      ExpressionTraversal.traverse(
        new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = {
            if (matcher(e)) result += e
            Left(None)
          }
        },
        e,
      )
      result.toList
    }

    /**
     * Returns all symbols of this `e` minus the explicitly quantified symbols (when we want \forall x differently from
     * [x:=...;]).
     */
    def baseSymbols: Set[NamedSymbol] =
      (StaticSemantics.symbols(e) --
        (e match {
          case _: Term => Set.empty // include all term symbols
          case f: Formula =>
            // exclude universally/existentially quantified symbols
            var quantifiedSymbols = Set.empty[Variable]
            ExpressionTraversal.traverse(
              new ExpressionTraversalFunction() {
                override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
                  case q: Quantified =>
                    quantifiedSymbols ++= q.vars
                    Left(None)
                  case _ => Left(None)
                }
              },
              f,
            )
            val fv = StaticSemantics.freeVars(f)
            if (fv.isInfinite) Set.empty else quantifiedSymbols -- fv.toSet
          case _: Program =>
            Set.empty // include all program symbols //@todo test with quantified formulas ?\exists y p(y)
        })).map({
        case DifferentialSymbol(v) => v
        case s => s
      })
  }

  /**
   * Augment sorts with additional tactics-only helper functions.
   * @author
   *   Stefan Mitsch
   */
  implicit class SortAugmentor(val sort: Sort) {

    /** Converts this `sort` into nested pairs of DotTerms. Returns the nested dots and the next unused dot index. */
    def toDots(idx: Int): (Term, Int) = sort match {
      case Real | Bool => (DotTerm(sort, Some(idx)), idx + 1)
      case Tuple(l, r) =>
        val (lDots, lNextIdx) = l.toDots(idx)
        val (rDots, rNextIdx) = r.toDots(lNextIdx)
        (Pair(lDots, rDots), rNextIdx)
    }

    /** Converts this `sort` into nested pairs of DotTerms. Returns the nested dots and unused dot indices. */
    def toDots(idxs: List[Int]): (Term, List[Int]) = sort match {
      case Real | Bool => idxs match {
          case idx :: q => (DotTerm(sort, Some(idx)), q)
          case _ => throw new IllegalArgumentException("Not enough indices to convert the sort")
        }
      case Tuple(l, r) =>
        val (lDots, lIdxs) = l.toDots(idxs)
        val (rDots, rIdxs) = r.toDots(lIdxs)
        (Pair(lDots, rDots), rIdxs)
    }

    /** Converts this `sort` into a flat list of [[DotTerm]]. */
    def toFlatDots(idx: Int): (List[DotTerm], Int) = toDots(idx) match {
      case (d: DotTerm, i) => (d :: Nil, i)
      case (Pair(d: DotTerm, r), i) =>
        val (rd, ni) = r.sort.toFlatDots(i)
        (d :: rd, ni)
      case _ => throw new IllegalArgumentException("Sort cannot be flattened")
    }
  }
}
