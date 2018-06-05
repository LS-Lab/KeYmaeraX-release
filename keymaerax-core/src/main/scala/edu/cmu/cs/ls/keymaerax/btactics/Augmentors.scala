/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{TopPosition, PosInExpr, Position}

/**
 * If imported, automatically augments core data structures with convenience wrappers for tactic purposes
 * such as subexpression positioning, context splitting, and replacements.
  *
 * @example To use this implicit augmentation automatically, import it via
  * {{{
  *   import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
  * }}}
  * Then use it as if its methods were part of the data structures
  * {{{
  *   val parser = KeYmaeraXParser
  *   val f = parser("x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1")
  *   // will obtain the x>=1 part
  *   val someSub = f.sub(PosInExpr(1::1::Nil))
  *   println(someSub)
  *   // construct x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x^2>y
  *   val other = f.replaceAt(PosInExpr(1::1::Nil), parser("x^2>y"))
  *   println(other)
  * }}}
 * @author Andre Platzer
 * @see [[Context]]
 */
object Augmentors {

  /**
    * Augment expressions with additional tactics-only helper functions.
    * @author Andre Platzer
    */
//  implicit class ExpressionAugmentor(val expr: Expression) {
//  }

  /**
   * Augment terms with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class TermAugmentor(val term: Term) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Subexpression at indicated position if exists, or None */
    def sub(pos: PosInExpr): Option[Expression] = try {Some(Context.sub(term, pos))} catch {case e: IllegalArgumentException => None}
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Term], Expression) = Context.at(term, pos)
    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Term = Context.replaceAt(term, pos, repl)
    /** Replace all free occurrences of `what` in `term` by `repl`. */
    def replaceFree(what: Term, repl: Term): Term = SubstitutionHelper.replaceFree(term)(what,repl)

    /**
      * Find the first (i.e., left-most) position of a subexpression satisfying `condition`, if any.
      * @param condition the condition that the subexpression sought for has to satisfy.
      * @return The first position, or None if no subexpression satisfies `condition`.
      */
    def find(condition: Term => Boolean): Option[(PosInExpr,Term)] = {
      var pos: Option[(PosInExpr,Term)] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          if (condition(e.asInstanceOf[Term])) { pos = Some((p,e)); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
      }, term)
      pos
    }

    /**
      * Find the first (i.e., left-most) position of the given term `e`, if any.
      * @return The first position, or None if `e` does not occur.
      */
    def find(e: Term): Option[PosInExpr] = find(t => e==t) match {case Some((pos,_))=>Some(pos) case None=>None}

    /** The substitution pair `this~>other`. */
    def ~>(other: Term): SubstitutionPair = SubstitutionPair(term, other)
  }

  /**
   * Augment formulas with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class FormulaAugmentor(val fml: Formula) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Subexpression at indicated position if exists, or None*/
    def sub(pos: PosInExpr): Option[Expression] = try {Some(Context.sub(fml, pos))} catch {case e: IllegalArgumentException => None}
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Formula], Expression) = Context.at(fml, pos)
    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Formula = Context.replaceAt(fml, pos, repl)
    /** Replace all free occurrences of `what` in `fml` by `repl`. */
    def replaceFree(what: Term, repl:Term): Formula = SubstitutionHelper.replaceFree(fml)(what,repl)
    /** Replace all occurrences of `what` in `fml` by `repl`. `what` and `repl` must be of the same kind, either Term or Formula */
    def replaceAll(what: Expression, repl: Expression): Formula = {
      require(what.kind == repl.kind, "Replacee and replacement must be of same kind, but got what.kind=" + what.kind + " and repl.kind=" + repl.kind)
      repl match {
        case term: Term => ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
            override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] =
              if (t == what) Right(term)
              else Left(None)
            override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
              // do not replace with invalid abbreviations in some obvious places
              case Forall(x, _) if x.contains(what) && !repl.isInstanceOf[Variable] => Right(f)
              case Forall(x, q) if x.contains(what) && repl.isInstanceOf[Variable] =>
                Right(Forall(x.map(v => if (v==what) repl.asInstanceOf[Variable] else v), q.replaceAll(what, repl)))
              case Exists(x, _) if x.contains(what) && !repl.isInstanceOf[Variable] => Right(f)
              case Exists(x, q) if x.contains(what) && repl.isInstanceOf[Variable] =>
                Right(Exists(x.map(v => if (v==what) repl.asInstanceOf[Variable] else v), q.replaceAll(what, repl)))
              case Box(Assign(x, _), _) if x == what && !repl.isInstanceOf[Variable] => Right(f)
              case Box(Assign(x, t), q) if x == what && repl.isInstanceOf[Variable] =>
                Right(Box(Assign(repl.asInstanceOf[Variable], t.replaceFree(what.asInstanceOf[Term], repl.asInstanceOf[Term])), q.replaceAll(what, repl)))
              case Box(AssignAny(x), _) if x == what && !repl.isInstanceOf[Variable] => Right(f)
              case Box(AssignAny(x), q) if x == what && repl.isInstanceOf[Variable] =>
                Right(Box(AssignAny(repl.asInstanceOf[Variable]), q.replaceAll(what, repl)))
              case Diamond(Assign(x, _), _) if x == what && !repl.isInstanceOf[Variable] => Right(f)
              case Diamond(Assign(x, t), q) if x == what && repl.isInstanceOf[Variable] =>
                Right(Diamond(Assign(repl.asInstanceOf[Variable], t.replaceFree(what.asInstanceOf[Term], repl.asInstanceOf[Term])), q.replaceAll(what, repl)))
              case Diamond(AssignAny(x), _) if x == what && !repl.isInstanceOf[Variable] => Right(f)
              case Diamond(AssignAny(x), q) if x == what && repl.isInstanceOf[Variable] =>
                Right(Diamond(AssignAny(repl.asInstanceOf[Variable]), q.replaceAll(what, repl)))
              case _ => Left(None)
            }
          }, fml) match {
            case Some(f) => f
          }

        case afml: Formula => ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] =
            if (f == what) Right(afml)
            else Left(None)
        }, fml) match {
          case Some(f) => f
        }

        case aprg: Program => ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preP(q: PosInExpr, a: Program): Either[Option[StopTraversal], Program] =
            if (a == what) Right(aprg)
            else Left(None)
        }, fml) match {
          case Some(f) => f
        }
      }
    }

    /**
      * Find the first (i.e., left-most) position of a subexpression satisfying `condition`, if any.
      * @param condition the condition that the subexpression sought for has to satisfy.
      * @return The first position and the subexpression at that position, or None if no subexpression satisfies `condition`.
      */
    def find(condition: Expression => Boolean): Option[(PosInExpr,Expression)] = {
      var pos: Option[(PosInExpr,Expression)] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
          if (condition(e)) { pos = Some((p,e)); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          if (condition(e)) { pos = Some((p,e)); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
      }, fml)
      pos
    }
    /**
      * Find the first (i.e., left-most) position of the given expression `e`, if any.
      * @return The first position, or None if `e` does not occur.
      */
    def find(e: Term): Option[PosInExpr] = find(t => e==t) match {case Some((pos,_))=>Some(pos) case None=>None}
    /**
      * Find the first (i.e., left-most) position of a subformula satisfying `condition`, if any.
      * @param condition the condition that the subformula sought for has to satisfy.
      * @return The first position and subformula at that position, or None if no subformula satisfies `condition`.
      */
    def findSubformula(condition: Formula => Boolean): Option[(PosInExpr,Formula)] = {
      var pos: Option[(PosInExpr,Formula)] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
          if (condition(e)) { pos = Some((p,e)); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
      }, fml)
      pos
    }

    /** Returns true if the formula is FOL, false otherwise. */
    def isFOL: Boolean = {
      var result = true
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Box(_, _) => result = false; Left(Some(ExpressionTraversal.stop))
          case Diamond(_, _) => result = false; Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, fml)
      result
    }

    /** Returns the universal closure of formula `fml`. */
    def universalClosure: Formula = {
      assert(fml.isFOL, "Universal closure on FOL formulas only")
      StaticSemantics.freeVars(fml).toSet[Variable].foldLeft(fml)((f,v) => Forall(v::Nil, f))
    }

    /** The substitution pair `this~>other`. */
    def ~>(repl: Formula): SubstitutionPair = SubstitutionPair(fml,repl)
  }

  /**
   * Augment programs with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class ProgramAugmentor(val prog: Program) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Subexpression at indicated position if exists, or None*/
    def sub(pos: PosInExpr): Option[Expression] = try {Some(Context.sub(prog,pos))} catch {case e: IllegalArgumentException => None}
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Program], Expression) = Context.at(prog, pos)
    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Program = Context.replaceAt(prog, pos, repl)
    /** Replace all free occurrences of what by repl */
    def replaceFree(what: Term, repl: Term): Program = SubstitutionHelper.replaceFree(prog)(what, repl)

    /** The substitution pair `this~>other`. */
    def ~>(repl: Program): SubstitutionPair = SubstitutionPair(prog,repl)
  }

  /**
   * Augment sequent with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class SequentAugmentor(val seq: Sequent) {
    /** Subexpression at indicated position */
    def apply(pos: Position): Expression = FormulaAugmentor(seq(pos.top))(pos.inExpr)
    /** Subexpression at indicated position if exists, or None */
    def sub(pos: Position): Option[Expression] = if (pos.isIndexDefined(seq)) FormulaAugmentor(seq(pos.top)).sub(pos.inExpr) else None
    /** Split into expression and its *formula* context at the indicated position */
    def at(pos: Position): (Context[Formula], Expression) = FormulaAugmentor(seq(pos.top)).at(pos.inExpr)
    /** Replace at position pos by repl */
    def replaceAt(pos: Position, repl: Expression): Formula = FormulaAugmentor(seq(pos.top)).replaceAt(pos.inExpr, repl)
    /** Replace all free occurrences of `what` in `seq` by `repl`. */
    def replaceFree(what: Term, repl: Term): Sequent = SubstitutionHelper.replaceFree(seq)(what,repl)
    /** Replace all occurrences of `what` in `seq` by `repl`. */
    def replaceAll(what: Expression, repl: Expression) = Sequent(seq.ante.map(_.replaceAll(what, repl)), seq.succ.map(_.replaceAll(what, repl)))
    //@todo implement returning both Ante+Succ
    def zipWithPositions: List[(Formula, TopPosition)] = ???
    /** Convert a sequent to its equivalent formula `/\antes -> \/succs` */
    def toFormula: Formula = {
      val anteAnd = seq.ante.reduceRightOption(And).getOrElse(True)
      val succOr = seq.succ.reduceRightOption(Or).getOrElse(False)
      //@note don't optimize true-> and ->false, since otherwise we'll have to deal with two special cases
      Imply(anteAnd, succOr)
    }
    /** Returns true if all formulas in the sequent are FOL, false otherwise. */
    def isFOL: Boolean = seq.ante.forall(_.isFOL) && seq.succ.forall(_.isFOL)
  }

  implicit class ExpressionAugmentor(val e: Expression) {
    def replaceFree(what: Term, repl: Term): Expression = e match {
      case f: Formula => f.replaceFree(what, repl)
      case t: Term => t.replaceFree(what, repl)
      case p: Program => p.replaceFree(what, repl)
    }

    /** The substitution pair `term~>other` after dottifying `other` to fit arguments of `term`. */
    def ~>>(other: Expression): SubstitutionPair = implicitSubst(other)

    def implicitSubst(other: Expression): SubstitutionPair = {

      /** Converts the atoms of term `t` into DotTerms. Returns a map of (atom -> dot), the accumulated nested terms,
        * and the next unused dot index. */
      def findDots(t: Term, idx: Int, dots: Map[Term, DotTerm]): (Map[Term, DotTerm], Term, Int) = t match {
        case Pair(l, r) =>
          val (lDots, lAccDots, lNextIdx) = findDots(l, idx, dots)
          val (rDots, rAccDots, rNextIdx) = findDots(r, lNextIdx, lDots)
          (rDots, Pair(lAccDots, rAccDots), rNextIdx)
        case _ =>
          val dot = DotTerm(t.sort, Some(idx))
          (dots + (t -> dot), dot, idx+1)
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
      }

      val (dots: Map[Term, DotTerm], arg: Term, _) = signature match {
        case Nothing => (Map.empty, Nothing, 0)
        case Pair(_, _) => findDots(signature, 0, Map.empty)
        case _ =>
          val dot = DotTerm(signature.sort)
          (Map(signature -> dot), dot, 1)
      }

      val what = e match {
        case FuncOf(fn, _) => FuncOf(fn, arg)
        case PredOf(fn, _) => PredOf(fn, arg)
      }

      val repl = dots.foldLeft(other)({ case (t, (w, r)) => t.replaceFree(w, r) })

      val undeclaredDots = dotsOf(repl) -- dotsOf(arg)
      if (undeclaredDots.nonEmpty) throw new IllegalArgumentException("Function/predicate " +
        what.prettyString + " defined using undeclared " + undeclaredDots.map(_.prettyString).mkString(","))

      SubstitutionPair(what, repl)
    }
  }
}
