/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.bellerophon.{SubstUnificationException, UnificationException}
import SubstitutionHelper.replaceFree
import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction

import scala.collection.immutable.{List, Nil}
import scala.util.Try

/**
  * Unification/matching algorithm for tactics.
  * `Unify(shape, input)` matches second argument `input` against the pattern `shape` of the first argument but not vice versa.
  * Matcher leaves `input` alone and only substitutes into `shape`, i.e., gives a single-sided matcher.
  * @see [[Matcher]]
  * @author Andre Platzer
  */
// 1 pass for semanticRenaming
//object UnificationMatch extends UnificationMatchBase {require(RenUSubst.semanticRenaming, "This implementation is meant for tactics built assuming semantic renaming")}
// 2 pass for semanticRenaming
//object UnificationMatch extends UnificationMatchURenAboveUSubst {require(RenUSubst.semanticRenaming, "This implementation is meant for tactics built assuming semantic renaming")}
// 2.5 pass for !semanticRenaming
//object UnificationMatch extends UnificationMatchUSubstAboveURen
// 1 pass for fresh cases of !semanticRenaming

object UnificationMatch extends FreshUnificationMatch

// 1 pass sweeping uniform matcher with semanticRenaming, incapable of recursive split like assignb
//object UnificationMatch extends UniformMatcher

//@todo not general enough, limited to linear pattern matching only
//object UnificationMatch extends LinearMatcher

// 1.5 pass for fresh cases of !semanticRenaming
//object UnificationMatch extends FreshPostUnificationMatch


/**
  * Generic schematic unification/matching algorithm for tactics.
  * Unify(shape, input) matches second argument `input` against the pattern `shape` of the first argument but not vice versa.
  * Matcher leaves input alone and only substitutes into shape.
  * Reasonably fast single-pass matcher.
  * Defined by recursive unification from compositions.
  * @author Andre Platzer
  */
abstract class SchematicComposedUnificationMatch extends SchematicUnificationMatch {

  /** @inheritdoc
    * Implemented by unifying from left to right, but will fall back to converse direction if exception.
    */
  //@note optimized: repeated implementation per type to enable the static type inference that Scala generics won't give.
  protected override def unifies2(s1:Expression, s2:Expression, t1:Expression, t2:Expression): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    try {
      compose(unify(Subst(u1)(s2), t2), u1)
    } catch {
      case e: ProverException =>
        logger.trace("      try converse since " + e.getMessage)
        val u2 = unify(s2, t2)
        compose(unify(t1, Subst(u2)(s1)), u2)
    }
  }
  protected override def unifies2(s1:Term, s2:Term, t1:Term, t2:Term): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    try {
      compose(unify(Subst(u1)(s2), t2), u1)
    } catch {
      case e: ProverException =>
        logger.trace("      try converse since " + e.getMessage)
        val u2 = unify(s2, t2)
        compose(unify(t1, Subst(u2)(s1)), u2)
    }
  }
  protected override def unifies2(s1:Formula, s2:Formula, t1:Formula, t2:Formula): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    try {
      compose(unify(Subst(u1)(s2), t2), u1) //@note fails on x=1, p(x)
    } catch {
      case e: ProverException =>
        try {
          logger.trace("      try converse since " + e.getMessage)
          compose(unify(t2, Subst(u1)(s2)), u1)
        } catch {
          case e: ProverException =>
            logger.trace("      try next converse since " + e.getMessage)
            val u2 = unify(s2, t2)
            try {
              compose(unify(t1, Subst(u2)(s1)), u2)
            } catch {
              case e: ProverException =>
                logger.trace("      try final converse since " + e.getMessage)
                compose(unify(Subst(u2)(s1), t1), u2)
            }
        }
    }
  }
  protected override def unifies2(s1:Program, s2:Program, t1:Program, t2:Program): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    try {
      compose(unify(Subst(u1)(s2), t2), u1)
    } catch {
      case e: ProverException =>
        logger.trace("      try converse since " + e.getMessage)
        val u2 = unify(s2, t2)
        compose(unify(t1, Subst(u2)(s1)), u2)
    }
  }
  protected override def unifiesODE2(s1:DifferentialProgram, s2:DifferentialProgram, t1:DifferentialProgram, t2:DifferentialProgram): List[SubstRepl] = {
    val u1 = unifyODE(s1, t1)
    try {
      compose(unifyODE(Subst(u1)(s2), t2), u1)
    } catch {
      case e: ProverException =>
        logger.trace("      try converse since " + e.getMessage)
        val u2 = unifyODE(s2, t2)
        compose(unifyODE(t1, Subst(u2)(s1)), u2)
    }
  }

  protected override def unify(s1: Sequent, s2: Sequent): List[SubstRepl] =
    if (!(s1.ante.length == s2.ante.length && s1.succ.length == s2.succ.length)) ununifiable(s1,s2)
    else {
      val composeFolder = (u1: List[SubstRepl], f1: Formula, f2: Formula) =>
        compose(unify(Subst(u1)(f1), f2), u1)
      val antesubst = s1.ante.indices.foldLeft(List[SubstRepl]()) ((subst,i) => composeFolder(subst, s1.ante(i), s2.ante(i)))
      val succsubst = s1.succ.indices.foldLeft(antesubst) ((subst,i) => composeFolder(subst, s1.succ(i), s2.succ(i)))
      distinctIfNeedBe(succsubst)
      //@note if flat ++ this would be easy:
      //        //@todo this is really a zip fold
      //      (
      //        s1.ante.indices.foldLeft(List[SubstRepl]())((subst,i) => subst ++ unify(s1.ante(i), s2.ante(i))) ++
      //          s1.succ.indices.foldLeft(List[SubstRepl]())((subst,i) => subst ++ unify(s1.succ(i), s2.succ(i)))
      //        ).distinct
    }

  /** Make `repl` distinct (if this algorithm does not preserve distinctness).
    * @return repl.distinct*/
  protected def distinctIfNeedBe(repl: List[SubstRepl]): List[SubstRepl] = repl.distinct
}


/**
  * Generic base for unification/matching algorithm for tactics.
  * Unify(shape, input) matches second argument `input` against the pattern `shape` of the first argument but not vice versa.
  * Matcher leaves input alone and only substitutes into shape.
  * Reasonably fast single-pass matcher.
  * @author Andre Platzer
  */
class UnificationMatchBase extends SchematicComposedUnificationMatch {

  /** @inheritdoc */
  protected override def compose(after: List[SubstRepl], before: List[SubstRepl]): List[SubstRepl] =
    if (after.isEmpty) before else if (before.isEmpty) after else {
      val us = Subst(after)
      try {
        //@todo uniform renaming part is flat and comes first so would really need a simple transitive closure treatment. And avoid there-and-back-again renamings. Such as (x~>y) compose (x~>y) should not be (x~>x)=()
        //@todo this is a rough approximation that may not generalize: leave vars alone
        val r = before.map(sp => try { (sp._1, if (sp._1.isInstanceOf[Variable]) sp._2 else us(sp._2)) } catch {case e: ProverException => throw e.inContext("unify.compose failed on " + sp._1 + " and " + sp._2 + " for " + us)}) ++
          after.filter(sp => !before.exists(op => op._1 == sp._1))
        logger.trace("      unify.compose: " + after.mkString(", ") + " with " + before.mkString(", ") + " is " + r.mkString(", "))
        r
      } catch {case e:Throwable => logger.trace("UnificationMatch.compose({" + after.mkString(", ") + "} , {" + before.mkString(", ") + "})"); throw e}
    }

}


/**
  * Unification/matching algorithm for fresh shapes (with built-in names such as those in axioms).
  * Unify(shape, input) matches second argument `input` against the pattern `shape` of the first argument but not vice versa.
  * Matcher leaves input alone and only substitutes into shape.
  * Reasonably fast single-pass matcher.
  *
  * @note Expects shape to have fresh names that do not occur in the input.
  *       Usually shape has all built-in names ending in underscore _ and no input is like that.
  * @author Andre Platzer
  */
class FreshUnificationMatch extends SchematicComposedUnificationMatch {

  //private def renamingPart(repl: List[SubstRepl]): List[SubstRepl] = repl.distinct.filter(sp => sp._1.isInstanceOf[Variable] && sp._2.isInstanceOf[Variable])
  /** apply renamings of `repl` to `e` (if there are any renamings at all) */
  private def renameIfNeedBe(repl: List[SubstRepl], e: Expression): Expression = {
    val ren = RenUSubst.renamingPartOnly(repl)
    if (ren.isEmpty)
      e
    else
      Subst(ren)(e)
  }
  /** apply renamings of `repl` to the replacements of `input` (if there any renamings in `repl` at all).
    * Filtering identity renamings that may be caused by renamings. */
  private def renameAllIfNeedBe(repl: List[SubstRepl], input: List[SubstRepl]): List[SubstRepl] = {
    //@note converse renaming to prepare for renaming transposition
    val ren = RenUSubst.renamingPartOnly(repl).map({ case (a, b) => (b, a)})
    if (ren.isEmpty)
      input
    else {
      val ur = Subst(ren)
      input.map(sp => (sp._1, ur(sp._2))).filter(sp => sp._1 != sp._2)
    }
  }
  /**
    * Quickly compose patterns coming from fresh shapes by just concatenating them.
    * If indeed the shape used fresh names that did not occur in the input, this fast composition is fine.
    * @ensures s==s.distinct && t==t.distinct => \result==\result.distinct
    */
  protected override def compose(after: List[SubstRepl], before: List[SubstRepl]): List[SubstRepl] =
  //  after ++ renameAllIfNeedBe(after, before)
  //@todo would this fail and crossrename if both before and after have renaming parts?
  join(renameAllIfNeedBe(after,before), renameAllIfNeedBe(before, after))

  /** Make `repl` distinct fast by directly returning it since this algorithm preserves distinctness in [[compose]].
    * @return repl.distinct */
  protected override def distinctIfNeedBe(repl: List[SubstRepl]): List[SubstRepl] = repl
  /** @inheritdoc
    * Faster since [[compose]] preserves distinctness. */
  protected override def Subst(subs: List[SubstRepl]): Subst = RenUSubst(subs)

  protected override def unifier(e1: Expression, e2: Expression, us: List[SubstRepl]): Subst = {
    if (true)
      try {
        Subst(us)
      } catch {
        case ex: Throwable => throw new UnificationException(e1, e2, "Invalid substitution computed", ex)
      }
    else {
      val ren = MultiRename(RenUSubst.renamingPartOnly(us))
      Subst(us.map(sp =>
        if (sp._1.isInstanceOf[UnitPredicational] || sp._1.isInstanceOf[UnitFunctional] ||
          sp._1.isInstanceOf[ProgramConst] || sp._1.isInstanceOf[SystemConst] || sp._1.isInstanceOf[DifferentialProgramConst] || sp._1.isInstanceOf[PredicationalOf])
          (sp._1, ren(sp._2))
        else
          sp
      ))
    }
  }
}

object RestrictedBiDiUnificationMatch extends RestrictedBiDiUnificationMatch
class RestrictedBiDiUnificationMatch extends FreshUnificationMatch {
  override protected def unify(e1: Term, e2: Term): List[SubstRepl] = e1 match {
    case _: Number => e2 match {case Number(_) => if (e1==e2) id else ununifiable(e1,e2) case _: DotTerm | _: FuncOf => unify(e2,e1) case _ => ununifiable(e1,e2)}
    // homomorphic cases
    case Neg(t)          => e2 match {case Neg(t2)          => unify(t,t2) case fn: FuncOf => unify(fn,e1) case _ => ununifiable(e1,e2)}
    case Differential(t) => e2 match {case Differential(t2) => unify(t,t2) case fn: FuncOf => unify(fn,e1) case _ => ununifiable(e1,e2)}
    // case o: BinaryCompositeTerm => e2 match {case o2: BinaryCompositeTerm if o2.reapply==o.reapply => unify(o.left,o.right, o2.left,o2.right) case _ => ununifiable(e1,e2)}
    case Plus  (l, r) => e2 match {case Plus  (l2,r2) => unifies2(l,r, l2,r2) case fn: FuncOf => unify(fn,e1) case _ => ununifiable(e1,e2)}
    case Minus (l, r) => e2 match {case Minus (l2,r2) => unifies2(l,r, l2,r2) case fn: FuncOf => unify(fn,e1) case _ => ununifiable(e1,e2)}
    case Times (l, r) => e2 match {case Times (l2,r2) => unifies2(l,r, l2,r2) case fn: FuncOf => unify(fn,e1) case _ => ununifiable(e1,e2)}
    case Divide(l, r) => e2 match {case Divide(l2,r2) => unifies2(l,r, l2,r2) case fn: FuncOf => unify(fn,e1) case _ => ununifiable(e1,e2)}
    case Power (l, r) => e2 match {case Power (l2,r2) => unifies2(l,r, l2,r2) case fn: FuncOf => unify(fn,e1) case _ => ununifiable(e1,e2)}
    // unofficial
    case Pair  (l, r) => e2 match {case Pair  (l2,r2) => unifies2(l,r, l2,r2) case fn: FuncOf => unify(fn,e1) case _ => ununifiable(e1,e2)}

    // default
    case _ => super.unify(e1, e2)
  }

  override protected def unify(e1: Formula, e2: Formula): List[SubstRepl] = e1 match {
    // homomorphic base cases
    case Equal       (l, r) => e2 match {case Equal       (l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case NotEqual    (l, r) => e2 match {case NotEqual    (l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case GreaterEqual(l, r) => e2 match {case GreaterEqual(l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case Greater     (l, r) => e2 match {case Greater     (l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case LessEqual   (l, r) => e2 match {case LessEqual   (l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case Less        (l, r) => e2 match {case Less        (l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}

    // homomorphic cases
    case Not(g)      => e2 match {case Not(g2)      => unify(g,g2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case And  (l, r) => e2 match {case And  (l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case Or   (l, r) => e2 match {case Or   (l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case Imply(l, r) => e2 match {case Imply(l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case Equiv(l, r) => e2 match {case Equiv(l2,r2) => unifies2(l,r, l2,r2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}

    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(g) => e2 match {case DifferentialFormula(g2) => unify(g,g2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}

    // pseudo-homomorphic cases
    //@todo join should be enough for the two unifiers in this case after they have been applied to the other side
    case Forall(vars, g) if vars.length==1 => e2 match {case Forall(v2,g2) if v2.length==1 => unifies2(vars.head,g, v2.head,g2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case Exists(vars, g) if vars.length==1 => e2 match {case Exists(v2,g2) if v2.length==1 => unifies2(vars.head,g, v2.head,g2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}

    // homomorphic cases
    case Box    (a, p)   => e2 match {case Box    (a2,p2) => unifies2(a,p, a2,p2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}
    case Diamond(a, p)   => e2 match {case Diamond(a2,p2) => unifies2(a,p, a2,p2) case p: PredOf => unify(p,e1) case _ => ununifiable(e1,e2)}

    // default implementation
    case _ => super.unify(e1, e2)
  }

  override protected def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] =
    if (x1==e2) id else e2 match {
      case v: Variable => unifier(x1,v)
      case fn: FuncOf => unifier(fn,x1)
      case _ => ununifiable(x1,e2)}

  override protected def unify(e1: Program, e2: Program): List[SubstRepl] = e1 match {
    case Assign(x, t)             => e2 match {case Assign(x2,t2)    => unifies2(x,t, x2,t2) case _: ProgramConst | _: SystemConst => unify(e2, e1) case _ => ununifiable(e1,e2)}
    case AssignAny(x)             => e2 match {case AssignAny(x2)    => unify(x,x2) case _: ProgramConst | _: SystemConst => unify(e2, e1) case _ => ununifiable(e1,e2)}
    case Test(f)                  => e2 match {case Test(f2)         => unify(f,f2) case _: ProgramConst | _: SystemConst => unify(e2, e1) case _ => ununifiable(e1,e2)}
    case ODESystem(a, h)          => e2 match {case ODESystem(a2,h2) => unifies2(a,h, a2,h2) case _: ProgramConst | _: SystemConst => unify(e2, e1) case _ => ununifiable(e1,e2)}
    case Choice(a, b)             => e2 match {case Choice(a2,b2)    => unifies2(a,b, a2,b2) case _: ProgramConst | _: SystemConst => unify(e2, e1) case _ => ununifiable(e1,e2)}
    case Compose(a, b)            => e2 match {case Compose(a2,b2)   => unifies2(a,b, a2,b2) case _: ProgramConst | _: SystemConst => unify(e2, e1) case _ => ununifiable(e1,e2)}
    case Loop(a)                  => e2 match {case Loop(a2)         => unify(a,a2) case _: ProgramConst | _: SystemConst => unify(e2, e1) case _ => ununifiable(e1,e2)}
    case Dual(a)                  => e2 match {case Dual(a2)         => unify(a,a2) case _: ProgramConst => unify(e2, e1) case _ => ununifiable(e1,e2)}
    case _ => super.unify(e1, e2)
  }

  override protected def unifyApplicationOf(F: (Function, Term) => Expression, f: Function, t: Term, e2: Expression): List[SubstRepl] = {
    val dt = coloredDotsTerm(t.sort)

    val uInv0 = unify(dt, t).map(_.swap.asInstanceOf[(Term, Term)]).toMap
    val e2repl = SubstitutionHelper.replacesFree(e2)(uInv0.get)
    val diff = StaticSemantics.symbols(dt) -- StaticSemantics.symbols(e2repl)

    val uInv1: Map[Term, Term] =
      if (diff.size == 1) {
        // 1 argument not mentioned verbatim, see if e2 has a single number to match with
        val nums = scala.collection.mutable.ListBuffer.empty[Number]
        ExpressionTraversal.traverseExpr(new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
            case n: Number => nums += n; Left(None)
            case _ => Left(None)
          }
        }, e2)
        if (nums.distinct.size == 1) {
          val unmatched = uInv0.find(_._2 == diff.head).get
          Map(nums.head -> unmatched._2)
        } else Map.empty
      } else Map.empty

    unifier(F(f, dt), SubstitutionHelper.replacesFree(e2repl)(uInv1.get))
  }

  override def join(s: List[(Expression, Expression)], t: List[(Expression, Expression)]): List[(Expression, Expression)] = {
    var j = t
    for (el <- s) {
      t.find(sp => sp._1 == el._1) match {
        case Some(sp) =>
          if (sp._2 != el._2) {
            val repl = try {
              val m = this(sp._2, el._2)
              if (m.subsDefsInput.nonEmpty) {
                if (m(sp._2) != sp._2) Some(el -> sp)
                else Some(sp -> el)
              } else None
            } catch {
              case _: UnificationException => None
            }
            repl match {
              case Some((what, repl)) => j = j.map({ case e if e==what => repl case x => x})
              case None => throw new SubstUnificationException(Subst(s), Subst(t))
            }
          }
          // else skip since same already present in t and therefore also in j
        case None =>
          j = el :: j
      }
    }
    j
  }
}


/**
  * Unification/matching algorithm for fresh shapes (with built-in names such as those in axioms).
  * Unify(shape, input) matches second argument `input` against the pattern `shape` of the first argument but not vice versa.
  * Matcher leaves input alone and only substitutes into shape.
  * Reasonably fast 1.5-pass matcher gathering uncomposed unifiers with a subsequent post-processing
  * pass preparing for the after renaming.
  *
  * @note Expects shape to have fresh names that do not occur in the input.
  *       Usually shape has all built-in names ending in underscore _ and no input is like that.
  * @author Andre Platzer
  */
private class FreshPostUnificationMatch extends SchematicComposedUnificationMatch {

  /**
    * Quickly compose patterns coming from fresh shapes by just concatenating them.
    * If indeed the shape used fresh names that did not occur in the input, this fash composition is fine.
    * @note May contain duplicates but that will be filtered out when forming Subst() anyhow.
    */
  protected override def compose(after: List[SubstRepl], before: List[SubstRepl]): List[SubstRepl] =
    before ++ after

  protected override def unifier(e1: Expression, e2: Expression, us: List[SubstRepl]): Subst = {
    val uss = us.distinct
    val ren = MultiRename(RenUSubst.renamingPartOnly(uss))
    Subst(uss.map(sp =>
      if (sp._1.isInstanceOf[UnitPredicational] || sp._1.isInstanceOf[UnitFunctional] ||
        sp._1.isInstanceOf[ProgramConst] || sp._1.isInstanceOf[SystemConst] || sp._1.isInstanceOf[DifferentialProgramConst] || sp._1.isInstanceOf[PredicationalOf] ||
        sp._1.isInstanceOf[ApplicationOf])
        (sp._1, ren(sp._2))
      else
        sp
    ))
  }
}


/**
  * Unification/matching algorithm for tactics, respecting only renamings.
  * Unify(shape, input) matches second argument `input` against the pattern `shape` of the first argument but not vice versa.
  * Matcher leaves input alone and only substitutes into shape.
  *
  * This matcher only excerpts variable renaming, ignoring all other reasons to unify.
  * @author Andre Platzer
  */
private final object RenUnificationMatch extends UnificationMatchBase {
  // incomplete unification cannot succeed during REVERIFY
  override private[infrastruct] val REVERIFY = Matcher.REVERIFY
  // Always skip unifiers except variables, which are handled by unifyVar
  override protected def unifier(e1: Expression, e2: Expression): List[SubstRepl] = id ensures (r => !e1.isInstanceOf[Variable])
  // Create unifiers for variables even if all others are skipped above
  override protected def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] = if (x1==e2) id else e2 match { case _: Variable => List(SubstRepl(x1,e2.asInstanceOf[Variable])) case _ => List(SubstRepl(x1,e2))}
  override protected def unifyVar(xp1: DifferentialSymbol, e2: Expression): List[SubstRepl] = if (xp1==e2) id else e2 match { case _: DifferentialSymbol => List(SubstRepl(xp1.x,e2.asInstanceOf[DifferentialSymbol].x)) case _ => List(SubstRepl(xp1,e2))}

  // composition is easier for flat renaming unifiers without substitutions
  override protected def compose(after: List[SubstRepl], before: List[SubstRepl]): List[SubstRepl] = before++after
}


/**
  * Unification/matching algorithm for tactics for URenAboveUSubst.
  * Unify(shape, input) matches second argument `input` against the pattern `shape` of the first argument but not vice versa.
  * Matcher leaves input alone and only substitutes into shape.
  * @author Andre Platzer
  */
private class UnificationMatchURenAboveUSubst extends /*Insistent*/Matcher with Logging { outer =>
  require(RenUSubst.semanticRenaming, "This implementation is meant for tactics built assuming semantic renaming")
  override private[infrastruct] val REVERIFY = Matcher.REVERIFY
  // pass 1
  private val renUMatcher = RenUnificationMatch
  // pass 2
  private val usubstUMatcher = new UnificationMatchBase { override private[infrastruct] val REVERIFY = false }

  private def unify(e1: Expression, e2: Expression): Subst = {
    val ren = renUMatcher(e1, e2)
    usubstUMatcher(ren(e1), e2) ++ ren
  }

  private def unify(e1: Sequent, e2: Sequent): Subst = {
    val ren = renUMatcher(e1, e2)
    usubstUMatcher(ren(e1), e2) ++ ren
  }

  override def apply(shape: Term, input: Term): Subst       = apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: Formula, input: Formula): Subst = apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: Program, input: Program): Subst = apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: DifferentialProgram, input: DifferentialProgram): Subst = apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])

  override def unifiable(shape: Expression, input: Expression): Option[Subst] = try {Some(apply(shape, input))} catch {case e: UnificationException => logger.debug("Expression un-unifiable " + e); None}

  override def unifiable(shape: Sequent, input: Sequent): Option[Subst] = try {Some(apply(shape, input))} catch {case e: UnificationException => logger.debug("Sequent un-unifiable " + e); None}

  override def apply(e1: Expression, e2: Expression): Subst = { try {
    unify(e1, e2)
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)}
  } ensures (r => !REVERIFY || r(e1) == e2, "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString + "\nshould become equal under their unifier unifier\n" + (unify(e1, e2)) + "\nhence: " + (unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString)

  override def apply(e1: Sequent, e2: Sequent): Subst = { try {
    unify(e1, e2)
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)}
  } ensures (r => !REVERIFY || r(e1) == e2, "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString + "\nshould become equal under their unifier unifier\n" + (unify(e1, e2)) + "\nhence: " + (unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString)
}

class UnificationMatchUSubstAboveURen extends /*Insistent*/Matcher with Logging {
  require(!RenUSubst.semanticRenaming, "This implementation is meant for tactics built assuming NO semantic renaming")
  override private[infrastruct] val REVERIFY = Matcher.REVERIFY
  // pass 1
  private val usubstUMatcher = new UnificationMatchBase {
    // partial so can't REVERIFY
    override private[infrastruct] val REVERIFY = false
    // Skip unifiers for variables in this pass
    override protected def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] = e2 match { case _: Variable => id case _ => ununifiable(x1,e2)}
    override protected def unifyVar(xp1: DifferentialSymbol, e2: Expression): List[SubstRepl] = e2 match { case _: DifferentialSymbol => id case _ => ununifiable(xp1,e2)}
  }
  // pass 2
  private val renUMatcher = RenUnificationMatch

  private val dot = DotTerm(Real, Some(0))

  override def apply(shape: Term, input: Term): Subst       = apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: Formula, input: Formula): Subst = apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: Program, input: Program): Subst = apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: DifferentialProgram, input: DifferentialProgram): Subst = apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])

  override def unifiable(shape: Expression, input: Expression): Option[Subst] = try {Some(apply(shape, input))} catch {case e: UnificationException => logger.debug("Expression un-unifiable " + e); None}

  override def unifiable(shape: Sequent, input: Sequent): Option[Subst] = try {Some(apply(shape, input))} catch {case e: UnificationException => logger.debug("Sequent un-unifiable " + e); None}

  private def staple(e: Expression, ren: Subst, subst: Subst): Subst = {
    import Augmentors.FormulaAugmentor
    //@note optimizable
    val argOfPred: Function => Term = p => e.asInstanceOf[Formula].findSubformula(g => g match {
        //@note want to know t
      case PredOf(q,t) if q==p => true
      case _ => false
    }).get._2.asInstanceOf[PredOf].child
    val posthocDottify: (Expression, Expression) =>Expression = (what: Expression, repl: Expression) => {
      //@todo could post-hoc: replaceFree(sp._2)(ren(argumentWhereOccured),DotTerm)
      //@note this is a ridiculous approximation but fast for matching against p(x_) or f(x_) or p(x_') or f(x_') in axioms
      val r = repl match {
        case rhs: Term    => ren(
          replaceFree(
            replaceFree(rhs)(ren(Variable("x_")), dot)
          ) (ren(DifferentialSymbol(Variable("x_"))), dot)
        )
        case rhs: Formula => ren(
          //@todo if this match doesn't work, could keep looking for argument in next occurrence of what
          replaceFree(rhs)(ren(argOfPred(what.asInstanceOf[PredOf].func)), dot)
        )
      }
      logger.debug("\t\t\tINFO: post-hoc optimizable: " + repl + " dottify " + r)
      r
    }
    //@note URename with TRANSPOSITION=true are their own inverses
    val inverseRename = (subst:RenUSubst) => RenUSubst(subst.subsDefsInput.map(sp =>
      (sp._1, sp._1 match {
        case FuncOf(_, DotTerm(_, _)) => posthocDottify(sp._1, sp._2)
        case PredOf(_, DotTerm(_, _)) => posthocDottify(sp._1, sp._2)
        case _ => ren(sp._2)
      } )))
    val renamedSubst = inverseRename(subst)
//    if (DEBUG) println("\n  unify: " + e1.prettyString + "\n  with:  " + e2.prettyString + "\n  subst: " + subst + "\n  gives: " + e1s + "\n  ren:   " + ren + "\n  invren: " + renamedSubst + "\n  sum:   " + (renamedSubst ++ ren) + "\n  result: " + (renamedSubst ++ ren)(e1))
    renamedSubst ++ ren
  }

  private def unify(e1: Expression, e2: Expression): Subst = {
    val subst = usubstUMatcher(e1, e2)
    logger.debug("\n  unify: " + e1.prettyString + "\n  with:  " + e2.prettyString + "\n  subst: " + subst + "\n  gives: " + subst(e1))
    val ren = renUMatcher(subst(e1), e2)
    //@note instead of post-hoc stapling could also add a third pass that unifies with the resulting renaming `ren` in mind.
    staple(e1, ren, subst)
  }

  private def unify(e1: Sequent, e2: Sequent): Subst = {
    val subst = usubstUMatcher(e1, e2)
    val ren = renUMatcher(subst(e1), e2)
    import Augmentors.SequentAugmentor
    staple(e1.toFormula, ren, subst)
  }

  override def apply(e1: Expression, e2: Expression): Subst = { try {
    unify(e1, e2)
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)}
  } ensures (r => !REVERIFY || r(e1) == e2, "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString + "\nshould become equal under their unifier unifier\n" + (unify(e1, e2)) + "\nhence: " + (unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString)

  override def apply(e1: Sequent, e2: Sequent): Subst = { try {
    unify(e1, e2)
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)}
  } ensures (r => !REVERIFY || r(e1) == e2, "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString + "\nshould become equal under their unifier unifier\n" + (unify(e1, e2)) + "\nhence: " + (unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString)

}

/** Unify any term for variables in ODEs. */
object NonSubstUnificationMatch extends FreshUnificationMatch {
  //@note Overriding additional unify... and other methods might become necessary,
  // since FreshUnificationMatch.apply attempts to create RenUSubst, which will fail in the usual unsupported cases
  // (numbers for variables etc.)

  /** Returns either a standard RenUSubst or the naive unifier. */
  def unifier(subs: List[(Expression, Expression)]): (Expression => Expression) = {
    val distinct = subs.distinct
    Try(RenUSubst(distinct)).toOption.getOrElse(NaiveSubst(distinct))
  }

  /** Naive substitution for unsupported RenUSubst cases (numbers for variables etc.) */
  private case class NaiveSubst(subs: List[(Expression, Expression)]) extends (Expression => Expression) {
    import Augmentors._

    def apply(e: Expression): Expression = e match {
      case prg: Program => subs.foldLeft(prg)({ case (p, (what: Term, repl: Term)) => p.replaceFree(what, repl) })
      case fml: Formula => subs.foldLeft(fml)({ case (p, (what: Term, repl: Term)) => p.replaceFree(what, repl) })
      case trm: Term => subs.foldLeft(trm)({ case (p, (what: Term, repl: Term)) => p.replaceFree(what, repl) })
      case f: Function => assert(false, "No completed expressions of FunctionKind can be constructed"); ???
    }
  }

  override def unifyODE(e1: DifferentialProgram, e2: DifferentialProgram): List[(Expression, Expression)] = super.unifyODE(e1, e2)

  override def unifies2(s1: Term, s2: Term, t1: Term, t2: Term): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    try {
      compose(unify(unifier(u1)(s2), t2), u1)
    } catch {
      case e: ProverException =>
        logger.trace("      try converse since " + e.getMessage)
        val u2 = unify(s2, t2)
        compose(unify(t1, unifier(u2)(s1)), u2)
    }
  }

  override def unifies2(s1: Formula, s2: Formula, t1: Formula, t2: Formula): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    try {
      compose(unify(unifier(u1)(s2), t2), u1)
    } catch {
      case e: ProverException =>
        logger.trace("      try converse since " + e.getMessage)
        val u2 = unify(s2, t2)
        compose(unify(t1, unifier(u2)(s1)), u2)
    }
  }

  override def unifies2(s1: Program, s2: Program, t1: Program, t2: Program): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    try {
      compose(unify(unifier(u1)(s2), t2), u1)
    } catch {
      case e: ProverException =>
        logger.trace("      try converse since " + e.getMessage)
        val u2 = unify(s2, t2)
        compose(unify(t1, unifier(u2)(s1)), u2)
    }
  }

  override def unifiesODE2(s1: DifferentialProgram, s2: DifferentialProgram, t1: DifferentialProgram,
                           t2: DifferentialProgram): List[SubstRepl] = {
    val u1 = unifyODE(s1, t1)
    try {
      compose(unifyODE(unifier(u1)(s2).asInstanceOf[DifferentialProgram], t2), u1)
    } catch {
      case _: ProverException =>
        val u2 = unifyODE(s2, t2)
        compose(unifyODE(t1, unifier(u2)(s1).asInstanceOf[DifferentialProgram]), u2)
    }
  }

  override def compose(after: List[SubstRepl], before: List[SubstRepl]): List[SubstRepl] =
    before ++ transpose(before, after)

  private def transpose(repl: List[SubstRepl], input: List[SubstRepl]): List[SubstRepl] = {
    val ren = repl.filter({ case (_: BaseVariable, _: BaseVariable) => true case _ => false }).map(_.swap)
    if (ren.isEmpty) input
    else {
      val ur = unifier(ren)
      input.map(sp => (sp._1, ur(sp._2))).filter(sp => sp._1 != sp._2)
    }
  }

  override def unifyVar(x1: Variable, e2: Expression): List[(Expression, Expression)] =
    if (x1==e2) id
    else unifier(x1, e2)
}
