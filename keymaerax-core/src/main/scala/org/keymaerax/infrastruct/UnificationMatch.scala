/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.infrastruct

import org.keymaerax.{Configuration, Logging}
import org.keymaerax.bellerophon.{SeqUnificationException, SubstUnificationException, UnificationException}
import org.keymaerax.core._

import scala.collection.immutable.{List, Nil}

/**
 * `Matcher(shape, input)` matches second argument `input` against the pattern `shape` of the first argument but not
 * vice versa. Matcher leaves `input` alone and only substitutes into `shape`, i.e., gives a single-sided matcher.
 *
 * The following notation is used to indicate that `u` is the unifier computed for matching input `t` against shape `s`:
 * {{{
 *   s = t | u
 * }}}
 * That is `u` is the result of calling `Matcher.apply(s,t)`.
 *
 * @example
 *   {{{
 *   val s = Matcher("p()&q()".asFormula, "x<=0 & x^2>=0".asFormula)
 *   // gives {p() ~> x<=0, q() ~> x^2>=0}
 *   println(s)
 *   }}}
 * @example
 *   {{{
 *   val s = Matcher("[a;++b;]p()".asFormula, "[x:=x+1; ++ {x'=-x}]y<=0".asFormula)
 *   // gives {a ~> x:=x+1, b ~> {x'=-x}, p() ~> y<=0}
 *   println(s)
 *   }}}
 * @example
 *   {{{
 *   val s = Matcher("[a;++b;]p(||)".asFormula, "[x:=x+1; ++ {x'=-x}]x>=0".asFormula)
 *   // gives {a ~> x:=x+1, b ~> {x'=-x}, p(||) ~> x>=0}
 *   println(s)
 *   }}}
 * @example
 *   {{{
 *   // will throw UnificationException
 *   val s = Matcher("[a;++b;]p(||)".asFormula, "[x:=x+1;{x'=-x}]x>=0".asFormula)
 *   }}}
 * @author
 *   Andre Platzer
 * @see
 *   [[UnificationException]]
 * @see
 *   [[UnificationMatch]]
 * @see
 *   [[SchematicUnificationMatch]]
 */
trait Matcher extends ((Expression, Expression) => RenUSubst) {

  /** Check result of unification for being a valid unifier/matcher */
  private[infrastruct] val REVERIFY = Matcher.REVERIFY

  /**
   * The (generalized) substitutions used for unification purposes
   * @see
   *   [[RenUSubst]]
   */
  type Subst = RenUSubst

  /** Create a (generalized) substitution from the given representation `subs`. */
  // @todo optimizable .distinct may slow things down. Necessary all the time? distinctness being preserved in most unificaiton steps
  protected def Subst(subs: List[SubstRepl]): Subst = RenUSubst(subs.distinct)

  /**
   * A (generalized) substitution pair, which is either like a [[SubstitutionPair]] for uniform substitution or a pair
   * of [[Variable]] for uniform renaming.
   * @see
   *   [[SubstitutionPair]]
   */
  type SubstRepl = Tuple2[Expression, Expression]

  /**
   * Create a (generalized) substitution pair.
   * @see
   *   [[SubstitutionPair]]
   */
  protected def SubstRepl(what: Expression, repl: Expression): SubstRepl = (what, repl)

  /** Identity substitution `{}` that does not change anything. */
  protected val id: List[SubstRepl] = Nil

  /**
   * unifiable(shape, input) Compute some unifier matching `input` against the pattern `shape` if unifiable else None
   */
  def unifiable(shape: Expression, input: Expression): Option[Subst]

  /**
   * unifiable(shape, input) Compute some unifier matching `input` against the pattern `shape` if unifiable else None
   */
  def unifiable(shape: Sequent, input: Sequent): Option[Subst]

  /**
   * apply(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   */
  def apply(shape: Expression, input: Expression): Subst

  /**
   * apply(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  def apply(shape: Term, input: Term): Subst

  /**
   * apply(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  def apply(shape: Formula, input: Formula): Subst

  /**
   * apply(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  def apply(shape: Program, input: Program): Subst

  /**
   * apply(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  def apply(shape: DifferentialProgram, input: DifferentialProgram): Subst

  /**
   * apply(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  def apply(shape: Sequent, input: Sequent): Subst
}

object Matcher {

  /** Check result of unification for being a valid unifier/matcher */
  private[infrastruct] val REVERIFY = Configuration(Configuration.Keys.DEBUG) == "true"
}

/**
 * A matcher that insists on always matching as if there were arbitrary expressions as opposed to specializing to Term
 * versus Formula etc.
 * @author
 *   Andre Platzer
 */
trait InsistentMatcher extends Matcher with Logging {
  override def apply(shape: Term, input: Term): Subst =
    apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: Formula, input: Formula): Subst =
    apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: Program, input: Program): Subst =
    apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])
  override def apply(shape: DifferentialProgram, input: DifferentialProgram): Subst =
    apply(shape.asInstanceOf[Expression], input.asInstanceOf[Expression])

  override def unifiable(shape: Expression, input: Expression): Option[Subst] =
    try { Some(apply(shape, input)) }
    catch { case e: UnificationException => logger.debug("Expression un-unifiable " + e); None }

  override def unifiable(shape: Sequent, input: Sequent): Option[Subst] =
    try { Some(apply(shape, input)) }
    catch { case e: UnificationException => logger.debug("Sequent un-unifiable " + e); None }
}

/**
 * Basic matcher infrastructure that simply forwards all unification functionality to [[BaseMatcher.unify()]]. Only
 * apply() functions wrap exceptions in context while unify() functions simply pass it upwards.
 * @author
 *   Andre Platzer
 */
trait BaseMatcher extends Matcher with Logging {
  private def unifyExpr(e1: Expression, e2: Expression): Subst =
    if (e1.kind == e2.kind || e1.kind == ProgramKind && e2.kind == DifferentialProgramKind) e1 match {
      case t1: Term => val t2 = e2.asInstanceOf[Term]; unifier(t1, t2, unify(t1, t2))
      case f1: Formula => val f2 = e2.asInstanceOf[Formula]; unifier(f1, f2, unify(f1, f2))
      case p1: DifferentialProgram if !p1.isInstanceOf[ODESystem] =>
        val p2 = e2.asInstanceOf[DifferentialProgram]; unifier(p1, p2, unify(p1, p2))
      case p1: Program => val p2 = e2.asInstanceOf[Program]; unifier(p1, p2, unify(p1, p2))
    }
    else throw new UnificationException(e1, e2, "have incompatible kinds " + e1.kind + " and " + e2.kind)

  override def apply(e1: Expression, e2: Expression): Subst =
    if (e1.kind == e2.kind || e1.kind == ProgramKind && e2.kind == DifferentialProgramKind) e1 match {
      case t1: Term => apply(t1, e2.asInstanceOf[Term])
      case f1: Formula => apply(f1, e2.asInstanceOf[Formula])
      case p1: DifferentialProgram if !p1.isInstanceOf[ODESystem] => apply(p1, e2.asInstanceOf[DifferentialProgram])
      case p1: Program => apply(p1, e2.asInstanceOf[Program])
    }
    else throw new UnificationException(e1, e2, "have incompatible kinds " + e1.kind + " and " + e2.kind)

  override def apply(e1: Term, e2: Term): Subst = {
    try { unifier(e1, e2, unify(e1, e2)) }
    catch {
      case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)
    }
  } ensures
    (
      r => !REVERIFY || r(e1) == e2,
      "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString +
        "\nshould become equal under their unifier unifier\n" + Subst(unify(e1, e2)) + "\nhence: " +
        Subst(unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString,
    )

  override def apply(e1: Formula, e2: Formula): Subst = {
    try { unifier(e1, e2, unify(e1, e2)) }
    catch {
      case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)
    }
  } ensures
    (
      r => !REVERIFY || r(e1) == e2,
      "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString +
        "\nshould become equal under their unifier unifier\n" + Subst(unify(e1, e2)) + "\nhence: " +
        Subst(unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString,
    )

  override def apply(e1: Program, e2: Program): Subst = {
    try { unifier(e1, e2, unify(e1, e2)) }
    catch {
      case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)
    }
  } ensures
    (
      r => !REVERIFY || r(e1) == e2,
      "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString +
        "\nshould become equal under their unifier unifier\n" + Subst(unify(e1, e2)) + "\nhence: " +
        Subst(unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString,
    )

  override def apply(e1: DifferentialProgram, e2: DifferentialProgram): Subst = {
    try { unifier(e1, e2, unifyODE(e1, e2)) }
    catch {
      case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)
    }
  } ensures
    (
      r => !REVERIFY || r(e1) == e2,
      "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString +
        "\nshould become equal under their unifier unifier\n" + Subst(unify(e1, e2)) + "\nhence: " +
        Subst(unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString,
    )

  override def apply(e1: Sequent, e2: Sequent): Subst = {
    try { unifier(e1, e2, unify(e1, e2)) }
    catch { case ex: ProverException => throw ex.inContext("match " + e1.toString + "\n   with  " + e2.toString) }
  } ensures
    (
      r => !REVERIFY || r(e1) == e2,
      "unifier match expected to unify or fail\nunify: " + e1.prettyString + "\nwith:  " + e2.prettyString +
        "\nshould become equal under their unifier unifier\n" + Subst(unify(e1, e2)) + "\nhence: " +
        Subst(unify(e1, e2))(e1).prettyString + "\nwith:  " + e2.prettyString,
    )

  override def unifiable(shape: Expression, input: Expression): Option[Subst] =
    try { Some(unifyExpr(shape, input)) }
    catch { case e: UnificationException => logger.debug("Expression un-unifiable " + e); None }

  override def unifiable(shape: Sequent, input: Sequent): Option[Subst] =
    try { Some(unifier(shape, input, unify(shape, input))) }
    catch { case e: UnificationException => logger.debug("Sequent un-unifiable " + e); None }

  // @todo optimize: this may be slower than static type inference
  protected def unify(shape: Expression, input: Expression): List[SubstRepl] = shape match {
    case t1: Term => unify(t1, input.asInstanceOf[Term])
    case f1: Formula => unify(f1, input.asInstanceOf[Formula])
    case p1: DifferentialProgram if !p1.isInstanceOf[ODESystem] => unifyODE(p1, input.asInstanceOf[DifferentialProgram])
    case p1: Program => unify(p1, input.asInstanceOf[Program])
  }

  // subtype's responsibilities

  /**
   * unify(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  protected def unify(shape: Term, input: Term): List[SubstRepl]

  /**
   * unify(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  protected def unify(shape: Formula, input: Formula): List[SubstRepl]

  /**
   * unify(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  protected def unify(shape: Program, input: Program): List[SubstRepl]

  /**
   * unify(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  protected def unifyODE(shape: DifferentialProgram, input: DifferentialProgram): List[SubstRepl]

  /**
   * unify(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that
   * `\result(shape)==input`.
   * @throws UnificationException
   *   if `input` cannot be matched against the pattern `shape`.
   */
  protected def unify(shape: Sequent, input: Sequent): List[SubstRepl]

  // base tools

  /**
   * Construct the base unifier that forces `shape` and `input` to unify unless equal already
   * @requires
   *   shape is a substitutable expression (unchecked now as checked later).
   * @return
   *   {shape~>input} unless shape=input in which case it's {}.
   */
  protected def unifier(shape: Expression, input: Expression): List[SubstRepl] =
    if (shape == input) id else SubstRepl(shape, input) :: Nil

  /** Create the unifier `us` (which was formed for e1 and e2, just for the record). */
  protected def unifier(e1: Expression, e2: Expression, us: List[SubstRepl]): Subst = {
    val s = Subst(us)
    logger.debug("  unify: " + e1.prettyString + "\n  with:  " + e2.prettyString + "\n  via:   " + s)
    s
  }

  /** Create the unifier `us` (which was formed for e1 and e2, just for the record). */
  protected def unifier(e1: Sequent, e2: Sequent, us: List[SubstRepl]): Subst = {
    val s = Subst(us)
    logger.debug("  unify: " + e1.prettyString + "\n  with:  " + e2.prettyString + "\n  via:   " + s)
    s
  }

  /**
   * Indicates that `input` cannot be matched against the pattern `shape` by raising a [[UnificationException]].
   * @throws UnificationException
   *   always.
   */
  protected def ununifiable(shape: Expression, input: Expression): Nothing = {
    // println(new UnificationException(shape.toString, input.toString))
    throw new UnificationException(shape, input)
  }

  /**
   * Indicates that `input` cannot be matched against the pattern `shape` by raising a [[UnificationException]].
   * @throws UnificationException
   *   always.
   */
  protected def ununifiable(shape: Sequent, input: Sequent): Nothing = {
    // println(new UnificationException(shape.toString, input.toString))
    throw new SeqUnificationException(shape, input)
  }

  /**
   * Union of renaming substitution representations: `join(s, t)` gives the representation of `s` performed together
   * with `t`, if compatible.
   * {{{
   *   s \cup t = {p(.)~>F | (p(.)~>F) \in s}  ++  {(p(.)~>F) | (p(.)~>F) \in t}
   *   if s and t are compatible, so do not map the same p(.) or f(.) or a to different replacements
   * }}}
   * @return
   *   a substitution that has the same effect as applying both substitutions `s` and `t` simultaneously. Similar to
   *   returning `s++t` but skipping duplicates and checking compatibility in passing.
   * @ensures
   *   s==s.distinct && t==t.distinct => \result==\result.distinct
   * @time
   *   O(s.size*t.size)
   */
  // @todo optimizable: fast but tree maps would be a faster data structure than lists for this frequent operation
  protected def join(s: List[SubstRepl], t: List[SubstRepl]): List[SubstRepl] = {
    var j = t
    for (el <- s) {
      t.find(sp => sp._1 == el._1) match {
        case Some(sp) => if (sp._2 != el._2) throw new SubstUnificationException(Subst(s), Subst(t))
        // else skip since same already present in t
        case None => j = el :: j
      }
    }
    return j
    // @note the following alternative is elegant but keeps duplicates or gets slow if modified
    //    // return s++t while checking all new additions from s to not conflict with t
    //    s.foldLeft(t)((list, el) => if (t.find(sp => sp._1 == el._1) match {
    //      case Some(sp) => sp._2 == el._2
    //      case None => true
    //    })
    //      el :: list
    //    else
    //      throw new UnificationException("<unifier> " + s, "<unifier> " + t)
    //    )
  }

}

/**
 * Generic schematic unification/matching algorithm for tactics. Their `unify(shape, input)` function matches second
 * argument `input` against the pattern `shape` of the first argument, but not vice versa. Thus, the matcher leaves
 * `input` alone and only substitutes into `shape`. Reasonably fast single-pass matcher that is defined by recursive
 * unification from compositions.
 * @note
 *   Central recursive unification implementation.
 * @author
 *   Andre Platzer
 * @see
 *   [[UniformMatching]]
 */
abstract class SchematicUnificationMatch extends BaseMatcher {

  /**
   * Composition of renaming substitution representations: `compose(after, before)` gives the representation of `after`
   * performed after `before`.
   * {{{
   *   s after t = {p(.)~>s(F) | (p(.)~>F) \in t}  ++  {(p(.)~>F) \in s | (p(.)~>G) \notin t for all G}
   * }}}
   * @return
   *   a substitution that has the same effect as applying substitution `after` after applying substitution `before`.
   */
  protected def compose(after: List[SubstRepl], before: List[SubstRepl]): List[SubstRepl]

  /**
   * `unifies2(s1,s2, t1,t2)` unifies the two expressions of shape (s2,s2) against the two inputs (t1,t2) by
   * single-sided matching.
   * {{{
   *   s1 = t1 | u1     u1(s2) = t2 | u2
   *   ----------------------------------
   *   (s1,s2) = (t1,t2)  | u2 after u1
   * }}}
   * @note
   *   For single-sided matching the unifier u1 is not applied to t2 on the right premise.
   */
  // @note optimized: repeated implementation per type to enable the static type inference that Scala generics won't give.
  protected def unifies2(s1: Expression, s2: Expression, t1: Expression, t2: Expression): List[SubstRepl]
  protected def unifies2(s1: Term, s2: Term, t1: Term, t2: Term): List[SubstRepl]
  protected def unifies2(s1: Formula, s2: Formula, t1: Formula, t2: Formula): List[SubstRepl]
  protected def unifies2(s1: Program, s2: Program, t1: Program, t2: Program): List[SubstRepl]
  protected def unifiesODE2(
      s1: DifferentialProgram,
      s2: DifferentialProgram,
      t1: DifferentialProgram,
      t2: DifferentialProgram,
  ): List[SubstRepl]

  // schematic unification

  /**
   * A simple recursive unification algorithm for single-sided matching.
   * @inheritdoc
   */
  protected def unify(e1: Term, e2: Term): List[SubstRepl] = e1 match {
    // @note prefer to unify Variables that are DifferentialSymbols by unifying their base variables.
    case xp: DifferentialSymbol => unifyVar(xp, e2)
    case x: BaseVariable => unifyVar(x, e2)
    case n: Number => if (e1 == e2) id else ununifiable(e1, e2)
    case f: UnitFunctional => unifier(e1, e2)
    case FuncOf(f: Function, Nothing) => unifier(e1, e2)
    case FuncOf(f: Function, t) => e2 match {
        case FuncOf(g, t2) if f == g => unify(t, t2)
        // otherwise DotTerm abstraction of all occurrences of the argument
        case _ => unifyApplicationOf(FuncOf, f, t, e2)
      }
    case Nothing => if (e1 == e2) id else ununifiable(e1, e2)
    case _: DotTerm => unifier(e1, e2)
    // @note case o1:UnaryCompositeTerm  => e2 match {case o2:UnaryCompositeTerm  if o1.reapply==o2.reapply => unify(o1.child,o2.child) case _ => ununifiable(e1,e2)}
    // @note case o1:BinaryCompositeTerm => e2 match {case o2:BinaryCompositeTerm if o1.reapply==o2.reapply => unify(o1.left,o2.left) ++ unify(o1.right,o2.right) case _ => ununifiable(e1,e2)}
    // homomorphic cases
    case Neg(t) => e2 match {
        case Neg(t2) => unify(t, t2)
        case _ => ununifiable(e1, e2)
      }
    case Differential(t) => e2 match {
        case Differential(t2) => unify(t, t2)
        case _ => ununifiable(e1, e2)
      }
    // case o: BinaryCompositeTerm => e2 match {case o2: BinaryCompositeTerm if o2.reapply==o.reapply => unify(o.left,o.right, o2.left,o2.right) case _ => ununifiable(e1,e2)}
    case Plus(l, r) => e2 match {
        case Plus(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Minus(l, r) => e2 match {
        case Minus(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Times(l, r) => e2 match {
        case Times(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Divide(l, r) => e2 match {
        case Divide(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Power(l, r) => e2 match {
        case Power(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    // unofficial
    case Pair(l, r) => e2 match {
        case Pair(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
  }

  /**
   * A simple recursive unification algorithm for single-sided matching.
   * @inheritdoc
   */
  protected def unify(e1: Formula, e2: Formula): List[SubstRepl] = e1 match {
    case p: UnitPredicational => unifier(e1, e2)
    case PredOf(f: Function, Nothing) => unifier(e1, e2)
    case PredOf(f: Function, t) => e2 match {
        case PredOf(g, t2) if f == g => unify(t, t2)
        // otherwise DotTerm abstraction of all occurrences of the argument
        case _ => unifyApplicationOf(PredOf, f, t, e2)
      }
    case PredicationalOf(f: Function, DotFormula) => unifier(e1, e2)
    case PredicationalOf(c, fml) => e2 match {
        case PredicationalOf(g, fml2) if c == g => unify(fml, fml2)
        // otherwise DotFormula abstraction of all occurrences of the argument
        case _ => // @todo List(SubstRepl(PredicationalOf(c,DotFormula), SubstitutionHelper.replaceFree(e2)(fml,DotFormula)))
          throw new UnsupportedOperationException("Not implemented for PredicationalOf matching: " + e1 + " for " + e2)
      }
    case DotFormula => unifier(e1, e2)
    case True | False => if (e1 == e2) id else ununifiable(e1, e2)

    // homomorphic base cases
    case Equal(l, r) => e2 match {
        case Equal(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case NotEqual(l, r) => e2 match {
        case NotEqual(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case GreaterEqual(l, r) => e2 match {
        case GreaterEqual(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Greater(l, r) => e2 match {
        case Greater(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case LessEqual(l, r) => e2 match {
        case LessEqual(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Less(l, r) => e2 match {
        case Less(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }

    // homomorphic cases
    case Not(g) => e2 match {
        case Not(g2) => unify(g, g2)
        case _ => ununifiable(e1, e2)
      }
    case And(l, r) => e2 match {
        case And(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Or(l, r) => e2 match {
        case Or(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Imply(l, r) => e2 match {
        case Imply(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }
    case Equiv(l, r) => e2 match {
        case Equiv(l2, r2) => unifies2(l, r, l2, r2)
        case _ => ununifiable(e1, e2)
      }

    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(g) => e2 match {
        case DifferentialFormula(g2) => unify(g, g2)
        case _ => ununifiable(e1, e2)
      }

    // pseudo-homomorphic cases
    // @todo join should be enough for the two unifiers in this case after they have been applied to the other side
    case Forall(vars, g) if vars.length == 1 =>
      e2 match {
        case Forall(v2, g2) if v2.length == 1 => unifies2(vars.head, g, v2.head, g2)
        case _ => ununifiable(e1, e2)
      }
    case Exists(vars, g) if vars.length == 1 =>
      e2 match {
        case Exists(v2, g2) if v2.length == 1 => unifies2(vars.head, g, v2.head, g2)
        case _ => ununifiable(e1, e2)
      }

    // homomorphic cases
    case Box(a, p) => e2 match {
        case Box(a2, p2) => unifies2(a, p, a2, p2)
        case _ => ununifiable(e1, e2)
      }
    case Diamond(a, p) => e2 match {
        case Diamond(a2, p2) => unifies2(a, p, a2, p2)
        case _ => ununifiable(e1, e2)
      }
  }

  /**
   * A simple recursive unification algorithm for single-sided matching.
   * @inheritdoc
   */
  protected def unify(e1: Program, e2: Program): List[SubstRepl] = e1 match {
    case a: ProgramConst => unifier(e1, e2)
    case a: SystemConst =>
      if (FormulaTools.dualFree(e2)) unifier(e1, e2)
      else throw new UnificationException(e1, e2, "hybrid games with duals not allowed for SystemConst")
    case Assign(x, t) => e2 match {
        case Assign(x2, t2) => unifies2(x, t, x2, t2)
        case _ => ununifiable(e1, e2)
      }
    case AssignAny(x) => e2 match {
        case AssignAny(x2) => unify(x, x2)
        case _ => ununifiable(e1, e2)
      }
    case Test(f) => e2 match {
        case Test(f2) => unify(f, f2)
        case _ => ununifiable(e1, e2)
      }
    case ODESystem(a, h) => e2 match {
        case ODESystem(a2, h2) => unifies2(a, h, a2, h2)
        case _ => ununifiable(e1, e2)
      }
    case Choice(a, b) => e2 match {
        case Choice(a2, b2) => unifies2(a, b, a2, b2)
        case _ => ununifiable(e1, e2)
      }
    case Compose(a, b) => e2 match {
        case Compose(a2, b2) => unifies2(a, b, a2, b2)
        case _ => ununifiable(e1, e2)
      }
    case Loop(a) => e2 match {
        case Loop(a2) => unify(a, a2)
        case _ => ununifiable(e1, e2)
      }
    case Dual(a) => e2 match {
        case Dual(a2) => unify(a, a2)
        case _ => ununifiable(e1, e2)
      }
    // @note This case happens for standalone uniform substitutions on differential programs such as x'=f() or c as they come up in unification for example.
    case dp1: DifferentialProgram => e2 match {
        case dp2: DifferentialProgram => unifyODE(dp1, dp2)
        case _ => ununifiable(e1, e2)
      }
  }

  /**
   * A simple recursive unification algorithm for single-sided matching.
   * @inheritdoc
   */
  protected def unifyODE(e1: DifferentialProgram, e2: DifferentialProgram): List[SubstRepl] = e1 match {
    case c: DifferentialProgramConst => unifier(e1, e2)
    case AtomicODE(xp, t) => e2 match {
        case AtomicODE(xp2, t2) => unifies2(xp, t, xp2, t2)
        case _ => ununifiable(e1, e2)
      }
    case DifferentialProduct(a, b) => e2 match {
        case DifferentialProduct(a2, b2) => unifiesODE2(a, b, a2, b2)
        case _ => ununifiable(e1, e2)
      }
  }

  // base cases

  /**
   * unifyVar(x1,e2) gives a unifier making x1 equal to e2 unless it already is.
   * @return
   *   unifyVar(x1,x2)={x1~>x2} if x2 is a variable other than x1. unifyVar(x1,x1)={}
   * @throws UnificationException
   *   if e2 is not a variable
   */
  protected def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] =
    if (x1 == e2) id
    else e2 match {
      case _: Variable => unifier(x1, e2.asInstanceOf[Variable])
      case _ => ununifiable(x1, e2)
    }

  /**
   * unifyVar(x1',e2) gives a unifier making x1' equal to e2 unless it already is.
   * @return
   *   unifyVar(x1',x2')={x1~>x2} if x2' is a differential variable other than x1' unifyVar(x1',x1')={}
   * @throws UnificationException
   *   if e2 is not a differential variable
   */
  protected def unifyVar(xp1: DifferentialSymbol, e2: Expression): List[SubstRepl] =
    if (xp1 == e2) id
    else e2 match {
      case xp2: DifferentialSymbol => unifier(xp1.x, xp2.x)
      case _ => ununifiable(xp1, e2)
    }

  /**
   * DotTerms of different "colors" for components of a Tuple, uncolored DotTerm for non-Tuples
   * @example
   *   {{{
   *   coloredDotsTerm(Real) = •_0
   *   coloredDotsTerm(Real*Real) = (•_0, •_1)
   *   coloredDotsTerm(Real*Real*Real) = (•_0, •_1, •_2)
   *   }}}
   */
  def coloredDotsTerm(s: Sort, color: Int = 0): Term = {
    def coloredDotsTermWithIndex(s: Sort, color: Int): (Int, Term) = s match {
      case Tuple(l, r) =>
        val (colorLeft, dotsLeft) = coloredDotsTermWithIndex(l, color)
        val (colorRight, dotsRight) = coloredDotsTermWithIndex(r, colorLeft)
        (colorRight, Pair(dotsLeft, dotsRight))
      case _ => (color + 1, DotTerm(s, Some(color)))
    }
    s match {
      case Tuple(_, _) => coloredDotsTermWithIndex(s, color)._2
      case _ => DotTerm(s, Some(color))
    }
  }

  /**
   * Unify `f(t)` with `e2` where `F` is the operator (`FuncOf` or `PredOf`) that forms the ApplicationOf `f(t)`.
   *
   *   1. unify the argument `t` with a DotTerm abstraction `•` (t may be a tuple, then `•` is a tuple:
   *      [[coloredDotsTerm]]) `ua = unify(•, t)`
   *   1. unifier = substitute with the inverse of the argument unifier e2 `f(•) ~> ua^-1(e2)`
   *
   * @example
   *   given `t = (a, b)`, `e2 = a^2*b`
   *   1. `unify((•_0, •_1), (a, b))` yields `ua = •_0 ~> a, •_1 ~> b`
   *   1. the inverse is `ua^-1 = a ~> •_0, b ~> •_1`, therefore `ua^-1(e2) = •_0^2*•_1`, resulting in `f(•_0, •_1) ~>
   *      (•_0^2*•_1)`
   *
   * The inverse substitution is applied top-down, i.e., larger abstractions get precedence when components of `t`
   * overlap: `t = (x, y, x + y)` and `e2 = x + y` yields `f(•_0, •_1, •_2) ~> •_2`; not `f(•_0, •_1, •_2) ~> •_0 + •_1`
   */
  protected def unifyApplicationOf(
      F: (Function, Term) => Expression,
      f: Function,
      t: Term,
      e2: Expression,
  ): List[SubstRepl] = {
    val dt = coloredDotsTerm(t.sort)
    val uInv = unify(dt, t).map(_.swap.asInstanceOf[(Term, Term)])
    unifier(F(f, dt), SubstitutionHelper.replacesFree(e2)(uInv.toMap.get))
  }

}
