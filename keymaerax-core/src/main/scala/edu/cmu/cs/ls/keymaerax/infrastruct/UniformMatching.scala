/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.bellerophon.UnificationException
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.{List, Nil}

/**
  * Uniform Matching algorithm for tactics by sweeping.
  * Their `unify(shape, input)` function matches second argument `input` against the pattern `shape` of the first argument, but not vice versa.
  * Uniform matching leaves `input` alone and only substitutes into `shape`.
  * Fast single-pass matcher that is defined by sweeping uniform matching.
  *
  * Sweeping Uniform Matching is provably sound and is fast but not necessarily complete.
  * @note Central recursive unification implementation.
  * @author Andre Platzer
  * @see [[SchematicUnificationMatch]]
  * @note a more comprehensive unification matcher would be found when jointly abstracting replacements at join conflicts if those have a joint lattice sup/inf.
  */
abstract class UniformMatching extends BaseMatcher {

  /** Create a (generalized) substitution from the given representation `subs`. */
  protected override def Subst(subs: List[SubstRepl]): Subst = if (false) RenUSubst(subs) else
    new FastURenAboveUSubst(subs)
    //new URenAboveUSubst(subs)

  /** `unifies2(s1,s2, t1,t2)` unifies the two expressions of shape (s2,s2) against the two inputs (t1,t2) by sweeping uniform matching.
    * {{{
    *   s1 = t1 | u1     s2 = t2 | u2
    *   -------------------------------- provided u1 and u2 compatible
    *   (s1,s2) = (t1,t2)  | u1 join u2
    * }}}
    */
  //@note optimized: repeated implementation per type to enable the static type inference that Scala generics won't give.
  protected def unifies2(s1:Expression, s2:Expression, t1:Expression, t2:Expression): List[SubstRepl] =
    join(unify(s1,t1), unify(s2,t2))
  protected def unifies2(s1:Term, s2:Term, t1:Term, t2:Term): List[SubstRepl] =
    join(unify(s1,t1), unify(s2,t2))
  protected def unifies2(s1:Formula, s2:Formula, t1:Formula, t2:Formula): List[SubstRepl] =
    join(unify(s1,t1), unify(s2,t2))
  protected def unifies2(s1:Program, s2:Program, t1:Program, t2:Program): List[SubstRepl] =
    join(unify(s1,t1), unify(s2,t2))
  protected def unifiesODE2(s1:DifferentialProgram, s2:DifferentialProgram, t1:DifferentialProgram, t2:DifferentialProgram): List[SubstRepl] =
    join(unifyODE(s1,t1), unifyODE(s2,t2))


  // schematic unification

  /** Algorithm for sweeping uniform matching.
    * @inheritdoc */
  protected def unify(e1: Term, e2: Term): List[SubstRepl] = e1 match {
      //@note prefer to unify Variables that are DifferentialSymbols by unifying their base variables.
    case xp: DifferentialSymbol           => unifyVar(xp,e2)
    case x: BaseVariable                  => unifyVar(x,e2)
    case n: Number                        => if (e1==e2) id else ununifiable(e1,e2)
    case f: UnitFunctional                => unifier(e1, e2)
    case FuncOf(f:Function, Nothing)      => unifier(e1, e2)
    case FuncOf(f: Function, t)           => e2 match {
        //@todo occurs check f\not\in unifier
      case FuncOf(g, t2) if f == g => unify(t, t2)
      // otherwise DotTerm abstraction of all occurrences of the argument t, so directly replace t by DotTerm
      case _                       => unifyApplicationOf(FuncOf, f, t, e2)
    }
    case Nothing                          => if (e1==e2) id else ununifiable(e1,e2)
    case _: DotTerm                       => unifier(e1, e2)
    //@note case o1:UnaryCompositeTerm  => e2 match {case o2:UnaryCompositeTerm  if o1.reapply==o2.reapply => unify(o1.child,o2.child) case _ => ununifiable(e1,e2)}
    //@note case o1:BinaryCompositeTerm => e2 match {case o2:BinaryCompositeTerm if o1.reapply==o2.reapply => unify(o1.left,o2.left) ++ unify(o1.right,o2.right) case _ => ununifiable(e1,e2)}
    // homomorphic cases
    case Neg(t)          => e2 match {case Neg(t2)          => unify(t,t2) case _ => ununifiable(e1,e2)}
    case Differential(t) => e2 match {case Differential(t2) => unify(t,t2) case _ => ununifiable(e1,e2)}
    // case o: BinaryCompositeTerm => e2 match {case o2: BinaryCompositeTerm if o2.reapply==o.reapply => unify(o.left,o.right, o2.left,o2.right) case _ => ununifiable(e1,e2)}
    case Plus  (l, r) => e2 match {case Plus  (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Minus (l, r) => e2 match {case Minus (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Times (l, r) => e2 match {case Times (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Divide(l, r) => e2 match {case Divide(l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Power (l, r) => e2 match {case Power (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    // unofficial
    case Pair  (l, r) => e2 match {case Pair  (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
  }


  /** Algorithm for sweeping uniform matching.
    * @inheritdoc */
  protected def unify(e1: Formula, e2: Formula): List[SubstRepl] = e1 match {
    case p: UnitPredicational             => unifier(e1, e2)
    case PredOf(f:Function, Nothing)      => unifier(e1, e2)
    case PredOf(f:Function, t)            => e2 match {
      case PredOf(g, t2) if f == g => unify(t, t2)
      // otherwise DotTerm abstraction of all FREE occurrences of the argument t, so directly replace t by DotTerm
      case _                       => unifyApplicationOf(PredOf, f, t, e2)
    }
    case PredicationalOf(f:Function, DotFormula) => unifier(e1, e2)
    case PredicationalOf(c, fml) => e2 match {
      case PredicationalOf(g, fml2) if c == g => unify(fml, fml2)
      // otherwise DotFormula abstraction of all FREE occurrences of the argument fml, so directly replace t by DotFormula
      case _ => //@todo List(SubstRepl(PredicationalOf(c,DotFormula), SubstitutionHelper.replaceFree(e2)(fml,DotFormula)))
        throw new UnsupportedOperationException("Not implemented for PredicationalOf matching: " + e1 + " for " + e2)
    }
    case DotFormula         => unifier(e1, e2)
    case True | False       => if (e1==e2) id else ununifiable(e1,e2)

    // homomorphic base cases
    case Equal       (l, r) => e2 match {case Equal       (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case NotEqual    (l, r) => e2 match {case NotEqual    (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case GreaterEqual(l, r) => e2 match {case GreaterEqual(l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Greater     (l, r) => e2 match {case Greater     (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case LessEqual   (l, r) => e2 match {case LessEqual   (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Less        (l, r) => e2 match {case Less        (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}

    // homomorphic cases
    case Not(g)      => e2 match {case Not(g2)      => unify(g,g2) case _ => ununifiable(e1,e2)}
    case And  (l, r) => e2 match {case And  (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Or   (l, r) => e2 match {case Or   (l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Imply(l, r) => e2 match {case Imply(l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Equiv(l, r) => e2 match {case Equiv(l2,r2) => unifies2(l,r, l2,r2) case _ => ununifiable(e1,e2)}

    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(g) => e2 match {case DifferentialFormula(g2) => unify(g,g2) case _ => ununifiable(e1,e2)}

    // pseudo-homomorphic cases
    case Forall(vars, g) if vars.length==1 => e2 match {case Forall(v2,g2) if v2.length==1 => unifies2(vars.head,g, v2.head,g2) case _ => ununifiable(e1,e2)}
    case Exists(vars, g) if vars.length==1 => e2 match {case Exists(v2,g2) if v2.length==1 => unifies2(vars.head,g, v2.head,g2) case _ => ununifiable(e1,e2)}

    // homomorphic cases
    case Box    (a, p)   => e2 match {case Box    (a2,p2) => unifies2(a,p, a2,p2) case _ => ununifiable(e1,e2)}
    case Diamond(a, p)   => e2 match {case Diamond(a2,p2) => unifies2(a,p, a2,p2) case _ => ununifiable(e1,e2)}
  }


  /** Algorithm for sweeping uniform matching.
    * @inheritdoc */
  protected def unify(e1: Program, e2: Program): List[SubstRepl] = e1 match {
    case a: ProgramConst          => unifier(e1, e2)
    case a: SystemConst           => if (FormulaTools.dualFree(e2)) unifier(e1, e2) else throw new UnificationException(e1, e2, "hybrid games with duals not allowed for SystemConst")
    case Assign(x, t)             => e2 match {case Assign(x2,t2)    => unifies2(x,t, x2,t2) case _ => ununifiable(e1,e2)}
    case AssignAny(x)             => e2 match {case AssignAny(x2)    => unify(x,x2) case _ => ununifiable(e1,e2)}
    case Test(f)                  => e2 match {case Test(f2)         => unify(f,f2) case _ => ununifiable(e1,e2)}
    case ODESystem(a, h)          => e2 match {case ODESystem(a2,h2) => unifies2(a,h, a2,h2) case _ => ununifiable(e1,e2)}
    case Choice(a, b)             => e2 match {case Choice(a2,b2)    => unifies2(a,b, a2,b2) case _ => ununifiable(e1,e2)}
    case Compose(a, b)            => e2 match {case Compose(a2,b2)   => unifies2(a,b, a2,b2) case _ => ununifiable(e1,e2)}
    case Loop(a)                  => e2 match {case Loop(a2)         => unify(a,a2) case _ => ununifiable(e1,e2)}
    case Dual(a)                  => e2 match {case Dual(a2)         => unify(a,a2) case _ => ununifiable(e1,e2)}
    //@note This case happens for standalone uniform substitutions on differential programs such as x'=f() or c as they come up in unification for example.
    case dp1: DifferentialProgram => e2 match {case dp2: DifferentialProgram => unifyODE(dp1, dp2) case _ => ununifiable(e1, e2)}
  }

  /** Algorithm for sweeping uniform matching.
    * @inheritdoc */
  protected def unifyODE(e1: DifferentialProgram, e2: DifferentialProgram): List[SubstRepl] = e1 match {
    case c: DifferentialProgramConst => unifier(e1, e2)
    case AtomicODE(xp, t)            => e2 match {case AtomicODE(xp2,t2) => unifies2(xp,t, xp2,t2) case _ => ununifiable(e1,e2)}
    case DifferentialProduct(a, b)   => e2 match {case DifferentialProduct(a2,b2) => unifiesODE2(a,b, a2,b2) case _ => ununifiable(e1,e2)}
  }


  // base cases

  /** unifyVar(x1,e2) gives a unifier making x1 equal to e2 unless it already is.
    * @return unifyVar(x1,x2)={x1~>x2} if x2 is a variable other than x1.
    *         unifyVar(x1,x1)={}
    * @throws UnificationException if e2 is not a variable
    */
  //@todo should this be protected for checking both are BaseVariables right away?
  protected def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] =
    if (x1==e2)  id else e2 match { case _: Variable => unifier(x1,e2.asInstanceOf[Variable]) case _ => ununifiable(x1,e2)}
  /** unifyVar(x1',e2) gives a unifier making x1' equal to e2 unless it already is.
    * @return unifyVar(x1',x2')={x1~>x2} if x2' is a differential variable other than x1'
    *         unifyVar(x1',x1')={}
    * @throws UnificationException if e2 is not a differential variable
    */
  protected def unifyVar(xp1: DifferentialSymbol, e2: Expression): List[SubstRepl] =
    if (xp1==e2) id else e2 match { case xp2: DifferentialSymbol => unifier(xp1.x,xp2.x)      case _ => ununifiable(xp1,e2)}


  /** DotTerms of different "colors" for components of a Tuple, uncolored DotTerm for non-Tuples
    * @example
    *   coloredDotsTerm(Real) = •
    *   coloredDotsTerm(Real*Real) = (•_1, •_2)
    *   coloredDotsTerm(Real*Real*Real) = (•_1, •_2, •_3)
    * */
  def coloredDotsTerm(s: Sort, color: Int = 1) : Term = {
    def coloredDotsTermWithIndex(s: Sort, color: Int) : (Int, Term) = s match {
      case Tuple(l, r) => {
        val (colorLeft,  dotsLeft)  = coloredDotsTermWithIndex(l, color)
        val (colorRight, dotsRight) = coloredDotsTermWithIndex(r, colorLeft)
        (colorRight, Pair(dotsLeft, dotsRight))
      }
      case _ => (color + 1, DotTerm(s, Some(color)))
    }
    s match {
      case Tuple(_, _) => coloredDotsTermWithIndex(s, color)._2
      case _ => DotTerm(s)
    }
  }

  /** Unify `f(t)` with `e2` where `F` is the operator (`FuncOf` or `PredOf`) that forms the ApplicationOf `f(t)`.
    *
    * 1) unify the argument `t` with a DotTerm abstraction `•` (t may be a tuple, then `•` is a tuple: [[coloredDotsTerm]])
    *    `ua = unify(•, t)`
    * 2) unifier = substitute with the inverse of the argument unifier e2
    *    `f(•) ~> ua^-1(e2)`
    *
    * @example given `t = (a, b)`, `e2 = a^2*b`
    *   1) `unify((•_1, •_2), (a, b))` yields
    *      `ua = •_1 ~> a, •_2 ~> b`
    *   2) the inverse is `ua^-1 = a ~> •_1, b ~> •_2`, therefore
    *      `ua^-1(e2) = •_1^2*•_2`, resulting in
    *      `f(•_1, •_2) ~> (•_1^2*•_2)`
    *
    * the inverse substitution is applied top-down, i.e., larger abstractions get precedence when components of `t` overlap:
    *   `t = (x, y, x + y)` and `e2 = x + y` yields `f(•_1, •_2, •_3) ~> •_3`; not `f(•_1, •_2, •_3) ~> •_1 + •_2`
    */
  protected def unifyApplicationOf(F: (Function, Term) => Expression, f: Function, t: Term, e2: Expression): List[SubstRepl] = {
    val dt = coloredDotsTerm(t.sort)
    val uInv = unify(dt, t).map(_.swap.asInstanceOf[(Term, Term)])
    unifier(F(f, dt), SubstitutionHelper.replacesFree(e2)(uInv.toMap.get))
  }

}

class UniformMatcher extends UniformMatching {
  protected override def unify(s1: Sequent, s2: Sequent): List[SubstRepl] =
    if (!(s1.ante.length == s2.ante.length && s1.succ.length == s2.succ.length)) ununifiable(s1,s2)
    else {
      val joinFolder = (u1: List[SubstRepl], f1: Formula, f2: Formula) =>
        join(u1, unify(f1, f2))
      val antesubst = s1.ante.indices.foldLeft(List[SubstRepl]()) ((subst,i) => joinFolder(subst, s1.ante(i), s2.ante(i)))
      val succsubst = s1.succ.indices.foldLeft(antesubst) ((subst,i) => joinFolder(subst, s1.succ(i), s2.succ(i)))
      succsubst
    }
}

object UniformMatcher extends UniformMatcher
