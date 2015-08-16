/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Unification/matching algorithm for tactics.
 * Matches second argument against the pattern of the first argument but not vice versa.
 * @author Andre Platzer
 */
object UnificationMatch extends ((Expression,Expression) => RenUSubst) {
//  type Subst = USubst
//  private def Subst(subs: List[SubstRepl]): Subst = USubst(subs)
//  type SubstRepl = SubstitutionPair
//  private def SubstRepl(what: Expression, repl: Expression): SubstRepl = SubstitutionPair(what,repl)
  type Subst = RenUSubst
  private def Subst(subs: List[SubstRepl]): Subst = RenUSubst(subs.distinct)
  type SubstRepl = scala.Predef.Pair[Expression,Expression]
  private def SubstRepl(what: Expression, repl: Expression): SubstRepl = (what,repl)

  //

  private val id: List[SubstRepl] = Nil

  def apply(e1: Expression, e2: Expression): Subst = if (e1.kind==e2.kind) e1 match {
    case t1: Term => apply(t1, e2.asInstanceOf[Term])
    case f1: Formula => apply(f1, e2.asInstanceOf[Formula])
    case p1: Program => apply(p1, e2.asInstanceOf[Program])
  } else throw new UnificationException(e1.prettyString, e2.prettyString, "have different kinds " + e1.kind + " and " + e2.kind)

  /** Compute some unifier if unifiable else None */
  def unifiable(e1: Expression, e2: Expression): Option[Subst] = try {Some(apply(e1, e2))} catch {case e: UnificationException => println("Expression unifiable " + e); None}

  /** Compute some unifier if unifiable else None */
  def unifiable(e1: Sequent, e2: Sequent): Option[Subst] = try {Some(apply(e1, e2))} catch {case e: UnificationException => println("Sequent unifiable " + e); None}

  //  def apply(t1: Term, t2: Term): Option[Subst] = {try { Some(Subst(unify(t1,t2))) } catch { case _: UnificationException => None }
//  } ensuring (r => r.isEmpty || r.get(t1) == t2, "unifier match makes " + t1 + " and " + t2 + " equal")
//
//  def apply(f1: Formula, f2: Formula): Option[Subst] = {try { Some(Subst(unify(f1,f2))) } catch { case _: UnificationException => None }
//  } ensuring (r => r.isEmpty || r.get(f1) == f2, "unifier match makes " + f1 + " and " + f2 + " equal")
//
//  def apply(p1: Program, p2: Program): Option[Subst] = {try { Some(Subst(unify(p1,p2))) } catch { case _: UnificationException => None }
//  } ensuring (r => r.isEmpty || r.get(p1) == p2, "unifier match makes " + p1 + " and " + p2 + " equal")
//
//  def apply(s1: Sequent, s2: Sequent): Option[Subst] = {try { Some(Subst(unify(s1,s2))) } catch { case _: UnificationException => None }
//  } ensuring (r => r.isEmpty || r.get(s1) == s2, "unifier match makes " + s1 + " and " + s2 + " equal")

  //@note To circumvent shortcomings of renaming-unaware unification algorithm, the following code unifies for renaming, renames, and then reunifies the renamed outcomes for substitution
  def apply(e1: Term, e2: Term): Subst = {try {
    val ren = RenUSubst.renamingPart(unify(e1,e2))
    Subst(unify(ren(e1),e2) ++ ren.subsDefsInput)
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + " with " + e2.prettyString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal")

  def apply(e1: Formula, e2: Formula): Subst = {try {
    val ren = RenUSubst.renamingPart(unify(e1,e2))
    Subst(unify(ren(e1),e2) ++ ren.subsDefsInput)
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + " with " + e2.prettyString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal")

  def apply(e1: Program, e2: Program): Subst = {try {
    val ren = RenUSubst.renamingPart(unify(e1,e2))
    Subst(unify(ren(e1),e2) ++ ren.subsDefsInput)
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + " with " + e2.prettyString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal")

  def apply(e1: Sequent, e2: Sequent): Subst = {try {
    val ren = RenUSubst.renamingPart(unify(e1,e2))
    //println("Unifying " + e1 + " and " + e2 + "\nwith renaming " + ren + " gives " + ren(e1) + " led to\n" + unify(ren(e1),e2) + " and ")
    Subst(unify(ren(e1),e2) ++ ren.subsDefsInput)
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.toString + " with " + e2.toString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal")

  private def ununifiable(e1: Expression, e2: Expression): Nothing = {println(new UnificationException(e1.toString, e2.toString)); throw new UnificationException(e1.toString, e2.toString)}

  private def ununifiable(e1: Sequent, e2: Sequent): Nothing = {println(new UnificationException(e1.toString, e2.toString)); throw new UnificationException(e1.toString, e2.toString)}

//  private def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] = if (x1==e2) id else ununifiable(x1,e2)
//  private def unifyVar(xp1: DifferentialSymbol, e2: Expression): List[SubstRepl] = if (xp1==e2) id else ununifiable(xp1,e2)
  private def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] = if (x1==e2) id else if (e2.isInstanceOf[Variable]) List(SubstRepl(x1,e2.asInstanceOf[Variable])) else ununifiable(x1,e2)
  private def unifyVar(xp1: DifferentialSymbol, e2: Expression): List[SubstRepl] = if (xp1==e2) id else if (e2.isInstanceOf[DifferentialSymbol]) List(SubstRepl(xp1.x,e2.asInstanceOf[DifferentialSymbol].x)) else ununifiable(xp1,e2)

  /** A simple recursive unification algorithm that actually just recursive single-sided matching without occurs check */
  private def unify(e1: Term, e2: Term): List[SubstRepl] = e1 match {
    case x: Variable                      => unifyVar(x,e2)
    case xp: DifferentialSymbol           => unifyVar(xp,e2)
    case n: Number                        => if (e1==e2) id else ununifiable(e1,e2)
    case FuncOf(f:Function, Anything)     => if (e1==e2) id else List(SubstRepl(e1, e2))
    case FuncOf(f:Function, Nothing)      => if (e1==e2) id else List(SubstRepl(e1, e2))
    case FuncOf(f:Function, t)            => e2 match {
      case FuncOf(g, t2) if f==g => unify(t,t2) /*case DotTerm => List(SubstRepl(DotTerm, t1))*/
      // otherwise DotTerm abstraction of all occurrences of the argument
      case _ => List(SubstRepl(FuncOf(f,DotTerm), SubstitutionHelper.replaceFree(e2)(t,DotTerm)))
    }
    case Anything | Nothing               => if (e1==e2) id else ununifiable(e1,e2)
    case DotTerm                          => if (e1==e2) id else List(SubstRepl(e1, e2))
    // homomorphic cases
    case Neg(t)       => e2 match {case Neg(t2) => unify(t,t2) case _ => ununifiable(e1,e2)}
    case Plus(l, r)   => e2 match {case Plus  (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Minus(l, r)  => e2 match {case Minus (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Times(l, r)  => e2 match {case Times (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Divide(l, r) => e2 match {case Divide(l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Power(l, r)  => e2 match {case Power (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Differential(t) => e2 match {case Differential(t2) => unify(t,t2) case _ => ununifiable(e1,e2)}
    // unofficial
    case Pair(l, r)   => e2 match {case Pair(l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
  }

  private def unify(e1: Formula, e2: Formula): List[SubstRepl] = e1 match {
    case PredOf(f:Function, Anything)     => if (e1==e2) id else List(SubstRepl(e1, e2))
    case PredOf(f:Function, Nothing)      => if (e1==e2) id else List(SubstRepl(e1, e2))
    case PredOf(f:Function, t)            => e2 match {
      case PredOf(g, t2) if f == g => unify(t, t2)
      // otherwise DotTerm abstraction of all occurrences of the argument
      case _ => List(SubstRepl(PredOf(f,DotTerm), SubstitutionHelper.replaceFree(e2)(t,DotTerm)))
    }
    case PredicationalOf(f:Function, DotFormula) => if (e1==e2) id else List(SubstRepl(e1, e2))
    case PredicationalOf(c, fml) => e2 match {
      case PredicationalOf(g, fml2) if c == g => unify(fml, fml2)
      // otherwise DotFormula abstraction of all occurrences of the argument
      case _ => ??? //@todo List(SubstRepl(PredicationalOf(c,DotFormula), SubstitutionHelper.replaceFree(e2)(fml,DotFormula)))
    }
    case DotFormula         => if (e1==e2) id else List(SubstRepl(e1, e2))
    case True | False       => if (e1==e2) id else ununifiable(e1,e2)

    // homomorphic base cases
    case Equal(l, r)        => e2 match {case Equal       (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case NotEqual(l, r)     => e2 match {case NotEqual    (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case GreaterEqual(l, r) => e2 match {case GreaterEqual(l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Greater(l, r)      => e2 match {case Greater     (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case LessEqual(l, r)    => e2 match {case LessEqual   (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Less(l, r)         => e2 match {case Less        (l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}

    // homomorphic cases
    case Not(g)      => e2 match {case Not(g2)      => unify(g,g2) case _ => ununifiable(e1,e2)}
    case And(l, r)   => e2 match {case And(l2,r2)   => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Or(l, r)    => e2 match {case Or(l2,r2)    => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Imply(l, r) => e2 match {case Imply(l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}
    case Equiv(l, r) => e2 match {case Equiv(l2,r2) => unify(l,l2) ++ unify(r,r2) case _ => ununifiable(e1,e2)}

    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(g) => e2 match {case DifferentialFormula(g2) => unify(g,g2) case _ => ununifiable(e1,e2)}

    // binding cases add bound variables to u
    case Forall(vars, g) => e2 match {case Forall(v2,g2) if vars==v2 => unify(g,g2)
      case Forall(v2,g2) if vars.length==1&&v2.length==1 => unifyVar(vars.head, v2.head) ++ unify(g,g2) case _ => ununifiable(e1,e2)}
    case Exists(vars, g) => e2 match {case Exists(v2,g2) if vars==v2 => unify(g,g2)
      case Exists(v2,g2) if vars.length==1&&v2.length==1 => unifyVar(vars.head, v2.head) ++ unify(g,g2) case _ => ununifiable(e1,e2)}

    case Box(a, p)       => e2 match {case Box(a2,p2)     => unify(a,a2) ++ unify(p,p2) case _ => ununifiable(e1,e2)}
    case Diamond(a, p)   => e2 match {case Diamond(a2,p2) => unify(a,a2) ++ unify(p,p2) case _ => ununifiable(e1,e2)}
  }

  private def unify(e1: Program, e2: Program): List[SubstRepl] = e1 match {
    case a: ProgramConst             => if (e1==e2) id else List(SubstRepl(e1, e2))
    case Assign(x, t)                => e2 match {case Assign(x2,t2) => unifyVar(x,x2) ++ unify(t,t2) case _ => ununifiable(e1,e2)}
    case DiffAssign(xp, t)           => e2 match {case DiffAssign(xp2,t2) => unifyVar(xp,xp2) ++ unify(t,t2) case _ => ununifiable(e1,e2)}
    case AssignAny(x)                => e2 match {case AssignAny(x2) => unifyVar(x,x2) case _ => ununifiable(e1,e2)}
    case Test(f)                     => e2 match {case Test(f2) => unify(f,f2) case _ => ununifiable(e1,e2)}
    case ODESystem(a, h)             => e2 match {case ODESystem(a2,h2) => unifyODE(a,a2) ++ unify(h,h2) case _ => ununifiable(e1,e2)}
    case Choice(a, b)                => e2 match {case Choice(a2,b2) => unify(a,a2) ++ unify(b,b2) case _ => ununifiable(e1,e2)}
    case Compose(a, b)               => e2 match {case Compose(a2,b2) => unify(a,a2) ++ unify(b,b2) case _ => ununifiable(e1,e2)}
    case Loop(a)                     => e2 match {case Loop(a2) => unify(a,a2) case _ => ununifiable(e1,e2)}
    case Dual(a)                     => e2 match {case Dual(a2) => unify(a,a2) case _ => ununifiable(e1,e2)}
  }

  private def unifyODE(e1: DifferentialProgram, e2: DifferentialProgram): List[SubstRepl] = e1 match {
    case AtomicODE(xp, t) => e2 match {case AtomicODE(xp2,t2) => unifyVar(xp,xp2) ++ unify(t,t2) case _ => ununifiable(e1,e2)}
    case c: DifferentialProgramConst => if (e1==e2) id else List(SubstRepl(e1, e2))
    case DifferentialProduct(a, b)   => e2 match {case DifferentialProduct(a2,b2) => unify(a,a2) ++ unify(b,b2) case _ => ununifiable(e1,e2)}
  }

  private def unify(s1: Sequent, s2: Sequent): List[SubstRepl] =
    if (!(s1.pref == s2.pref && s1.ante.length == s2.ante.length && s1.succ.length == s2.succ.length)) ununifiable(s1,s2)
    else {
      //@todo this is really a zip fold
      (
        (0 to s1.ante.length-1).foldLeft(List[SubstRepl]())((subst,i) => subst ++ unify(s1.ante(i), s2.ante(i))) ++
          (0 to s1.succ.length-1).foldLeft(List[SubstRepl]())((subst,i) => subst ++ unify(s1.succ(i), s2.succ(i)))
        ).distinct
    }
}

case class UnificationException(e1: String, e2: String, info: String = "")
  extends CoreException("Un-Unifiable:\n" + e1 + "\n" + e2 + "\n" + info) {}
