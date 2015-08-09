/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Unification algorithm for tactics.
 * @author Andre Platzer
 */
object Unification extends ((Expression,Expression) => Option[USubst]) {
  private val id: List[SubstitutionPair] = Nil

  def apply(e1: Expression, e2: Expression): Option[USubst] = if (e1.kind==e2.kind) e1 match {
    case t1: Term => apply(t1, e2.asInstanceOf[Term])
    case f1: Formula => apply(f1, e2.asInstanceOf[Formula])
    case p1: Program => apply(p1, e2.asInstanceOf[Program])
  } else None

  def apply(t1: Term, t2: Term): Option[USubst] = try { Some(USubst(unify(t1,t2))) } catch { case _: UnificationException => None }

  def apply(f1: Formula, f2: Formula): Option[USubst] = try { Some(USubst(unify(f1,f2))) } catch { case _: UnificationException => None }

  def apply(p1: Program, p2: Program): Option[USubst] = try { Some(USubst(unify(p1,p2))) } catch { case _: UnificationException => None }

  private def ununifiable(e1: Expression, e2: Expression): Nothing = throw new UnificationException(e1.toString, e2.toString)

  /** A simple recursive unification algorithm that actually just recursive single-sided matching without occurs check */
  private def unify(e1: Term, e2: Term): List[SubstitutionPair] = e1 match {
    case x: Variable                      => if (e1==e2) id else ununifiable(e1,e2)
    case DifferentialSymbol(x)            => if (e1==e2) id else ununifiable(e1,e2)
    case n: Number                        => if (e1==e2) id else ununifiable(e1,e2)
    case FuncOf(f:Function, Anything)     => if (e1==e2) id else List(SubstitutionPair(e1, e2))
    case FuncOf(f:Function, Nothing)      => if (e1==e2) id else List(SubstitutionPair(e1, e2))
    case FuncOf(f:Function, t)            => e2 match {
      case FuncOf(g, t2) if f==g => unify(t,t2) /*case DotTerm => List(SubstitutionPair(DotTerm, t1))*/
      // otherwise DotTerm abstraction of all occurrences of the argument
      case _ => List(SubstitutionPair(FuncOf(f,DotTerm), SubstitutionHelper.replaceFree(e2)(t,DotTerm)))
    }
    case Anything | Nothing               => if (e1==e2) id else ununifiable(e1,e2)
    case DotTerm                          => if (e1==e2) id else List(SubstitutionPair(e1, e2))
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

  private def unify(e1: Formula, e2: Formula): List[SubstitutionPair] = e1 match {
    case PredOf(f:Function, Anything)     => if (e1==e2) id else List(SubstitutionPair(e1, e2))
    case PredOf(f:Function, Nothing)      => if (e1==e2) id else List(SubstitutionPair(e1, e2))
    case PredOf(f:Function, t)            => e2 match {
      case PredOf(g, t2) if f == g => unify(t, t2)
      // otherwise DotTerm abstraction of all occurrences of the argument
      case _ => List(SubstitutionPair(PredOf(f,DotTerm), SubstitutionHelper.replaceFree(e2)(t,DotTerm)))
    }
    case PredicationalOf(f:Function, DotFormula) => if (e1==e2) id else List(SubstitutionPair(e1, e2))
    case PredicationalOf(c, fml) => e2 match {
      case PredicationalOf(g, fml2) if c == g => unify(fml, fml2)
      // otherwise DotFormula abstraction of all occurrences of the argument
      case _ => ??? //@todo List(SubstitutionPair(PredicationalOf(c,DotFormula), SubstitutionHelper.replaceFree(e2)(fml,DotFormula)))
    }
    case DotFormula         => if (e1==e2) id else List(SubstitutionPair(e1, e2))
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
    case Forall(vars, g) => e2 match {case Forall(v2,g2) if vars==v2 => unify(g,g2) case _ => ununifiable(e1,e2)}
    case Exists(vars, g) => e2 match {case Exists(v2,g2) if vars==v2 => unify(g,g2) case _ => ununifiable(e1,e2)}

    case Box(a, p)       => e2 match {case Box(a2,p2)     => unify(a,a2) ++ unify(p,p2) case _ => ununifiable(e1,e2)}
    case Diamond(a, p)   => e2 match {case Diamond(a2,p2) => unify(a,a2) ++ unify(p,p2) case _ => ununifiable(e1,e2)}
  }

  private def unify(e1: Program, e2: Program): List[SubstitutionPair] = e1 match {
    case a: ProgramConst             => if (e1==e2) id else List(SubstitutionPair(e1, e2))
    case Assign(x, t)                => e2 match {case Assign(x2,t2) if x==x2 => unify(t,t2) case _ => ununifiable(e1,e2)}
    case DiffAssign(xp, t)           => e2 match {case DiffAssign(xp2,t2) if xp==xp2 => unify(t,t2) case _ => ununifiable(e1,e2)}
    case AssignAny(x)                => e2 match {case AssignAny(x2) if x==x2 => id case _ => ununifiable(e1,e2)}
    case Test(f)                     => e2 match {case Test(f2) => unify(f,f2) case _ => ununifiable(e1,e2)}
    case ODESystem(a, h)             => e2 match {case ODESystem(a2,h2) => unifyODE(a,a2) ++ unify(h,h2) case _ => ununifiable(e1,e2)}
    case Choice(a, b)                => e2 match {case Choice(a2,b2) => unify(a,a2) ++ unify(b,b2) case _ => ununifiable(e1,e2)}
    case Compose(a, b)               => e2 match {case Compose(a2,b2) => unify(a,a2) ++ unify(b,b2) case _ => ununifiable(e1,e2)}
    case Loop(a)                     => e2 match {case Loop(a2) => unify(a,a2) case _ => ununifiable(e1,e2)}
    case Dual(a)                     => e2 match {case Dual(a2) => unify(a,a2) case _ => ununifiable(e1,e2)}
  }

  private def unifyODE(e1: DifferentialProgram, e2: DifferentialProgram): List[SubstitutionPair] = e1 match {
    case AtomicODE(xp, t) => e2 match {case AtomicODE(xp2,t2) if xp==xp2 => unify(t,t2) case _ => ununifiable(e1,e2)}
    case c: DifferentialProgramConst => if (e1==e2) id else List(SubstitutionPair(e1, e2))
    case DifferentialProduct(a, b)   => e2 match {case DifferentialProduct(a2,b2) => unify(a,a2) ++ unify(b,b2) case _ => ununifiable(e1,e2)}
  }

}

case class UnificationException(e1: String, e2: String, info: String = "")
  extends CoreException("Unifiable:\n" + e1 + "\n" + e2 + "\n" + info) {}
