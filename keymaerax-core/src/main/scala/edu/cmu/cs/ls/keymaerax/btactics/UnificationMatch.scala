/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import scala.collection.immutable._
import scala.collection.immutable

import edu.cmu.cs.ls.keymaerax.core._


/**
  * Unification/matching algorithm for tactics.
  * Unify(shape, input) matches second argument `input` against the pattern `shape` of the first argument but not vice versa.
  * Matcher leaves input alone and only substitutes into shape.
  * @author Andre Platzer
  */
object UnificationMatch extends ((Expression,Expression) => RenUSubst) {
  import edu.cmu.cs.ls.keymaerax.tactics.SubstitutionHelper.replaceFree

  //@todo import a debug flag as in Tactics.DEBUG
  private val DEBUG = System.getProperty("DEBUG", "true")=="true"
  private val REUNIFY = false

//  type Subst = USubst
//  private def Subst(subs: List[SubstRepl]): Subst = USubst(subs)
//  type SubstRepl = SubstitutionPair
//  private def SubstRepl(what: Expression, repl: Expression): SubstRepl = SubstitutionPair(what,repl)
  type Subst = RenUSubst
  private def Subst(subs: List[SubstRepl]): Subst = if (!REUNIFY) RenUSubst(subs) else RenUSubst(subs.distinct)
  type SubstRepl = scala.Predef.Pair[Expression,Expression]
  private def SubstRepl(what: Expression, repl: Expression): SubstRepl = (what,repl)

  //

  private val id: List[SubstRepl] = Nil

  /** apply(shape, input) matches `input` against the pattern `shape` to find a uniform substitution `\result` such that `\result(shape)==input`. */
  def apply(e1: Expression, e2: Expression): Subst = if (e1.kind==e2.kind || e1.kind==ProgramKind && e2.kind==DifferentialProgramKind)
    e1 match {
    case t1: Term => apply(t1, e2.asInstanceOf[Term])
    case f1: Formula => apply(f1, e2.asInstanceOf[Formula])
    case p1: DifferentialProgram if !p1.isInstanceOf[ODESystem] => apply(p1, e2.asInstanceOf[DifferentialProgram])
    case p1: Program => apply(p1, e2.asInstanceOf[Program])
  } else throw new UnificationException(e1.prettyString, e2.prettyString, "have different kinds " + e1.kind + " and " + e2.kind)

  /** Compute some unifier if unifiable else None */
  def unifiable(e1: Expression, e2: Expression): Option[Subst] = try {Some(apply(e1, e2))} catch {case e: UnificationException => println("Expression un-unifiable " + e); None}

  /** Compute some unifier if unifiable else None */
  def unifiable(e1: Sequent, e2: Sequent): Option[Subst] = try {Some(apply(e1, e2))} catch {case e: UnificationException => println("Sequent un-unifiable " + e); None}

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
    if (!REUNIFY) Subst(unify(e1, e2)) else {
      val ren = RenUSubst.renamingPart(unify(e1,e2))
      Subst(reunify(unify(ren(e1),e2) ++ ren.subsDefsInput))
    }
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal\n" + Subst(unify(e1, e2)))

  def apply(e1: Formula, e2: Formula): Subst = {try {
    if (!REUNIFY) Subst(unify(e1, e2)) else {
      val ren = RenUSubst.renamingPart(unify(e1, e2))
      Subst(reunify(unify(ren(e1), e2) ++ ren.subsDefsInput))
    }
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal\n" + Subst(unify(e1, e2)))

  def apply(e1: Program, e2: Program): Subst = {try {
    if (!REUNIFY) Subst(unify(e1, e2)) else {
      val ren = RenUSubst.renamingPart(unify(e1, e2))
      Subst(reunify(unify(ren(e1), e2) ++ ren.subsDefsInput))
    }
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal\n" + Subst(unify(e1, e2)))

  def apply(e1: DifferentialProgram, e2: DifferentialProgram): Subst = {try {
    if (!REUNIFY) {if (e1.isInstanceOf[ODESystem] || e2.isInstanceOf[ODESystem]) Subst(unify(e1,e2)) else Subst(unifyODE(e1, e2))} else {
      val ren = RenUSubst.renamingPart(unifyODE(e1, e2))
      Subst(reunify(unify(ren(e1), e2) ++ ren.subsDefsInput))
    }
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.prettyString + "\n   with  " + e2.prettyString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal\n" + Subst(unifyODE(e1, e2)))

  def apply(e1: Sequent, e2: Sequent): Subst = {try {
    if (!REUNIFY) Subst(unify(e1, e2)) else {
      val ren = RenUSubst.renamingPart(unify(e1, e2))
      //println("Unifying " + e1 + " and " + e2 + "\nwith renaming " + ren + " gives " + ren(e1) + " led to\n" + unify(ren(e1),e2) + " and ")
      Subst(reunify(unify(ren(e1), e2) ++ ren.subsDefsInput))
    }
  } catch {case ex: ProverException => throw ex.inContext("match " + e1.toString     + "\n   with  " + e2.toString)}
  } ensuring (r => r(e1) == e2, "unifier match makes " + e1 + " and " + e2 + " equal\n" + Subst(unify(e1, e2)))

  /** Re-unify multiple replacements for the same what */
  private def reunify(subst: List[SubstRepl]): List[SubstRepl] = {
    // map matchKey to all substitution pairs in subst that sahre that matchKey
    var matchKeyMap = new scala.collection.mutable.HashMap[Expression,immutable.List[SubstRepl]]()
    for (sp <- subst.distinct) {
      val key = RenUSubst.matchKey(sp)
      matchKeyMap.get(key) match {
        case None => matchKeyMap.put(key, List(sp))
        case Some(list) => matchKeyMap.put(key, list :+ sp)
      }
    }
    var harmless: List[SubstRepl] =
      matchKeyMap.filter(kv => kv._2.size<=1).values.map(list=>{assert(list.length==1); list.head}).toList
    var dups: scala.collection.mutable.HashMap[Expression,immutable.List[SubstRepl]] =
      matchKeyMap.filter(kv => kv._2.size>=2)
    while (!dups.isEmpty) {
      val dupkv: (Expression,immutable.List[SubstRepl]) = dups.head
      dups = dups.tail
      if (DEBUG) print("unify duplicate " + dupkv._2.map(sp=>sp._1.prettyString + "~>" + sp._2.prettyString).mkString(", ") + "  ")
      val dup = dupkv._2
      if (dup.map(sp=>sp._1).distinct.length==1) {
        // all have same left-hand side
        assert(dup.length>=2, "duplicates come in sizes of at least 2")
        val remaining = if (unifiable(dup.head._2, dup.tail.head._2).isDefined)
          // dup.head is more general, so just drop the other and hope for unification
          dup.patch(1,Nil,1)
        else if (unifiable(dup.tail.head._2, dup.head._2).isDefined)
        // dup.tail.head is more general, so just drop the other and hope for unification
          dup.patch(0,Nil,1)
        else
          throw new ProverException("Duplicates do not reunify " + dup)
        if (DEBUG) println("unified duplicate to " + remaining)
        assert (remaining.length < dup.length, "reunify made progress by shrinking one list")
        if (remaining.length>=2) matchKeyMap.put(dupkv._1, remaining)
        else {
          // move to harmless
          assert(remaining.length==1)
          harmless = harmless :+ remaining.head
          //matchKeyMap.remove(dupkv._1)
        }
      } else {
        throw new ProverException("Don't currently reunify different left-hand sides " + dup)
      }
    }
    assert(dups.isEmpty, "handled all duplicates")
    harmless
  }

  private def ununifiable(e1: Expression, e2: Expression): Nothing = {
    //println(new UnificationException(e1.toString, e2.toString))
    throw new UnificationException(e1.toString, e2.toString)}

  private def ununifiable(e1: Sequent, e2: Sequent): Nothing = {
    //println(new UnificationException(e1.toString, e2.toString))
    throw new UnificationException(e1.toString, e2.toString)}

//  private def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] = if (x1==e2) id else ununifiable(x1,e2)
//  private def unifyVar(xp1: DifferentialSymbol, e2: Expression): List[SubstRepl] = if (xp1==e2) id else ununifiable(xp1,e2)
  private def unifyVar(x1: Variable, e2: Expression): List[SubstRepl] = if (x1==e2) id else if (e2.isInstanceOf[Variable]) List(SubstRepl(x1,e2.asInstanceOf[Variable])) else ununifiable(x1,e2)
  private def unifyVar(xp1: DifferentialSymbol, e2: Expression): List[SubstRepl] = if (xp1==e2) id else if (e2.isInstanceOf[DifferentialSymbol]) List(SubstRepl(xp1.x,e2.asInstanceOf[DifferentialSymbol].x)) else ununifiable(xp1,e2)

  //@todo optimize: this may be slower than static type inference
  private def unify(e1: Expression, e2: Expression): List[SubstRepl] = e1 match {
    case t1: Term => unify(t1, e2.asInstanceOf[Term])
    case f1: Formula => unify(f1, e2.asInstanceOf[Formula])
    case p1: DifferentialProgram if !p1.isInstanceOf[ODESystem] => unifyODE(p1, e2.asInstanceOf[DifferentialProgram])
    case p1: Program => unify(p1, e2.asInstanceOf[Program])
  }

  private def compose(after: List[SubstRepl], before: List[SubstRepl]): List[SubstRepl] = {
    val us = Subst(after)
    try {
      before.map(sp => (sp._1, us(sp._2))) ++ after.filter(sp => !before.exists(op => op._1 == sp._1))
    } catch {case e:Throwable => println("UnificationMatch.compose({" + after.mkString(", ") + "} , {" + before.mkString(", ") + "})"); throw e}
  }

  // unify(s1, t1) ++ unify(s2, t2)  // flat approximation without cross-cut
  //@note optimized: repeated implementation per type to enable the static type inference that Scala generics won't give.
  private def unify(s1:Expression,s2:Expression, t1:Expression,t2:Expression): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    compose(unify(Subst(u1)(s2), t2), u1)
  }
  private def unify(s1:Term,s2:Term, t1:Term,t2:Term): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    compose(unify(Subst(u1)(s2), t2), u1)
  }
  private def unify(s1:Formula,s2:Formula, t1:Formula,t2:Formula): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    compose(unify(Subst(u1)(s2), t2), u1)
  }
  private def unify(s1:Program,s2:Program, t1:Program,t2:Program): List[SubstRepl] = {
    val u1 = unify(s1, t1)
    compose(unify(Subst(u1)(s2), t2), u1)
  }


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
      case _ => List(SubstRepl(FuncOf(f,DotTerm), replaceFree(e2)(t,DotTerm)))
    }
    case Anything                         => if (e1==e2) id else List(SubstRepl(Anything, e2))  //@todo where does this happen?
    case Nothing                          => if (e1==e2) id else ununifiable(e1,e2)
    case DotTerm                          => if (e1==e2) id else List(SubstRepl(e1, e2))
    //@note case o1:UnaryCompositeTerm  => e2 match {case o2:UnaryCompositeTerm  if o1.reapply==o2.reapply => unify(o1.child,o2.child) case _ => ununifiable(e1,e2)}
    //@note case o1:BinaryCompositeTerm => e2 match {case o2:BinaryCompositeTerm if o1.reapply==o2.reapply => unify(o1.left,o2.left) ++ unify(o1.right,o2.right) case _ => ununifiable(e1,e2)}
    // homomorphic cases
    case Neg(t)       => e2 match {case Neg(t2) => unify(t,t2) case _ => ununifiable(e1,e2)}
      // case o: BinaryCompositeTerm => e2 match {case o2: BinaryCompositeTerm if o2.reapply==o.reapply => unify(o.left,o.right, o2.left,o2.right) case _ => ununifiable(e1,e2)}
    case Plus(l, r)   => e2 match {case Plus  (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Minus(l, r)  => e2 match {case Minus (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Times(l, r)  => e2 match {case Times (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Divide(l, r) => e2 match {case Divide(l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Power(l, r)  => e2 match {case Power (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Differential(t) => e2 match {case Differential(t2) => unify(t,t2) case _ => ununifiable(e1,e2)}
    // unofficial
    case Pair(l, r)   => e2 match {case Pair(l2,r2)   => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
  }

  private def unify(e1: Formula, e2: Formula): List[SubstRepl] = e1 match {
    case PredOf(f:Function, Anything)     => if (e1==e2) id else List(SubstRepl(e1, e2))
    case PredOf(f:Function, Nothing)      => if (e1==e2) id else List(SubstRepl(e1, e2))
    case PredOf(f:Function, t)            => e2 match {
      case PredOf(g, t2) if f == g => unify(t, t2)
      // otherwise DotTerm abstraction of all occurrences of the argument
        //@todo stutter  if not free
      case _ => if (DEBUG) println("unify " + e1 + "\nwith  " + e2 + "\ngives " + SubstRepl(PredOf(f,DotTerm), replaceFree(e2)(t,DotTerm)))
        List(SubstRepl(PredOf(f,DotTerm), replaceFree(e2)(t,DotTerm)))
        //@todo heuristic: for p(f()) simply pass since f() must occur somewhere else in isolation to match on it. In general may have to remember p(subst(f())) = e2 constraint regardless and post-unify.
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
    case Equal(l, r)        => e2 match {case Equal       (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case NotEqual(l, r)     => e2 match {case NotEqual    (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case GreaterEqual(l, r) => e2 match {case GreaterEqual(l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Greater(l, r)      => e2 match {case Greater     (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case LessEqual(l, r)    => e2 match {case LessEqual   (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Less(l, r)         => e2 match {case Less        (l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}

    // homomorphic cases
    case Not(g)      => e2 match {case Not(g2)      => unify(g,g2) case _ => ununifiable(e1,e2)}
    case And(l, r)   => e2 match {case And(l2,r2)   => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Or(l, r)    => e2 match {case Or(l2,r2)    => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Imply(l, r) => e2 match {case Imply(l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}
    case Equiv(l, r) => e2 match {case Equiv(l2,r2) => unify(l,r, l2,r2) case _ => ununifiable(e1,e2)}

    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(g) => e2 match {case DifferentialFormula(g2) => unify(g,g2) case _ => ununifiable(e1,e2)}

    // pseudo-homomorphic cases
      //@todo join should be enough for the two unifiers in this case after they have been applied to the other side
    case Forall(vars, g) if vars.length==1 => e2 match {case Forall(v2,g2) if v2.length==1 => unify(vars.head,g, v2.head,g2) case _ => ununifiable(e1,e2)}
    case Exists(vars, g) if vars.length==1 => e2 match {case Exists(v2,g2) if v2.length==1 => unify(vars.head,g, v2.head,g2) case _ => ununifiable(e1,e2)}

    // homomorphic cases
    case Box(a, p)       => e2 match {case Box(a2,p2)     => unify(a,p, a2,p2) case _ => ununifiable(e1,e2)}
    case Diamond(a, p)   => e2 match {case Diamond(a2,p2) => unify(a,p, a2,p2) case _ => ununifiable(e1,e2)}
  }

  private def unify(e1: Program, e2: Program): List[SubstRepl] = e1 match {
    case a: ProgramConst             => if (e1==e2) id else List(SubstRepl(e1, e2))
    case Assign(x, t)                => e2 match {case Assign(x2,t2) => unify(x,t, x2,t2) case _ => ununifiable(e1,e2)}
    case DiffAssign(xp, t)           => e2 match {case DiffAssign(xp2,t2) => unify(xp,t, xp2,t2) case _ => ununifiable(e1,e2)}
    case AssignAny(x)                => e2 match {case AssignAny(x2)    => unify(x,x2) case _ => ununifiable(e1,e2)}
    case Test(f)                     => e2 match {case Test(f2)         => unify(f,f2) case _ => ununifiable(e1,e2)}
    case ODESystem(a, h)             => e2 match {case ODESystem(a2,h2) => unify(a,h, a2,h2) case _ => ununifiable(e1,e2)}
    case Choice(a, b)                => e2 match {case Choice(a2,b2)    => unify(a,b, a2,b2) case _ => ununifiable(e1,e2)}
    case Compose(a, b)               => e2 match {case Compose(a2,b2)   => unify(a,b, a2,b2) case _ => ununifiable(e1,e2)}
    case Loop(a)                     => e2 match {case Loop(a2)         => unify(a,a2) case _ => ununifiable(e1,e2)}
    case Dual(a)                     => e2 match {case Dual(a2)         => unify(a,a2) case _ => ununifiable(e1,e2)}
  }

  private def unifyODE(e1: DifferentialProgram, e2: DifferentialProgram): List[SubstRepl] = e1 match {
    case AtomicODE(xp, t) => e2 match {case AtomicODE(xp2,t2) => unify(xp,t, xp2,t2) case _ => ununifiable(e1,e2)}
    case c: DifferentialProgramConst => if (e1==e2) id else List(SubstRepl(e1, e2))
    case DifferentialProduct(a, b)   => e2 match {case DifferentialProduct(a2,b2) => unify(a,b, a2,b2) case _ => ununifiable(e1,e2)}
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
  extends CoreException("Un-Unifiable: " + e1 + "\nfor:          " + e2 + "\n" + info) {}
