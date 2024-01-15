/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch

/** Basic functions about lists, expressions, and non-Kaisar data structures which "should" be a standard library */
object StandardLibrary {
  // Vectorial type real^n
  def rN(n: Int): Sort = {
    if(n == 0) Unit
    else if (n == 1) Real
    else Tuple(Real, rN(n-1))
  }

  /** Tuple containing terms [[fs]] */
   def termsToTuple(fs: List[Term]): Term = {
    fs match {case Nil => Nothing case _ => fs.reduceRight[Term](Pair)}
  }

  /** List of elements conjoined in (possibly) tuple f */
  def tupleToTerms(f: Term, node: ASTNode = Triv()): List[Term] = {
    f match {
      case Nothing => Nil
      case Pair(l, r) => l :: tupleToTerms(r, node)
      case f => f :: Nil
      case _ => throw ProofCheckException("Expected list argument to label reference, but got: " + f, node = node)
    }
  }

  /** unzip triples */
  def unzip3[T1,T2,T3](seq:List[(T1,T2,T3)]):(List[T1],List[T2],List[T3]) = {
    seq match {
      case Nil => (Nil, Nil, Nil)
      case (x, y, z):: xyzs =>
        val (xs, ys, zs) = unzip3(xyzs)
        (xs.+:(x), ys.+:(y), zs.+:(z))
    }
  }

  /** zip triples */
  def zip3[T1,T2,T3](xs:List[T1],ys:List[T2],zs:List[T3], astNode: ASTNode = Triv()):List[(T1,T2,T3)] = {
    (xs, ys, zs) match {
      case (Nil, Nil, Nil) => Nil
      case (x :: xs, y :: ys, z :: zs) => (x, y, z) :: zip3(xs, ys, zs, astNode)
      case _ => throw new NodeException("Mismatched lengths in zip3"){ override val node: ASTNode = astNode}
    }
  }

  /** @return whether formula can easily be evaluated for truth in a state */
  def isExecutable(fml: Formula): Boolean = fml match {
    case _: Less | _: LessEqual | _: Greater | _: GreaterEqual | _: Equal | _: NotEqual | True | False => true
    case Not(f) => isExecutable(f)
    case Or(l, r) => isExecutable(l) && isExecutable(r)
    case And(l, r) => isExecutable(l) && isExecutable(r)
    case Imply (l, r) => isExecutable(l) && isExecutable(r)
    case Equiv (l, r) => isExecutable(l) && isExecutable(r)
    case _ => false
  }

  /** Elaborate fact binding patterns as in assertions ?pat:(fml); Vectorial patterns ?(x, y):(p & q) become lists of bindings. */
  def factBindings(lhs: Expression, rhs: Formula, node: ASTNode = Triv()): List[(Option[Ident], Formula)] = {
    def loop(lhs: Expression, rhs: Formula): List[(Option[Ident], Formula)] = {
      (lhs, rhs) match {
        case (Nothing, _) => (None, rhs) :: Nil
        case (v: Variable, _) => (Some(v), rhs) :: Nil
        case (Pair(v: Variable, Nothing), _) => (Some(v), rhs) :: Nil
        case (Pair(l, r), And(pl, pr)) => loop(l, pl) ++ loop(r, pr)
        // Note: Vectorial assumption must look like a conjunction in the *source syntax,* not just after expanding definitions
        case _ => throw ElaborationException(s"Vectorial fact $lhs:$rhs expected right-hand-side to have shape p1 & ... & ... pn with one conjunct per fact name, but it did not.", node)
      }
    }
    lhs match {
      case v: Variable => List((Some(v), rhs))
      case _ => loop(lhs, rhs)
    }
  }

  /** @return equivalent formula of f, with shape [a]P */
  def asBox(f: Formula): Box = {
    f match {
      case b: Box => b
      case _ => Box(Dual(Test(f)), True)
    }
  }

  /** @return equivalent formula of f, with shape <a>P */
  def asDiamond(f: Formula): Diamond = {
    f match {
      case b: Diamond => b
      case _ => Diamond(Test(f), True)
    }
  }

  /** @return unification result of p and q, if any */
  def unifyFml(p: Formula, q: Formula): Option[Formula] = {
    try {
      val subst = UnificationMatch(p, q)
      val r = subst(p)
      Some(r)
    } catch {
      case _: ProverException => None
    }
  }

  /** @return unification result of formulas, if any. */
  def unifyFmls(ps: Seq[Formula]): Option[Formula] = {
    ps match {
      case Nil => None
      case p :: Nil => Some(p)
      case p :: ps => unifyFmls(ps) match {
        case None => None
        case Some(q) => unifyFml(p, q)
      }
    }
  }

  /** @return Box formula which runs programs of [[p]] first, then programs of [[b]]*/
  def concatBox(p: Formula, q: Formula): Formula = {
    (p, q) match {
      case (True, _) => q
      case (_, True) => p
      case (Box(a, True), Box(b, q1)) => Box(Compose(a, b), q1)
      case (Box(a, True), q) => Box(Compose(a, Dual(Test(q))), True)
      case (Box(a, p1), Box(b, q1)) => Box(Compose(a, Compose(Dual(Test(p1)), b)), q1)
      case (p, Box(b, q1)) => Box(Compose(Dual(Test(p)), b), q1)
      case (Box(a, p1), q) => Box(Compose(a,Compose(Dual(Test(p1)), Dual(Test(q)))), True)
    }
  }

  /** @param k must be >= 1
    * Return list of k branches if g is a nested choice down its right spine, else None */
  def unchoose(g: Program, k: Int): Option[List[Program]] = {
    (g, k) match {
      case (g, 1) => Some(List(g))
      case (Choice(l, r), k) => unchoose(r, k-1).map(xs => l :: xs)
    }
  }
}
