package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

/** Basic functions about lists, expressions, and non-Kaisar data structures which "should" be a standard library */
object StandardLibrary {
  // Vectorial type real^n
  def rN(n: Int): Sort = {
    if(n == 0) Unit
    else Tuple(Real, rN(n-1))
  }

  /** Tuple containing terms [[fs]] */
   def termsToTuple(fs: List[Term]): Term = {
    fs.foldRight[Term](Nothing)(Pair)
  }

  /** List of elements conjoined in (possibly) tuple f */
  def tupleToTerms(f: Term): List[Term] = {
    f match {
      case Nothing => Nil
      case Pair(l, r) => l :: tupleToTerms(r)
      case _ => throw ProofCheckException("Expected list argument to label reference, but got: " + f)
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
  def zip3[T1,T2,T3](xs:List[T1],ys:List[T2],zs:List[T3]):List[(T1,T2,T3)] = {
    (xs, ys, zs) match {
      case (Nil, Nil, Nil) => Nil
      case (x :: xs, y :: ys, z :: zs) => (x, y, z) :: zip3(xs, ys, zs)
      case _ => throw new Exception("Mismatched lengths in zip3")
    }
  }

}
