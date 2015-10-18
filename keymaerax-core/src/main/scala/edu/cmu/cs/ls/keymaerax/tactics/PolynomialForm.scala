package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.{SortedSet, TreeSet, Set}

/** Alternate representation of terms as polynomials. This representation is useful for some tactics because it makes
  * analyses such as term complexity easier to compute.
  * Created by bbohrer on 10/14/15.
  */
object PolynomialForm {

  // Expand constant powers to iterated products.
  private def expandPower(t: Term, n: BigInt): Term = {
    (n == BigInt(0), n == BigInt(1)) match {
      case (true, false) => Number(1)
      case (false, true) => t
      case _ => Times(t, expandPower(t, n - 1))
    }
  }

  private def syntacticDerivative(t: Term): Term =
    t match {
      case Differential(t1) => syntacticDerivative(syntacticDerivative(t1))
      case Plus(t1, t2) => Plus(syntacticDerivative(t1), syntacticDerivative(t2))
      case Minus(t1, t2) => Minus(syntacticDerivative(t1), syntacticDerivative(t2))
      case Times(t1, t2) => Plus(Times(t1, syntacticDerivative(t2)), Times(t2, syntacticDerivative(t1)))
      case Divide(t1, t2) => Divide(Minus(Times(syntacticDerivative(t1), t2), Times(t1, syntacticDerivative(t2))), Times(t2, t2))
      case x@Variable(_, _, _) => DifferentialSymbol(x)
      case Neg(t1) => Neg(syntacticDerivative(t1))
      case Number(_) => Number(0)
      case DifferentialSymbol(_) => ??? // @todo Decide whether it's better to introduce auxilliary variables or just fail
    }

  // Remove all variables from vs1 that appear in vs2 (possibly with different exponents)
  private def removeVarsOf(vs1: Set[(Term, Int)], vs2: Set[(Term, Int)]): Set[(Term, Int)] =
    vs1.filter(xn => !vs2.exists(ym => xn._1 == ym._1))

  // Compute the variables that appear in both vs1 and vs2 with their associated exponents.
  private def commonVars(vs1: Set[(Term, Int)], vs2: Set[(Term, Int)]): Set[(Term, Int, Int)] =
    vs1.flatMap((xn: (Term, Int)) => {
      val (found: Option[(Term, Int)]) = vs2.find(ym => xn._1 == ym._1)
      found match {
        case None => Set.empty[(Term, Int, Int)]
        case Some(ym: (Term, Int)) => Set.empty.+((xn._1, ym._2, xn._2))
      }
    })

  // Exceptions for reporting terms that can't be turned into polynomials.
  class BadDivision extends Exception {}
  class BadPower extends Exception {}

  sealed trait NormResult {}
  case class NormalForm (p: Polynomial) extends NormResult
  case class BadPowerResult () extends NormResult
  case class BadDivResult () extends NormResult

  object Monomial {
    val zero : Monomial = Monomial(Number(0), Set.empty)
  }

  case class Monomial (coeff: Number, vars: Set[(Term, Int)]) {
    def asPair : (Number, Set[(Term, Int)]) = (coeff, vars)

    // Computes the product of two monomials
    def times(other: Monomial): Monomial = {
      val common = commonVars(vars, other.vars).map(cvs => (cvs._1, cvs._2 + cvs._3))
      Monomial(Number(coeff.value * other.coeff.value),
        removeVarsOf(vars, common) ++ removeVarsOf(other.vars, common) ++ common)
    }

    def totalDegree: Int = vars.foldLeft(0)({case (n1,(v,n2)) => n1+n2})
  }

  object Polynomial {
    val zero : Polynomial = Polynomial(Set.empty)

    def create(t: Term): NormResult = {
      try {
        NormalForm(new Polynomial(t))
      } catch {
        case ex: BadDivision => BadDivResult()
        case ex: BadPower => BadPowerResult()
      }
    }

    // Create a polynomial of form x (or x')/
    private def ofVariable(x: Term): Polynomial =
      Polynomial(Set.empty.+(Monomial(Number(1), Set.empty.+((x, 1)))))

    // Main loop for normalizing terms to polynomials. Throws an exception if the term has no normal form.
    // Breaks the invariant that all coefficients are non-zero
    private def normLoop(t: Term): Polynomial = {
      t match {
        case Times(t1: Term, t2: Term) =>
          val normT2 = normLoop(t2)
          normLoop(t1).asSet.foldLeft(zero){case (acc,mon1) =>
            normT2.asSet.foldLeft(acc)({case (acc,mon2) =>
              acc.plus(new Polynomial(Set(mon1.times(mon2))))})}
        case Plus(t1: Term, t2: Term) => normLoop(t1).plus(normLoop(t2))
        case Minus(t1: Term, t2: Term) =>
          val (norm1, norm2) = (normLoop(t1), normLoop(t2))
          val commonMonomials = norm1.mapCommon(norm2,{case (x,y) => Number(x.value-y.value)})
          Polynomial(commonMonomials.asSet ++ norm1.removeMonomialsOf(commonMonomials).asSet ++ norm2.removeMonomialsOf(commonMonomials).asSet)
        case Neg(t1:Term) => normLoop(Minus(Number(0),t1))
        case Differential(t1) => normLoop(syntacticDerivative(t1))
        case Divide(t1, Number(x)) =>
          if (x == Number(0)) {
            throw new BadDivision
          }
          else
            normLoop(Times(t1, Number(1 / x)))
        case Divide(_,_) => throw new BadDivision
        case x@Number(_) => new Polynomial(x)
        case x@Variable(_, _, _) => ofVariable(x)
        case x@DifferentialSymbol(_) => ofVariable(x)
        case Power(t1, Number(x)) =>
          x.toBigIntExact() match {
            case None => throw new BadPower
            case Some(n) =>
              if (n < BigInt(0)) {
                throw new BadPower
              }
              normLoop(expandPower(t1, n))
          }
        case Power(_,_) => throw new BadPower
      }
    }
  }

  private object VariableComparator extends Ordering[(Term,Int)] {
    def compare(t1: (Term,Int), t2: (Term,Int)): Int = compareVars (t1._1, t2._1)
  }

  private def sortVars(s: Set[(Term, Int)]): SortedSet[(Term, Int)] = {
    val ss : SortedSet[(Term,Int)] = TreeSet[(Term,Int)]()(VariableComparator)
    s.foldLeft(ss)({case (ss, xn) => ss.+(xn)})
  }

  // Compares two variables in a polynomial, ordered by complexity. We consider differential symbols more complex
  // than program variables because it seems likely that eliminating them will usually make proofs simpler.
  private def compareVars(x1:Term,x2:Term):Int = {
    (x1,x2) match {
      case (v1@Variable(_,_,_),v2@Variable(_,_,_)) => v1.compare(v2)
      case (v1@DifferentialSymbol(_), v2@DifferentialSymbol(_)) =>
        v1.compare(v2)
      case (DifferentialSymbol(_),Variable(_,_,_)) => 1
      case (Variable(_,_,_), DifferentialSymbol(_)) => -1
    }
  }

  // Compares the variables of two monomials (assumes the input lists are sorted on the variables)
  private def compareSortedVars(l1:List[(Term,Int)],l2:List[(Term,Int)]):Int = {
    (l1, l2) match {
      case (Nil, Nil) => 0
      case ((x: (Term, Int)) :: _, Nil) => x._2.compare(0)
      case (Nil, (x: (Term, Int)) :: _) => 0.compare(x._2)
      case ((x: (Term, Int)) :: xs, (y: (Term, Int)) :: ys) =>
        val varCmp = compareVars(x._1, y._1)
        if (varCmp < 0) {
          x._2.compare(0)
        } else if (varCmp > 0) {
          0.compare(y._2)
        } else {
          val expCmp = x._2.compare(y._2)
          if (expCmp != 0) {
            expCmp
          } else {
            compareSortedVars(xs, ys)
          }
        }
    }
  }

  private def compareMonomialVars(s1:Set[(Term,Int)],s2:Set[(Term,Int)]):Int = {
    compareSortedVars(sortVars(s1).toList,sortVars(s2).toList)
  }

  // Graded lexicographic monomial ordering, commonly used when finding Groebner bases.
  object MonomialGrlex extends Ordering[Monomial] {
    def compare(mon1: Monomial, mon2: Monomial): Int = {
      val cmpDegree = mon1.totalDegree.compare(mon2.totalDegree)
      if (cmpDegree != 0) cmpDegree
      else {
        val cmpVars = compareMonomialVars(mon1.vars, mon2.vars)
        if (cmpVars != 0) {
          cmpVars
        } else {
          mon1.coeff.value.compare(mon2.coeff.value)
        }
      }
    }
  }

  case class Polynomial (mons: Set[Monomial]) {
    def asSet : Set[Monomial] = mons

    // Find the common elements of norm1 and norm2, combining corresponding elements with f
    private def mapCommon (other: Polynomial, f: (Number, Number) => Number): Polynomial = {
      val mons =
        asSet.flatMap(mon1 =>
          other.asSet.find(mon2 => mon1.vars == mon2.vars) match {
            case None => Set.empty[Monomial]
            case Some(mon2) => Set(Monomial(f(mon1.coeff,mon2.coeff), mon1.vars))
          })
      Polynomial(mons)
    }

    private def plus(other:Polynomial):Polynomial = {
      val commonMonomials = mapCommon(other, { case (x, y) => Number (x.value + y.value) })
      Polynomial(commonMonomials.mons ++ removeMonomialsOf(commonMonomials).mons ++ other.removeMonomialsOf(commonMonomials).mons)
    }

    // Remove all monomials from p1 that appear in p2 (possibly with different coefficients)
    private def removeMonomialsOf(other: Polynomial): Polynomial =
      Polynomial (mons.filter(p1 => !other.mons.exists(p2 => p1.vars == p2.vars)))

    // Raises an exception if t cannot be represented as a polynomial
    def this (t: Term) =
      // Since normLoop breaks the invariant that coefficients are nonzero, we restore it here.
      this(Polynomial.normLoop(t).mons.filter({case mon => Number(0) != mon.coeff}))

    // Create a polynomial of form c for some real c.
    def this (x: Number) = this(Set(Monomial(x, Set.empty[(Term, Int)])))
    def this (mon: Monomial) = this(Set(mon))

    // Compares two polynomials assuming their monomials are in sorted order
    private def compareSortedPolyTermsLoop(l1:List[Monomial],l2:List[Monomial]):Int = {
      (l1,l2) match {
        case (Nil,Nil) => 0
        case ((x:Monomial) :: _, Nil) => MonomialGrlex.compare(x, Monomial.zero)
        case (Nil, (x:Monomial) ::_) => MonomialGrlex.compare(Monomial.zero, x)
        case ((x:Monomial)::xs,(y:Monomial)::ys) =>
          val varCmp = compareMonomialVars(x.vars, y.vars)
          if (varCmp < 0) {
            MonomialGrlex.compare(x,Monomial.zero)
          } else if (varCmp > 0) {
            MonomialGrlex.compare(Monomial.zero, y)
          } else {
            x.coeff.value.compare(y.coeff.value)
          }
      }
    }

    // Compares two polynomials assuming their monomials are in sorted order
    private def compareSortedPolyTerms(l1:List[Monomial],l2:List[Monomial]):Int = {
      val cmp = (l1,l2) match {
        case ((x: Monomial) :: xs, (y: Monomial) :: ys) =>
          val degreeCmp = x.totalDegree.compare(y.totalDegree)
          if (degreeCmp != 0) degreeCmp
          else l1.length.compare(l2.length)
        case _ => 0
      }

      if (cmp == 0) compareSortedPolyTermsLoop(l1, l2)
      else cmp
    }

    def compareComplexity(other: Polynomial): Int = {
      def moreComplex (mon1: Monomial, mon2: Monomial): Boolean = MonomialGrlex.compare(mon1, mon2) > 0
      val ls = mons.toList.sortWith(moreComplex)
      val rs = other.mons.toList.sortWith(moreComplex)
      compareSortedPolyTerms(ls,rs)
    }
  }

  /** To compare the complexity of terms we first normalize them to polynomials (where we include differential symbols in the
    * set of possible variables). Since quotients and exponentials cannot be normalized to polynomials, we consider quotients
    * more complex than polynomials and exponentials most complex of all.
    *
    * This comparison is based on the graded lexicographic ordering often used when computing Groebner bases with Buchberger's algorithm,
    * though it may vary in some of the details.
    *
    * The type Monomial encodes a monomial as a coefficient and a set of variables raised to positive exponents. Constant terms are encoded
    * as coefficients with no variables. A Polynomial represents a polynomial over Numbers where the variables are program variables and
    * their differential symbols.
    */
  def compareTermComplexity(l:Term, r:Term) : Int = {
    (Polynomial.create(l), Polynomial.create(r)) match {
      case (NormalForm(norm1), NormalForm(norm2)) => norm1.compareComplexity(norm2)
      case (BadPowerResult(), BadPowerResult()) => 0
      case (BadPowerResult(), _) => 1
      case (_, BadPowerResult()) => -1
      case (BadDivResult(), BadDivResult()) => 0
      case (BadDivResult(), _) => 1
      case (_, BadDivResult()) => -1
    }
  }
}
