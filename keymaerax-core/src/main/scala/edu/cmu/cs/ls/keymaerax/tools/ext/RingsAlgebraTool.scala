package edu.cmu.cs.ls.keymaerax.tools.ext

import cc.redberry.rings.bigint.BigInteger
import cc.redberry.rings.scaladsl._
import cc.redberry.rings.scaladsl.syntax._
import edu.cmu.cs.ls.keymaerax.btactics.{AnonymousLemmas, Idioms, PolynomialArith, SequentCalculus}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.{Tool, ToolExecutionException}
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DependentPositionTactic}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.JavaConverters._

/**
  * A link to Rings library for its algebra tools
  */

class RingsLibrary(terms: Traversable[Term]) {

  private def varprefix = "AVAR"
  private def funcprefix = "BFUNC"

  val names = {
    //@note sort for stable results
    val syms = terms.toList.flatMap(p => StaticSemantics.symbols(p)).distinct.sorted
    // Only constant symbols f() and vars are kept. Everything else is discarded
    val (vars,rest) = syms.partition( p => p.isInstanceOf[BaseVariable])
    val (funcs,emp) = rest.partition( p => p.isInstanceOf[Function] && p.asInstanceOf[Function].domain == Unit )

    if(emp.nonEmpty)
      throw ToolExecutionException("RingsLibrary does not handle non-constant function symbols: " +emp)
    vars ++ funcs
  }

  val ringsNames =
    names.zipWithIndex.map(p =>
      p._1 match {
        case v: Variable => (p._1, varprefix + p._2)
        case _ => (p._1, funcprefix + p._2)
      }
    )
  val mapper = ringsNames.toMap
  val unmapper =
    names.zipWithIndex.map(p => (p._2,
      p._1 match {
        case v: Variable => v
        case f: Function => FuncOf(f, Nothing)
        case _ => ??? //never happens
      }
    )).toMap

  implicit val ring = MultivariateRing(Q,ringsNames.map(_._2).toArray)
  type Ring = MultivariatePolynomial[Rational[BigInteger]]
  def toRing(term:Term) : Ring = {
    term match {
      case Neg(l) =>
        ring.negate(toRing(l))
      case Plus(l,r) =>
        ring.add(toRing(l),toRing(r))
      case Minus(l,r) =>
        ring.subtract(toRing(l),toRing(r))
      case Times(l,r) =>
        ring.multiply(toRing(l),toRing(r))
      case Divide(l,r) =>
        val arr = ring.divideAndRemainder(toRing(l),toRing(r))
        if(!arr(1).isZero)
          throw ToolExecutionException("Unable to divide "+l+" by "+r+" to obtain a polynomial")
        arr(0)
      // Only ints
      case n:Number => {
        val num = n.value.bigDecimal.unscaledValue()
        val denom = BigDecimal(1).bigDecimal.movePointRight(n.value.scale).toBigInteger
        ring.divideExact(ring(num),ring(denom))
      }
      // Every named symbol must be mapped
      case v:NamedSymbol => ring(mapper(v))
      // Some special cases for powers
      case Power(l,Number(n)) if n.isValidInt && n >= 0 =>
        ring.pow(toRing(l), n.toIntExact)
      case Power(l,r) => {
        PolynomialArith.groundNormaliseProof(r,true) match {
          case Some((n:Number,pr)) if n.value.isValidInt && n.value >= 0 => {
            ring.pow(toRing(l) , n.value.toIntExact)
          }
          case _ => throw ToolExecutionException("Unable to reduce exponent "+r+" to a natural number")
        }
      }
      case f:FuncOf if f.child == Nothing =>
        ring(mapper(f.func))
      case _ => throw ToolExecutionException("Unable to convert "+term+" to polynomial")
    }
  }

  def fromRing(m: Monomial[Rational[BigInteger]]): Term = {
    val v = m.coefficient

    val vn = v.numerator().longValueExact()
    val vd = v.denominator().longValueExact()
    val cof = if (vd == 1) Number(vn) else Divide(Number(vn), Number(vd))

    val k = m.exponents.toList
    val xis = (cof::k.zipWithIndex.map( i =>
      if(i._1==0)  Number(1)
      else if(i._1 == 1) unmapper(i._2)
      else Power(unmapper(i._2), Number(i._1))
    )).filterNot(t => t==Number(1))
    def cleverTimes(a: Term, b: Term) = a match {
      case Number(n) if n == 1 => b
      case Number(n) if n == -1 => Neg(b)
      case _ => Times(a, b)
    }
    if(xis.isEmpty) cof
    else xis.tail.fold(xis.head)(cleverTimes)
  }

  def fromRing( p: Ring ): Term =
  {
    //Monomials contain their coefficients as well
    val monomials = p.collection().asScala.toList
    val ls1 = monomials.map(fromRing)

    val ls2 = ls1.filterNot(t => t==Number(0))
    if(ls2.isEmpty) Number(0)
    else ls2.tail.fold(ls2.head)(Plus)
  }

  //TODO: this is probably available somewhere in the library but I can't find it
  //Turn univariate polynomial back into the multivariant ring
  private def multiringify(varname:String, upoly: UnivariatePolynomial[Ring], ring:MultivariateRing[Rational[BigInteger]]) : Ring = {
    val coeffs = upoly.iterator().asScala.toList
    coeffs.zipWithIndex.map(
      p => ring.multiply(p._1,ring(varname+"^"+p._2.toString))
    ).foldLeft(ring.getZero)( (p1,p2) => ring.add(p1,p2))
  }

  def quotientRemainder(term: Term, div: Term, x:Variable): (Term,Term) = {
    val ringvar = mapper(x)
    val varindex = ring.index(ringvar)

    val ringterm = toRing(term).asUnivariate(varindex)
    val ringdiv = toRing(div).asUnivariate(varindex)

    val uniring = UnivariateRing(ringterm.ring, ringvar)

    val res = uniring.divideAndRemainder(ringterm,ringdiv)

    val mringquo = multiringify(ringvar,res(0),ring)
    val mringrem = multiringify(ringvar,res(1),ring)

    (fromRing(mringquo),fromRing(mringrem))
  }

  def groebnerBasis(polynomials: List[Term]): List[Term] = {
    if(polynomials.isEmpty) return List()
    Ideal(polynomials.map(toRing)).groebnerBasis.toList.map(fromRing)
  }

  def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term) = {
    val ringpoly = toRing(polynomial)
    val ringGB = GB.map(toRing)
    val res = (ringpoly /%/%* (ringGB:_*)).toList
    (res.init.map(fromRing),fromRing(res.last))
  }

  /** integral/primitive of `t` w.r.t. Variable `i` */
  def integrate(i: Int)(t: Ring) : Ring =
    t.mapTerms(Q, { mon =>
      val p = mon.dv.exponents(i)
      mon.
        setCoefficient(mon.coefficient.divide(p + 1)).
        setDegreeVector(mon.dv.dvMultiply(i, 1))
    })

  /** compute the Lie Derivative */
  def lieDerivative(ode: Variable => Option[Ring])(t: Term) : Ring = t match {
    case v: Variable => ode(v) match {
      case Some(u) => u
      case None => 0
    }
    case _: AtomicTerm => 0
    case f@FuncOf(_, Nothing) => 0
    case Neg(u) => -lieDerivative(ode)(u)
    case Plus(u, v) => lieDerivative(ode)(u) + lieDerivative(ode)(v)
    case Minus(u, v) => lieDerivative(ode)(u) - lieDerivative(ode)(v)
    case Times(u, v) => lieDerivative(ode)(u) * toRing(v) + toRing(u) * lieDerivative(ode)(v)
    case Divide(u, Number(n)) if n.isValidInt => lieDerivative(ode)(u) / n.toIntExact
    case Power(u, Number(n)) if n.isValidInt =>
      n.toIntExact * (toRing(u) ^ (n.toIntExact - 1)) * lieDerivative(ode)(u)
    case _ => throw ToolExecutionException("Operation not (yet) supported by RingsLibrary: " + t)
  }

  /** return None if b does not divide a, otherwise Some (quotient, remainder) */
  def internalQuotientRemainder(a: Ring, b: Ring) : Option[(Ring, Ring)] =
  {
    val array = ring.divideAndRemainder(a, b)
    val q = array(0)
    if (q.isZero) None
    else Some(q, array(1))
  }

  /** rewrite t to Horner Form (w.r.t. "Variables" xs)
    *
    * we allow arbitrary terms as "variables" in order to factor out e.g., squares.
    * */
  def toHorner(t: Ring, xs: List[Ring]): Term = xs match {
    case Nil => fromRing(t)
    case x :: xs => {
      internalQuotientRemainder(t, x) match {
        case None => toHorner(t, xs)
        case Some((q, r)) => {
          val hq = toHorner(q, x :: xs)
          val hr = toHorner(r, xs)
          val prod =
            if (hq == Number(0)) Number(0)
            else if (hq == Number(1)) fromRing(x)
            else if (hq == Number(-1)) Neg(fromRing(x))
            else Times(fromRing(x), hq)
          if (hr == Number(0)) prod
          else if (prod == Number(0)) hr
          else Plus(hr, prod)
        }
      }
    }
  }

  /** a distributive representation w.r.t. Variables in `xs` */
  def distributive(t: Ring, xs: Seq[Term]): Map[List[Int], Term] = {
    val monomials = t.collection().asScala.toList
    val exponentIndices = xs.map{
      case n: NamedSymbol => ring.index(mapper(n))
      case FuncOf(f, Nothing) => ring.index(mapper(f))
      case _ => throw ToolExecutionException("distributive only for variables and constants.")
    }
    def makeMonomialRep(m: Monomial[Rational[BigInteger]]) : List[Int] = exponentIndices.map(m.exponents(_)).toList
    monomials.foldLeft(Map[List[Int],Term]()){case(coeffs, m) =>
      val monRep = makeMonomialRep(m)
      val exponents2 = m.exponents.clone // TODO: how immutable is this rings library?
      exponentIndices.foreach(i => exponents2.update(i, 0))
      val monomial2 = fromRing(m.setDegreeVector(exponents2))
      coeffs.updated(monRep,
        coeffs.get(monRep) match {
          case None => monomial2
          case Some(trm) => Plus(trm, monomial2)
        })
    }
  }

  /** Substitute into a polynomial: simultaneously replace Variables v */
  def substitutes(subst: Variable => Option[Ring])(t: Term) : Ring = t match {
    case v: Variable => subst(v) match {
      case Some(u) => u
      case None => toRing(v)
    }
    case FuncOf(_, Nothing) => toRing(t)
    case Neg(u) => -substitutes(subst)(u)
    case Plus(u, v) => substitutes(subst)(u) + substitutes(subst)(v)
    case Minus(u, v) => substitutes(subst)(u) - substitutes(subst)(v)
    case Times(u, v) => substitutes(subst)(u) * substitutes(subst)(v)
    case Divide(u, Number(n)) if n.isValidInt => substitutes(subst)(u) / n.toIntExact
    case Power(u, Number(n)) if n.isValidInt => substitutes(subst)(u) ^ n.toIntExact
    case n : Number => toRing(n)
    case _ => throw ToolExecutionException("Operation " + t.kind + " not (yet) supported by substitutes in RingsLibrary: " + t)
  }

  /** split polynomial according to order w.r.t variables in list */
  def splitInternal(p: Ring, order: Int, vars: Seq[Int], drop: Seq[Int]) = {
    def keep(p: Monomial[Rational[BigInteger]]) : Boolean =
      p.dvTotalDegree(vars: _*) <= order && !drop.exists{d =>
        val pdve = p.dv.exponents
        p.dv.exponents(d) > 0
      }
    def mapToKeep(keep: Monomial[Rational[BigInteger]] => Boolean) : Ring =
      p.mapTerms(Q, { p => if(keep(p)) p else p.setCoefficient(Rational(0)(Z)) } )
    val poly = mapToKeep(keep)
    val rest = mapToKeep(!keep(_))
    (poly, rest)
  }

  private val namespace = "ringsalgebratool"

  private def remember(fml: Formula, tac: BelleExpr) = AnonymousLemmas.remember(fml, tac, namespace)

  private lazy val normalizeLemma = remember("a_() <= b_() <-> 0 <= b_() - a_()".asFormula, QE & done)

  /** a<=b to 0<=a-b, with the standard representation of a-b (distributive and according to the variable order of [[ring]],
    * also distributes over conjunctions... */
  def normalizeLessEquals(qeTac: BelleExpr): DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    seq.sub(pos) match {
      // TODO: generalize, chase?
      case Some(And(f1, f2)) =>
        normalizeLessEquals(qeTac)(pos ++ PosInExpr(0 :: Nil)) & normalizeLessEquals(qeTac)(pos ++ PosInExpr(1 :: Nil))
      case Some(LessEqual(a, b)) => {
        val d = fromRing(toRing(b) - toRing(a))
        useAt(normalizeLemma)(pos) &
          SequentCalculus.cut(Equal(Minus(b, a), d)) &
          Idioms.<(
            eqL2R(-seq.ante.length - 1)(pos) & hideL(-seq.ante.length - 1),
            cohideR('Rlast) & qeTac & done
          )
      }
    }
  }

  /** encapsulates information relevant for working with ODEs with the Rings library */
  case class ODE(time: Variable, state: Seq[Variable], const0: Seq[FuncOf], rhs: Seq[Term]) {
    private val stateI = state.map(v=>ring.index(mapper(v)))
    private val timeI = ring.index(mapper(time))
    private val const0I = const0.map(v=>ring.index(mapper(v.func)))
    private val tmVariablesI = Seq(timeI)++const0I

    def applyODE(xs: Seq[Ring]) = {
      rhs.map(f_i => substitutes((state,xs).zipped.toMap.get)(f_i))
    }

    /** compute the Picard operator P(x)*/
    def PicardOperation(x0R: Seq[Ring],
                        ps:  Seq[Ring],
                        order: Int,
                        consts_to_remainder: Seq[Int] = Nil,
                       ) : (Seq[Ring], Seq[Ring]) =
    {
      val fps = applyODE(ps)
      val pairs = (x0R,fps).zipped.map{case (x0R_i, fp) =>
        val int = integrate(timeI)(fp)
        val sum = x0R_i + int
        splitInternal(sum, order, tmVariablesI, consts_to_remainder)
      }
      pairs.unzip
    }

    /** perform picard iteration for initial value tm0 (a polynomial in const0) up to order */
    def PicardIteration(tm0: Seq[Ring], order: Int) = {
      var ptm = tm0
      for (i <- 0 until order) {
        ptm = PicardOperation(tm0, ptm, order)._1
      }
      ptm
    }
  }
}

class RingsAlgebraTool extends Tool with AlgebraTool {
  /** @inheritdoc */
  override val name: String = "RingsAlgebra"

  /** @inheritdoc */
  final override def init(config: Map[String, String]): Unit = {}

  /** @inheritdoc */
  final override def shutdown(): Unit = {}

  /** @inheritdoc */
  final override def restart(): Unit = {}

  /** @inheritdoc */
  final override def isInitialized: Boolean = true

  /** @inheritdoc */
  final override def cancel(): Boolean = true

  /** @inheritdoc */
  final override def quotientRemainder(term: Term, div: Term, x:Variable): (Term,Term) = {
    new RingsLibrary(x::List(term,div)).quotientRemainder(term, div, x)
  }

  /** @inheritdoc */
  final override def groebnerBasis(polynomials: List[Term]): List[Term] = {
    if(polynomials.isEmpty) return List()
    new RingsLibrary(polynomials).groebnerBasis(polynomials)
  }

  /** @inheritdoc */
  final override def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term) = {
    new RingsLibrary(polynomial::GB).polynomialReduce(polynomial, GB)
  }

}