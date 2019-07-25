package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._
import cc.redberry.rings
import cc.redberry.rings.bigint.BigInteger
import cc.redberry.rings.poly.multivar.MultivariateDivision
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith
import rings.scaladsl._
import syntax._

import scala.collection.JavaConverters._

/**
  * A link to Rings library for its algebra tools
  */

class RingsAlgebraTool() extends AlgebraTool{

//  private def mkCoeff(n:Int,m:Int, vmap:Map[NamedSymbol,Int]) : Polynomial = {
//    val arr = 1.until(vmap.size).foldLeft(Array(vf.rational(n,m)).asInstanceOf[Object])( (res,i) => Array(res))
//    vf.polynomial(arr)
//  }
//
  private def uniqueNames(names:List[NamedSymbol]) : (Map[NamedSymbol,String],Map[Int,Term]) = {
    val ls = names.zipWithIndex.map( p =>
      p._1 match {
        case v:Variable => (p._1,"AVAR"+p._2)
        case _ => (p._1,"BFUNC"+p._2)
      }
    )

    val lsun = names.zipWithIndex.map( p => (p._2,
      p._1 match {
        case v:Variable => v
        case f:Function => FuncOf(f,Nothing)
        case _ => ??? //never happens
      }))

    (ls.toMap,lsun.toMap)
  }

  private def toRing(term:Term, ring:MultivariateRing[Rational[BigInteger]], mapper: Map[NamedSymbol,String]) : MultivariatePolynomial[Rational[BigInteger]] = {
    term match {
      case Neg(l) =>
        ring.negate(toRing(l,ring,mapper))
      case Plus(l,r) =>
        ring.add(toRing(l,ring,mapper),toRing(r,ring,mapper))
      case Minus(l,r) =>
        ring.subtract(toRing(l,ring,mapper),toRing(r,ring,mapper))
      case Times(l,r) =>
        ring.multiply(toRing(l,ring,mapper),toRing(r,ring,mapper))
      case Divide(l,r) =>
        val arr = ring.divideAndRemainder(toRing(l,ring,mapper),toRing(r,ring,mapper))
        if(!arr(1).isZero)
          throw new IllegalArgumentException("Unable to divide "+l+" by "+r+" to obtain a polynomial")
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
      case Power(l,r) => {
        PolynomialArith.groundNormaliseProof(r,true) match {
          case Some((n:Number,pr)) if n.value.isValidInt && n.value >= 0 => {
            ring.pow(toRing(l,ring,mapper) , n.value.toIntExact)
          }
          case res => throw new IllegalArgumentException("Unable to reduce exponent "+r+" to a natural number")
        }
      }
      case f:FuncOf if f.child == Nothing =>
        ring(mapper(f.func))
      case _ => throw new IllegalArgumentException("Unable to convert "+term+" to polynomial")
    }
  }

  private def fromRing( p: MultivariatePolynomial[Rational[BigInteger]], unmapper:  Map[Int,Term] ): Term =
  {
    //Monomials contain their coefficients as well
    val monomials = p.collection().asScala.toList
    val ls1 = monomials.map(
      m => {
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
        if(xis.isEmpty) cof
        else xis.tail.fold(xis.head)(Times)
      }
    )

    val ls2 = ls1.filterNot(t => t==Number(0))
    if(ls2.isEmpty) Number(0)
    else ls2.tail.fold(ls2.head)(Plus)
  }

  //TODO: this is probably available somewhere in the library but I can't find it
  //Turn univariate polynomial back into the multivariant ring
  private def multiringify(varname:String, upoly: UnivariatePolynomial[MultivariatePolynomial[Rational[BigInteger]]], ring:MultivariateRing[Rational[BigInteger]]) :
  MultivariatePolynomial[Rational[BigInteger]] = {
    val coeffs = upoly.iterator().asScala.toList
    coeffs.zipWithIndex.map(
      p => ring.multiply(p._1,ring(varname+"^"+p._2.toString))
    ).foldLeft(ring.getZero)( (p1,p2) => ring.add(p1,p2))
  }

  override def quotientRemainder(term: Term, div: Term, x:Variable): (Term,Term) = {
    //@note sort for stable results
    val syms = (x::List(term,div).flatMap(p => StaticSemantics.symbols(p))).distinct.sorted

    // Only constant symbols f() and vars are kept. Everything else is discarded
    val (vars,rest) = syms.partition( p => p.isInstanceOf[BaseVariable])
    val (funcs,emp) = rest.partition( p => p.isInstanceOf[Function] && p.asInstanceOf[Function].domain == Unit )

    if(emp.nonEmpty)
      throw new IllegalArgumentException("RingsAlgebraTool does not handle non-constant function symbols: " +emp)

    val (mapper,unmapper) = uniqueNames(vars++funcs)

    //It should always be VAR(XXX)
    val varindex = mapper(x).drop(3).toInt

    implicit val ring = MultivariateRing(Q,mapper.values.toArray.sorted)

    val ringterm = toRing(term,ring,mapper).asUnivariate(varindex)
    val ringdiv = toRing(div,ring,mapper).asUnivariate(varindex)

    val uniring = UnivariateRing(ringterm.ring,"VAR"+varindex)

    val res = uniring.divideAndRemainder(ringterm,ringdiv)

    val mringquo = multiringify("VAR"+varindex,res(0),ring)
    val mringrem = multiringify("VAR"+varindex,res(1),ring)

    (fromRing(mringquo,unmapper),fromRing(mringrem,unmapper))
  }

  override def groebnerBasis(polynomials: List[Term]): List[Term] = {

    if(polynomials.isEmpty) return List()
    //@note sort for stable results
    val syms = polynomials.flatMap(p => StaticSemantics.symbols(p)).distinct.sorted

    // Only constant symbols f() and vars are kept. Everything else is discarded
    val (vars,rest) = syms.partition( p => p.isInstanceOf[BaseVariable])
    val (funcs,emp) = rest.partition( p => p.isInstanceOf[Function] && p.asInstanceOf[Function].domain == Unit )

    if(emp.nonEmpty)
      throw new IllegalArgumentException("RingsAlgebraTool does not handle non-constant function symbols: " +emp)

    val (mapper,unmapper) = uniqueNames(vars++funcs)

    implicit val ring = MultivariateRing(Q,mapper.values.toArray.sorted)

    val ringpolynomials = polynomials.map(toRing(_,ring,mapper))

    val gb = Ideal(ringpolynomials).groebnerBasis.toList
    //println(ringpolynomials,gb)
    gb.map(fromRing(_,unmapper))
  }

  override def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term) = {
    //@note sort for stable results
    val syms = (polynomial::GB).flatMap(p => StaticSemantics.symbols(p)).distinct.sorted

    // Only constant symbols f() and vars are kept. Everything else is discarded
    val (vars,rest) = syms.partition( p => p.isInstanceOf[BaseVariable])
    val (funcs,emp) = rest.partition( p => p.isInstanceOf[Function] && p.asInstanceOf[Function].domain == Unit )

    if(emp.nonEmpty)
      throw new IllegalArgumentException("RingsAlgebraTool does not handle non-constant function symbols: " +emp)

    val (mapper,unmapper) = uniqueNames(vars++funcs)

    implicit val ring = MultivariateRing(Q,mapper.values.toArray.sorted)

    val ringpoly = toRing(polynomial,ring,mapper)
    val ringGB = GB.map(toRing(_,ring,mapper))

    val res = (ringpoly /%/%* (ringGB:_*)).toList

    val quos = res.init.map(fromRing(_,unmapper))
    val rem = fromRing(res.last,unmapper)

    (quos,rem)
  }
}