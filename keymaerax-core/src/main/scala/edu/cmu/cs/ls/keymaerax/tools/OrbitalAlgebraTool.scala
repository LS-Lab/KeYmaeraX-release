package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith
import orbital.math._
import orbital.util.KeyValuePair

import scala.collection.JavaConverters._

/**
 * A link to Orbital for its algebra tools
 */

class OrbitalAlgebraTool() extends AlgebraTool{

  private val vf = Values.getDefault

  private def mkCoeff(n:Int,m:Int, vmap:Map[NamedSymbol,Int]) : Polynomial = {
    val arr = 1.until(vmap.size).foldLeft(Array(vf.rational(n,m)).asInstanceOf[Object])( (res,i) => Array(res))
    vf.polynomial(arr)
  }

  // emap gives the indeterminates of an underlying coefficient ring
  // vmap gives the indeterminates of the polynomial ring over this coefficient ring
  // both assumed to be non-empty
  private def mapWith(term:Term, vmap:Map[NamedSymbol,Int]) : Polynomial = {
    term match {
      case Plus(l,r) =>
        mapWith(l,vmap).add(mapWith(r,vmap))
      case Minus(l,r) =>
        mapWith(l,vmap).subtract(mapWith(r,vmap))
      case Times(l,r) =>
        mapWith(l,vmap).multiply(mapWith(r,vmap))
      // Only rationals are supported
      case Divide(n:Number,m:Number) if n.value.isValidInt && m.value.isValidInt =>
        //Construct a/b in the underlying coefficient ring
        mkCoeff(n.value.toIntExact,m.value.toIntExact,vmap)
      // Only ints
      case n:Number if n.value.isValidInt => {
        mkCoeff(n.value.toIntExact,1,vmap)
      }
      // Every variable must be mapped
      case v:Variable =>
        vmap.get(v) match {
          case Some(i) => vf.MONOMIAL(Array.tabulate[Int](vmap.size)(n => if (n==i) 1 else 0))
          case None => ???
        }
      // Some special cases for powers
      case Power(l,r) => {
        PolynomialArith.groundNormaliseProof(r,true) match {
          case Some((n:Number,pr)) if n.value.isValidInt && n.value >= 0 => {
             mapWith(0.until(n.value.toIntExact-1).foldLeft(l) ( (t,i) => Times(t,l)),vmap)
          }
          case res => ???
        }
      }
      case _ => ???
    }
  }

  private def unmapWith(p : Polynomial, vunmap:Map[Int,NamedSymbol]) : Term = {
    val monkvp = p.monomials().asScala.toList.map(_.asInstanceOf[KeyValuePair])

    val ls1 = monkvp.map( kv => {
      val v = kv.getValue.asInstanceOf[Rational]
      val vn = v.numerator().intValue()
      val vd = v.denominator().intValue()
      if (vn==0) Number(0)
      else {
        val cof = if (vd == 1) Number(vn) else Divide(Number(vn), Number(vd))
        val k =
          if(kv.getKey.isInstanceOf[Vector])
            kv.getKey.asInstanceOf[Vector].iterator().asScala.toList.map(_.asInstanceOf[Integer].intValue())
          else if(kv.getKey.isInstanceOf[Integer])
            List(kv.getKey.asInstanceOf[Integer].intValue())
          else
            ???
        val xis = (cof::k.zipWithIndex.map( i =>
          if(i._1==0)  Number(1)
          else if(i._1 == 1) vunmap(i._2).asInstanceOf[Term]
          else Power(vunmap(i._2).asInstanceOf[Term], Number(i._1))
        )).filterNot(t => t==Number(1))
        if(xis.isEmpty) cof
        else xis.tail.fold(xis.head)(Times)
      }
    })
    val ls2 = ls1.filterNot(t => t==Number(0))
    if(ls2.isEmpty) Number(0)
    else ls2.tail.fold(ls2.head)(Plus)
  }

  override def quotientRemainder(term: Term, div: Term, x:Variable): (Term,Term) = {
    ???
  }

  override def groebnerBasis(polynomials: List[Term]): List[Term] = {
    //@note sort for stable results
    val vars = polynomials.flatMap(p => StaticSemantics.vars(p).symbols[NamedSymbol]).distinct.sorted
    val varmap = vars.zipWithIndex.toMap
    val varunmap = vars.zipWithIndex.map( p => (p._2,p._1) ).toMap

    val orbitalpolys = polynomials.map( p => mapWith(p,varmap))
    val orbitalgrob = AlgebraicAlgorithms.groebnerBasis(orbitalpolys.toSet.asJava,AlgebraicAlgorithms.DEGREE_REVERSE_LEXICOGRAPHIC)

    val grob = orbitalgrob.iterator().asScala.toList.map( _.asInstanceOf[Polynomial])

    grob.map(p => unmapWith(p,varunmap))
  }

  override def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term) = {
    //@note sort for stable results
    val vars = (polynomial::GB).flatMap(p => StaticSemantics.vars(p).symbols[NamedSymbol]).distinct.sorted
    val varmap = vars.zipWithIndex.toMap
    val varunmap = vars.zipWithIndex.map( p => (p._2,p._1) ).toMap

    val orbitalpoly = mapWith(polynomial,varmap)
    val orbitalGB = GB.map( mapWith(_,varmap)).asJava
    val orbitalred = AlgebraicAlgorithms.reduce(orbitalpoly,orbitalGB,AlgebraicAlgorithms.DEGREE_REVERSE_LEXICOGRAPHIC)

    /* cofactors ??? */
    (List(), unmapWith(orbitalred,varunmap))
  }
}
