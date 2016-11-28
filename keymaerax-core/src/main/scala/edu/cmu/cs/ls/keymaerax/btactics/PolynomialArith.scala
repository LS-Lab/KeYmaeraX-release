package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.{Variable, _}

import scala.collection.immutable.{Map, _}

/**
  * Created by yongkiat on 11/27/16.
  */
object PolynomialArith {

  /**
    * Normalised polynomial arithmetic
    *
    * A normalised monomial has the following shape in KeYmaeraX's term grammar (n is a number > 0):
    *
    * mono:= 1 | mono * (Var)^n
    *
    * Variables in the first half of * must be lexicographically > than the variable in the second by Scala string cmp
    *
    * Similarly, a normalised polynomial has the following shape (const is non-zero):
    *
    * poly:= 0 | poly + const * mono
    *
    * monomials in the second half of + must be smaller than the first half by monomial ordering
    *
    * The units are included for now to get a nicer definition??
    *
    */

  //Sanity check that a term representing a monomial satisfies the monomial normalisation requirement
  def checkMono(t:Term,maxs:String = ""): Boolean = {
    t match {
      case n:Number => n.value == 1
      case Times(l,Power(s:Variable,n:Number)) =>
        n.value.isValidInt && s.name > maxs && checkMono(l,s.name)
      case _ => false
    }
  }

  //Monomial order
  def ordMono(t:Term) : Integer = {
    //assert(checkMono(t))
    t match {
      case Times(l,Power(s:Variable,n:Number)) => n.value.toInt + ordMono(l)
      case _ => 0
    }
  }

  //Lexicographical < comparison of monomials
  def lexMono(l:Term,r:Term) :Boolean = {
    (l,r) match {
      case(n:Number,m:Number) => false
      case (Times(l,Power(sl:Variable,nl:Number)),Times(r,Power(sr:Variable,nr:Number))) =>
        if(sl.name > sr.name) true
        else if(sl.name == sr.name) {
          if (nl.value < nr.value) true
          else if(nl.value == nr.value) lexMono(l,r)
          else false
        }
        else false
    }
  }

  //Strict monomial comparison l < r?
  def cmpMono(l:Term,r:Term) : Boolean = {
    val or = ordMono(r)
    val ol = ordMono(l)
    if (or > ol) {
      true
    }
    else if(or == ol) {
      lexMono(l,r)
    }
    else false
  }

  //Sanity check that a term representing a polynomial satisfies the normalisation requirement
  def checkPoly(t:Term,maxm:Option[Term] = None): Boolean = {
    t match {
      case n:Number => n.value == 0
      case Plus(l,Times(c:Number,m)) =>
        (c.value != 0) && checkMono(m) &&
          (maxm match {
          case None => checkPoly(l,Some(m))
          case Some(n) => cmpMono(m,n) && checkPoly(l,Some(n))
          })
      case _ => false
    }
  }

  //Takes and returns normalised polynomials
  def addPoly(l:Term,r:Term): Term = {
    println(l,r)
    (l,r) match {
      case (n:Number,_) => r //Left unit for addition
      case (_,n:Number) => l //Right unit for addition
      case (Plus(nl,Times(cl:Number,ml)),Plus(nr,Times(cr:Number,mr))) => {
        if(cmpMono(ml,mr)) {
          Plus(addPoly(l,nr),Times(cr:Number,mr))
        }
        else if (ml == mr) {
          val cnew = cl.value + cr.value
          if(cnew == 0)
            addPoly(nl,nr)
          else
            Plus(addPoly(nl,nr),Times(Number(cl.value+cr.value),ml))
        }
        else addPoly(r,l)
      }
      case _ => ???
    }
  }

  //Multiplies and returns normalised monomials
  def mulMono(l:Term,r:Term): Term = {
    (l,r) match {
      case(n:Number,_) => r  //Unit
      case (_,n:Number) => l //Unit
      case (Times(nl,Power(sl:Variable,ml:Number)),Times(nr,Power(sr:Variable,mr:Number))) =>
        if(sl.name > sr.name)
        {
          Times(mulMono(l,nr),Power(sr:Variable,mr:Number))
        }
        else if(sl.name == sr.name) {
          Times(mulMono(nl,nr),Power(sl,Number(ml.value+mr.value)))
        }
        else mulMono(r,l)
      case _ => ???
    }
  }

  //Multiplies a normalized polynomial by a constant and a normalized monomial
  def mulPolyMono(l:Term,c:Number,r:Term): Term = {
    l match {
      case n:Number => n // Multiplication by 0 poly
      case Plus(nl,Times(cl:Number,ml)) =>
        Plus(mulPolyMono(nl,c,r),Times(Number(cl.value*c.value),mulMono(ml,r)) )
      case _ => ???
    }
  }

  //Multiplies and returns normalised polynomials
  def mulPoly(l:Term,r:Term): Term = {
    r match {
      case n:Number => n //Multiplication by 0 poly
      case Plus(nr,Times(cr:Number,mr)) => addPoly(mulPoly(l,nr),mulPolyMono(l,cr,mr))
      case _ => ???
    }
  }
}
