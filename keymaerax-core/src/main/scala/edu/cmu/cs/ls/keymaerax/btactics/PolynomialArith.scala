package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._

import scala.collection.immutable.{Map, _}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

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

  //List of reassociations needed -- avoids QE inside the actual proof (QE should get everything right)
  private val plusAssoc1 = proveBy("(F_() + G_()) + (A_() + B_()) = ((F_()+G_())+A_())+B_()".asFormula,QE)
  private val plusAssoc2 = proveBy("(F_() + K_()*M_()) + (A_() + L_()*M_()) = (F_()+A_())+(K_()+L_())*M_()".asFormula,QE)

  private val plusCoeff1 = proveBy("K_() = 0 -> (F_() + K_()*M_() = F_())".asFormula,QE)
  private val plusCoeff2 = proveBy("K_() = L_() -> (F_() + K_()*M_() = F_() + L_()*M_())".asFormula,
    byUS("const congruence"))

  //Takes and returns normalised polynomials
  def addPoly(l:Term,r:Term): (Term,ProvableSig) = {
    val lhs = Plus(l,r)
    (l,r) match {
      case (n:Number,_) => //Left unit for addition
        (r,proveBy(Equal(lhs,r), byUS("0+")))
      case (_,n:Number) => //Right unit for addition
        (l,proveBy(Equal(lhs,l), byUS("+0")))
      case (Plus(nl,Times(cl:Number,ml)),Plus(nr,Times(cr:Number,mr))) => {
        if(cmpMono(ml,mr)) {
          val (rec,pr) = addPoly(l,nr)
          val res = Plus(rec,Times(cr:Number,mr))
          (res,proveBy(Equal(lhs,res), useAt(plusAssoc1)(SuccPosition(1,0::Nil))
            & useAt(pr)(SuccPosition(1,0::0::Nil)) & byUS("= reflexive")))
        }
        else if (ml == mr) {
          val (rec,pr) = addPoly(nl,nr)
          val cnew = cl.value + cr.value
          if(cnew == 0) //Canceling out the 0
            (rec, proveBy(Equal(lhs,rec), useAt(plusAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(plusCoeff1,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & TactixLibrary.RCF))
          else {
            val res = Plus(rec,Times(Number(cl.value+cr.value),ml))
            (res, proveBy(Equal(lhs,res), useAt(plusAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(plusCoeff2,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          }
        }
        else {
          val (rec,pr) = addPoly(r,l)
          //Flip the +
          (rec,useFor("+ commute")(SuccPosition(1,0::Nil))(pr))
        }
      }
      case _ => ???
    }
  }

  //One of these is missing in DerivedAxioms
  private val onetimes = proveBy("1*F_() = F_()".asFormula,QE)
  private val timesone = proveBy("F_()*1 = F_()".asFormula,QE)

  private val timesAssoc1 = proveBy("(F_() * G_()) * (A_() * B_()) = ((F_()*G_())*A_())*B_()".asFormula,QE)
  private val timesAssoc2 = proveBy("(F_() * M_()^K_()) * (A_() * M_()^L_()) = (F_()*A_())*M_()^(K_()+L_())".asFormula,QE)

  //QE has interesting ideas about X^0
  private val timesCoeff1Lem = proveBy("F_() = F_() * M_() ^ 0".asFormula,QE)
  private val timesCoeff1 = proveBy("K_() = 0 -> (F_() * M_()^K_() = F_() )".asFormula,
    useAt(timesCoeff1Lem)(SuccPosition(1,1::1::Nil)) & byUS("const congruence"))

  private val timesCoeff2 = proveBy("K_() = L_() -> (F_() * M_()^K_() = F_() * M_()^L_())".asFormula,
    byUS("const congruence"))

  //Multiplies and returns normalised monomials (this is basically the same as the implementation for adding polynomials)
  def mulMono(l:Term,r:Term): (Term,ProvableSig) = {
    val lhs = Times(l,r)
    (l,r) match {
      case(n:Number,_) => (r,proveBy(Equal(lhs,r),byUS(onetimes)))  //Unit
      case (_,n:Number) => (l,proveBy(Equal(lhs,l),byUS(timesone))) //Unit
      case (Times(nl,Power(sl:Variable,ml:Number)),Times(nr,Power(sr:Variable,mr:Number))) =>
        if(sl.name > sr.name)
        {
          val(rec,pr) = mulMono(l,nr)
          val res = Times(rec,Power(sr:Variable,mr:Number))
          (res,proveBy(Equal(lhs,res), useAt(timesAssoc1)(SuccPosition(1,0::Nil))
            & useAt(pr)(SuccPosition(1,0::0::Nil)) & byUS("= reflexive")))
        }
        else if(sl.name == sr.name) {
          val(rec,pr) = mulMono(nl,nr)
          val mnew = ml.value + mr.value
          if(mnew == 0) //Canceling out the 0
            (rec, proveBy(Equal(lhs,rec), useAt(timesAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(timesCoeff1,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          else {
            val res = Times(rec,Power(sl,Number(ml.value+mr.value)))
            (res, proveBy(Equal(lhs,res), useAt(timesAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(timesCoeff2,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          }
        }
        else {
          val (rec,pr) = mulMono(r,l)
          //Flip the *
          (rec,useFor("* commute")(SuccPosition(1,0::Nil))(pr))
        }
      case _ => ???
    }
  }

  private val timesAssoc3 = proveBy(("(P_() + C_() * M_()) * (D_() * N_()) = " +
    "P_() * (D_() * N_()) + (C_() * D_()) * (M_() * N_())").asFormula,QE)

  //Multiplies a normalized polynomial by a constant and a normalized monomial
  def mulPolyMono(l:Term,c:Number,r:Term): (Term,ProvableSig) = {
    val lhs = Times(l,Times(c,r))
    l match {
      case n:Number => (n,proveBy(Equal(lhs,n),byUS("0*"))) // Multiplication by 0 poly
      case Plus(nl,Times(cl:Number,ml)) =>
        val (rec1,pr1) = mulPolyMono(nl,c,r)
        val (rec2,pr2) = mulMono(ml,r)
        val res =  Plus(rec1,Times(Number(cl.value*c.value),rec2) )

        (res,proveBy(Equal(lhs,res),useAt(timesAssoc3)(SuccPosition(1,0::Nil))
          & useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::1::Nil))
          & useAt(plusCoeff2,PosInExpr(1::Nil))(1)
          //Should only be simple arithmetic
          & RCF))

      case _ => ???
    }
  }

  //Multiplies and returns normalised polynomials
  def mulPoly(l:Term,r:Term): (Term,ProvableSig) = {
    val lhs = Times(l,r)
    r match {
      case n:Number => (n,proveBy(Equal(lhs,n),byUS("*0"))) //Multiplication by 0 poly
      case Plus(nr,Times(cr:Number,mr)) =>
        val (rec1,pr1) = mulPoly(l,nr)
        val (rec2,pr2) = mulPolyMono(l,cr,mr)
        val (res,pr3) = addPoly(rec1,rec2)
        (res,proveBy(Equal(lhs,res),useAt("distributive")(SuccPosition(1,0::Nil))
          & useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)
        ))

      case _ => ???
    }
  }

  //Normalizes an otherwise un-normalized term
  //Not many bells and whistles yet
  def normalise(l:Term) : (Term,ProvableSig) = {
    l match {
      case n:Number =>
        val res = Plus(Number(0), Times(n,Number(1)))
        (res,proveBy(Equal(l,res), RCF ))
      case v:Variable =>
        val res = Plus(Number(0),Times(Number(1), Times(Number(1),Power(v,Number(1))) ))
        (res,proveBy(Equal(l,res), RCF ))
      case Plus(ln,rn) =>
        val (rec1,pr1) = normalise(ln)
        val (rec2,pr2) = normalise(rn)
        val (res,pr3) = addPoly(rec1,rec2)
        (res,proveBy(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)))
      case Times(ln,rn) =>
        val (rec1,pr1) = normalise(ln)
        val (rec2,pr2) = normalise(rn)
        val (res,pr3) = mulPoly(rec1,rec2)
        (res,proveBy(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)))
      case _ => ???
    }
  }
}
