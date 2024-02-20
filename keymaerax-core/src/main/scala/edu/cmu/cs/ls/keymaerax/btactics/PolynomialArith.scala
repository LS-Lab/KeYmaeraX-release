/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.bellerophon._

import scala.collection.immutable
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.infrastruct.{RenUSubst, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._

/**
  * Created by yongkiat on 11/27/16.
  */
object PolynomialArith extends Logging {

  private val namespace = "polynomialarith"

  /**
    * Normalised polynomial arithmetic
    *
    * A normalised monomial has the following shape in KeYmaeraX's term grammar:
    *
    * mono:= 1 | mono * (Var)^n
    *
    * Variables in the first half of * must be lexicographically > than the variable in the second by VarOrd
    * ("Variables" is meant a bit loosely in that nullary function symbols are allowed too)
    * (n must be a Number)
    *
    * Similarly, a normalised polynomial has the following shape (const is non-zero):
    *
    * poly:= 0 | poly + const * mono
    *
    * monomials in the second half of + must be smaller than the first half by monomial ordering
    * const must be a rational coefficient represented by Divide(Number,Number),
    * with both numerator != 0, denominator > 0 and they must be co-prime
    *
    * The units are included for now to get a nicer definition??
    *
    */

  // Collection of all the axioms used

  //These are all basic re-association lemmas for the polynomial normalization
  private lazy val plusAssoc1 = remember("(F_() + G_()) + (A_() + B_()) = ((F_()+G_())+A_())+B_()".asFormula, useAt(Ax.equalCommute)(1) & byUS(Ax.plusAssociative), namespace).fact
  //todo: we might get this if the simplifier understood AC rewriting..
  private lazy val plusAssoc2 = remember("(F_() + K_()*M_()) + (A_() + L_()*M_()) = (F_()+A_())+(K_()+L_())*M_()".asFormula, QE & done, namespace).fact

  private lazy val plusCoeff1 = remember("K_() = 0 -> (F_() + K_()*M_() = F_())".asFormula, prop & exhaustiveEqL2R(-1) & SimplifierV3.simpTac()(1) & close, namespace).fact
  private lazy val plusCoeff2 = remember("K_() = L_() -> (F_() + K_()*M_() = F_() + L_()*M_())".asFormula, byUS(Ax.constCongruence), namespace).fact

  private lazy val onetimes = useFor(Ax.timesCommute, PosInExpr(0 :: Nil))(SuccPosition(1,0::Nil))(Ax.timesIdentity.provable)
  private lazy val timesone = Ax.timesIdentity

  private lazy val timesAssoc1 = remember("(F_() * G_()) * (A_() * B_()) = ((F_()*G_())*A_())*B_()".asFormula,
    useAt(Ax.equalCommute)(1) & byUS(Ax.timesAssociative), namespace).fact
  //todo: we might get this if the simplifier understood AC rewriting..
  private lazy val timesAssoc2 = remember("(F_() * M_()^K_()) * (A_() * M_()^L_()) = (F_()*A_())*M_()^(K_()+L_())".asFormula, QE & done, namespace).fact
  private lazy val timesAssoc3 = remember(("(P_() + C_() * M_()) * (D_() * N_()) = " +
    "P_() * (D_() * N_()) + (C_() * D_()) * (M_() * N_())").asFormula, QE & done, namespace).fact

  //QE has interesting ideas about X^0
  private lazy val timesCoeff1Lem = remember("F_() = F_() * M_() ^ 0".asFormula, SimplifierV3.simpTac()(1) & close, namespace).fact
  private lazy val timesCoeff1 = remember("K_() = 0 -> (F_() * M_()^K_() = F_() )".asFormula,
    useAt(timesCoeff1Lem)(SuccPosition(1,1::1::Nil)) & byUS(Ax.constCongruence), namespace).fact
  private lazy val timesCoeff2 = remember("K_() = L_() -> (F_() * M_()^K_() = F_() * M_()^L_())".asFormula,
    byUS(Ax.constCongruence), namespace).fact

  //These are used for iterated squaring
  private lazy val powLem1 = Ax.powZero.provable
  private lazy val powLem2 = Ax.powOne.provable
  private lazy val powLem3 = remember("(F_()^K_())^2 = F_()^(2*K_())".asFormula, QE & done, namespace)
  private lazy val powLem4 = remember("(F_()^K_())^2 * F_() = F_()^(2*K_()+1)".asFormula, QE & done, namespace)
  private lazy val powLem5 = remember("K_() = L_() -> (M_()^K_() = M_()^L_())".asFormula,
    byUS(Ax.constCongruence), namespace).fact

  private lazy val negNormalise = remember("-P_() = P_() * (-1/1 * 1)".asFormula,SimplifierV3.simpTac()(1) & close, namespace).fact
  //todo: this could be added to simplifier
  private lazy val minusNormalise = remember("P_()-Q_() = P_() + -(Q_())".asFormula, QE & done, namespace).fact
  private lazy val powNormalise = remember("P_()^2 = P_() * P_()".asFormula, QE & done, namespace).fact

  //todo: this could be added to simplifier
  private lazy val divNormalise = remember(" P_() / Q_()  = (1/Q_()) *P_() ".asFormula, QE & done, namespace).fact
  //Add ^1 for a variable
  private lazy val var1Normalise = remember("P_() = 0 + (1/1) * (1 * P_()^1)".asFormula, SimplifierV3.simpTac()(1) & close, namespace).fact
  //Normalization for any variable (or power of variable)
  private lazy val varNormalise = remember("P_() = 0 + (1/1) * (1 * P_())".asFormula, SimplifierV3.simpTac()(1) & close, namespace).fact

  //todo: These are the key axioms, but they can probably be derived from simplifer things
  private lazy val zeroGeZero:ProvableSig = remember("0>=0".asFormula, RCF, namespace).fact
  private lazy val plusGeMono: ProvableSig = remember("(f_() >= k_() & g_() >= 0) -> f_() + g_() >= k_()".asFormula, QE, namespace).fact
  private lazy val timesPos: ProvableSig = remember("(f_() >= 0 & g_() >= 0) -> f_() * g_() >= 0".asFormula, QE, namespace).fact

  private lazy val neGtSquared : ProvableSig = remember(" f_() != 0 & g_() > 0 -> f_()^2 * g_() > 0 ".asFormula, QE, namespace).fact
  private lazy val plusGtMono: ProvableSig = remember("(f_() > k_() & g_() >= 0) -> f_() + g_() > k_()".asFormula, QE, namespace).fact

  private lazy val gtNotZero: ProvableSig = remember("f_() > 0 -> !(f_() = 0)".asFormula,
    prop & exhaustiveEqL2R(-2) & SimplifierV3.simpTac()(-1) & close, namespace).fact
  private lazy val axMov: ProvableSig = remember("f_() + a_() * g_() = k_() -> (a_() = 0 -> f_() = k_())".asFormula,
    prop & exhaustiveEqL2R(-2) & SimplifierV3.simpTac()(-1) & close, namespace).fact

  /**
    * The rest of the axiomatization
    */


  //(based on note in DerivedAxioms) These require Mathematica QE to prove, will be asserted as axioms
  //note: these fold = 0 normalisation in as well
  //todo: do the existsL naming properly

  private lazy val doubleNeg = remember("P_() <-> !(!P_())".asFormula, prop, namespace).fact

  //This just makes sorting the assumptions a bit easier
  private lazy val neAnteZ: ProvableSig = remember("f_() != g_() <-> !!(f_()-g_() !=0)".asFormula, QE & done, namespace).fact
  private lazy val ltAnteZ: ProvableSig = remember("f_() < g_() <-> f_() <= g_() & f_() - g_() != 0 ".asFormula, QE, namespace).fact
  private lazy val gtAnteZ: ProvableSig = remember("f_() > g_() <-> f_() >= g_() & f_() - g_() != 0 ".asFormula, QE, namespace).fact

  private lazy val existsOr1 = remember("(\\exists x_ p_(x_) | \\exists y_ q_(y_)) <-> (\\exists x_ (p_(x_) |  q_(x_)))".asFormula,
    prop & OnAll(existsL(Symbol("L")) & prop) <( existsR(Symbol("R")), existsR(Symbol("R")), existsR("y_".asTerm)(Symbol("R")), existsR("x_".asTerm)(Symbol("Rlast"))) & OnAll(prop), namespace).fact

  private lazy val existsSame = remember("(\\exists x_ p_(x_) | \\exists x_ q_(x_)) <-> (\\exists x_ (p_(x_) |  q_(x_)))".asFormula,
    prop & OnAll(existsL(Symbol("L")) & prop) <( existsR(Symbol("R")), existsR(Symbol("R")), existsR("x_".asTerm)(Symbol("R")), existsR("x_".asTerm)(Symbol("Rlast"))) & OnAll(prop), namespace).fact

  private lazy val existsOr2 = remember("\\exists x_ p_(x_) | q_() <-> (\\exists x_ (p_(x_) |  q_()))".asFormula,
    prop & OnAll(SaturateTactic(existsL(Symbol("L"))) & SaturateTactic(existsR(Symbol("R"))) & prop), namespace).fact

  private lazy val existsOr3 = remember("q_() | \\exists x_ p_(x_) <-> (\\exists x_ (p_(x_) |  q_()))".asFormula,
    prop & OnAll(SaturateTactic(existsL(Symbol("L"))) & SaturateTactic(existsR(Symbol("R"))) & prop), namespace).fact

  private lazy val existsAnd1 = remember("(\\exists x_ p_(x_) & \\exists y_ q_(y_)) <-> (\\exists x_ \\exists y_ (p_(x_) & q_(y_)))".asFormula,
    prop & OnAll(SaturateTactic(existsL(Symbol("L"))) & prop) <( existsR(Symbol("R")) & existsR(Symbol("R")) & prop, existsR(Symbol("R")) & prop, existsR(Symbol("R")) & prop), namespace).fact

  private lazy val existsAnd2 = remember("(\\exists x_ p_(x_) & q_()) <-> (\\exists x_ (p_(x_) & q_()))".asFormula,
    prop & OnAll(SaturateTactic(existsL(Symbol("L"))) & SaturateTactic(existsR(Symbol("R"))) & prop), namespace).fact

  private lazy val existsAnd3 = remember("(q_() & \\exists x_ p_(x_)) <-> (\\exists x_ (p_(x_) & q_()))".asFormula,
    prop & OnAll(SaturateTactic(existsL(Symbol("L"))) & SaturateTactic(existsR(Symbol("R"))) & prop), namespace).fact

  private lazy val existsRename = remember("(\\exists x_ p_(x_) & \\exists x_ q_(x_)) <-> (\\exists x_ p_(x_) & \\exists z_ q_(z_))".asFormula,
    prop & OnAll(SaturateTactic(existsL(Symbol("L"))) & prop) <(existsR("x_".asTerm)(Symbol("R")), existsR("z_".asTerm)(Symbol("R"))) & OnAll(prop), namespace).fact

  //A=0 | B = 0 <-> A*B=0
  //A=0 & B = 0 <-> A^2+B^2=0
  private lazy val orEqz = remember("F_()=0 | G_() =0 <-> F_()*G_()=0".asFormula, QE, namespace).fact
  private lazy val andEqz = remember("F_()=0 & G_() =0 <-> F_()^2 + G_()^2 =0".asFormula, QE, namespace).fact

  private lazy val divEq = remember("!(G_()=0) -> F_()/G_() = 0 -> F_() = 0".asFormula, QE, namespace).fact
  private lazy val divNeq = remember("!(G_()=0) -> (F_()/G_() != 0) -> F_() != 0".asFormula, QE, namespace).fact //Derivable from the above

  //Only the B ones are necessary, but the others help avoid extra terms
  private lazy val addDiv = (
    remember("F_()/G_() + A_()/B_() = (F_()*B_()+A_()*G_())/(G_()*B_())".asFormula, QE, namespace).fact,
    remember("F_()/G_() + A_() = (F_()+A_()*G_())/G_()".asFormula, QE, namespace).fact,
    remember("F_() + A_()/B_() = (F_()*B_()+A_())/B_()".asFormula, QE, namespace).fact)

  private lazy val mulDiv = (
    remember("(F_()/G_()) * (A_()/B_()) = (F_()*A_())/(G_()*B_())".asFormula, QE, namespace).fact,
    remember("(F_()/G_()) * A_() = (F_()*A_())/G_()".asFormula, QE, namespace).fact,
    remember("F_() * (A_()/B_()) = (F_()*A_())/B_()".asFormula, QE, namespace).fact)

  private lazy val subDiv = (
    remember("F_()/G_() - A_()/B_() = (F_()*B_()-A_()*G_())/(G_()*B_())".asFormula, QE, namespace).fact,
    remember("F_()/G_() - A_() = (F_()-A_()*G_())/G_()".asFormula, QE, namespace).fact,
    remember("F_() - A_()/B_() = (F_()*B_()-A_())/B_()".asFormula, QE, namespace).fact)

  private lazy val divDiv = (
    remember("(F_()/G_()) / (A_()/B_()) = (F_()*B_())/(A_()*G_())".asFormula, QE, namespace).fact,
    remember("(F_()/G_()) / A_() = (F_()/(G_()*A_()))".asFormula, QE, namespace).fact,
    remember("F_()/(A_()/B_()) = (F_()*B_())/A_()".asFormula, QE, namespace).fact)

  private lazy val negDiv = remember("-(F_()/G_()) = (-F_())/G_()".asFormula, QE, namespace).fact
  // This next one is only provable for concrete instances of K_(), probably have to do it on the fly
  // val powDivB = remember("(F_()/G_())^K_() = F_()^K_()/G_()^K_()".asFormula, QE, namespace).fact)


  //Assumes that the terms are Variables or nullary Functions
  // Default: x < y, x < x(), y < x()
  // Invalid inputs lead to transitive failure: a+b = x = c+d = x()
  object VarOrd extends Ordering[Term] {
    def compare(x: Term, y: Term): Int =
      (x,y) match {
        //todo: remove the prettyString and properly check things like wit_1 wit_0
        case (vx:Variable,vy:Variable) => vx.prettyString.compare(vy.prettyString)
        case (FuncOf(fx,Nothing),vy:Variable) => 1
        case (vx:Variable,FuncOf(fy,Nothing)) => -1
        case (FuncOf(fx,Nothing),FuncOf(fy,Nothing)) => fx.name.compare(fy.name)
        case _ => 0
      }
  }

  def isVar(s:Term) : Boolean = {
    s match {
      case _:Variable | FuncOf(_,Nothing) => true
      case _ => false
    }
  }

  //Sanity check that a term representing a monomial satisfies the monomial normalisation requirement
  //Additional check: the terms in "variable" position are actual variables
  //The nested variables i.e. those in l must be lexicographically smaller so (a^5)*b^3 is valid, (b^3)*a^5 is invalid
  def checkMono(t:Term,maxs:Option[Term] = None): Boolean = {
    logger.debug(s"Checking $t, $maxs")
    t match {
      case n:Number => n.value == 1
      case Times(l,Power(s,n:Number)) if isVar(s) =>
        n.value.isValidInt && n.value.toInt > 0 &&
        maxs.forall(t=>VarOrd.compare(s,t) < 0 ) && checkMono(l,Some(s))
      case _ => false
    }
  }

  //Monomial order (of a normalized monomial)
  def ordMono(t:Term) : Integer = {
    //assert(checkMono(t))
    t match {
      case Times(l,Power(_,n:Number)) => n.value.toInt + ordMono(l)
      case _ => 0
    }
  }

  object MonOrd extends Ordering[Term] {
    //Reverse lexicographic order for monomials of the same degree
    private def lexMono(l:Term,r:Term) : Int = {
      (l,r) match {
        case (n: Number, m: Number) => 0 //Impossible for normalized monomials
        case (Times(l, Power(vl, nl: Number)), Times(r, Power(vr, nr: Number))) =>
          val cmp = VarOrd.compare(vl,vr)
          if (cmp == 0) {
            if (nl.value < nr.value) -1
            else if (nl.value == nr.value) lexMono(l, r)
            else 1
          }
          else cmp
        case _ => ???
      }
    }

    def compare(l: Term, r: Term): Int = {
      val ol = ordMono(l)
      val or = ordMono(r)
      logger.debug(s"monos: $l, $r, $ol, $or")
      if (ol < or) -1
      else if(ol > or) 1
      else lexMono(l,r)
    }
  }

  def gcd(a: BigDecimal,b: BigDecimal):  BigDecimal = {
    if(b ==0) a else gcd(b, a%b)
  }

  def checkCoeff(t:Term) : Boolean = {
    t match {
      case Divide(numer:Number,denom:Number) =>
        numer.value != 0 && denom.value > 0 && gcd(numer.value,denom.value).abs==1
      case _ => false
    }
  }

  //Sanity check that a term representing a polynomial satisfies the normalisation requirement
  def checkPoly(t:Term,maxm:Option[Term] = None): Boolean = {
    logger.debug(s"Checking $t, $maxm")
    t match {
      case n:Number => n.value == 0
      case Plus(l,Times(c,m)) =>
        checkCoeff(c) && checkMono(m) &&
          (maxm match {
          case None => checkPoly(l,Some(m))
          case Some(n) => {
            MonOrd.compare(m,n) < 0 && checkPoly(l,Some(m))
          }
          })
      case _ => false
    }
  }

  //This seems like it might be a bad idea ...
  private def getProver(skip_proofs:Boolean) :(Formula,BelleExpr)=>ProvableSig =
    if (skip_proofs) ( (f:Formula,b:BelleExpr) => Ax.equivReflexive.provable ) else proveBy

  def addCoeff(cl:Term,cr:Term) : (Term,Boolean) = {
    (cl,cr) match {
      case(Divide(lnum:Number,lden:Number),Divide(rnum:Number,rden:Number)) =>
        val num = lnum.value*rden.value + rnum.value * lden.value
        val den = lden.value * rden.value
        val normalizer = gcd(num,den).abs
        (Divide(Number(num/normalizer),Number(den/normalizer)),num==0)
      case _ => ???
    }
  }

  //Takes and returns normalised polynomials
  //The returned provable is just reflexivity if no proof is required
  def addPoly(l:Term,r:Term,skip_proofs:Boolean = false): (Term,ProvableSig) = {
    val lhs = Plus(l,r)
    val prover = getProver(skip_proofs)
    val res: (Term, ProvableSig) = (l,r) match {
      case (n:Number,_) => //Left unit for addition
        (r,prover(Equal(lhs,r), byUS(Ax.zeroPlus)))
      case (_,n:Number) => //Right unit for addition
        (l,prover(Equal(lhs,l), byUS(Ax.plusZero)))
      case (Plus(nl,Times(cl,ml)),Plus(nr,Times(cr,mr))) => {
        val cmp = MonOrd.compare(ml,mr)
        if(cmp < 0) {
          val (rec,pr) = addPoly(l,nr,skip_proofs)
          val res = Plus(rec,Times(cr,mr))
          (res,prover(Equal(lhs,res), useAt(plusAssoc1)(SuccPosition(1,0::Nil))
            & useAt(pr)(SuccPosition(1,0::0::Nil)) & byUS(Ax.equalReflexive)))
        }
        else if (cmp == 0) {
          val (rec,pr) = addPoly(nl,nr,skip_proofs)
          val (cnew,isZero) = addCoeff(cl,cr)
          if (isZero) //Canceling out the 0
            (rec, prover(Equal(lhs,rec), useAt(plusAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(plusCoeff1,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & TactixLibrary.RCF))
          else {
            val res = Plus(rec,Times(cnew,ml))
            (res, prover(Equal(lhs,res), useAt(plusAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(plusCoeff2,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          }
        }
        else {
          val (rec,pr) = addPoly(r,l,skip_proofs)
          //Flip the +
          (rec,if (skip_proofs) Ax.equivReflexive.provable else useFor(Ax.plusCommute)(SuccPosition(1,0::Nil))(pr))
        }
      }
      case _ => ???
    }
    res
  }

  //Multiplies and returns normalised monomials (this is basically the same as the implementation for adding polynomials)
  def mulMono(l:Term,r:Term,skip_proofs:Boolean = false): (Term,ProvableSig) = {
    val lhs = Times(l,r)
    val prover = getProver(skip_proofs)
    (l,r) match {
      case(n:Number,_) => (r,prover(Equal(lhs,r),byUS(onetimes)))  //Unit
      case (_,n:Number) => (l,prover(Equal(lhs,l),byUS(timesone))) //Unit
      case (Times(nl,Power(sl,ml:Number)),Times(nr,Power(sr,mr:Number))) =>
        val cmp = VarOrd.compare(sl,sr)
        if(cmp < 0)
        {
          val(rec,pr) = mulMono(l,nr,skip_proofs)
          val res = Times(rec,Power(sr,mr:Number))
          (res,prover(Equal(lhs,res), useAt(timesAssoc1)(SuccPosition(1,0::Nil))
            & useAt(pr)(SuccPosition(1,0::0::Nil)) & byUS(Ax.equalReflexive)))
        }
        else if(cmp == 0) {
          val(rec,pr) = mulMono(nl,nr,skip_proofs)
          val mnew = ml.value + mr.value
          if(mnew == 0) //Canceling out the 0
            (rec, prover(Equal(lhs,rec), useAt(timesAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(timesCoeff1,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          else {
            val res = Times(rec,Power(sl,Number(ml.value+mr.value)))
            (res, prover(Equal(lhs,res), useAt(timesAssoc2)(SuccPosition(1,0::Nil))
              & useAt(pr)(SuccPosition(1,0::0::Nil))
              & useAt(timesCoeff2,PosInExpr(1::Nil))(1)
              //Only for coefficient calculation
              & RCF))
          }
        }
        else {
          val (rec,pr) = mulMono(r,l,skip_proofs)
          //Flip the *
          (rec,if (skip_proofs) Ax.equivReflexive.provable else useFor(Ax.timesCommute)(SuccPosition(1,0::Nil))(pr))
        }
      case _ => ???
    }
  }

  def mulCoeff(cl:Term,cr:Term) : Term = {
    (cl,cr) match {
      case(Divide(lnum:Number,lden:Number),Divide(rnum:Number,rden:Number)) =>
        val num = lnum.value * rnum.value
        val den = lden.value * rden.value
        val normalizer = gcd(num,den).abs
        Divide(Number(num/normalizer),Number(den/normalizer))
      case _ =>
        ???
    }
  }

  //Multiplies a normalized polynomial (l) by a constant (c) and a normalized monomial (r)
  def mulPolyMono(l:Term,c:Term,r:Term,skip_proofs:Boolean = false): (Term,ProvableSig) = {
    logger.debug(s"mul poly, const, mono $l, $c, $r")
    val lhs = Times(l,Times(c,r))
    val prover = getProver(skip_proofs)
    l match {
      case n:Number => (n,prover(Equal(lhs,n),byUS(Ax.zeroTimes))) // Multiplication by 0 poly
      case Plus(nl,Times(cl,ml)) =>
        val (rec1,pr1) = mulPolyMono(nl,c,r,skip_proofs)
        val (rec2,pr2) = mulMono(ml,r,skip_proofs)
        val res =  Plus(rec1,Times(mulCoeff(cl,c),rec2) )

        (res,prover(Equal(lhs,res),useAt(timesAssoc3)(SuccPosition(1,0::Nil))
          & useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::1::Nil))
          & useAt(plusCoeff2,PosInExpr(1::Nil))(1)
          //Should only be simple arithmetic at this step
          & RCF))

      case _ => ???
    }
  }

  //Multiplies and returns normalised polynomials
  def mulPoly(l:Term,r:Term,skip_proofs:Boolean = false): (Term,ProvableSig) = {
    val lhs = Times(l,r)
    val prover = getProver(skip_proofs)
    r match {
      case n:Number => (n,prover(Equal(lhs,n),byUS(Ax.timesZero))) //Multiplication by 0 poly
      case Plus(nr,Times(cr,mr)) =>
        val (rec1,pr1) = mulPoly(l,nr,skip_proofs)
        val (rec2,pr2) = mulPolyMono(l,cr,mr,skip_proofs)
        val (res,pr3) = addPoly(rec1,rec2,skip_proofs)
        (res,prover(Equal(lhs,res),useAt(Ax.distributive)(SuccPosition(1,0::Nil))
          & useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)
        ))

      case _ => ???
    }
  }

  //Reduces t^n to iterated squares
  def iterSquare(l:Term,p:Int,skip_proofs:Boolean = false) : (Term,ProvableSig) = {
    val lhs = Power(l,Number(p))
    val prover = getProver(skip_proofs)
    if (p == 0) (Number(1),prover(Equal(lhs,Number(1)),byUS(powLem1)))
    else if (p == 1) (l,prover(Equal(lhs,l),byUS(powLem2)))
    else if (p % 2 == 0)
    {
      val (rec,pr) = iterSquare(l,p/2,skip_proofs)
      val rhs = Power(rec,Number(2))
      (rhs,prover(Equal(lhs,rhs),
        useAt(pr,PosInExpr(1::Nil))(SuccPosition(1,1::0::Nil)) &
        useAt(powLem3)(SuccPosition(1,1::Nil)) &
        useAt(powLem5,PosInExpr(1::Nil))(1) & RCF))
    }
    else
    {
      val (rec,pr) = iterSquare(l,p/2,skip_proofs)
      val rhs = Times(Power(rec,Number(2)),l)
      (rhs,prover(Equal(lhs,rhs),
        useAt(pr,PosInExpr(1::Nil))(SuccPosition(1,1::0::0::Nil)) &
        useAt(powLem4)(SuccPosition(1,1::Nil)) &
        useAt(powLem5,PosInExpr(1::Nil))(1) & RCF))
    }
  }

  def divCoeff(cl:Term,cr:Term) : Term = {
    (cl,cr) match {
      case(Divide(lnum:Number,lden:Number),Divide(rnum:Number,rden:Number)) =>
        val num = lnum.value * rden.value
        val den = lden.value * rnum.value
        val normalizer = gcd(num,den).abs
        Divide(Number(num/normalizer),Number(den/normalizer))
      case _ =>
        ???
    }
  }

  def ratToNum(t:Term) : Option[Number] = {
    t match{
      case Divide(n:Number,d:Number) if d.value == 1 => Some(n)
      case _ => None
    }
  }

  // Try to turn a ground term into an equivalent normalized rational (A/B)
  // Proves the equivalence using RCF
  // The proof gets generated afterwards using RCF
  def groundNormalise(t:Term) : Option[Term] = {
    t match{
      case (n:Number) => Some(Divide(n,Number(1)))
      case Power(l,r) => {
        val ln = groundNormalise(l)
        val rn = groundNormalise(r).flatMap(ratToNum)
        (ln, rn) match {
          case (Some(Divide(n: Number, d: Number)), Some(p: Number)) =>
            Some(Divide(Number(n.value.pow(p.value.intValue)), Number(d.value.pow(p.value.intValue))))
          case _ => None
        }
      }
      case bop:BinaryCompositeTerm =>
        (groundNormalise(bop.left),groundNormalise(bop.right)) match {
          case (Some(l),Some(r)) =>
            bop match{
              case Plus(_,_) => Some(addCoeff(l,r)._1)
              case Minus(_,_) => Some(addCoeff(l,mulCoeff(Divide(Number(-1),Number(1)),r))._1)
              case Times(_,_) => Some(mulCoeff(l,r))
              case Divide(_,_) => Some(divCoeff(l,r))
              case _ => None
            }
          case _=> None
        }
      case Neg(u) =>
        groundNormalise(u).map( t => mulCoeff(Divide(Number(-1),Number(1)),t))
      case _ => None
    }
  }

  def groundNormaliseProof(t:Term,toNum:Boolean=false) : Option[(Term,ProvableSig)] = {
    val gt = groundNormalise(t)
    (if(toNum) gt.flatMap(ratToNum) else gt) match{
      case Some(tt) =>
        val pr = ProvableSig.startPlainProof(Equal(t,tt))(opt(RCF), 0)
        if (pr.isProved) Some(tt,pr) else None
      case _ => None
    }
  }

  def isMono(t:Term): Boolean = {
    t match {
      case Times(l,r) =>
        isMono(l) && isMono(r)
      case Power(l,r:Number) =>
        isMono(l) && r.value.isValidInt
      case v:Variable => isVar(v)
      case _ => false
    }
  }

  //Optimized normalisation for a monomial
  //Assume the input term is of the shape x^n * y ^ m * ...
  //i.e. it is a monomial but not necessarily normalised
//  def normaliseMonomial(m:Term,skip_proofs:Boolean = false) : (Term,ProvableSig) = {
//    val prover = getProver(skip_proofs)
//    val res = m match {
//      case Times(lm,rm) =>
//        val (ln,lpr) = normaliseMonomial(lm)
//        val (rn,rpr) = normaliseMonomial(rm)
//        val (res,pr) = mulMono(ln,rn,skip_proofs)
//        (res,prover(Equal(m,res),QE)) //temporary
//      case Power(_:Variable,_:Number) =>
//        val res = Times(Number(1),m)
//        (res,prover(Equal(m,res),QE)) //temporary
//      case Power(p,n:Number) if n.value.intValue == 2 =>
//        val (res1,pr1) = normaliseMonomial(p)
//        val (res2,pr2) = mulMono(res1,res1,skip_proofs)
//        (res2,prover(Equal(m,res2),QE)) //temporary
//      case _:Variable =>
//        val res = Times(Number(1),Power(m,Number(1)))
//        (res,prover(Equal(m,res),QE)) //temporary
//      case _ => ???
//    }
//    res
//  }


  //Normalizes an otherwise un-normalized term
  def normalise(l:Term,skip_proofs:Boolean = false) : (Term,ProvableSig) = {

    logger.debug(s"Normalizing at $l")
    val prover = getProver(skip_proofs)

//    if(isMono(l)){
//      val (mon,pr) = normaliseMonomial(l,skip_proofs)
//      //0 + 1 * (1 * v^n)
//      val res = Plus(Number(0),Times(Divide(Number(1),Number(1)), mon) )
//      return (res,prover(Equal(l,res), useAt(pr)(SuccPosition(1,0::Nil)) & byUS(var2Normalise)))
//    }
    val res = l match {
      case n:Number =>
        //0 + 1 * n (unless n = 0)
        val res = if (n.value == 0) n else Plus(Number(0), Times(Divide(n,Number(1)),Number(1)))
        (res,prover(Equal(l,res), RCF ))
      case v if isVar(v) =>
        //0 + 1/1 * (1 * v^1)
        val pow1 = Power(v,Number(1))
        val res = Plus(Number(0),Times(Divide(Number(1),Number(1)), Times(Number(1),pow1) ))
        (res,prover(Equal(l,res), byUS(var1Normalise) ))
      case Plus(ln,rn) =>
        val (rec1,pr1) = normalise(ln,skip_proofs)
        val (rec2,pr2) = normalise(rn,skip_proofs)
        val (res,pr3) = addPoly(rec1,rec2,skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)))
      case Times(ln,rn) =>
        val (rec1,pr1) = normalise(ln,skip_proofs)
        val (rec2,pr2) = normalise(rn,skip_proofs)
        val (res,pr3) = mulPoly(rec1,rec2,skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3)))
      case Power(_:Variable,_:Number) =>
        //0 + 1 * (1 * v^n)
        val res = Plus(Number(0),Times(Divide(Number(1),Number(1)), Times(Number(1),l) ))
        (res,prover(Equal(l,res),byUS(varNormalise)))
      case Power(ln,n:Number) if n.value == 2 =>
        val (rec1,pr1) = normalise(ln,skip_proofs)
        //Square the polynomial by hand
        val (res,pr2) = mulPoly(rec1,rec1,skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(powNormalise)(SuccPosition(1,0::Nil))
          & by(pr2)))
      case Power(ln,n:Number) if n.value.isValidInt =>
        val(rec1,pr1) = iterSquare(ln,n.value.intValue,skip_proofs)
        val(res,pr2) = normalise(rec1,skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::Nil))
          & by(pr2)))
      //If the power is not itself a number, try harder to make it a Number
      case Power(ln,e:Term) =>
        val pr = groundNormaliseProof(e,true)
        pr match {
          case None => ???  // Could not normalize the power
          case Some((n:Number,pr)) => {
            val (res,pr2) = normalise(Power(ln,n),skip_proofs)
            (res,prover(Equal(l,res), useAt(pr)(SuccPosition(1,0::1::Nil)) & by(pr2)))
          }
        }
      case Neg(ln) =>
        //Negation ~= multiply by -1 monomial
        val (rec1,pr1) = normalise(ln,skip_proofs)
        val (res,pr2) = mulPolyMono(rec1,Divide(Number(-1),Number(1)),Number(1),skip_proofs)
        (res,prover(Equal(l,res), useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(negNormalise)(SuccPosition(1,0::Nil)) & by(pr2) ))
      case Minus(ln,rn) =>
        //Minus ~= move - into negation
        val (rec1,pr1) = normalise(ln,skip_proofs)
        val (rec2,pr2) = normalise(Neg(rn),skip_proofs)
        val (res,pr3) = addPoly(rec1,rec2,skip_proofs)
        (res,prover(Equal(l,res), useAt(minusNormalise)(SuccPosition(1,0::Nil))
          & useAt(pr1)(SuccPosition(1,0::0::Nil))
          & useAt(pr2)(SuccPosition(1,0::1::Nil))
          & by(pr3) ))
      case Divide(num:Number,den:Number) =>
        val res = if (num.value == 0) num else Plus(Number(0), Times(l,Number(1)))
        (res,prover(Equal(l,res), RCF ))
      case Divide(ln,e:Term) =>
        //Simple hack: Try hard to convert a division to a number
        val propt = groundNormaliseProof(Divide(Number(1),e))
        propt match {
          case None =>
            ???  // Could not normalize
          case Some((n,pr)) => {
            val (res,pr2) = normalise(Times(n,ln),skip_proofs)
            (res,prover(Equal(l,res), useAt(divNormalise)(SuccPosition(1,0::Nil)) &
              useAt(pr)(SuccPosition(1,0::0::Nil)) &
              by(pr2)
            ))
          }
        }
      case _ => {
        ???
      }
    }
    res
  }

  lazy val normaliseAt:DependentPositionTactic = new DependentPositionTactic("normalise at"){
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        sequent.sub(pos) match
        {
          case Some(t:Term) =>
            val(tt,pr) = normalise(t,false)
            //println(tt,pr)
            CEat(useFor(Ax.equalCommute)(SuccPos(0))(pr))(pos)
          case _ => ident
        }
      }
    }
  }

  lazy val equalityByNormalisation = PolynomialArithV2.equate
  /*"equalityByNormalisation" by { (pos: Position, seq: Sequent) =>
      pos.checkTop
      pos.checkSucc
      seq.sub(pos) match {
        case Some(Equal(t1, t2)) =>
          normaliseAt(pos++PosInExpr(0::Nil)) &
            normaliseAt(pos++PosInExpr(1::Nil)) &
            cohideR(1) & byUS(Ax.equalReflexive)
        case Some(e) => throw new TacticInapplicableFailure("equalityByNormalisation only applicable to equalities, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
      }
    } */

  //Polynomial division: no proof needed, although the polynomials need to be pre-normalised
  //todo: Might this be implemented in terms of mulMono with -ve power? (probably not because ordering gets messed up)

  //Monomial division l/r : returns the normalised quotient monomial q s.t. q * r = l only if it is truly divisible
  def divMono(l:Term,r:Term): Option[Term] = {
    val lhs = Times(l,r)
    (l,r) match {
      case (_,n:Number) => Some(l) //Divide by 1
      case(n:Number,_) => None //Dividing 1 by something not 1
      case (Times(nl,Power(sl,ml:Number)),Times(nr,Power(sr,mr:Number))) =>
        val cmp = VarOrd.compare(sl,sr)
        if(cmp < 0) None
        else if(cmp == 0) {
          val mnew = ml.value - mr.value
          if (mnew < 0) None
          else
          divMono(nl, nr) match {
            case None => None
            case Some(q) =>
              Some (if (mnew == 0) q else Times(q, Power(sr, Number(mnew))))
          }
        }
        else {
          divMono(nl,r) match
          {
            case None => None
            case Some(q) => Some(Times(q,Power(sl,ml)))
          }
        }
      case _ => ???
    }
  }

  //Polynomial division on head monomials (no proofs)

  //Find the first non-zero monomial in l that r divides if it exists & returns the quotient along with its coefficient
  def divPolyMono(l:Term,r:Term) : Option[(Term,Term)] = {
    l match {
      case n: Number => None //We want non-zero monomials only
      case Plus(nl, Times(cl, ml)) =>
        divMono(ml, r) match {
          case None => divPolyMono(nl, r)
          case Some(q) => Some(cl, q)
        }
    }
  }

  def negDivCoeff(cl:Term,cr:Term) : Term = {
    (cl,cr) match {
      case(Divide(lnum:Number,lden:Number),Divide(rnum:Number,rden:Number)) =>
        val num = lnum.value * rden.value
        val den = lden.value * rnum.value
        val normalizer = gcd(num,den).abs
        //Manually flips the sign
        if(den < 0) Divide(Number(num/normalizer),Number(-den/normalizer))
        else
          Divide(Number(-num/normalizer),Number(den/normalizer))
      case _ =>
        ???
    }
  }

  //Returns the divisor and quotient (if one exists)
  def divPoly(l:Term,r:Term): Option[(Term,Term)] = {
    r match {
      case n:Number => None //Division by 0
      case Plus(nr,Times(cr,mr)) =>
        divPolyMono(l,mr) match {
          case None => None //No monomial in l divisible by r
          case Some((c,q)) => //The monomial c*(q*mr) was in l
            //The actual coefficient we need to return for the reduction:
            val divisor = Times(negDivCoeff(c,cr),q)
            //For division, we need to use the normalized version internally
            val quotient = addPoly(l, mulPolyMono(r, negDivCoeff(c,cr), q,true)._1,true)._1
            Some(divisor,quotient)
        }
    }
  }

  //Don't know how to do this in Scala neatly
  def firstDivisor(l:List[Term],i:Int,r:Term) : Option[(Int,Term,Term)] ={
    l match {
      case Nil => None
      case (x::xs) =>
        divPoly(r,x) match {
          case None => firstDivisor(xs,i+1,r)
          case Some((d,q)) => Some(i,d,q)
        }
    }
  }

  //Repeated division of normalized things
  //Returns the sequence of reduction steps, each a pair of the index and divisor of the dividing polynomial
  def reduction(l:List[Term],r:Term): List[(Int,Term)] ={
    firstDivisor(l,0,r) match {
      case None => Nil
      case Some((i,d,q)) =>
        (i,d)::reduction(l,q)
    }
  }

  /***
    *   Updated procedure using g<>0 |- g^2 + SOS > 0 (previously, g = 1 was just a special case)
    */

  // Input: list of pairs a_i, p_i
  // Proves sum_i (a_i * p_i ^2) >= 0
  // Each a_i should be a positive (rational) coefficient (proved by RCF)
  def sosGeZero(l:List[(Term,Term)]) : (Term,ProvableSig) =
  {
    l match {
      case Nil => (Number(0),zeroGeZero)
      case ((a,s)::xs) =>
        val (rec,pr) = sosGeZero(xs) //foo >= 0
        val res = Plus(rec,Times(a,Power(s,Number(2))))
          (res,proveBy(GreaterEqual(res,Number(0)), // (foo) + x^2 >0
            useAt(plusGeMono,PosInExpr(1::Nil))(1) & andR(1) <( by(pr),
              useAt(timesPos,PosInExpr(1::Nil))(1) & andR(1) <( RCF, byUS(Ax.nonnegativeSquares) ) )))
    }
  }

  // Given a goal of the form a_i = 0 , b_j != 0 |-
  // Proves that some provided combination of the b_j is > 0
  // The input combination is zero-indexed, so the first !=0 position is computed
  def neqGtZero(l:List[Int],sequent:Sequent) : (Term,BelleExpr) =
  {
    val antes = sequent.ante
    val ineqPos = antes.indexWhere(_ match {case NotEqual(_,_) => true case _ => false})
    //The actual polynomial we want
    val ineqP = l.foldRight(Number(1):Term)( (e,n)=>
      {
        val poly = antes(ineqPos+e) match {
          case NotEqual(p,_) => p
          case _ => ???
        }
        Times(Power(poly,Number(2)),n)
      })
    val tac =
      l.foldRight(cohideR(1) & by(Ax.oneGreaterZero):BelleExpr)((e, n)=>
      {
        useAt(neGtSquared,PosInExpr(1::Nil))(1) & andR(1) <( id, n)
      })
    (ineqP,cut(Greater(ineqP,Number(0))) <( ident,tac))
  }

  // Generate a proof for |- g>0 -> g + a_1 * s_1^2 + ... + a_n * s_n^2 > 0)
  // Each a_i should be a positive (rational) coefficient (proved by RCF)
  def genWitness(gtz:Term,l:List[(Term,Term)]) : (Term,ProvableSig) =
  {
    val (sos,geZ) = sosGeZero(l)
    val trm = Plus(gtz,sos)

    (trm,
      proveBy(Imply(Greater(gtz,Number(0)),Greater(trm,Number(0))),
        implyR(1) & useAt(plusGtMono,PosInExpr(1::Nil))(1) & andR(1) <(id, cohideR(1) & by(geZ) )))

  }

  //Goal must be of the form (Fi=0, Gj!=0 |- )
  def genWitnessTac(mon:List[Int], witness:List[(Term,Term)], instopt:Option[List[(Int,Term)]] = None) : DependentTactic = anon ((sequent: Sequent) => {
    val (gtZ, tac) = neqGtZero(mon,sequent)

    //Assert the witness provided
    val (wit, pfi) = genWitness(gtZ,witness)
    val pf = useFor(gtNotZero, PosInExpr(0 :: Nil))(SuccPosition(1,1::Nil))(pfi)
    //assert(pf.isProved)
    //Generate our own reduction instructions if not available
    //Proofs skipped
    val inst = instopt.getOrElse({
      val ante_polys = sequent.ante.flatMap(_ match {
        case Equal(t, n: Number) if n.value == 0 => Some(t)
        case _ => None
      }).toList
      val wit_norm = normalise(wit, true)._1
      val ctx_norm = ante_polys.map(t => normalise(t, true)._1)
      reduction(ctx_norm, wit_norm)
    })

    //g >0 -> g+s_i^2 != 0
    cut(pf.conclusion.succ.head) < (
      implyL(Symbol("Llast")) < (tac & id,ident)&
      notL(Symbol("Llast")) &
        //Run the instructions
        inst.foldRight[BelleExpr](ident)(
          (h, tac) =>
            implyRi(keep = true)(AntePos(h._1), SuccPos(0))
              & useAt(axMov, PosInExpr(1 :: Nil), (us: Option[Subst]) => us.get ++ RenUSubst(("g_()".asTerm, h._2) :: Nil))(1)
              & tac) &
        equalityByNormalisation(1)
      ,
      cohideR(1) & by(pf)
      )
  })

  /**
    * End updated procedure
    */
}
