package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._
import scala.collection.mutable.ListBuffer
import scala.language.postfixOps

/**
  * Differential Saturation (Fig 6.3, Logical Analysis of Hybrid Systems)
  * Considers a sequent of the form Gamma |- [ODE & Q]p
  * All of Gamma, Q and p are assumed to be FOL_R only
  * Does NOT construct proofs along the way
 */

object DifferentialSaturation {

  //Check if the evolution domain already implies the post condition using QE
  def checkProved(domain:Formula, post:Formula) : Boolean = {
    val pr = TactixLibrary.proveBy(Imply(domain,post),TactixLibrary.QE)
    pr.isProved
  }

  //Generate a polynomial parametric candidates up to degree deg
  private def freshConstName = "a_"

  //Generates all the parametric terms for vars up to degree deg
  def parametricCandAux(vars:List[Variable],deg:Int) : List[Term] = {
    vars match {
      case Nil => List(Number(1))
      case (v::vs) =>
        val ls = List.range(0,deg).foldLeft(List[Term]()) ((t,i)=>{
          val cands = parametricCandAux(vs,deg-i)
          if(i == 0)
            cands
          else
            cands.map( c => Times(Power(v,Number(i)),c )) ++ t
        })
        ls
    }
  }

  def freshConst(ind:Int) : Variable = {
    Variable(freshConstName,Some(ind))
  }

  //The actual parametric polynomial
  //Also returns the generated parametric constants
  def parametricCand(vars:List[Variable],deg:Int,freshInd:Int) : (Term,List[Variable],Int) = {
    val ts = parametricCandAux(vars,deg)
    ts.foldRight(Number(0):Term,List[Variable](),freshInd) ( (t,s) => {
      val c = freshConst(s._3)
      (Plus(Times(c, t), s._1),c :: s._2, s._3 + 1)
    }
    )
  }

  // Computes and simplifies the lie derivative
  // Firstly, it turns all remaining differentials into 0, then it simplifies and strips out things like x^0 = 1
  // The simplifier can't do the last simplification without proof (since 0^0 is nasty)
  def stripConstants(t:Term) : Term = {
    t match {
      case v:DifferentialSymbol => Number(0)
      case bop:BinaryCompositeTerm => bop.reapply(stripConstants(bop.left),stripConstants(bop.right))
      case uop:UnaryCompositeTerm => uop.reapply(stripConstants(uop.child))
      case _ => t
    }
  }

  def stripPowZero(t:Term) : Term = {
    t match {
      case Power(v,n:Number) if n.value.isValidInt && n.value.intValue()== 0 => Number(1)
      case bop:BinaryCompositeTerm => bop.reapply(stripPowZero(bop.left),stripPowZero(bop.right))
      case uop:UnaryCompositeTerm => uop.reapply(stripPowZero(uop.child))
      case _ => t
    }
  }

  def simplifiedLieDerivative(p:DifferentialProgram,t:Term) : Term = {
    val ld = stripConstants(lieDerivative(p,t))
    val ts1 = termSimp(ld,emptyCtx,defaultTaxs)._1
    val ts2 = termSimp(stripPowZero(ts1),emptyCtx,defaultTaxs)._1
    ts2
  }

  //Closes formula under the differential program
  def diffClosure (p:DifferentialProgram,f:Formula) : Formula = {
    val diffVars = StaticSemantics.freeVars(f).intersect(StaticSemantics.boundVars(p))
    diffVars.toSet.toList.foldLeft(f) ( (qf,v) => Forall(Seq(v),qf))
    //Direct vector quantifier: Forall(diffVars.toSet.toList,f)
  }

  def extractEquations(fml:Formula,instVars: List[Variable]) : Option[Map[Variable,Term]] = {
    fml match {
      case Equal(l:Variable,r) =>
        if (instVars.contains(l)) Some(Map(l -> r))
        else None
      case And(l,r) => {
        //Might lead to contradictory substitutions
        val lm = extractEquations(l, instVars)
        val rm = extractEquations(r, instVars)
        (lm,rm) match {
          case (Some(lm),Some(rm)) => Some(lm ++ rm)
          case _ => None
        }
      }
      case Or(l,r) =>
        val lm = extractEquations(l,instVars)
        lm match {
          case Some(lv) => lm
          case None => {
            extractEquations(r,instVars)
          }
        }
      case _ => {
        println(fml)
        None
      }
    }
  }

  // This is just a hack to deal with repeated substitution
  def repeatedSubst(e:Expression,subst:Map[Variable,Term],limit:Int = 100) : Option[Expression] = {
    val e2 = subst.foldLeft(e)( (f,s) =>
      SubstitutionHelper.replaceFree(f)(s._1,s._2))
    if (e==e2)
      Some(e2)
    else if (limit == 0) None
    else
      repeatedSubst(e2,subst,limit-1)
  }

  //Generate parametric differential invariants
  //Given a formula, compute its partial QE and guess a partial substitution
  def guessInstantiation(fml:Formula, instVars : List[Variable]) : Option[Map[Variable,Term]] = {
    val pr1 = proveBy(fml,partialQE)
    if (pr1.isProved)
      return Some(Map())
    val conc = pr1.subgoals(0).succ(0)
    val eqnsopt = extractEquations(conc,instVars)
    if (eqnsopt.isEmpty)
      return None

    val eqns = eqnsopt.get

    val fml2 = repeatedSubst(fml,eqns)
    if (fml2.isEmpty)
      return None
    val pr = proveBy(fml2.get.asInstanceOf[Formula],partialQE)
    println(pr)
    if(pr.isProved)
      Some(eqns)
    else
      None
  }

  //Attempts to guess a parametric equational differential invariant for ode&dom
  //candSet = variables to consider in the parametric invariant
  //insts = parameters that can be instantiated
  //fresh = next index for fresh parameter
  //deg = degree of the parametric candidate

  def parametricInvariant(ode:DifferentialProgram, dom:Formula, candSet: List[Variable], insts : List[Variable],
                          fresh:Int, deg : Int)  : Option[(Term,Map[Variable,Term],List[Variable],Int)]  = {
    val (candidate,genvars,nextfresh) = parametricCand(candSet,deg,fresh)
    val trm = simplifiedLieDerivative(ode,candidate)
    val instvars = genvars ++ insts
    val invCand = Equal(trm,Number(0))
    val fml = diffClosure(ode,Imply(dom,invCand))
    println("Formula:"+fml)
    val substopt = guessInstantiation(fml,instvars)
    if (substopt.isEmpty) {
      println("Failed")
      return None
    }
    val subst = substopt.get
    val candSubst = repeatedSubst(candidate,subst)
    val invTrm = termSimp(candSubst.get.asInstanceOf[Term],emptyCtx,defaultTaxs)._1
    // Check that the candidate isn't already implied by the evolution domain
    // and that it at least mentions part of the ODE
    if(StaticSemantics.freeVars(invTrm).intersect(StaticSemantics.boundVars(ode)).isEmpty)
      None
    else{
      val pr = proveBy(Imply(dom,Equal(invTrm,Number(0))),QE)
      if (pr.isProved) None
      else Some(invTrm,subst,instvars,nextfresh)
    }

  }

  //Generate increasingly complex candidates
  def parametricInvariants(ode:DifferentialProgram,dom:Formula, candSets: List[List[Variable]], degLimit : Int) : Unit = {
    var insts = List[Variable]()
    var fresh = 0
    var invs = ListBuffer[(Term,Map[Variable,Term])]()
    var domain = dom
    for (cs <- candSets) {
      for (deg <- List.range(1,degLimit)) {
        parametricInvariant(ode,domain,cs,insts,fresh,deg) match {
          case None => ()
          case Some((t,s,iv,nf)) =>
            insts = iv
            fresh = nf
            //todo: deal with this properly
            //domain = And(domain,Equal(t,Number(0)))
            invs+=((t,s))
        }
      }
    }
    println(invs.toList)

  }

}
