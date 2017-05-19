package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleThrowable, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tools._
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

  def pQE(f:Formula) : Formula = {
    val qe = ToolProvider.qeTool().getOrElse(throw new BelleThrowable("partialQE requires a QETool, but got None"))
    qe.qeEvidence(f)._1
  }

  def simpWithTool(tool: Option[SimplificationTool],t:Term) : Term = {
    tool match {
      case None => termSimp(t,emptyCtx,defaultTaxs)._1
      case Some(tl) => tl.simplify(t,List())
    }
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
      case v:DifferentialSymbol => {
        Number(0)
      }
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

  def simplifiedLieDerivative(p:DifferentialProgram,t:Term, tool: Option[SimplificationTool]) : Term = {
    val ld = stripConstants(lieDerivative(p,t))
    val ts1 = simpWithTool(tool,ld)
    val ts2 = simpWithTool(tool,stripPowZero(ts1))
    ts2
  }

  //Closes formula under the differential program
  def diffClosure (f:Formula,p:DifferentialProgram) : Formula = {
    val diffVars = StaticSemantics.freeVars(f).intersect(StaticSemantics.boundVars(p))
    diffVars.toSet.toList.foldLeft(f) ( (qf,v) => Forall(Seq(v),qf))
    //Direct vector quantifier: Forall(diffVars.toSet.toList,f)
  }

  //Closes formula except for variables that can be instantiated
  def instClosure (f:Formula, instVars: List[Variable]) : Formula = {
    val vars = StaticSemantics.freeVars(f).toSet.toList.diff(instVars)
    vars.foldLeft(f) ( (qf,v) => Forall(Seq(v),qf))
    //Direct vector quantifier: Forall(diffVars.toSet.toList,f)
  }

  // Given a formula, returns a list of potential substitutions to instVars to make
  // that formula true (not accurate for comparisons)
  def extractEquations(fml:Formula,instVars: List[Variable]) : List[Map[Variable,Term]] = {
    fml match {
      case False => List()
      case bop:ComparisonFormula if bop.left.isInstanceOf[Variable] =>
        //Avoid generating invs with singular RHS
        if (instVars.contains(bop.left) && FormulaTools.singularities(bop.right).isEmpty){
          bop match {
            //First one is legit, the rest are horrible hacks to find instantiations when pQE gives ineqs instead of =
            case Equal(l:Variable,r) => List(Map(l->r))
            case GreaterEqual(l:Variable,r:Number) if r.value.intValue() == 0 => List(Map(l -> Plus(r,Number(1))))
            case Greater(l:Variable,r:Number) if r.value.intValue() == 0  => List(Map(l -> Plus(r,Number(1))))
            case LessEqual(l:Variable,r:Number)  if r.value.intValue() == 0 => List(Map(l -> Minus(r,Number(1))))
            case Less(l:Variable,r:Number)  if r.value.intValue() == 0 => List(Map(l -> Minus(r,Number(1))))
            case _ => List(Map())
          }
        }
        else {
          List(Map())
        }
      case And(l,r) => {
        //Might lead to contradictory substitutions
        val lm = extractEquations(l, instVars)
        val rm = extractEquations(r, instVars)
        //Any combination of the two maps
        lm.flatMap(x => rm.map(y => x++y))
      }
      case Or(l,r) => {
        val lm = extractEquations(l, instVars)
        val rm = extractEquations(r, instVars)
        lm ++ rm
      }
      case _ => {
        // todo: does mathematica ever return other formula shapes?
        // this just ignores all other shapes
        List(Map())
      }
    }
  }

  // This is just to deal with looping substitution
  def repeatedSubst(e:Expression,subst:Map[Variable,Term],limit:Int = 100) : Option[Expression] = {
    val e2 = subst.foldLeft(e)( (f,s) =>
      SubstitutionHelper.replaceFree(f)(s._1,s._2))
    if (e==e2)
      Some(e2)
    else if (limit == 0) None
    else
      repeatedSubst(e2,subst,limit-1)
  }

  def occamify(subs : List[Map[Variable,Term]],instVars:List[Variable]) : List[Map[Variable,Term]] = {
    subs.map( s =>
      s++instVars.diff(s.keySet.toList).map( v => (v,Number(1))).toMap
    )
  }

  //Generate parametric differential invariants
  //Given a formula, compute its partial QE and guess partial substitutions from the PQE
  //For each guessed substitution, double check that it really works
  //The substitution is only allowed to instantiate variables in instVars
  def guessInstantiations(fml:Formula, instVars : List[Variable]) : List[Map[Variable,Term]] = {
    //todo: should not be using PQE here, the generated decomposition is heavily dependent on the variable order
    val pr = proveBy(fml,partialQE)
    if(pr.isProved)
      return List(Map())

    val conc = pr.subgoals(0).succ(0)
    //val conc = pQE(fml)

    val subs = extractEquations(conc,instVars)
    //val subs = occamify(subs,instVars)
    //Occam-ify the substitutions: set all unconstrained variables to 1
    //Filter out the substitutions that don't work
    subs.filter( s => {
      val fml2 = repeatedSubst(fml, s)
      if(fml2.isEmpty) false
      else {
        proveBy(fml2.get.asInstanceOf[Formula], QE).isProved
      }
    }
    )
  }

  //Attempts to guess a parametric differential invariant for ode&dom
  //candSet = variables to consider in the parametric invariant
  //insts = parameters that can be instantiated
  //fresh = next index for fresh parameter
  //deg = degree of the parametric candidate

  def parametricInvariant(ode:DifferentialProgram, domls:List[Formula], candSet: List[Variable], insts : List[Variable],
                          fresh:Int, deg : Int, tool: Option[SimplificationTool], ineq : Boolean) : Option[(Term,Map[Variable,Term],List[Variable],Int)]  = {
    val (candidate,genvars,nextfresh) = parametricCand(candSet,deg,fresh)
    val trm = simplifiedLieDerivative(ode,candidate,tool)
    val instvars = genvars ++ insts
    val invCandPre = if (ineq) GreaterEqual(trm,Number(0)) else Equal(trm,Number(0))

    //If a simplifier is available, and the formula is non-trivial, pre-simplify it
    val invCand =
    if(!StaticSemantics.freeVars(invCandPre).isEmpty && tool.isDefined) {
      tool.get.simplify(invCandPre, domls)
    }
    else invCandPre
    //val dom = domls.foldLeft(True:Formula)( (f,p) => And(f,p))

    //val fml = diffClosure(Imply(dom,invCand),ode)
    val fml = diffClosure(invCand,ode) //todo: disabled saturation

    //println("Candidate",candidate,dom)
    //println("closure of derivative",fml)
    //val fml = instClosure(Imply(dom,invCand),instvars)
    //println("Formula:"+fml)
    val substeqns = guessInstantiations(fml,instvars)

    //Find the first substitution that results in a non-trivial invariant term
    //where non-trivial means not already implied by the evolution domain
    val substpre = substeqns.iterator.map( s => {
      val candSubst = repeatedSubst(candidate,s)
      if(candSubst.isEmpty) None
      else {
        val invTrm = simpWithTool(tool,candSubst.get.asInstanceOf[Term])
        val fvs = StaticSemantics.freeVars(invTrm)
        // Check that it at least mentions part of the ODE
        if(fvs.intersect(StaticSemantics.boundVars(ode)).isEmpty) None
        // and that the candidate isn't already implied by the evolution domain
        else {
          val invCandSubst = if (ineq) GreaterEqual(invTrm,Number(0)) else Equal(invTrm,Number(0))
          if (domls.exists( f => UnificationMatch.unifiable(f,invCandSubst).isDefined)) None
          //else if(proveBy(Imply(dom,invCandSubst),QE).isProved) None
          else Some(invTrm,s)
        }
      }
    })

    val subst = substpre.find(_.isDefined)

    if(subst.isEmpty)
      return None

    val eqns = subst.get.get
    //todo: maybe return a list of all the (distinct) parametric invariants that work instead of just the first?
    //this makes it trickier for later invariants to instantiate earlier ones though
    //todo: eqns._2 should be reduced to only instantiating earlier fresh variables
    Some(eqns._1,eqns._2,instvars,nextfresh)

  }

  //Generate increasingly complex candidates
  def parametricInvariants(ode:DifferentialProgram,dom:List[Formula], candSets: List[List[Variable]],
                           degLimit : Int, withIneq :Boolean = false,tool: Option[SimplificationTool] = None)
                            : (List[(Term,Map[Variable,Term])],List[(Term,Map[Variable,Term])]) = {
    var insts = List[Variable]()
    var fresh = 0
    var eqinvs = ListBuffer[(Term,Map[Variable,Term])]()
    var ineqinvs = ListBuffer[(Term,Map[Variable,Term])]()
    var domain = dom.to[ListBuffer]
    for (cs <- candSets) {
      println("Parametric invariants for",cs)
      for (deg <- List.range(1,degLimit)) {
        println("Degree",deg)

        //Try for equational invariant first
        val eqinv = parametricInvariant(ode,domain.toList,cs,insts,fresh,deg,tool,false) match {
          case None => false
          case Some((t,s,iv,nf)) =>
            insts = iv
            fresh = nf
            println("Found = invariant",t)
            //This unfortunately seems to make PQE do badly...
            domain += Equal(t,Number(0))
            eqinvs+=((t,s))
            true
        }

        //If we found an equational invariant, don't bother with the inequality version (by DDC)
        if(withIneq && !eqinv) {
          //Then try for a >= invariant
          parametricInvariant(ode, domain.toList, cs, insts, fresh, deg, tool, true) match {
            case None => ()
            case Some((t, s, iv, nf)) =>
              insts = iv
              fresh = nf
              println("Found >= invariant", t)
              //This unfortunately seems to make PQE do badly...
              domain += GreaterEqual(t, Number(0))
              ineqinvs += ((t, s))
          }
        }
      }
    }
    (eqinvs.toList,ineqinvs.toList)
  }

}
