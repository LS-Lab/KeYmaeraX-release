package edu.cmu.cs.ls.keymaerax.btactics

import java.util

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._
import scala.language.postfixOps

/**
  * Dependency Analysis
  * For a set of output variables, determine the set of input variables across a hybrid program that
  * could affect their values
 */

object DependencyAnalysis {

  //Same as freeVars except it throws out differential symbols
  def freeVarsTerm(t:Term) : Set[BaseVariable] = {
    StaticSemantics.freeVars(t).toSet.collect(PartialFunction[Variable,BaseVariable]{
      case bv:BaseVariable => bv
    })
  }

  def freeVarsFml(f:Formula) : Set[BaseVariable] = {
    StaticSemantics.freeVars(f).toSet.collect(PartialFunction[Variable,BaseVariable]{
      case bv:BaseVariable => bv
    })
  }

  def dependencies(p:Program,s:HashSet[BaseVariable]) : HashSet[BaseVariable] ={
    p match {
      case Assign(v:BaseVariable,t) =>
        if(s.contains(v)) s.union(freeVarsTerm(t))
        else s
      case AssignAny(v:BaseVariable) =>
        s - v
      case Test(f) =>
        s.union(freeVarsFml(f))
      case Choice(p1,p2) =>
        dependencies(p1,s).union(dependencies(p2,s))
      case Compose(p1,p2) =>
        dependencies(p1,dependencies(p2,s))
      case p:ODESystem => analyseODE(p,s)
      case Loop(l) =>
        val inn = dependencies(l,s)
        if(inn.subsetOf(s)) s //Nothing to add
        else dependencies(p,s.union(inn)) //More to add
      case _ => ???
    }

  }

  //Turns a differential program into vectorial form
  def collapseODE(p:DifferentialProgram) : Map[BaseVariable,Term] = {
    p match {
      case AtomicODE(DifferentialSymbol(v:BaseVariable), e) => HashMap((v,e))
      case DifferentialProduct(p1,p2) =>
        val dp1 = collapseODE(p1)
        val dp2 = collapseODE(p2)
        //Assume that the keys are unique
        dp1 ++ dp2
      case _ => HashMap[BaseVariable,Term]()
    }
  }

  //Returns an estimate of the maximum degree of a given variable
  //This is accurate only when it reports degree either 0 or 1, which is what we need for linearity
  def degVar(t:Term,v:BaseVariable) : Int = {
    t match {
      case n:Number => 0
      case x:Variable =>
        if(x.equals(v)) 1
        else 0
      case Neg(t) => degVar(t,v)
      case Times(l,r) => degVar(l,v) * degVar(r,v)
      case Power(l,n:Number) => degVar(l,v) * n.value.toInt
      case Divide(l,r) =>
        val dr = degVar(r,v)
        if(dr != 0) -1 //Fails on stupid cases like 1 / (1/x)
        else degVar(l,v) //Denominator doesn't contain v
      case Plus(l,r) =>
        Math.max(degVar(l,v),degVar(r,v))
      case Minus(l,r) =>
        Math.max(degVar(l,v),degVar(r,v))
      case _ => print(t)
        ??? //Unimplemented: Pair, AppOf, Differential, Power that is not an integer
    }
  }

  // The ODE is linear if all the variables on the RHS occur with
  def isLinearODE(vs:Map[BaseVariable,Term]) : Boolean = {
    val vars = vs.keySet
    vars.forall(v =>
      vs.values.forall( t =>
      {
        val dv = degVar(t,v)
        dv == 0 || dv ==1
      }))
  }

  def transitiveAnalysis(vs:Map[BaseVariable,Set[BaseVariable]],s:HashSet[BaseVariable]) : HashSet[BaseVariable] = {
    val newvars =
    s.map(v => vs.get(v) match{
      case None => Set[BaseVariable]()
      case Some(vs) => vs -- s
    } ).foldLeft(Set[BaseVariable]())((s,t) => s.union(t))
    if(newvars.isEmpty)
      return s
    else
      return transitiveAnalysis(vs,s.union(newvars))
  }

  //Dependency Analysis for ODEs
  def analyseODE(p:ODESystem,s:HashSet[BaseVariable]) : HashSet[BaseVariable] = {
    val ode = p.ode
    val dom = p.constraint
    //Converts the ODE to a list of AtomicODEs
    val odels = collapseODE(ode)
    //If the ODE is linear, apply the transitive analysis
    if(isLinearODE(odels)){
      //println("Linear ODE")
      val ds = odels.mapValues( v => freeVarsTerm(v) )
      transitiveAnalysis(ds,s)
    }
    else {
     //println("Non-linear ODE")
     if(s.intersect(odels.keySet).isEmpty)
       s
     else
       (odels.values.map(t => freeVarsTerm(t))).foldLeft(s.union(odels.keySet))( (s,t) => s.union(t))
    }
  }

}
