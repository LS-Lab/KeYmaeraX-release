package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._
import scala.language.postfixOps

/**
  * Dependency Analysis
  * For a set of output variables, determine the set of input variables across a hybrid program that
  * could affect their values
 */

object DependencyAnalysis {

  def varSetToBaseVarSet (s:Set[Variable]) : Set[BaseVariable] = {
    s.flatMap( (v:Variable) =>
      v match {
        case bv:BaseVariable => Some(bv)
        case _ => None
      }
    )
  }
  //Same as freeVars except it throws out differential symbols
  def freeVars(t:Expression) : Set[BaseVariable] = {
    varSetToBaseVarSet(StaticSemantics.freeVars(t).toSet)
  }

  def freeVars(s:Sequent) : Set[BaseVariable] = {
    (s.succ.map( f => freeVars(f)) ++ s.ante.map(f=>freeVars(f))).flatten.toSet
  }

  //Same as signature except it throws out everything except Function symbols
  def signature(t:Expression) : Set[Function] = {
    StaticSemantics.signature(t).flatMap( (e:Expression) =>
      e match {
        case bv:Function => Some(bv)
        case _ => None
    })
  }

  def dependencies(p:Program,s:Set[BaseVariable],ignoreTest:Boolean = false) : (Set[BaseVariable],Set[Function]) ={
    p match {
      case Assign(v:BaseVariable,t) =>
        if(s.contains(v))
          ((s - v).union(freeVars(t)),signature(t))
        else (s,Set.empty)
      case AssignAny(v:BaseVariable) =>
        (s - v,Set.empty)
      case Test(f) =>
        if(ignoreTest) (s,Set.empty)
        else (s.union(freeVars(f)),signature(f))
      case Choice(p1,p2) =>
        val (d1,f1) = dependencies(p1,s,ignoreTest)
        val (d2,f2) = dependencies(p2,s,ignoreTest)
        (d1.union(d2),f1.union(f2))
      case Compose(p1,p2) =>
        val (d2,f2) = dependencies(p2,s,ignoreTest)
        val (d1,f1) = dependencies(p1,d2,ignoreTest)
        (d1,f1.union(f2))
      case p:ODESystem => analyseODE(p,s,ignoreTest)
      case Loop(l) =>
        val (inn,funcs) = dependencies(l,s,ignoreTest)
        if(inn.subsetOf(s)) (s,funcs) //Nothing to add
        else {
          val (d, f) = dependencies(p, s.union(inn),ignoreTest) //More to add
          (d, f.union(funcs))
        }
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

  //Returns an estimate of the maximum degree w.r.t. a set of variables
  //This is accurate only when it reports degree either 0 or 1, which is what we need for linearity
  def degVar(t:Term,vs:Set[BaseVariable]) : Int = {
    t match {
      case n:Number => 0
      case x:BaseVariable =>
        if(vs.contains(x)) 1
        else 0
      case Neg(t) => degVar(t,vs)
      case Times(l,r) => degVar(l,vs) + degVar(r,vs)
      case Power(l,n:Number) if n.value.isValidInt => degVar(l,vs) * n.value.toInt
      case Divide(l,r) =>
        val dr = degVar(r,vs)
        if(dr != 0) -1 //Fails on stupid cases like 1 / (1/x)
        else degVar(l,vs) //Denominator doesn't contain vs
      case Plus(l,r) =>
        Math.max(degVar(l,vs),degVar(r,vs))
      case Minus(l,r) =>
        Math.max(degVar(l,vs),degVar(r,vs))
      case FuncOf(_,Nothing) =>
        0
      case FuncOf(_,t) =>
        if(degVar(t,vs)!=0)
          -1
        else
          0
      case Pair(l,r) =>
        Math.max(degVar(l,vs),degVar(r,vs))
      case _ => print(t)
        ??? //Unimplemented: Differential, Power that is not a number
    }
  }

  // The ODE is linear if all the variables on the RHS occur linearly
  def isLinearODE(vs:Map[BaseVariable,Term]) : Boolean = {
    //val vars = vs.keySet
    //println(vars)
    vs.values.forall( t =>
    {
      val dv = degVar(t,vs.keySet)
      dv == 0 || dv ==1
    })
  }

  def transitiveAnalysis(vs:Map[BaseVariable,(Set[BaseVariable],Set[Function])],s:Set[BaseVariable],f:Set[Function]) : (Set[BaseVariable],Set[Function]) = {
    val newvars =
    s.map(v => vs.get(v) match{
      case None => (Set[BaseVariable](),Set[Function]())
      case Some((vars,fs)) => (vars -- s,fs)
    } ).foldLeft(Set[BaseVariable](),Set[Function]())((s,t) => (s._1.union(t._1),s._2.union(t._2)))
    if(newvars._1.isEmpty) {
      return (s, f.union(newvars._2))
    }
    else
      return transitiveAnalysis(vs,s.union(newvars._1),f.union(newvars._2))
  }

  //Dependency Analysis for ODEs
  def analyseODE(p:ODESystem,s:Set[BaseVariable],ignoreTest:Boolean) : (Set[BaseVariable],Set[Function]) = {
    val ode = p.ode
    val dom = p.constraint
    val (fvdom:Set[BaseVariable]) = if (ignoreTest) Set.empty else freeVars(dom)
    val (fvsig:Set[Function]) = if (ignoreTest) Set.empty else signature(dom)
    //Converts the ODE to a list of AtomicODEs
    val odels = collapseODE(ode)

    //Special case: the set of variables that we are concerned with is not mentioned at all in the ODE
    if (s.intersect(odels.keySet).isEmpty) {
      return (s.union(fvdom),fvsig)
    }

    //Otherwise, transitively close over the set
    val ds = odels.mapValues( v => (freeVars(v),signature(v)) )

    //Compute the transitive closure T
    val (vars,funcs) = transitiveAnalysis(ds,s.union(fvdom),fvsig)

    //println("T analysis",vars,funcs)

    //Check that the remainder of the ODE is linear
    if (isLinearODE(odels -- vars)) {
      (vars, funcs)
    }
    //Otherwise, give up and return the whole ODE
    else {
       val odedom = odels.values.map(t => freeVars(t)).foldLeft(s.union(odels.keySet))((s, t) => s.union(t))
       val odesig = odels.values.map(t => signature(t)).foldLeft(Set[Function]())((s, t) => s.union(t))
       (odedom.union(fvdom), odesig.union(fvsig))
    }
  }

  def analyseModalVars(p:Program,ls:Set[BaseVariable],ignoreTest:Boolean = false) : Map[BaseVariable,(Set[BaseVariable],Set[Function])]= {
    ls.map(v => (v,dependencies(p,Set(v),ignoreTest))).toMap
  }

  //Given a sequent, find the dependencies of all its variables w.r.t. a modal program
  def analyseModal(p:Program,s:Sequent,ignoreTest:Boolean = false) : Map[BaseVariable,(Set[BaseVariable],Set[Function])]= {
    val vars = (s.succ.map( f => freeVars(f)) ++ s.ante.map(f=>freeVars(f))).flatten.toSet
    analyseModalVars(p,vars,ignoreTest)
  }

  // Naive DFS starting from a variable
  // Returns a set of newly visited variables and a visit order
  def dfs_aux(v:BaseVariable, adjlist: Map[BaseVariable,Set[BaseVariable]], done:Set[BaseVariable]) : (List[BaseVariable],Set[BaseVariable]) = {
    //println("DFS: ",v,done)

    //Already visited or visiting
    if(done.contains(v))
      (List(),done)

    else if(adjlist.contains(v)){
      val ls = adjlist(v).foldLeft((List[BaseVariable](),done+v))((l,vv) => {
        //println(v,l,vv)
        val (ls, vis) = dfs_aux(vv, adjlist, l._2)
        (ls ++ l._1, vis)
      }
      )
      (v::ls._1,ls._2)
    }
    else {
      (List(v),done+v)
    }
  }

  def dfs(adjlist: Map[BaseVariable,Set[BaseVariable]]) : List[BaseVariable] = {

    adjlist.keySet.foldLeft(List[BaseVariable](),Set[BaseVariable]())((l,v) => {
      if(l._2.contains(v)) l
      else {
        val (ls,vis) = dfs_aux(v,adjlist,l._2)
        (ls++l._1,vis)
      }
    }
    )._1
  }

  //Could be done faster, but the problems aren't that big
  def transClose(adjlist: Map[BaseVariable,Set[BaseVariable]]) : Map[BaseVariable,Set[BaseVariable]] = {
    adjlist.keySet.map( v => {
      (v,dfs_aux(v,adjlist,Set[BaseVariable]())._2)
    }).toMap
  }

  def transpose(adjlist:Map[BaseVariable,Set[BaseVariable]]) : Map[BaseVariable,Set[BaseVariable]] = {
    adjlist.values.flatten.map( k => (k,
      adjlist.keys.filter(v => adjlist(v).contains(k)).toSet)).toMap
  }

  //Find the SCCs of a graph defined on the BaseVariables
  def scc(adjlist: Map[BaseVariable,Set[BaseVariable]]) : List[Set[BaseVariable]] = {
    val stack = dfs(adjlist)
    val trans = transpose(adjlist)
    stack.foldLeft((List[Set[BaseVariable]](),Set[BaseVariable]()))( (d,v) => {

      if(d._2.contains(v)){
        d
      }
      else {
        val (ls, vis) = dfs_aux(v, trans, d._2)
        (ls.toSet::d._1,vis)
      }
    })._1
  }

  def stripImp(f:Formula) : Option[Program] = {
    f match {
      case Imply(l,r) => stripImp(r)
      case Box(a,f) => Some(a)
      case _ => None
    }
  }

  // Returns the program in [A]P, but only if the sequent is in the appropriate shape
  // e.g. Gamma ==> R_1 -> R_2 -> ... -> [A]P
  def stripSeq(s:Sequent) : Option[Program] = {
    if (s.succ.length==1)
      stripImp(s.succ(0))
    else
      None
  }

  def inducedOrd(edges: Map[BaseVariable,Set[BaseVariable]]) : Ordering[Variable] = new Ordering[Variable]{

    def compare(x:Variable,y:Variable): Int = {
      (x,y) match{
        case(x:BaseVariable,y:BaseVariable) => {
          if(!edges.contains(x) || !edges.contains(y)) return 0 //Not in the PO graph
          val b1 = edges(x).contains(y)
          val b2 = edges(y).contains(x)
          if(b1 == b2) 0 // Same eq class
          else
          if(b2) -1 else 1
        }
        case _ => 0
      }
    }
  }
}
