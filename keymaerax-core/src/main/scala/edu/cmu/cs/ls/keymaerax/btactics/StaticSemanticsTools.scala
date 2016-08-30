/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics._
import edu.cmu.cs.ls.keymaerax.core.SetLattice.bottom
import edu.cmu.cs.ls.keymaerax.core.{StaticSemantics, _}

import scala.collection.{immutable, mutable}
import scala.collection.immutable._
import PosInExpr.HereP

/**
 * Additional tools read off from the static semantics for the tactics.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.StaticSemantics]]
 */
object StaticSemanticsTools {

  /**
   * The set of variables that the top-level operator of this formula is binding itself,
   * so not those variables that are only bound because of operators in subformulas.
   */
  def bindingVars(formula: Formula): SetLattice[Variable] = formula match {
    // DotFormula is like a reserved Predicational
    case DotFormula => boundVars(DotFormula)
    case PredicationalOf(p, arg) => boundVars(formula)

    // quantifier binding cases omit bound vars from fv and add bound variables to bf
    case f: Quantified => SetLattice(f.vars) ensuring (r=> r==boundVars(Forall(f.vars,True)) && r==boundVars(Exists(f.vars,True)))

    // modality bounding cases omit must-bound vars from fv and add (may-)bound vars to bv
    case f: Modal => boundVars(f.program) ensuring (r=> r==boundVars(Box(f.program,True)) && r==boundVars(Diamond(f.program,True)))

    // special cases
    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(df) => boundVars(formula)

    //@note dangerous catch-all but not soundness-critical
    case _ => bottom

  }
  //@todo ensuring(r => !formula.isInstanceOf[BinaryCompositeFormula] || r==boundVars(formula.class.apply(True,True)), "same bound variables as replacing left,right with True)

  /**
   * The set of variables that the top-level operator of this program is binding itself,
   * so not those variables that are only bound because of operators in subprograms.
   */
  def bindingVars(program: Program): SetLattice[Variable] = program match {
    //@note It's the pieces of ODESystems that bind but the scope is the whole ODESystem, which is somewhat like an AtomicProgram
    case a: ODESystem     => boundVars(a)
    // base cases
    case a: AtomicProgram => boundVars(a)
    //@note acceptable but slightly dangerous catch-all but not soundness-critical
    case a: CompositeProgram => bottom
  }
  //@todo ensuring(r => !formula.isInstanceOf[BinaryCompositeFormula] || r==boundVars(formula.class.apply(True,True)), "same bound variables as replacing left,right with True)

  /**
   * The set of variables that, if they occurred at formula(pos) would be bound occurrences,
   * because there was an operator in formula on the path to pos for which it was binding.
   * If an occurrence of a variable at formula(pos) is not boundAt(formula,pos) then it is a free occurrence.
   * @see [[Context.at()]]
   */
  def boundAt(formula: Formula, pos: PosInExpr): SetLattice[Variable] = if (pos==HereP) bottom else formula match {
    case e:Quantified             if pos.head==0 => bindingVars(e) ++ boundAt(e.child, pos.child)
    case e:Modal                  if pos.head==0 => boundAt(e.program, pos.child)
    case e:Modal                  if pos.head==1 => bindingVars(e) ++ boundAt(e.child, pos.child)
    case e:UnaryCompositeFormula  if pos.head==0 => bindingVars(e) ++ boundAt(e.child, pos.child)
    case e:BinaryCompositeFormula if pos.head==0 => bindingVars(e) ++ boundAt(e.left,  pos.child)
    case e:BinaryCompositeFormula if pos.head==1 => bindingVars(e) ++ boundAt(e.right, pos.child)
    //@note predicationals will bind everything anyhow so no need to descend
    case e:PredicationalOf                       => bindingVars(e)
    //@note term children won't bind anything anyhow so no need to descend
    case e:AtomicFormula                         => bindingVars(e)
    case _ => throw new IllegalArgumentException("boundAt position " + pos + " of formula " + formula + " may not be defined")
  }

  /**
   * The set of variables that, if they occurred at program(pos) would be bound occurrences,
   * because there was an operator in program on the path to pos for which it was binding.
   * If an occurrence of a variable at program(pos) is not boundAt(program,pos) then it is a free occurrence.
   * @see [[Context.at()]]
   */
  def boundAt(program: Program, pos: PosInExpr): SetLattice[Variable] = if (pos==HereP) bottom else program match {
    //@note differential programs have global scope within the whole DifferentialProgram
    case dp:DifferentialProgram                  => bindingVars(dp)
    case e@ODESystem(ode, h)      if pos.head<=1 => bindingVars(e)
    case e:UnaryCompositeProgram  if pos.head==0 => bindingVars(e) ++ boundAt(e.child, pos.child)
    case e:BinaryCompositeProgram if pos.head==0 => bindingVars(e) ++ boundAt(e.left,  pos.child)
    case e:Compose                if pos.head==1 => bindingVars(e) ++ boundVars(e.left) ++ boundAt(e.right, pos.child)
    case e:BinaryCompositeProgram if pos.head==1 => bindingVars(e) ++ boundAt(e.right, pos.child)
    case e@Assign(x,t)            if pos.head==0 => bindingVars(e)
    case e@Assign(x,t)            if pos.head==1 => bottom
    case Test(f)                  if pos.head==0 => bottom
    //case e:DifferentialProduct    if pos.head==0 => boundAt(e.left,  pos.child)
    //case e:DifferentialProduct    if pos.head==1 => boundAt(e.right,  pos.child)
    //@todo the following would be suboptimal (except for AssignAny,Test,ProgramConst,DifferentialProgramConst)
    case e:AtomicProgram                         => bindingVars(e)
    case _ => throw new IllegalArgumentException("boundAt position " + pos + " of program " + program + " may not be defined")
  }


  /**
    * Compute all variable dependencies, i.e. the set of all variables that each variable depends on
    * by data flow dependencies.
    * @example {{{
    *           dependencies("a:=-b;{x'=v,v'=a,t'=1}".asProgram) == (a->{b}, x->{v}, v->{a}, t->{})
    *           dependencies("a:=-b+a;{x'=y,y'=-x,z'=x^2+y}".asProgram) == (a->{a,b}, x->{y}, y->{x}, z->{x,y})
    * }}}
    * @note so far only a simple data flow dependencies ignoring all control flow.
    * @note currently ignores some differential symbol dependencies.
    * @note ignores self-dependency from x'=1
    * @todo could respect control-flow dependencies too but might degenerate.
    */
  def dependencies(program: Program): immutable.Map[Variable,immutable.Set[Variable]] = convert(depend(program))
  def dependencies(ode: DifferentialProgram): immutable.Map[Variable,immutable.Set[Variable]] = convert(depend(ode))

  /**
    * Compute all transitive variable dependencies, i.e. the set of all variables that each variable depends on
    * directly or indirectly by data flow dependencies.
    * The order of the dependent variables will be by approximate topological sort, so variables after the ones they depend on themselves.
    * @example {{{
    *           dependencies("{x'=v,v'=a,a'=j,t'=1}".asProgram) == (x->{j,a,v}, v->{j,a}, a->{j}, t->{})
    *           dependencies("a:=-b;{x'=v,v'=a,t'=1}".asProgram) == (a->{b}, x->{a,v}, v->{a}, t->{})
    *           dependencies("a:=-b+a;{x'=y,y'=-x,z'=x^2+y}".asProgram) == (a->{a,b}, x->{x,y}, y->{y,x}, z->{x,y})
    * }}}
    * @note so far only a simple data flow dependencies ignoring all control flow.
    * @note currently ignores some differential symbol dependencies.
    * @note ignores self-dependency from x'=1
    * @todo could respect control-flow dependencies too but might degenerate.
    */
  def transitiveDependencies(program: Program): immutable.Map[Variable,immutable.List[Variable]] = transitivize(dependencies(program))
  def transitiveDependencies(ode: DifferentialProgram): immutable.Map[Variable,immutable.List[Variable]] = transitivize(dependencies(ode))

  /** Inverse of the dependency relation `deps` */
  def inverseDependencies(deps: immutable.Map[Variable,immutable.List[Variable]]): immutable.Map[Variable,immutable.List[Variable]] = {
    //deps.keysIterator.map(k => deps.iterator.foldLeft(List.empty[Variable])
    //((l, kvp) => if (kvp._2.contains(k)) l :+ kvp._1 else l))
    val foo: mutable.Map[Variable,mutable.ListBuffer[Variable]] = mutable.Map.empty
    deps.keySet.foreach(k => foo += k->mutable.ListBuffer.empty)
    deps.foreach(kvp => kvp._2.foreach(d => foo(d) += kvp._1))
    foo.map(p => p._1 -> p._2.toList).toMap
  }


  // implementation

  /** Form some sort of directed transitive closure to obtain an approximate topological sort on each.   */
  private def transitivize(dep: immutable.Map[Variable,immutable.Set[Variable]]): immutable.Map[Variable,immutable.List[Variable]] = {
    //@todo performance: bottom-up dynamic programming would make this a quicker single pass, walking in topologically sorted order without recursion
    //@todo breadth-first search also gives more precise answer than depth-first
//    def transitiveChase(proc: immutable.List[Variable], d: immutable.List[Variable]): immutable.List[Variable] =
//    if (proc.isEmpty)
//      d
//    else {
//      // prepends new transitive dependencies so that they get sorted in before stuff that caused those dependencies
//      val moreDeps = (proc.flatMap(y => dep.get(y) match {
//        case Some(set) => (set--d).toList ensuring(r => r.distinct==r && r.intersect(d).isEmpty)
//        case None => List.empty
//      }).distinct) ensuring(r => r.distinct==r && r.intersect(d).isEmpty)
//      moreDeps.flatMap(y => transitiveChase(moreDeps,moreDeps ++ d)).distinct ++ moreDeps ++ d
//    } ensuring(r => r.distinct==r && d.forall(y=>r.contains(y)), "transitivize(" + proc + ", " + d + ")")
    def transitiveChase(proc: immutable.List[Variable], d: immutable.List[Variable]): immutable.List[Variable] = {
      // prepends new transitive dependencies so that they get sorted in before stuff that caused those dependencies
      val moreDeps = (proc.flatMap(y => dep.get(y) match {
        case Some(set) => (set--d).toList ensuring(r => r.distinct==r && r.intersect(d).isEmpty)
        case None => List.empty
      }).distinct) ensuring(r => r.distinct==r && r.intersect(d).isEmpty)
      (d ++ moreDeps ++ moreDeps.flatMap(y => transitiveChase(moreDeps,moreDeps ++ d)).distinct).distinct
    } ensuring(r => r.distinct==r && d.forall(y=>r.contains(y)), "transitivize(" + proc + ", " + d + ")")
    dep.iterator.map(sp => sp._1->transitiveChase(sp._2.to, sp._2.to).reverse).toMap
  }


  private def depend(program: Program): mutable.Map[Variable,immutable.Set[Variable]] = program match {
    // can't know so just say empty even if that's wrong
    case a: ProgramConst   => mutable.Map.empty
    case Assign(x, e)      => mutable.Map(x->StaticSemantics.freeVars(e).symbols)
    case a: AssignAny      => mutable.Map.empty
      // empty only if ignoring control flow dependencies
    case Test(f)           => mutable.Map.empty
    case ODESystem(ode, h) => depend(ode)
    // homomorphic cases
    case Choice(a, b)      => merge(depend(a),depend(b))
    //@todo could improve when taking must-bounds into account and turning transitive
    case Compose(a, b)     => merge(depend(a),depend(b))
    case Loop(a)           => depend(a)
    case Dual(a)           => depend(a)
    case ode:DifferentialProgram => depend(ode)
  }

  private def depend(ode: DifferentialProgram): mutable.Map[Variable,immutable.Set[Variable]] = ode match {
      // simply ignores xp->e so far.
    case AtomicODE(xp: DifferentialSymbol, e) => mutable.Map(xp.x->StaticSemantics.freeVars(e).symbols)
    // can't know so just say empty even if that's wrong
    case c: DifferentialProgramConst => mutable.Map.empty
    // homomorphic cases
    case DifferentialProduct(a, b) => merge(depend(a),depend(b))
  }

  //@note performance optimize: mutable maps might make this faster
  private def merge[K,V](a: mutable.Map[K,immutable.Set[V]], b:mutable.Map[K,immutable.Set[V]]): mutable.Map[K,immutable.Set[V]] = {
    for ((k,v) <- b) {
      a.get(k) match {
        case Some(w) => a += k -> (v++w)
        case None => a += k -> v
      }
    }
    return a
  }

  private def convert(a: mutable.Map[Variable,immutable.Set[Variable]]): immutable.Map[Variable,immutable.Set[Variable]] =
    a.toMap
  // a.map(p => p._1 -> p._2.to[scala.collection.immutable.Set]).toMap
  // val foo: scala.collection.immutable.Map[Int, scala.collection.immutable.Set[String]] = a.map(p => p._1 -> p._2.toSet).toMap
}
