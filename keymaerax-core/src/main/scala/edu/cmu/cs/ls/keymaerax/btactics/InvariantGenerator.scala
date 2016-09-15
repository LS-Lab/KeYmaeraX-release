/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleError, BelleExpr, Position}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import Augmentors._

/** Invariant generators and differential invariant generators.
  * @author Andre Platzer
  * @see [[TactixLibrary.invGenerator]]
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-642-32347-8_3 A differential operator approach to equational differential invariants]]. In Lennart Beringer and Amy Felty, editors, Interactive Theorem Proving, International Conference, ITP 2012, August 13-15, Princeton, USA, Proceedings, volume 7406 of LNCS, pages 28-48. Springer, 2012.
  * @see Andre Platzer and Edmund M. Clarke. [[http://dx.doi.org/10.1007/s10703-009-0079-8 Computing differential invariants of hybrid systems as fixedpoints]]. Formal Methods in System Design, 35(1), pp. 98-120, 2009
  */
object InvariantGenerator {
  import Generator.Generator

  /** A relevance filtering tool for dependency-optimized invariant and differential invariant generation
    * based on the candidates from `generator`.
    * @author Andre Platzer */
  def relevanceFilter(generator: Generator[Formula]): Generator[Formula] = (sequent,pos) => {
    //@todo if frees depend on bound variables that are not mentioned in evolution domain constraint, then diffCut
    val (system, constraint, post) = sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, post)) => (ode.ode,ode.constraint,post)
      case Some(Box(system: Loop, post)) => (system,True,post)
      case Some(ow) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }
    val evos = if (constraint==True) Nil else DifferentialHelper.flattenAnds(List(constraint))
    new Iterator[Formula] {
      lazy val deps = StaticSemanticsTools.transitiveDependencies(system)
      lazy val bounds = StaticSemantics.boundVars(system).symbols
      lazy val frees = StaticSemantics.freeVars(post).symbols
      lazy val knowledge = StaticSemantics.freeVars(constraint).symbols
      // bound variables that free variables of the postcondition depend on but that are not yet free in the evolution domain constraint, so missing knowledge.
      // i.e. variables that the free variables of the postcondition depend on, that are also bound, but not yet free in the evolution domain constraint
      lazy val missing = frees.flatMap(x => deps.getOrElse(x,List.empty).intersect(bounds.to)).filter(x => !knowledge.contains(x))
      //@todo above of course even vars that are in the domain might need more knowledge, but todo that later and lazy
      lazy val candidates = generator(sequent,pos).toList.
        distinct.
        // new invariants only that aren't in the evolution domain constraint yet
        //@note it's never a good idea to diffCut the postcondition itself, because a direct proof then also succeeds
        filter(fml => fml!=post && !evos.contains(fml)).
        // filter out constants
        // filter(fml => !StaticSemantics.freeVars(fml).symbols.intersect(bounds).isEmpty)
        // candidates with knowledge about missing variables
        //@todo could check that a cut with this extra knowledge would actually prove invariant, but not sure if that pays off compared to just trying the proof.
        filter(fml => !StaticSemantics.freeVars(fml).symbols.intersect(missing).isEmpty).
        //@todo could check that it's not a tautology using RCF or check that it's not provable by DW
        //@todo postpone and try later candidates not covering all their dependencies (given the knowledge)
        //        filter(fml => {
        //          val fv=StaticSemantics.freeVars(fml).symbols
        //          !fv.flatMap(x=>deps.getOrElse(x,List.empty)).subsetOf(fv++knowledge)}).
        // sort by dependency order
        //@todo performance construction should probably have been the other way around to ensure primitive dependencies are tried first and avoding sorting by that order retroactively
        sortWith((a:Formula,b:Formula) =>
        //@todo improve sorting to take dependency order into account, not just number. If x depends on y then y is smaller.
        //@todo improve sorting to take dependency cluster into account, too.
        // smaller set of variables that it depends on means good idea to try first in dependency order, excluding self-dependencies
        StaticSemantics.freeVars(a).symbols.flatMap((x:Variable) => deps.getOrElse(x,List.empty).filter(y=>y!=x)).size <
          StaticSemantics.freeVars(b).symbols.flatMap((x:Variable) => deps.getOrElse(x,List.empty).filter(y=>y!=x)).size
      )
      lazy val iterareHumanumEst = {
        if (BelleExpr.DEBUG) println("dependencies:\t" + deps + "\nbounds:\t" + bounds.mkString(",") + "\nfrees:\t" + frees.mkString(",") + "\nknowledge:\t" + knowledge.mkString(",")  + "\nmissing:\t" + missing.mkString(","))
        if (BelleExpr.DEBUG) println("CANDIDATE: " + candidates)
        candidates.iterator
      }
      def hasNext: Boolean = iterareHumanumEst.hasNext
      def next(): Formula = iterareHumanumEst.next()
    }
  }

  /** A differential invariant generator.
    * @author Andre Platzer */
  lazy val differentialInvariantGenerator: Generator[Formula] = cached((sequent,pos) =>
    //@todo performance: ++ is not quite as fast a lazy concatenation as it could be.
    TactixLibrary.invGenerator(sequent,pos) ++ relevanceFilter(differentialInvariantCandidates)(sequent,pos)
  // ++ relevanceFilter(inverseCharacteristicDifferentialInvariantGenerator)(sequent,pos)
  )

  /** A more expensive extended differential invariant generator.
    * @author Andre Platzer */
  lazy val extendedDifferentialInvariantGenerator: Generator[Formula] = cached((sequent,pos) =>
    relevanceFilter(inverseCharacteristicDifferentialInvariantGenerator)(sequent,pos)
  )

  /** A loop invariant generator.
    * @author Andre Platzer */
  lazy val loopInvariantGenerator: Generator[Formula] = cached((sequent,pos) =>
    //@todo performance: ++ is not quite as fast a lazy concatenation as it could be.
    TactixLibrary.invGenerator(sequent,pos) ++ relevanceFilter(loopInvariantCandidates)(sequent,pos)
  )

  /** A simplistic differential invariant candidate generator.
    * @author Andre Platzer */
  lazy val differentialInvariantCandidates: Generator[Formula] = simpleInvariantCandidates

  /** A simplistic loop invariant candidate generator.
    * @author Andre Platzer */
  lazy val loopInvariantCandidates: Generator[Formula] = simpleInvariantCandidates


  /** A simplistic invariant and differential invariant candidate generator.
    * @author Andre Platzer */
  private val simpleInvariantCandidates: Generator[Formula] = (sequent,pos) =>
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, post)) => DifferentialHelper.flattenAnds(post +: sequent.ante.toList).iterator
      case Some(Box(loop: Loop, post))     => DifferentialHelper.flattenAnds(post +: sequent.ante.toList).iterator
      case Some(ow) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }

  /** Inverse Characteristic Method differential invariant generator.
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-642-32347-8_3 A differential operator approach to equational differential invariants]]. In Lennart Beringer and Amy Felty, editors, Interactive Theorem Proving, International Conference, ITP 2012, August 13-15, Princeton, USA, Proceedings, volume 7406 of LNCS, pages 28-48. Springer, 2012.
    */
  val inverseCharacteristicDifferentialInvariantGenerator: Generator[Formula] = (sequent,pos) => {
    import FormulaTools._
    if (!ToolProvider.algebraTool().isDefined) throw new BelleError("inverse characteristic method needs a computer algebra tool")
    if (!ToolProvider.pdeTool().isDefined) throw new BelleError("inverse characteristic method needs a PDE Solver")
    val (ode, constraint, post) = sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, post)) => (ode.ode,ode.constraint,post)
      case Some(ow) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }
    val evos = if (constraint==True) Nil else DifferentialHelper.flattenAnds(List(constraint))
    val solutions = try {
      ToolProvider.pdeTool().get.pdeSolve(ode)
    } catch {
      case e: Exception => if (BelleExpr.DEBUG) println("inverseCharacteristic generation unsuccessful: " + e)
        //e.printStackTrace()
        Nil.iterator
    }
    if (!solutions.hasNext) throw new BelleError("No solutions found that would construct invariants")
    val polynomials = atomicFormulas(negationNormalForm(post)).collect({
      case Equal(p,q)        => Minus(p,q)
      case GreaterEqual(p,q) => Minus(p,q)
      case LessEqual(p,q)    => Minus(q,p)
    }).distinct
    val algebra = ToolProvider.algebraTool().get
    val GB = algebra.groebnerBasis(polynomials)
    solutions.flatMap({case FuncOf(_, arg) => argumentList(arg)}).flatMap((inv:Term) => {
      val initial = algebra.polynomialReduce(inv, GB)
      //@todo could check that it's not a tautology using RCF
      List(Equal(inv,initial),GreaterEqual(inv,initial),LessEqual(inv,initial)).filter(cand => !evos.contains(cand))
    })
  }


  /** A cached invariant generator based on the candidates from `generator` that also remembers answers
    * to speed up computations.
    * @author Andre Platzer */
  def cached(generator: Generator[Formula]): Generator[Formula] = {
    var cache: scala.collection.mutable.Map[Box, List[Formula]] = new scala.collection.mutable.HashMap()
    (sequent,pos) => {
      val (box, system, constraint, post) = sequent.sub(pos) match {
        case Some(box@Box(ode: ODESystem, post)) => (box, ode.ode, ode.constraint, post)
        case Some(box@Box(system: Loop, post)) => (box, system, True, post)
        case Some(ow) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
        case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
      }
      cache.get(box) match {
        case Some(cached) => cached.iterator
        case None =>
          //@todo performance: this will eager-enumerate the full iterator for storage purposes. Could do lazy iteration by storing a lazy list, but that's more annoying.
          val remember = generator(sequent,pos).toList
          cache.put(box,remember)
          remember.iterator
      }
    }
  }
}
