/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, Position}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import Augmentors._

/** Invariant generators and differential invariant generators.
  * @author Andre Platzer
  * @see [[TactixLibrary.invGenerator]]
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
  lazy val differentialInvariantGenerator: Generator[Formula] = (sequent,pos) =>
    //@todo performance: ++ is not quite as fast a lazy concatenation as it could be.
    TactixLibrary.invGenerator(sequent,pos) ++ relevanceFilter(differentialInvariantCandidates)(sequent,pos)

  /** A loop invariant generator.
    * @author Andre Platzer */
  lazy val loopInvariantGenerator: Generator[Formula] = (sequent,pos) =>
    //@todo performance: ++ is not quite as fast a lazy concatenation as it could be.
    TactixLibrary.invGenerator(sequent,pos) ++ relevanceFilter(loopInvariantCandidates)(sequent,pos)


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

}

