/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleThrowable}
import Augmentors._
import org.apache.logging.log4j.scala.Logging

/** Invariant generators and differential invariant generators.
  * @author Andre Platzer
  * @see [[TactixLibrary.invGenerator]]
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-642-32347-8_3 A differential operator approach to equational differential invariants]]. In Lennart Beringer and Amy Felty, editors, Interactive Theorem Proving, International Conference, ITP 2012, August 13-15, Princeton, USA, Proceedings, volume 7406 of LNCS, pages 28-48. Springer, 2012.
  * @see Andre Platzer and Edmund M. Clarke. [[https://doi.org/10.1007/s10703-009-0079-8 Computing differential invariants of hybrid systems as fixedpoints]]. Formal Methods in System Design, 35(1), pp. 98-120, 2009
  */
object InvariantGenerator extends Logging {
  import Generator.Generator

  /** A proof hint on how to use an invariant. */
  abstract class ProofHint
  /** A tactic proof hint. */
  case class BelleExprProofHint(t: BelleExpr) extends ProofHint
  /** Proof hint from Pegasus */
  case class PegasusProofHint(isInvariant: Boolean, t: Option[String]) extends ProofHint
  /** Proof hint from annotation */
  case class AnnotationProofHint(tryHard: Boolean) extends ProofHint

  type GenProduct = (Formula, Option[ProofHint])

  /** A relevance filtering tool for dependency-optimized invariant and differential invariant generation
    * based on the candidates from `generator`.
    * @author Andre Platzer */
  def relevanceFilter(generator: Generator[GenProduct], analyzeMissing: Boolean): Generator[GenProduct] = (sequent,pos) => {
    //@todo if frees depend on bound variables that are not mentioned in evolution domain constraint, then diffCut
    val (system, constraint, post, allowPost) = sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, pf)) => (ode.ode,ode.constraint,pf,false)
      case Some(Box(system: Loop, pf)) => (system,True,pf,true)
      case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }
    lazy val evos = if (constraint==True) Nil else FormulaTools.conjuncts(constraint)
    lazy val deps = StaticSemanticsTools.transitiveDependencies(system)
    lazy val bounds = StaticSemantics.boundVars(system).symbols
    lazy val frees = StaticSemantics.freeVars(post).symbols
    lazy val knowledge = StaticSemantics.freeVars(constraint).symbols
    // bound variables that free variables of the postcondition depend on but that are not yet free in the evolution domain constraint, so missing knowledge.
    // i.e. variables that the free variables of the postcondition depend on, that are also bound, but not yet free in the evolution domain constraint
    def relevantInvVars(x: Variable) = system match {
      //@note ODEs can be proved with diffcut chains, but loops need single shot attempt
      case _: DifferentialProgram => deps.getOrElse(x,List.empty).intersect(bounds.to)
      case _: Loop => (x +: deps.getOrElse(x,List.empty)).intersect(bounds.to)
    }
    lazy val missing = if (analyzeMissing) frees.flatMap(relevantInvVars).diff(knowledge) else frees.flatMap(relevantInvVars)
    //@todo above of course even vars that are in the domain might need more knowledge, but todo that later and lazy
    generator(sequent,pos).
      distinct.
      // new invariants only that aren't in the evolution domain constraint yet
      //@note it's never a good idea to diffCut the postcondition itself, because a direct proof then also succeeds
      filter(prod => (allowPost || prod._1!=post) && !evos.contains(prod._1)).
      // filter out constants
      // filter(fml => !StaticSemantics.freeVars(fml).symbols.intersect(bounds).isEmpty)
      // candidates with knowledge about missing variables
      //@todo could check that a cut with this extra knowledge would actually prove invariant, but not sure if that pays off compared to just trying the proof.
      filter(prod => StaticSemantics.freeVars(prod._1).symbols.intersect(missing).nonEmpty)
      //@todo could check that it's not a tautology using RCF or check that it's not provable by DW
      //@todo postpone and try later candidates not covering all their dependencies (given the knowledge)
      //        filter(fml => {
      //          val fv=StaticSemantics.freeVars(fml).symbols
      //          !fv.flatMap(x=>deps.getOrElse(x,List.empty)).subsetOf(fv++knowledge)}).
  }

  /** A relevance filtering tool for dependency-optimized invariant and differential invariant generation
    * based on the candidates from `generator`.
    * @author Andre Platzer */
  def sortedRelevanceFilter(generator: Generator[GenProduct]): Generator[GenProduct] = (sequent,pos) => {
    //@todo if frees depend on bound variables that are not mentioned in evolution domain constraint, then diffCut
    val system = sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _)) => ode.ode
      case Some(Box(loop: Loop, _)) => loop
      case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }

    lazy val deps = StaticSemanticsTools.transitiveDependencies(system)

    def sizeCompare(a: Formula, b: Formula) = system match {
      case _: DifferentialProgram =>
        // smaller set of variables that it depends on means good idea to try first in dependency order, excluding self-dependencies
        StaticSemantics.freeVars(a).symbols.flatMap((x:Variable) => deps.getOrElse(x,List.empty).filter(_!=x)).size <
        StaticSemantics.freeVars(b).symbols.flatMap((x:Variable) => deps.getOrElse(x,List.empty).filter(_!=x)).size
      case _: Loop =>
        // try invariants with larger coverage of the loop's free variables first
        (StaticSemantics.freeVars(system).symbols -- StaticSemantics.freeVars(a).symbols).size <
        (StaticSemantics.freeVars(system).symbols -- StaticSemantics.freeVars(b).symbols).size
    }

    relevanceFilter(generator, analyzeMissing = true)(sequent, pos).
      // sort by dependency order
      //@todo performance construction should probably have been the other way around to ensure primitive dependencies are tried first and avoding sorting by that order retroactively
      sortWith((a: GenProduct, b: GenProduct) =>
        //@todo improve sorting to take dependency order into account, not just number. If x depends on y then y is smaller.
        //@todo improve sorting to take dependency cluster into account, too.
        if (a._1.isFOL == b._1.isFOL) sizeCompare(a._1, b._1)
        else a._1.isFOL //@note a.isFOL != b.isFOL, FOL are smaller than non-FOL formulas
      )
  }

  /** Default invariant generator used in Bellerophon tactics if no specific generator is requested. */
  lazy val defaultInvariantGenerator: Generator[GenProduct] = cached((sequent,pos) =>
    (loopInvariantGenerator(sequent,pos) #::: differentialInvariantGenerator(sequent,pos)).distinct)

  /** A differential invariant generator.
    * @author Andre Platzer */
  lazy val differentialInvariantGenerator: Generator[GenProduct] = cached((sequent,pos) =>
    (TactixLibrary.invGenerator(sequent,pos) #::: differentialInvariantCandidates(sequent,pos)).distinct
  // ++ relevanceFilter(inverseCharacteristicDifferentialInvariantGenerator)(sequent,pos)
  )

  /** A more expensive extended differential invariant generator.
    * @author Andre Platzer */
  lazy val extendedDifferentialInvariantGenerator: Generator[GenProduct] = cached((sequent,pos) =>
    sortedRelevanceFilter(inverseCharacteristicDifferentialInvariantGenerator)(sequent,pos).distinct
  )

  /** A loop invariant generator.
    * @author Andre Platzer */
  lazy val loopInvariantGenerator: Generator[GenProduct] = cached((sequent,pos) =>
    (TactixLibrary.invGenerator(sequent,pos) #::: sortedRelevanceFilter(loopInvariantCandidates)(sequent,pos)).distinct
  )

  /** A simplistic differential invariant candidate generator.
    * @author Andre Platzer */
  lazy val differentialInvariantCandidates: Generator[GenProduct] = cached((sequent,pos) =>
    //@note be careful to not evaluate entire stream by sorting etc.
    (sortedRelevanceFilter(simpleInvariantCandidates)(sequent,pos) #:::
      relevanceFilter(pegasusCandidates, analyzeMissing = false)(sequent,pos)).distinct)

  /** A simplistic loop invariant candidate generator.
    * @author Andre Platzer */
  lazy val loopInvariantCandidates: Generator[GenProduct] = simpleInvariantCandidates


  /** A simplistic invariant and differential invariant candidate generator.
    * @author Andre Platzer */
  lazy val simpleInvariantCandidates: Generator[GenProduct] = (sequent,pos) => {
    def combinedAssumptions(loop: Loop): Formula = {
      sequent.ante.toList.filter(fml => !StaticSemantics.freeVars(fml).intersect(StaticSemantics.boundVars(loop)).isEmpty).reduceOption(And).getOrElse(True)
    }
    sequent.sub(pos) match {
      case Some(Box(_: ODESystem, post)) => FormulaTools.conjuncts(post +: sequent.ante.toList).map(_ -> None).toStream.distinct
      case Some(Box(l: Loop, post))     => (FormulaTools.conjuncts(post +: sequent.ante.toList) :+ combinedAssumptions(l) :+ post).map(_ -> None).toStream.distinct
      case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }}

  /** Pegasus invariant generator (requires Mathematica). */
  lazy val pegasusInvariants: Generator[GenProduct] = pegasus(includeCandidates=false)
  lazy val pegasusCandidates: Generator[GenProduct] = pegasus(includeCandidates=true)
  def pegasus(includeCandidates: Boolean): Generator[GenProduct] = (sequent,pos) => sequent.sub(pos) match {
    case Some(Box(ode: ODESystem, post: Formula)) if post.isFOL =>
      def strictInequality(fml: Formula): Boolean = {
        FormulaTools.atomicFormulas(fml).exists({
          case _: Less => true
          case _: Greater => true
          case _: NotEqual => true
          case _ => false
        })
      }

      ToolProvider.invGenTool() match {
        case Some(tool) =>
          def proofHint(s: String): Option[String] = if (s != "Unknown") Some(s) else None
          lazy val pegasusInvs = tool.invgen(ode, sequent.ante, post)
          lazy val conjunctiveCandidates: Seq[Either[Seq[(Formula, String)], Seq[(Formula, String)]]] = pegasusInvs.withFilter({
            case Left(l) => l.length > 1 && l.map(_._1).exists(strictInequality)
            case Right(r) => r.length > 1 && r.map(_._1).exists(strictInequality)
          }).map({
            case Left(l) => Right((l.map(_._1).reduce(And), "Unknown") :: Nil)
            case Right(r) => Right((r.map(_._1).reduce(And), "Unknown") :: Nil)
          })
          lazy val invs: Seq[GenProduct] =
            if (includeCandidates) {
              (pegasusInvs ++ conjunctiveCandidates).flatMap({
                case Left(l) => l.map(i => i._1 -> Some(PegasusProofHint(isInvariant = true, proofHint(i._2))))
                case Right(r) => r.map(i => i._1 -> Some(PegasusProofHint(isInvariant = false, proofHint(i._2))))
              })
            } else {
              pegasusInvs.filter(_.isLeft).flatMap(_.left.get.map(i => i._1 -> Some(PegasusProofHint(isInvariant=true, proofHint(i._2)))))
            }
          Stream[GenProduct]() #::: invs.toStream.distinct
        case _ => Seq().toStream
      }
    case Some(Box(_: ODESystem, post: Formula)) if !post.isFOL => Seq().toStream.distinct
    case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation in " + sequent)
    case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
  }

  /** Inverse Characteristic Method differential invariant generator.
    * @see Andre Platzer. [[https://doi.org/10.1007/978-3-642-32347-8_3 A differential operator approach to equational differential invariants]]. In Lennart Beringer and Amy Felty, editors, Interactive Theorem Proving, International Conference, ITP 2012, August 13-15, Princeton, USA, Proceedings, volume 7406 of LNCS, pages 28-48. Springer, 2012.
    */
  val inverseCharacteristicDifferentialInvariantGenerator: Generator[GenProduct] = (sequent,pos) => {
    import FormulaTools._
    if (ToolProvider.algebraTool().isEmpty) throw new BelleThrowable("inverse characteristic method needs a computer algebra tool")
    if (ToolProvider.pdeTool().isEmpty) throw new BelleThrowable("inverse characteristic method needs a PDE Solver")
    val (ode, constraint, post) = sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, pf)) => (ode.ode,ode.constraint,pf)
      case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }
    val evos = if (constraint==True) Nil else FormulaTools.conjuncts(constraint)
    val solutions = try {
      ToolProvider.pdeTool().get.pdeSolve(ode).toStream.distinct
    } catch {
      case e: Throwable => throw new BelleThrowable("inverseCharacteristic generation unsuccessful", e)
    }
    if (solutions.isEmpty) throw new BelleThrowable("No solutions found that would construct invariants")
    val polynomials = atomicFormulas(negationNormalForm(post)).collect({
      case Equal(p,q)        => Minus(p,q)
      case GreaterEqual(p,q) => Minus(p,q)
      case LessEqual(p,q)    => Minus(q,p)
    }).distinct
    val algebra = ToolProvider.algebraTool().get
    val GB = algebra.groebnerBasis(polynomials)
    solutions.flatMap({case FuncOf(_, arg) => argumentList(arg)}).flatMap((inv:Term) => {
      val initial = algebra.polynomialReduce(inv, GB)._2
      //@todo could check that it's not a tautology using RCF
      List(Equal(inv,initial),GreaterEqual(inv,initial),LessEqual(inv,initial)).filter(cand => !evos.contains(cand))
    }).map(_ -> None).distinct
  }


  /** A cached invariant generator based on the candidates from `generator` that also remembers answers
    * to speed up computations.
    * @author Andre Platzer */
  def cached(generator: Generator[GenProduct]): Generator[GenProduct] = {
    val cache: scala.collection.mutable.Map[Box, Stream[GenProduct]] = new scala.collection.mutable.LinkedHashMap()
    (sequent,pos) => {
      val box = sequent.sub(pos) match {
        case Some(Box(ODESystem(ode, And(True, q)), pf)) => Box(ODESystem(ode, q), pf)
        case Some(box@Box(_: ODESystem, _)) => box
        case Some(box@Box(_: Loop, _)) => box
        case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
        case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
      }
      cache.get(box) match {
        case Some(cached) => cached
        case None =>
          val remember = generator(sequent,pos)
          cache.put(box,remember)
          remember
      }
    }
  }
}
