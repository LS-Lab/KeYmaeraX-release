/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleNoProgress, ProverSetupException}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{DependencyAnalysis, FormulaTools, StaticSemanticsTools}
import edu.cmu.cs.ls.keymaerax.tools.ToolException

import scala.collection.immutable.List

/** Invariant generators and differential invariant generators.
  * @author Andre Platzer
  * @see [[TactixLibrary.invSupplier]]
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
  def relevanceFilter(generator: Generator[GenProduct], analyzeMissing: Boolean): Generator[GenProduct] = (sequent,pos,defs) => {
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
      case _: DifferentialProgram => deps.getOrElse(x,List.empty).intersect(bounds.toList)
      case _: Loop => (x +: deps.getOrElse(x,List.empty)).intersect(bounds.toList)
    }
    lazy val missing = if (analyzeMissing) frees.flatMap(relevantInvVars).diff(knowledge) else frees.flatMap(relevantInvVars)
    //@todo above of course even vars that are in the domain might need more knowledge, but todo that later and lazy
    generator(sequent,pos,defs).
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
  def sortedRelevanceFilter(generator: Generator[GenProduct]): Generator[GenProduct] = (sequent,pos,defs) => {
    //@todo if frees depend on bound variables that are not mentioned in evolution domain constraint, then diffCut
    val system = sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _)) => ode
      case Some(Box(loop: Loop, _)) => loop
      case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }

    lazy val indOrder = DependencyAnalysis.inducedOrd(DependencyAnalysis.transClose(DependencyAnalysis.analyseModalVars(
      system, DependencyAnalysis.varSetToBaseVarSet(StaticSemantics.vars(system).toSet), ignoreTest = false).view.mapValues(v => v._1).toMap))

    lazy val vars = DependencyAnalysis.freeVars(sequent)
    lazy val order = vars.toList.sortWith((x, y) => {
      val ord = indOrder.compare(x, y)
      if (ord == 0) x.compare(y) < 0
      else ord < 0
    }
    )

    lazy val deps = StaticSemanticsTools.transitiveDependencies(system)

    def sizeCompare(a: Formula, b: Formula) = system match {
      case ODESystem(_: DifferentialProgram, _) =>
        // smaller set of variables that it depends on means good idea to try first in dependency order, excluding self-dependencies
        StaticSemantics.freeVars(a).symbols.flatMap((x:Variable) => deps.getOrElse(x,List.empty).filter(_!=x)).size <
        StaticSemantics.freeVars(b).symbols.flatMap((x:Variable) => deps.getOrElse(x,List.empty).filter(_!=x)).size
      case _: Loop =>
        // try invariants with larger coverage of the loop's free variables first
        (StaticSemantics.freeVars(system).symbols -- StaticSemantics.freeVars(a).symbols).size <
        (StaticSemantics.freeVars(system).symbols -- StaticSemantics.freeVars(b).symbols).size
    }

    def depCompare(a: Formula, b: Formula): Boolean = {
      val aOrder = order.lastIndexWhere(v => StaticSemantics.freeVars(a).contains(v))
      val bOrder = order.lastIndexWhere(v => StaticSemantics.freeVars(b).contains(v))
      if (aOrder == bOrder) sizeCompare(a, b)
      else aOrder < bOrder
    }

    relevanceFilter(generator, analyzeMissing = true)(sequent, pos, defs).
      // sort by dependency order
      //@todo performance construction should probably have been the other way around to ensure primitive dependencies are tried first and avoding sorting by that order retroactively
      sortWith((a: GenProduct, b: GenProduct) =>
        //@todo improve sorting to take dependency order into account, not just number. If x depends on y then y is smaller.
        //@todo improve sorting to take dependency cluster into account, too.
        if (a._1.isFOL == b._1.isFOL) depCompare(a._1, b._1)
        else a._1.isFOL //@note a.isFOL != b.isFOL, FOL are smaller than non-FOL formulas
      )
  }

  /** A differential invariant generator.
    * @author Andre Platzer */
  lazy val differentialInvariantGenerator: Generator[GenProduct] = (sequent,pos,defs) =>
    (TactixLibrary.invSupplier(sequent,pos,defs) #::: differentialInvariantCandidates(sequent,pos,defs)).distinct
  // ++ relevanceFilter(inverseCharacteristicDifferentialInvariantGenerator)(sequent,pos)

  /** A more expensive extended differential invariant generator.
    * @author Andre Platzer */
  lazy val extendedDifferentialInvariantGenerator: Generator[GenProduct] = (sequent,pos,defs) =>
    sortedRelevanceFilter(inverseCharacteristicDifferentialInvariantGenerator)(sequent,pos,defs).distinct

  /** A loop invariant generator.
    * @author Andre Platzer */
  lazy val loopInvariantGenerator: Generator[GenProduct] = (sequent,pos,defs) =>
    (TactixLibrary.invSupplier(sequent,pos,defs) #::: sortedRelevanceFilter(loopInvariantCandidates)(sequent,pos,defs)).distinct

  /** A simplistic differential invariant candidate generator.
    * @author Andre Platzer */
  lazy val differentialInvariantCandidates: Generator[GenProduct] = (sequent,pos,defs) =>
    //@note be careful to not evaluate entire stream by sorting/filtering etc.
    //@note do not relevance filter Pegasus candidates: they contain trivial results, that however make ODE try harder
    // since flagged as truly invariant and not just a guess like the simple candidates
    (sortedRelevanceFilter(simpleInvariantCandidates)(sequent,pos,defs) #::: pegasusCandidates(sequent,pos,defs)).distinct

  /** A simplistic loop invariant candidate generator.
    * @author Andre Platzer */
  lazy val loopInvariantCandidates: Generator[GenProduct] = simpleInvariantCandidates


  /** A simplistic invariant and differential invariant candidate generator.
    * @author Andre Platzer */
  lazy val simpleInvariantCandidates: Generator[GenProduct] = (sequent,pos,defs) => {
    def combinedAssumptions(loop: Loop, post: Formula): List[Formula] = {
      val anteConjuncts = defs.exhaustiveSubst(sequent).ante.toList.flatMap(FormulaTools.conjuncts)
      val postConjuncts = FormulaTools.conjuncts(post)
      val loopBV = StaticSemantics.boundVars(loop)
      val combined = anteConjuncts.
        filter(fml => !postConjuncts.contains(fml) && !StaticSemantics.freeVars(fml).intersect(loopBV).isEmpty)
      val anteInvCandidate = combined.reduceRightOption(And).getOrElse(True)
      //@todo pre -> post counterexample is not strong enough to indicate what to filter (need to consult loop body).
      if (ToolProvider.cexTool().isDefined) {
        //@note used to be Imply, now filter only duplicate information
        postConjuncts.filter(fml => fml.isFOL && TactixLibrary.findCounterExample(Equiv(anteInvCandidate, fml)).isDefined) match {
          case Nil => combined
          case missingPost => missingPost ++ combined
        }
      } else postConjuncts ++ combined
    }
    defs.exhaustiveSubst(sequent).sub(pos) match {
      case Some(Box(_: ODESystem, post)) => FormulaTools.conjuncts(post +: defs.exhaustiveSubst(sequent).ante.toList).distinct.map(_ -> None).toStream.distinct
      case Some(Box(l: Loop, post))      =>
        val combined = combinedAssumptions(l, post).distinct
        (combined :+ combined.reduceRightOption(And).getOrElse(True) :+ post).map(_ -> None).toStream.distinct
      case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation or loop in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }}

  /** Pegasus invariant generator (requires Mathematica). */
  lazy val pegasusInvariants: Generator[GenProduct] = pegasus(includeCandidates=false)
  lazy val pegasusCandidates: Generator[GenProduct] = pegasus(includeCandidates=true)
  def pegasus(includeCandidates: Boolean): Generator[GenProduct] = (sequent,pos,_) => sequent.sub(pos) match {
    case Some(Box(ode: ODESystem, post: Formula)) if post.isFOL =>
      ToolProvider.invGenTool() match {
        case Some(tool) =>
          def proofHint(s: String): Option[String] = if (s != "Unknown") Some(s) else None
          lazy val pegasusInvs: Seq[Either[Seq[(Formula, String)], Seq[(Formula, String)]]] = {
            val succFmls = sequent.succ.patch(pos.index0, Nil, 1).filter(_.isFOL)
            val assumptions =
              if (succFmls.isEmpty) sequent.ante
              else sequent.ante :+ Not(succFmls.reduceRight(Or))
            tool.invgen(ode, assumptions, post)
          }
          lazy val invs: Seq[GenProduct] =
            if (includeCandidates) {
              pegasusInvs.flatMap({
                case Left(l) => l.map(i => i._1 -> Some(PegasusProofHint(isInvariant = true, proofHint(i._2))))
                case Right(r) => r.map(i => i._1 -> Some(PegasusProofHint(isInvariant = false, proofHint(i._2))))
              })
            } else {
              pegasusInvs.filter(_.isLeft).flatMap(_.left.toOption.get.map(i => i._1 -> Some(PegasusProofHint(isInvariant=true, proofHint(i._2)))))
            }
          invs.toStream.distinct
        case _ => Seq().toStream
      }
    case Some(Box(_: ODESystem, post: Formula)) if !post.isFOL => Seq().toStream.distinct
    case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation in " + sequent)
    case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
  }

  /** Inverse Characteristic Method differential invariant generator.
    * @see Andre Platzer. [[https://doi.org/10.1007/978-3-642-32347-8_3 A differential operator approach to equational differential invariants]]. In Lennart Beringer and Amy Felty, editors, Interactive Theorem Proving, International Conference, ITP 2012, August 13-15, Princeton, USA, Proceedings, volume 7406 of LNCS, pages 28-48. Springer, 2012.
    */
  val inverseCharacteristicDifferentialInvariantGenerator: Generator[GenProduct] = (sequent,pos,defs) => {
    import FormulaTools._
    if (ToolProvider.algebraTool().isEmpty) throw new ProverSetupException("inverse characteristic method needs a computer algebra tool")
    if (ToolProvider.pdeTool().isEmpty) throw new ProverSetupException("inverse characteristic method needs a PDE Solver")
    val (ode, constraint, post) = sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, pf)) => (ode.ode,ode.constraint,pf)
      case Some(_) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation in " + sequent)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + sequent)
    }
    val evos = if (constraint==True) Nil else FormulaTools.conjuncts(constraint)
    val solutions = try {
      ToolProvider.pdeTool().get.pdeSolve(ode).toStream.distinct
    } catch {
      case ex: ToolException => throw new BelleNoProgress("inverseCharacteristic generation unsuccessful", ex)
    }
    if (solutions.isEmpty) throw new BelleNoProgress("No solutions found that would construct invariants")
    val polynomials = atomicFormulas(negationNormalForm(post)).collect({
      case Equal(p,q)        => Minus(p,q)
      case GreaterEqual(p,q) => Minus(p,q)
      case LessEqual(p,q)    => Minus(q,p)
    }).distinct
    val algebra = ToolProvider.algebraTool().get
    try {
      val GB = algebra.groebnerBasis(polynomials)
      solutions.flatMap({ case FuncOf(_, arg) => argumentList(arg) }).flatMap((inv: Term) => {
        val initial = algebra.polynomialReduce(inv, GB)._2
        //@todo could check that it's not a tautology using RCF
        List(Equal(inv, initial), GreaterEqual(inv, initial), LessEqual(inv, initial)).filter(cand => !evos.contains(cand))
      }).map(_ -> None).distinct
    } catch {
      case ex: ToolException => throw new BelleNoProgress("inverseCharacteristic generation unsuccessful", ex)
    }
  }


  /** A cached invariant generator based on the candidates from `generator` that also remembers answers
    * to speed up computations.
    * @author Andre Platzer */
  def cached(generator: Generator[GenProduct]): Generator[GenProduct] = {
    val cache: scala.collection.mutable.Map[Box, Stream[GenProduct]] = new scala.collection.mutable.LinkedHashMap()
    (sequent,pos,defs) => {
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
          val remember = generator(sequent,pos,defs)
          cache.put(box,remember)
          remember
      }
    }
  }
}
