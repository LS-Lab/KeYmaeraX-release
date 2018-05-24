/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleThrowable, _}
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticIndex.TacticRecursors
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement
import org.apache.logging.log4j.scala.Logger

import scala.collection.immutable.Seq
import scala.collection.immutable.List
import util.control.Breaks._

/**
  * Created by aplatzer on 5/17/18.
  *
  * @author Andre Platzer
  */
object InvariantProvers {
  import Generator.Generator
  import TactixLibrary._

  private val logger = Logger(getClass) //@note instead of "with Logging" to avoid cyclic dependencies

  /** loopSR: cleverly prove a property of a loop automatically by induction, trying hard to generate loop invariants.
    * Uses [[SearchAndRescueAgain]] to avoid repetitive proving.
    * @see [[loopauto]]
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
    *      Example 32. */
  def loopSR(gen: Generator[Formula]): DependentPositionTactic = "loopSR" by ((pos:Position,seq:Sequent) => Augmentors.SequentAugmentor(seq)(pos) match {
    case loopfml@Box(prog, post) =>
      val cand: Iterator[Formula] = gen(seq, pos)
      val bounds: List[Variable] =
        if (StaticSemantics.freeVars(post).toSet.exists( v => v.isInstanceOf[DifferentialSymbol] ) )
          StaticSemantics.boundVars(loopfml).toSet.toList
        else DependencyAnalysis.dependencies(prog, DependencyAnalysis.freeVars(post))._1.toList
      var i = -1
      val subst: USubst = if (bounds.length==1)
        USubst(Seq(SubstitutionPair(DotTerm(), bounds.head)))
      else
        USubst(bounds.map(xi=> {i=i+1; SubstitutionPair(DotTerm(Real,Some(i)), xi)}))
      val jj: Formula = KeYmaeraXParser.formulaParser("jjl(" + subst.subsDefsInput.map(sp=>sp.what.prettyString).mkString(",") + ")")
      SearchAndRescueAgain(jj :: Nil,
        //@todo OnAll(ifThenElse(shape [a]P, chase(1.0) , skip)) instead of | to chase away modal postconditions
        loop(subst(jj))(pos) < (nil, nil, chase(pos) & OnAll(chase(pos ++ PosInExpr(1::Nil)) | skip)),
        feedOneAfterTheOther(cand),
        //@todo switch to quickstop mode
        OnAll(master()) & done
      )
    case e => throw new BelleThrowable("Wrong shape to generate an invariant for " + e + " at position " + pos)
  })

  private def feedOneAfterTheOther[A<:Expression](gen: Iterator[A]) : (ProvableSig,ProverException)=>Seq[Expression] = {
    (_,e) => logger.debug("SnR loop status " + e)
      if (gen.hasNext)
        gen.next() :: Nil
      else
        throw new BelleThrowable("loopSR ran out of loop invariant candidates")
  }



  /** [[TactixLibrary.loopPostMaster()]] */
  def loopPostMaster(gen: Generator[Formula]): DependentPositionTactic = "loopPostMaster" by ((pos:Position,seq:Sequent) => Augmentors.SequentAugmentor(seq)(pos) match {
    case loopfml@Box(prog, post) =>
      val initialCond = seq.ante.reduceRightOption(And).getOrElse(True)
      val bounds: List[Variable] =
        // DependencyAnalysis is incorrect when primed symbols occur, so default to all bound variables in that case
        if (StaticSemantics.freeVars(post).toSet.exists(v => v.isInstanceOf[DifferentialSymbol]))
          StaticSemantics.boundVars(loopfml).toSet.toList
        else DependencyAnalysis.dependencies(prog, DependencyAnalysis.freeVars(post))._1.toList
      var i = -1
      val subst: USubst = if (bounds.length == 1)
        USubst(Seq(SubstitutionPair(DotTerm(), bounds.head)))
      else
        USubst(bounds.map(xi => {
          i = i + 1; SubstitutionPair(DotTerm(Real, Some(i)), xi)
        }))

      def constructPred(name: String, args: Seq[Term]): Formula = {
        val head :: tail = args.reverse
        val arg = tail.foldLeft(head)({ case (ps, t) => Pair(t, ps) })
        PredOf(Function(name, None, arg.sort, Bool), arg)
      }

      val jj: Formula = constructPred("jjl", subst.subsDefsInput.map(_.what.asInstanceOf[Term]))
      val jjl: Formula = constructPred("jjl", subst.subsDefsInput.map(_.repl.asInstanceOf[Term]))
      // eventually instantiated to True, trick to substitute initialCond in during the search process
      val jja: Formula = PredOf(Function("jja", None, Unit, Bool), Nothing)

      /* stateful mutable candidate used in generateOnTheFly and the pass-through later since usubst end tactic not present yet */
      var candidate: Option[Formula] = Some(post)

      val finishOff: BelleExpr =
        OnAll(ifThenElse(DifferentialTactics.isODE,
          odeInvariant(pos) |
            // augment loop invariant to local ODE invariant if possible
            ("ANON" by ((pos: Position, seq: Sequent) => { dC(gen(seq, pos).toList.head)(pos) <(dW(pos) & QE(), odeInvariant(pos)) }))
          ,
          QE())(pos)) & done

      def nextCandidate(pr: ProvableSig, sequent: Sequent, currentCandidate: Option[Formula]): Option[Formula] = currentCandidate match {
        case Some(cand) =>
          logger.debug("loopPostMaster subst " + USubst(Seq(jjl ~>> cand, jja ~> True)))
          // plug in true for jja, commit if succeeded. Else plug in init for jja and generate
          val wouldBeSeq = USubst(Seq(jjl ~>> cand, jja ~> True))(sequent)
          lazy val wouldBeSubgoals = USubst(Seq(jjl ~>> cand, jja ~> True))(pr)
          logger.debug("loopPostMaster looks at\n" + wouldBeSeq)
          //@note first check induction step; then lazily check all subgoals (candidate may not be true initially or not strong enough)
          val stepProof = proveBy(wouldBeSeq, ?(finishOff))
          if (stepProof.isProved && proveBy(wouldBeSubgoals(stepProof, wouldBeSubgoals.subgoals.indexOf(stepProof.conclusion)), ?(finishOff)).isProved) {
            // proof will work so no need to change candidate
            println("Proof will work " + wouldBeSubgoals.prettyString)
            currentCandidate
          } else {
            logger.debug("loopPostMaster progressing")
            val assumeMoreSeq = USubst(Seq(jjl ~>> cand, jja ~> initialCond))(sequent)
            val generator = gen(assumeMoreSeq, pos)
            if (generator.hasNext) {
              candidate = Some(gen(assumeMoreSeq, pos).next())
              println/*logger.info*/("loopPostMaster next    " + candidate.get)
              candidate
            } else {
              None
            }
          }
        case _ => currentCandidate
      }

      def generateOnTheFly[A <: Expression](pos: Position): (ProvableSig, ProverException) => scala.collection.immutable.Seq[Expression] = {
        logger.debug("loopPostMaster initial " + candidate)
        (pr: ProvableSig, _: ProverException) => {
          var sawODE: Boolean = false
          //@note updates "global" candidate
          breakable {
            for (seq <- pr.subgoals) {
              seq.sub(pos) match {
                case Some(Box(_: ODESystem, _)) =>
                  sawODE = true
                  candidate = nextCandidate(pr, seq, candidate); break
                case _ => // ignore branches that are not about ODEs
              }
            }
          }
          candidate match {
            case Some(c) =>
              logger.debug("loopPostMaster cand    " + c)
              // c for jjl, eventual True for jja
              c :: True :: Nil
            case _ =>
              if (sawODE)
                throw new BelleThrowable("loopPostMaster: Invariant generator ran out of ideas for\n" + pr.prettyString)
              else
                throw new BelleThrowable("loopPostMaster: No more progress for lack of ODEs in the loop\n" + pr.prettyString)
          }
        }
      }

      SearchAndRescueAgain(jjl :: jja :: Nil,
        //@todo OnAll(ifThenElse(shape [a]P, chase(1.0) , skip)) instead of | to chase away modal postconditions
        loop(subst(jj))(pos) < (nil, nil,
          cut(jja) <(
            /* use jja() |- */
            chase(pos) & OnAll(unfoldProgramNormalize) & OnAll(?(chase(pos ++ PosInExpr(1::Nil))) & ?(QE() & done))
            ,
            /* show |- jja() is postponed since only provable for jja()=True */
            cohide('Rlast)
            //@todo cohide(Find.FindR(0, Some(jja)))
            )
          ),
        generateOnTheFly(pos)
        ,
        finishOff
      )

    case e => throw new BelleThrowable("Wrong shape to generate an invariant for " + e + " at position " + pos)
  })

}
