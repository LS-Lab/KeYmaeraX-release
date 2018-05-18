/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
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
      SearchAndRescueAgain(jj,
        //@todo OnAll(ifThenElse(shape [a]P, chase(1.0) , skip)) instead of | to chase away modal postconditions
        loop(subst(jj))(pos) < (nil, nil, chase(pos) & OnAll(chase(pos ++ PosInExpr(1::Nil)) | skip)),
        feedOneAfterTheOther(cand),
        //@todo switch to quickstop mode
        OnAll(master()) & done
      )
    case e => throw new BelleThrowable("Wrong shape to generate an invariant for " + e + " at position " + pos)
  })

  private def feedOneAfterTheOther[A<:Expression](gen: Iterator[A]) : (ProvableSig,ProverException)=>Expression = {
    (_,e) => logger.debug("SnR loop status " + e)
      if (gen.hasNext)
        gen.next()
      else
        throw new BelleThrowable("loopSR ran out of loop invariant candidates")
  }

  def loopPostMaster(gen: Generator[Formula]): DependentPositionTactic = "loopPostMaster" by ((pos:Position,seq:Sequent) => Augmentors.SequentAugmentor(seq)(pos) match {
    case loopfml@Box(prog, post) =>
      val initialCond = seq.ante.reduceRightOption(And).getOrElse(True)
      //val cand: Iterator[Formula] = gen(seq, pos)
      val bounds: List[Variable] =
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
      val jj: Formula = KeYmaeraXParser.formulaParser("jjl(" + subst.subsDefsInput.map(sp => sp.what.prettyString).mkString(",") + ")")
      val jja: Formula = KeYmaeraXParser.formulaParser("jja()")

      val finishOff: BelleExpr =
      //@todo switch to quickstop mode
      //@todo if (ODE) then ODEInvariance.sAIclosedPlus(1) else ....
      //@todo plug in true for jja, commit if succeeded. Else plug in init for jja and generate
        OnAll(ODEInvariance.sAIclosedPlus(1)) & done


      def generateOnTheFly[A <: Expression](initialCond: Formula, pos: Position, initialCandidate: Formula): (ProvableSig, ProverException) => Expression = {
        var candidate: Formula = initialCandidate
        println/*logger.info*/("loopPostMaster initial " + candidate)
        return {
          (pr, e) => {
              breakable {
                for (seq <- pr.subgoals) {
                  seq.sub(pos) match {
                    case Some(Box(sys: ODESystem, post)) =>
                      val wouldBeSeq = USubst(Seq(SubstitutionPair(jj, candidate), SubstitutionPair(jja, True)))(seq)
                      if (proveBy(wouldBeSeq, finishOff).isProved) {
                        // proof will work so no need to change candidate
                      } else {
                        val assumeMoreSeq = USubst(Seq(SubstitutionPair(jj, candidate), SubstitutionPair(jja, initialCond)))(seq)
                        candidate = gen(assumeMoreSeq, pos).next()
                        println/*logger.info*/("loopPostMaster next    " + candidate)
                        break
                      }
                    case _ =>
                    // ignore branches that are not about ODEs
                      //@todo don't loop forever if there are no odes anywhere
                  }
                }
              }
            candidate
          }
        }
      }


      SearchAndRescueAgain(jj,
        //@todo OnAll(ifThenElse(shape [a]P, chase(1.0) , skip)) instead of | to chase away modal postconditions
        loop(subst(jj))(pos) < (nil, nil,
          cut(jja) <(
            /* show postponed |- jja() */
            hide(pos)
            //@todo cohide(Find.FindR(0, Some(jja)))
            ,
            /* use jja() |- */
            chase(pos) & OnAll(propChase) & OnAll((chase(pos ++ PosInExpr(1::Nil)) | skip) & (QE() | skip))
            )
          ),
        generateOnTheFly(initialCond, pos, post)
        ,
        finishOff
      )
    case e => throw new BelleThrowable("Wrong shape to generate an invariant for " + e + " at position " + pos)
  })

  //@todo this is a suboptimal emulation for propositional chase on (1)
  def propChase = normalize

}
