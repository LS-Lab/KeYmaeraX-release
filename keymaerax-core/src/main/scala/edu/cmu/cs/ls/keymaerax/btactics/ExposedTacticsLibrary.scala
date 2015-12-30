
package edu.cmu.cs.ls.keymaerax.btactics

import java.lang.Number

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.HilbertCalculus._
import edu.cmu.cs.ls.keymaerax.btactics.RenUSubst
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{PositionTactic, Tactic}

import scala.collection.immutable.HashMap

/**
  * A bidirectional mapping
  * @author Nathan Fulton
  */
class BiMap[S, T](private val underlyingMap: Map[S, T]) extends Map[S, T] {
  override def +[TPrime >: T](kv: (S, TPrime)): BiMap[S, TPrime] = {
    if(underlyingMap.keySet.contains(kv._1) || underlyingMap.values.toSet.contains(kv._2))
      throw new Exception("Bidirectional maps must be bijective.")
    else
      new BiMap(underlyingMap + kv)
  }

  override def get(key: S): Option[T] = underlyingMap.get(key)

  override def -(key: S): BiMap[S, T] = new BiMap(underlyingMap - key)

  def inverse : BiMap[T, S] = new BiMap(underlyingMap.map(kvp => (kvp._2, kvp._1)))

  override def iterator: Iterator[(S, T)] = underlyingMap.iterator
}

/**
  * Created by bbohrer on 12/19/15.
  */
object ExposedTacticsLibrary {
  /** Positional Tactics */
  val tactics: BiMap[String, BelleExpr] = new BiMap(Map(
   "nil"    ->  Idioms.nil
  ,"StepAt" ->  HilbertCalculus.stepAt
  ,"CloseFalse " ->  ProofRuleTactics.closeFalse
  ,"CloseTrue " ->  ProofRuleTactics.closeTrue
  ,"NotL" ->  ProofRuleTactics.notL
  ,"NotR" ->  ProofRuleTactics.notR
  ,"AndR" ->  ProofRuleTactics.andR
  ,"AndL" ->  ProofRuleTactics.andL
  ,"OrR" ->  ProofRuleTactics.orR
  ,"OrL" ->  ProofRuleTactics.orL
  ,"ImplyR" ->  ProofRuleTactics.implyR
  ,"ImplyL" ->  ProofRuleTactics.implyL
  ,"EquivR" ->  ProofRuleTactics.equivR
  ,"EquivL" ->  ProofRuleTactics.equivL
  ,"CommuteEquivL" ->  ProofRuleTactics.commuteEquivL
  ,"CommuteEquivR" ->  ProofRuleTactics.commuteEquivR
  ,"EquivifyR" ->  ProofRuleTactics.equivifyR
  ,"Hide " ->  ProofRuleTactics.hide
  ,"HideL" ->  ProofRuleTactics.hideL
  ,"HideR" ->  ProofRuleTactics.hideR
  ,"CoHide" ->  ProofRuleTactics.coHide
  ,"CoHideL" ->  ProofRuleTactics.coHideL
  ,"CoHideR" ->  ProofRuleTactics.coHideR
  ,"Skolemize" -> ProofRuleTactics.skolemize
  ,"SkolemizeL" ->  ProofRuleTactics.skolemizeL
  ,"SkolemizeR" ->  ProofRuleTactics.skolemizeR
  ,"DualFree" ->  ProofRuleTactics.dualFree
  // modalities
  ,"BoxAssign" ->  HilbertCalculus.assignb
  ,"BoxRandom" ->  HilbertCalculus.randomb
  ,"BoxTest" ->  HilbertCalculus.testb
//  ,"DiffSolution" ->  HilbertCalculus.diffSolve @todo diffSolve needs an implementation
  ,"BoxChoice" ->  HilbertCalculus.choiceb
  ,"BoxCompose" ->  HilbertCalculus.composeb
  ,"BoxIterate" ->  HilbertCalculus.iterateb
//  ,"BoxDual" ->  HilbertCalculus.dualb //@todo commented out b/c we get an error whenever dualb is initialized.
  ,"DiamondAssign" ->  HilbertCalculus.assignd
//  ,"DiamondRandom" ->  HilbertCalculus.randomd //@todo causes some other error.
  ,"DiamondTest" ->  HilbertCalculus.testd
//  ,"DiamondDiffSolution" ->  HilbertCalculus.diffSolved //@todo diffSolved needs an implementation
  ,"DiamondChoice" ->  HilbertCalculus.choiced
//  ,"DiamondCompose" ->  HilbertCalculus.composed
//  ,"DiamondIterate" ->  HilbertCalculus.iterated
//  ,"DiamondDual" ->  HilbertCalculus.duald
//  ,"V" ->  HilbertCalculus.V
  ,"DW" ->  HilbertCalculus.DW
//  /* @TODO DC, DG */
  ,"DE" ->  HilbertCalculus.DE
  ,"DI" ->  HilbertCalculus.DI
////  ,"DiffInd" ->  //@todo this no longer exists: HilbertCalculus.diffInd
  ,"DS" ->  HilbertCalculus.DS
  ,"BoxDifferentialAssign" ->  HilbertCalculus.Dassignb
  ,"Derive" ->  HilbertCalculus.derive
  ,"DerivePlus" ->  HilbertCalculus.Dplus
  ,"DeriveNeg" ->  HilbertCalculus.Dneg
  ,"DeriveMinus" ->  HilbertCalculus.Dminus
  ,"DeriveTimes" ->  HilbertCalculus.Dtimes
  ,"DeriveQuotient" ->  HilbertCalculus.Dquotient
  ,"DerivePower" ->  HilbertCalculus.Dpower
  ,"DeriveConstant" ->  HilbertCalculus.Dconst
//  ,"DeriveVariable" ->  HilbertCalculus.Dvariable //@todo causes some error
  ,"DeriveAnd" ->  HilbertCalculus.Dand
  ,"DeriveOr" ->  HilbertCalculus.Dor
//  ,"DeriveImply" ->  HilbertCalculus.Dimply //@todo causes some error
  ,"DeriveEqual" ->  HilbertCalculus.Dequal
  ,"DeriveNotEqual" ->  HilbertCalculus.Dnotequal
  ,"DeriveLess" ->  HilbertCalculus.Dless
  ,"DeriveLessEqual" ->  HilbertCalculus.Dlessequal
  ,"DeriveGreater" ->  HilbertCalculus.Dgreater
  ,"DeriveGreaterEqual" ->  HilbertCalculus.Dgreaterequal
  ,"DeriveForall" ->  HilbertCalculus.Dforall
  ,"DeriveExists" ->  HilbertCalculus.Dexists
  ,"BoxSplit" -> HilbertCalculus.splitb
  ,"VacuousAll" ->  HilbertCalculus.vacuousAll
//  ,"DiamondSplit" -> HilbertCalculus.splitd //@todo causes some error
//  ,"VacuousExists" ->  HilbertCalculus.vacuousExists //@todo causes some error
  ,"Step" -> TactixLibrary.step
  //two position tactics
  ,"Close" -> ProofRuleTactics.close
  ,"CoHide2" -> ProofRuleTactics.coHide2
  ,"ExchangeL" -> ProofRuleTactics.exchangeL
  ,"ExchangeR" -> ProofRuleTactics.exchangeR
  //nullary tactics
  , "TrivialCloser" -> ProofRuleTactics.trivialCloser
  ,"Prop" -> TactixLibrary.prop
//  ,"Master" -> TactixLibrary.master) @todo cannot do this b/c master needs a generator
  //formula position tactics @todo these are also not okay because we need a map of BelleExpr's.
//  , "CutLR" -> {case fml => {case pos => ProofRuleTactics.cutLR(fml)(pos)}}
//  , "Cut" -> {case fml => ProofRuleTactics.cut(fml)}
  ))
  /* @TODO US, axiomatic, uniformRenaming, boundRenaming
  *   All of PropositionalTactics.scala */
}
