
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
  * Created by bbohrer on 12/19/15.
  */
object ExposedTacticsLibrary {
  /** Positional Tactics */
  val positionalTactics: Map[String, BelleExpr] = Map(
   "StepAt" ->  HilbertCalculus.stepAt
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
  ,"DiffSolution" ->  HilbertCalculus.diffSolve
  ,"BoxChoice" ->  HilbertCalculus.choiceb
  ,"BoxCompose" ->  HilbertCalculus.composeb
  ,"BoxIterate" ->  HilbertCalculus.iterateb
  ,"BoxDual" ->  HilbertCalculus.dualb
  ,"DiamondAssign" ->  HilbertCalculus.assignd
  ,"DiamondRandom" ->  HilbertCalculus.randomd
  ,"DiamondTest" ->  HilbertCalculus.testd
  ,"DiamondDiffSolution" ->  HilbertCalculus.diffSolved
  ,"DiamondChoice" ->  HilbertCalculus.choiced
  ,"DiamondCompose" ->  HilbertCalculus.composed
  ,"DiamondIterate" ->  HilbertCalculus.iterated
  ,"DiamondDual" ->  HilbertCalculus.duald
  ,"V" ->  HilbertCalculus.V
  ,"DW" ->  HilbertCalculus.DW
  /* @TODO DC, DG */
  ,"DE" ->  HilbertCalculus.DE
  ,"DI" ->  HilbertCalculus.DI
  ,"DiffInd" ->  HilbertCalculus.diffInd
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
  ,"DeriveVariable" ->  HilbertCalculus.Dvariable
  ,"DeriveAnd" ->  HilbertCalculus.Dand
  ,"DeriveOr" ->  HilbertCalculus.Dor
  ,"DeriveImply" ->  HilbertCalculus.Dimply
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
  ,"DiamondSplit" -> HilbertCalculus.splitd
  ,"VacuousExists" ->  HilbertCalculus.vacuousExists
  ,"Step" -> TactixLibrary.step)

  val twoPositionTactics: Map[String, BuiltInTwoPositionTactic] = Map(
   "Close" -> ProofRuleTactics.close
  ,"CoHide2" -> ProofRuleTactics.coHide2
  ,"ExchangeL" -> ProofRuleTactics.exchangeL
  ,"ExchangeR" -> ProofRuleTactics.exchangeR)

  val nullaryTactics: Map[String, BelleExpr] = Map(
   "TrivialCloser" -> ProofRuleTactics.trivialCloser
  ,"Prop" -> TactixLibrary.prop
  ,"Master" -> TactixLibrary.master)

  val formulaPositionTactics: Map[String, Formula => Position => BelleExpr] = Map (
    "CutLR" -> {case fml => {case pos => ProofRuleTactics.cutLR(fml)(pos)}}
  )

  val formulaTactics: Map[String, Formula => BelleExpr] = Map (
    "Cut" -> {case fml => ProofRuleTactics.cut(fml)}
  )
  /* @TODO Do we have input versions of cut cutL cutR cutLR*/
  /* @TODO US, axiomatic, uniformRenaming, boundRenaming
  *   All of PropositionalTactics.scala */
}
