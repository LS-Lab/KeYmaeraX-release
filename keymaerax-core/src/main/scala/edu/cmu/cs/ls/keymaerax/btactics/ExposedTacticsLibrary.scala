
package edu.cmu.cs.ls.keymaerax.btactics

import java.lang.Number

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.HilbertCalculus._
import edu.cmu.cs.ls.keymaerax.btactics.RenUSubst
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{PositionTactic, Tactic}

/**
  * Created by bbohrer on 12/19/15.
  */
object ExposedTacticsLibrary {
  def CloseFalse : BuiltInLeftTactic = ProofRuleTactics.closeFalse
  def CloseTrue : BuiltInRightTactic = ProofRuleTactics.closeTrue
  def Close : BuiltInTwoPositionTactic = ProofRuleTactics.close
  def TrivialCloser: BuiltInTactic = ProofRuleTactics.trivialCloser
  /* @TODO Do we have input versions of cut cutL cutR cutLR*/
  /* @TODO US, axiomatic, uniformRenaming, boundRenaming
  *   All of PropositionalTactics.scala */
  def NotL: BuiltInLeftTactic = ProofRuleTactics.notL
  def NotR: BuiltInRightTactic = ProofRuleTactics.notR
  def AndR: BuiltInRightTactic = ProofRuleTactics.andR
  def AndL: BuiltInLeftTactic = ProofRuleTactics.andL
  def OrR: BuiltInRightTactic = ProofRuleTactics.orR
  def OrL: BuiltInLeftTactic = ProofRuleTactics.orL
  def ImplyR: BuiltInRightTactic = ProofRuleTactics.implyR
  def ImplyL: BuiltInLeftTactic = ProofRuleTactics.implyL
  def EquivR: BuiltInRightTactic = ProofRuleTactics.equivR
  def EquivL: BuiltInLeftTactic = ProofRuleTactics.equivL
  def CommuteEquivL: BuiltInLeftTactic = ProofRuleTactics.commuteEquivL
  def CommuteEquivR: BuiltInRightTactic = ProofRuleTactics.commuteEquivR
  def EquivifyR: BuiltInRightTactic = ProofRuleTactics.equivifyR
  def Hide : DependentPositionTactic = ProofRuleTactics.hide
  def HideL: BuiltInLeftTactic = ProofRuleTactics.hideL
  def HideR: BuiltInRightTactic = ProofRuleTactics.hideR
  def CoHide: DependentPositionTactic = ProofRuleTactics.coHide
  def CoHideL: BuiltInLeftTactic = ProofRuleTactics.coHideL
  def CoHideR: BuiltInRightTactic = ProofRuleTactics.coHideR
  def CoHide2: BuiltInTwoPositionTactic = ProofRuleTactics.coHide2
  def ExchangeL: BuiltInTwoPositionTactic = ProofRuleTactics.exchangeL
  def ExchangeR: BuiltInTwoPositionTactic = ProofRuleTactics.exchangeR

  def Skolemize: BuiltInPositionTactic = ProofRuleTactics.skolemize
  def SkolemizeL: BuiltInLeftTactic = ProofRuleTactics.skolemizeL
  def SkolemizeR: BuiltInRightTactic = ProofRuleTactics.skolemizeR
  def DualFree: BuiltInRightTactic = ProofRuleTactics.dualFree

  // modalities
  def BoxAssign: BelleExpr = HilbertCalculus.assignb
  def BoxRandom: BelleExpr = HilbertCalculus.randomb
  def BoxTest: BelleExpr = HilbertCalculus.testb
  def DiffSolution: BelleExpr = HilbertCalculus.diffSolve
  def BoxChoice: BelleExpr = HilbertCalculus.choiceb
  def BoxCompose: BelleExpr = HilbertCalculus.composeb
  def BoxIterate: BelleExpr = HilbertCalculus.iterateb
  def BoxDual: BelleExpr = HilbertCalculus.dualb

  def DiamondAssign: BelleExpr = HilbertCalculus.assignd
  def DiamondRandom: BelleExpr = HilbertCalculus.randomd
  def DiamondTest: BelleExpr = HilbertCalculus.testd
  def DiamondDiffSolution: BelleExpr = HilbertCalculus.diffSolved
  def DiamondChoice: BelleExpr = HilbertCalculus.choiced
  def DiamondCompose: BelleExpr = HilbertCalculus.composed
  def DiamondIterate: BelleExpr = HilbertCalculus.iterated
  def DiamondDual: BelleExpr = HilbertCalculus.duald
  def V: BelleExpr = HilbertCalculus.V
  def DW: BelleExpr = HilbertCalculus.DW
  /* @TODO DC, DG */
  def DE: BelleExpr = HilbertCalculus.DE
  def DI: BelleExpr = HilbertCalculus.DI
  def DiffInd: BelleExpr = HilbertCalculus.diffInd
  def DS: BelleExpr = HilbertCalculus.DS
  def BoxDifferentialAssign: BelleExpr = HilbertCalculus.Dassignb

  def Derive: BelleExpr = HilbertCalculus.derive
  def DerivePlus: BelleExpr = HilbertCalculus.Dplus
  def DeriveNeg: BelleExpr = HilbertCalculus.Dneg
  def DeriveMinus: BelleExpr = HilbertCalculus.Dminus
  def DeriveTimes: BelleExpr = HilbertCalculus.Dtimes
  def DeriveQuotient: BelleExpr = HilbertCalculus.Dquotient
  def DerivePower: BelleExpr = HilbertCalculus.Dpower
  def DeriveConstant: BelleExpr = HilbertCalculus.Dconst
  def DeriveVariable: BelleExpr = HilbertCalculus.Dvariable
  def DeriveAnd: BelleExpr = HilbertCalculus.Dand
  def DeriveOr: BelleExpr = HilbertCalculus.Dor
  def DeriveImply: BelleExpr = HilbertCalculus.Dimply
  def DeriveEqual: BelleExpr = HilbertCalculus.Dequal
  def DeriveNotEqual: BelleExpr = HilbertCalculus.Dnotequal
  def DeriveLess: BelleExpr = HilbertCalculus.Dless
  def DeriveLessEqual: BelleExpr = HilbertCalculus.Dlessequal
  def DeriveGreater: BelleExpr = HilbertCalculus.Dgreater
  def DeriveGreaterEqual: BelleExpr = HilbertCalculus.Dgreaterequal
  def DeriveForall: BelleExpr = HilbertCalculus.Dforall
  def DeriveExists: BelleExpr = HilbertCalculus.Dexists

  def BoxSplit:BelleExpr = HilbertCalculus.splitb
  def DiamondSplit:BelleExpr = HilbertCalculus.splitd

  def VacuousAll: BelleExpr = HilbertCalculus.vacuousAll
  def VacuousExists: BelleExpr = HilbertCalculus.vacuousExists

  def StepAt: DependentPositionTactic = HilbertCalculus.stepAt
}
