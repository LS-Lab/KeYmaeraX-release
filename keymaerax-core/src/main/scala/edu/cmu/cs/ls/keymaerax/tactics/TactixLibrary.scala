/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.{Formula, Term, Variable}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{PositionTactic, Tactic}

/**
 * Main tactic library with simple interface.
 * Created by aplatzer on 7/17/15.
 * @author aplatzer
 */
object TactixLibrary {
  // Locating applicable positions for PositionTactics

  /** Locate applicable position in succedent */
  def ls(tactic: PositionTactic): Tactic = TacticLibrary.locateSucc(tactic)
  /** Locate applicable position in antecedent */
  def la(tactic: PositionTactic): Tactic = TacticLibrary.locateAnte(tactic)
  /** Locate applicable position in antecedent or succedent */
  def l(tactic: PositionTactic): Tactic  = TacticLibrary.locateAnteSucc(tactic)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Propositional tactics
  def hide                    : PositionTactic = TacticLibrary.hideT
  def hideL                   : PositionTactic = TacticLibrary.hideT
  def hideR                   : PositionTactic = TacticLibrary.hideT
  def notL                    : PositionTactic = TacticLibrary.NotLeftT
  def notR                    : PositionTactic = TacticLibrary.NotRightT
  def andL                    : PositionTactic = TacticLibrary.AndLeftT
  def andR                    : PositionTactic = TacticLibrary.AndRightT
  def orL                     : PositionTactic = TacticLibrary.OrLeftT
  def orR                     : PositionTactic = TacticLibrary.OrRightT
  def implyL                  : PositionTactic = TacticLibrary.ImplyLeftT
  def implyR                  : PositionTactic = TacticLibrary.ImplyRightT
  def equivL                  : PositionTactic = ???
  def equivR                  : PositionTactic = ???

  def cut(cut : Formula)      : Tactic         = TacticLibrary.cutT(Some(cut))

  // quantifiers
  def allR                    : PositionTactic = TacticLibrary.skolemizeT
  def allL(x: Variable, inst: Term) : PositionTactic = TacticLibrary.instantiateQuanT(x, inst)
  def allL(inst: Term)        : PositionTactic = TacticLibrary.instantiateQuanT(???, inst)
  def existsL                 : PositionTactic = TacticLibrary.skolemizeT
  def existsR(x: Variable, inst: Term) : PositionTactic = TacticLibrary.instantiateQuanT(x, inst)
  def existsR(inst: Term)     : PositionTactic = TacticLibrary.instantiateQuanT(???, inst)

  // modalities
  //  def SpecificMaster(toolId : String) : Tactic = TacticLibrary.master(new NoneGenerate(), true, toolId)
  def assignb                 : PositionTactic = TacticLibrary.boxAssignT
  def randomb                 : PositionTactic = TacticLibrary.boxNDetAssign
  def testb                   : PositionTactic = TacticLibrary.boxTestT
  def diffSolve               : PositionTactic = TacticLibrary.diffSolutionT
  def choiceb                 : PositionTactic = TacticLibrary.boxChoiceT
  def composeb                : PositionTactic = TacticLibrary.boxSeqT
  def I(invariant : Formula)  : PositionTactic = TacticLibrary.inductionT(Some(invariant))
  def loop(invariant: Formula) = I(invariant)
  def iterateb                : PositionTactic = ???
  def K                       : PositionTactic = ???
  def V                       : PositionTactic = ???

  // differential equations
  def DW                      : PositionTactic = TacticLibrary.diffWeakenT
  def DC(invariant: Formula)  : PositionTactic = TacticLibrary.diffCutT(invariant)
  def DE                      : PositionTactic = ???
  def DI                      : PositionTactic = TacticLibrary.diffInvariant
  def DG                      : PositionTactic = ???
  def DS                      : PositionTactic = ???
  def Dassignb                : PositionTactic = ???
  def Dplus                   : PositionTactic = ???
  def Dminus                  : PositionTactic = ???
  def Dtimes                  : PositionTactic = ???
  def Dcompose                : PositionTactic = ???

  // arithmetic
  def QE                      : Tactic         = TacticLibrary.arithmeticT

  //@todo def axiom                   : Tactic         = TacticLibrary.AxiomCloseT
  def closeT                  : PositionTactic = TacticLibrary.CloseTrueT
  def closeF                  : PositionTactic = TacticLibrary.CloseFalseT

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Bigger Tactics.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def master                  : Tactic = TacticLibrary.master(new NoneGenerate(), true, "Mathematica")

  // Utility Tactics
  def nil : Tactic = Tactics.NilT

}
