/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, EqualityTactics, Idioms}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors.SequentAugmentor

import scala.language.postfixOps

/**
  * Tactics used to prove several lemmas/theorems.
  *
  * @author Khalil Ghorbal
  * @author Jean-Baptiste Jeannin
  * @author Yanni A. Kouskoulas
  * @author Stefan Mitsch
  * @author Andre Platzer
  */
object SharedTactics {

  private val DEBUG = true

  /* Common tactics */
  def dT(s: => String): BelleExpr = /*Tactics.SubLabelBranch(s) &*/ DebuggingTactics.debug(s, doPrint = DEBUG, _.prettyString)

  def cutEZ(c: Formula, t: BelleExpr): BelleExpr = cut(c) & Idioms.<(skip, /* show */ t & done)

  /** Insert a lemma that has no assumptions. */
  def allTRoHoL(caseName: String, tInst: String, roInst: String, hoInst: String): BelleExpr =
    dT(caseName) &
    allL("t".asVariable, tInst.asTerm)('L) &
    allL("ro".asVariable, roInst.asTerm)('L) &
    allL("ho".asVariable, hoInst.asTerm)('L) &
    dT(s"$caseName Inst")

  /* Use case lower bound */
  def ucLoTac(condImpl: Formula): BelleExpr =
    dT("before orL") & orL('L, condImpl) & Idioms.<(
      dT("before inst 0 lower") &
        allL(Variable("t"), Number(0))('L) &
        allL(Variable("ro"), Number(0))('L) &
        allL(Variable("ho"), Number(0))('L) & implyL('L) & Idioms.<(
        dT("Use case 1") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
          EqualityTactics.abbrv("max((0,w*(dhf-dhd)))".asTerm, Some(Variable("maxI"))) &
          max('L, "max(0,w*(dhf-dhd))".asTerm) &
          dT("MinMax Lower") & QE & done
        ,
        dT("Absolute value") &
          abs('R, "abs(r)".asTerm) &
          abs('R, "abs(h)".asTerm) &
          abs('L, "abs(r-0)".asTerm) &
          dT("Use case 2") & QE & done
      ) & done,
      dT("before inst 0 upper") &
        allL(Variable("t"), Number(0))('L) &
        allL(Variable("ro"), Number(0))('L) &
        allL(Variable("ho"), Number(0))('L) & implyL('L) & Idioms.<(
        dT("Use case 1") & hideR('R, "abs(r)>rp|abs(h)>hp".asFormula) &
          EqualityTactics.abbrv("max((0,w*(dhfM-dhd)))".asTerm, Some(Variable("maxIM"))) &
          max('L, "max(0,w*(dhfM-dhd))".asTerm) &
          dT("MinMax Upper") & QE,
        dT("Absolute value") &
          abs('R, "abs(r)".asTerm) &
          abs('R, "abs(h)".asTerm) &
          abs('L, "abs(r-0)".asTerm) &
          dT("Use case 2 upper") & QE & done
      ))

  // Hides everything except the positions requested
  // Used to hide positions in a sequent for calls to QE when only a few of them are used
  def hideAllBut(keep:Int*) = new SingleGoalDependentTactic("hide all but") {
    override def computeExpr(seq: Sequent): BelleExpr = {
      assert(keep.forall(n => seq.sub(Position(n)).isDefined))
      val antehide =
        (List.range(-1,-(seq.ante.length+1),-1).foldLeft(nil)
        ((tac:BelleExpr,i:Int)=> (if (keep.contains(i)) skip else hideL(i)) & tac))
      (List.range(1,seq.succ.length+1,1).foldLeft(antehide)
        ((tac:BelleExpr,i:Int)=> (if (keep.contains(i)) skip else hideR(i)) & tac))
    }
  }

  //Exhaustive andL*
  val eAndL: BelleExpr = andL('L)*

  //Exhaustive or cases at a position
  def eOrLPos(i: Int): BelleExpr = OnAll(Idioms.?(orL(i)))*

  //Cuts a duplicate of an antecedent at the end of the sequent
  def dupL(i:Int) = new SingleGoalDependentTactic("dup L") {
    override def computeExpr(seq: Sequent): BelleExpr = {
      assert(i<0 && seq.ante.length>= -i)
      cutEZ(seq.ante(-(i+1)), cohide2(i,seq.succ.length+1) & close)
    }
  }

  //Simplified case tactic for binary case on a formula
  @deprecated("Use Idioms.cases((Case(f), ...), (Case(Not(f)), ...)) instead")
  def bCases(f:Formula) : BelleExpr =
    cutEZ(Or(f,Not(f)),cohide(2) & prop) & orL('Llast)

}
