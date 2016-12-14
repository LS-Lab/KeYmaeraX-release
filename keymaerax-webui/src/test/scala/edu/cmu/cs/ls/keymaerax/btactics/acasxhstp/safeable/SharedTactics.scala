/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, EqualityTactics, Idioms}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Formula, Number, Variable}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

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

}
