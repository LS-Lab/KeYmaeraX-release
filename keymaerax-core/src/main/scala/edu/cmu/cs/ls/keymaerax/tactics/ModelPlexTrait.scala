/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.{Term, Formula, Variable}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic

/**
 * Created by nfulton on 9/25/15.
 */
trait ModelPlexTrait extends ((List[Variable], Symbol) => (Formula => Formula)) {
  def apply(formula: Formula, kind: Symbol, checkProvable: Boolean = true): Formula
  def apply(vars: List[Variable], kind: Symbol): (Formula => Formula)
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Boolean): (Formula => Formula)
  def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): Formula
  def controllerMonitorByChase: PositionTactic
  def modelplexSequentStyle: PositionTactic
  def modelplexAxiomaticStyle(useOptOne: Boolean)(unprog: Boolean => PositionTactic): PositionTactic
  def controllerMonitorT(useOptOne: Boolean): PositionTactic
  def modelMonitorT(useOptOne: Boolean): PositionTactic
  def diamondDiffSolve2DT: PositionTactic
  def diamondTestRetainConditionT: PositionTactic
  def locateT(tactics: List[PositionTactic]): PositionTactic
  def optimizationOneWithSearch: PositionTactic
  def optimizationOne(inst: Option[(Variable, Term)] = None): PositionTactic
}