/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic
import edu.cmu.cs.ls.keymaerax.core.{Formula, Term, Variable}

trait ModelPlexTrait extends ((List[Variable], Symbol) => (Formula => Formula)) {
  def apply(formula: Formula, kind: Symbol, checkProvable: Boolean = true): Formula
  def apply(vars: List[Variable], kind: Symbol): (Formula => Formula)
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Boolean): (Formula => Formula)
  def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): Formula
  def controllerMonitorByChase: DependentPositionTactic
  def modelplexSequentStyle: DependentPositionTactic
  def modelplexAxiomaticStyle(useOptOne: Boolean)(unprog: Boolean => DependentPositionTactic): DependentPositionTactic
  def controllerMonitorT(useOptOne: Boolean): DependentPositionTactic
  def modelMonitorT(useOptOne: Boolean): DependentPositionTactic
  def diamondDiffSolve2DT: DependentPositionTactic
  def diamondTestRetainConditionT: DependentPositionTactic
  def locateT(tactics: List[DependentPositionTactic]): DependentPositionTactic
  def optimizationOneWithSearch: DependentPositionTactic
  def optimizationOne(inst: Option[(Variable, Term)] = None): DependentPositionTactic
}