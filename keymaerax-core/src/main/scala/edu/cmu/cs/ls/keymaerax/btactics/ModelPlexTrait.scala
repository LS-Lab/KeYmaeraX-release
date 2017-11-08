/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic
import edu.cmu.cs.ls.keymaerax.core.{Formula, Term, Variable}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.SimplificationTool

/**
 * ModelPlex: Verified runtime validation of verified cyber-physical system models.
 * @author Stefan Mitsch
 * @author Andre Platzer
 * @see Stefan Mitsch and André Platzer. [[http://dx.doi.org/10.1007/s10703-016-0241-z ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *      Formal Methods in System Design, 42 pp. 2016. Special issue for selected papers from RV'14.
 * @see Stefan Mitsch and André Platzer. [[http://dx.doi.org/10.1007/978-3-319-11164-3_17 ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *      In Borzoo Bonakdarpour and Scott A. Smolka, editors, Runtime Verification - 5th International Conference, RV 2014, Toronto, ON, Canada, September 22-25, 2014. Proceedings, volume 8734 of LNCS, pages 199-214. Springer, 2014.
 */
trait ModelPlexTrait extends ((List[Variable], Symbol) => (Formula => Formula)) {
  def apply(formula: Formula, kind: Symbol, checkProvable: Option[(ProvableSig => Unit)] = Some({case _ => ()})): Formula
  def apply(vars: List[Variable], kind: Symbol): (Formula => Formula)
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Option[(ProvableSig => Unit)]): (Formula => Formula)
  def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): (Formula, List[Formula])
  def controllerMonitorByChase: DependentPositionTactic
  def modelplexSequentStyle: DependentPositionTactic
  def modelplexAxiomaticStyle(useOptOne: Boolean)(unprog: Boolean => DependentPositionTactic): DependentPositionTactic
  def controllerMonitorT(useOptOne: Boolean): DependentPositionTactic
  def modelMonitorT(useOptOne: Boolean): DependentPositionTactic
  def diamondDiffSolve2DT: DependentPositionTactic
  def diamondTestRetainConditionT: DependentPositionTactic
  def locateT(tactics: List[DependentPositionTactic]): DependentPositionTactic
  def optimizationOneWithSearch(tool: Option[SimplificationTool], assumptions: List[Formula]): DependentPositionTactic
  def optimizationOne(inst: Option[(Variable, Term)] = None): DependentPositionTactic
}