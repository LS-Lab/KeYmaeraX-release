/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic
import edu.cmu.cs.ls.keymaerax.core.{Formula, Term, Variable}

import scala.language.postfixOps

/**
 * ModelPlex: Verified runtime validation of verified cyber-physical system models.
 * Created by smitsch on 3/6/15.
 * @author Stefan Mitsch
 * @author Andre Platzer
 * @see "Stefan Mitsch and André Platzer. ModelPlex: Verified runtime validation of verified cyber-physical system models.
In Borzoo Bonakdarpour and Scott A. Smolka, editors, Runtime Verification - 5th International Conference, RV 2014, Toronto, ON, Canada, September 22-25, 2014. Proceedings, volume 8734 of LNCS, pages 199-214. Springer, 2014."
 */
object ModelPlex extends ModelPlexTrait {
  class ProprietaryCodeException()
    extends Exception("This code is proprietary and is not shipped with the GPL'd portion of KeYnmaera X. Please email the KeYmaera X developers for more information about ModelPlex")

  def ??? = throw new ProprietaryCodeException()

  def apply(formula: Formula, kind: Symbol, checkProvable: Boolean = true): Formula = ???
  def apply(vars: List[Variable], kind: Symbol): (Formula => Formula) = ???
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Boolean): (Formula => Formula) = ???
  def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): Formula = ???
  def controllerMonitorByChase: DependentPositionTactic = ???
  def modelplexSequentStyle: DependentPositionTactic = ???
  def modelplexAxiomaticStyle(useOptOne: Boolean)(unprog: Boolean => DependentPositionTactic): DependentPositionTactic = ???
  def controllerMonitorT(useOptOne: Boolean): DependentPositionTactic = ???
  def modelMonitorT(useOptOne: Boolean): DependentPositionTactic = ???
  def diamondDiffSolve2DT: DependentPositionTactic = ???
  def diamondTestRetainConditionT: DependentPositionTactic = ???
  def locateT(tactics: List[DependentPositionTactic]): DependentPositionTactic = ???
  def optimizationOneWithSearch: DependentPositionTactic = ???
  def optimizationOne(inst: Option[(Variable, Term)] = None): DependentPositionTactic = ???
}
