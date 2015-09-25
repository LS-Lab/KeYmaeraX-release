/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.{Variable, Term, Formula}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic

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

  override def apply(formula: Formula, kind: Symbol, checkProvable: Boolean): Formula = ???

  override def optimizationOneWithSearch: PositionTactic = ???

  override def diamondDiffSolve2DT: PositionTactic = ???

  override def modelplexSequentStyle: PositionTactic = ???

  override def controllerMonitorT(useOptOne: Boolean): PositionTactic = ???

  override def optimizationOne(inst: Option[(Variable, Term)]): PositionTactic = ???

  override def modelMonitorT(useOptOne: Boolean): PositionTactic = ???

  override def modelplexAxiomaticStyle(useOptOne: Boolean)(unprog: (Boolean) => PositionTactic): PositionTactic = ???

  override def locateT(tactics: List[PositionTactic]): PositionTactic = ???

  override def apply(vars: List[Variable], kind: Symbol): (Formula) => Formula = ???

  override def apply(vars: List[Variable], kind: Symbol, checkProvable: Boolean): (Formula) => Formula = ???

  override def controllerMonitorByChase: PositionTactic = ???

  override def diamondTestRetainConditionT: PositionTactic = ???

  override def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): Formula = ???
}
