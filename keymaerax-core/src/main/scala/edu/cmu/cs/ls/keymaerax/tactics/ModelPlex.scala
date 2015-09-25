/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal, TraverseToPosition}
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl.localQuantifierElimination
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ConstructionTactic, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.instantiateT
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.diffIntroduceConstantT
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{onBranch,locateAnte,locateSucc}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT,cutT,hideT}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper.isFormula
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{NilT,NilPT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tools.Tool
import scala.collection.immutable
import scala.compat.Platform
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
  override def apply(formula: Formula, kind: Symbol, checkProvable: Boolean): Formula = ???

  override def optimizationOneWithSearch: PositionTactic = ???

  override def diamondDiffSolve2DT: PositionTactic = ???

  override def modelplexSequentStyle: PositionTactic = ???

  override def controllerMonitorT(useOptOne: Boolean): Unit = ???

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
