/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic
import edu.cmu.cs.ls.keymaerax.btactics.ModelPlex.NAMED_POST_VAR
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Formula, NamedSymbol, Term, Variable}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.SimplificationTool

import scala.collection.immutable.ListMap

/** A ModelPlex conjecture. The `constAssumptions` are a subset of `init` for variables/function symbols not bound in the program. */
case class ModelPlexConjecture(init: Formula, conjecture: Formula, constAssumptions: List[Formula])

/**
 * ModelPlex: Verified runtime validation of verified cyber-physical system models.
 * @author Stefan Mitsch
 * @author Andre Platzer
 * @see Stefan Mitsch and André Platzer. [[https://doi.org/10.1007/s10703-016-0241-z ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *      Formal Methods in System Design, 42 pp. 2016. Special issue for selected papers from RV'14.
 * @see Stefan Mitsch and André Platzer. [[https://doi.org/10.1007/978-3-319-11164-3_17 ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *      In Borzoo Bonakdarpour and Scott A. Smolka, editors, Runtime Verification - 5th International Conference, RV 2014, Toronto, ON, Canada, September 22-25, 2014. Proceedings, volume 8734 of LNCS, pages 199-214. Springer, 2014.
 */
trait ModelPlexTrait extends ((List[Variable], Symbol) => (Formula => Formula)) {
  /** Returns the post variable of `v` identified by name postfix `post`. */
  val NAMED_POST_VAR: Variable=>Variable = (v: Variable) => BaseVariable(v.name + "post", v.index)
  /** Returns the post variable of `v` identified by index increase. */
  val INDEXED_POST_VAR: Variable=>Variable = (v: Variable) => BaseVariable(v.name, Some(v.index.map(_ + 1).getOrElse(0)))

  def apply(formula: Formula, kind: Symbol, checkProvable: Option[ProvableSig => Unit] = Some(_ => ()),
            unobservable: ListMap[_ <: NamedSymbol, Option[Formula]] = ListMap.empty): Formula
  def apply(vars: List[Variable], kind: Symbol): Formula => Formula = apply(vars, kind, checkProvable=Some(_ => ()))
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Option[ProvableSig => Unit]): Formula => Formula
  def createMonitorSpecificationConjecture(fml: Formula, vars: List[Variable],
                                           unobservable: ListMap[_ <: NamedSymbol, Option[Formula]],
                                           postVar: Variable=>Variable = NAMED_POST_VAR): ModelPlexConjecture
  def controllerMonitorByChase: DependentPositionTactic
  def modelplexSequentStyle: DependentPositionTactic
  def modelplexAxiomaticStyle(unprog: DependentPositionTactic): DependentPositionTactic
  def controllerMonitorT: DependentPositionTactic
  def modelMonitorT: DependentPositionTactic
  def diamondDiffSolve2DT: DependentPositionTactic
  def diamondTestRetainConditionT: DependentPositionTactic
  def locateT(tactics: List[DependentPositionTactic]): DependentPositionTactic
  def optimizationOneWithSearch(tool: Option[SimplificationTool], assumptions: List[Formula],
                                unobservable: List[_ <: NamedSymbol], simplifier: Option[DependentPositionTactic],
                                postVar: Variable=>Variable = NAMED_POST_VAR): DependentPositionTactic
}