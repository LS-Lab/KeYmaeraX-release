/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{AtPosition, BelleExpr, BuiltInPositionTactic, DependentPositionTactic}
import org.keymaerax.core.{BaseVariable, Formula, NamedSymbol, Variable}
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tools.ext.SimplificationTool

import scala.collection.immutable.ListMap

// TODO Replace with Scala 3 enum
object ModelPlexKind extends Enumeration {
  val Ctrl, Model = Value
}

/**
 * A ModelPlex conjecture. The `constAssumptions` are a subset of `init` for variables/function symbols not bound in the
 * program.
 */
case class ModelPlexConjecture(init: Formula, conjecture: Formula, constAssumptions: List[Formula])

/**
 * ModelPlex: Verified runtime validation of verified cyber-physical system models.
 * @author
 *   Stefan Mitsch
 * @author
 *   Andre Platzer
 * @see
 *   Stefan Mitsch and André Platzer.
 *   [[https://doi.org/10.1007/s10703-016-0241-z ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *   Formal Methods in System Design, 42 pp. 2016. Special issue for selected papers from RV'14.
 * @see
 *   Stefan Mitsch and André Platzer.
 *   [[https://doi.org/10.1007/978-3-319-11164-3_17 ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *   In Borzoo Bonakdarpour and Scott A. Smolka, editors, Runtime Verification - 5th International Conference, RV 2014,
 *   Toronto, ON, Canada, September 22-25, 2014. Proceedings, volume 8734 of LNCS, pages 199-214. Springer, 2014.
 */
trait ModelPlexTrait extends ((List[Variable], ModelPlexKind.Value) => (Formula => Formula)) {

  /** Returns the post variable of `v` identified by name postfix `post`. */
  val NAMED_POST_VAR: Variable => Variable = (v: Variable) =>
    BaseVariable(if (v.name.endsWith("_")) v.name.stripSuffix("_") + "post_" else v.name + "post", v.index)

  /** Returns the post variable of `v` identified by index increase. */
  val INDEXED_POST_VAR: Variable => Variable =
    (v: Variable) => BaseVariable(v.name, Some(v.index.map(_ + 1).getOrElse(0)))

  def apply(
      formula: Formula,
      kind: ModelPlexKind.Value,
      checkProvable: Option[ProvableSig => Unit] = Some(_ => ()),
      unobservable: ListMap[_ <: NamedSymbol, Option[Formula]] = ListMap.empty,
  ): Formula
  def apply(vars: List[Variable], kind: ModelPlexKind.Value): Formula => Formula =
    apply(vars, kind, checkProvable = Some(_ => ()))
  def apply(
      vars: List[Variable],
      kind: ModelPlexKind.Value,
      checkProvable: Option[ProvableSig => Unit],
  ): Formula => Formula
  def createMonitorSpecificationConjecture(
      fml: Formula,
      vars: List[Variable],
      unobservable: ListMap[_ <: NamedSymbol, Option[Formula]],
      postVar: Variable => Variable = NAMED_POST_VAR,
  ): ModelPlexConjecture
  def controllerMonitorByChase: BuiltInPositionTactic
  def modelplexSequentStyle: DependentPositionTactic
  def modelplexAxiomaticStyle(unprog: DependentPositionTactic): DependentPositionTactic
  def controllerMonitorT: DependentPositionTactic
  def modelMonitorT: DependentPositionTactic
  def diamondDiffSolve2DT: DependentPositionTactic
  def diamondTestRetainConditionT: DependentPositionTactic
  def locateT(tactics: List[AtPosition[_ <: BelleExpr]]): DependentPositionTactic
  def optimizationOneWithSearch(
      tool: Option[SimplificationTool],
      assumptions: List[Formula],
      unobservable: List[_ <: NamedSymbol],
      simplifier: Option[BuiltInPositionTactic],
      postVar: Variable => Variable = NAMED_POST_VAR,
  ): DependentPositionTactic
}
