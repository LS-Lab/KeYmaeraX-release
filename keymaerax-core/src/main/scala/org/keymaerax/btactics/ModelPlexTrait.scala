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
 *   [[org.keymaerax.Bibliography.FmsdMitschP16]]
 * @see
 *   [[org.keymaerax.Bibliography.RvMitschP14]]
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
      unobservable: ListMap[_ <: NamedSymbol, Option[Formula]] = ListMap.empty,
  ): Formula
  def apply(vars: List[Variable], kind: ModelPlexKind.Value): Formula => Formula
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
