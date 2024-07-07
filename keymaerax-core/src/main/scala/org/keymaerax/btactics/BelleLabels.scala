/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{
  BelleCommitTxLabel,
  BelleLabel,
  BelleLabelTx,
  BelleRollbackTxLabel,
  BelleStartTxLabel,
  BelleSubLabel,
  BelleTopLevelLabel,
}

/**
 * Default labels used by the KeYmaera X tactics. Other labels can be used by the user, but this list of labels makes it
 * easier to match.
 * @author
 *   aplatzer
 */
object BelleLabels {

  /** Starts a label transaction */
  val startTx: BelleLabel = BelleStartTxLabel

  /**
   * Rollback a label transaction started with [[startTx]]; rollback should be followed immediately by a label.
   * {{{
   * label(startTx) & doStuffThatCreatesLabels & label(rollbackTx) & label(useCase)
   * }}}
   */
  val rollbackTx: BelleLabel = BelleRollbackTxLabel

  /**
   * Commit a label transaction started with [[startTx]].
   * {{{
   * label(startTx) & doStuffThatCreatesLabels & label(commitTx)
   * }}}
   */
  val commitTx: BelleLabel = BelleCommitTxLabel

  /** Shorthand for rollback, insert label, commit. */
  def replaceTxWith(l: BelleLabel): BelleLabel = BelleLabelTx(BelleSubLabel(rollbackTx, l.label), None)

  // loop induction
  val useCase: BelleLabel = BelleTopLevelLabel("Post")
  val initCase: BelleLabel = BelleTopLevelLabel("Init")
  val indStep: BelleLabel = BelleTopLevelLabel("Step")

  // fixpoint
  val fixUseCase: BelleLabel = BelleTopLevelLabel("Usefix")
  val fixpoint: BelleLabel = BelleTopLevelLabel("Fixpoint")

  // cuts
  val cutUse: BelleLabel = BelleTopLevelLabel("Use")
  val cutShow: BelleLabel = BelleTopLevelLabel("Show")

  val mrShow: BelleLabel = BelleTopLevelLabel("Show [a]Q")
  val mrUse: BelleLabel = BelleTopLevelLabel("Use Q->P")

  // lemmas
  def lemmaUnproved(name: String): BelleLabel = BelleTopLevelLabel("Lemma " + name)

  // QE
  val QECEX: BelleLabel = BelleTopLevelLabel("QE CEX")

  val dIInit: BelleLabel = BelleTopLevelLabel("dI Init")
  val dIStep: BelleLabel = BelleTopLevelLabel("dI Step")

  // dV existence and derivative
  val dVexists: BelleLabel = BelleTopLevelLabel("dV existence")
  val dVderiv: BelleLabel = BelleTopLevelLabel("dV derivative")
}
