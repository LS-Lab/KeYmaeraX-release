/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleLabel, BelleRollbackLabel, BelleSubLabel, BelleTopLevelLabel}

/**
  * Default labels used by the KeYmaera X tactics.
  * Other labels can be used by the user, but this list of labels makes it easier to match.
  * @author aplatzer
  */
object BelleLabels {
  val rollback: BelleLabel = BelleRollbackLabel
  /** Creates a label that first rolls back to the last transaction start, then appends label `l`. */
  def rollbackAndAdd(l: BelleLabel): BelleLabel = BelleSubLabel(rollback, l.label)

  // loop induction
  val useCase: BelleLabel = BelleTopLevelLabel("Post")
  val initCase: BelleLabel = BelleTopLevelLabel("Init")
  val indStep: BelleLabel = BelleTopLevelLabel("Step")

  // cuts
  val cutUse: BelleLabel = BelleTopLevelLabel("Use")
  val cutShow: BelleLabel = BelleTopLevelLabel("Show")

  // lemmas
  def lemmaUnproved(name: String): BelleLabel = BelleTopLevelLabel("Lemma " + name)

  // QE
  val QECEX: BelleLabel = BelleTopLevelLabel("QE CEX")

  val dIInit: BelleLabel = BelleTopLevelLabel("dI Init")
  val dIStep: BelleLabel = BelleTopLevelLabel("dI Step")
}
