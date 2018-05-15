/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleTopLevelLabel

/**
  * Default labels used by the KeYmaera X tactics.
  * Other labels can be used by the user, but this list of labels makes it easier to match.
  * @author aplatzer
  */
object BelleLabels {
  // loop induction
  val useCase = BelleTopLevelLabel("Use case")
  val initCase = BelleTopLevelLabel("Init case")
  val indStep = BelleTopLevelLabel("Induction step")

  // cuts
  val cutUse = BelleTopLevelLabel("Cut use")
  val cutShow = BelleTopLevelLabel("Cut show")

  // QE
  val QECEX = BelleTopLevelLabel("QE CEX")
}
