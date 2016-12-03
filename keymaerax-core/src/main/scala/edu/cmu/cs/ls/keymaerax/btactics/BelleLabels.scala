/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleTopLevelLabel

/**
  * Created by aplatzer on 1/25/16.
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
}
