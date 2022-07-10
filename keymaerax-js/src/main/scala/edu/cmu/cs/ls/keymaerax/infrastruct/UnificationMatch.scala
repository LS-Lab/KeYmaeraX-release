/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core._

object UnificationMatch {
  type Subst
  def unifiable(shape: Expression, input: Expression): Option[Subst] = None
}