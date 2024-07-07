/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package org.keymaerax.infrastruct

import org.keymaerax.core._

object UnificationMatch {
  type Subst
  def unifiable(shape: Expression, input: Expression): Option[Subst] = None
}
