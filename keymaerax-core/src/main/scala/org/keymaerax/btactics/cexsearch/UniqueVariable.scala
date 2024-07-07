/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.cexsearch

import org.keymaerax.core.Variable

/** Created by bbohrer on 4/24/16. */
object UniqueVariable {
  private var theIndex = 0
  private val theName = "secretvariable"
  def make = {
    theIndex = theIndex + 1
    Variable(theName + theIndex + "_")
  }
}
