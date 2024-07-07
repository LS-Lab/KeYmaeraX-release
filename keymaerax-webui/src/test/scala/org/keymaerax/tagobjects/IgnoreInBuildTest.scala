/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tagobjects

import org.scalatest.Tag

// TODO We're not using Jenkins any more
/** A test that should be ignored in an automated build via Jenkins. */
object IgnoreInBuildTest extends Tag("org.keymaerax.tags.IgnoreInBuildTest")
