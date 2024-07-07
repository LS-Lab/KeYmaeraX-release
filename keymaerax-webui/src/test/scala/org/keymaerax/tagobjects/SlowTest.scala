/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tagobjects

import org.scalatest.Tag

/**
 * A test that takes a long time to run.
 *
 * Use this instead of [[org.scalatest.tagobjects.Slow]].
 *
 * See also [[ExtremeTest]].
 */
object SlowTest extends Tag("org.keymaerax.tags.SlowTest")
