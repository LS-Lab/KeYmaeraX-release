/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tagobjects

import org.scalatest.Tag

// TODO Tag every ExtremeTest as SlowTest?

/**
 * A test that takes a ''very'' long time to run.
 *
 * See also [[SlowTest]].
 */
object ExtremeTest extends Tag("org.keymaerax.tags.ExtremeTest")
