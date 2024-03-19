/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tagobjects

import org.scalatest.Tag

// TODO Tag every ExtremeTest as SlowTest?

/**
 * A test that takes a ''very'' long time to run.
 *
 * See also [[SlowTest]].
 */
object ExtremeTest extends Tag("edu.cmu.cs.ls.keymaerax.tags.ExtremeTest")
