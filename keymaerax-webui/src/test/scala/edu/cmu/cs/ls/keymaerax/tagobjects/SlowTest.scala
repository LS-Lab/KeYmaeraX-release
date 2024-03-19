/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tagobjects

import org.scalatest.Tag

/**
 * A test that takes a long time to run.
 *
 * Use this instead of [[org.scalatest.tagobjects.Slow]].
 */
object SlowTest extends Tag("edu.cmu.cs.ls.keymaerax.tags.SlowTest")
