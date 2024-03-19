/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package testHelper

/**
 * Test categories.
 * @todo
 *   Figure out a way to specify timeouts for certain tags.
 * @author
 *   Nathan Fulton Created by nfulton on 9/11/15.
 */
object KeYmaeraXTestTags {

  /** An advocatus diavoli test that's sceptical about soundness. */
  object AdvocatusTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest")
}
