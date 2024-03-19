/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package testHelper

import org.scalatest.Tag

/**
 * Test categories.
 * @todo
 *   Figure out a way to specify timeouts for certain tags.
 * @author
 *   Nathan Fulton Created by nfulton on 9/11/15.
 */
object KeYmaeraXTestTags {

  /** A user-interface test. */
  object UITest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.UITest")

  /** Tests the persistence layer (DB, caches, etc.) */
  object PersistenceTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.UITest")

  /** Tests that only make sense to run pre-deployment. */
  object DeploymentTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.Deployment")

  /** Uniform substitution tests */
  object USubstTest extends Tag("edu.cmu.cs.ls.keymaerax.tags.USubstTest")

  /** Tests that are overly optimistic about the capabilities and might want to be ignored. */
  object OptimisticTest extends Tag("edu.cmu.cs.ls.keymaerax.tags.OptimisticTest")

  /** Tests that are obsolete, e.g. from old tactic framework. */
  object ObsoleteTest extends Tag("edu.cmu.cs.ls.keymaerax.tags.ObsoleteTest")

  /** Tests that should be ignored in an automated build via Jenkins. */
  object IgnoreInBuildTest extends Tag("edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest")

  /** Tests codifying todo's. These may be ignored and should be un-ignored occasionally. */
  object TodoTest extends Tag("edu.cmu.cs.ls.keymaerax.tags.TodoTest")

  /** Tests of unfixed bugs. */
  object NotfixedTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.NotfixedTest")

  /** Tests that are added for coverage analysis and not critically used. */
  object CoverageTest extends Tag("edu.cmu.cs.ls.keymaerax.tags.CoverageTest")

  /** An advocatus diavoli test that's sceptical about soundness. */
  object AdvocatusTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest")
}
