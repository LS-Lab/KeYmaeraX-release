package testHelper

/**
 * @todo Figure out a way to specify timeouts for certain tags.
 * @author @nrfulton
 * Created by nfulton on 9/11/15.
 */
object KeYmaeraXTestTags {

  /**
   * Usually tests that call QE or test a lot of cases.
   * Set runs for unbounded amount of time.
   */
  object SlowTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.SlowTest")

  /**
   * A small core of very fasts tests that could be run before each check-in or even every compile.
   * Each test should run in under :30 seconds
   * Set runs in a minute or two.
   */
  object CheckinTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.CheckinTest")

  /**
   * A test that summarizes all of the tests occuring in a package or file.
   * These tests definitely get run before *pushing* any code to GitHub in a normal development process.
   * Set runs in under 15 minutes.
   */
  object SummaryTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.SummaryTest")

  /**
   * Case Study tests are (typically long-running) tests that run an entire case study, sometimes
   * step-by-step.
   * Set runs for unbounded amount of time.
   */
  object CaseStudyTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.CaseStudyTest")

  /**
   * A user-interface test.
   */
  object UITest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.UITest")

  /**
   * Tests the persistence layer (DB, caches, etc.)
   */
  object PersistenceTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.UITest")

  /**
   * Tests that only make sense to run pre-deployment.
   */
  object DeploymentTest extends org.scalatest.Tag("edu.cmu.cs.ls.keymaerax.tags.Deployment")


}
