/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.USubstTest
import testHelper.CustomAssertions.withSafeClue
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach, FlatSpec, Matchers}

import scala.collection.immutable.{List, Seq, Set}
import scala.util.Random
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq
import scala.concurrent.duration.Duration

/**
 * @author Andre Platzer
 * @note Test needs KeYmaereaXParser.LAX==true
 */
@USubstTest
class USubstPerformanceTests extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll {

  val randomTrials = 200
  val randomComplexity = 10
  val randomSubstitutions = 5
  val rand = new RandomFormula()

  val yellAtClash = true

  /** Test setup */
  override def beforeEach() = {
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    //KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => None)
  }

  /* Test teardown */
  override def afterEach() = {
    PrettyPrinter.setPrinter(e => e.getClass.getName)
  }

  override def afterAll(): Unit = {
    println("RandomFormula(" + rand.seed + "L) seed will regenerate this class's random sequence\n\n")
    super.afterAll()
  }

  private def print(s: => String): Unit = {
    println(s)
  }


  "USubst performance" should "substitute random formulas with random admissible uniform substitutions" in {
    var us1duration = 0L
    var us2duration = 0L
    for (k <- 1 to randomTrials) {
      val fml = rand.nextF(rand.nextNames("z", randomComplexity / 3 + 1), randomComplexity,
        modals=true, dotTs=false, dotFs=false, diffs=false, funcs=true, duals=true)
      for (i <- 1 to randomSubstitutions) {
        val randClue = "Uniform substitution produced for " + fml + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        val us = withSafeClue("Error generating uniform substitution\n\n" + randClue) {
          rand.nextAdmissibleUSubst(fml, randomComplexity, false)
        }

        withSafeClue("Random substitution " + us + "\n\n" + randClue) {
          print("usubst:  " + us)
          print("formula: " + fml)
          val t10 = System.nanoTime()
          val r = try { Some(USubst(us.subsDefsInput)(fml)) } catch {case e:SubstitutionClashException=> None}
          us1duration += System.nanoTime()-t10
          print("result:  " + r.getOrElse("clash"))
          val t20 = System.nanoTime()
          var r2 = try { Some(USubstChurch(us.subsDefsInput)(fml)) } catch {case e:SubstitutionClashException=> None}
          us2duration += System.nanoTime()-t20
          print("result:  " + r2.getOrElse("clash"))
          r shouldBe r2
          if (yellAtClash) Some(USubst(us.subsDefsInput)(fml))
          print("")
        }
      }
    }
    println()
    println("===================================")
    println()
    printf("USubstOne duration:   \t%9d ms\n", Duration.fromNanos(us1duration).toMillis)
    printf("USubstChurch duration:\t%9d ms\n", Duration.fromNanos(us2duration).toMillis)
    println()
    //println("RandomFormula(" + rand.seed + "L) seed will regenerate this class's random sequence\n\n")
  }
}
