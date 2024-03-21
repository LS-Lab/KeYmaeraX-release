/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.ConfigurableGenerator
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalactic.{AbstractStringUniformity, Uniformity}
import org.scalatest.BeforeAndAfterEach
import org.scalatest.LoneElement._
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Base class for KeYmaera X system tests without tactics need.
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase]]
 */
class SystemTestBase extends AnyFlatSpec with Matchers with BeforeAndAfterEach {

  /** Test setup */
  override def beforeEach(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerator[Formula]()
    Parser
      .parser
      .setAnnotationListener((p: Program, inv: Formula) =>
        generator.products += (p -> (generator.products.getOrElse(p, Nil) :+ inv))
      )
  }

  /* Test teardown */
  override def afterEach(): Unit = { PrettyPrinter.setPrinter(e => e.getClass.getName) }

  /**
   * Removes all whitespace for string comparisons in tests.
   * @example
   *   {{{"My string with whitespace" should equal ("Mystring with whitespace") (after being whiteSpaceRemoved)}}}
   */
  val whiteSpaceRemoved: Uniformity[String] = new AbstractStringUniformity {
    def normalized(s: String): String = s.replaceAll("\\s+", "")
    override def toString: String = "whiteSpaceRemoved"
  }

  def loneSucc(p: ProvableSig): Formula = p.subgoals.loneElement.succ.loneElement
}
