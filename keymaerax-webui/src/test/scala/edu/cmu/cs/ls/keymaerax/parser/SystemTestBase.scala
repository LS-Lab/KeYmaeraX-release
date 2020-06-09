package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerator, DerivationInfoRegistry}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalactic.{AbstractStringUniformity, Uniformity}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}


/**
 * Base class for KeYmaera X system tests without tactics need.
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase]]
 */
class SystemTestBase extends FlatSpec with Matchers with BeforeAndAfterEach {

  /** Test setup */
  override def beforeEach() = {
    DerivationInfoRegistry.init
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) =>
      generator.products += (p->(generator.products.getOrElse(p, Nil) :+ inv)))
  }

  /* Test teardown */
  override def afterEach() = {
    PrettyPrinter.setPrinter(e => e.getClass.getName)
  }


  /** Removes all whitespace for string comparisons in tests.
    * @example {{{
    *     "My string with     whitespace" should equal ("Mystring   with whitespace") (after being whiteSpaceRemoved)
    * }}}
    */
  val whiteSpaceRemoved: Uniformity[String] =
    new AbstractStringUniformity {
      def normalized(s: String): String = s.replaceAll("\\s+", "")
      override def toString: String = "whiteSpaceRemoved"
    }

  def loneSucc(p: ProvableSig) = {
    assert(p.subgoals.length==1)
    assert(p.subgoals.last.succ.length==1)
    p.subgoals.last.succ.last
  }
}
