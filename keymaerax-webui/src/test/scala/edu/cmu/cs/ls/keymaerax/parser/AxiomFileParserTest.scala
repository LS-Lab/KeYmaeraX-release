/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.CheckinTest
import org.scalatest.{PrivateMethodTester, Matchers, FlatSpec}

/**
  * @author Nathan Fulton
 */
@CheckinTest
class AxiomFileParser extends FlatSpec with Matchers with PrivateMethodTester {
  val loadAxiomString = PrivateMethod[String]('loadAxiomString)

  "The AxiomFileParser" should "parse the axiom file" in {
    // even AxiomBase is private[core], so get Class by Java reflection
    val clazz = Class.forName("edu.cmu.cs.ls.keymaerax.core.AxiomBase$")
    val axiomFile = clazz.getField("MODULE$").get() invokePrivate loadAxiomString()
    val axioms = KeYmaeraXAxiomParser(axiomFile)
    axioms.size shouldNot be <= 0
    // check for a sample
    axioms should contain ("<> diamond", "![a;]!p(||) <-> <a;>p(||)".asFormula)
  }
}
