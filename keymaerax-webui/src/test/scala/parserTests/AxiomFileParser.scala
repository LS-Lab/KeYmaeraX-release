/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXLexer, KeYmaeraXAxiomParser}
import edu.cmu.cs.ls.keymaerax.tags.CheckinTest
import org.scalatest.{PrivateMethodTester, Matchers, FlatSpec}

/**
 * Created by nfulton on 6/18/15.
 * @todo Nathan
 */
@CheckinTest
class AxiomFileParser extends FlatSpec with Matchers with PrivateMethodTester {

  "The AxiomFileParser" should "parse the axiom file" in {
    val axiomFile = edu.cmu.cs.ls.keymaerax.core.AxiomBase.loadAxiomString()
    KeYmaeraXAxiomParser(axiomFile)
  }
}
