/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

import scala.language.postfixOps

/**
 * Tutorial test cases.
 *
 * @author Stefan Mitsch
 */
@SlowTest
class FMTutorial extends TacticTestBase {

  "Example 1" should "be provable with master" in withQE { _ => withDatabase { db =>
    val modelContent = KeYmaeraXArchiveParser.getEntry("Formal Methods Tutorial Example 1", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get.fileContent
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 2" should "stop in the right place" in withMathematica { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("Formal Methods Tutorial Example 2", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get
    val modelContent = entry.fileContent
    val tactic = entry.tactics.head._2
    val result = db.proveBy(modelContent, tactic)
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "==> m-x>=A/2*ep^2+ep*v".asSequent
    result.subgoals(1) shouldBe "==> m-x>=v^2/(2*b)".asSequent
  }}

  "Example 3" should "be provable with master" in withQE { _ => withDatabase { db =>
    val modelContent = KeYmaeraXArchiveParser.getEntry("Formal Methods Tutorial Example 3", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get.fileContent
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 4" should "be provable with master" in withQE { _ => withDatabase { db =>
    val modelContent = KeYmaeraXArchiveParser.getEntry("Formal Methods Tutorial Example 4", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get.fileContent
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

}
