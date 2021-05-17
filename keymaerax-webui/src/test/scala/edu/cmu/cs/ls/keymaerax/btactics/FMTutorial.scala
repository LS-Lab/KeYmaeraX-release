/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
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
    val modelContent = ArchiveParser.getEntry("FM16/Tutorial Example 1", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get.fileContent
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 2" should "stop in the right place" in withMathematica { _ => withDatabase { db =>
    val entry = ArchiveParser.getEntry("FM16/Tutorial Example 2", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get
    val modelContent = entry.fileContent
    val tactic = entry.tactics.head._3
    val result = db.proveBy(modelContent, tactic)
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x<=m, A>=0, b>0, ep>0, m-x>=sb, t=0 ==> m-x>=A/2*ep^2+ep*v".asSequent
    result.subgoals(1) shouldBe "x<=m, A>=0, b>0, ep>0, t=0 ==> m-x>=v^2/(2*b)".asSequent
  }}

  "Example 3" should "be provable with master" in withQE { _ => withDatabase { db =>
    val modelContent = ArchiveParser.getEntry("FM16/Tutorial Example 3", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get.fileContent
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 4" should "be provable with master" in withQE { _ => withDatabase { db =>
    val modelContent = ArchiveParser.getEntry("FM16/Tutorial Example 4", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get.fileContent
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  "Example 5" should "be provable with tactic" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("FM16/Tutorial Example 5", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get
    proveBy(entry.expandedModel.asInstanceOf[Formula], entry.tactics.head._3) shouldBe 'proved
  }

}
