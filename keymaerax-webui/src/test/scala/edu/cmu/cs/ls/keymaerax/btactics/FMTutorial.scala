/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
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
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/00_stopsignsbfalse.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withQE { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/00_stopsignsbfalse.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/00_stopsignsbfalse.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 2" should "stop in the right place" in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/01_stopsignabstractsb.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/01_stopsignabstractsb.kyt")).mkString)
    val result = db.proveBy(modelContent, tactic)
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "==> m-x>=A/2*ep^2+ep*v".asSequent
    result.subgoals(1) shouldBe "==> m-x>=v^2/(2*b)".asSequent
  }}

  "Example 3" should "be provable with master" in withQE { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/02_stopsign.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/02_stopsign.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/02_stopsign.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 4" should "be provable with master" in withQE { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/03_increasinglydampedoscillator.kyx")).mkString
    db.proveBy(modelContent, master()) shouldBe 'proved
  }}

  it should "be provable from parsed tactic" in withQE { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/03_increasinglydampedoscillator.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/03_increasinglydampedoscillator.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

  "Example 5" should "be provable from parsed tactic" in withQE { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/04_car.kyx")).mkString
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/fm/04_car.kyt")).mkString)
    db.proveBy(modelContent, tactic) shouldBe 'proved
  }}

}
