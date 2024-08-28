/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.infrastruct

import org.keymaerax.core.{PrettyPrinter, Variable}
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.parser.KeYmaeraXPrettyPrinter
import org.keymaerax.parser.StringConverter._
import org.keymaerax.{Configuration, FileConfiguration}
import org.scalatest.BeforeAndAfterEach
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/** Tests expression, term, formula, program, sequent augmentors. */
class AugmentorsTests extends AnyFlatSpec with Matchers with BeforeAndAfterEach {

  override protected def beforeEach(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  }

  "Expression augmentor" should "elaborate variables to functions" in {
    "f>0 -> f>=0".asFormula.elaborateToFunctions(Set("f()".asFunction)) shouldBe "f()>0 -> f()>=0".asFormula
    "f>0 -> [x:=f;]f>=0".asFormula.elaborateToFunctions(Set("f()".asFunction)) shouldBe
      "f()>0 -> [x:=f();]f()>=0".asFormula
    // unlike uniform substitution, it should replace literally
    "f>0 -> [prg;]f>=0".asFormula.elaborateToFunctions(Set("f()".asFunction)) shouldBe "f()>0 -> [prg;]f()>=0".asFormula
  }

  it should "complain about mixed variable/function input" in {
    the[AssertionError] thrownBy "x()=1 -> [x:=3;]x<=2".asFormula.elaborateToFunctions(Set("x()".asFunction)) should
      have message
      """assertion failed: Cannot elaborate:
        |  Symbol x used with inconsistent kinds x:Unit->Real,x:Real""".stripMargin
  }

  it should "complain about mixed differential symbol/function input" in {
    the[AssertionError] thrownBy "x=1 -> [{x'=3}]x<=2".asFormula.elaborateToFunctions(Set("x()".asFunction)) should
      have message
      """assertion failed: Cannot elaborate:
        |  Symbol x used with inconsistent kinds x:Real,x':Real""".stripMargin
  }

  it should "complain about mixed variable/function result" in {
    the[AssertionError] thrownBy "x=1 -> [x:=x;]x<=2".asFormula.elaborateToFunctions(Set("x()".asFunction)) should
      have message
      """assertion failed: Elaboration results in inconsistent kinds:
        |  Symbol x used with inconsistent kinds x:Unit->Real,x:Real""".stripMargin
  }

  it should "complain when trying to elaborate in literal bound occurrence" in {
    the[AssertionError] thrownBy
      "x=1 -> [y:=y;x:=x;]x<=2".asPlainFormula.elaborateToFunctions(Set("x()".asPlainFunction)) should have message
      """Elaboration tried replacing x in literal bound occurrence inside x=1->[y:=y;x:=x;]x<=2""".stripMargin
  }

  it should "replace all (rename) variables and differential symbols" in {
    "\\exists x [{x'=-x}][x':=-x;]x>=0".asFormula.replaceAll(Variable("x"), Variable("y")) shouldBe
      "\\exists y [{y'=-y}][y':=-y;]y>=0".asFormula
  }

  it should "not replace bound occurrences with terms" in {
    "\\exists x x>=1".asFormula.replaceAll(Variable("x"), "y+1".asTerm) shouldBe "\\exists x x>=1".asFormula
  }

}
