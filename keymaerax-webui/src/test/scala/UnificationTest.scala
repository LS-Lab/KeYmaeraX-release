/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Unification
import scala.collection.immutable._
import org.scalatest.{Matchers, FlatSpec}


/**
 * Created by aplatzer on 7/28/15.
 * @author aplatzer
 */
class UnificationTest extends FlatSpec with Matchers {

  "Unification terms" should "unify f() with x^2+y" in {
    Unification("f()".asTerm, "x^2+y".asTerm) shouldBe USubst(
      SubstitutionPair("f()".asTerm, "x^2+y".asTerm) :: Nil)
  }

  it should "unify f(x) with x^2+y" in {
    Unification("f(x)".asTerm, "x^2+y".asTerm) shouldBe USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil)
  }

  it should "unify 3+f() with 3+(x^2+y)" in {
    Unification("3+f()".asTerm, "3+(x^2+y)".asTerm) shouldBe USubst(
      SubstitutionPair("f()".asTerm, "x^2+y".asTerm) :: Nil)
  }

  it should "unify 3+f(x) with 3+(x^2+y)" in {
    Unification("3+f(x)".asTerm, "3+(x^2+y)".asTerm) shouldBe USubst(
      SubstitutionPair("f(.)".asTerm, "(.)^2+y".asTerm) :: Nil)
  }


  "Unification formulas" should "unify p() with x^2+y>=0" in {
    Unification("p()".asFormula, "x^2+y>=0".asFormula) shouldBe USubst(
      SubstitutionPair("p()".asFormula, "x^2+y>=0".asFormula) :: Nil)
  }


  "Unification programs" should "unify [a;]x>=0 with [x:=x+5;]x>=0" in {
    Unification("[a;]x>=0".asFormula, "[x:=x+5;]x>=0".asFormula) shouldBe USubst(
      SubstitutionPair("a;".asProgram, "x:=x+5;".asProgram) :: Nil)
  }

  it should "unify [a;x:=7;]x>=0 with [x:=x+5;x:=7;]x>=0" in {
    Unification("[a;x:=7;]x>=0".asFormula, "[x:=x+5;x:=7;]x>=0".asFormula) shouldBe USubst(
      SubstitutionPair("a;".asProgram, "x:=x+5;".asProgram) :: Nil)
  }
}
