/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, StaticSemanticsTools}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}
import scala.collection.immutable

import scala.collection.immutable._
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}

/**
 * Tests basic expression data structures
  *
 * @author Andre Platzer
 */
class ExpressionTests extends FlatSpec with Matchers {
  "Expressions" should "refuse empty names" in {
    a [CoreException] shouldBe thrownBy(new Variable("",None,Real))
    a [CoreException] shouldBe thrownBy(new Function("",None,Unit,Real))
    a [CoreException] shouldBe thrownBy(new ProgramConst(""))
    a [CoreException] shouldBe thrownBy(new DifferentialProgramConst("", ???))
  }

  it should "refuse names with primes" in {
    a [CoreException] shouldBe thrownBy(new Variable("x'",None,Real))
    a [CoreException] shouldBe thrownBy(new DifferentialSymbol(new Variable("x'",None,Real)))
    a [CoreException] shouldBe thrownBy(new Function("x'",None,Unit,Real))
    a [CoreException] shouldBe thrownBy(new ProgramConst("x'"))
    a [CoreException] shouldBe thrownBy(new DifferentialProgramConst("x'", ???))
  }

  it should "refuse names with inner underscores to avoid confusion with name.index" in {
    a [CoreException] shouldBe thrownBy(new Variable("x_1",None,Real))
    a [CoreException] shouldBe thrownBy(new DifferentialSymbol(new Variable("x_1",None,Real)))
    a [CoreException] shouldBe thrownBy(new Function("x_1",None,Unit,Real))
    a [CoreException] shouldBe thrownBy(new ProgramConst("x_1"))
    a [CoreException] shouldBe thrownBy(new DifferentialProgramConst("x_1", ???))
  }

  it should "refuse names with middle inner underscores to avoid confusion with name.index" in {
    a [CoreException] shouldBe thrownBy(new Variable("x_a",None,Real))
    a [CoreException] shouldBe thrownBy(new DifferentialSymbol(new Variable("x_a",None,Real)))
    a [CoreException] shouldBe thrownBy(new Function("x_a",None,Unit,Real))
    a [CoreException] shouldBe thrownBy(new ProgramConst("x_a"))
    a [CoreException] shouldBe thrownBy(new DifferentialProgramConst("x_a", ???))
  }

  it should "refuse names with negative index" in {
    a [IllegalArgumentException] shouldBe thrownBy(new Variable("x",Some(-1),Real))
    a [IllegalArgumentException] shouldBe thrownBy(new DifferentialSymbol(new Variable("x",Some(-1),Real)))
    a [IllegalArgumentException] shouldBe thrownBy(new Function("x",Some(-1),Unit,Real))
  }

  it should "support reapplying pairs" in {
    Pair(Number(5),Number(7)).reapply(Number(5),Number(7)) shouldBe Pair(Number(5),Number(7))
    Pair(Number(5),Number(7)).reapply(Number(-2),Number(-7)) shouldBe Pair(Number(-2),Number(-7))
  }
}
