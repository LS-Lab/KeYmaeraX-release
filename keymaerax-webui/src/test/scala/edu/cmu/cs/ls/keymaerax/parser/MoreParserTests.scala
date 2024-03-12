/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

/**
 * Created by nfulton on 2/23/15.
 *
 * @author
 *   Nathan Fulton
 */
class ArithmeticParserTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  private val one = Number(1)
  private val two = Number(2)
  private val three = Number(3)
  private val six = Number(6)

  override def beforeEach(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  }

  override def afterEach(): Unit = { PrettyPrinter.setPrinter(e => e.getClass.getName) }

  "Add" should "print/parse correctly -- left" in {
    val t = Plus(one, Plus(two, three))
    t.prettyString.asTerm.asInstanceOf[Plus].left shouldBe one
  }

  it should "print/parse correctly -- right" in {
    val t = Plus(Plus(two, three), one)
    t.prettyString.asTerm.asInstanceOf[Plus].left shouldBe Plus(two, three)
  }

  "-" should "print/parse correctly -- left" in {
    val t = Minus(one, Minus(two, three))
    t.prettyString.asTerm.asInstanceOf[Minus].left shouldBe one
  }

  it should "print/parse correctly -- right" in {
    val t = Minus(Minus(two, three), one)
    t.prettyString.asTerm.asInstanceOf[Minus].left shouldBe Minus(two, three)
  }

  "*" should "print/parse correctly -- left" in {
    val t = Times(one, Times(two, three))
    t.prettyString.asTerm.asInstanceOf[Times].left shouldBe one
  }

  it should "print/parse correctly -- right" in {
    val t = Times(Times(two, three), one)
    t.prettyString.asTerm.asInstanceOf[Times].left shouldBe Times(two, three)
  }

  "/" should "print/parse correctly -- left" in {
    val t = Divide(one, Divide(two, three))
    t.prettyString.asTerm.asInstanceOf[Divide].left shouldBe one
  }

  "-+" should "print/parse correctly -- left" in {
    val t = Minus(one, Plus(one, two))
    t.prettyString.asTerm.asInstanceOf[Minus].left shouldBe one
  }

  "+*" should "print/parse correctly" in {
    val t = Times(one, Plus(two, three))
    t.prettyString.asTerm.asInstanceOf[Times].left shouldBe one
  }

  it should "print/parse correctly 2" in {
    val t = Times(Plus(two, three), one)
    t.prettyString.asTerm.asInstanceOf[Times].left shouldBe Plus(two, three)
  }

  "1-1+x" should "print/parse correctly" in {
    val t = "1-1+x".asTerm
    t.prettyString.asTerm.asInstanceOf[Plus].left shouldBe Minus(one, one)
  }

  it should "print/parse correctly -- right" in {
    val t = Divide(Divide(two, three), one)
    t.prettyString.asTerm.asInstanceOf[Divide].left shouldBe Divide(two, three)
  }

  it should "print/parse left assoc correctly" in {
    val add = Divide(Divide(one, two), three)
    add.right should be(three)
    add.prettyString.asTerm.asInstanceOf[Divide].right shouldBe three
  }

  "-/" should "print/parse correctly" in {
    Neg(Divide(one, two)).prettyString.asTerm.asInstanceOf[Neg].child shouldBe Divide(one, two)
    Neg(Times(one, two)).prettyString.asTerm.asInstanceOf[Neg].child shouldBe Times(one, two)
    Neg(Plus(one, two)).prettyString.asTerm.asInstanceOf[Neg].child shouldBe Plus(one, two)
    Neg(Minus(one, two)).prettyString.asTerm.asInstanceOf[Neg].child shouldBe Minus(one, two)
  }

  "Power" should "give useful location information" in {
    val ex = the[ParseException] thrownBy "((f(||)^(c()))'".asTerm
    ex.getMessage should (include("1:1 Imbalanced parenthesis") or include("1:16 Error parsing termList at 1:1"))
    ex.getMessage should (include("Found:    ( at 1:1") or include("Found:    \"\" at 1:16"))
  }

  "Abs" should "parse" in {
    "abs(x)".asTerm shouldBe FuncOf(InterpretedSymbols.absF, Variable("x"))
    "abs_0".asTerm shouldBe Variable("abs", Some(0))
    "abs_0()".asTerm shouldBe FuncOf(Function("abs", Some(0), Unit, Real, interp = None), Nothing)
  }

  ///

  "pp" should "parse Add (none) correctly" in {
    val f = "1 + 2 + 3 = 6".asFormula
    val expected = Equal(Plus(Plus(one, two), three), six)
    f.equals(expected) shouldBe true
  }

  it should "print Add (left) correctly" in {
    val f = Equal(Plus(Plus(one, two), three), six)
    f.prettyString shouldBe "1+2+3=6"
  }

  it should "print Add (right) correctly" in {
    val f = Equal(Plus(one, Plus(two, three)), six)
    f.prettyString shouldBe "1+(2+3)=6"
  }
}
