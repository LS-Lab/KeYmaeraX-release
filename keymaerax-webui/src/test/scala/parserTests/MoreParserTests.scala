package parserTests

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.{FlatSpec, Matchers}

/**
 * Created by nfulton on 2/23/15.
 * @author Nathan Fulton
 */
class AirthmeticParserTests extends FlatSpec with Matchers {

  val one = Number(1)
  val two = Number(2)
  val three = Number(3)
  val six = Number(6)


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
    t.prettyString.asTerm.asInstanceOf[Plus].left shouldBe Minus(one,one)
  }

  it should "print/parse correctly -- right" in {
    val t = Divide(Divide(two, three), one)
    t.prettyString.asTerm.asInstanceOf[Divide].left shouldBe Divide(two, three)
  }

  it should "print/parse left assoc correctly" in {
    val add = Divide(Divide(one, two), three)
    add.right should be (three)
    add.prettyString.asTerm.asInstanceOf[Divide].right shouldBe three
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
