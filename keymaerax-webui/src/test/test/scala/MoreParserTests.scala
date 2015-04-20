import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{Matchers, FlatSpec}

import testHelper.StringConverter._

/**
 * Created by nfulton on 2/23/15.
 */
class AirthmeticParserTests extends FlatSpec with Matchers {

  val one = Number(1)
  val two = Number(2)
  val three = Number(3)
  val six = Number(6)


  "Add" should "print/parse correctly -- left" in {
    val t = Add(Real, one, Add(Real, two, three))
    t.prettyString().asTerm.asInstanceOf[Add].left shouldBe one
  }

  it should "print/parse correctly -- right" in {
    val t = Add(Real, Add(Real, two, three), one)
    t.prettyString().asTerm.asInstanceOf[Add].left shouldBe Add(Real, two, three)
  }

  "-" should "print/parse correctly -- left" in {
    val t = Subtract(Real, one, Subtract(Real, two, three))
    t.prettyString().asTerm.asInstanceOf[Subtract].left shouldBe one
  }

  it should "print/parse correctly -- right" in {
    val t = Subtract(Real, Subtract(Real, two, three), one)
    t.prettyString().asTerm.asInstanceOf[Subtract].left shouldBe Subtract(Real, two, three)
  }



  "*" should "print/parse correctly -- left" in {
    val t = Multiply(Real, one, Multiply(Real, two, three))
    t.prettyString().asTerm.asInstanceOf[Multiply].left shouldBe one
  }

  it should "print/parse correctly -- right" in {
    val t = Multiply(Real, Multiply(Real, two, three), one)
    t.prettyString().asTerm.asInstanceOf[Multiply].left shouldBe Multiply(Real, two, three)
  }

  "/" should "print/parse correctly -- left" in {
    val t = Divide(Real, one, Divide(Real, two, three))
    t.prettyString().asTerm.asInstanceOf[Divide].left shouldBe one
  }

  "-+" should "print/parse correctly -- left" in {
    val t = Subtract(Real, one, Add(Real, one, two))
    t.prettyString().asTerm.asInstanceOf[Subtract].left shouldBe one
  }

  "+*" should "print/parse correctly" in {
    val t = Multiply(Real, one, Add(Real, two, three))
    t.prettyString().asTerm.asInstanceOf[Multiply].left shouldBe one
  }

  it should "print/parse correctly 2" in {
    val t = Multiply(Real, Add(Real, two, three), one)
    t.prettyString().asTerm.asInstanceOf[Multiply].left shouldBe Add(Real, two, three)
  }

  "1-1+x" should "print/parse correctly" in {
    val t = "1-1+x".asTerm
    t.prettyString().asTerm.asInstanceOf[Add].left shouldBe Subtract(Real,one,one)
  }

  it should "print/parse correctly -- right" in {
    val t = Divide(Real, Divide(Real, two, three), one)
    t.prettyString().asTerm.asInstanceOf[Divide].left shouldBe Divide(Real, two, three)
  }

  it should "print/parse left assoc correctly" in {
    val add = Divide(Real, Divide(Real, one, two), three)
    add.right should be (three)
    add.prettyString().asTerm.asInstanceOf[Divide].right shouldBe three
  }



  ///

  "pp" should "parse Add (none) correctly" in {
    val f = "1 + 2 + 3 = 6".asFormula
    val expected = Equals(Real, Add(Real, Add(Real, one, two), three), six)
    f.equals(expected) shouldBe true
  }

  it should "print Add (left) correctly" in {
    val f = Equals(Real, Add(Real, Add(Real, one, two), three), six)
    f.prettyString() shouldBe ("1+2+3=6")
  }

  it should "print Add (right) correctly" in {
    val f = Equals(Real, Add(Real, one, Add(Real, two, three)), six)
    f.prettyString() shouldBe ("1+(2+3)=6")
  }
}
