/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

/**
 * Created by ran on 3/23/15.
 * @author Ran Ji
 */
class SMTConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  val converter = new SMTConverter {}

  "Numbers" should "convert numbers" in {
    converter("1 > 2".asFormula) should be("(assert (not (> 1 2)))")
  }

  it should "convert legal big positive numbers" in {
    converter("9223372036854775807 > 1".asFormula) should be("(assert (not (> 9223372036854775807 1)))")
  }

  it should "convert legal big negative numbers" in {
    converter("-9223372036854775807 < 1".asFormula) should be("(assert (not (< (- 9223372036854775807) 1)))")
  }

  it should "throw exception in converting illegal big positive numbers" in {
    a [SMTConversionException] should be thrownBy converter("9223372036854775808 > 1".asFormula)
  }

  it should "throw exception in converting illegal big negative numbers" in {
    a [SMTConversionException] should be thrownBy converter("-9223372036854775808 < 1".asFormula)
  }

  "Variables" should "convert numbers" in {
    converter("x > 2".asFormula) should be ("(declare-fun x () Real)\n(assert (not (> x 2)))")
  }

  it should "convert numbers complex" in {
    converter("x > 2 & y < 3".asFormula) should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (and (> x 2) (< y 3))))")
  }

  it should "convert numbers const" in {
    converter("x > a & y < x".asFormula) should be("(declare-fun a () Real)\n"
      + "(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(assert (not (and (> x a) (< y x))))")
  }

  "Constant function" should "convert" in {
    converter("g() > 0".asFormula) should be ("(declare-fun g () Real)\n"
      + "(assert (not (> g 0)))")
  }

  "Quantifiers" should "convert forall" in {
    converter("\\forall x x>y()".asFormula) should be ("(declare-fun x () Real)\n(declare-fun y () Real)\n(assert (not (forall ((x Real)) (> x y))))")
  }

  it should "convert exists" in {
    converter("\\exists x x>y()".asFormula) should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (exists ((x Real)) (> x y))))")
  }

  it should "convert nested qutifiers" in {
    converter("\\forall x \\exists y x>y".asFormula) should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (exists ((y Real)) (> x y)))))")
  }

  "Quantifiers with Z3 converter" should "convert complex quantifiers" in {
    new Z3SMTConverter()("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula) should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (forall ((x Real) (y Real)) (exists ((z Real)) (= (+ (^ x 2) (^ y 2)) (^ z 2))))))")
  }

  "Exponentials with default converter" should "fail" in {
    an [SMTConversionException] should be thrownBy converter("3^2 > 1".asFormula)
  }

  "Exponentials with Z3 converter" should "convert positive" in {
    new Z3SMTConverter()("3^3 > 1".asFormula) should be  ("(assert (not (> (^ 3 3) 1)))")
  }

  it should "convert negative" in {
    new Z3SMTConverter()("3^-2 < 1".asFormula) should be ("(assert (not (< (^ 3 (- 2)) 1)))")
  }

  it should "convert index 0" in {
    new Z3SMTConverter()("(x+y-z)^(1-1) = 1".asFormula) should be ("(declare-fun x () Real)\n(declare-fun y () Real)\n(declare-fun z () Real)\n(assert (not (= (^ (- (+ x y) z) (- 1 1)) 1)))")
  }

  it should "convert base 0" in {
    new Z3SMTConverter()("(0+0)^(x+y-1) = 1".asFormula) should be ("(declare-fun x () Real)\n(declare-fun y () Real)\n(assert (not (= (^ (+ 0 0) (- (+ x y) 1)) 1)))")
  }

  it should "convert fractions" in {
    new Z3SMTConverter()("3^(-0.5) < 1".asFormula) shouldBe "(assert (not (< (^ 3 (- 0.5)) 1)))"
  }

  it should "convert complex" in {
    new Z3SMTConverter()("(x+y-z)^3 = 1".asFormula) should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (^ (- (+ x y) z) 3) 1)))")
  }

  it should "convert complex 2" in {
    new Z3SMTConverter()("(x+x+x)^3 = 1".asFormula) should be ("(declare-fun x () Real)\n(assert (not (= (^ (+ (+ x x) x) 3) 1)))")
  }

  it should "convert complex 3" in {
    new Z3SMTConverter()("(x+y-z)^(y*2-y-y+3) = 1".asFormula) should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (^ (- (+ x y) z) (+ (- (- (* y 2) y) y) 3)) 1)))")
  }

  // complex
  ignore should "try bouncing ball" in {
    converter("c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & kxtime_1=0 & h_2=h & v_2=v & kxtime_4=kxtime_1 & v_3=-1*kxtime_5*g+v_2 & h_3=1/2*(-1*kxtime_5^2*g+2*h_2+2*kxtime_5*v_2) & h_3>=0 & kxtime_5>=kxtime_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)".asFormula) should be ("")
  }

  ignore should "try bouncing ball constfun" in {
    converter("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & kxtime_4()=kxtime_1 & v_3=-1*kxtime_5*g()+v_2() & h_3=1/2*(-1*kxtime_5^2*g()+2*h_2()+2*kxtime_5*v_2()) & h_3>=0 & kxtime_5>=kxtime_4() & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g()*(H-h_3)".asFormula) should be ("")
  }
}
