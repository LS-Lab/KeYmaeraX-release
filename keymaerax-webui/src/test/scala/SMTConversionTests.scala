/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{Interpreter, Tactics}
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Created by ran on 3/23/15.
 * @author Ran Ji
 */
class SMTConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.Z3Scheduler = Some(new Interpreter(new Z3))
    Tactics.Z3Scheduler.get.init(Map())
  }

  override def afterEach() = {
    Tactics.Z3Scheduler.get.shutdown()
    Tactics.Z3Scheduler = null
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
  }

  "Numbers" should "convert numbers" in {
    SMTConverter("1 > 2".asFormula, "Z3") should be  ("(assert (not (> 1 2)))")
    SMTConverter("1 > 2".asFormula, "Polya")  should be  ("(assert (not (> 1 2)))")
  }

  "Variables" should "convert numbers" in {
    SMTConverter("x > 2".asFormula, "Z3") should be ("(declare-fun x () Real)\n")
    SMTConverter("x > 2".asFormula, "Polya") should be ("(declare-fun x () Real)\n")
  }

  it should "convert numbers complex" in {
    SMTConverter("x > 2 & y < 3".asFormula, "Z3") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (and (> x 2) (< y 3))))")
    SMTConverter("x > 2 & y < 3".asFormula, "Polya") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (and (> x 2) (< y 3))))")
  }

  it should "convert numbers const" in {
    SMTConverter("x > a & y < x".asFormula, "Z3") should be("(declare-fun x () Real)\n"
      + "(declare-fun a () Real)\n" + "(declare-fun y () Real)\n" + "(assert (not (and (> x a) (< y x))))")
    SMTConverter("x > a & y < x".asFormula, "Polya") should be("(declare-fun x () Real)\n"
      + "(declare-fun a () Real)\n" + "(declare-fun y () Real)\n" + "(assert (not (and (> x a) (< y x))))")
  }

  "Constant function" should "convert" in {
    SMTConverter("g = 0 & g() > 0".asFormula, "Z3") should be ("(declare-fun g () Real)\n"
      + "(assert (not (and (= g 0) (> g 0))))")
    SMTConverter("g = 0 & g() > 0".asFormula, "Polya") should be ("(declare-fun g () Real)\n"
      + "(assert (not (and (= g 0) (> g 0))))")
  }

  "Quantifiers" should "convert forall" in {
    SMTConverter("\\forall x x>y()".asFormula, "Z3") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (> x y))))")
    SMTConverter("\\forall x x>y()".asFormula, "Polya") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (> x y))))")
  }

  it should "convert exists" in {
    SMTConverter("\\exists x x>y()".asFormula, "Z3") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (exists ((x Real)) (> x y))))")
    SMTConverter("\\exists x x>y()".asFormula, "Polya") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (exists ((x Real)) (> x y))))")
  }

  it should "convert nested qutifiers" in {
    SMTConverter("\\forall x \\exists y x>y".asFormula, "Z3") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (exists ((y Real)) (> x y)))))")
    SMTConverter("\\forall x \\exists y x>y".asFormula, "Polya") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (exists ((y Real)) (> x y)))))")
  }

  it should "convert complex qutifiers" in {
    SMTConverter("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula, "Z3") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (forall ((x Real) (y Real)) (exists ((z Real)) (= (+ (* x x) (* y y)) (* z z))))))")
    SMTConverter("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula, "Polya") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (forall ((x Real) (y Real)) (exists ((z Real)) (= (+ (* x x) (* y y)) (* z z))))))")
  }

  "Exponentials" should "convert positive" in {
    SMTConverter("3^3 > 1".asFormula, "Z3") should be  ("(assert (not (> (* 3 3 3) 1)))")
    SMTConverter("3^3 > 1".asFormula, "Polya") should be  ("(assert (not (> (* 3 3 3) 1)))")
  }

  it should "convert negative" in {
    SMTConverter("3^-2 < 1".asFormula, "Z3") should be ("(assert (not (< (/ 1 (* 3 3)) 1)))")
    SMTConverter("3^-2 < 1".asFormula, "Polya") should be ("(assert (not (< (/ 1 (* 3 3)) 1)))")
  }

  it should "convert index 0" in {
    SMTConverter("(x+y-z)^(1-1) = 1".asFormula, "Z3") should be ("(assert (not (= 1 1)))")
    SMTConverter("(x+y-z)^(1-1) = 1".asFormula, "Polya") should be ("(assert (not (= 1 1)))")
  }

  it should "convert base 0" in {
    SMTConverter("(0+0)^(x+y-1) = 1".asFormula, "Z3") should be ("(assert (not (= 0 1)))")
    SMTConverter("(0+0)^(x+y-1) = 1".asFormula, "Polya") should be ("(assert (not (= 0 1)))")
  }

  it should "cause exception when converting fraction" in {
    a [SMTConversionException] should be thrownBy SMTConverter("3^(-0.5) < 1".asFormula, "Z3")
    a [SMTConversionException] should be thrownBy SMTConverter("3^(-0.5) < 1".asFormula, "Polya")
  }

  it should "convert complex" in {
    // Z3 and Polya gives different conversion results, both are sound
    SMTConverter("(x+y-z)^3 = 1".asFormula, "Z3") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (* (- (+ x y) z) (- (+ x y) z) (- (+ x y) z)) 1)))")
    SMTConverter("(x+y-z)^3 = 1".asFormula, "Polya") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (* (+ (+ x y) (* (- 1) z)) (+ (+ x y) (* (- 1) z)) (+ (+ x y) (* (- 1) z))) 1)))")
  }

  it should "convert complex 2" in {
    // Z3 and Polya gives different conversion results, both are sound, Polya is better
    SMTConverter("(x+x+x)^3 = 1".asFormula, "Z3") should be ("(declare-fun x () Real)\n"
      + "(assert (not (= (* (+ (+ x x) x) (+ (+ x x) x) (+ (+ x x) x)) 1)))")
    SMTConverter("(x+x+x)^3 = 1".asFormula, "Polya") should be ("(declare-fun x () Real)\n"
      + "(assert (not (= (* (* 3 x) (* 3 x) (* 3 x)) 1)))")
  }

  it should "convert complex simplify index" in {
    // Z3 and Polya gives different conversion results, both are sound
    SMTConverter("(x+y-z)^(y*2-y-y+3) = 1".asFormula, "Z3") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (* (- (+ x y) z) (- (+ x y) z) (- (+ x y) z)) 1)))")
    SMTConverter("(x+y-z)^(y*2-y-y+3) = 1".asFormula, "Polya") should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (* (+ (+ x y) (* (- 1) z)) (+ (+ x y) (* (- 1) z)) (+ (+ x y) (* (- 1) z))) 1)))")
  }

  // complex
  ignore should "try bouncing ball" in {
    SMTConverter("c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & kxtime_1=0 & h_2=h & v_2=v & kxtime_4=kxtime_1 & v_3=-1*kxtime_5*g+v_2 & h_3=1/2*(-1*kxtime_5^2*g+2*h_2+2*kxtime_5*v_2) & h_3>=0 & kxtime_5>=kxtime_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)".asFormula, "Z3") should be ("")
    SMTConverter("c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & kxtime_1=0 & h_2=h & v_2=v & kxtime_4=kxtime_1 & v_3=-1*kxtime_5*g+v_2 & h_3=1/2*(-1*kxtime_5^2*g+2*h_2+2*kxtime_5*v_2) & h_3>=0 & kxtime_5>=kxtime_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)".asFormula, "Polya") should be ("")
  }

  ignore should "try bouncing ball constfun" in {
    SMTConverter("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & kxtime_4()=kxtime_1 & v_3=-1*kxtime_5*g()+v_2() & h_3=1/2*(-1*kxtime_5^2*g()+2*h_2()+2*kxtime_5*v_2()) & h_3>=0 & kxtime_5>=kxtime_4() & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g()*(H-h_3)".asFormula, "Z3") should be ("")
    SMTConverter("c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & kxtime_1=0 & h_2=h & v_2=v & kxtime_4=kxtime_1 & v_3=-1*kxtime_5*g+v_2 & h_3=1/2*(-1*kxtime_5^2*g+2*h_2+2*kxtime_5*v_2) & h_3>=0 & kxtime_5>=kxtime_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)".asFormula, "Polya") should be ("")
  }
}
