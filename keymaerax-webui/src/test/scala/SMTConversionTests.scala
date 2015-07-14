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
  type SExpr = SMTLib
  var z3 : Z3Solver = null
  var polya : PolyaSolver = null

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.Z3Scheduler = Some(new Interpreter(new Z3))
    Tactics.Z3Scheduler.get.init(Map())
    z3 = new Z3Solver
    polya = new PolyaSolver
  }

  override def afterEach() = {
    z3 = null
    polya = null
    Tactics.Z3Scheduler.get.shutdown()
    Tactics.Z3Scheduler = null
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
  }

  "Numbers" should "convert numbers" in {
    z3.toSMT("1 > 2".asFormula).getAssertNot should be  ("(assert (not (> 1 2)))")
    polya.toSMT("1 > 2".asFormula).getAssertNot should be  ("(assert (not (> 1 2)))")
  }

  "Variables" should "convert numbers" in {
    z3.toSMT("x > 2".asFormula).getVariableList should be ("(declare-fun x () Real)\n")
    polya.toSMT("x > 2".asFormula).getVariableList should be ("(declare-fun x () Real)\n")
  }

  it should "convert numbers complex" in {
    z3.toSMT("x > 2 & y < 3".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (and (> x 2) (< y 3))))")
    polya.toSMT("x > 2 & y < 3".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (and (> x 2) (< y 3))))")
  }

  it should "convert numbers const" in {
    z3.toSMT("x > a & y < x".asFormula).getAssertNot should be("(declare-fun x () Real)\n"
      + "(declare-fun a () Real)\n" + "(declare-fun y () Real)\n" + "(assert (not (and (> x a) (< y x))))")
    polya.toSMT("x > a & y < x".asFormula).getAssertNot should be("(declare-fun x () Real)\n"
      + "(declare-fun a () Real)\n" + "(declare-fun y () Real)\n" + "(assert (not (and (> x a) (< y x))))")
  }

  "Constant function" should "convert" in {
    z3.toSMT("g = 0 & g() > 0".asFormula).getAssertNot should be ("(declare-fun g () Real)\n"
      + "(assert (not (and (= g 0) (> g 0))))")
    polya.toSMT("g = 0 & g() > 0".asFormula).getAssertNot should be ("(declare-fun g () Real)\n"
      + "(assert (not (and (= g 0) (> g 0))))")
  }

  "Quantifiers" should "convert forall" in {
    z3.toSMT("\\forall x x>y()".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (> x y))))")
    polya.toSMT("\\forall x x>y()".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (> x y))))")
  }

  it should "convert exists" in {
    z3.toSMT("\\exists x x>y()".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (exists ((x Real)) (> x y))))")
    polya.toSMT("\\exists x x>y()".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (exists ((x Real)) (> x y))))")
  }

  it should "convert nested qutifiers" in {
    z3.toSMT("\\forall x \\exists y x>y".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (exists ((y Real)) (> x y)))))")
    polya.toSMT("\\forall x \\exists y x>y".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (exists ((y Real)) (> x y)))))")
  }

  it should "convert complex qutifiers" in {
    z3.toSMT("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (forall ((x Real) (y Real)) (exists ((z Real)) (= (+ (* x x) (* y y)) (* z z))))))")
    polya.toSMT("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (forall ((x Real) (y Real)) (exists ((z Real)) (= (+ (* x x) (* y y)) (* z z))))))")
  }

  "Exponentials" should "convert positive" in {
    z3.toSMT("3^3 > 1".asFormula).getAssertNot should be  ("(assert (not (> (* 3 3 3) 1)))")
    polya.toSMT("3^3 > 1".asFormula).getAssertNot should be  ("(assert (not (> (* 3 3 3) 1)))")
  }

  it should "convert negtive" in {
    z3.toSMT("3^-2 < 1".asFormula).getAssertNot should be ("(assert (not (< (/ 1. (* 3 3)) 1)))")
    polya.toSMT("3^-2 < 1".asFormula).getAssertNot should be ("(assert (not (< (/ 1. (* 3 3)) 1)))")
  }

  it should "convert index 0" in {
    z3.toSMT("(x+y-z)^(1-1) = 1".asFormula).getAssertNot should be ("(assert (not (= 1 1)))")
    polya.toSMT("(x+y-z)^(1-1) = 1".asFormula).getAssertNot should be ("(assert (not (= 1 1)))")
  }

  it should "convert base 0" in {
    z3.toSMT("(0+0)^(x+y-1) = 1".asFormula).getAssertNot should be ("(assert (not (= 0 1)))")
    polya.toSMT("(0+0)^(x+y-1) = 1".asFormula).getAssertNot should be ("(assert (not (= 0 1)))")
  }

  it should "cause exception when converting fraction" in {
    a [SMTConversionException] should be thrownBy z3.toSMT("3^(-0.5) < 1".asFormula).getAssertNot
    a [SMTConversionException] should be thrownBy polya.toSMT("3^(-0.5) < 1".asFormula).getAssertNot
  }

  it should "convert complex" in {
    // Z3 and Polya gives different conversion results, both are sound
    z3.toSMT("(x+y-z)^3 = 1".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (* (+ x (- y z)) (+ x (- y z)) (+ x (- y z))) 1)))")
    polya.toSMT("(x+y-z)^3 = 1".asFormula).getAssertNot should be ("(declare-fun z () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun x () Real)\n"
      + "(assert (not (= (* (+ (+ (* (- 1) z) y) x) (+ (+ (* (- 1) z) y) x) (+ (+ (* (- 1) z) y) x)) 1)))")
  }

  it should "convert complex 2" in {
    // Z3 and Polya gives different conversion results, both are sound, Polya is better
    z3.toSMT("(x+x+x)^3 = 1".asFormula).getAssertNot should be ("(declare-fun x () Real)\n"
      + "(assert (not (= (* (+ (+ x x) x) (+ (+ x x) x) (+ (+ x x) x)) 1)))")
    polya.toSMT("(x+x+x)^3 = 1".asFormula).getAssertNot should be ("(declare-fun x () Real)\n"
      + "(assert (not (= (* (* 3 x) (* 3 x) (* 3 x)) 1)))")
  }

  it should "convert complex simplify index" in {
    // Z3 and Polya gives different conversion results, both are sound
    z3.toSMT("(x+y-z)^(y*2-y-y+3) = 1".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (* (+ x (- y z)) (+ x (- y z)) (+ x (- y z))) 1)))")
    polya.toSMT("(x+y-z)^(y*2-y-y+3) = 1".asFormula).getAssertNot should be ("(declare-fun z () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun x () Real)\n"
      + "(assert (not (= (* (+ (+ (* (- 1) z) y) x) (+ (+ (* (- 1) z) y) x) (+ (+ (* (- 1) z) y) x)) 1)))")
  }

  // complex
  ignore should "try bouncing ball" in {
    z3.toSMT("c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & kxtime_1=0 & h_2=h & v_2=v & kxtime_4=kxtime_1 & v_3=-1*kxtime_5*g+v_2 & h_3=1/2*(-1*kxtime_5^2*g+2*h_2+2*kxtime_5*v_2) & h_3>=0 & kxtime_5>=kxtime_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)".asFormula).getAssertNot should be ("")
    polya.toSMT("c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & kxtime_1=0 & h_2=h & v_2=v & kxtime_4=kxtime_1 & v_3=-1*kxtime_5*g+v_2 & h_3=1/2*(-1*kxtime_5^2*g+2*h_2+2*kxtime_5*v_2) & h_3>=0 & kxtime_5>=kxtime_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)".asFormula).getAssertNot should be ("")
  }

  ignore should "try bouncing ball constfun" in {
    z3.toSMT("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & kxtime_4()=kxtime_1 & v_3=-1*kxtime_5*g()+v_2() & h_3=1/2*(-1*kxtime_5^2*g()+2*h_2()+2*kxtime_5*v_2()) & h_3>=0 & kxtime_5>=kxtime_4() & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g()*(H-h_3)".asFormula).getAssertNot should be ("")
    polya.toSMT("c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & kxtime_1=0 & h_2=h & v_2=v & kxtime_4=kxtime_1 & v_3=-1*kxtime_5*g+v_2 & h_3=1/2*(-1*kxtime_5^2*g+2*h_2+2*kxtime_5*v_2) & h_3>=0 & kxtime_5>=kxtime_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)".asFormula).getAssertNot should be ("")
  }
}
