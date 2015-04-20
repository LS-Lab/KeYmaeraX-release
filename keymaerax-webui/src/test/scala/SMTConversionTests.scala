import edu.cmu.cs.ls.keymaera.core.{Z3, KeYmaera}
import edu.cmu.cs.ls.keymaera.tactics.{Interpreter, Tactics}
import edu.cmu.cs.ls.keymaera.tools.{KeYmaeraToSMT, SMTConversionException, Z3Solver, SMTLib}
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._

/**
 * Created by ran on 3/23/15.
 */
class SMTConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  type KExpr = edu.cmu.cs.ls.keymaera.core.Expr
  type SExpr = SMTLib
  var smt : Z3Solver = null

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.Z3Scheduler = new Interpreter(new Z3)
    Tactics.Z3Scheduler.init(Map())
    smt = new Z3Solver
  }

  override def afterEach() = {
    smt = null
    Tactics.Z3Scheduler.shutdown()
    Tactics.Z3Scheduler = null
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
  }

  "Numbers" should "convert numbers" in {
    smt.toSMT("1 > 2".asFormula).getAssertNot should be  ("(assert (not (> 1 2)))")
  }

  "Variables" should "convert numbers" in {
    smt.toSMT("x > 2".asFormula).getVariableList should be ("(declare-fun x () Real)\n")
  }

  it should "convert numbers complex" in {
    smt.toSMT("x > 2 & y < 3".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (and (> x 2) (< y 3))))")
  }

  it should "convert numbers const" in {
    smt.toSMT("x > a & y < x".asFormula).getAssertNot should be("(declare-fun x () Real)\n"
      + "(declare-fun a () Real)\n" + "(declare-fun y () Real)\n" + "(assert (not (and (> x a) (< y x))))")
  }

  "Constant function" should "convert" in {
    smt.toSMT("g = 0 & g() > 0".asFormula).getAssertNot should be ("(declare-fun g () Real)\n"
      + "(assert (not (and (= g 0) (> g 0))))")
  }

  "Quantifiers" should "convert forall" in {
    smt.toSMT("\\forall x. x>y()".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (> x y))))")
  }

  it should "convert exists" in {
    smt.toSMT("\\exists x. x>y()".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (exists ((x Real)) (> x y))))")
  }

  it should "convert nested qutifiers" in {
    smt.toSMT("\\forall x. \\exists y. x>y".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n"
      + "(assert (not (forall ((x Real)) (exists ((y Real)) (> x y)))))")
  }

  it should "convert complex qutifiers" in {
    smt.toSMT("\\forall x. \\forall y. \\exists z. x^2+y^2=z^2".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (forall ((x Real) (y Real)) (exists ((z Real)) (= (+ (* x x) (* y y)) (* z z))))))")
  }

  "Exponentials" should "convert positive" in {
    smt.toSMT("3^3 > 1".asFormula).getAssertNot should be  ("(assert (not (> (* 3 3 3) 1)))")
  }

  it should "convert negtive" in {
    smt.toSMT("3^-2 < 1".asFormula).getAssertNot should be ("(assert (not (< (/ 1. (* 3 3)) 1)))")
  }

  it should "convert index 0" in {
    smt.toSMT("(x+y-z)^(1-1) = 1".asFormula).getAssertNot should be ("(assert (not (= 1 1)))")
  }

  it should "convert base 0" in {
    smt.toSMT("(0+0)^(x+y-1) = 1".asFormula).getAssertNot should be ("(assert (not (= 0 1)))")
  }

  it should "cause exception when converting fraction" in {
    a [SMTConversionException] should be thrownBy smt.toSMT("3^(-0.5) < 1".asFormula).getAssertNot
  }

  it should "convert complex" in {
    smt.toSMT("(x+y-z)^3 = 1".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (* (+ x (- y z)) (+ x (- y z)) (+ x (- y z))) 1)))")
  }

  it should "convert complex simplify index" in {
    smt.toSMT("(x+y-z)^(y*2-y-y+3) = 1".asFormula).getAssertNot should be ("(declare-fun x () Real)\n" + "(declare-fun y () Real)\n" + "(declare-fun z () Real)\n"
      + "(assert (not (= (* (+ x (- y z)) (+ x (- y z)) (+ x (- y z))) 1)))")
  }

  // complex
  ignore should "try bouncing ball" in {
    smt.toSMT("c<1 & c>=0 & H>=0 & g>0 & v^2<=2*g*(H-h) & h>=0 & k4_t_1=0 & h_2=h & v_2=v & k4_t_4=k4_t_1 & v_3=-1*k4_t_5*g+v_2 & h_3=1/2*(-1*k4_t_5^2*g+2*h_2+2*k4_t_5*v_2) & h_3>=0 & k4_t_5>=k4_t_4 & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g*(H-h_3)".asFormula).getAssertNot should be ("")
  }

  ignore should "try bouncing ball constfun" in {
    smt.toSMT("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & k4_t_1=0 & h_2()=h & v_2()=v & k4_t_4()=k4_t_1 & v_3=-1*k4_t_5*g()+v_2() & h_3=1/2*(-1*k4_t_5^2*g()+2*h_2()+2*k4_t_5*v_2()) & h_3>=0 & k4_t_5>=k4_t_4() & h_3=0 & v_5=-c*v_3 -> v_5^2<=2*g()*(H-h_3)".asFormula).getAssertNot should be ("")
  }
}
