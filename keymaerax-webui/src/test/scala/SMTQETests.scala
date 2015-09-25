/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.core.True
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{Interpreter, Tactics}
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Created by ran on 3/27/15.
 * @author Ran Ji
 */
class SMTQETests extends FlatSpec with Matchers with BeforeAndAfterEach {
  var z3: Z3Solver = null
  var polya: PolyaSolver = null

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.Z3Scheduler = Some(new Interpreter(new Z3))
    Tactics.PolyaScheduler = Some(new Interpreter(new Polya))
    z3 = new Z3Solver
    polya = new PolyaSolver
  }

  override def afterEach() = {
    Tactics.PolyaScheduler.get.shutdown()
    Tactics.Z3Scheduler.get.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.Z3Scheduler = null
    Tactics.KeYmaeraScheduler = null
    z3 = null
    polya = null
  }

  // ---------------------------
  // Simplify
  // ---------------------------

  "Simplify" should "simplify term" in {
    z3.simplify("1+x-x".asTerm) should be ("1".asTerm)
    polya.simplify("1+x-x".asTerm) should be ("1".asTerm)
  }

  // ---------------------------
  // Basics
  // ---------------------------

  "QE" should "prove reals" in {
    z3.qe("3^0 = 1".asFormula) should be ("true".asFormula)
    polya.qe("3^0 = 1".asFormula) should be ("true".asFormula)
  }

  it should "prove constant function" in {
    z3.qe("f()=f()".asFormula) should be("true".asFormula)
    polya.qe("f()=f()".asFormula) should be("true".asFormula)

  }

  it should "prove unary function" in {
    z3.qe("f(x)=f(x)".asFormula) should be("true".asFormula)
    polya.qe("f(x)=f(x)".asFormula) should be("true".asFormula)
  }

  it should "prove binary function" in {
    z3.qe("f(x,y)=f(x,y)".asFormula) should be("true".asFormula)
    polya.qe("f(x,y)=f(x,y)".asFormula) should be("true".asFormula)
  }

  it should "prove function with more parameters" in {
    z3.qe("f(x,y,z)=f(x,y,z)".asFormula) should be("true".asFormula)
    polya.qe("f(x,y,z)=f(x,y,z)".asFormula) should be("true".asFormula)
  }

  it should "prove absolute value" in {
    z3.qe("abs(y)>=y".asFormula) should be("true".asFormula)
    //TODO Polya support
//    polya.qe("abs(y)>=y".asFormula) should be("true".asFormula)
  }

  it should "prove minimum" in {
    z3.qe("min(x, y)<=x".asFormula) should be("true".asFormula)
    //TODO Polya support
//    polya.qe("min(x, y)<=x".asFormula) should be("true".asFormula)
  }

  it should "prove maximum" in {
    z3.qe("max(x, y)>=x".asFormula) should be("true".asFormula)
    //TODO Polya support
//    polya.qe("max(x, y)>=x".asFormula) should be("true".asFormula)
  }

  // ---------------------------
  // Complicated
  // ---------------------------

  it should "prove complex quantifiers" in {
    z3.qe("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula) should be ("false".asFormula)
    polya.qe("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula) should be ("false".asFormula)
  }

  it should "prove complex" in {
    z3.qe("(x+y-z)^3 = 1 -> true".asFormula) should be("true".asFormula)
    polya.qe("(x+y-z)^3 = 1 -> true".asFormula) should be("true".asFormula)
  }

  it should "prove complex 1" in {
    z3.qe("x > 0 -> !x^2-2*x+1=0".asFormula) should be("false".asFormula)
    // TODO returns false but for the wrong reasons (Polya timeout)
//    polya.qe("x > 0 -> !x^2-2*x+1=0".asFormula) should be("false".asFormula)
  }

  it should "prove complex 2" in {
    z3.qe("(c<1&c>=0&H>=0&g()>0&v^2<=2*g()*(H-h)&h>=0&kxtime_1=0&h_2()=h&v_2()=v&h_3=0&kxtime_4()=0&v_3=-1*kxtime_5*g()+v&0>=0&0=1/2*(-1*kxtime_5^2*g()+2*h+2*kxtime_5*v)&kxtime_5>=0&v_5=-c*(-1*kxtime_5*g()+v)->(-c*(-1*kxtime_5*g()+v))^2<=2*g()*(H-0))".asFormula) should be("true".asFormula)
    // TODO Polya disagrees with Z3
//    polya.qe("(c<1&c>=0&H>=0&g()>0&v^2<=2*g()*(H-h)&h>=0&kxtime_1=0&h_2()=h&v_2()=v&h_3=0&kxtime_4()=0&v_3=-1*kxtime_5*g()+v&0>=0&0=1/2*(-1*kxtime_5^2*g()+2*h+2*kxtime_5*v)&kxtime_5>=0&v_5=-c*(-1*kxtime_5*g()+v)->(-c*(-1*kxtime_5*g()+v))^2<=2*g()*(H-0))".asFormula) should be("true".asFormula)
  }

  it should "prove complex 3" in {
    z3.qe("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & h>=0 & kxtime_4()=0 & 0>=0 -> v=(0*2-1*0)/2^2*(-1*0^2*g()+2*h+2*0*v)+1/2*((-0*0^2+-1*(2*0^1*(0*0+1)))*g()+-1*0^2*0+(0*h+2*0)+((0*0+2*(0*0+1))*v+2*0*0))".asFormula) should be ("true".asFormula)
    polya.qe("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & h>=0 & kxtime_4()=0 & 0>=0 -> v=(0*2-1*0)/2^2*(-1*0^2*g()+2*h+2*0*v)+1/2*((-0*0^2+-1*(2*0^1*(0*0+1)))*g()+-1*0^2*0+(0*h+2*0)+((0*0+2*(0*0+1))*v+2*0*0))".asFormula) should be ("true".asFormula)
  }

  // ---------------------------
  // Real applications
  // ---------------------------

  "STTT Tutorial Example 5 simplectrl" should "prove subgoal" in {
    z3.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&a_2=-B_0)&c_9=0)&v_6>=0)&x_4+v_6^2/(2*B_0)<=S_0)&x_5=x_4)&v_4=v_6)&c_7<=ep_0)&c_8=0)&c_7>=0)&v_5=v_6+-B_0*(c_7-0))&x_6=1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2))&v_6+-B_0*(c_7-0)>=0->1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2)+(v_6+-B_0*(c_7-0))^2/(2*B_0)<=S_0)".asFormula) should be ("true".asFormula)
    // TODO Polya support
//    polya.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&a_2=-B_0)&c_9=0)&v_6>=0)&x_4+v_6^2/(2*B_0)<=S_0)&x_5=x_4)&v_4=v_6)&c_7<=ep_0)&c_8=0)&c_7>=0)&v_5=v_6+-B_0*(c_7-0))&x_6=1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2))&v_6+-B_0*(c_7-0)>=0->1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2)+(v_6+-B_0*(c_7-0))^2/(2*B_0)<=S_0)".asFormula) should be ("true".asFormula)
  }

  "STTT Tutorial Example 5" should "prove subgoal 1" in {
    z3.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&a_2=A_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+A_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2))&v_4+A_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2)+(v_4+A_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula) should be("true".asFormula)
    // TODO Polya support
//    polya.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&a_2=A_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+A_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2))&v_4+A_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2)+(v_4+A_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula) should be("true".asFormula)
  }

  it should "prove subgoal 2" in {
    z3.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula) should be("true".asFormula)
    // TODO Polya support
//    polya.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula) should be("true".asFormula)
  }

  "STTT Tutorial Example 6" should "prove subgoal 1" in {
//    z3.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula) should be("true".asFormula)
    // TODO Polya support
//    polya.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula) should be("true".asFormula)
  }

  it should "prove subgoal 2" in {
    z3.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula) should be("true".asFormula)
    // TODO Polya support
//    polya.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula) should be("true".asFormula)
  }

  "STTT Tutorial Example 7" should "prove subgoal 1" in {
    z3.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&x_6+v_4^2/(2*b_0)+(A_0/b_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula) should be("true".asFormula)
    // TODO Polya support
//    polya.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&x_6+v_4^2/(2*b_0)+(A_0/b_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula) should be("true".asFormula)
  }

  it should "prove subgoal 2" in {
    z3.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=-b_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula) should be("true".asFormula)
    // TODO Polya support
//    polya.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=-b_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula) should be("true".asFormula)
  }
}
