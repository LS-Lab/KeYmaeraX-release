/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.core.True
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools._
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}

/**
 * Created by ran on 3/27/15.
 *
 * @author Ran Ji
 */
class SMTQETests extends TacticTestBase {
  var z3: Z3Solver = null
  var polya: PolyaSolver = null

  override def beforeEach() = {
    z3 = new Z3Solver
    polya = new PolyaSolver
  }

  override def afterEach() = {
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
    z3.qeEvidence("3^0 = 1".asFormula)._1 should be ("true".asFormula)
    //@todo update Polya to latest version
    //polya.qeEvidence("3^0 = 1".asFormula)._1 should be ("true".asFormula)
  }

  it should "prove constant function" in {
    z3.qeEvidence("f()=f()".asFormula)._1 should be("true".asFormula)
    polya.qeEvidence("f()=f()".asFormula)._1 should be("true".asFormula)

  }

  it should "prove unary function" in {
    z3.qeEvidence("f(x)=f(x)".asFormula)._1 should be("true".asFormula)
    polya.qeEvidence("f(x)=f(x)".asFormula)._1 should be("true".asFormula)
  }

  it should "prove binary function" in {
    z3.qeEvidence("f(x,y)=f(x,y)".asFormula)._1 should be("true".asFormula)
    polya.qeEvidence("f(x,y)=f(x,y)".asFormula)._1 should be("true".asFormula)
  }

  it should "prove function with more parameters" in {
    z3.qeEvidence("f(x,y,z)=f(x,y,z)".asFormula)._1 should be("true".asFormula)
    polya.qeEvidence("f(x,y,z)=f(x,y,z)".asFormula)._1 should be("true".asFormula)
  }

  it should "prove absolute value" in {
    z3.qeEvidence("abs(y)>=y".asFormula)._1 should be("true".asFormula)
    //TODO Polya support
//    polya.qeEvidence("abs(y)>=y".asFormula)._1 should be("true".asFormula)
  }

  it should "prove minimum" in {
    z3.qeEvidence("min(x, y)<=x".asFormula)._1 should be("true".asFormula)
    //TODO Polya support
//    polya.qeEvidence("min(x, y)<=x".asFormula)._1 should be("true".asFormula)
  }

  it should "prove maximum" in {
    z3.qeEvidence("max(x, y)>=x".asFormula)._1 should be("true".asFormula)
    //TODO Polya support
//    polya.qeEvidence("max(x, y)>=x".asFormula)._1 should be("true".asFormula)
  }

  // ---------------------------
  // Complicated
  // ---------------------------

  it should "prove complex quantifiers" in {
    z3.qeEvidence("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula) should be("true".asFormula)
    //@todo update Polya to latest version
    //polya.qeEvidence("\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula) //@todo check expected result
  }

  it should "prove complex" in {
    z3.qeEvidence("(x+y-z)^3 = 1 -> true".asFormula)._1 should be("true".asFormula)
    //@todo update Polya to latest version
    //polya.qeEvidence("(x+y-z)^3 = 1 -> true".asFormula)._1 should be("true".asFormula)
  }

  it should "prove complex 1" in {
    a [SMTQeException] should be thrownBy z3.qeEvidence("x > 0 -> !x^2-2*x+1=0".asFormula)
    //@todo update Polya to latest version
    //polya.qeEvidence("x > 0 -> !x^2-2*x+1=0".asFormula) //@todo check expected result
  }

  it should "prove complex 2" in {
    z3.qeEvidence("(c<1&c>=0&H>=0&g()>0&v^2<=2*g()*(H-h)&h>=0&kxtime_1=0&h_2()=h&v_2()=v&h_3=0&kxtime_4()=0&v_3=-1*kxtime_5*g()+v&0>=0&0=1/2*(-1*kxtime_5^2*g()+2*h+2*kxtime_5*v)&kxtime_5>=0&v_5=-c*(-1*kxtime_5*g()+v)->(-c*(-1*kxtime_5*g()+v))^2<=2*g()*(H-0))".asFormula)._1 should be("true".asFormula)
    // TODO Polya disagrees with Z3
//    polya.qeEvidence("(c<1&c>=0&H>=0&g()>0&v^2<=2*g()*(H-h)&h>=0&kxtime_1=0&h_2()=h&v_2()=v&h_3=0&kxtime_4()=0&v_3=-1*kxtime_5*g()+v&0>=0&0=1/2*(-1*kxtime_5^2*g()+2*h+2*kxtime_5*v)&kxtime_5>=0&v_5=-c*(-1*kxtime_5*g()+v)->(-c*(-1*kxtime_5*g()+v))^2<=2*g()*(H-0))".asFormula) should be("true".asFormula)
  }

  it should "prove complex 3" in {
    z3.qeEvidence("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & h>=0 & kxtime_4()=0 & 0>=0 -> v=(0*2-1*0)/2^2*(-1*0^2*g()+2*h+2*0*v)+1/2*((-0*0^2+-1*(2*0^1*(0*0+1)))*g()+-1*0^2*0+(0*h+2*0)+((0*0+2*(0*0+1))*v+2*0*0))".asFormula)._1 should be ("true".asFormula)
    //@todo update Polya to latest version
    //polya.qeEvidence("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & h>=0 & kxtime_4()=0 & 0>=0 -> v=(0*2-1*0)/2^2*(-1*0^2*g()+2*h+2*0*v)+1/2*((-0*0^2+-1*(2*0^1*(0*0+1)))*g()+-1*0^2*0+(0*h+2*0)+((0*0+2*(0*0+1))*v+2*0*0))".asFormula)._1 should be ("true".asFormula)
  }

  // ---------------------------
  // Real applications
  // ---------------------------

  "STTT Tutorial Example 5 simplectrl" should "prove subgoal" in {
    z3.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&a_2=-B_0)&c_9=0)&v_6>=0)&x_4+v_6^2/(2*B_0)<=S_0)&x_5=x_4)&v_4=v_6)&c_7<=ep_0)&c_8=0)&c_7>=0)&v_5=v_6+-B_0*(c_7-0))&x_6=1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2))&v_6+-B_0*(c_7-0)>=0->1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2)+(v_6+-B_0*(c_7-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be ("true".asFormula)
    // TODO Polya support
//    polya.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&a_2=-B_0)&c_9=0)&v_6>=0)&x_4+v_6^2/(2*B_0)<=S_0)&x_5=x_4)&v_4=v_6)&c_7<=ep_0)&c_8=0)&c_7>=0)&v_5=v_6+-B_0*(c_7-0))&x_6=1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2))&v_6+-B_0*(c_7-0)>=0->1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2)+(v_6+-B_0*(c_7-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be ("true".asFormula)
  }

  it should "prove in Mathematica" in withMathematica(_ => {
    val f = "\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&a_2=-B_0)&c_9=0)&v_6>=0)&x_4+v_6^2/(2*B_0)<=S_0)&x_5=x_4)&v_4=v_6)&c_7<=ep_0)&c_8=0)&c_7>=0)&v_5=v_6+-B_0*(c_7-0))&x_6=1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2))&v_6+-B_0*(c_7-0)>=0->1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2)+(v_6+-B_0*(c_7-0))^2/(2*B_0)<=S_0)".asFormula
    TactixLibrary.proveBy(f, TactixLibrary.QE) shouldBe 'proved
  })

  "STTT Tutorial Example 5" should "prove subgoal 1" in {
    z3.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&a_2=A_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+A_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2))&v_4+A_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2)+(v_4+A_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be("true".asFormula)
    // TODO Polya support
//    polya.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&a_2=A_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+A_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2))&v_4+A_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2)+(v_4+A_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be("true".asFormula)
  }

  it should "prove subgoal 2" in {
    z3.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be("true".asFormula)
    // TODO Polya support
//    polya.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be("true".asFormula)
  }

  "STTT Tutorial Example 6" should "prove subgoal 1" in {
//    z3.qe("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be("true".asFormula)
    // TODO Polya support
//    polya.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be("true".asFormula)
  }

  it should "prove subgoal 2" in {
    z3.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be("true".asFormula)
    // TODO Polya support
//    polya.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula)._1 should be("true".asFormula)
  }

  "STTT Tutorial Example 7" should "prove subgoal 1" in {
    z3.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&x_6+v_4^2/(2*b_0)+(A_0/b_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula)._1 should be("true".asFormula)
    // TODO Polya support
//    polya.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&x_6+v_4^2/(2*b_0)+(A_0/b_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula)._1 should be("true".asFormula)
  }

  it should "prove subgoal 2" in {
    z3.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=-b_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula)._1 should be("true".asFormula)
    // TODO Polya support
//    polya.qeEvidence("\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=-b_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula)._1 should be("true".asFormula)
  }


  "Z3Reports" should "prove intervalUpDivide" ignore {
    val intervalUpDivideStr = "\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (x/y<=z <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(xx/yy<=z & xx/Y<=z & X/yy<=z & X/Y<=z))))"
    val intervalUpDivide = intervalUpDivideStr.asFormula;
    println(intervalUpDivideStr)
    z3.qeEvidence(intervalUpDivide)
  }

  it should "prove intervalDownDivide" ignore {
    val intervalDownDivideStr = "\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (z<=x/y <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(z<=xx/yy & z<=xx/Y & z<=X/yy & z<=X/Y))))"
//    val intervalDownDivideStr = "h_() <= f_()/g_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((G_()<0 | 0 < gg_()) & (h_()<=ff_()/gg_() & h_()<=ff_()/G_() & h_()<=F_()/gg_() & h_()<=F_()/G_())))"
    val intervalDownDivide = intervalDownDivideStr.asFormula
    println(intervalDownDivideStr)
    z3.qeEvidence(intervalDownDivide)

  }
}
