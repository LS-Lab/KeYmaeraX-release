/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase

import org.scalatest.prop.TableDrivenPropertyChecks._

/**
 * Tests Z3 and Polya on SMT-Lib format input.
 * Created by ran on 3/27/15.
 *
 * @author Ran Ji
 * @author Stefan Mitsch
 */
class SMTQETests extends TacticTestBase {
  var z3: Z3Solver = _
  var polya: PolyaSolver = _

  override def beforeEach(): Unit = {
    super.beforeEach()
    z3 = new Z3Solver
    polya = new PolyaSolver
  }

  override def afterEach(): Unit = {
    z3 = null
    polya = null
    super.afterEach()
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

  private val basicExamples = Table(("Name", "Formula", "Expected"),
    ("Reals", "3^0 = 1".asFormula, "true".asFormula),
    ("Constant function reflexivity", "f()=f()".asFormula, "true".asFormula),
    ("Unary function reflexivity", "f(x)=f(x)".asFormula, "true".asFormula),
    ("Binary function reflexivity", "f(x,y)=f(x,y)".asFormula, "true".asFormula),
    ("Ternary function reflexivity", "f(x,y,z)=f(x,y,z)".asFormula, "true".asFormula),
    ("Abs", "abs(y)>=y".asFormula, "true".asFormula),
    ("Min", "min(x,y)<=x".asFormula, "true".asFormula),
    ("Max", "max(x,y)>=x".asFormula, "true".asFormula)
  )

  "Z3" should "prove every basic example" in {
    forEvery (basicExamples) {
      (name, input, expected) => withClue(name) { z3.qeEvidence(input)._1 shouldBe expected }
    }
  }

  "Polya" should "prove every basic example" ignore {
    //@todo Polya proves not every example
    forEvery (basicExamples) {
      (name, input, expected) => withClue(name) { polya.qeEvidence(input)._1 shouldBe expected }
    }
  }

  // ---------------------------
  // Complicated
  // ---------------------------

  private val complicatedExamples = Table(("Name", "Formula", "Expected"),
    //Does not prove with 4.4.1 //("Complex quantifiers", "\\forall x \\forall y \\exists z x^2+y^2=z^2".asFormula, "true".asFormula),
    ("Complex", "(x+y-z)^3 = 1 -> true".asFormula, "true".asFormula),
    ("Complex 2", "(c<1&c>=0&H>=0&g()>0&v^2<=2*g()*(H-h)&h>=0&kxtime_1=0&h_2()=h&v_2()=v&h_3=0&kxtime_4()=0&v_3=-1*kxtime_5*g()+v&0>=0&0=1/2*(-1*kxtime_5^2*g()+2*h+2*kxtime_5*v)&kxtime_5>=0&v_5=-c*(-1*kxtime_5*g()+v)->(-c*(-1*kxtime_5*g()+v))^2<=2*g()*(H-0))".asFormula, "true".asFormula),
    ("Complex 3", "c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & kxtime_1=0 & h_2()=h & v_2()=v & h>=0 & kxtime_4()=0 & 0>=0 -> v=(0*2-1*0)/2^2*(-1*0^2*g()+2*h+2*0*v)+1/2*((-0*0^2+-1*(2*0^1*(0*0+1)))*g()+-1*0^2*0+(0*h+2*0)+((0*0+2*(0*0+1))*v+2*0*0))".asFormula, "true".asFormula)
    //Does not prove with 4.4.1 //("Typical ODE solution output", "A>=0 & v>=0 & x_0>=0 -> \\forall t_ (t_>=0 -> (\\forall s_ (0<=s_&s_<=t_ -> v+A*s_>=0) -> A/2*t^2+v*t_+x_0>=0))".asFormula, "true".asFormula)
  )

  "Z3" should "prove every complicated example" in {
    forEvery (complicatedExamples) {
      (name, input, expected) => withClue(name) { z3.qeEvidence(input)._1 shouldBe expected }
    }
  }

  it should "prove complex 1" in {
    a [SMTQeException] should be thrownBy z3.qeEvidence("x > 0 -> !x^2-2*x+1=0".asFormula)
    //@todo update Polya to latest version
    //polya.qeEvidence("x > 0 -> !x^2-2*x+1=0".asFormula) //@todo check expected result
  }

  // ---------------------------
  // Real applications
  // ---------------------------

  // proved with Z3 v4.4.1, but no longer with v4.5.0
  private val regressionExamples = Table(("Name", "Formula", "Expected"),
    ("STTT Tutorial Example 5 simplectrl", "\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&a_2=-B_0)&c_9=0)&v_6>=0)&x_4+v_6^2/(2*B_0)<=S_0)&x_5=x_4)&v_4=v_6)&c_7<=ep_0)&c_8=0)&c_7>=0)&v_5=v_6+-B_0*(c_7-0))&x_6=1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2))&v_6+-B_0*(c_7-0)>=0->1/2*(2*x_4+2*v_6*(c_7-0)+-B_0*(c_7-0)^2)+(v_6+-B_0*(c_7-0))^2/(2*B_0)<=S_0)".asFormula, "true".asFormula),
    ("STTT Tutorial Example 5", "\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&a_2=A_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+A_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2))&v_4+A_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+A_0*(c_8-0)^2)+(v_4+A_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula, "true".asFormula),
    ("STTT Tutorial Example 5 subgoal 2", "\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula, "true".asFormula),
    ("STTT Tutorial Example 6", "\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&x_6+v_4^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula, "true".asFormula),
    ("STTT Tutorial Example 6 subgoal 2", "\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall a_2 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((A_0>0&B_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*B_0)<=S_0)&a_2=-B_0)&c_9=0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+-B_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2))&v_4+-B_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+-B_0*(c_8-0)^2)+(v_4+-B_0*(c_8-0))^2/(2*B_0)<=S_0)".asFormula, "true".asFormula),
    ("STTT Tutorial Example 7", "\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 (((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&x_6+v_4^2/(2*b_0)+(A_0/b_0+1)*(A_0/2*ep_0^2+ep_0*v_4)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=A_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula, "true".asFormula),
    ("STTT Tutorial Example 7 subgoal 2", "\\forall x_6 \\forall x_5 \\forall x_4 \\forall v_6 \\forall v_5 \\forall v_4 \\forall ep_0 \\forall c_9 \\forall c_8 \\forall c_7 \\forall b_0 \\forall a_0 \\forall S_0 \\forall B_0 \\forall A_0 ((((((((((((((((A_0>0&B_0>=b_0)&b_0>0)&ep_0>0)&v_4>=0)&x_6+v_4^2/(2*b_0)<=S_0)&c_9=0)&-B_0<=a_0)&a_0<=-b_0)&x_5=x_6)&v_6=v_4)&c_8<=ep_0)&c_7=0)&c_8>=0)&v_5=v_4+a_0*(c_8-0))&x_4=1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2))&v_4+a_0*(c_8-0)>=0->1/2*(2*x_6+2*v_4*(c_8-0)+a_0*(c_8-0)^2)+(v_4+a_0*(c_8-0))^2/(2*b_0)<=S_0)".asFormula, "true".asFormula),
    ("Robix Theorem 14-1", "\\forall xr_0 \\forall xg_0 \\forall ep_0 \\forall b_0 \\forall Vmax_0 \\forall T_0 \\forall GDelta_0 \\forall A_0 (A_0>0&xr_0 < xg_0-GDelta_0&b_0>0&ep_0>0&Vmax_0>=2*A_0*ep_0&GDelta_0>Vmax_0*ep_0+Vmax_0^2/(2*b_0)&T_0>ep_0+(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0->0<=0&0<=Vmax_0&xr_0+0^2/(2*b_0) < xg_0+GDelta_0&(xg_0-GDelta_0 < xr_0->0=0|T_0>=0/b_0)&(xr_0<=xg_0-GDelta_0->0>=A_0*ep_0&T_0>(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0|0<=A_0*ep_0&T_0>ep_0-0/A_0+(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0))".asFormula, "true".asFormula),
    ("Robix Theorem 14-2", "\\forall xr_0 \\forall xg_0 \\forall vr_0 \\forall ep_0 \\forall b_0 \\forall Vmax_0 \\forall T_0 \\forall GDelta_0 \\forall A_0 (A_0>0&b_0>0&ep_0>0&Vmax_0>=2*A_0*ep_0&GDelta_0>Vmax_0*ep_0+Vmax_0^2/(2*b_0)&0<=vr_0&vr_0<=Vmax_0&xr_0+vr_0^2/(2*b_0) < xg_0+GDelta_0&(xg_0-GDelta_0 < xr_0->vr_0=0|T_0>=vr_0/b_0)&(xr_0<=xg_0-GDelta_0->vr_0>=A_0*ep_0&T_0>(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0|vr_0<=A_0*ep_0&T_0>ep_0-vr_0/A_0+(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0)->xr_0 < xg_0+GDelta_0&(T_0<=0->xg_0-GDelta_0 < xr_0&vr_0=0))".asFormula, "true".asFormula),
    ("Robix Theorem 14-3", "\\forall xr_0 \\forall xg_0 \\forall vr_0 \\forall t__0 \\forall ep_0 \\forall b_0 \\forall Vmax_0 \\forall T_0 \\forall GDelta_0 \\forall A_0 (A_0>0&b_0>0&ep_0>0&Vmax_0>=2*A_0*ep_0&GDelta_0>Vmax_0*ep_0+Vmax_0^2/(2*b_0)&0<=vr_0&vr_0<=Vmax_0&xr_0+vr_0^2/(2*b_0) < xg_0+GDelta_0&(xg_0-GDelta_0 < xr_0->vr_0=0|T_0>=vr_0/b_0)&(xr_0<=xg_0-GDelta_0->vr_0>=A_0*ep_0&T_0>(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0|vr_0<=A_0*ep_0&T_0>ep_0-vr_0/A_0+(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0)&xr_0>xg_0-GDelta_0&t__0>=0&(0<=t__0&t__0<=t__0->t__0+0<=ep_0&(-b_0)*t__0+vr_0>=0)->0<=(-b_0)*t__0+vr_0&(-b_0)*t__0+vr_0<=Vmax_0&(-b_0)/2*t__0^2+vr_0*t__0+xr_0+((-b_0)*t__0+vr_0)^2/(2*b_0) < xg_0+GDelta_0&(xg_0-GDelta_0 < (-b_0)/2*t__0^2+vr_0*t__0+xr_0->(-b_0)*t__0+vr_0=0|-t__0+T_0>=((-b_0)*t__0+vr_0)/b_0)&((-b_0)/2*t__0^2+vr_0*t__0+xr_0<=xg_0-GDelta_0->(-b_0)*t__0+vr_0>=A_0*ep_0&-t__0+T_0>(xg_0-((-b_0)/2*t__0^2+vr_0*t__0+xr_0)-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0|(-b_0)*t__0+vr_0<=A_0*ep_0&-t__0+T_0>ep_0-((-b_0)*t__0+vr_0)/A_0+(xg_0-((-b_0)/2*t__0^2+vr_0*t__0+xr_0)-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0))".asFormula, "true".asFormula),
    ("Robix Theorem 14-4", "\\forall xr_0 \\forall xg_0 \\forall vr_0 \\forall t__0 \\forall ep_0 \\forall b_0 \\forall Vmax_0 \\forall T_0 \\forall GDelta_0 \\forall A_0 (A_0>0&b_0>0&ep_0>0&Vmax_0>=2*A_0*ep_0&GDelta_0>Vmax_0*ep_0+Vmax_0^2/(2*b_0)&0<=vr_0&vr_0<=Vmax_0&xr_0+vr_0^2/(2*b_0) < xg_0+GDelta_0&(xg_0-GDelta_0 < xr_0->vr_0=0|T_0>=vr_0/b_0)&(xr_0<=xg_0-GDelta_0->vr_0>=A_0*ep_0&T_0>(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0|vr_0<=A_0*ep_0&T_0>ep_0-vr_0/A_0+(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0)&xr_0<=xg_0-GDelta_0&xr_0+vr_0^2/(2*b_0)+(A_0/b_0+1)*(A_0/2*ep_0^2+ep_0*vr_0) < xg_0+GDelta_0&vr_0+A_0*ep_0<=Vmax_0&t__0>=0&(0<=t__0&t__0<=t__0->t__0+0<=ep_0&A_0*t__0+vr_0>=0)->0<=A_0*t__0+vr_0&A_0*t__0+vr_0<=Vmax_0&A_0/2*t__0^2+vr_0*t__0+xr_0+(A_0*t__0+vr_0)^2/(2*b_0) < xg_0+GDelta_0&(xg_0-GDelta_0 < A_0/2*t__0^2+vr_0*t__0+xr_0->A_0*t__0+vr_0=0|-t__0+T_0>=(A_0*t__0+vr_0)/b_0)&(A_0/2*t__0^2+vr_0*t__0+xr_0<=xg_0-GDelta_0->A_0*t__0+vr_0>=A_0*ep_0&-t__0+T_0>(xg_0-(A_0/2*t__0^2+vr_0*t__0+xr_0)-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0|A_0*t__0+vr_0<=A_0*ep_0&-t__0+T_0>ep_0-(A_0*t__0+vr_0)/A_0+(xg_0-(A_0/2*t__0^2+vr_0*t__0+xr_0)-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0))".asFormula, "true".asFormula),
    ("Robix Theorem 14-5", "\\forall xr_0 \\forall xg_0 \\forall vr_0 \\forall t__0 \\forall ep_0 \\forall b_0 \\forall Vmax_0 \\forall T_0 \\forall GDelta_0 \\forall A_0 (A_0>0&b_0>0&ep_0>0&Vmax_0>=2*A_0*ep_0&GDelta_0>Vmax_0*ep_0+Vmax_0^2/(2*b_0)&0<=vr_0&vr_0<=Vmax_0&xr_0+vr_0^2/(2*b_0) < xg_0+GDelta_0&(xg_0-GDelta_0 < xr_0->vr_0=0|T_0>=vr_0/b_0)&(xr_0<=xg_0-GDelta_0->vr_0>=A_0*ep_0&T_0>(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0|vr_0<=A_0*ep_0&T_0>ep_0-vr_0/A_0+(xg_0-xr_0-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0)&xr_0<=xg_0-GDelta_0&(xr_0+vr_0^2/(2*b_0)+(A_0/b_0+1)*(A_0/2*ep_0^2+ep_0*vr_0)>=xg_0+GDelta_0|vr_0+A_0*ep_0>Vmax_0)&t__0>=0&(0<=t__0&t__0<=t__0->t__0+0<=ep_0&vr_0>=0)->0<=vr_0&vr_0<=Vmax_0&vr_0*t__0+xr_0+vr_0^2/(2*b_0) < xg_0+GDelta_0&(xg_0-GDelta_0 < vr_0*t__0+xr_0->vr_0=0|-t__0+T_0>=vr_0/b_0)&(vr_0*t__0+xr_0<=xg_0-GDelta_0->vr_0>=A_0*ep_0&-t__0+T_0>(xg_0-(vr_0*t__0+xr_0)-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0|vr_0<=A_0*ep_0&-t__0+T_0>ep_0-vr_0/A_0+(xg_0-(vr_0*t__0+xr_0)-GDelta_0)/(A_0*ep_0)+ep_0+Vmax_0/b_0))".asFormula, "true".asFormula)
  )

  "Z3" should "prove every regression example" in {
    forEvery (regressionExamples) {
      (name, input, expected) => withClue(name) { z3.qeEvidence(input)._1 shouldBe expected }
    }
  }

  it should "not exceed a timeout" ignore {
    //@note takes >60s with v4.5.0
    val f = "\\forall x_0 \\forall v_0 \\forall t__0 \\forall ep_0 \\forall S_0 \\forall B_0 \\forall A_0 (A_0>0&B_0>0&ep_0>0&x_0+v_0^2/(2*B_0)+(A_0/B_0+1)*(A_0/2*ep_0^2+ep_0*v_0)<=S_0&t__0>=0&\\forall s_ (0<=s_&s_<=t__0->A_0*s_+v_0>=0&s_+0<=ep_0)&v_0>=0&x_0+v_0^2/(2*B_0)<=S_0->A_0/2*t__0^2+v_0*t__0+x_0+(A_0*t__0+v_0)^2/(2*B_0)<=S_0)".asFormula
    z3.setOperationTimeout(5)
    the [ToolException] thrownBy z3.qeEvidence(f) should have message "Z3 timeout of 5s exceeded"
  }

  "Z3Reports" should "prove intervalUpDivide" ignore {
    val intervalUpDivideStr = "\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (x/y<=z <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(xx/yy<=z & xx/Y<=z & X/yy<=z & X/Y<=z))))"
    val intervalUpDivide = intervalUpDivideStr.asFormula
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
