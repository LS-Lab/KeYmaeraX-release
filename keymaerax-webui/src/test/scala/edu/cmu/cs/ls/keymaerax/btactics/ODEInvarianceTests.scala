/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.SaturateTactic
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.ODEInvariance._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tagobjects.{IgnoreInBuildTest, TodoTest}
import org.scalatest.LoneElement._

class ODEInvarianceTests extends TacticTestBase {

  "vdbx" should "prove matrix and vector bounds" in withQE { _ =>
    // These bounds ought to be enough for all intents and purposes
    val cs = cauchy_schwartz_bound(5)
    val fs = frobenius_subord_bound(5)
    cs shouldBe Symbol("proved")
    fs._1 shouldBe Symbol("proved")
    fs._2 shouldBe Symbol("proved")
  }

  it should "prove matrix and vector bounds (requires high stack size)" taggedAs IgnoreInBuildTest in withQE { _ =>
    val cs = cauchy_schwartz_bound(6)
    val fs = frobenius_subord_bound(6)
    cs shouldBe Symbol("proved")
    fs._1 shouldBe Symbol("proved")
    fs._2 shouldBe Symbol("proved")
  }

  // TODO: Z3 is bad at this
  it should "test caching" in withMathematica { _ =>
    val lemmaDB = LemmaDBFactory.lemmaDB
    val dim = 5

    // Initial versions in DB
    println("Initial call")
    val cs1 = cauchy_schwartz_bound(dim)
    val fs1 = frobenius_subord_bound(dim)
    println("Done.")

    // Definitely cached
    println("Cached call")
    val cs2 = cauchy_schwartz_bound(dim)
    val fs2 = frobenius_subord_bound(dim)
    println("Done.")

    lemmaDB.remove("cauchy_schwartz_" + dim.toString)
    lemmaDB.remove("frobenius_subord_U_" + dim.toString)
    lemmaDB.remove("frobenius_subord_L_" + dim.toString)

    // Definitely uncached
    println("Uncached call")
    val cs3 = cauchy_schwartz_bound(dim)
    val fs3 = frobenius_subord_bound(dim)
    println("Done.")

    (cs1 == cs2 && cs2 == cs3, fs1 == fs2 && fs2 == fs3) shouldBe (true, true)
  }

  it should "prove a 2D equilibirum" in withQE { _ =>
    val fml = "x=0&y=0 ==> [{x'=y,y'=x}](x=0&y=0)".asSequent

    val cofactors = List(List("0", "1"), List("1", "0")).map(ls => ls.map(s => s.asTerm))
    val polys = List("x", "y").map(s => s.asTerm)
    val pr = proveBy(fml, dgVdbx(cofactors, polys)(1) & dW(1) & QE)
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove a 2D equilibirum with consts" in withQE { _ =>
    val fml = "x=0&y=0&a=1&c=0 ==> [{x'=a*y+b,y'=a*x+b&b=0}](x=c&y=x*c)".asSequent

    val cofactors = List(List("0", "1"), List("1", "0")).map(ls => ls.map(s => s.asTerm))
    val polys = List("x", "y").map(s => s.asTerm)
    val pr = proveBy(fml, dgVdbx(cofactors, polys)(1) & dW(1) & QE)
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove a 2D disequilibirum" in withQE { _ =>
    val fml = "x=0&y=1 ==> [{x'=y,y'=x}](x!=0|y!=0)".asSequent

    val cofactors = List(List("0", "1"), List("1", "0")).map(ls => ls.map(s => s.asTerm))
    val polys = List("x", "y").map(s => s.asTerm)
    val pr = proveBy(fml, dgVdbx(cofactors, polys, negate = true)(1) & dW(1) & QE)
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove a 3D equilibirum" in withQE { _ =>
    val fml = "x=0&y=0 ==> z!=1 , [{x'=(2*z+y)*x+x^2*y+z-1,y'=x+y^2+(z-1),z'=x*y+x+z-1}](x=0&y=0&z=1)".asSequent

    val cofactors = List(List("2*z+y", "x^2", "1"), List("1", "y", "1"), List("1", "x", "1"))
      .map(ls => ls.map(s => s.asTerm))
    val polys = List("x", "y", "z-1").map(s => s.asTerm)
    val pr = proveBy(fml, dgVdbx(cofactors, polys)(2) & dW(2) & QE)
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove a 3D disequilibirum" in withQE { _ =>
    val fml = "x=0&y=0 ==> z=1 , [{x'=(2*z+y)*x+x^2*y+z-1,y'=x+y^2+(z-1),z'=x*y+x+z-1}](x!=0|y!=0|z!=1)".asSequent

    val cofactors = List(List("2*z+y", "x^2", "1"), List("1", "y", "1"), List("1", "x", "1"))
      .map(ls => ls.map(s => s.asTerm))
    val polys = List("x", "y", "z-1").map(s => s.asTerm)
    val pr = proveBy(fml, dgVdbx(cofactors, polys, negate = true)(2) & dW(2) & QE)
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove a DRI SAS Ex 12" in withQE { _ =>
    val polys = List("x1^2+x2^2-1", "x3-x1").map(s => s.asTerm)

    val system = "{x1'=-x2,x2'=x3,x3'=-x2}".asProgram.asInstanceOf[ODESystem]
    val cofactors = List(List("0", "2*x2"), List("0", "0")).map(ls => ls.map(s => s.asTerm))
    val pr = proveBy(
      "x1^2+x2^2-1=0 & x3-x1=0 -> [{x1'=-x2,x2'=x3,x3'=-x2}](x1^2+x2^2-1=0 & x3-x1=0)".asFormula,
      implyR(1) & dgVdbx(cofactors, polys)(1) & dW(1) & QE,
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  "DRI" should "prove SAS Ex 12 automatically" in withQE { _ =>
    val pr = proveBy(
      "x1^2+x2^2-1=0 & x3-x1=0 -> [{x1'=-x2,x2'=x3,x3'=-x2}](x1^2+x2^2-1=0 & x3-x1=0)".asFormula,
      implyR(1) & dRI(1),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove SAS 5d non-linear equilibria" in withQE { _ =>
    val pr = proveBy(
      "x1=1 & x3=4 & x4=4 & x5=1 -> [{x1' = (x1 - 1)*x2, x2' = x1, x3' = (x3 - 4)*x2, x4' = (x4 - 4)*x2, x5' = (x5 - 1)*x1}](x1=1 & x3=4 & x4=4 & x5=1)"
        .asFormula,
      implyR(1) & dRI(1),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove SAS aircraft" in withQE { _ =>
    val pr = proveBy(
      "(x1^2 + x2^2 - 1)=0& x3=0& x4^2 + x5^2 - 1 =0 &(x6 - x4) =0 -> [{x1' = -x2 + x1*(1 - x1^2 - x2^2), x2' = x1 + x2*(1 - x1^2 - x2^2), x3' = x3, x4' = -x5, x5' = x6, x6'=-x5}]((x1^2 + x2^2 - 1)=0& x3=0& x4^2 + x5^2 - 1 =0 &(x6 - x4) =0)"
        .asFormula,
      implyR(1) & dRI(1),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove SAS extended Motzkin (rank 3)" in withQE { _ =>
    val pr = proveBy(
      "x1^4*x2^2 + x1^2*x2^4 - 3*x1^2*x2^2 + 1 = 0 & x3=0 -> [{x1' = (x1 - 1)*(x1 + 1), x2' = (x2 - 1)*(x2 + 1),x3' = -x3}](x1^4*x2^2 + x1^2*x2^4 - 3*x1^2*x2^2 + 1 = 0 & x3=0)"
        .asFormula,
      implyR(1) & dRI(1),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove an example with symbols (rank 4)" in withMathematica { _ =>
    // The postcondition is NOT an invariant
    val pr = proveBy(
      "y=1&x=0&b()=1 -> 1=0 | 2 = 0 | [{x'=-y - x* (1 - x^2 - y^2), y'=x - y* (1 - x^2 - y^2)}](1 - x^2 - x*y + x^3*y - y^2 + x*y^3)*a() + b() = 1"
        .asFormula,
      implyR(1) & orR(1) & orR(2) & dRI(3),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "correctly handle constants" in withQE { _ =>
    val pr = proveBy("x+a+b+c+d=y -> [{y'=b+c+d& b=1 & c=-1 & d=0}](x+a=y-b-c-d)".asFormula, implyR(1) & dRI(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "correctly handle constants2" in withQE { _ =>
    val pr = proveBy("a=0&b=0&c=0&z=0 -> [{y'=b+c+d}](a=0&b=0&c=0&z=0)".asFormula, implyR(1) & dRI(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "solve nilpotent linear system" in withQE { _ =>
    // Solves for all 3 variables
    val pr = proveBy(
      "x=x0&y=y0&z=z0&t=0 -> [{x'=5*x-3*y+2*z,y'=15*x-9*y+6*z,z'=10*x-6*y+4*z,t'=1}](x=(1+5*t)*x0-3*t*y0 + 2*t*z0 & y=15*t*x0 + (1 - 9*t)*y0 + 6*t*z0& z=10*t*x0 - 6*t*y0 + (1 + 4*t)*z0)"
        .asFormula,
      implyR(1) & dRI(1),
    )
    // partial solve for x only
    val pr2 = proveBy(
      "x=x0&y=y0&z=z0&t=0 -> [{x'=5*x-3*y+2*z,y'=15*x-9*y+6*z,z'=10*x-6*y+4*z,t'=1}](x=(1+5*t)*x0-3*t*y0 + 2*t*z0)"
        .asFormula,
      implyR(1) & dRI(1),
    )
    println(pr)
    println(pr2)
    pr shouldBe Symbol("proved")
    pr2 shouldBe Symbol("proved")
  }

  it should "prove a disjunctive equational postcondition" in withQE { _ =>
    val pr = proveBy(
      "x1=1 & x2=2 -> [{x1' = (x1 - 1)*x2, x2' = x1*(x2-2) }](x2=2 & x1=1 | x1*x2=1)".asFormula,
      implyR(1) & dRI(1),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  // Mathematica crashes badly
  //  it should "handle the largest example" in withMathematica { _ =>
  //    val pr = proveBy("(1 - 3*x1^2*x2^2 +x1^4*x2^2 +x1^2*x2^4)^13 = 0 & (x3^4*x4^2 + x3^2*x4^4 - 3*x3^2*x4^2*x5^2 +x5^6)^7 = 0 & (-1 +x6^2 +x7^2 + x8^2)^73 = 0 & (-3 + 6*x10^2 +x10^4 + 2*x10*x9 + 2*x10^3*x9 +x9^2)^21 = 0 & -1 +x13 +x11*x13 = 0 & x12=0 -> [{x1' = -292*x7*(-1 + x6^2 + x7^2 + x8^2)^145,\nx2' = -292*x8*(-1 + x6^2 + x7^2 + x8^2)^145,\nx3' = -42*(2*x10 + 2*x10^3 + 2*x9)* (-3 + 6*x10^2 + x10^4 + 2*x10*x9 + 2*x10^3*x9 + x9^2)^41,\nx4' = -42*(12*x10 + 4*x10^3 + 2*x9 + 6*x10^2*x9) * (-3 + 6*x10^2 + x10^4 + 2*x10*x9 + 2*x10^3*x9 + x9^2)^41,\nx5' = -2*x13*(-1 +x13 +x11*x13),\nx6' = -2*x12,\nx7' = 26*(-6*x1*x2^2 + 4*x1^3*x2^2 + 2*x1*x2^4)*(1 - 3*x1^2*x2^2 +x1^4*x2^2 +x1^2*x2^4)^25,\nx8' = 26*(-6*x1^2*x2 + 2*x1^4*x2 + 4*x1^2*x2^3) * (1 - 3*x1^2*x2^2 +x1^4*x2^2 +x1^2*x2^4)^25,\nx9' = 14*(4*x3^3*x4^2 + 2*x3*x4^4 - 6*x3*x4^2*x5^2)*(x3^4*x4^2 + x3^2*x4^4 - 3*x3^2*x4^2*x5^2 +x5^6)^13,\nx10' = 14*(2*x3^4*x4 + 4*x3^2*x4^3 - 6*x3^2*x4*x5^2)*(x3^4*x4^2 +x3^2*x4^4 - 3*x3^2*x4^2*x5^2 + x5^6)^13,\nx11'= 14*(-6*x3^2*x4^2*x5 + 6*x5^5)*(x3^4*x4^2 +x3^2*x4^4 - 3*x3^2*x4^2*x5^2 +x5^6)^13,\nx12'= 292*x6*(-1 +x6^2 +x7^2 +x8^2)^145}]((1 - 3*x1^2*x2^2 +x1^4*x2^2 +x1^2*x2^4)^13 = 0 & (x3^4*x4^2 + x3^2*x4^4 - 3*x3^2*x4^2*x5^2 +x5^6)^7 = 0 & (-1 +x6^2 +x7^2 + x8^2)^73 = 0 & (-3 + 6*x10^2 +x10^4 + 2*x10*x9 + 2*x10^3*x9 +x9^2)^21 = 0 & -1 +x13 +x11*x13 = 0 & x12=0)".asFormula,
  //      implyR(1) & dRI(1))
  //    println(pr)
  //    pr shouldBe 'proved
  //  }

  // TODO: Z3 gives slightly different but correct (unsimplified) results for next 3 test cases
  "p*>=0" should "compute p*>0 and p*=0" in withMathematica { _ =>
    val odeSys = "{x'=x^2+1, y'=2*x+y, z'=x+y+z & x=5}".asProgram.asInstanceOf[ODESystem]
    val poly = "x+y+z".asTerm
    val (pgt, (r, cof, gs)) = pStarGeq(odeSys, poly)
    pgt shouldBe "x+y+z>=0&(x+y+z=0->1+x*(3+x)+2*y+z>0)".asFormula
    r shouldBe 2
  }

  "f*>=0" should "compute f*" in withMathematica { _ =>
    val odeSys = "{x'=x^2+1, y'=2*x+y, z'=x+y+z & x=5}".asProgram.asInstanceOf[ODESystem]
    val fml = "y>=0 & x-z>=0|x+y*z>0 & x>=0 &x+y+z = 0".asFormula
    val fs = fStar(odeSys, fml)
    println(fs)
    fs._1 shouldBe
      "(y>=0&(y=0->2*x+y>0))&x-z>=0&(x-z=0->1+((-1)+x)*x+(-1)*y+(-1)*z>=0&(1+((-1)+x)*x+(-1)*y+(-1)*z=0->(-1)+((-1)+x)*x*(1+2*x)+(-2)*y+(-1)*z>0))|(x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>0)))&x>0&((-31)+z=0&36+y=0)&(-5)+x=0"
        .asFormula
  }

  "sAIc" should "take a local progress step" in withMathematica { _ =>
    val seq = "x>=0 ==> <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0, <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0".asSequent
    val pr = proveBy(seq, lpstep(2))
    println(pr)
    pr.subgoals should have size 2
    // Local progress into p>=0 requires p>0 | p=0 initially
    pr.subgoals(0) shouldBe "x>=0 ==> <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0, x>0|x=0".asSequent
    // In the p=0 case, more work needs to be done
    pr.subgoals(1) shouldBe
      "x>=0, x=0 ==> <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0, <{t_'=1,z'=2,x'=x+1,y'=1&1+x>=0}>t_!=0".asSequent
  }

  it should "take a local progress step with Dconstify" in withMathematica { _ =>
    val seq = "x>=0, a=1, b=1 ==> <{t_'=1,x'=a&x-a*b>=0}>t_!=0, <{t_'=1,x'=a&x-a*b>=0}>t_!=0".asSequent
    val pr = proveBy(seq, lpstep(2))
    println(pr)
    pr.subgoals should have size 2
    // Local progress into p>=0 requires p>0 | p=0 initially
    pr.subgoals(0) shouldBe "x>=0, a=1, b=1 ==> <{t_'=1,x'=a&x-a*b>=0}>t_!=0, x-a*b>0|x-a*b=0".asSequent
    // In the p=0 case, more work needs to be done
    pr.subgoals(1) shouldBe
      "x>=0, a=1, b=1, x-a*b=0 ==> <{t_'=1,x'=a&x-a*b>=0}>t_!=0, <{t_'=1,x'=a&a>=0}>t_!=0".asSequent
  }

  it should "package with real induction" in withQE { _ =>
    val fml =
      "-x<=0 & -y<=0 | x+y<=1 | y>=0 -> [{z'=2,x'=x+1,y'=1&x^2+y^2<1}] (-x<=0 & -y<=0 | x+y<=1 | y>=0)".asFormula
    val pr = proveBy(fml, implyR(1) & sAIclosed(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "try some invariants (1)" in withMathematica { _ =>
    val fml = "x^2+y^2>=1 -> [{x'=x-y^3, y'=x^3+y}]!(x^2+y^2<1/2)".asFormula
    val pr = proveBy(fml, implyR(1) & dC("(2*(x^2+y^2)-1>=0)".asFormula)(1) < (dW(1) & QE, sAIclosed(1)))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "try some invariants (1) in position" in withMathematica { _ =>
    val seq = "x^2+y^2>=1 ==> a>0, [{x'=x-y^3, y'=x^3+y}]!(x^2+y^2<1/2)".asSequent
    val pr = proveBy(seq, dC("(2*(x^2+y^2)-1>=0)".asFormula)(2) < (dW(2) & QE, sAIclosed(2)))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: try some invariants (1) in position" taggedAs TodoTest in withZ3 { _ =>
    val seq = "x^2+y^2>=1 ==> a>0, [{x'=x-y^3, y'=x^3+y}]!(x^2+y^2<1/2)".asSequent
    val pr = proveBy(seq, dC("(2*(x^2+y^2)-1>=0)".asFormula)(2) < (dW(2) & QE, sAIclosed(2)))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "try some invariants (2)" in withQE { _ =>
    val fml = "x=-1 & y=-1 & z=a -> [{x'=x*(x-2*y), y'=-(2*x-y)*y}](!(x>0 | y>0)& z=a)".asFormula
    val pr = proveBy(fml, implyR(1) & dC("((x<=0&x^2<=2*x*y)&y<=0)".asFormula)(1) < (dW(1) & QE, sAIclosed(1)))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "try some invariants (3)" in withQE { _ =>
    // The disjunct x=0 should become "trivial" in the progress proof
    val fml = "x <=0 | x=0 -> [{x'=x-1}] (x <=0 | x=0)".asFormula
    val pr = proveBy(fml, implyR(1) & sAIclosed(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  // TODO: fails on Z3 algebra tool step (bigint to long)
  it should "prove van der pol" in withMathematica { _ =>
    // the higher Lie derivatives are very nasty
    val fml = "1.25<=x&x<=1.55 & 2.35<=y&y<=2.45 -> [{x'=y, y'=y-x-x^2*y, t'=1 & 0<=t&t<=7}]!(y>=2.75)".asFormula
    // The actual invariant:
    val pr = proveBy(
      fml,
      implyR(1) & dC(
        "0.20595*x^4*y - 0.15329*x^4 - 1.1185*x^3*y + 1.7568*x^2*y^2 - 0.73732*x*y^3 + 0.13061*y^4 - 0.18577*x^3 - 0.12111*x^2*y + 0.074299*x*y^2 + 0.16623*y^3 - 1.6423*x^2 + 0.81389*x*y - 0.40302*y^2 - 0.88487*x + 0.35337*y - 3.7906<=0"
          .asFormula
      )(1) < (dW(1) & QE, sAIclosed(1)),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove duffing" in withMathematica { _ =>
    val fml =
      "(-((2*x)/5) + y)^2 <= 1/200 & x^2 <= 1/16 -> [{x'=y, y'=x - x^3 - y}] -(3/2) + x^2 + 4*y^2 <= 0".asFormula
    // The actual invariant:
    val pr = proveBy(
      fml,
      implyR(1) &
        dC(
          "-641 + 2*x - 5*y + 49039*y^2 + 115*y^3 + 397279*y^4 + 1022*y^5 + 64226*y^6 - 41291*x*y - 148*x*y^2 - 248650*x*y^3 - 362*x*y^4 - 11562*x*y^5 + 10969*x^2 + 17*x^2*y - 102496*x^2*y^2 - 18*x^2*y^3 + 10911*x^2*y^4 + 12*x^3 + 83659*x^3*y + 51*x^3*y^2 + 98766*x^3*y^3 - 20780*x^4 + 4*x^4*y + 66980*x^4*y^2 - 13*x^5 - 40639*x^5*y + 10000*x^6<=0"
            .asFormula
        )(1) <
        (
          dW(1) & QE,
          // this barrier certificate fails to prove with sAIclosed because its internal rank computation gets stuck
          // sAIclosed(1)
          sAIclosedPlus(3)(1),
        ),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove FM'18 constructed example" in withMathematica { _ =>
    val fml =
      "x1<=0 & x2<=0 & x3 <=0 -> [{x1'=2*x1+x2+2*x3-x1^2+x1*x3-x3^2, x2'=-2+x1-x2-x2^2, x3'=-2-x2-x3+x1^2-x1*x3}]!(x1+x2+x3>=1)"
        .asFormula
    val pr = proveBy(
      fml,
      implyR(1) &
        // B1,B2,B3 <=0
        dC(
          "1/100*(365*x1+365*x2+365*x3-60) <= 0 & 1/100*(175*x1+180*x2+100*x3-160)<=0 & 1/100*(460*x1+155*x2+270*x3-250)<=0"
            .asFormula
        )(1) < (dW(1) & QE, sAIclosed(1)),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove Strict(3) example" in withMathematica { _ =>
    // The invariant has a special point which requires the 3rd Lie derivative
    val fml =
      "(-4 + x^2 + y^2)*(-5*x*y + 1/2*(x^2 + y^2)^3) <= 0 & y>= 1/3 -> [{x'=2*(-(3/5) + x)*(1 - 337/225*(-(3/5) + x)^2 + 56/75 * (-(3/5) + x)*(-(4/5) + y) - 32/25 * (-(4/5) + y)^2) - y + 1/2 *x * (4 - x^2 - y^2), y'=x +  2*(1 - 337/225*(-(3/5) + x)^2 + 56/75*(-(3/5) + x)*(-(4/5) + y) - 32/25 * (-(4/5) + y)^2)*(-(4/5) + y) + 1/2 *y * (4 - x^2 - y^2)}]((-4 + x^2 + y^2)*(-5*x*y + 1/2*(x^2 + y^2)^3) <= 0 & y>= 1/3)"
        .asFormula
    val pr = proveBy(
      fml,
      implyR(1) &
        // this barrier certificate fails to prove with sAIclosed because its internal rank computation gets stuck
        // sAIclosed(1)
        sAIclosedPlus(3)(1),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  "Frozen time" should "freeze predicates with time (manual)" in withMathematica { _ =>
    val fml = "x+y=5 -> [{t'=1,x'=x^5+y, y'=x, c'=5 ,d'=100 & t=0 & c=1}]x+y=5".asFormula
    val pr = proveBy(
      fml,
      implyR(1) &
        // This is slightly optimized only to freeze the coordinates free in postcondition
        dC("(x-old(x))^2+(y-old(y))^2 <= (2*(x-x_0)*(x^5+y) + 2*(y-y_0)*x)*t".asFormula)(1) <
        (dW(1) & QE, dI(Symbol("full"))(1)),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "freeze predicates with time (auto)" in withMathematica { _ =>
    val fml = "x+y=5 -> [{t'=1,x'=x^5+y, y'=x, c'=5 ,d'=100 & t=0 & c=1}]x+y=5".asFormula
    val pr = proveBy(fml, implyR(1) & timeBound(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  "ODEInvariance" should "compute (bounded) p*>0" in withMathematica { _ =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asProgram.asInstanceOf[ODESystem]
    val poly = "x+y*z".asTerm
    val p0 = pStar(ode, poly, Some(0))
    val p1 = pStar(ode, poly, Some(1))
    val p2 = pStar(ode, poly, Some(2))
    val p3 = pStar(ode, poly, Some(3))
    val pn = pStar(ode, poly, None)

    println(p0)
    println(p1)
    println(p2)
    println(p3)
    println(pn)

    p0 shouldBe "x+y*z>0".asFormula
    p1 shouldBe "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>0)".asFormula
    p2 shouldBe
      "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>0))"
        .asFormula
    p3 shouldBe
      "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>=0&(2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)=0->2+6*x^4+12*y+12*y^2+8*(1+y)*z+2*x^3*(6+y+2*z)+4*x^2*(8+3*y+2*z)+x*(12+37*y+18*z)>0)))"
        .asFormula
  }

  it should "compute bounded P*" in withMathematica { _ =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asDifferentialProgram
    val poly = "max(min(z,min(x,y)),min(x,y))".asTerm
    val p0 = pStarHom(ode, poly, 0)
    val p1 = pStarHom(ode, poly, 1)
    val p2 = pStarHom(ode, poly, 2)
    val p3 = pStarHom(ode, poly, 3)
    // Huge mess of a formula here
    (p0, p1, p2, p3) shouldBe
      (
        "z>0&x>0&y>0|x>0&y>0".asFormula,
        "(z>=0&(z=0->x+y+z>0))&(x>=0&(x=0->1+x^2>0))&y>=0&(y=0->2*x+y>0)|(x>=0&(x=0->1+x^2>0))&y>=0&(y=0->2*x+y>0)"
          .asFormula,
        "(z>=0&(z=0->x+y+z>=0&(x+y+z=0->1+x*(3+x)+2*y+z>0)))&(x>=0&(x=0->1+x^2>=0&(1+x^2=0->2*(x+x^3)>0)))&y>=0&(y=0->2*x+y>=0&(2*x+y=0->2+2*x*(1+x)+y>0))|(x>=0&(x=0->1+x^2>=0&(1+x^2=0->2*(x+x^3)>0)))&y>=0&(y=0->2*x+y>=0&(2*x+y=0->2+2*x*(1+x)+y>0))"
          .asFormula,
        "(z>=0&(z=0->x+y+z>=0&(x+y+z=0->1+x*(3+x)+2*y+z>=0&(1+x*(3+x)+2*y+z=0->3+x*(7+x*(3+2*x))+3*y+z>0))))&(x>=0&(x=0->1+x^2>=0&(1+x^2=0->2*(x+x^3)>=0&(2*(x+x^3)=0->2+8*x^2+6*x^4>0))))&y>=0&(y=0->2*x+y>=0&(2*x+y=0->2+2*x*(1+x)+y>=0&(2+2*x*(1+x)+y=0->2+2*x*(3+x+2*x^2)+y>0)))|(x>=0&(x=0->1+x^2>=0&(1+x^2=0->2*(x+x^3)>=0&(2*(x+x^3)=0->2+8*x^2+6*x^4>0))))&y>=0&(y=0->2*x+y>=0&(2*x+y=0->2+2*x*(1+x)+y>=0&(2+2*x*(1+x)+y=0->2+2*x*(3+x+2*x^2)+y>0)))"
          .asFormula,
      )
    println(p0, p1, p2, p3)
  }

  it should "aggressively try rank 1" in withMathematica { _ =>
    val ode = "{x'=x*(x-2*y), y'=-(2*x-y)*y}".asDifferentialProgram
    val fml = "((x^2-2*x*y<=0 & x<=0)&y<=0)".asFormula
    val res = rankOneFml(ode, True, fml)
    // Reorder the conjuncts
    println(res)
    res shouldBe Some("x<=0&y<=0&x^2-2*x*y<=0&true".asFormula)
  }

  it should "try rank 1 invariants (1)" in withQE { _ =>
    val seq = "x=-1 & y=-1 -> [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asFormula
    val pr =
      proveBy(seq, implyR(1) & dC("x=0&y=0 | (x^2<=2*x*y)&x<=0&y<=0".asFormula)(1) < (dW(1) & QE, sAIRankOne(true)(1)))
    println("proved: ", pr)
    pr shouldBe Symbol("proved")
  }

  it should "try rank 1 invariants (1) in position" in withQE { _ =>
    val seq = "x=-1 & y=-1 ==> a>0 , [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asSequent
    val pr = proveBy(seq, dC("x=0&y=0 | (x^2<=2*x*y)&x<=0&y<=0".asFormula)(2) < (dW(2) & QE, sAIRankOne(true)(2)))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "try rank 1 invariants (1) without reorder" in withQE { _ =>
    val seq = "x=-1 & y=-1 -> [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asFormula
    // Tactic fails when given wrong ordering of conjuncts
    val pr = proveBy(
      seq,
      implyR(1) & dC("x=0&y=0 | x<=0&y<=0 & (x^2<=2*x*y)".asFormula)(1) < (dW(1) & QE, sAIRankOne(false)(1)),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "try a (very) difficult invariant" in withQE { _ =>
    val fml = "1/100 - x^2 - y^2 >= 0 -> [{x'=-2*x+x^2+y, y'=x-2*y+y^2 & x!=0 | y!=0}]!(x^2+y^2 >= 1/4)".asFormula
    // Original question did not have x!=0 | y!=0 constraint
    // Pegasus invariant: ((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)&-1+4*x^2+4*y^2 < 0
    // However, the equilibrium point at the origin for x*y<=x^2+y^2 is insurmountable for all current tactics
    val pr =
      proveBy(fml, implyR(1) & dC("((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)".asFormula)(1) < (dW(1), sAIclosedPlus(1)(1)))
    // This needs a strict inequality to prove
    println(pr)

    // The actual invariant proves with the specialized rank 1 tactic:
    val pr2 = proveBy(
      fml,
      implyR(1) &
        dC("((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)&-1+4*x^2+4*y^2 < 0".asFormula)(1) < (dW(1) & QE, sAIRankOne(true)(1)),
    )
    println(pr2)
    pr2 shouldBe Symbol("proved")
  }

  it should "prove with consts (sAIRankOne)" in withQE { _ =>
    val fml = "x>=0 & y>=0 -> [{x'=x+y}](x>=0 & y>=0)".asFormula
    // This worked out because the tactic reorders y>=0 before x>=0
    val pr = proveBy(fml, implyR(1) & sAIRankOne(true)(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove with consts (auto andL)" in withQE { _ =>
    val fml = "x>=0 & y>0 -> [{x'=x+y}](x>=0 & y>0)".asFormula
    val pr = proveBy(fml, implyR(1) & odeInvariant(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "ignore bad dbx cofactors" in withQE { _ =>
    val fml = "x>=5 & y>=0 -> [{x'=x^2+y,y'=x}](x>=1 & y>=0)".asFormula
    // This won't work because neither conjunct is rank 1
    // In addition, Mathematica returns a rational function answer for the polynomial division
    // val pr = proveBy(fml, implyR(1) & sAIRankOne(1))
    // Fortunately, sAIclosedPlus is a fallback
    val pr = proveBy(fml, implyR(1) & sAIclosedPlus()(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "false and true invariant" in withQE { _ =>
    val fmlF = "false -> [{x'=x^2+y,y'=x}]false".asFormula
    val fmlT = "true -> [{x'=x^2+y,y'=x}]true".asFormula
    val prF = proveBy(fmlF, implyR(1) & odeInvariant(1))
    val prT = proveBy(fmlT, implyR(1) & odeInvariant(1))
    prF shouldBe Symbol("proved")
    prT shouldBe Symbol("proved")
  }

  it should "put postcondition into NNF first" in withQE { _ =>
    val fml3 = "!!!(x < 0) -> [{x'=x^10}]!!!(x<0)".asFormula
    val pr = proveBy(fml3, implyR(1) & odeInvariant(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove wien bridge with barrier certificate" in withMathematica { _ =>
    val fml =
      "x^2<=1/2&y^2<=1/3->[{x'=-x-1117*y/500+439*y^3/200-333*y^5/500,y'=x+617*y/500-439*y^3/200+333*y^5/500&true}]x-4*y < 8"
        .asFormula
    val pr = proveBy(
      fml,
      implyR(1) &
        dC(
          "0.29974*x^4 + 0.88095*x^3*y + 1.2781*x^2*y^2 + 1.0779*x*y^3 + \n 0.36289*y^4 - 0.064049*x^3 - 0.31889*x^2*y - 0.55338*x*y^2 - \n 0.33535*y^3 + 0.63612*x^2 + 0.44252*x*y + 1.4492*y^2 + 0.28572*x - \n 0.051594*y - 2.1067 <= 0 & x-4*y <= 8"
            .asFormula
        )(1) <
        (
          dW(1) & QE,
          // dgBarrier(1)
          sAIclosedPlus()(1),
        ),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove example where Darboux heuristic fails" in withZ3 { _ =>
    val seq =
      "2*g()*x<=2*g()*H()-v_0^2&x>=0, g()>0, 1>=c(), c()>=0, r()>=0, x=0, v=-c()*v_0\n  ==>  [{x'=v,v'=-g()-r()*v^2&x>=0&v>=0}]2*g()*x<=2*g()*H()-v^2"
        .asSequent
    val pr = proveBy(seq, odeInvariant(1))
    pr shouldBe Symbol("proved")
  }

  "SAI" should "compute p*>=0" in withMathematica { _ =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asProgram.asInstanceOf[ODESystem]
    val poly = "x+y*z".asTerm
    val p0 = pStar(ode, poly, Some(0))
    val p1 = pStar(ode, poly, Some(1))
    val p2 = pStar(ode, poly, Some(2))
    val p3 = pStar(ode, poly, Some(3))
    val pn = pStar(ode, poly, None)

    println(p0)
    println(p1)
    println(p2)
    println(p3)
    println(pn)

    p0 shouldBe "x+y*z>0".asFormula
    p1 shouldBe "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>0)".asFormula
    p2 shouldBe
      "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>0))"
        .asFormula
    p3 shouldBe
      "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>=0&(2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)=0->2+6*x^4+12*y+12*y^2+8*(1+y)*z+2*x^3*(6+y+2*z)+4*x^2*(8+3*y+2*z)+x*(12+37*y+18*z)>0)))"
        .asFormula
  }

  "nilpotent solver" should "fail fast on various problematic examples" in withMathematica { _ =>
    // Non-linear ODE
    val pr = proveBy("[{x'=y,y'=x^2}] x+v+a+j=1".asFormula, ?(nilpotentSolve(false)(1)))

    // Linear but not nilpotent
    val pr2 = proveBy("[{x'=a()*y,y'=b*x}] x+v+a+j=1".asFormula, ?(nilpotentSolve(false)(1)))

    pr should not be Symbol("proved")
    pr2 should not be Symbol("proved")
  }

  it should "solve ODE with correct positioning" in withQE { _ =>
    def time[T](block: => T): T = {
      val start = System.currentTimeMillis
      val res = block
      val totalTime = System.currentTimeMillis - start
      println("Elapsed time: %1d ms".format(totalTime))
      res
    }

    val seq = "x=0&v=0 ==> j!=1,[{x'=v,v'=a, a'=j & x+v+a <= 100}] x+v+a>=0, a!=0".asSequent

    val pr = time { proveBy(seq, nilpotentSolve(false)(2) & dWPlus(3) & QE) }
    pr shouldBe Symbol("proved")

    val pr2 = time { proveBy(seq, nilpotentSolve(true)(2)) }
    pr2 shouldBe Symbol("proved")

    val pr3 = time { proveBy(seq, solve(2) & QE) }
    pr3 shouldBe Symbol("proved")
  }

  it should "solve ODE quickly (1)" in withQE { _ =>
    def time[T](block: => T): T = {
      val start = System.currentTimeMillis
      val res = block
      val totalTime = System.currentTimeMillis - start
      println("Elapsed time: %1d ms".format(totalTime))
      res
    }

    val fml = "x=0&v=0&a=1 -> [{x'=v,v'=a & x+v+a <= 100}] x+v+a>=0".asFormula

    val pr = time { proveBy(fml, implyR(1) & nilpotentSolve(false)(1) & dWPlus(1) & QE) }
    pr shouldBe Symbol("proved")

    // Simulate solveEnd
    val pr2 = time { proveBy(fml, implyR(1) & nilpotentSolve(true)(1)) }
    pr2 shouldBe Symbol("proved")

    val pr3 = time { proveBy(fml, implyR(1) & solve(1) & QE) }
    pr3 shouldBe Symbol("proved")
  }

  // TODO: Z3 too slow
  it should "solve ODE quickly (2)" in withMathematica { _ =>
    def time[T](block: => T): T = {
      val start = System.currentTimeMillis
      val res = block
      val totalTime = System.currentTimeMillis - start
      println("Elapsed time: %1d ms".format(totalTime))
      res
    }

    val fml = "x=0&v=0&a=0&j=0&k=1&l=0 -> [{k'=l,l'=1,x'=v,v'=a,a'=j,j'=k & x+x*v+a+j+k <= 100}] x+v+a+j+k>=0".asFormula
    val pr = time { proveBy(fml, implyR(1) & nilpotentSolve(false)(1) & dWPlus(1) & QE) }
    pr shouldBe Symbol("proved")

    val pr2 = time { proveBy(fml, implyR(1) & nilpotentSolve(true)(1)) }
    pr2 shouldBe Symbol("proved")

    val pr3 = time { proveBy(fml, implyR(1) & solve(1) & QE) }
    pr3 shouldBe Symbol("proved")
  }

  it should "put an obfuscated ODE into linear form and cut solution" in withMathematica { _ =>
    // x'   (2 2 -2) x    A
    // y' = (5 1 -3) y + -B
    // z'   (1 5 -3) z   5C
    val pr = proveBy(
      "x=1&y=1&A()=1 -> [{x'=2*(-z+x+y)+A(),y'=y+5*x-3*z-B(),z'=x-3*z+5*(y+C)}] x+y+z >= 0".asFormula,
      // val pr = proveBy("x=1&y=1 -> [{x'=x+y,y'=-x-y}] x=0".asFormula,
      implyR(1) & nilpotentSolve(false)(1) & dWPlus(1) & SaturateTactic(andL(Symbol("Llast"))),
    )

    pr.subgoals(0).ante.length shouldBe 7
    pr.subgoals(0).ante(4) shouldBe
      "x=2/3*(3*A()+B()+(-5)*C)*time_^3+x_0+time_*(A()+2*(x_0+y_0+(-1)*z_0))+time_^2*(A()+(-1)*B()+(-5)*C+6*x_0+(-2)*(y_0+z_0))"
        .asFormula
    pr.subgoals(0).ante(5) shouldBe
      "y=2/3*(3*A()+B()+(-5)*C)*time_^3+y_0+time_*((-1)*B()+5*x_0+y_0+(-3)*z_0)+1/2*time_^2*(5*A()+(-1)*B()+(-15)*C+12*x_0+(-4)*(y_0+z_0))"
        .asFormula
    pr.subgoals(0).ante(6) shouldBe
      "z=4/3*(3*A()+B()+(-5)*C)*time_^3+time_*(5*C+x_0+5*y_0+(-3)*z_0)+z_0+1/2*time_^2*(A()+(-5)*B()+(-15)*C+24*x_0+(-8)*(y_0+z_0))"
        .asFormula
  }

  it should "not dW when unprovable" in withMathematica { _ =>
    val result = proveBy(
      "l() < r(), l()<=x, x<=r(), x=l() ==> [{x'=1&l()>=x|x>=r()}](l()<=x&x<=r())".asSequent,
      nilpotentSolve(true)(1),
    )
    result.subgoals.loneElement shouldBe
      "l() < r(), l()<=x_0, x_0<=r(), x_0=l(), l()>=x_0|x_0>=r(), time_=0, x_0=x ==> [{x'=1,time_'=1&(l()>=x|x>=r())&time_>=0&x=time_+x_0}](l()<=x&x<=r())"
        .asSequent
  }

  "diffDivConquer" should "divide and conquer" in withMathematica { _ =>
    val pr = proveBy(
      "x*y=1 , A() = 5 ==> x > b() , [{x'=A() * x & b() * x < A()}] x=b()+A()".asSequent,
      diffDivConquer("x".asTerm)(2),
    )

    pr.subgoals(0) shouldBe "x*y=1, A()=5, x=0  ==>  x>b(), [{x'=A()*x&b()*x < A()&x=0}]x=b()+A()".asSequent
    pr.subgoals(1) shouldBe "x*y=1, A()=5, x>0  ==>  x>b(), [{x'=A()*x&b()*x < A()&x>0}]x=b()+A()".asSequent
    pr.subgoals(2) shouldBe "x*y=1, A()=5, x<0  ==>  x>b(), [{x'=A()*x&b()*x < A()&x<0}]x=b()+A()".asSequent

  }

  "dfp" should "do dfp" in withMathematica { _ =>
    val seq =
      "x=1 , y=2 , z=3 , a=4, B > 0 ==> [{z'=a-z-x, x'=B*(a-z-x)*(z-x-y), a'=x^2*y^2*z^2*(y-2*x)}] (x<z^2+B)".asSequent
    val pr = proveBy(seq, dFP(1) & dW(1) & QE)
    println(pr)
    pr shouldBe Symbol("proved")
  }

  "domainStuck" should "work on a simple example" in withMathematica { _ =>
    val pr = proveBy("x=1 ==> [{x'=-x & x>=1}]x=1".asSequent, domainStuck(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "work on a parametric example" in withMathematica { _ =>
    val pr = proveBy(
      "x=1 & v = 0 & a = 0 & b() < 0 & c() > 0 ==> [{v'=a,x'=c() * v,a'=b() & x>=1 | x^2>=1 & x >= -5 | x <= -2 }]x <= 5"
        .asSequent,
      domainStuck(1),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "work on a simple example in other positions" in withMathematica { _ =>
    val pr = proveBy("==> [{x'=-x & x>=1}]x=1, x!=1".asSequent, domainStuck(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "work on a parametric example in other positions" in withMathematica { _ =>
    val pr = proveBy(
      ("x=1 & v = 0 & c() > 0 ==>" +
        "a!= 0,[{v'=a,x'=c() * v,a'=b() & x>=1 | x^2>=1 & x >= -5 | x <= -2 }]x <= 5, b() >= 0, [{x'=x}]x<1").asSequent,
      domainStuck(2),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  "SAI" should "prove simple inv" in withMathematica { _ =>
    val pr = proveBy(
      "x = 1 -> x > 1 | [{x'=x+y,y'=y+x+z&y=0}](x>0 | (x^3 > 0 & x <= 1))".asFormula,
      implyR(1) & orR(1) & sAI(2),
    )

    println(pr)
    println("Proof steps:", pr.steps)
    pr shouldBe Symbol("proved")
  }

  it should "work with domains" in withMathematica { _ =>
    val pr = proveBy("x = 1 -> [{x'=y,y'=-x&x>=0 | y>=0 | x > 0 & y > 0}](x>-1 & x>=0)".asFormula, implyR(1) & sAI(1))

    println(pr)
    println("Proof steps:", pr.steps)
    pr shouldBe Symbol("proved")
  }

  it should "prove a difficult invariant" in withMathematica { _ =>
    val fml =
      "a() = 0 & 1/100 - x^2 - y^2 >= a() -> a()=1 | [{x'=-2*x+x^2+y, y'=x-2*y+y^2+a()}]!(x^2+y^2 >= 1/4)".asFormula
    val pr = proveBy(fml, implyR(1) & andL(-1) & orR(1) & sAI(2))
    println(pr)
    println("Proof steps:", pr.steps)
    pr shouldBe Symbol("proved")
  }

  it should "prove a simple inv" in withMathematica { _ =>
    val fml = "x>0 -> [{x'=x}] x>0".asFormula
    val pr = proveBy(fml, implyR(1) & sAI(1))
    println(pr)
    println("Proof steps:", pr.steps)
    pr shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: support division/square root" taggedAs TodoTest in withMathematica { _ =>
    val s = """g>0 & p>a & a>0 & T>0 & m< -(g/p)^(1/2) &
              |  x>=0 & v<0 & v> -(g/p)^(1/2) & r=a
              |==>
              |[ {
              |    {
              |      ?(v - g*T > -(g/p)^(1/2) & r = a);
              |      ++
              |      r := p;
              |    }
              |    t := 0;
              |    {x'=v, v'=-g+r*v^2, t'=1 & t<=T & x>=0 & v<0}
              |  }*
              |](x=0 -> v>=m)
              |""".stripMargin.asSequent
    // @todo sAI causes singularities in dG because it hides the assumptions g>0, p>a, a>0
    proveBy(s, autoClose) shouldBe Symbol("proved")
  }

  "ode rewrite" should "prove an ODE rewrite" in withMathematica { _ =>
    val pr = proveBy(
      "[{x'=-(z+5)+10,y'=y*y+y-y&z=2}]x+y>=1000 -> [{x'=3,y'=y^2&z=2}]x+y>=1000 ".asFormula,
      implyR(1) & rewriteODEAt("x'=-(z+5)+10,y'=y*y+y-y".asDifferentialProgram)(1) & id,
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "rewrite at any top position" in withMathematica { _ =>
    val pr = proveBy(
      "[{x'=1+1}]x>0,<{x'=1+1}>x>0  ==> <{x'=1+1}>x>0,[{x'=1+1}]x>0  ".asSequent,
      rewriteODEAt("x'=2".asDifferentialProgram)(2) & rewriteODEAt("x'=2".asDifferentialProgram)(-2) &
        rewriteODEAt("x'=2".asDifferentialProgram)(-1) & rewriteODEAt("x'=2".asDifferentialProgram)(1),
    )

    println(pr)
    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "[{x'=2}]x>0, <{x'=2}>x>0  ==>  <{x'=2}>x>0, [{x'=2}]x>0".asSequent
  }

  it should "rewrite with predicates" in withMathematica { _ =>
    val pr = proveBy("==> [{x'=x&x>0&q(x)}]x>0".asSequent, rewriteODEAt("x'=--x+x-x".asDifferentialProgram)(1))

    println(pr)
    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "==>  [{x'=--x+x-x&x>0&q(x)}]x>0".asSequent
  }
}
