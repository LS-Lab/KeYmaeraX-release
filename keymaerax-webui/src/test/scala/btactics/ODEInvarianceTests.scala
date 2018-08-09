package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{PosInExpr, SaturateTactic, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.ODEInvariance._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.IndexedSeq

class ODEInvarianceTests extends TacticTestBase {

  "ODEInvariance" should "compute (bounded) p*>0" in withMathematica { qeTool =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asProgram.asInstanceOf[ODESystem]
    val poly = "x+y*z".asTerm
    val p0 = pStar(ode,poly,Some(0))
    val p1 = pStar(ode,poly,Some(1))
    val p2 = pStar(ode,poly,Some(2))
    val p3 = pStar(ode,poly,Some(3))
    val pn = pStar(ode,poly,None)

    //println(p0)
    //println(p1)
    //println(p2)
    //println(p3)
    //println(pn)

    p0 shouldBe "x+y*z>0".asFormula
    p1 shouldBe "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>0)".asFormula
    p2 shouldBe "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>0))".asFormula
    p3 shouldBe "x+y*z>=0&(x+y*z=0->1+x^2+x*y+y^2+2*(x+y)*z>=0&(1+x^2+x*y+y^2+2*(x+y)*z=0->2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)>=0&(2*x^3+y+2*z+4*y*(y+z)+x^2*(4+y+2*z)+x*(2+9*y+6*z)=0->2+6*x^4+12*y+12*y^2+8*(1+y)*z+2*x^3*(6+y+2*z)+4*x^2*(8+3*y+2*z)+x*(12+37*y+18*z)>0)))".asFormula
  }

  it should "compute bounded P*" in withMathematica { qeTool =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asDifferentialProgram
    val poly = "max(min(z,min(x,y)),min(x,y))".asTerm
    val p0 = pStarHom(ode,poly,0)
    val p1 = pStarHom(ode,poly,1)
    val p2 = pStarHom(ode,poly,2)
    val p3 = pStarHom(ode,poly,3)
    //Huge mess of a formula here
    (p0,p1,p2,p3) shouldBe
      ("z>0&x>0&y>0|x>0&y>0".asFormula,
       "(z>=0&(z=0->x+y+z>0))&(x>=0&(x=0->1+x^2>0))&y>=0&(y=0->2*x+y>0)|(x>=0&(x=0->1+x^2>0))&y>=0&(y=0->2*x+y>0)".asFormula,
       "(z>=0&(z=0->x+y+z>=0&(x+y+z=0->1+x*(3+x)+2*y+z>0)))&(x>=0&(x=0->1+x^2>=0&(1+x^2=0->2*(x+x^3)>0)))&y>=0&(y=0->2*x+y>=0&(2*x+y=0->2+2*x*(1+x)+y>0))|(x>=0&(x=0->1+x^2>=0&(1+x^2=0->2*(x+x^3)>0)))&y>=0&(y=0->2*x+y>=0&(2*x+y=0->2+2*x*(1+x)+y>0))".asFormula,
       "(z>=0&(z=0->x+y+z>=0&(x+y+z=0->1+x*(3+x)+2*y+z>=0&(1+x*(3+x)+2*y+z=0->3+x*(7+x*(3+2*x))+3*y+z>0))))&(x>=0&(x=0->1+x^2>=0&(1+x^2=0->2*(x+x^3)>=0&(2*(x+x^3)=0->2+8*x^2+6*x^4>0))))&y>=0&(y=0->2*x+y>=0&(2*x+y=0->2+2*x*(1+x)+y>=0&(2+2*x*(1+x)+y=0->2+2*x*(3+x+2*x^2)+y>0)))|(x>=0&(x=0->1+x^2>=0&(1+x^2=0->2*(x+x^3)>=0&(2*(x+x^3)=0->2+8*x^2+6*x^4>0))))&y>=0&(y=0->2*x+y>=0&(2*x+y=0->2+2*x*(1+x)+y>=0&(2+2*x*(1+x)+y=0->2+2*x*(3+x+2*x^2)+y>0)))".asFormula)
    println(p0,p1,p2,p3)
  }

  it should "take a local progress step" in withMathematica { qeTool =>
    val seq = "x>=0 ==> <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0, <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0".asSequent
    val pr = proveBy(seq, lpstep(2))
    println(pr)
    pr.subgoals should have size 2
    //Local progress into p>=0 requires p>0 | p=0 initially
    pr.subgoals(0) shouldBe "x>=0 ==> <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0, x>0|x=0".asSequent
    //In the p=0 case, more work needs to be done
    pr.subgoals(1) shouldBe "x>=0, x=0 ==> <{t_'=1,z'=2,x'=x+1,y'=1&x>=0}>t_!=0, <{t_'=1,z'=2,x'=x+1,y'=1&1+x>=0}>t_!=0".asSequent
  }

  it should "package with real induction" in withMathematica { qeTool =>
    val fml = "-x<=0 & -y<=0 | x+y<=1 | y>=0 -> [{z'=2,x'=x+1,y'=1&x^2+y^2<1}] (-x<=0 & -y<=0 | x+y<=1 | y>=0)".asFormula
    val pr = proveBy(fml, implyR(1) & sAIclosedPlus(0)(1))
    println(pr)
    pr shouldBe 'proved
  }

  it should "try some invariants (1)" in withMathematica { qeTool =>
    val fml = "x^2+y^2>=1 -> [{x'=x-y^3, y'=x^3+y}]!(x^2+y^2<1/2)".asFormula
    val pr = proveBy(fml, implyR(1) &
      dC("(2*(x^2+y^2)-1>=0)".asFormula)(1) <(
        dW(1) & QE,
        sAIclosedPlus()(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "try some invariants (1) in position" in withMathematica { qeTool =>
    val seq = "x^2+y^2>=1 ==> a>0, [{x'=x-y^3, y'=x^3+y}]!(x^2+y^2<1/2)".asSequent
    val pr = proveBy(seq,
      dC("(2*(x^2+y^2)-1>=0)".asFormula)(2) <(
        dW(2) & QE,
        sAIclosedPlus()(2)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "try some invariants (2)" ignore withMathematica { qeTool =>
    val fml = "x=-1 & y=-1 -> [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asFormula
    //This is an invariant which cannot be proved by the current tactic
    //But it could be proved by re-ordering in a smarter way
    val pr = proveBy(fml, implyR(1) &
      dC("((x<=0&x^2<=2*x*y)&y<=0)".asFormula)(1) <(
        dW(1) & QE,
        (?(sAIclosedPlus(3)(1)))
      )
    )
    println(pr)
    //pr shouldBe 'proved
  }

  it should "try some invariants (3)" in withMathematica { qeTool =>
    //The disjunct x=0 should become "trivial" in the progress proof
    val fml = "x <=0 | x=0 -> [{x'=x-1}] (x <=0 | x=0)".asFormula
    val pr = proveBy(fml, implyR(1) &
        sAIclosedPlus(3)(1)
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "aggressively try rank 1" in withMathematica { qeTool =>
    val ode = "{x'=x*(x-2*y), y'=-(2*x-y)*y}".asDifferentialProgram
    val fml = "((x^2-2*x*y<=0 & x<=0)&y<=0)".asFormula
    val res = rankOneFml(ode,True,fml)
    //Reorder the conjuncts
    println(res)
    res shouldBe Some("x<=0&y<=0&x^2-2*x*y<=0&true".asFormula)
  }

  it should "try rank 1 invariants (1)" in withMathematica { qeTool =>
    val seq = "x=-1 & y=-1 -> [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asFormula
    val pr = proveBy(seq, implyR(1) &
      dC("x=0&y=0 | (x^2<=2*x*y)&x<=0&y<=0".asFormula)(1) <(
        dW(1) & QE,
        sAIRankOne(true)(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "try rank 1 invariants (1) in position" in withMathematica { qeTool =>
    val seq = "x=-1 & y=-1 ==> a>0 , [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asSequent
    val pr = proveBy(seq,
      dC("x=0&y=0 | (x^2<=2*x*y)&x<=0&y<=0".asFormula)(2) <(
        dW(2) & QE,
        sAIRankOne(true)(2)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "try rank 1 invariants (1) without reorder" in withMathematica { qeTool =>
    val seq = "x=-1 & y=-1 -> [{x'=x*(x-2*y), y'=-(2*x-y)*y}]!(x>0 | y>0)".asFormula
    //Tactic fails when given wrong ordering of conjuncts
    val pr = proveBy(seq, implyR(1) &
      dC("x=0&y=0 | x<=0&y<=0 & (x^2<=2*x*y)".asFormula)(1) <(
        dW(1) & QE,
        sAIRankOne(false)(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "try a (very) difficult invariant" in withMathematica { qeTool =>
    val fml = "1/100 - x^2 - y^2 >= 0 -> [{x'=-2*x+x^2+y, y'=x-2*y+y^2 & x!=0 | y!=0}]!(x^2+y^2 >= 1/4)".asFormula
    //Original question did not have x!=0 | y!=0 constraint
    //Pegasus invariant: ((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)&-1+4*x^2+4*y^2 < 0
    //However, the equilibrium point at the origin for x*y<=x^2+y^2 is insurmountable for all current tactics
    val pr = proveBy(fml, implyR(1) &
      dC("((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)".asFormula)(1) <(
        dW(1),
        sAIclosedPlus(1)(1)
      )
    )
    //This needs a strict inequality to prove
    println(pr)

    //The actual invariant proves with the specialized rank 1 tactic:
    val pr2 = proveBy(fml, implyR(1) &
      dC("((x*y<=x^2+y^2&x+y<=2)&4*(x^2+y^2)<=1)&-1+4*x^2+4*y^2 < 0".asFormula)(1) <(
        dW(1) & QE,
        sAIRankOne(true)(1)
      )
    )
    println(pr2)
    pr2 shouldBe 'proved
  }

  it should "prove van der pol" in withMathematica { qeTool =>
    val fml = "1.25<=x&x<=1.55 & 2.35<=y&y<=2.45 -> [{x'=y, y'=y-x-x^2*y, t'=1 & 0<=t&t<=7}]!(y>=2.75)".asFormula
    //The actual invariant:
    val pr = proveBy(fml, implyR(1) &
      dC("0.20595*x^4*y - 0.15329*x^4 - 1.1185*x^3*y + 1.7568*x^2*y^2 - 0.73732*x*y^3 + 0.13061*y^4 - 0.18577*x^3 - 0.12111*x^2*y + 0.074299*x*y^2 + 0.16623*y^3 - 1.6423*x^2 + 0.81389*x*y - 0.40302*y^2 - 0.88487*x + 0.35337*y - 3.7906<=0".asFormula)(1) <(
        dW(1) & QE,
        //dgBarrier(1)
        sAIclosedPlus()(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "prove duffing" in withMathematica { qeTool =>
    val fml = "(-((2*x)/5) + y)^2 <= 1/200 & x^2 <= 1/16 -> [{x'=y, y'=x - x^3 - y}] -(3/2) + x^2 + 4*y^2 <= 0".asFormula
    //The actual invariant:
    val pr = proveBy(fml, implyR(1) &
      dC("-641 + 2*x - 5*y + 49039*y^2 + 115*y^3 + 397279*y^4 + 1022*y^5 + 64226*y^6 - 41291*x*y - 148*x*y^2 - 248650*x*y^3 - 362*x*y^4 - 11562*x*y^5 + 10969*x^2 + 17*x^2*y - 102496*x^2*y^2 - 18*x^2*y^3 + 10911*x^2*y^4 + 12*x^3 + 83659*x^3*y + 51*x^3*y^2 + 98766*x^3*y^3 - 20780*x^4 + 4*x^4*y + 66980*x^4*y^2 - 13*x^5 - 40639*x^5*y + 10000*x^6<=0".asFormula)(1) <(
        dW(1) & QE,
        //dgBarrier(1)
        sAIclosedPlus()(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "prove FM'18 constructed example" in withMathematica { qeTool =>
    val fml = "x1<=0 & x2<=0 & x3 <=0 -> [{x1'=2*x1+x2+2*x3-x1^2+x1*x3-x3^2, x2'=-2+x1-x2-x2^2, x3'=-2-x2-x3+x1^2-x1*x3}]!(x1+x2+x3>=1)".asFormula
    val pr = proveBy(fml, implyR(1) &
      //B1,B2,B3 <=0
      dC("1/100*(365*x1+365*x2+365*x3-60) <= 0 & 1/100*(175*x1+180*x2+100*x3-160)<=0 & 1/100*(460*x1+155*x2+270*x3-250)<=0".asFormula)(1) <(
        dW(1) & QE,
        //dgBarrier(1)
        sAIclosedPlus()(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "prove Strict(3) example" in withMathematica { qeTool =>
    //The invariant has a special point which requires the 3rd Lie derivative
    val fml = "(-4 + x^2 + y^2)*(-5*x*y + 1/2*(x^2 + y^2)^3) <= 0 & y>= 1/3 -> [{x'=2*(-(3/5) + x)*(1 - 337/225*(-(3/5) + x)^2 + 56/75 * (-(3/5) + x)*(-(4/5) + y) - 32/25 * (-(4/5) + y)^2) - y + 1/2 *x * (4 - x^2 - y^2), y'=x +  2*(1 - 337/225*(-(3/5) + x)^2 + 56/75*(-(3/5) + x)*(-(4/5) + y) - 32/25 * (-(4/5) + y)^2)*(-(4/5) + y) + 1/2 *y * (4 - x^2 - y^2)}]((-4 + x^2 + y^2)*(-5*x*y + 1/2*(x^2 + y^2)^3) <= 0 & y>= 1/3)".asFormula
    val pr = proveBy(fml, implyR(1) &
      sAIclosedPlus(3)(1)
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "prove with consts (sAIRankOne)" in withMathematica { qeTool =>
    val fml = "x>=0 & y>=0 -> [{x'=x+y}](x>=0 & y>=0)".asFormula
    //This worked out because the tactic reorders y>=0 before x>=0
    val pr = proveBy(fml, implyR(1) &
      sAIRankOne(true)(1)
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "prove with consts (auto const)" in withMathematica { qeTool =>
    val fml = "x>=0 & y>0 -> [{x'=x+y}](x>=0 & y>0)".asFormula
    val pr = proveBy(fml, implyR(1) & andL(-1) & odeInvariant(1))
    println(pr)
    pr shouldBe 'proved
  }

  it should "ignore bad dbx cofactors" in withMathematica { qeTool =>
    val fml = "x>=5 & y>=0 -> [{x'=x^2+y,y'=x}](x>=1 & y>=0)".asFormula
    // This won't work because neither conjunct is rank 1
    // In addition, Mathematica returns a rational function answer for the polynomial division
    // val pr = proveBy(fml, implyR(1) & sAIRankOne(1))
    // Fortunately, sAIclosedPlus is a fallback
    val pr = proveBy(fml, implyR(1) & sAIclosedPlus()(1))
    println(pr)
    pr shouldBe 'proved
  }

  it should "false and true invariant" in withMathematica { qeTool =>
    val fmlF = "false -> [{x'=x^2+y,y'=x}]false".asFormula
    val fmlT = "true -> [{x'=x^2+y,y'=x}]true".asFormula
    val prF = proveBy(fmlF, implyR(1) & odeInvariant(1))
    val prT = proveBy(fmlT, implyR(1) & odeInvariant(1))
    prF shouldBe 'proved
    prT shouldBe 'proved
  }

  it should "put postcondition into NNF first" in withMathematica { _ =>
    val fml3 = "!!!(x < 0) -> [{x'=x^10}]!!!(x<0)".asFormula
    val pr = proveBy(fml3,implyR(1) & odeInvariant(1))
    println(pr)
    pr shouldBe'proved
  }

  it should "prove wien bridge with barrier certificate" in withMathematica { qeTool =>
    val fml = "x^2<=1/2&y^2<=1/3->[{x'=-x-1117*y/500+439*y^3/200-333*y^5/500,y'=x+617*y/500-439*y^3/200+333*y^5/500&true}]x-4*y < 8".asFormula
    val pr = proveBy(fml, implyR(1) &
      dC("0.29974*x^4 + 0.88095*x^3*y + 1.2781*x^2*y^2 + 1.0779*x*y^3 + \n 0.36289*y^4 - 0.064049*x^3 - 0.31889*x^2*y - 0.55338*x*y^2 - \n 0.33535*y^3 + 0.63612*x^2 + 0.44252*x*y + 1.4492*y^2 + 0.28572*x - \n 0.051594*y - 2.1067 <= 0 & x-4*y <= 8".asFormula)(1) <(
      dW(1) & QE,
      //dgBarrier(1)
      sAIclosedPlus()(1)
    ))
    println(pr)
    pr shouldBe 'proved
  }

  it should "normalize invariants" ignore withMathematica { _ =>
    //@note fails because rank
    val normalizedSeq = "(1/2*x<=x & x<=7/10 & 0<=y & y<=3/10) ==> [{x'=-x+x*y, y'=-y}](-4/5 < x | x < -1 | -7/10 < y | y < -1)".asSequent
    proveBy(normalizedSeq, odeInvariant(1)) shouldBe 'proved
    //@note fails because not normalized
    val seq = "(1/2*x<=x & x<=7/10 & 0<=y & y<=3/10) ==> [{x'=-x+x*y, y'=-y}]!(((-4/5>=x&x>=-1)&-7/10>=y)&y>=-1)".asSequent
    proveBy(seq, odeInvariant(1)) shouldBe 'proved
  }

  it should "prove example where Darboux heuristic fails" in withMathematica { _ =>
    val seq = "2*g()*x<=2*g()*H()-v_0^2&x>=0, g()>0, 1>=c(), c()>=0, r()>=0, x=0, v=-c()*v_0\n  ==>  [{x'=v,v'=-g()-r()*v^2&x>=0&v>=0}]2*g()*x<=2*g()*H()-v^2".asSequent
    val pr = proveBy(seq, odeInvariant(1))
    pr shouldBe 'proved
  }

  "VDbx" should "prove a simple equilibirum" in withMathematica { _ =>
    val polys = List("x","y").map( s => s.asTerm)
    // Directly prove that the origin is an equilibrium point
    val system = "x'=y,y'=x".asProgram.asInstanceOf[ODESystem]
    val cofactors = List(List("0","1"),List("1","0")).map(ls => ls.map(s => s.asTerm))
    val pr = dgVdbx(system,cofactors,polys)
    println(pr)
    pr shouldBe 'proved
  }

  it should "SAS'14 Example 12" in withMathematica { _ =>
    val polys = List("x1^2+x2^2-1","x3-x1").map( s => s.asTerm)
    // Directly prove that the origin is an equilibrium point
    val system = "x1'=-x2,x2'=x3,x3'=-x2".asProgram.asInstanceOf[ODESystem]
    val cofactors = List(List("0","2*x2"),List("0","0")).map(ls => ls.map(s => s.asTerm))
    val pr = dgVdbx(system,cofactors,polys)
    println(pr)
    pr shouldBe 'proved
  }

  "Frozen time" should "freeze predicates with time (manual)" in withMathematica { _ =>
    val fml = "x+y=5 -> [{t'=1,x'=x^5+y, y'=x, c'=5 ,d'=100 & t=0 & c=1}]x+y=5".asFormula
    val pr = proveBy(fml, implyR(1) &
      //This is slightly optimized only to freeze the coordinates free in postcondition
      dC("(x-old(x))^2+(y-old(y))^2 <= (2*(x-x_0)*(x^5+y) + 2*(y-y_0)*x)*t".asFormula)(1) <(
        dW(1) & QE,
        dI('full)(1)
      ))
    println(pr)
    pr shouldBe 'proved
  }

  it should "freeze predicates with time (auto)" in withMathematica { _ =>
    val fml = "x+y=5 -> [{t'=1,x'=x^5+y, y'=x, c'=5 ,d'=100 & t=0 & c=1}]x+y=5".asFormula
    val pr = proveBy(fml, implyR(1) &
      timeBound(1))
    println(pr)
    pr shouldBe 'proved
  }

  it should "freeze predicates with stuck domains (auto)" in withMathematica { _ =>
    val seq = "x=5 & y=100 ==> x=3 , [{x'=x, y'=x+y+z & x<=5}]y=100".asSequent
    val pr = proveBy(seq,
      domainStuck(2) &
      cutR("(x-5)-stuck_^2>=0 & ((x-5)-stuck_^2=0 -> -2*stuck_+x>0)".asFormula)(2) <(
        QE,
        cohideR(2) & implyR(1) &
        lpgt(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  "local progress" should "report the full local progress formula" in withMathematica { _ =>
    val ode = "{x'=x^2+1, y'=2*x+y, z'=x+y+z}".asProgram.asInstanceOf[ODESystem]
    val fml = "x-z<=0|x+y*z>0 & x<=0".asFormula
    println(localProgressFml(ode,fml))
    //todo
  }
}
