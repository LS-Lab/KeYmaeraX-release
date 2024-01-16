/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.TacticStatistics
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.pt.ElidingProvable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.ODELiveness._
import edu.cmu.cs.ls.keymaerax.parser.Declaration
import testHelper.KeYmaeraXTestTags.SlowTest

import scala.collection.immutable.Nil

class ODELivenessTests extends TacticTestBase {

  "DGs" should "return raw DDGs" in withMathematica { _ =>
    val ax = (1 to 1).map(getDDG)
    println(ax)
    //TODO: write some additional tests when parsing for list taboos is supported
  }

  it should "unify ODEs correctly" in withQE { _ =>
      val ax = ElidingProvable(Provable.vectorialDG(2)._1, Declaration(Map.empty))
      val pr = proveBy(
        ("[{y'=z,z'=-y,x'=1 & x <= 5}](y*y+z*z) <= x^2 ->" +
          "([{x'=1 & x <= 5}]x >= 5 <- [{y'=z,z'=-y,x'=1 & x <= 5}]x>=5)").asFormula,
        byUS(ax)
      )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "correctly prove affine norm bound" in withQE { _ =>
    val affnorm = (1 to 4).map(ODEInvariance.affine_norm_bound)
    affnorm.exists(_.isProved == false) shouldBe false
  }

  it should "get instantiated vdg" in withQE { _ =>
    val vdginst = getVDGinst("v'=v^2+z,z'=v*y+z".asDifferentialProgram)
    println(vdginst)

    vdginst._1 shouldBe Symbol("proved")
    vdginst._1.conclusion shouldBe "==> [{v'=v^2+z,z'=v*y+z,c{|v,z|}&q(|v,z|)}]v*v+z*z<=f_(|v,z|)->[{v'=v^2+z,z'=v*y+z,c{|v,z|}&q(|v,z|)}]p(|v,z|)->[{c{|v,z|}&q(|v,z|)}]p(|v,z|)".asSequent

    vdginst._2 shouldBe Symbol("proved")
    vdginst._2.conclusion shouldBe "==> [{c{|v,z|}&q(|v,z|)}]p(|v,z|)->[{v'=v^2+z,z'=v*y+z,c{|v,z|}&q(|v,z|)}]p(|v,z|)".asSequent
  }

  it should "get instantiated ddg" in withQE { _ =>
    val ddginst = getDDGinst("v'=v^2+z,z'=v*y+z".asDifferentialProgram)
    println(ddginst)

    ddginst shouldBe Symbol("proved")
    ddginst.conclusion shouldBe "==> [{v'=v^2+z,z'=v*y+z,c{|y_,z_,v,z|}&q(|y_,z_,v,z|)}]2*(v*(v^2+z)+z*(v*y+z))<=a_(|y_,z_,v,z|)*(v*v+z*z)+b_(|y_,z_,v,z|)->[{v'=v^2+z,z'=v*y+z,c{|y_,z_,v,z|}&q(|y_,z_,v,z|)}]p(|y_,z_,v,z|)->[{c{|y_,z_,v,z|}&q(|y_,z_,v,z|)}]p(|y_,z_,v,z|)".asSequent
  }

  it should "vDG on left and right of sequent" in withQE { _ =>
    val seq = "[{z'=100}]z=1, <{a'=x+y+z}>a=1 ==> < {x'=1} > 1+1 = 3 , [{y'=2}] 1+1=0".asSequent

    val pr = proveBy(seq,
      // nonlinear ghosts can always be added to boxes on left and diamonds on right
      vDG("z'=z^100*y,y'=z*y^2".asDifferentialProgram)(1) &
      vDG("a'=a^2+b^3+x+y+100".asDifferentialProgram)(-1) &
      // only affine ones can be added to diamonds on left and boxes on right
      vDG("z'=y*a*z+a+b+w,w'=w+z".asDifferentialProgram)(2) &
      vDG("b'=a*b+b*a+1,c'=b+c".asDifferentialProgram)(-2)
    )

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe
    "[{a'=a^2+b^3+x+y+100,z'=100&true}]z=1, <{b'=a*b+b*a+1,c'=b+c,a'=x+y+z&true}>a=1 ==> <{z'=z^100*y,y'=z*y^2,x'=1&true}>1+1=3, [{z'=y*a*z+a+b+w,w'=w+z,y'=2&true}]1+1=0".asSequent
  }

  it should "dDG and bDG nonlinear ghosts on right of sequent" in withQE { _ =>

    val seq = " ==> < {x'=1} > 1+1 = 3 , [{y'=2}] 1+1=0".asSequent
    val pr = proveBy(seq,
      dDG("z'=z^2,w'=w*z".asDifferentialProgram,"x^2".asTerm,"y^2".asTerm)(2) <(
        skip,
        bDG("u'=u^3".asDifferentialProgram,"x".asTerm)(2)
      )
    )

    pr.subgoals.length shouldBe 3
    pr.subgoals(0) shouldBe
    " ==>  <{x'=1}>1+1=3, [{z'=z^2,w'=w*z,y'=2}]2*(z*z^2+w*(w*z))<=x^2*(z*z+w*w)+y^2".asSequent
    pr.subgoals(1) shouldBe
    " ==>  <{x'=1}>1+1=3, [{u'=u^3,z'=z^2,w'=w*z,y'=2}]u*u<=x".asSequent
    pr.subgoals(2) shouldBe
    " ==>  <{x'=1}>1+1=3, [{u'=u^3,z'=z^2,w'=w*z,y'=2}]1+1=0".asSequent
  }

  "GEx" should "identity affine form for an ODE" in withQE { _ =>
    val ode = "z'=v^2+g()*y+z,y'=f()*x*x+z".asDifferentialProgram

    val res = affine_form(ode)

    res._1 shouldBe List(List("1", "g()").map(_.asTerm), List("1", "0").map(_.asTerm))
    res._2.head shouldBe "v^2".asTerm
    //Mathematica: res._2.tail.head shouldBe "f()*x^2".asTerm
    //Z3: res._2.tail.head shouldBe "f()*x*x".asTerm
    res._3 shouldBe List("z".asVariable,"y".asVariable)
  }

  it should "derive global existence axiom for nested linear system" in withQE { _ =>
    val ode = "y'= f()*x*x + z, z'= v^2+g() * y + z,x'=v,v'=a".asDifferentialProgram

    val res = deriveGlobalExistence(ode)

    res.isDefined shouldBe true
    res.get.isProved shouldBe true
    res.get.conclusion.succ(0) shouldBe "<{gextimevar_'=1,y'=f()*x*x+z,z'=v^2+g()*y+z,x'=v,v'=a&true}>gextimevar_>p()".asFormula
  }

  it should "fail to derive global existence axiom for nonlinear system" in withQE { _ =>
    val ode = "y'= f()*x*x + z, z'= v^2+g() * y + z^2,x'=v,v'=a".asDifferentialProgram

    val res = deriveGlobalExistence(ode)

    res shouldBe None
  }

  it should "derive global existence for large and badly structured system" in withQE { _ =>
    val ode = "ee'=ff, g'=aa^2*g+gg,gg'=g+b^2*g,f'=a,dd'=ee,a'=b,aa'=bb,cc'=dd,e_'=f,bb'=cc,d'=e_,c'=d,b'=c,ff'=aa".asDifferentialProgram
    //When sorted correctly, this is just two cyclic ODEs with an extra dependency:
    //f'=a,e_'=f,d'=e_,c'=d,b'=c,a'=b, ff'=aa,ee'=ff,dd'=ee,cc'=dd,bb'=cc,aa'=bb, g'=aa^2*g

    val res = deriveGlobalExistence(ode)

    res.isDefined shouldBe true
    res.get.isProved shouldBe true
    res.get.conclusion.succ(0) shouldBe "<{gextimevar_'=1,ee'=ff,g'=aa^2*g+gg,gg'=g+b^2*g,f'=a,dd'=ee,a'=b,aa'=bb,cc'=dd,e_'=f,bb'=cc,d'=e_,c'=d,b'=c,ff'=aa&true}>gextimevar_>p()".asFormula
  }

  "compatibility" should "automatically match by compatibility" in withQE { _ =>
    //The first and last assumptions are compatible and can be automatically added
    val seq = "[{x'=1 & x < 6}]x>1,[{x'=1 & x < 4}]x>4, [{v'=2,x'=1,a'=b}]v<=5, [{v'=2,x'=1}]x+z<=5 ==> a > 0, [{x'=1,v'=2,a'=a^2+x+v^2 & x < 5}]1+1=2".asSequent

    val pr = proveBy(seq, odeUnify(2))

    println(pr)

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "[{x'=1&x < 6}]x>1, [{x'=1&x < 4}]x>4, [{v'=2,x'=1,a'=b&true}]v<=5, [{v'=2,x'=1&true}]x+z<=5  ==>  a > 0, [{x'=1,v'=2,a'=a^2+x+v^2&(x < 5&x>1)&x+z<=5}]1+1=2".asSequent
  }

  it should "introduce compatible cuts" in withQE { _ =>
    //Adds compatible cut in any position left/right, box or diamond
    val seq = "<{x'=1}>x=1, [{x'=1}]x=1 ==> <{x'=1}>x=1,[{x'=1}]x=1 ".asSequent
    val pr = proveBy(seq, compatCut("1=1".asFormula)(1) <(
      compatCut("1=1".asFormula)(-2),
      compatCut("1=1".asFormula)(2)
    ))

    pr.subgoals.length shouldBe 4
    proveBy(pr, prop) shouldBe Symbol("proved")
  }

  "odeReduce" should "detect nonlinear ode" in withQE { _ =>
    val seq = "[{x'=y^2,y'=-x^2}] y^2+x^2 <= k^2 ==> <{x' = y^2, y' = -x^2, t'=1}> t > 100".asSequent

    val pr = proveBy(seq, odeReduce(true,"y*y+x*x<=k^2+c()^2".asFormula::Nil)(1))

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "[{x'=y^2,y'=-x^2}] y^2+x^2 <= k^2 ==> <{t'=1&true}>t>100".asSequent
  }

  it should "use hints in sequence" in withQE { _ =>
    val seq = "[{a'=b^2,b'=a^2}]a^2+b^2 <= 5, [{x'=y^2,y'=-x^2}] 2*(y*(-x^2)+x*y^2) <= c() ==> <{x' = y^2, y' = -x^2, a'=b^2, b'=a^2, t'=1}> t > 100".asSequent

    val pr = proveBy(seq, odeReduce(true,"a*a+b*b<=10".asFormula::"2*(y*(-x^2)+x*y^2) <= 0*(y*y+x*x) + c() ".asFormula::Nil)(1))

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "[{a'=b^2,b'=a^2}]a^2+b^2 <= 5, [{x'=y^2,y'=-x^2}] 2*(y*(-x^2)+x*y^2) <= c() ==> <{t'=1&true}>t>100".asSequent
  }

  it should "automatically delete irrelevant ODEs and stabilize" in withQE { _ =>
    val seq = "d >0 , 1+1=2 ==> 1+1=3, <{a'=b+c+e_*5, x'=x+1, v'=2, e_' = a+e_, b'=c+f(),c'=d+e_() & c <= 5}> x+v<= 5, 2+2=1".asSequent

    val pr = proveBy(seq, odeReduce(strict = true, Nil)(2))

    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "d>0, 1+1=2  ==> 1+1=3, <{x'=x+1,c'=d+e_(),v'=2&c<=5}>x+v<=5, 2+2=1".asSequent
  }

  it should "throw a helpful error when it gets stuck" in withQE { _ =>
    val seq = "==> <{a'=b,b'=c,c'=d,d'=d^2+f,f'=f,e_'=5 & e_ <= 5}> e_<= 5".asSequent

    the [Exception] thrownBy proveBy(seq, odeReduce(strict = true, Nil)(1)) should have message
      "odeReduce failed to autoremove: {d'=d^2+f}. Try to add a hint of either this form: d*d<=f_(|d|) or this form: 2*(d*(d^2+f))<=a_(|y_,z_,d|)*(d*d)+b_(|y_,z_,d|)"
  }

  it should "continue using assms (format 1)" in withQE { _ =>
    val seq = "[{d'=d^2+f,f'=f,e_'=5&e_<=5}] d^2 <= e_*f ==> <{a'=b,b'=c,c'=d,d'=d^2+f,f'=f,e_'=5 & e_ <= 5}> e_<= 5".asSequent

    val pr = proveBy(seq, odeReduce(strict = true, "d*d <= f*e_".asFormula::Nil)(1))
    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "[{d'=d^2+f,f'=f,e_'=5&e_<=5}]d^2<= e_*f ==>  <{e_'=5&e_<=5}>e_<=5".asSequent
  }

  it should "continue using assms (format 2)" in withQE { _ =>
    val seq = "[{d'=d^2+f,f'=f,e_'=5&e_<=5}] 2*(d*(d^2+f)) <= 1*(d^2) ==> <{a'=b,b'=c,c'=d,d'=d^2+f,f'=f,e_'=5 & e_ <= 5}> e_<= 5".asSequent

    val pr = proveBy(seq, odeReduce(strict = true, "2*(d*(d^2+f)) <= 1*(d*d)+5".asFormula :: Nil)(1))
    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "[{d'=d^2+f,f'=f,e_'=5&e_<=5}]2*(d*(d^2+f))<=1*(d^2)  ==>  <{e_'=5&e_<=5}>e_<=5".asSequent
  }

  "kdomd" should "refine ODE postcondition (with auto DC of assumptions)" in withQE { _ =>
    val seq = "[{x'=x,v'=v}] v <= 100 , a > 0, [{x'=x,v'=v&x+v^2<=6}] x <= 1 , b < 0, [{x'=x,v'=v&x=1}] 1+1=2 ==> <{x'=x, v'=v}> x+v^2 > 5".asSequent

    val pr = proveBy(seq, kDomainDiamond("x > 5".asFormula)(1))

    println(pr)

    pr.subgoals.length shouldBe 2
    pr.subgoals(0) shouldBe "[{x'=x,v'=v&true}]v<=100, a>0, [{x'=x,v'=v&x+v^2<=6}]x<=1, b < 0, [{x'=x,v'=v&x=1}]1+1=2 ==> <{x'=x,v'=v&true}>x>5".asSequent
    pr.subgoals(1) shouldBe "[{x'=x,v'=v&true}]v<=100, a>0, [{x'=x,v'=v&x+v^2<=6}]x<=1, b < 0, [{x'=x,v'=v&x=1}]1+1=2 ==> [{x'=x,v'=v&((true&!x+v^2>5)&v<=100)&x<=1}](!x>5)".asSequent
  }

  "ddr" should "refine ODE domains (with auto DC of assumptions)" in withQE { _ =>
    val seq = "a() > 0, [{x'=x,v'=v}]v>=0 , v = 1 ==> <{x'=x, v'=v & v >= 0}> x+v^2 > 5".asSequent

    val pr = proveBy(seq, dDR("x > 100 & v <= 5".asFormula)(1))

    println(pr)

    pr.subgoals.length shouldBe 2
    pr.subgoals(0) shouldBe "a()>0, [{x'=x,v'=v&true}]v>=0, v=1  ==>  <{x'=x,v'=v&x>100&v<=5}>x+v^2>5".asSequent
    pr.subgoals(1) shouldBe "a()>0, [{x'=x,v'=v&true}]v>=0, v=1  ==>  [{x'=x,v'=v&(x>100&v<=5)&v>=0}]v>=0".asSequent
  }

  "ddx" should "prove diamonds that are true in the beginning" in withQE { _ =>
    val fml = "<{x'=x^2,v'=v^3+x+v+v+a()+b+c & b*x^2<= v+c+a()}>x+v<=a()".asFormula

    val pr = proveBy(fml,
      dDX(1)
    )

    println(pr)
    pr.subgoals.length shouldBe 1
    pr.subgoals(0) shouldBe "==> b*x^2<=v+c+a()&x+v<=a()".asSequent
  }

  "dV" should "work on simple examples (1)" in withQE { _ =>
    val pr = proveBy("a>0 ==> <{x'=a,y'=z}>x>=b()".asSequent,
      dV("a".asTerm)(1))

    val pr2 = proveBy("c=1 ==> a<=0 , <{y'=z,x'=a+c}>x>=b()".asSequent,
      dV("a".asTerm)(2))

    println(pr)
    println(pr2)
    pr shouldBe Symbol("proved")
    pr2 shouldBe Symbol("proved")
  }

  it should "work on simple examples (1) symbolically" in withQE { _ =>
    val pr = proveBy("a>0 ==> <{x'=a,y'=z}>x>=b()".asSequent,
      cutR("\\exists e_ (e_ > 0 & \\forall x \\forall y (a >= e_))".asFormula)(1) <(
        QE,
        implyR(1) & existsL(Symbol("Llast")) & dV("e_".asTerm)(1)
      )
    )

    val pr2 = proveBy("c=1 ==> a<=0 , <{y'=z,x'=a+c}>x>=b()".asSequent,
      cutR("\\exists e_ (e_ > 0 & \\forall y \\forall x (a+c >= e_))".asFormula)(2) <(
        QE,
        implyR(2) & existsL(Symbol("Llast")) & dV("e_".asTerm)(2)
      )
    )

    println(pr)
    println(pr2)
    pr shouldBe Symbol("proved")
    pr2 shouldBe Symbol("proved")
  }

  it should "work on simple examples (1) automatically" in withQE { _ =>

    val pr = proveBy("a>0 ==> <{x'=a,y'=z}>x>=b()".asSequent,
      dVAuto()(1)
    )

    val pr2 = proveBy("c=1 ==> a<=0 , <{y'=z,x'=a+c}>x>=b()".asSequent,
      dVAuto()(2)
    )

    println(pr)
    println(pr2)
    pr shouldBe Symbol("proved")
    pr2 shouldBe Symbol("proved")
  }

  it should "diff var a()>0 |- <{x'=a()}>x>=b()" in withQE { _ =>
    val pr = proveBy("a()>0 ==> <{x'=a()}>x>=b()".asSequent, dVAuto()(1))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "diff var flat flight progress [function]" in withQE { _ =>
    val pr = proveBy("b>0 -> \\exists d (d^2<=b^2 & <{x'=d}>x>=p())".asFormula,
      implyR(1) &
        existsR("b".asTerm)(1) &
        andR(1) <( QE , dVAuto()(1))
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "diff var flat flight progress [variable]" in withQE { _ =>
    val pr = proveBy("b>0 -> \\forall p \\exists d (d^2<=b^2 & <{x'=d}>x>=p)".asFormula,
      implyR(1) &
        allR(1) &
        existsR("b".asTerm)(1) &
        andR(1) <( QE , dVAuto()(1)))
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "support higher derivatives" in withMathematica { _ =>
    // note: postcondition x > j fails because of a renaming bug
    val pr = proveBy("j > 0 ==> <{d'=c, x'=v, v'=a, a'=j, c'=-d}> x > 100".asSequent,
      // Should be old(x), etc.
      higherdV(List("x-100","v","a/2","j/6").map(_.asTerm))(1) &
      // This is manual by design, although this is probably the main way to do it
      dC("a>=2*coeff2+6*coeff3*t".asFormula)(1) <( skip, dI(Symbol("full"))(1) ) &
      dC("v>=coeff1+2*coeff2*t+3*coeff3*t^2".asFormula)(1) <( dI(Symbol("full"))(1), dI(Symbol("full"))(1) )
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "support semialgebraic dV (disjunctive)" in withMathematica { _ =>
    val pr = proveBy("v!=0 -> <{x'=v}> (x>100 | x < 100)".asFormula,
      implyR(1) &
        //encode abs(v)
        cut("\\exists absv (absv = abs(v))".asFormula) < (
          existsL(-2),
          hideR(1) & QE
        ) &
        semialgdV("absv".asTerm)(1)
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "support semialgebraic dV auto (disjunctive)" in withMathematica { _ =>
    val pr = proveBy("v!=0 -> v=0 | <{x'=v}> (x>100 | x < 100)".asFormula,
      implyR(1) & orR(1) & semialgdVAuto()(2)
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "support semialgebraic dV auto 2" taggedAs SlowTest in withMathematica { _ =>
    val pr = proveBy("<{u'=-u^3}>(-1<=u & u <=1 )".asFormula,
      semialgdVAuto()(1)
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

  "cor" should "refine a closed domain" in withQE { _ =>
    val seq = "x^2+y^2=1/2 ==> <{x'=x, y'=y & -1 <= x & x <= 1 & -1 <=y & y<=1}> (x=1|y=1|x=-1|y=-1)".asSequent

    val pr = proveBy(seq,
      // Helpful cut that is used twice
      cut("[{x'=x,y'=y&true&!(x=1|y=1|x=-1|y=-1)}](x<1&y<1&x>-1&y>-1)".asFormula) <(
        skip,
        hideR(1) & ODE(1)
      ) &
        closedRef("true".asFormula)(1) <(
          skip,
          hideL(-2) & QE, // initial circle is in the interior
          dW(1) & QE //using compatible cut
        ) &
        kDomainDiamond("x^2+y^2 > 2".asFormula)(1) <(
          skip,
          dW(1) & QE //using compatible cut
        ) &
        compatCut("x^2+y^2 >= 1/2".asFormula)(1) <(
          // dV("1".asTerm)(1),
          dVAuto()(1),
          hideL(-2) & hideR(1) & ODE(1)
        )
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

  "univariate" should "automatically odeReduce univariate" in withMathematica { _ =>
    val fml = "b() > 0 & k > 0 & v > 0 -> <{x'=v, v' = -k* v^3 -v^2 - b() * v + 1, y'=y, t'=1}> t > 1000".asFormula

    val pr = proveBy(fml, implyR(1) & odeReduce(true,Nil)(1) &
      cohideR(1) & byUS(Ax.TExgt)
    )

    //@todo: works with Mathematica but something is wrong with ODE and z3??
    val fail = "b()>0&k>0&initx_>0  ==>  [{v'=-k*v^3-v^2-b()*v+1,y'=y,t'=1&true&v*v<=initx_*initx_+root_*root_}]v*v<=initx_*initx_+root_*root_".asSequent
    println("fails on Z3: ",proveBy(fail, ODE(1)))

//    println(pr)
//    pr shouldBe 'proved
  }

  it should "not try univariate removal when inapplicable (1)" in withQE { _ =>
    val fml = "a > 0 & v > 0 -> <{v'=-v^2 * a,a'=a^2*v, t'=1}> t > 1000".asFormula

    // In this case, the univariate reduction should never fire
    // and things should fallback to the nonlinear case
    the [Exception] thrownBy proveBy(fml, prop & odeReduce(true,Nil)(1)) should have message
      "odeReduce failed to autoremove: {a'=a^2*v,v'=-v^2*a}. Try to add a hint of either this form: a*a+v*v<=f_(|a,v|) or this form: 2*(a*(a^2*v)+v*(-v^2*a))<=a_(|y_,z_,a,v|)*(a*a+v*v)+b_(|y_,z_,a,v|)"
  }

  it should "not try univariate removal when inapplicable (2)" in withQE { _ =>
    val fml = "a > 0 & v > 0 -> <{v'=-v^2 * a,a'=1, t'=1}> t > 1000".asFormula

    // In this case, the univariate reduction should never fire
    the [Exception] thrownBy proveBy(fml, implyR(1) & odeReduce(true,Nil)(1)) should have message
      "odeReduce failed to autoremove: {v'=-v^2*a}. Try to add a hint of either this form: v*v<=f_(|v|) or this form: 2*(v*(-v^2*a))<=a_(|y_,z_,v|)*(v*v)+b_(|y_,z_,v|)"
  }

  it should "work on a hard symbolic case" in withMathematica { _ =>
    val fml = "a > 0 & b() < 0 & x<= a& x>= b()-> <{x'=x*(x-a)*(x-b()), t'=1}> t > 1000".asFormula

    val pr = proveBy(fml, implyR(1) & odeReduce(true,Nil)(1) & solve(1) & QE)
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "work with interleaved cases" in withQE { _ =>
    val fml = "a > 0 & b() < 0 & x<= a& x>= b()& y^2 = 0 -> <{k'=z+x+k,  y'=y*(y-a)*(y-b()),z'=x+z, x'=x*(x-a)*(x-b()), t'=1}> t > 1000".asFormula

    val pr = proveBy(fml, implyR(1) & odeReduce(true,Nil)(1) & solve(1) & QE)
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "try manual univariate boundedness proof" in withQE { _ =>
    val fml = "a*r^2+b*r+c = 0 & (v-r=0 | v-r < 0 & a*v0^2+b*v0+c > 0 | a*v0^2+b*v0+c < 0 & v-r > 0 ) & v=v0 -> [{v' = a*v^2+b*v+c}] v^2 <= v0^2+r^2".asFormula
    val pr = proveBy(fml,
      implyR(1) & cut("\\exists d \\exists e_ \\forall v a*v^2+b*v+c=(v-r)*(d*v+e_)".asFormula) <(
        existsL(Symbol("Llast")) & existsL(Symbol("Llast")) &
          dC("a*v^2+b*v+c=(v-r)*(d*v+e_)".asFormula)(1) <(
            ODEInvariance.diffDivConquer("v-r".asTerm, Some("d*v+e_".asTerm))(1)
              <(
              dW(1) & QE,
              // Should just do DDC manually to avoid this cut
              cut("a*v0^2+b*v0+c < 0".asFormula) <( dC("v<=v0".asFormula)(1) <(dW(1) & QE, ODE(1)), cohideOnlyR(2) & QE),
              cut("a*v0^2+b*v0+c > 0".asFormula) <( dC("v>=v0".asFormula)(1) <(dW(1) & QE, ODE(1)), cohideOnlyR(2) & QE),
            )
            , ODE(1)
          ),
        cohideOnlyR(2) & QE
      )
    )

    println(pr)
    pr shouldBe Symbol("proved")
  }

  "FAOC" should "initialize" in withMathematica { _ =>
  }

  it should "prove Example 1 (manual)" in withMathematica { _ =>

    val tac =  implyR(1) & allR(1) &
      dDDG("0".asTerm,"0".asTerm)(1) <(
        ODE(1),
        cohideR(1) & byUS(Ax.TExgt)
      )

    val pr = proveBy("v > 0 & k > 0 -> \\forall tau <{v'=-k * v^2, t'=1}> t > tau".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Example 1 (automatic)" in withMathematica { _ =>

    val tac = implyR(1) & allR(1) & gEx(Nil)(1)

    val pr = proveBy("v > 0 & k > 0 -> \\forall tau <{v'=-k * v^2, t'=1}> t > tau".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Example 2 (manual)" in withMathematica { _ =>
    // Note: the u,v ODEs are swapped here for a simpler manual proof
    // The automatic proof below does this swapping automatically
    val tac = allR(1) &
      dDDG("2*u".asTerm,"0".asTerm)(1) <(
        ODE(1),
        dDDG("2".asTerm,"0".asTerm)(1) <(
          ODE(1),
          byUS(Ax.TExgt)
        )
      )

    val pr = proveBy("\\forall tau <{v'=u*v, u'=u, t'=1}> t > tau".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Example 2 (automatic)" in withMathematica { _ =>

    val tac = allR(1) & gEx(Nil)(1)

    val pr = proveBy("\\forall tau <{u'=u, v'=u*v, t'=1}> t > tau".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Example 3 (manual)" in withMathematica { _ =>

    val tac = implyR(1) & allR(1) &
      dBDG("1/4".asTerm,2)(1) <(
        ODE(1),
        cohideR(1) & byUS(Ax.TExgt)
      )

    val pr = proveBy("u^2 + v^2 <= 1/4 -> \\forall tau <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2), t'=1}> t > tau".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Example 3 (automatic)" in withMathematica { _ =>

    val tac = implyR(1) & allR(1) &
      gEx("u*u+v*v<=1/4".asFormula :: Nil)(1)
      // If gEx is called without hints here, it should fail with a helpful error:
      // odeReduce failed to autoremove: {u'=-v-u*(1/4-u^2-v^2),v'=u-v*(1/4-u^2-v^2)}.
      // Try to add an assumption to the antecedents of either this form:
      // [{u'=-v-u*(1/4-u^2-v^2),v'=u-v*(1/4-u^2-v^2),t'=1&true}]u*u+v*v<=f_(|u,v|) or this form:
      // [{u'=-v-u*(1/4-u^2-v^2),v'=u-v*(1/4-u^2-v^2),t'=1&true}]2*(u*(-v-u*(1/4-u^2-v^2))+v*(u-v*(1/4-u^2-v^2)))<=a_(|y_,z_,u,v|)*(u*u+v*v)+b_(|y_,z_,u,v|)

    val pr = proveBy("u^2 + v^2 <= 1/4 -> \\forall tau <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2), t'=1}> t > tau".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Example 4 (manual)" in withMathematica { _ =>

    val fml = "u^2+v^2 = 1 -> <{u'=-v-u, v'=u-v}> (1/4 <= max(abs(u),abs(v)) & max(abs(u),abs(v)) <= 1/2)".asFormula

    val tac = implyR(1) &
      // Replace the postcondition
      kDomainDiamond("u^2+v^2<=1/4".asFormula)(1) <(
        skip,
        ODE(1) // ODE is smart enough to do two steps at once here
      ) &
      // This is a manual implementation of dV
      cut("\\exists t t=0".asFormula) <( existsL(-2) , cohideR(2) & QE) &
      vDG("t'=1".asDifferentialProgram)(1) &
      cut("\\exists p u^2+v^2=p".asFormula) <( existsL(-3) , cohideR(2) & QE) &
      kDomainDiamond("t > 2*p".asFormula)(1) <(
        skip,
        dC("p-1/2*t >= u^2+v^2-1/4".asFormula)(1) <( ODE(1), ODE(1) )
      ) &
      // Global existence:
      useAt(Ax.commaCommuteD)(1) &
      dDDG("0".asTerm,"0".asTerm,2)(1) <(
        ODE(1),
        cohideR(1) & byUS(Ax.TExgt)
      )

    val pr = proveBy(fml, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Example 4 (automatic) " in withMathematica { _ =>

    val fml = "u^2+v^2 = 1 -> <{u'=-v-u, v'=u-v}> (1/4 <= max(abs(u),abs(v)) & max(abs(u),abs(v)) <= 1/2)".asFormula

    val tac = implyR(1) &
      // Replace the postcondition
      kDomainDiamond("u^2+v^2<=1/4".asFormula)(1) <(
        dVAuto()(1), //dV("1/2".asTerm)(1)
        ODE(1)
      )

    val pr = proveBy(fml, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Examples 5,6,7 (manual) " in withMathematica { _ =>

    //First, prove the liveness property without domain constraints
    val fml = "u^2+v^2 = 1 -> <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}> (u^2+v^2 >= 2)".asFormula

    val tac = implyR(1) &
      // "Assume" for contradiction that goal is not reached, then solution is trapped in compact set
      cut("[{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}] !(u^2+v^2 >= 2)".asFormula) <(
        skip,
        useAt(Ax.diamond,PosInExpr(1::Nil))(1) & propClose
      ) &
      // Manual dV
      cut("\\exists t t=0".asFormula) <( existsL(-3) , cohideR(2) & QE) &
      vDG("t'=1".asDifferentialProgram)(1) &
      cut("\\exists p u^2+v^2=p".asFormula) <( existsL(-4) , cohideR(2) & QE) &
      kDomainDiamond("t > 2/3*p".asFormula)(1) <(
        skip,
        dC("p-3/2*t >= 2- (u^2+v^2)".asFormula)(1) <(
          hideL(-2) & ODE(1),
          hideL(-2) &
            dC("u^2+v^2>=1".asFormula)(1) <(
              ODE(1),
              ODE(1)
            )
        )) &
      useAt(Ax.commaCommuteD)(1) &
      dBDG("2".asTerm,2)(1) <(
        cohideOnlyL(-2) & vDG("t'=1".asDifferentialProgram)(-1) &
          useAt(Ax.commaCommute)(-1) &
          monb & QE
        ,
        cohideR(1) & byUS(Ax.TExgt)
      )

    val pr = proveBy(fml, tac)

    //Then, prove the liveness property with domain constraints
    val fml2 = "u^2+v^2 = 1 -> <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2) & 1 <= u^2+v^2 & u^2+v^2 <= 2}> (u^2+v^2 >= 2)".asFormula

    val tac2 = implyR(1) &
      dDR("u^2+v^2 <= 2".asFormula)(1) <(
        skip,
        ODE(1)
      ) &
      closedRef("true".asFormula)(1) <(
        implyRi & byUS(pr), //The (proved) liveness property without constraints is used here via substitution
        QE,
        ODE(1)
      )

    val pr2 = proveBy(fml2, tac2)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")

    // Note: proof steps for pr2 already includes those from pr
    // Total tactic size is counted as size for tac1 + tac2
    println(pr2)
    println("Proof steps:",pr2.steps)
    println("Tactic size:",TacticStatistics.size(tac2))
    pr2 shouldBe Symbol("proved")
  }

  it should "prove Examples 5,6,7 (automatic) " in withMathematica { _ =>

    val fml = "u^2+v^2 = 1 -> <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}> (u^2+v^2 >= 2)".asFormula

    val tac = implyR(1) &
      // "Assume" for contradiction that goal is not reached
      saveBox(1) &
      cut("[{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2)}] u^2+v^2>=1".asFormula) < (
        dVAuto()(1), //dV("3/2".asTerm)(1)
        hideL(-2) & cohideOnlyR(2) & ODE(1)
      ) &
      gEx("2*(u*(-v-u*(1/4-u^2-v^2))+v*(u-v*(1/4-u^2-v^2)))<=0*(u*u+v*v)+8".asFormula::Nil)(1)

    val pr = proveBy(fml, tac)

    val fml2 = "u^2+v^2 = 1 -> <{u'=-v-u*(1/4-u^2-v^2), v'=u-v*(1/4-u^2-v^2) & 1 <= u^2+v^2 & u^2+v^2 <= 2}> (u^2+v^2 >= 2)".asFormula

    val tac2 = implyR(1) &
      dDR("u^2+v^2 <= 2".asFormula)(1) <(
        skip,
        ODE(1)
      ) &
      closedRef("true".asFormula)(1) <(
        implyRi & byUS(pr),
        QE,
        ODE(1)
      )

    val pr2 = proveBy(fml2, tac2)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")

    // Note: proof steps for pr2 already includes those from pr
    // Total tactic size is counted as size for tac1 + tac2
    println(pr2)
    println("Proof steps:",pr2.steps)
    println("Tactic size:",TacticStatistics.size(tac2))
    pr2 shouldBe Symbol("proved")
  }

  it should "prove Example 8 (manual)" in withMathematica { _ =>

    val tac = kDomainDiamond("u^2 <= 1".asFormula)(1) <(
      skip,
      ODE(1)
    ) &
    // This is a manual implementation of dV
    cut("\\exists t t=0".asFormula) <( existsL(-1) , cohideR(2) & QE) &
    vDG("t'=1".asDifferentialProgram)(1) &
    cut("\\exists p u^2=p".asFormula) <( existsL(-2) , cohideR(2) & QE) &
    kDomainDiamond("t > p".asFormula)(1) <(
      skip,
      dC("p-t >= u^2-1".asFormula)(1) <( ODE(1), ODE(1) )
    ) &
    // Global existence:
    useAt(Ax.commaCommuteD)(1) &
    dDDG("0".asTerm,"0".asTerm)(1) <(
      ODE(1),
      cohideR(1) & byUS(Ax.TExgt)
    )

    val pr = proveBy("<{u'=-u}> (-1 <= u & u <= 1)".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Example 8 (automatic)" in withMathematica { _ =>

    val tac = semialgdV("1".asTerm)(1)

    val pr = proveBy("<{u'=-u}> (-1 <= u & u <= 1)".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Sogokon & Jackson FM'15 Example 11" in withMathematica { _ =>
    val X0 = "x2 > 0 & x1 >= -1/4 & x1 <= 1/4 & (x1^2+x2^2-1)^2<=1/30".asFormula
    val XT = "x2 < 0 & x1 >= -1/4 & x1 <= 1/4 & (x1^2+x2^2-1)^2<=1/30".asFormula
    val ode = "{x1'=x2-x1*(x1^2+x2^2-1), x2'=-x1-x2*(x1^2+x2^2-1)}".asDifferentialProgram
    val dom = "x1<=2 & x1>=-2 & x2<=2 & x2>=-2".asFormula

    val S1 = And(Not(XT), "x1 >= -1/4 & (x1^2+x2^2-1)^2<=1/30".asFormula)
    val p1 = "-(x1 - 6/5)^2 + (x1 - x2 - 2)^2 +10".asTerm

    val S2 = And(Not(X0), "x1 <= 1/4 & (x1^2+x2^2-1)^2<=1/30".asFormula)
    val p2 = "-(-x1 - 6/5)^2 + (-x1 + x2 - 2)^2 +10".asTerm

    val tac1 = implyR(1) &
      // This part is an invariant, so cut it as context
      cut(Box(ODESystem(ode,True),"(x1^2+x2^2-1)^2<=1/30".asFormula)) <(
        skip,
        cohideOnlyR(2) & ODE(1)
      ) &
      // Thanks to the invariant, the avoid constraint is trivial with compatible cuts
      dDR(True)(1) <(
        skip,
        dW(1) & QE //or: ODE(1)
      ) &
      // Use a staging set that cannot be left without reaching the target
      kDomainDiamond(Not(S1))(1) <(
        skip,
        dC("x1>=-1/4".asFormula)(1) <(
          ODE(1),
          ODE(1)
        )
      ) &
      // Save the staging set as context
      saveBox(1) &
      // Use a progress function
      kDomainDiamond(Less(p1, Number(0)))(1) <(
        //dV("0.1".asTerm)(1), //0.1 arbitrarily chosen here...
        dVAuto()(1),
        dW(1) & QE
      ) &
    gEx("2*(x1*(x2-x1*(x1^2+x2^2-1))+x2*(-x1-x2*(x1^2+x2^2-1)))<=0*(x1*x1+x2*x2)+10000".asFormula :: Nil)(1)

    val pr1 = proveBy( Imply(X0, Diamond(ODESystem(ode,dom),XT)) , tac1)

    val tac2 = implyR(1) &
      // This part is an invariant, so cut it as context
      cut(Box(ODESystem(ode,True),"(x1^2+x2^2-1)^2<=1/30".asFormula)) <(
        skip,
        cohideOnlyR(2) & ODE(1)
      ) &
      // Thanks to the invariant, the avoid constraint is trivial with compatible cuts
      dDR(True)(1) <(
        skip,
        dW(1) & QE //or: ODE(1)
      ) &
      // Use a staging set that cannot be left without reaching the target
      kDomainDiamond(Not(S2))(1) <(
        skip,
        dC("x1<=1/4".asFormula)(1) <(
          ODE(1),
          ODE(1)
        )
      ) &
      // Save the staging set as context
      saveBox(1) &
      // Use a progress function
      kDomainDiamond(Less(p2, Number(0)))(1) <(
        //dV("0.1".asTerm)(1), //0.1 arbitrarily chosen here...
        dVAuto()(1),
        dW(1) & QE
      ) &
      gEx("2*(x1*(x2-x1*(x1^2+x2^2-1))+x2*(-x1-x2*(x1^2+x2^2-1)))<=0*(x1*x1+x2*x2)+10000".asFormula :: Nil)(1)

    val pr2 = proveBy( Imply(XT, Diamond(ODESystem(ode,dom),X0)) , tac2)

    println(pr1)
    println("Proof steps:",pr1.steps)
    println("Tactic size:",TacticStatistics.size(tac1))
    pr1 shouldBe Symbol("proved")

    println(pr2)
    println("Proof steps:",pr2.steps)
    println("Tactic size:",TacticStatistics.size(tac2))
    pr2 shouldBe Symbol("proved")
  }

  it should "prove Sogokon & Jackson FM'15 Example 12" in withMathematica { _ =>
    val X0 = "x2 - x1 < 0".asFormula
    val XT = "x2 - x1 = 0".asFormula
    val ode = "{x1'=-1, x2'=(x2-x1)^2}".asDifferentialProgram
    val dom = "true".asFormula

    val tac = implyR(1) &
      kDomainDiamond("x2 - x1 >=0".asFormula)(1) <(
        saveBox(1) &
          // dV("1".asTerm)(1) &
          dVAuto()(1) &
          // Proving bound on derivative
          //todo: cut needs to support old(.) directly
          cut("\\exists oldv oldv = x2-x1".asFormula) <(
            existsL(-5),
            cohideR(2) & QE
          ) &
          compatCut("x2-x1>=oldv".asFormula)(1) <(
            gEx("2*(x2*(x2-x1)^2)<= oldv^2*(x2*x2)+oldv^2".asFormula :: Nil)(1),
            cohideOnlyR(2) & hideL(-2) & ODE(1)
          )
        ,
        ODE(1)
      )

    val pr = proveBy( Imply(X0, Diamond(ODESystem(ode,dom),XT)) , tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove Sogokon & Jackson FM'15 Example 15" in withMathematica { _ =>

    val tac = semialgdV("1".asTerm)(1)

    val pr = proveBy("<{x1'=-x1,x2'=-x2}> (x1<=1 & x1>=-1 & x2<=1 &x2>=-1)".asFormula, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove RAL goal reachability" in withMathematica { _ =>
    val seq = "v>0, vl<=v, v<=vh, a=0, eps>0, k*eps^2-2*eps < k*(x^2+y^2)-2*x, k*(x^2+y^2)-2*x < k*eps^2-2*eps, y>0 ==> <{x'=-v*k*y, y'=v*(k*x-1), v'=0 & v>=0}>( x^2+y^2<=eps^2 & (vl<=v & v<=vh) )".asSequent

    val tac = cut("\\exists oldv (oldv = v)".asFormula) < (
        existsL(Symbol("Llast")),
        hideR(1) & QE
      ) &
        // known invariants: v stays constant, and robot always on annulus
        cut("[{x'=-v*k*y, y'=v*(k*x-1), v'=0}]( v=oldv & k*eps^2-2*eps < k*(x^2+y^2)-2*x & k*(x^2+y^2)-2*x < k*eps^2-2*eps) ".asFormula) <(
          skip,
          hideR(1) & ODE(1)
        ) &
        // dDR gets rid of domain constraint easily thanks to builtin compatible cuts
        dDR(True)(1) <(
          skip,
          dW(1) & QE
        ) &
        // K<&> simplifies postcondition again thanks to builtin compatible cuts
        kDomainDiamond("x^2+y^2<=eps^2".asFormula)(1) <(
          skip,
          dW(1) & QE
        ) &
        // todo: replace with old
        cut("\\exists oldhalfy (oldhalfy = y/2)".asFormula) < (
          existsL(Symbol("Llast")),
          hideL(Symbol("Llast")) & hideR(1) & QE
        ) &
        // As long as the goal is not yet reached, y will stay positive
        cut("[{x'=-v*k*y,y'=v*(k*x-1),v'=0&!x^2+y^2<=eps^2}] y > oldhalfy".asFormula)<(
          skip,
          hideR(1) & odeUnify(1) & hideL(-10) & ODE(1) //todo: Z3 gets stuck here for whatever reason
        ) &
        // dV("2*oldv*oldhalfy".asTerm)(1)
        dVAuto()(1)

    val pr = proveBy(seq, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

  it should "prove RAL velocity bounds" in withMathematica { _ =>
    // abridged proof
    val seq = "v>=0, 0<vl, vl<vh, A>0, B>0 ==> \\exists a ( (a <= A & -B <= a) & <{x'=-v*k*y, y'=v*(k*x-1), v'=a & v>=0}>( vl<=v & v<=vh ))".asSequent

    val tac = // Trichotomy
      cut("v < vl|vl<=v&v<=vh|vh < v".asFormula) <(
        skip,
        hideR(1) & QE
      ) &
        orL(Symbol("Llast")) <(
          // v < vl, pick a = A
          existsR("A".asTerm)(1) & andR(1) <( QE,
            kDomainDiamond("v >= vl".asFormula)(1) <(
              skip,
              ODE(1) //note the slightly tricky refinement here (using IVT)
            ) &
              dDR(True)(1) <(
                skip,
                ODE(1)
              ) &
              // dV("A".asTerm)(1)
              dVAuto()(1)
          ),
          orL(Symbol("Llast")) <(
            //a=0
            dDX(1, 0::1::Nil) & QE,
            // In this easy case, solve would do it after removing extra ODEs
            //existsR("0".asTerm)(1) & andR(1) <( QE,
            // odeReduce()(1) & solve(1) & QE
            //a=-B
            existsR("-B".asTerm)(1) & andR(1) <( QE,
              kDomainDiamond("v <= vh".asFormula)(1) <(
                skip,
                ODE(1) //note the slightly tricky refinement here (using IVT)
              ) &
                closedRef("true".asFormula)(1) <(
                  //dV("B".asTerm)(1),
                  dVAuto()(1),
                  QE,
                  //todo: fix ODE so that DconstV correctly calculates const assms to keep
                  dWPlus(1) & QE
                )
            )
          )
        )

    val pr = proveBy(seq, tac)

    println(pr)
    println("Proof steps:",pr.steps)
    println("Tactic size:",TacticStatistics.size(tac))
    pr shouldBe Symbol("proved")
  }

}
