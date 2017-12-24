package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import edu.cmu.cs.ls.keymaerax.tools.Tool
import testHelper.KeYmaeraXTestTags.{SummaryTest, TodoTest}

import scala.collection.immutable._
import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps
import org.scalatest.LoneElement._
import org.scalatest.prop.TableDrivenPropertyChecks._

/**
 * Tests automatic
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.ODE]] differential equations proving.
 */
@UsualTest
class ODETests extends TacticTestBase {

  /**
    * Temporary test cases for Darboux
    */

  "ODE Darboux" should "prove equational darboux" in withQE { _ =>
    //(x+z)' = (x*A+B)(x+z)
    val fml = "x+z=0 -> [{x'=(A*y+B()*x), z' = A*z*x+B()*z & y = x^2}] x+z=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbx("x*A+B()".asTerm)(1))
    pr shouldBe 'proved
  }

  it should "prove fractional darboux" in withQE { _ =>
    //(x+z)' = ((x*A+B)/z^2)(x+z), where z^2 > 0
    //assumes z^2 already in evol domain, or the ghost will report a singularity
    val fml = "x+z=0 -> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbx("(x*A+B())/z^2".asTerm)(1))
    pr shouldBe 'proved
  }

  it should "prove >= darboux" in withQE { _ =>
    //(x+z)' =  x^2 + z*x + x^2 >= x*(x+z)
    //Maybe this should leave open that the remainder is >= 0?
    val fml = "x+z>=0 -> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbx("x".asTerm)(1))
    pr shouldBe 'proved
  }

  it should "prove >= fractional darboux" in withQE { _ =>
    //(x+z)' =  (1/z^2)(x+z) + x^2 >= (1/z^2)(x+z)
    //Maybe this should leave open that the remainder is >= 0?
    val fml = "x+z>=0 -> [{x'=1/z, z' = x/z^2 + y & z^2 > 0 & y = x^2}] x+z>=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbx("1/z^2".asTerm)(1))
    pr shouldBe 'proved
  }

  it should "prove < darboux" in withQE { _ =>
    //(x+z)' =  x^2 + z*x - x^2 <= x*(x+z)
    val fml = "x+z<0 -> [{x'=x^2, z' = z*x+y & y = -x^2}] x+z<0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbx("x".asTerm)(1))
    pr shouldBe 'proved
  }

  it should "prove < fractional darboux" in withQE { _ =>
    //(x+z)' =  (1/z^2)(x+z) - x^2 <= (1/z^2)(x+z)
    //Maybe this should leave open that the remainder is >= 0?
    val fml = "x+z<0 -> [{x'=1/z, z' = x/z^2 + y & z^2 > 0 & y = -x^2}] x+z<0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbx("1/z^2".asTerm)(1))
    pr shouldBe 'proved
  }

  it should "automatically find equational darboux" in withMathematica { _ =>
    //(x+z)' = (x*A+B)(x+z)
    val fml = "x+z=0 -> [{x'=(A*x^2+B()*x), z' = A*z*x+B()*z}] 0=-x-z".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbxAuto(1))
    pr shouldBe 'proved
  }

  it should "automatically find fractional darboux" in withMathematica { _ =>
    //(x+z)' = ((x*A+B)/z^2)(x+z), where z^2 > 0
    val fml = "x+z=0 -> [{x'=(A*x^2+B()*x)/z^2, z' = (A*x+B())/z & z^2 > 0}] x+z=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbxAuto(1))
    pr shouldBe 'proved
  }

  it should "fail with evolution domain constraints" in withMathematica { _ =>
    //(x+z)' = (x*A+B)(x+z)
    val fml = "x+z=0 -> [{x'=(A*y+B()*x), z' = A*z*x+B()*z & y = x^2}] x+z=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) & DifferentialTactics.dgDbxAuto(1))
    pr should not be 'proved
    pr.subgoals.loneElement shouldBe "x+z=0 ==> [{x'=(A*y+B()*x), z' = A*z*x+B()*z & y = x^2}] x+z=0".asSequent
  }

  "ODE" should "prove a strict barrier certificate" in withMathematica {qeTool =>
    //This one doesn't actually need the full power of strict barriers because it's also an inequational dbx
    val fml = "x>=0 -> [{x'=100*x^4+y*x^3-x^2+x+c, c'=x+y+z & c > x}] x>=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) &
      DifferentialTactics.dgBarrier()(1))
    pr shouldBe 'proved
  }

  "ODE" should "prove a strict barrier certificate 1" in withMathematica {qeTool =>
    val fml = "(87*x^2)/200 - (7*x*y)/180 + (209*y^2)/1080 - 10 >=0 -> [{x'=(5*x)/4 - (5*y)/6, y'=(9*x)/4 + (5*y)/2}] (87*x^2)/200 - (7*x*y)/180 + (209*y^2)/1080 - 10>=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) &
      DifferentialTactics.dgBarrier(Some(qeTool))(1))
    pr shouldBe 'proved
  }

  "ODE" should "prove a strict barrier certificate 2" in withMathematica {qeTool =>
    val fml = "(23*x^2)/11 + (34*x*y)/11 + (271*y^2)/66 - 5 <= 0 -> [{x'=(x/2) + (7*y)/3 , y'=-x - y}] (23*x^2)/11 + (34*x*y)/11 + (271*y^2)/66 - 5<=0".asFormula
    val pr = TactixLibrary.proveBy(fml,implyR(1) &
      DifferentialTactics.dgBarrier(Some(qeTool))(1))
    pr shouldBe 'proved
  }

  /** End temporary tests */

  "ODE" should "prove x=0 -> [{x'=-x}]x=0" in withMathematica { _ =>
    TactixLibrary.proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "do a ghost with Z3" ignore withZ3 { _ =>
    //@note Z3 does not implement AlgebraTool
    TactixLibrary.proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "prove FM tutorial 4" in withQE { _ => withDatabase { db =>
    val modelContent = KeYmaeraXArchiveParser.getEntry("Formal Methods Tutorial Example 4", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get.fileContent
    db.proveBy(modelContent, implyR(1) & ODE(1)) shouldBe 'proved
  }}

  "Z3" should "prove what's needed by ODE for the Z3 ghost" in withZ3 { _ =>
    the [BelleThrowable] thrownBy TactixLibrary.proveBy("\\forall x_0 (x_0>0&true->\\forall x (x>0->-x>=0))".asFormula, QE) should have message
      "[Bellerophon Runtime] QE with Z3 gives SAT. Cannot reduce the following formula to True:\ntrue->\\forall x_0 (x_0>0&true->\\forall x (x>0->-x>=0))\n"
    TactixLibrary.proveBy("\\forall y__0 \\forall x_0 (x_0*y__0^2>0->x_0>0)".asFormula, QE) shouldBe 'proved
    TactixLibrary.proveBy("true->2!=0".asFormula, QE) shouldBe 'proved
    TactixLibrary.proveBy("\\forall x_0 (x_0>0->\\exists y_ (true->x_0*y_^2>0&\\forall x \\forall y_ (-x)*y_^2+x*(2*y_^(2-1)*(1/2*y_+0))>=0))".asFormula, QE) shouldBe 'proved
  }


  "QE" should "be able to prove the arithmetic subgoal from x'=-x case" in withQE { _ =>
    val f = "x>0->(\\exists y_ (true->x*y_^2>0&\\forall x \\forall y_ (-x)*y_^2+x*(2*y_^(2-1)*(1/2*y_+0))>=0))".asFormula
    TactixLibrary.proveBy(f, QE) shouldBe 'proved
  }

  "Pretest" should "PDEify x^2+y^2=1&e=x -> [{x'=-y,y'=e,e'=-y}](x^2+y^2=1&e=x)" in withQE { _ =>
    TactixLibrary.proveBy("x^2+y^2=1&e=x -> [{x'=-y,y'=e,e'=-y}](x^2+y^2=1&e=x)".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "autocut x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "solve to prove x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0".asFormula, implyR(1) & ODE(1) & onAll(QE)) shouldBe 'proved
  }

  it should "DI to prove w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9" in withQE { _ =>
    TactixLibrary.proveBy("w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "cut to prove x>=0&v>=0&a>=0->[{x'=v,v'=a,a'=a^2}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&v>=0&a>=0->[{x'=v,v'=a,a'=a^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "cut to prove x>=0&v>=0&a>=0&j>=0->[{x'=v,v'=a,a'=j,j'=j^2}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&v>=0&a>=0&j>=0->[{x'=v,v'=a,a'=j,j'=j^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  "openDiffInd" should "directly prove x>0 -> [{x'=x}]x>0" in withQE { _ =>
    proveBy("x>0 -> [{x'=x}]x>0".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  "DGauto" should "DGauto x>0 -> [{x'=-x}]x>0 by DA" in withMathematica { _ =>
    proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  //  ignore should "DGauto x_>0 -> [{x_'=-x_}]x_>0 by DA" in withQE { qeTool =>
  //    proveBy("x_>0 -> [{x_'=-x_}]x_>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  //  }

  it should "DGauto x>0->[{x'=-x+1}]x>0" in withMathematica { _ =>
    //@note: ghost is y'=1/2*y for x*y^2>0
    proveBy("x>0->[{x'=-x+1}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0&a()>0->[{x'=-a()*x}]x>0" in withMathematica { _ =>
    proveBy("x>0&a()>0->[{x'=-a()*x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0&a>0->[{x'=-a*x}]x>0" in withMathematica { _ =>
    proveBy("x>0&a>0->[{x'=-a*x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0" in withMathematica { _ =>
    proveBy("x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0->[{x'=-a*x,a'=4&a>0}]x>0" in withMathematica { _ =>
    proveBy("x>0->[{x'=-a*x,a'=4&a>0}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>0 |- [{x'=2}]x>0" in withMathematica { _ =>
    //@note: ghost is y'=x*y for x*y^2>0
    proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>0".asFormula)), DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>b() |- [{x'=2}]x>b()" in withMathematica { _ =>
    proveBy(Sequent(IndexedSeq("x>b()".asFormula), IndexedSeq("[{x'=2}]x>b()".asFormula)), DGauto(1)) shouldBe 'proved
  }

  it should "DGauto x>b |- [{x'=2}]x>b" taggedAs TodoTest ignore withMathematica { _ =>
    proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)), DGauto(1)) shouldBe 'proved
  }

  "Auto ODE" should "prove x>0 -> [{x'=x}]x>0" taggedAs SummaryTest in withQE { _ =>
    proveBy("x>0 -> [{x'=x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }
  it should "prove x>0 -> [{x'=x}]x>0 with lengthy tactic" in withQE { _ =>
    proveBy("x>0 -> [{x'=x}]x>0".asFormula, (implyR(1) & ODE(1) & (onAll(QE) | done)) | skip) shouldBe 'proved
  }
  it should "prove x>0 -> [{x'=x}]x>0 with lengthy tactic 2" in withQE { _ =>
    TactixLibrary.proveBy("x>0 -> [{x'=x}]x>0".asFormula, (implyR(1) & ODE(1) & (onAll(QE) | done)) | skip) shouldBe 'proved
  }

  it should "prove x^3>5 -> [{x'=x^3+x^4}]x^3>5" in withQE { _ =>
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "split and prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withQE { _ =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & boxAnd(1) & andR(1) <(
      ODE(1),
      ODE(1)
      )) shouldBe 'proved
  }

  it should "split and on all prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withQE { _ =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & boxAnd(1) & andR(1) & onAll(
      ODE(1)
      )) shouldBe 'proved
  }

  it should "split* and on all prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withQE { _ =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & ((boxAnd(1) & andR(1))*) & onAll(
      ODE(1)
    )) shouldBe 'proved
  }

  it should "prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withQE { _ =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "prove x>0 -> [{x'=-x}]x>0 by DA" taggedAs SummaryTest in withMathematica { _ =>
    proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "prove x>0&y>0&a>0->[{x'=y,y'=y*a}]x>0" in withQE { _ =>
    proveBy("x>0&y>0&a>0->[{x'=y,y'=y*a}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "cut to prove x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "cut to prove x>=0&y>=0&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&y>=0&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "PDEify to prove x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" in withQE { _ =>
    TactixLibrary.proveBy("x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8".asFormula, implyR(1) & ODE(1)) shouldBe 'proved
  }

  it should "work with nested ODEs" in withQE { _ =>
    proveBy("x>0 -> [{x'=5};{x'=2};{x'=x}]x>0".asFormula, (unfoldProgramNormalize & ODE(1))*3) shouldBe 'proved
  }

  it should "work with solvable maybe bound" in withQE { _ =>
    val result = proveBy("[{x'=5}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asFormula, ODE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain theSameElementsAs List("\\forall t_ (t_>=0 -> \\forall x (x=5*t_+x_1 -> [{x:=x+3;}* ++ y:=x;](x>0&y>0)))".asFormula)
  }

  it should "work with maybe bound" in withMathematica { _ =>
    val result = proveBy("x>0 -> [{x'=-x}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asFormula,
      implyR(1) & DifferentialTactics.ODE(introduceStuttering=true, dW(1) & assignb(1, 1::Nil))(1))
    result.subgoals.loneElement shouldBe "==> true&x>0 -> [{x:=x+3;}* ++ y:=x;](x>0&y>0)".asSequent
  }

  it should "not stutter repeatedly" in withQE { _ =>
    val result = proveBy("[{x'=x^x}]x>0".asFormula, ODE(1) | skip)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain theSameElementsAs "[{x'=x^x}]x>0".asFormula::Nil
  }

  it should "prove cheat sheet example" in withQE { _ => {
    val f = KeYmaeraXProblemParser(
      """
        |/* Example from KeYmaera X Cheat Sheet */
        |Functions.        /* function symbols cannot change their value */
        |    R A.          /* real-valued maximum acceleration constant */
        |    R B.          /* real-valued maximum braking constant */
        |End.
        |
        |ProgramVariables. /* program variables may change their value over time */
        |    R x.          /* real-valued position */
        |    R v.          /* real-valued velocity */
        |    R a.          /* current acceleration chosen by controller */
        |End.
        |
        |Problem.                               /* conjecture in differential dynamic logic */
        |    v>=0 & A>0 & B>0                   /* initial condition */
        |  ->                                   /* implies */
        |  [                                    /* all runs of hybrid system dynamics */
        |    {                                  /* braces {} for grouping of programs */
        |      {?v<=5;a:=A; ++ a:=0; ++ a:=-B;} /* nondeterministic choice of acceleration a */
        |      {x'=v, v'=a & v>=0}              /* differential equation system with domain */
        |    }* @invariant(v>=0)                /* loop repeats, with invariant contract */
        |  ] v>=0                               /* safety/postcondition */
        |End.
      """.stripMargin
    )

    val t =
      """
        |implyR(1) ; andL(-1) ; andL(-2) ; loop({`v>=0`}, 1) ; <(
        |  master,
        |  master,
        |  composeb(1) ; choiceb(1) ; andR(1) ; <(
        |    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; ODE(1),
        |    choiceb(1) ; assignb(1.0) ; assignb(1.1) ; andR(1) ; <(
        |      solve(1) ; master,
        |      solve(1) ; master
        |      )
        |    )
        |  )
      """.stripMargin.asTactic

    TactixLibrary.proveBy(f, t) shouldBe 'proved


  }}

  //@note: there's overlap as multiple methods are able to prove some of the following examples
  private val list = Table(("Formula", "QE Tool"),
    // solvable cases
    ("x>=0&v=1 -> [{x'=v}]x>=0", "Any"),
    ("x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0", "Any"),
    ("x>0&v=1 -> [{x'=v}]x>0", "Any"),
    ("x>0&v=1&a=2 -> [{x'=v,v'=a}]x>0", "Any"),
    ("x>0&v=1&a=2 -> [{x'=v,v'=a&v>=0}](x>0&v>=0)", "Any"),
    ("x>1&v=10&a=-2 -> [{x'=v,v'=a&v>=0}](x>1&v>=0)", "Any"),
    ("x>=1&v=10&a=-2 -> [{x'=v,v'=a&v>=0}](x>=1&v>=0)", "Any"),
    ("x>b -> [{x'=2}]x>b", "Any"),
    // open cases
    ("x^2>5 -> [{x'=x^3}]x^2>5", "Any"),
    ("5<x^2 -> [{x'=x^3}]5<x^2", "Any"),
    ("x^3>5 -> [{x'=x^4}]x^3>5", "Any"),
    ("5<x^3 -> [{x'=x^4}]5<x^3", "Any"),
    ("x^3>5 -> [{x'=x^3+x^4}]x^3>5", "Any"),
    ("5<x^3 -> [{x'=x^3+x^4}]5<x^3", "Any"),
    ("x>0->[{x'=x+5}]x>0", "Any"),
    ("x>0->[{x'=x^2+5}]x>0", "Any"),
    ("x^3>0->[{x'=x+5}]x^3>0", "Any"),
    ("x^3>0->[{x'=x^2+5}]x^3>0", "Any"),
    ("y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}]y>2", "Any"),
    ("y^3>2 -> [{x'=x^3+x^4,y'=5*y+y^2}]y^3>2", "Any"),
    ("y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}]y^3>2", "Any"),
    // split open cases
    ("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)", "Any"),
    // split cases
    ("x>=1&y=10&a=-2 -> [{x'=y,y'=a+y^2-y&y>=0}](x>=1&y>=0)", "Any"),
    // auto-ghost
    ("x>0->[{x'=-x}]x>0", "Mathematica"),
    ("x>0->[{x'=x}]x>0", "Any"),
    ("x>0->[{x'=-5*x}]x>0", "Mathematica"),
    ("x>0->[{x'=5*x}]x>0", "Any"),
    ("x>0->[{x'=x+1}]x>0", "Any"),
    ("z>0->[{z'=-z}]z>0", "Mathematica"),
    ("z>0->[{z'=z}]z>0", "Any"),
    ("z>0->[{z'=z+1}]z>0", "Any"),
    //"x>0->[{x'=-x+1}]x>0",
    ("x>0&a()>0->[{x'=-a()*x}]x>0", "Mathematica"),
    ("x>0&a>0->[{x'=-a*x}]x>0", "Mathematica"),
    ("x>0->[{x'=-a*x,a'=4&a>0}]x>0", "Mathematica"),
    ("x>0->[{x'=-a*x,a'=-4&a>0}]x>0", "Mathematica"),
    ("x>0&a()<0->[{x'=a()*x}]x>0", "Mathematica"),
    ("x>0&a<0->[{x'=a*x}]x>0", "Mathematica"),
    ("x>0&a()>0&c()<0->[{x'=a()*c()*x}]x>0", "Mathematica"),
    ("x>0&a>0&c<0->[{x'=a*c*x}]x>0", "Mathematica"),
    ("x>0&a>0&b>=0->[{x'=a*x+b}]x>0", "Any"),
    //"x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0",
    //"x>0&a<0&b>=0->[{x'=a*x+b}]x>0",
    // conserved quantity
    ("x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c -> [{x1'=2*x1^4*x2+4*x1^2*x2^3-6*x1^2*x2, x2'=-4*x1^3*x2^2-2*x1*x2^4+6*x1*x2^2}] x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c", "Any"),
    // diffcut
    //"x>=0&y>0&a>0->[{x'=y,y'=y*a}]x>=0",
    // misc
    ("x>0->[{x'=-x+1}]x>0", "Mathematica"),
    ("x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0", "Mathematica"),
    ("x>0&a<0&b>=0->[{x'=a*x+b}]x>0", "Mathematica"),
    ("x^3>0&a<0&b>0->[{x'=a*x+b}]x^3>0", "Mathematica"),
    ("x>0->[{x'=x^3+x}]x>0", "Any"),
    ("x>0->[{x'=-x^3-x}]x>0", "Mathematica"),
    ("x^3>0->[{x'=x^3+x^4}]x^3>0", "Any"),
    ("x^3>0->[{x'=-x^3-x^4}]x^3>0", "Mathematica"),
    // exams
    ("x>=1|x^3>=8->[{x'=x^4+x^2}](x>=1|x^3>=8)", "Any"),
    ("x^3-4*x*y>=99->[{x'=4*x,y'=3*x^2-4*y}]x^3-4*x*y>=99", "Any"),
    ("x^3-4*x*y=100->[{x'=4*x,y'=3*x^2-4*y}]x^3-4*x*y=100", "Any"),
    //"x>=2&y>=22->[{x'=4*x^2,y'=x+y^4}]y>=22",
    ("w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9", "Any"),
    //"x>=2&y=1->[{x'=x^2+y+x^4,y'=y^2+1}]x^3>=1",
    //"x=-1&y=1->[{x'=6*x*y-2*y^3,y'=-6*x^2+6*x*y^2}]-2*x*y^3+6*x^2*y>=0",
    //"x>=2&y=1->[{x'=x^2*y^3+x^4*y,y'=y^2+2*y+1}]x^3>=8",
    //"x-x^2*y>=2&y!=5->[{x'=-x^3,y'=-1+2*x*y}]x-x^2*y>=2",
    //"x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8",
    ("x>0&y>0&a>0->[{x'=y,y'=y*a}]x>0", "Any"),
    ("x>=0&y>0&a>0->[{x'=y,y'=y*a}]x>=0", "Any"),
    ("x>=2&y>=22->[{x'=4*x^2,y'=x+y^4}]y>=22", "Any"),
    ("x>=2&y>=0->[{x'=x^2+y+x^4,y'=y^2+1}]x^3>=1", "Any"),
    ("x>=0&y>=0&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8", "Any"),
    ("x>=0&v>=0&a>=0->[{x'=v,v'=a,a'=a^2}]x>=0", "Any"),
    ("x>=0&v>=0&a>=0&j>=0->[{x'=v,v'=a,a'=j,j'=j^2}]x>=0", "Any"),
    // ITP'12
    ("x^2+y^2=1&e=x -> [{x'=-y,y'=e,e'=-y}](x^2+y^2=1&e=x)", "Any"),
    ("d1^2+d2^2=w()^2*p^2&d1=-w()*x2&d2=w()*x1 -> [{x1'=d1,x2'=d2,d1'=-w()*d2,d2'=w()*d1}](d1^2+d2^2=w()^2*p^2&d1=-w()*x2&d2=w()*x1)", "Any"),
    ("d1^2+d2^2=w^2*p^2&d1=-w*x2&d2=w*x1 -> [{x1'=d1,x2'=d2,d1'=-w*d2,d2'=w*d1}](d1^2+d2^2=w^2*p^2&d1=-w*x2&d2=w*x1)", "Any"),
    // more
    ("x>-1->[{x'=-x-1}]x>-1", "Mathematica"),
    // improved
    ("x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8", "Any"),
    ("x>=1->[{x'=x^2+2*x^4}]x^3>=x^2", "Any") // @generalize(x>=1)&dI
  )

  it should "prove a list of ODEs" in withQE { qeTool =>
    forEvery (list) {
      (formula, requiredTool) =>
        if (requiredTool == "Any" || qeTool.asInstanceOf[Tool].name == requiredTool) {
          TactixLibrary.proveBy(formula.asFormula, implyR(1) & ODE(1) & onAll(QE)) shouldBe 'proved
        }
    }
  }

  it should "detect when additional auto ODEs become supported" in withQE { qeTool =>
    forEvery (list) {
      (formula, requiredTool) =>
        if (requiredTool != "Any" && qeTool.asInstanceOf[Tool].name != requiredTool) {
          a [BelleThrowable] should be thrownBy TactixLibrary.proveBy(formula.asFormula, implyR(1) & ODE(1) & onAll(QE))
        }
    }
  }

  private val nops = Table("Formula",
    "x=-1&y>=0->[{x'=6*x*y-2*y^3,y'=-6*x^2+6*x*y^2}]-2*x*y^3+6*x^2*y>=0",
    "x=-1&y=1->[{x'=6*x*y-2*y^3,y'=-6*x^2+6*x*y^2}]-2*x*y^3+6*x^2*y>=0",
    "x-x^2*y>=2&y!=5->[{x'=-x^3,y'=-1+2*x*y}]x-x^2*y>=2",
    "x^3>-1->[{x'=-x-1}]x^3>-1" // @generalize(x>=-1)&ode
  )

  it should "prove a list of ODEs with cuts after improving tactics" taggedAs TodoTest ignore withQE { _ =>
    forEvery (nops) {
      formula =>
        TactixLibrary.proveBy(formula.asFormula, implyR(1) & ODE(1) & onAll(QE)) shouldBe 'proved
    }
  }

  "splitWeakInequality" should "split x>=0->[{x'=x}]x>=0" in withQE { _ =>
    val f = "x>=0->[{x'=x}]x>=0".asFormula
    val result = proveBy(f, implyR(1) & DifferentialTactics.splitWeakInequality(1))
    result.subgoals.length shouldBe 2
    result.subgoals(0).succ.last shouldBe "[{x'=x&true}]x>0".asFormula
    result.subgoals(1).succ.last shouldBe "[{x'=x&true}]x=0".asFormula
  }

  it should "prove x>=0->[{x'=x}]x>=0 via ODE" in withMathematica { _ =>
    val f = "x>=0->[{x'=x}]x>=0".asFormula
    proveBy(f, implyR(1) & ODE(1) & onAll(QE)) shouldBe 'proved
  }

  "1D Saddle Node" should "prove with a bifurcation" in withMathematica { _ =>
    val formula = """r <= 0 -> \exists f (x=f -> [{x'=r+x^2}]x=f)""".asFormula
    val tactic = """implyR(1);
              |cut({`r=0|r < 0`}) <(hideL(-1), hideR(1) ; QE); orL(-1) <(
              |  existsR({`0`}, 1) ;
              |  implyR(1) ;
              |  dG({`{y'=-x*y}`}, {`y*x=0&y>0`}, 1) ; existsR({`1`}, 1) ;
              |  boxAnd(1) ; andR(1) ; <(
              |    dI(1),
              |    dG({`{z'=x/2*z}`}, {`z^2*y=1`}, 1) ; existsR({`1`}, 1) ; dI(1)
              |  )
              |  ,
              |  cut({`\exists s r=-s*s`}) ; <(
              |    existsL(-2) ; existsR({`-s`}, 1) ; implyR(1) ; dG({`{y'=(-(x-s))*y}`}, {`y*(x+s)=0&y>0`}, 1) ; existsR({`1`}, 1) ; boxAnd(1) ; andR(1) ; <(
              |      dI(1),
              |      dG({`{z'=(x-s)/2*z}`}, {`z^2*y=1`}, 1) ; existsR({`1`}, 1) ; dI(1)
              |    ),
              |    hideR(1) ; QE
              |  )
              |)""".stripMargin.asTactic

    proveBy(formula, tactic) shouldBe 'proved
  }

  it should "prove with tree-shaped proof" in withMathematica { _ =>
    val formula = """r <= 0 -> \exists f (x=f -> [{x'=r+x^2}]x=f)""".asFormula

    val tactic = """implyR(1);
                   |cut({`r=0|r < 0`}) <(
                   |  hideL(-1); orL(-1) <(
                   |    existsR({`0`}, 1) ;
                   |    implyR(1) ;
                   |    dG({`{y'=-x*y}`}, {`y*x=0&y>0`}, 1) ; existsR({`1`}, 1) ;
                   |    boxAnd(1) ; andR(1) ; <(
                   |      dI(1),
                   |      dG({`{z'=x/2*z}`}, {`z^2*y=1`}, 1) ; existsR({`1`}, 1) ; dI(1)
                   |    )
                   |    ,
                   |    cut({`\exists s r=-s*s`}) ; <(
                   |      existsL(-2) ; existsR({`-s`}, 1) ; implyR(1) ; dG({`{y'=(-(x-s))*y}`}, {`y*(x+s)=0&y>0`}, 1) ; existsR({`1`}, 1) ; boxAnd(1) ; andR(1) ; <(
                   |        dI(1),
                   |        dG({`{z'=(x-s)/2*z}`}, {`z^2*y=1`}, 1) ; existsR({`1`}, 1) ; dI(1)
                   |      ),
                   |      hideR(1) ; QE
                   |    )
                   |  )
                   |  ,
                   |  hideR(1) ; QE
                   |)""".stripMargin.asTactic

    proveBy(formula, tactic) shouldBe 'proved
  }
}
