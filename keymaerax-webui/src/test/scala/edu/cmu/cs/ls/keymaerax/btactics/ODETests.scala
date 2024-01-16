/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics.universalGen
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.AnnotationProofHint
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import edu.cmu.cs.ls.keymaerax.tools.Tool
import testHelper.KeYmaeraXTestTags.{SummaryTest, TodoTest}

import scala.collection.immutable._
import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps
import org.scalatest.LoneElement._
import org.scalatest.exceptions.TestCanceledException
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.time.SpanSugar._

/**
 * Tests automatic
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.ODE]] differential equations proving.
 */
@UsualTest
class ODETests extends TacticTestBase(registerAxTactics = Some("z3")) {

  "ODE" should "prove x>0 -> [{x'=-x}]x>0" in withMathematica { _ =>
    TactixLibrary.proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove after unstable diffcut position" in withMathematica { _ =>
    TactixLibrary.proveBy(
      "(x+w/-1-ox)^2+(y-v/-1-oy)^2!=v^2+w^2 ==> [{x'=v,y'=w,v'=-1*w,w'=--1*v&true}](!(x=ox&y=oy)), x=ox&y=oy".asSequent,
      ODE(1)) shouldBe Symbol("proved")
  }

  it should "do a ghost with Z3" in withZ3 { _ =>
    TactixLibrary.proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove FM tutorial 4" in withMathematica { _ => withDatabase { db =>
    val modelContent = ArchiveParser.getEntry("FM16/Tutorial Example 4", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/fm/fm.kyx")).mkString).get.fileContent
    db.proveBy(modelContent, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }}

  it should "prove STTT tutorial 3a cases" in withQE { _ =>
    proveBy("A()>0, B()>0, v>=0, x+v^2/(2*B())<=S(), x+v^2/(2*B()) < S()\n  ==>  [{x'=v,v'=A()&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())".asSequent, ODE(1)) shouldBe Symbol("proved")
    proveBy("A()>0, B()>0, v>=0, x+v^2/(2*B())<=S(), x+v^2/(2*B()) < S()\n  ==>  [{x'=v,v'=A()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())".asSequent, ODE(1)) shouldBe Symbol("proved")
    proveBy("A()>0, B()>0, v>=0, x+v^2/(2*B())<=S(), v=0\n  ==>  [{x'=v,v'=0&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())".asSequent, ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove a double integrator with events" in withMathematica { _ =>
    val s = "x()>=0, A()>0, B()>0, y<=x()|(y-x())^2<=2*B()*(i-j), x()>=0, y>=0, A()>0, B()>0, j<=i, y<=x()|(y-x())^2<=4*B()*(i-j) ==> [{j'=y,y'=A(),i'=x()&y>=0&!(y<=x()|(y-x())^2<=2*B()*(i-j))}]((x()>=0&y>=0&A()>0&B()>0&j<=i)&(y<=x()|(y-x())^2<=2*B()*(i-j)))".asSequent
    proveBy(s, ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove a barrier certificate" in withQE { _ =>
    val fml =
      """
        |x^2 <= 1/2 & y^2 <= 1/3 ->
        | [
        |   {x'=-x - (1117*y)/500 + (439*y^3)/200 - (333*y^5)/500, y'=x + (617*y)/500 - (439*y^3)/200 + (333*y^5)/500}
        | ] (x - 4*y < 8)
      """.stripMargin.asFormula

    TactixInit.differentialInvGenerator = new FixedGenerator[(Formula, Option[InvariantGenerator.ProofHint])](
      ("x^2 + x*y + y^2 - 111/59 <= 0".asFormula -> Some(AnnotationProofHint(tryHard = false))) :: Nil)
    proveBy(fml, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove when invariants are present in negated form" in withQE { _ =>
    val s = "x!=ox | y!=oy, (x+w/1-ox)^2+(y-v/1-oy)^2 != v^2+w^2 ==> [{x'=v, y'=w, v'=1*w, w'=-1*v}]!(x=ox & y=oy)".asSequent
    proveBy(s, ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove when postcondition is invariant" in withMathematica { _ =>
    // tests that trivial invariant generator results are not accidentally discarded
    // (e.g., Pegasus will return (True,PostInv) as an invariant, which is discarded in relevance filtering)
    val seq = "y=2*(x1^2+x2^2) ==>  [{x1'=-x1-x2,x2'=x1-x2,y'=- 1*y&true}]x1^2+2*x2^2-y<=0".asSequent
    TactixLibrary.proveBy(seq, ODE(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: prove when postcondition is invariant" taggedAs TodoTest in withZ3 { _ =>
    // tests that trivial invariant generator results are not accidentally discarded
    // (e.g., Pegasus will return (True,PostInv) as an invariant, which is discarded in relevance filtering)
    val seq = "y=2*(x1^2+x2^2) ==>  [{x1'=-x1-x2,x2'=x1-x2,y'=- 1*y&true}]x1^2+2*x2^2-y<=0".asSequent
    TactixLibrary.proveBy(seq, ODE(1)) shouldBe Symbol("proved")
  }

  it should "fall back to dI in non-top positions" in withQE { _ =>
    //@todo support true ODE in context
    proveBy("x=1 ==> \\exists y [{x'=y}]x>=1".asSequent, ODE(1, 0::Nil)).subgoals.loneElement shouldBe "x=1 ==> \\exists y (x>=1&y>=0)".asSequent
    proveBy("x=1 ==> \\forall y (y>=0 -> [{x'=y}]x>=1)".asSequent, ODE(1, 0::1::Nil)).subgoals.loneElement shouldBe "x=1 ==> \\forall y (y>=0 -> x>=1&y>=0)".asSequent
    proveBy("x=1 ==> \\forall y (y>=0 -> [{x'=y}@invariant(x>=1)]x>=0)".asSequent, ODE(1, 0::1::Nil)).subgoals.loneElement shouldBe "x=1 ==> \\forall y (y>=0 -> x>=1 -> x>=0 & \\forall x (x>=1->y>=0))".asSequent
  }

  it should "prove STTT Example 9b subgoal fast" in withMathematica { _ =>
    proveBy("Kp()=2, Kd()=3, 5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm_0)/2)^2, xr=(xm_0+S())/2, v>=0, xm_0<=x, xm=x, 5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2\n  ==>  [{x'=v,v'=-Kp()*(x-(xm+S())/2)-Kd()*v&v>=0}]5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2".asSequent, ODE(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: work in existential context" taggedAs TodoTest in withQE { _ =>
    proveBy("x=1 ==> \\exists y [{x'=y}@invariant(x>=1)]x>=0".asSequent, ODE(1, 0::Nil)) shouldBe Symbol("proved") // or at least not fail in dC
  }

  "Z3" should "prove what's needed by ODE for the Z3 ghost" in withZ3 { _ =>
    the [BelleThrowable] thrownBy TactixLibrary.proveBy("\\forall x_0 (x_0>0&true->\\forall x (x>0->-x>=0))".asFormula, QE) should have message
      "QE with Z3 gives SAT. Cannot reduce the following formula to True:\n\\forall x_0 \\forall x (x_0>0&x>0->-x>=0)\n"
    TactixLibrary.proveBy("\\forall y__0 \\forall x_0 (x_0*y__0^2>0->x_0>0)".asFormula, QE) shouldBe Symbol("proved")
    TactixLibrary.proveBy("true->2!=0".asFormula, QE) shouldBe Symbol("proved")
    TactixLibrary.proveBy("\\forall x_0 (x_0>0->\\exists y_ (true->x_0*y_^2>0&\\forall x \\forall y_ (-x)*y_^2+x*(2*y_^(2-1)*(1/2*y_+0))>=0))".asFormula, QE) shouldBe Symbol("proved")
  }

  it should "prove a postcondition invariant that requires trying hard" in withMathematica { _ =>
    proveBy("u^2<=v^2+9/2 ==> [{u'=-v+u/4*(1-u^2-v^2),v'=u+v/4*(1-u^2-v^2)}]u^2<=v^2+9/2".asSequent, ODE(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: prove a postcondition invariant that requires trying hard" taggedAs TodoTest in withZ3 { _ =>
    proveBy("u^2<=v^2+9/2 ==> [{u'=-v+u/4*(1-u^2-v^2),v'=u+v/4*(1-u^2-v^2)}]u^2<=v^2+9/2".asSequent, ODE(1)) shouldBe Symbol("proved")
  }

  "QE" should "be able to prove the arithmetic subgoal from x'=-x case" in withQE { _ =>
    val f = "x>0->(\\exists y_ (true->x*y_^2>0&\\forall x \\forall y_ (-x)*y_^2+x*(2*y_^(2-1)*(1/2*y_+0))>=0))".asFormula
    TactixLibrary.proveBy(f, QE) shouldBe Symbol("proved")
  }

  "Pretest" should "PDEify x^2+y^2=1&f=x -> [{x'=-y,y'=f,f'=-y}](x^2+y^2=1&f=x)" in withQE { _ =>
    withTemporaryConfig(Map(Configuration.Keys.ODE_TIMEOUT_FINALQE -> "-1")) {
      TactixLibrary.proveBy("x^2+y^2=1&f=x -> [{x'=-y,y'=f,f'=-y}](x^2+y^2=1&f=x)".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
    }
  }

  it should "autocut x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "solve to prove x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&v=1&a=2 -> [{x'=v,v'=a}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9" in withQE { _ =>
    TactixLibrary.proveBy("w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "cut to prove x>=0&v>=0&a>=0->[{x'=v,v'=a,a'=a^2}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&v>=0&a>=0->[{x'=v,v'=a,a'=a^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "cut to prove x>=0&v>=0&a>=0&j>=0->[{x'=v,v'=a,a'=j,j'=j^2}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&v>=0&a>=0&j>=0->[{x'=v,v'=a,a'=j,j'=j^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  "DGauto" should "DGauto x>0 -> [{x'=-x}]x>0 by DA" in withMathematica { _ =>
    proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe Symbol("proved")
  }

  it should "DGauto x>0->[{x'=-x+1}]x>0" in withMathematica { _ =>
    //@note: ghost is y'=1/2*y for x*y^2>0
    proveBy("x>0->[{x'=-x+1}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe Symbol("proved")
  }

  it should "DGauto x>0&a()>0->[{x'=-a()*x}]x>0" in withMathematica { _ =>
    proveBy("x>0&a()>0->[{x'=-a()*x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe Symbol("proved")
  }

  it should "DGauto x>0&a>0->[{x'=-a*x}]x>0" in withMathematica { _ =>
    proveBy("x>0&a>0->[{x'=-a*x}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe Symbol("proved")
  }

  it should "DGauto x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0" in withMathematica { _ =>
    proveBy("x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe Symbol("proved")
  }

  it should "DGauto x>0->[{x'=-a*x,a'=4&a>0}]x>0" in withMathematica { _ =>
    proveBy("x>0->[{x'=-a*x,a'=4&a>0}]x>0".asFormula, implyR(1) & DGauto(1)) shouldBe Symbol("proved")
  }

  it should "DGauto x>0 |- [{x'=2}]x>0" in withMathematica { _ =>
    //@note: ghost is y'=x*y for x*y^2>0
    proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>0".asFormula)), DGauto(1)) shouldBe Symbol("proved")
  }

  it should "DGauto x>b() |- [{x'=2}]x>b()" in withMathematica { _ =>
    proveBy(Sequent(IndexedSeq("x>b()".asFormula), IndexedSeq("[{x'=2}]x>b()".asFormula)), DGauto(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: DGauto x>b |- [{x'=2}]x>b" taggedAs TodoTest in withMathematica { _ =>
    proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)), DGauto(1)) shouldBe Symbol("proved")
  }

  "Auto ODE" should "prove x>0 -> [{x'=x}]x>0" taggedAs SummaryTest in withQE { _ =>
    proveBy("x>0 -> [{x'=x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove x^3>5 -> [{x'=x^3+x^4}]x^3>5" in withQE { _ =>
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "split and prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withQE { _ =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & boxAnd(1) & andR(1) <(
      ODE(1),
      ODE(1)
      )) shouldBe Symbol("proved")
  }

  it should "split and on all prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withQE { _ =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & boxAnd(1) & andR(1) & onAll(
      ODE(1)
      )) shouldBe Symbol("proved")
  }

  it should "split* and on all prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withQE { _ =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & SaturateTactic(onAll(Idioms.?(boxAnd(1) & andR(1)))) & onAll(
      ODE(1)
    )) shouldBe Symbol("proved")
  }

  it should "prove x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)" in withQE { _ =>
    proveBy("x^3>5 & y>2 -> [{x'=x^3+x^4,y'=5*y+y^2}](x^3>5&y>2)".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove x>0 -> [{x'=-x}]x>0 by DA" taggedAs SummaryTest in withMathematica { _ =>
    proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "prove x>0&y>0&a>0->[{x'=y,y'=y*a}]x>0" in withQE { _ =>
    proveBy("x>0&y>0&a>0->[{x'=y,y'=y*a}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "cut to prove x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&y>=0 -> [{x'=y,y'=y^2}]x>=0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "cut to prove x>=0&y>=0&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" in withQE { _ =>
    TactixLibrary.proveBy("x>=0&y>=0&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "PDEify to prove x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8" in withMathematica { _ =>
    //@todo Z3
    TactixLibrary.proveBy("x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  it should "work with nested ODEs" in withQE { _ =>
    proveBy("x>0 -> [{x'=5};{x'=2};{x'=x}]x>0".asFormula, (unfoldProgramNormalize & ODE(1) & dWPlus(1))*3) shouldBe Symbol("proved")
  }

  it should "work with solvable maybe bound" in withQE { _ =>
    val result = proveBy("[{x'=5}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asFormula, ODE(1))
    result.subgoals.loneElement should
      (   be("true, time_=0, x_0=x ==> [{x'=5,time_'=1 & true & time_>=0&x=5*time_+x_0}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asSequent)
       //Z3
       or be("true, time_=0, x_0=x ==> [{x'=5,time_'=1 & true & time_>=0&x=x_0+5*time_}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asSequent))
  }

  it should "work with maybe bound" in withMathematica { _ =>
    //@note partial result from ODE
    val result = proveBy("x>0 -> [{x'=-x}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asFormula, implyR(1) & ODE(1))
    result.subgoals.loneElement shouldBe "x>0 ==> [{x'=-x & x>0}][{x:=x+3;}* ++ y:=x;](x>0&y>0)".asSequent
  }

  it should "neither stutter nor fail evolution domain simplification on empty evolution domain constraint with Z3" in withZ3 { _ =>
    //@note now throws exception instead of stuttering
    the [BelleThrowable] thrownBy proveBy("[{x'=x^x}]x>0".asFormula, ODE(1)) should have message
      "ODE automation was neither able to prove the postcondition invariant nor automatically find new ODE invariants. Try annotating the ODE with additional invariants or refining the evolution domain with a differential cut.\nAn (internal) check failed at the subgoal formula [{x'=x^x}]x>0"
  }

  it should "neither stutter nor fail evolution domain simplification on empty evolution domain constraint with Mathematica" in withMathematica { _ =>
    //@note now reports CEX with Mathematica instead of stuttering
    proveBy("[{x'=x^x}]x>0".asFormula, ODE(1)).subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "prove cheat sheet example" in withQE { _ => {
    val f = ArchiveParser.parseAsFormula(
      """
        |ArchiveEntry "Example from KeYmaera X Cheat Sheet"
        |Definitions        /* function symbols cannot change their value */
        |    Real A;          /* real-valued maximum acceleration constant */
        |    Real B;          /* real-valued maximum braking constant */
        |End.
        |
        |ProgramVariables /* program variables may change their value over time */
        |    Real x;          /* real-valued position */
        |    Real v;          /* real-valued velocity */
        |    Real a;          /* current acceleration chosen by controller */
        |End.
        |
        |Problem                                /* conjecture in differential dynamic logic */
        |    v>=0 & A>0 & B>0                   /* initial condition */
        |  ->                                   /* implies */
        |  [                                    /* all runs of hybrid system dynamics */
        |    {                                  /* braces {} for grouping of programs */
        |      {?v<=5;a:=A; ++ a:=0; ++ a:=-B;} /* nondeterministic choice of acceleration a */
        |      {x'=v, v'=a & v>=0}              /* differential equation system with domain */
        |    }* @invariant(v>=0)                /* loop repeats, with invariant contract */
        |  ] v>=0                               /* safety/postcondition */
        |End.
        |End.
      """.stripMargin
    )

    val t =
      """
        |implyR(1) ; andL(-1) ; andL(-2) ; loop("v>=0", 1) ; <(
        |  auto,
        |  auto,
        |  composeb(1) ; choiceb(1) ; andR(1) ; <(
        |    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; ODE(1),
        |    choiceb(1) ; assignb(1.0) ; assignb(1.1) ; andR(1) ; <(
        |      solve(1) ; auto,
        |      solve(1) ; auto
        |      )
        |    )
        |  )
      """.stripMargin.asTactic

    TactixLibrary.proveBy(f, t) shouldBe Symbol("proved")


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
    ("x>0->[{x'=-x}]x>0", "Any"),
    ("x>0->[{x'=x}]x>0", "Any"),
    ("x>0->[{x'=-5*x}]x>0", "Any"),
    ("x>0->[{x'=5*x}]x>0", "Any"),
    ("x>0->[{x'=x+1}]x>0", "Any"),
    ("z>0->[{z'=-z}]z>0", "Any"),
    ("z>0->[{z'=z}]z>0", "Any"),
    ("z>0->[{z'=z+1}]z>0", "Any"),
    //"x>0->[{x'=-x+1}]x>0",
    ("x>0&a()>0->[{x'=-a()*x}]x>0", "Any"),
    ("x>0&a>0->[{x'=-a*x}]x>0", "Any"),
    ("x>0->[{x'=-a*x,a'=4&a>0}]x>0", "Any"),
    ("x>0->[{x'=-a*x,a'=-4&a>0}]x>0", "Any"),
    ("x>0&a()<0->[{x'=a()*x}]x>0", "Any"),
    ("x>0&a<0->[{x'=a*x}]x>0", "Any"),
    ("x>0&a()>0&c()<0->[{x'=a()*c()*x}]x>0", "Any"),
    ("x>0&a>0&c<0->[{x'=a*c*x}]x>0", "Any"),
    //("x>0&a>0&b>=0->[{x'=a*x+b}]x>0", "Any"),
    //"x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0",
    //"x>0&a<0&b>=0->[{x'=a*x+b}]x>0",
    // conserved quantity
    ("x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c -> [{x1'=2*x1^4*x2+4*x1^2*x2^3-6*x1^2*x2, x2'=-4*x1^3*x2^2-2*x1*x2^4+6*x1*x2^2}] x1^4*x2^2+x1^2*x2^4-3*x1^2*x2^2+1 <= c", "Any"),
    // diffcut
    //"x>=0&y>0&a>0->[{x'=y,y'=y*a}]x>=0",
    // misc
    ("x>0->[{x'=-x+1}]x>0", "Any"),
    //("x>0&a()<0&b()>=0->[{x'=a()*x+b()}]x>0", "Mathematica"), @note DGauto can prove, but not ODE
    //("x>0&a<0&b>=0->[{x'=a*x+b}]x>0", "Mathematica"), @note DGauto can prove, but not ODE
    ("x^3>0&a<0&b>0->[{x'=a*x+b}]x^3>0", "Any"),
    ("x>0->[{x'=x^3+x}]x>0", "Any"),
    ("x>0->[{x'=-x^3-x}]x>0", "Any"),
    ("x^3>0->[{x'=x^3+x^4}]x^3>0", "Any"),
    ("x^3>0->[{x'=-x^3-x^4}]x^3>0", "Any"),
    // exams
    ("x>=1|x^3>=8->[{x'=x^4+x^2}](x>=1|x^3>=8)", "Any"),
    ("x^3-4*x*y>=99->[{x'=4*x,y'=3*x^2-4*y}]x^3-4*x*y>=99", "Any"),
    ("x^3-4*x*y=100->[{x'=4*x,y'=3*x^2-4*y}]x^3-4*x*y=100", "Any"),
    //"x>=2&y>=22->[{x'=4*x^2,y'=x+y^4}]y>=22",
    //("w>=0&x=0&y=3->[{x'=y,y'=-w^2*x-2*w*y}]w^2*x^2+y^2<=9", "Any"),
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
    ("x>-1->[{x'=-x-1}]x>-1", "Any"),
    // improved
    ("x=1&y=2&z>=8->[{x'=x^2,y'=4*x,z'=5*y}]z>=8", "Any"),
    ("x>=1->[{x'=x^2+2*x^4}]x^3>=x^2", "Any"), // @generalize(x>=1)&dI
    ("x-x^2*y>=2&y!=5->[{x'=-x^2,y'=-1+2*x*y}]x-x^2*y>=2", "Any")
  )

  it should "prove a list of ODEs" in withQE { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.ODE_TIMEOUT_FINALQE -> "60")) {
      forEvery(list) {
        (formula, requiredTool) =>
          whenever(qeTool.isInitialized) {
            println("Proving " + formula)
            if (requiredTool == "Any" || qeTool.asInstanceOf[Tool].name == requiredTool) {
              TactixLibrary.proveBy(formula.asFormula, implyR(1) & ODE(1) & onAll(QE)) shouldBe Symbol("proved")
            }
          }
      }
    }
  }

  it should "detect when additional auto ODEs become supported" in withQE { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.ODE_TIMEOUT_FINALQE -> "60")) {
      forEvery(list) {
        (formula, requiredTool) =>
          whenever(qeTool.isInitialized) {
            if (requiredTool != "Any" && qeTool.asInstanceOf[Tool].name != requiredTool) {
              println("Works now with " + qeTool.asInstanceOf[Tool].name + "? " + formula)
              try {
                cancelAfter(2.minutes) {
                  a[BelleThrowable] should be thrownBy TactixLibrary.proveBy(formula.asFormula, implyR(1) & ODE(1) & onAll(QE) & done)
                }
              } catch {
                case _: TestCanceledException => // cancelled by timeout, not yet solved fast enough
              }
            }
          }
      }
    }
  }

  private val nops = Table("Formula",
    "x=-1&y>=0->[{x'=6*x*y-2*y^3,y'=-6*x^2+6*x*y^2}]-2*x*y^3+6*x^2*y>=0", // false, expect counterexample
    "x=-1&y=1->[{x'=6*x*y-2*y^3,y'=-6*x^2+6*x*y^2}]-2*x*y^3+6*x^2*y>=0",  // false, expect counterexample
    "x^3>-1->[{x'=-x-1}]x^3>-1" // @generalize(x>=-1)&ode
  )

  it should "FEATURE_REQUEST: prove a list of ODEs with cuts after improving tactics" taggedAs TodoTest in withQE { tool =>
    forEvery (nops) {
      formula =>
        whenever(tool.isInitialized) {
          TactixLibrary.proveBy(formula.asFormula, implyR(1) & ODE(1) & onAll(QE)) shouldBe Symbol("proved")
        }
    }
  }

  it should "use an annotated differential invariant" in withMathematica { _ =>
    proveBy("x=3 & y=4 ==> [{x'=-y,y'=x}]x^2+y^2=25".asSequent, ODE(1)) shouldBe Symbol("proved")
    //@todo find out whether ODE uses the annotated invariant at all
    proveBy("x=3 & y=4 ==> [{x'=-y,y'=x}@invariant(x^2+y^2=old(x^2+y^2))]x^2+y^2<=25".asSequent, ODE(1)) shouldBe Symbol("proved")
  }

  it should "use annotated differential invariants" in withMathematica { _ =>
    //@todo find out whether ODE uses the annotated invariant at all
    val g = "z>0, x=3, y=4 ==> [{x'=-z*y,y'=z*x,z'=z}@invariant(z>=old(z), x^2+y^2=old(x^2+y^2))]x^2+y^2=25".asSequent
    proveBy(g, ODE(1)) shouldBe Symbol("proved")
  }

  it should "interpret implications as differential invariants in simple ODE" in withMathematica { _ =>
    //@note unprovable, so that automation doesn't run off
    val g = "A>=0, b()>0 ==> [{a:=A; ++ a:=-b(); ++ a:=0;}{{v'=a}@invariant((v'=A -> v>=old(v)), (v'=-b() -> v<=old(v)), (v'=0 -> v=old(v)))}]x>0".asSequent
    val cutAnnotatedInvs = anon ((pos: Position, seq: Sequent) => {
      dC(InvariantGenerator.differentialInvariantGenerator(seq, pos, Declaration(Map.empty)).map(_._1).toList)(1) <(skip, dI()(1))
    })
    val result = proveBy(g, chase(1) & andR(1) <(cutAnnotatedInvs(1), andR(1) <(cutAnnotatedInvs(1), cutAnnotatedInvs(1))))
    result.subgoals(0) shouldBe "A>=0, b()>0, v_0=v ==> [{v'=A & true & v>=v_0}]x>0".asSequent
    result.subgoals(1) shouldBe "A>=0, b()>0, v_0=v ==> [{v'=-b() & true & v<=v_0}]x>0".asSequent
    result.subgoals(2) shouldBe "A>=0, b()>0, v_0=v ==> [{v'=0 & true & v=v_0}]x>0".asSequent
  }

  it should "interpret implications as differential invariants on multiple occurrences of substituted variable" in withMathematica { _ =>
    val g = "A>=0, b()>0 ==> [{a:=A; ++ a:=-b(); ++ a:=0;}{{v'=a,w'=a/r}@invariant((v'=A -> v>=old(v)), (v'=-b() -> v<=old(v)), (v'=0 -> v=old(v)))}]x>0".asSequent
    val cutAnnotatedInvs = anon ((pos: Position, seq: Sequent) => {
      dC(InvariantGenerator.differentialInvariantGenerator(seq, pos, Declaration(Map.empty)).map(_._1).toList)(1) <(skip, dI()(1))
    })
    val result = proveBy(g, chase(1) & andR(1) <(cutAnnotatedInvs(1), andR(1) <(cutAnnotatedInvs(1), cutAnnotatedInvs(1))))
    result.subgoals(0) shouldBe "A>=0, b()>0, v_0=v ==> [{v'=A,w'=A/r & true & v>=v_0}]x>0".asSequent
    result.subgoals(1) shouldBe "A>=0, b()>0, v_0=v ==> [{v'=-b(),w'=(-b())/r & true & v<=v_0}]x>0".asSequent
    result.subgoals(2) shouldBe "A>=0, b()>0, v_0=v ==> [{v'=0,w'=0/r & true & v=v_0}]x>0".asSequent
  }

  //todo: Move?
  "splitWeakInequality" should "split x>=0->[{x'=x}]x>=0" in withQE { _ =>
    val f = "x>=0->[{x'=x}]x>=0".asFormula
    val result = proveBy(f, implyR(1) & DifferentialTactics.splitWeakInequality(1))
    result.subgoals.length shouldBe 2
    result.subgoals(0).succ.last shouldBe "[{x'=x&true}]x>0".asFormula
    result.subgoals(1).succ.last shouldBe "[{x'=x&true}]x=0".asFormula
  }

  it should "prove x>=0->[{x'=x}]x>=0 via ODE" in withMathematica { _ =>
    val f = "x>=0->[{x'=x}]x>=0".asFormula
    proveBy(f, implyR(1) & ODE(1)) shouldBe Symbol("proved")
  }

  //todo: Move?
  "1D Saddle Node" should "prove with a bifurcation" in withMathematica { _ =>
    val formula = """r <= 0 -> \exists f (x=f -> [{x'=r+x^2}]x=f)""".asFormula
    val tactic = """implyR(1);
              |cut("r=0|r < 0") ; <(hideL(-1), hideR(1) ; QE); orL(-1) ; <(
              |  existsR("0", 1) ;
              |  implyR(1) ;
              |  dG("y'=-x*y", "y*x=0&y>0", 1) ; existsR("1", 1) ;
              |  boxAnd(1) ; andR(1) ; <(
              |    dI(1),
              |    dG("z'=x/2*z", "z^2*y=1", 1) ; existsR("1", 1) ; dI(1)
              |  )
              |  ,
              |  cut("\exists s r=-s*s") ; <(
              |    existsL(-2) ; existsR("-s", 1) ; implyR(1) ; dG("y'=(-(x-s))*y", "y*(x+s)=0&y>0", 1) ; existsR("1", 1) ; boxAnd(1) ; andR(1) ; <(
              |      dI(1),
              |      dG("z'=(x-s)/2*z", "z^2*y=1", 1) ; existsR("1", 1) ; dI(1)
              |    ),
              |    hideR(1) ; QE
              |  )
              |)""".stripMargin.asTactic

    proveBy(formula, tactic) shouldBe Symbol("proved")
  }

  //todo: Move?
  it should "prove with tree-shaped proof" in withMathematica { _ =>
    val formula = """r <= 0 -> \exists f (x=f -> [{x'=r+x^2}]x=f)""".asFormula

    val tactic = """implyR(1);
                   |cut("r=0|r < 0") ; <(
                   |  hideL(-1); orL(-1) ; <(
                   |    existsR("0", 1) ;
                   |    implyR(1) ;
                   |    dG("y'=-x*y", "y*x=0&y>0", 1) ; existsR("1", 1) ;
                   |    boxAnd(1) ; andR(1) ; <(
                   |      dI(1),
                   |      dG("z'=x/2*z", "z^2*y=1", 1) ; existsR("1", 1) ; dI(1)
                   |    )
                   |    ,
                   |    cut("\exists s r=-s*s") ; <(
                   |      existsL(-2) ; existsR("-s", 1) ; implyR(1) ; dG("{y'=(-(x-s))*y}", "y*(x+s)=0&y>0", 1) ; existsR("1", 1) ; boxAnd(1) ; andR(1) ; <(
                   |        dI(1),
                   |        dG("z'=(x-s)/2*z", "z^2*y=1", 1) ; existsR("1", 1) ; dI(1)
                   |      ),
                   |      hideR(1) ; QE
                   |    )
                   |  )
                   |  ,
                   |  hideR(1) ; QE
                   |)""".stripMargin.asTactic

    proveBy(formula, tactic) shouldBe Symbol("proved")
  }

  //todo: Move?
  "liveness" should "prove that exponential diff eqs are unbounded" in withMathematica { _ =>
    //Tests out a derived version of DV

    //Abuse DS to show that solutions exist for all time
    val texists = "x0 > 0 -> <{t'=1}> 0<=x0-x1+x0*t".asFormula
    val pr1 = proveBy(texists,
      implyR(1) & useAt(Ax.DSdnodomain)(1) &
        chase(1, 0::1::Nil) & QE
    )

    //DG for linear systems
    val xexists = "x0>0 -> <{t'=1,x'=1*x+0}> 0<=x0-x1+x0*t".asFormula
    val pr2 = proveBy(xexists,
      implyR(1) &
      universalGen(Some("x".asVariable),"x".asTerm)(1) &
      useAt(Ax.DGd, PosInExpr(1::Nil))(1) &
      implyRi &
      by(pr1)
    )

    val fml = "x=x0 & t = 0  & x0 > 0 -> <{t'=1,x'=1*x+0}> x - x1 >= 0".asFormula
    val pr = proveBy(fml, prop &
      cut("[{t'=1,x'=1*x+0 & true & x-x1 < 0}] 0 > (x0-x1)+x0*t".asFormula)
      <(
        useAt(Ax.diamond, PosInExpr(1::Nil))(1) & notR(1)  & SimplifierV3.fullSimpTac() &
        //Inverse diff cut
        cut("[{t'=1,x'=1*x+0 & true}] 0 > (x0-x1)+x0*t".asFormula) <(
          useAt(Ax.box, PosInExpr(1::Nil))(-6) & notL(-6) &
            chase(1, 1::Nil) & implyRi()(AntePos(2),SuccPos(0)) & cohideR(1) & byUS(pr2),
          dC("x-x1 < 0".asFormula)(1) < ( id,id) )
        ,
        hideR(1) & dC("x >= x0".asFormula)(1)
        <( dC("x-x1 >= (x0-x1)+x0*t".asFormula)(1) <(dW(1)&QE,dI(Symbol("full"))(1)), ODE(1))
      )
    )
    pr shouldBe Symbol("proved")
  }

  //todo: Move?
  "invariant clusters" should "prove example 6 (Kong et. al. HSCC'17)" in withMathematica { _ =>
    val fml = "(x+15)^2 + (y-17)^2 - 1 <= 0 -> [{x'=y^2, y'=x*y}] (x-11)^2+(y-33/2)^2-1>0".asFormula
    val pr = proveBy(fml,implyR(1) &
      cut("\\exists u1 \\exists u3 ( (u1^2+u3^2) !=0 & u1 -u3*(x^2-y^2)=0)".asFormula)
        <(
        SaturateTactic(existsL(Symbol("L"))) & dC("u1-u3*(x^2-y^2)=0".asFormula)(1)
          <(
          dWPlus(1) & QE,
          dI(Symbol("full"))(1)
        ),
        hideR(1) & QE
      )
    )
    //println(pr)
    pr shouldBe Symbol("proved")
  }

  "ODE Counterexample" should "disprove a wrong conjecture" in withMathematica { _ =>
    val fml = "7.1798*x^3-7.1798*y^3+21.539*x^2+21.539*y^2-3081.9<=0 ->  [{ x'=y^2-2*y, y'=x^2+2*x } ]7.1798*x^3-7.1798*y^3+21.539*x^2+21.539*y^2-3081.9<=0".asFormula
    proveBy(fml, implyR(1) & DifferentialTactics.cexODE(1)).subgoals.loneElement shouldBe "==> false".asSequent
    proveBy(fml, implyR(1) & ODE(1)).subgoals.loneElement shouldBe "==> false".asSequent
    proveBy(fml, master()).subgoals.loneElement shouldBe "==> false".asSequent
  }
}
