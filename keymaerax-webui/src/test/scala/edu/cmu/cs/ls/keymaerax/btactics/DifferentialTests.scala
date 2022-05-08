package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, TodoTest}

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Name, Signature, UnknownLocation}
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.ToolException
import testHelper.CustomAssertions._
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable.IndexedSeq
import org.scalatest.LoneElement._
import org.scalatest.OptionValues._
import org.scalatest.prop.TableDrivenPropertyChecks.forEvery
import org.scalatest.prop.Tables._

/**
  * Basic differential equation proving technology tests
  * [[edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics]],
  * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.DW]], and
  * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.DC]]
  * @see [[ContinuousInvariantTests]]
  */
@SummaryTest
@UsualTest
class DifferentialTests extends TacticTestBase {
  val randomTrials = 500
  val randomComplexity = 6
  val rand = new RandomFormula()

  "DW" should "pull out evolution domain constraint" in withTactics {
    val result = proveBy("[{x'=1 & x>2}]x>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{x'=1&x>2}](x>2 -> x>0)".asSequent
  }

  it should "pull out evolution domain constraint in some context" in withTactics {
    val result = proveBy("[x:=0;][{x'=1 & x>2}]x>0".asFormula, DW(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=0;][{x'=1 & x>2}](x>2 -> x>0)".asSequent
  }

  it should "perform alpha renaming if necessary" in withTactics {
    val result = proveBy("[{y'=y & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{y'=y & y>2 & z<0}](y>2 & z<0 -> y>0)".asSequent
  }

  it should "introduce true if there is no evolution domain constraint" in withTactics {
    val result = proveBy("[{x'=1}]x>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{x'=1}](true -> x>0)".asSequent
  }

  it should "pull out evolution domain constraints from system of ODEs" in withTactics {
    val result = proveBy("[{x'=x, y'=1 & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{x'=x, y'=1 & y>2 & z<0}](y>2 & z<0 -> y>0)".asSequent
  }

  it should "also work when the ODEs are interdependent" in withTactics {
    val result = proveBy("[{x'=x+y, y'=1, z'=2 & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{x'=x+y, y'=1, z'=2 & y>2 & z<0}](y>2 & z<0 -> y>0)".asSequent
  }

  "diffWeaken" should "perform alpha renaming if necessary" in withTactics {
    val result = proveBy("[{y'=y & y>2 & z<0}]y>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "y>2 & z<0 ==> y>0".asSequent
  }

  it should "introduce true if there is no evolution domain constraint" in withTactics {
    val result = proveBy("[{x'=1}]x>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "true ==> x>0".asSequent
  }

  it should "pull out evolution domain constraint from system of ODEs" in withTactics {
    val result = proveBy("[{x'=x, y'=1 & y>2 & z<0}]y>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "y>2 & z<0 ==> y>0".asSequent
  }

  it should "also work when the ODEs are interdependent" in withTactics {
    val result = proveBy("[{x'=x+y, y'=1, z'=2 & y>2 & z<0}]y>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "y>2 & z<0 ==> y>0".asSequent
  }

  it should "weaken if ODE afterwards" in withTactics {
    val result = proveBy("[{x'=1}][{x'=2}]x>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "true ==> [{x'=2}]x>0".asSequent
  }

  it should "retain single context formula" in withQE { _ =>
    proveBy("A>0, x=4 ==> [{x'=1&x>0}]x>0".asSequent, dW(1)).
      subgoals.loneElement shouldBe "x>0 & A>0 ==> x>0".asSequent
    proveBy("A>0, x=4 ==> [{x'=1&x>0}]x>0".asSequent, DifferentialTactics.diffWeakenPlus(1)).
      subgoals.loneElement shouldBe "A>0, x_0=4, x>0 ==> x>0".asSequent
  }

  it should "retain context" in withQE { _ =>
    proveBy("A>0&A>1, B=1, C=2&D=3, x=4 ==> [{x'=1&x>0}]x>0".asSequent, dW(1)).
      subgoals.loneElement shouldBe "x>0 & A>0 & A>1 & B=1 & C=2 & D=3 ==> x>0".asSequent
    proveBy("A>0&A>1, B=1, C=2&D=3, x=4 ==> [{x'=1&x>0}]x>0".asSequent, DifferentialTactics.diffWeakenPlus(1)).
      subgoals.loneElement shouldBe "A>0&A>1, B=1, C=2&D=3, x_0=4, x>0 ==> x>0".asSequent
  }

  it should "retain negated context" in withQE { _ =>
    proveBy("A>0&A>1, C=2&D=3, x=4 ==> [{x'=1&x>0}]x>0, !B=1".asSequent, dW(1)).
      subgoals.loneElement shouldBe "x>0 & A>0 & A>1 & C=2 & D=3 & !!B=1 ==> x>0".asSequent
    proveBy("A>0&A>1, C=2&D=3 ==> [{x'=1&x>0}]x>0, !B=1, !x=4".asSequent, DifferentialTactics.diffWeakenPlus(1)).
      subgoals.loneElement shouldBe "A>0&A>1, C=2&D=3, x>0 ==> !x_0=4, !B=1, x>0".asSequent
  }

  it should "keep initial conditions" in withQE { _ =>
    proveBy(("dx_0^2+dy_0^2=1&x^2+y^2>0, dx_0=dx, dy_0=dy, old=dy*x-(dx-1)*y " +
      " ==> [{x'=dx-1,y'=dy,dx'=0,dy'=0 & dx=dx_0&dy=dy_0&dy*x-(dx-1)*y=old}](dx^2+dy^2=1 & x^2+y^2>0)").asSequent, dW(1)).
      subgoals.loneElement shouldBe "(dx=dx_0&dy=dy_0&dy*x-(dx-1)*y=old)&dx_0^2+dy_0^2=1 ==> dx^2+dy^2=1&x^2+y^2>0".asSequent
    proveBy(("dx_0^2+dy_0^2=1&x^2+y^2>0, dx_0=dx, dy_0=dy, old=dy*x-(dx-1)*y " +
      " ==> [{x'=dx-1,y'=dy,dx'=0,dy'=0 & dx=dx_0&dy=dy_0&dy*x-(dx-1)*y=old}](dx^2+dy^2=1 & x^2+y^2>0)").asSequent,
      DifferentialTactics.diffWeakenPlus(1)).
      subgoals.loneElement shouldBe ("dx_0^2+dy_0^2=1&x_0^2+y_0^2>0, old=dy_0*x_0-(dx_0-1)*y_0, dx=dx_0&dy=dy_0&dy*x-(dx-1)*y=old " +
      " ==> dx^2+dy^2=1&x^2+y^2>0").asSequent
  }

  it should "support box assumptions" in withQE { _ =>
    proveBy(
      """x_0<=m, A()>=0, b()>0, true, t=0,
        |[{x'=v,v'=A(),t'=1&v>=0&t<=ep()}][{x'=v,v'=-b()&true}]x<=m,
        |t_1=0, v_0>=0&t_1<=ep(), time_=0, t_1=t_0, v_0=v, x_0=x
        |==>
        |[{x'=v,v'=A(),t_0'=1,time_'=1&(v>=0&t_0<=ep())&time_>=0&t_0=time_+t_1&v=A()*time_+v_0&x=1/2*A()*time_^2+time_*v_0+x_0}]x<=m""".stripMargin.asSequent,
      DifferentialTactics.diffWeakenPlus(1)).subgoals.loneElement shouldBe
      """x_0<=m, A()>=0, b()>0, true, t=0, t_1=0, v_0>=0&t_1<=ep(), time__0=0,
        |(v>=0&t_0<=ep())&time_>=0&t_0=time_+t_1&v=A()*time_+v_0&x=1/2*A()*time_^2+time_*v_0+x_0
        |==>
        |x<=m""".stripMargin.asSequent
  }

  it should "work if not sole formula in succedent" in withQE { _ =>
    proveBy("A>0&A>1, B=1, C=2&D=3, x=4 ==> Blah=1, [{x'=1&x>2}]x>0, Blub=3".asSequent, dW(2)).subgoals.
      loneElement shouldBe "x>2 & A>0 & A>1 & B=1 & C=2 & D=3 & !Blah=1 & !Blub=3 ==> x>0".asSequent
    proveBy("A>0&A>1, B=1, C=2&D=3, x=4 ==> Blah=1, [{x'=1&x>2}]x>0, Blub=3".asSequent, DifferentialTactics.diffWeakenPlus(2)).subgoals.
      loneElement shouldBe "A>0&A>1, B=1, C=2&D=3, x_0=4, x>2 ==> Blub=3, Blah=1, x>0".asSequent
  }

  it should "DW in context" in withQE { _ =>
    proveBy("==> [x:=2;][{x'=-3&x>=1}]x>=0".asSequent, dW(1, 1::Nil)).subgoals.
      loneElement shouldBe "==> [x:=2;]\\forall x (x>=1 -> x>=0)".asSequent
    proveBy("==> [x:=2;][{x'=-3&x>=1}]x>=0".asSequent, DifferentialTactics.diffWeakenPlus(1, 1::Nil)).subgoals.
      loneElement shouldBe "==> [x:=2;]\\forall x (x>=1 -> x>=0)".asSequent
  }

  "Differential effect" should "introduce a differential assignment" in withTactics {
    val result = proveBy("[{x'=5 & x>2}]x>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5 & x>2}][x':=5;]x>0".asSequent
  }

  it should "introduce differential assignments exhaustively" in withTactics {
    val result = proveBy("[{x'=5, y'=x}]x>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5, y'=x}][y':=x;][x':=5;]x>0".asSequent
  }

  it should "introduce differential assignments whatever the names (manual useAt)" in withTactics {
    val result = proveBy("[{z'=5, y'=z}]z>0".asFormula, useAt(Ax.DEs)(1))
    result.subgoals.loneElement shouldBe "==> [{y'=z,z'=5}][z':=5;]z>0".asSequent
  }

  it should "introduce differential assignments in long cases whatever the names (manual useAt)" in withTactics {
    val result = proveBy("[{z'=5, y'=z, u'=v}]z>0".asFormula, useAt(Ax.DEs)(1))
    result.subgoals.loneElement shouldBe "==> [{y'=z,u'=v,z'=5}][z':=5;]z>0".asSequent
  }

  it should "introduce differential assignments exhaustively whatever the names" in withTactics {
    val result = proveBy("[{z'=5, y'=3}]z>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{z'=5, y'=3}][y':=3;][z':=5;]z>0".asSequent
  }

  it should "introduce differential assignments exhaustively for x" in withTactics {
    val result = proveBy("[{x'=5, y'=3}]x>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5, y'=3}][y':=3;][x':=5;]x>0".asSequent
  }

  it should "introduce differential assignments exhaustively whatever the names even mutually recursive" in withTactics {
    val result = proveBy("[{z'=5, y'=z}]z>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{z'=5, y'=z}][y':=z;][z':=5;]z>0".asSequent
  }

  it should "introduce differential assignments exhaustively despite evolution domain" in withTactics {
    val result = proveBy("[{x'=5, y'=x & x>2}]x>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5, y'=x & x>2}][y':=x;][x':=5;]x>0".asSequent
  }

  it should "introduce a differential assignment when the postcondition is primed" in withTactics {
    val result = proveBy("[{x'=5 & x>2}](x>0)'".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5 & x>2}][x':=5;](x>0)'".asSequent
  }

  it should "introduce differential assignments when the postcondition is primed" in withTactics {
    val result = proveBy("[{x'=5, y'=2 & x>2}](x>0)'".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5, y'=2 & x>2}][y':=2;][x':=5;](x>0)'".asSequent
  }

  it should "introduce a differential assignment in context" in withTactics {
    val result = proveBy("[x:=0;][{x'=5 & x>2}]x>0".asFormula, DE(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=0;][{x'=5 & x>2}][x':=5;]x>0".asSequent
  }

  it should "alpha rename if necessary" in withTactics {
    val result = proveBy("[{y'=5 & y>2}]y>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{y'=5 & y>2}][y':=5;]y>0".asSequent
  }

  it should "alpha rename with remaining ODEs mentioning original x from axiom" in withTactics {
    val result = proveBy("[{y'=5,x'=2 & y>2 & x>0}]y>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{y'=5, x'=2 & y>2 & x>0}][x':=2;][y':=5;]y>0".asSequent
  }

  "Dassignb" should "assign isolated single variable" in withTactics {
    val result = proveBy("[x':=v;]x'>=0".asFormula, Dassignb(1))
    result.subgoals.loneElement shouldBe "==> v>=0".asSequent
  }

  it should "assign isolated single const" in withTactics {
    val result = proveBy("[u':=b();]u'>=0".asFormula, Dassignb(1))
    result.subgoals.loneElement shouldBe "==> b()>=0".asSequent
  }
  it should "assign isolated single const 2" in withTactics {
    val result = proveBy("[x':=v();]x'>=0".asFormula, Dassignb(1))
    result.subgoals.loneElement shouldBe "==> v()>=0".asSequent
  }

  it should "assign single const" in withTactics {
    val result = proveBy("[{x'=v()}][x':=v();]x'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v()}]v()>=0".asSequent
  }
  it should "assign single variable" in withTactics {
    val result = proveBy("[{x'=v}][x':=v;]x'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v}]v>=0".asSequent
  }

  it should "prove single variable" in withQE { _ =>
    proveBy("v>=0 -> [{x'=v}][x':=v;]x'>=0".asFormula, Dassignb(1, 1::1::Nil) & implyR(1) & abstractionb(1) & QE) shouldBe 'proved
  }

  it should "prove single const" in withQE { _ =>
    proveBy("v()>=0 -> [{x'=v()}][x':=v();]x'>=0".asFormula, Dassignb(1, 1::1::Nil) & implyR(1) & abstractionb(1) & QE) shouldBe 'proved
  }

  it should "assign flat variable" in withTactics {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::1::Nil) & Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a&true}]a>=0".asSequent
  }

  it should "assign flat const" in withTactics {
    val result = proveBy("[{x'=v,v'=a()}][v':=a();][x':=v;]v'>=0".asFormula, Dassignb(1, 1::1::Nil) & Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a()&true}]a()>=0".asSequent
  }

  it should "assign nested variabe" in withTactics {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a&true}][x':=v;]a>=0".asSequent
  }

  it should "assign nested variable" in withTactics {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a&true}][x':=v;]a>=0".asSequent
  }

  it should "assign nested const" in withTactics {
    val result = proveBy("[{x'=v,v'=a()}][v':=a();][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a()&true}][x':=v;]a()>=0".asSequent
  }

  it should "assign nested separate variable" in withTactics {
    val result = proveBy("[{x'=v,y'=a}][y':=a;][x':=v;]y'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,y'=a&true}][x':=v;]a>=0".asSequent
  }

  it should "assign nested separate const" in withTactics {
    val result = proveBy("[{x'=v,y'=a()}][y':=a();][x':=v;]y'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,y'=a()&true}][x':=v;]a()>=0".asSequent
  }

  "diffInd" should "auto-prove x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withQE { _ =>
    proveBy("x>=5 -> [{x'=2}]x>=5".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }

  it should "step into a constified ODE" taggedAs KeYmaeraXTestTags.SummaryTest in withQE { _ =>
    proveByS("x>=a & a>=0 ==> [{x'=a}]x>=a".asSequent, dI(auto='diffInd)(1), _.value should contain theSameElementsAs List(
      BelleLabels.dIInit, BelleLabels.dIStep
    ), "a()~>a".asDeclaration).subgoals should contain theSameElementsInOrderAs
      "x>=a()&a()>=0, true ==> x>=a()".asSequent ::
      "x>=a()&a()>=0, true ==> [x':=a();]x'>=0".asSequent :: Nil
  }

  it should "auto-prove x>=5 -> [{x'=2}]!x<5" taggedAs KeYmaeraXTestTags.SummaryTest in withQE { _ =>
    proveBy("x>=5 -> [{x'=2}]!x<5".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
    proveBy("x>=5 -> [{x'=2}](!x<5 | !x<4)".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
    proveBy("x>=5 -> [{x'=2}](!(x<5 & (x<2 & !x>3)) | !x<4)".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }

  it should "disregard other modalities when auto-proving x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withQE { _ =>
    proveBy("x>=5, [y:=3;]y<=3 ==> [{x'=2}]x>=5".asSequent, dI()(1)) shouldBe 'proved
  }

  it should "behave as DI rule on x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withQE { _ =>
    val result = proveBy("x>=5 -> [{x'=2}]x>=5".asFormula, implyR(1) & dI('none)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>=5, true ==> x>=5".asSequent
    result.subgoals.last shouldBe "x>=5, true ==> [{x'=2}](x>=5)'".asSequent
  }

  it should "behave as diffInd rule on x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withQE { _ =>
    val result = proveBy("x>=5 -> [{x'=2}]x>=5".asFormula, implyR(1) & dI('diffInd)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>=5, true ==> x>=5".asSequent
    result.subgoals.last shouldBe "x>=5, true ==> [x':=2;]x'>=0".asSequent
  }

  it should "auto-prove x>=5 -> [{x'=2&x<=10}](5<=x)" in withQE { _ =>
    proveBy("x>=5 -> [{x'=2&x<=10}](5<=x)".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }

  it should "auto-prove x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in withQE { _ =>
    proveBy("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }

  it should "behave as DI on x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in withQE { _ =>
    val result = proveBy("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula, implyR(1) & dI('none)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x*x+y*y>=8, true ==> x*x+y*y>=8".asSequent
    result.subgoals.last shouldBe "x*x+y*y>=8, true ==> [{x'=5*y,y'=-5*x}](x*x+y*y>=8)'".asSequent
  }

  it should "behave as diffInd on x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in withQE { _ =>
    val result = proveBy("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula, implyR(1) & dI('diffInd)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x*x+y*y>=8, true ==> x*x+y*y>=8".asSequent
    result.subgoals.last shouldBe "x_0*x_0+y_0*y_0>=8, true ==> [y':=-5*x;][x':=5*y;]x'*x+x*x'+(y'*y+y*y')>=0".asSequent
  }

  it should "prove x>=5 |- [x:=x+1][{x'=2}]x>=5" in withQE { _ =>
    proveBy("x>=5 ==> [x:=x+1;][{x'=2}]x>=5".asSequent, assignb(1) & dI()(1)) shouldBe 'proved
  }

  it should "prove x>=5 |- [x:=x+1][{x'=2}]x>=5 in reverse" in withQE { _ =>
    proveBy("x>=5 ==> [x:=x+1;][{x'=2}]x>=5".asSequent,
      dI()(1, 1::Nil) &
        assignb(1) & // handle updates
        QE
    ) shouldBe 'proved
  }

  it should "x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withTactics {
    val result = proveBy("x>=5 ==> [{x'=2}]x>=5".asSequent, DifferentialTactics.diffInd('none)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>=5, true ==> x>=5".asSequent
    result.subgoals.last shouldBe "x>=5, true ==> [{x'=2}](x>=5)'".asSequent
  }

  it should "x>=5 -> [{x'=2}]x>=5 in context" taggedAs KeYmaeraXTestTags.SummaryTest in withTactics {
    val result = proveBy("x>=5 ==> [x:=x+1;][{x'=2}]x>=5".asSequent, DifferentialTactics.diffInd('none)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x>=5 ==> [x:=x+1;](true->x>=5&[{x'=2}](x>=5)')".asSequent
  }

  it should "fail constification in context if ODE consts are bound outside" taggedAs KeYmaeraXTestTags.SummaryTest in withTactics {
    proveBy("x>=5, y=2 ==> [x:=x+1;][{x'=y}]x>=y".asSequent, DifferentialTactics.diffInd('full)(1, 1::Nil)).
      subgoals.loneElement shouldBe "x>=5, y()=2 ==> [x:=x+1;](true->x>=y()&y()>=0)".asSequent
    the [BelleProofSearchControl] thrownBy proveBy("x>=5 ==> [y:=2;x:=x+1;][{x'=y}]x>=y".asSequent,
      DifferentialTactics.diffInd('full)(1, 1::Nil)) should
      have message "Unable to constify in context ReplContext{{[y:=2;x:=x+1;][{x'=y}]x>=y at .1}}, because it binds y"
  }

  it should "autoprove x>=5 -> [{x'=2}]x>=5 in context" taggedAs KeYmaeraXTestTags.SummaryTest in withTactics {
    val result = proveBy("x>=5 ==> [x:=x+1;][{x'=2}]x>=5".asSequent, DifferentialTactics.diffInd('full)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x>=5 ==> [x:=x+1;](true->x>=5&2>=0)".asSequent
  }

  it should "autoprove x>=5&y>=0 -> [{x'=y}]x>=5 in context" taggedAs KeYmaeraXTestTags.SummaryTest in withTactics {
    val result = proveBy("x>=5&y>=0 ==> [x:=x+1;][{x'=y}]x>=5".asSequent, DifferentialTactics.diffInd('full)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x>=5&y>=0 ==> [x:=x+1;](true->x>=5&y>=0)".asSequent
  }

  it should "x>=5 -> [{x'=2&x>7}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withQE { _ =>
    val result = proveBy("x>=5 ==> [{x'=2 & x>7}]x>=5".asSequent, DifferentialTactics.diffInd('diffInd)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>=5, x>7 ==> x>=5".asSequent
    result.subgoals.last shouldBe "x_0>=5, x_0>7, x>7 ==> [x':=2;]x'>=0".asSequent
  }

  it should "keep context around" in withQE { _ =>
    val result = proveBy("x>=5&A()>0 -> [{x'=A()}]x>=5".asFormula, implyR(1) & dI('diffInd)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>=5&A()>0, true ==> x>=5".asSequent
    result.subgoals.last shouldBe "x>=5&A()>0, true ==> [x':=A();]x'>=0".asSequent
  }

  it should "prove x >= 0 & y >= 0 & z >= 0 -> [{x'=y, y'=z, z'=x^2 & y >=0}]x>=0" in withQE { _ =>
    val input = """ProgramVariables.
                  |  R x.
                  |  R y.
                  |  R z.
                  |End.
                  |Problem.
                  |  x >= 0 & y >= 0 & z >= 0
                  |  ->
                  |  [{x'=y, y'=z, z'=x^2 & y >=0}]x>=0
                  |End.
                  |""".stripMargin

    proveBy(ArchiveParser.parseAsFormula(input), implyR(1) & dI('full)(1)) shouldBe 'proved
  }

  it should "prove with and without frame constraint y'=0" in withQE { _ =>
    proveBy("x=y ==> [{x'=2 & x>=0}]x>=y".asSequent, dI('full)('R)) shouldBe 'proved
    proveBy("x=y ==> [{x'=2, y'=0 & x>=0}]x>=y".asSequent, dI('full)('R)) shouldBe 'proved
  }

  it should "report when invariant not true in the beginning" in withQE { _ =>
    the [BelleThrowable] thrownBy proveBy("x<0 ==> [{x'=-x}]x>0".asSequent, dI()(1)) should
      have message "Differential invariant must hold in the beginning: expected to have proved, but got open goals"
  }

  it should "report when not an invariant" in withQE { _ =>
    the [BelleThrowable] thrownBy proveBy("x>0 ==> [{x'=-x}]x>0".asSequent, dI()(1)) should
      have message "Differential invariant must be preserved: expected to have proved, but got open goals"
  }

  it should "report when failing to derive postcondition" in withQE { _ =>
    the [BelleThrowable] thrownBy proveBy("x>0, f(x,y)>0 ==> [{x'=2}]f(x,y)>0".asSequent, dI()(1)) should
      have message """After deriving, the right-hand sides of ODEs cannot be substituted into the postcondition
                     |Provable{
                     |   -1:  x>0	Greater
                     |   -2:  f(x,y())>0	Greater
                     |   -3:  true	True$
                     |==> 1:  [{x'=2}](f(x,y())>0)'	Box
                     |  from
                     |   -1:  x>0	Greater
                     |   -2:  f(x,y())>0	Greater
                     |   -3:  true	True$
                     |==> 1:  [{x'=2}][x':=2;](f(x,y()))'>=0	Box}""".stripMargin
  }


  it should "work with quantified postconditions" in withMathematica { _ =>
    proveBy("[{x'=3}]\\exists y y<=x".asFormula, dI(auto='diffInd)(1)).subgoals should contain theSameElementsInOrderAs List(
      "true ==> \\exists y y<=x".asSequent,
      "true ==> [x':=3;]\\forall y y'<=x'".asSequent
    )
    the [BelleProofSearchControl] thrownBy proveBy("[{x'=3}]\\exists y y<=x".asFormula, dI()(1)) should
      have message "Differential invariant must be preserved: expected to have proved, but got open goals"
  }

  it should "expand special functions" in withQE { _ =>
    proveBy("[{x'=3}]abs(x)>=2".asFormula, dI(auto='diffInd)(1)).subgoals should contain theSameElementsInOrderAs List(
      "true ==> x>=0&x>=2 | x<0&-x>=2".asSequent,
      "true ==> [x':=3;]((x'>=0&x'>=0) & x'<=0&-x'>=0)".asSequent
    )
    proveBy("[{x'=3}]max(x,4)>=2".asFormula, dI(auto='diffInd)(1)).subgoals should contain theSameElementsInOrderAs List(
      "true ==> x>=4&x>=2 | x<4&4>=2".asSequent,
      "true ==> [x':=3;]((x'>=0&x'>=0) & x'<=0&0>=0)".asSequent
    )
    proveBy("[{x'=3}]min(x,4)<=6".asFormula, dI(auto='diffInd)(1)).subgoals should contain theSameElementsInOrderAs List(
      "true ==> x<=4&x<=6 | x>4&4<=6".asSequent,
      "true ==> [x':=3;]((x'<=0&x'<=0) & x'>=0&0<=0)".asSequent
    )
  }

  it should "FEATURE_REQUEST: expand special functions and constify their abbreviation if possible" taggedAs TodoTest in withQE { _ =>
    //@todo needs expand outside DConstify(...) with intermediate result between expand and DConstify stored in DB
    proveBy("[{x'=3}]abs(f())>=2".asFormula, dI(auto='diffInd)(1)).subgoals should contain theSameElementsInOrderAs List(
      "f()>=0&abs_0()=f() | f()<0&abs_0()=-f(), true ==> abs_0()>=2".asSequent,
      "f()>=0&abs_0()=f() | f()<0&abs_0()=-f(), true ==> [x':=3;]0>=0".asSequent
    )
  }

  it should "work when not sole formula in succedent" in withQE { _ =>
    proveBy("x>=0 ==> [{x'=1}]x>=0, false".asSequent, dI()(1)) shouldBe 'proved
  }

  it should "not be applicable on non-FOL postcondition" in withQE { _ =>
    the [TacticInapplicableFailure] thrownBy proveBy("x>=0, y>=1 ==> [{x'=2}][{x'=5&y>=2} ++ y:=y+1;](x>=0 & y>=2)".asSequent, dI()(1)) should
      have message "diffInd only applicable to FOL postconditions, but got [{x'=5&y>=2}++y:=y+1;](x>=0&y>=2)"
  }

  it should "leave uninterpreted function symbols untouched" in withMathematica { _ =>
    proveBy("test(x)>=0 ==> [{x'=2}]test(x)>=0".asSequent, dI(auto='diffInd)(1)).subgoals should
      contain theSameElementsInOrderAs List(
      "test(x)>=0, true ==> test(x)>=0".asSequent,
      "test(x_0)>=0, true ==> [x':=2;](test(x))'>=0".asSequent
    )
  }

  it should "expand definitions" in withMathematica { _ =>
    val entry = ArchiveParser.parse(
      """ArchiveEntry "DI"
        |  Definitions Bool unitCircle(Real x, Real y) <-> x^2+y^2=1; End.
        |  ProgramVariables Real x, y; End.
        |  Problem unitCircle(x,y) -> [{x'=y, y'=-x}]unitCircle(x,y) End.
        |End.""".stripMargin).head
    proveByS(entry.sequent, implyR(1) & dI(auto='full)(1), entry.defs) shouldBe 'proved
  }

  it should "work as dIRule in existential context" in withMathematica { _ =>
    proveBy("x>0 ==> \\exists y [{x'=-x,y'=1/2*y}]x*y^2=1".asSequent, dI(auto='diffInd)(1, 0::Nil)).subgoals.
      loneElement shouldBe "x>0 ==> \\exists y (true->x*y^2=1&\\forall x \\forall y [y':=1/2*y;][x':=-x;]x'*y^2+x*(2*y^(2-1)*y')=0)".asSequent
  }

  "odeInvariant" should "prove STTT Example 9b invariant" in withQE { _ =>
    val seq = "Kp()=2, Kd()=3, v>=0, xm<=x, xr=(xm+S())/2, 5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2, true ==> [{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0&xm<=x}]5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2".asSequent
    proveBy(seq, DifferentialTactics.diffInd()(1)) shouldBe 'proved
    proveBy(seq, DifferentialTactics.odeInvariant(tryHard = false)(1)) shouldBe 'proved
    proveBy(seq, DifferentialTactics.odeInvariant(tryHard = true)(1)) shouldBe 'proved
  }

  "Derive" should "derive quantifiers" in withTactics {
    proveBy("(\\exists x x>=0)'".asFormula, derive(1)).subgoals.loneElement shouldBe "==> \\forall x x'>=0".asSequent
  }

  it should "derive implications" in withTactics {
    proveBy("(a=0->b=1)'".asFormula, derive(1)).subgoals.loneElement shouldBe "==> a'=0 & b'=0".asSequent
    proveBy("(a=0->(b=1->c=2))'".asFormula, derive(1)).subgoals.loneElement shouldBe "==> a'=0 & b'=0 & c'=0".asSequent
    proveBy("((a=0->b=1)->c=2)'".asFormula, derive(1)).subgoals.loneElement shouldBe "==> (a'=0 & b'=0) & c'=0".asSequent
  }

  "Dvariable" should "work when the Differential() occurs in a formula without []'s" in withQE { _ =>
    // Equal(Differential(Variable("x")), "1".asTerm)
    val result = proveBy("(x)'=1".asFormula, Derive.Dvar(1, 0::Nil))
    result.subgoals.loneElement shouldBe "==> x'=1".asSequent
  }

  it should "alpha rename if necessary" in withQE { _ =>
    val result = proveBy("(z)'=1".asFormula, Derive.Dvar(1, 0::Nil))
    result.subgoals.loneElement shouldBe "==> z'=1".asSequent
  }

  it should "work in context" in withQE { _ =>
    val result = proveBy("[y:=1;](z)'=1".asFormula, Derive.Dvar(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> [y:=1;]z'=1".asSequent
  }

  it should "work in a context that binds the differential symbol" in withQE { _ =>
    val result = proveBy("[z':=1;](z)'=1".asFormula, Derive.Dvar(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> [z':=1;]z'=1".asSequent
  }

  it should "work in a context that binds x" in withTactics {
    val result = proveBy("[z:=1;](z)'=1".asFormula, Derive.Dvar(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> [z:=1;]z'=1".asSequent
  }

  it should "work with other formulas around" in withTactics {
    val result = proveBy("a>0 ==> b<0, [z:=1;](z)'=1, c=0".asSequent, Derive.Dvar(2, 1::0::Nil))
    result.subgoals.loneElement shouldBe "a>0 ==> b<0, [z:=1;]z'=1, c=0".asSequent
  }

  "DC" should "cut in a simple formula" in withQE { _ =>
    val result = proveBy("[{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> [{x'=2 & true & x>0}]x>=0".asSequent
    result.subgoals(1) shouldBe "==> [{x'=2}]x>0".asSequent
  }

  it should "retain context for showing condition" in withQE { _ =>
    val result = proveBy("x>0 ==> y<0, [{x'=2}]x>=0, z=0".asSequent, DC("x>0".asFormula)(2))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>0 ==> y<0, [{x'=2 & true & x>0}]x>=0, z=0".asSequent
    result.subgoals(1) shouldBe "x>0 ==> y<0, z=0, [{x'=2}]x>0".asSequent
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ODEProduct" in withQE { _ =>
    val result = proveBy("[{x'=2, y'=3, z'=4 & y>4}]x>0".asFormula, DC("x>1".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> [{x'=2,y'=3,z'=4 & (y>4&x>1)}]x>0".asSequent
    result.subgoals(1) shouldBe "==> [{x'=2,y'=3,z'=4 & y>4}]x>1".asSequent
  }

  it should "cut formula into rightmost ODE in ODEProduct, even if constraint empty" in withQE { _ =>
    val result = proveBy("[{x'=2, y'=3}]x>0".asFormula, DC("x>1".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> [{x'=2,y'=3 & (true&x>1)}]x>0".asSequent
    result.subgoals(1) shouldBe "==> [{x'=2, y'=3}]x>1".asSequent
  }

  it should "preserve existing evolution domain constraint" in withQE { _ =>
    val result = proveBy("[{x'=2 & x>=0 | y<z}]x>=0".asFormula, DC("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> [{x'=2 & (x>=0 | y<z) & x>0}]x>=0".asSequent
    result.subgoals(1) shouldBe "==> [{x'=2 & x>=0 | y<z}]x>0".asSequent
  }

  it should "work in context" in withQE { _ =>
    val result = proveBy("[x:=3;][{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> [x:=3;][{x'=2 & true & x>0}]x>=0".asSequent
    result.subgoals.last shouldBe "==> [x:=3;][{x'=2}]x>0".asSequent
  }

  it should "work in context 2" in withQE { _ =>
    val result = proveBy("[z:=1;][y:=2;][x:=3;][{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1, 1::1::1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> [z:=1;][y:=2;][x:=3;][{x'=2 & true & x>0}]x>=0".asSequent
    result.subgoals.last shouldBe "==> [z:=1;][y:=2;][x:=3;][{x'=2}]x>0".asSequent
  }

  it should "work in context 3" in withQE { _ =>
    val result = proveBy("a>1 -> [z:=1;][y:=2;][x:=3;][{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1, 1::1::1::1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> a>1 -> [z:=1;][y:=2;][x:=3;][{x'=2 & true & x>0}]x>=0".asSequent
    result.subgoals.last shouldBe "==> a>1 -> [z:=1;][y:=2;][x:=3;][{x'=2}]x>0".asSequent
  }

  it should "work in context 4" in withQE { _ =>
    val result = proveBy("a>1 -> b=2|([z:=1;][y:=2;][x:=3;][{x'=2}]x>=0 | c<3)".asFormula, DC("x>0".asFormula)(1, 1::1::0::1::1::1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> a>1 -> b=2|([z:=1;][y:=2;][x:=3;][{x'=2 & true & x>0}]x>=0 | c<3)".asSequent
    result.subgoals.last shouldBe "==> a>1 -> b=2|([z:=1;][y:=2;][x:=3;][{x'=2}]x>0 | c<3)".asSequent
  }

  it should "work in context 5" in withQE { _ =>
    val result = proveBy("a>1 & [{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> a>1  & [{x'=2 & true & x>0}]x>=0".asSequent
    result.subgoals.last shouldBe "==> a>1 & [{x'=2}]x>0".asSequent
  }

  it should "work in context 6" in withQE { _ =>
    val result = proveBy("a>1 -> b=2 & (c<3|[z:=1;][y:=2;][x:=3;][{x'=2}]x>=0) & d=4".asFormula,
      DC("x>0".asFormula)(1, 1::1::0::1::1::1::1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> a>1 -> b=2 & (c<3|[z:=1;][y:=2;][x:=3;][{x'=2 & true & x>0}]x>=0) & d=4".asSequent
    result.subgoals.last shouldBe "==> a>1 -> b=2 & (c<3|[z:=1;][y:=2;][x:=3;][{x'=2}]x>0) & d=4".asSequent
  }

  "diffCut" should "cut in a simple formula" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2}]x>=0".asSequent, dC("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>0 ==> [{x'=2 & true & x>0}]x>=0".asSequent
    result.subgoals(1) shouldBe "x>0 ==> [{x'=2}]x>0".asSequent
  }

  it should "cut in a simple formula in the antecedent" in withQE { _ =>
    val result = proveBy("x>0, [{x'=2}]x>=0 ==> ".asSequent, dC("x>0".asFormula)(-2))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>0, [{x'=2 & true & x>0}]x>=0 ==> ".asSequent
    result.subgoals(1) shouldBe "x>0 ==> [{x'=2}]x>0".asSequent
  }

  it should "cut in a simple formula in context" in withQE { _ =>
    val result = proveBy("x>0 -> [{x'=2}]x>=0".asFormula, dC("x>0".asFormula)(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> x>0 -> [{x'=2 & true & x>0}]x>=0".asSequent
    result.subgoals(1) shouldBe "==> x>0 -> [{x'=2}]x>0".asSequent
  }

  it should "retain context for showing condition" in withQE { _ =>
    val result = proveBy("x>0 ==> y<0, [{x'=2}]x>=0, z=0".asSequent, dC("x>0".asFormula)(2))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>0 ==> y<0, [{x'=2 & true & x>0}]x>=0, z=0".asSequent
    result.subgoals(1) shouldBe "x>0 ==> y<0, z=0, [{x'=2}]x>0".asSequent
  }

  it should "not branch formulas in context" in withQE { _ =>
    val result = proveBy("x>0->x>0 ==> y<0&z=1, [{x'=2}]x>=0, z=0".asSequent, dC("x>0".asFormula)(2))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>0->x>0 ==> y<0&z=1, [{x'=2 & true & x>0}]x>=0, z=0".asSequent
    result.subgoals(1) shouldBe "x>0->x>0 ==> y<0&z=1, z=0, [{x'=2}]x>0".asSequent
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ODEProduct" in withQE { _ =>
    val result = proveBy("x>1 ==> [{x'=2, y'=3, z'=4 & y>4}]x>0".asSequent, dC("x>1".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>1 ==> [{x'=2,y'=3,z'=4 & (y>4&x>1)}]x>0".asSequent
    result.subgoals(1) shouldBe "x>1 ==> [{x'=2,y'=3,z'=4 & y>4}]x>1".asSequent
  }
  it should "cut formula into rightmost ODE in ODEProduct, even if constraint empty" in withQE { _ =>
    val result = proveBy("x>1 ==> [{x'=2, y'=3}]x>0".asSequent, dC("x>1".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>1 ==> [{x'=2,y'=3 & (true&x>1)}]x>0".asSequent
    result.subgoals(1) shouldBe "x>1 ==> [{x'=2,y'=3}]x>1".asSequent
  }
  it should "preserve existing evolution domain constraint" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2 & x>=0 | y<z}]x>=0".asSequent, dC("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>0 ==> [{x'=2 & (x>=0 | y<z) & x>0}]x>=0".asSequent
    result.subgoals(1) shouldBe "x>0 ==> [{x'=2 & (x>=0 | y<z)}]x>0".asSequent
  }

  it should "introduce ghosts when special function old is used" in withQE { _ =>
    val result = proveBy("[{x'=2 & x>=0 | y<z}]x>=0".asFormula, dC("x>=old(x)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x_0=x ==> [{x'=2 & (x>=0 | y<z) & x>=x_0}]x>=0".asSequent
    result.subgoals(1) shouldBe "x_0=x ==> [{x'=2 & (x>=0 | y<z)}]x>=x_0".asSequent
  }

  it should "auto-generate names for term-ghosts when special function old is used" in withQE { _ =>
    val result = proveBy("[{x'=2 & x>=0 | y<z}]x>=0".asFormula, dC("x>=old(x^2+4)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "old=x^2+4 ==> [{x'=2 & (x>=0 | y<z) & x>=old}]x>=0".asSequent
    result.subgoals(1) shouldBe "old=x^2+4 ==> [{x'=2 & (x>=0 | y<z)}]x>=old".asSequent
  }

  it should "auto-generate multiple names for term-ghosts when special function old is used" in withQE { _ =>
    val result = proveBy("[{x'=2 & x>=0 | y<z}]x>=0".asFormula, dC("x>=old(x^2+4)+old(y*z)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "old=x^2+4, old_0=y*z ==> [{x'=2 & (x>=0 | y<z) & x>=old+old_0}]x>=0".asSequent
    result.subgoals(1) shouldBe "old=x^2+4, old_0=y*z ==> [{x'=2 & (x>=0 | y<z)}]x>=old+old_0".asSequent
  }

  it should "auto-generate multiple names for term-ghosts when special function old is used over consecutive cuts" in withQE { _ =>
    val result = proveBy("[{x'=2 & x>=0 | y<z}]x>=0".asFormula,
      dC("x>=old(x^2+4)+old(y*z)".asFormula)(1) & Idioms.<(dC("x>old(2+4)".asFormula)(1), nil))
    result.subgoals should have size 3
    result.subgoals.head shouldBe "old=x^2+4, old_0=y*z, old_1=2+4 ==> [{x'=2 & ((x>=0 | y<z) & x>=old+old_0) & x>old_1}]x>=0".asSequent
    result.subgoals(1) shouldBe "old=x^2+4, old_0=y*z ==> [{x'=2 & (x>=0 | y<z)}]x>=old+old_0".asSequent
    result.subgoals(2) shouldBe "old=x^2+4, old_0=y*z, old_1=2+4 ==> [{x'=2 & (x>=0 | y<z) & x>=old+old_0}]x>old_1".asSequent
  }

  it should "auto-generate and re-use names" in withQE { _ =>
    val result = proveBy("[{x'=2 & x>=0 | y<z}]x>=0".asFormula,
      dC("x>=old(x^2+4)+old(y*z)+old(x^2+4)".asFormula)(1) & Idioms.<(dC("x>old(x^2+4)".asFormula)(1), nil))
    result.subgoals should have size 3
    result.subgoals.head shouldBe "old=x^2+4, old_0=y*z ==> [{x'=2 & ((x>=0 | y<z) & x>=old+old_0+old) & x>old}]x>=0".asSequent
    result.subgoals(1) shouldBe "old=x^2+4, old_0=y*z ==> [{x'=2 & (x>=0 | y<z)}]x>=old+old_0+old".asSequent
    result.subgoals(2) shouldBe "old=x^2+4, old_0=y*z ==> [{x'=2 & (x>=0 | y<z) & x>=old+old_0+old}]x>old".asSequent
  }

  it should "already rewrite existing conditions and introduce ghosts when special function old is used" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2}]x>=0".asSequent, dC("x>=old(x)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x_0>0, x_0=x ==> [{x'=2 & true & x>=x_0}]x>=0".asSequent
    result.subgoals(1) shouldBe "x_0>0, x_0=x ==> [{x'=2}]x>=x_0".asSequent
  }

  it should "cut in single formula with multiple old variables" in withQE { _ =>
    val result = proveBy("dx^2+dy^2=1 ==> [{dx'=0,dy'=0}]dx^2+dy^2=1".asSequent,
      dC("dx=old(dx) & dy=old(dy)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "dx_0^2+dy_0^2=1, dx_0=dx, dy_0=dy ==> [{dx'=0,dy'=0&true&dx=dx_0&dy=dy_0}]dx^2+dy^2=1".asSequent
    result.subgoals(1) shouldBe "dx_0^2+dy_0^2=1, dx_0=dx, dy_0=dy ==> [{dx'=0,dy'=0}](dx=dx_0&dy=dy_0)".asSequent
  }

  it should "not duplicate ghosts with multiple occurrences of old" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=5}]x>0".asSequent,
      dC("x>=old(x)".asFormula)(1) <(dC("x>=2*old(x)-old(x)".asFormula)(1), skip))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "x_0>0, x_0=x ==> [{x'=5&(true&x>=x_0)&x>=2*x_0-x_0}]x>0".asSequent
    result.subgoals(1) shouldBe "x_0>0, x_0=x ==> [{x'=5}]x>=x_0".asSequent
    result.subgoals(2) shouldBe "x_0>0, x_0=x ==> [{x'=5&true&x>=x_0}]x>=2*x_0-x_0".asSequent
  }

  it should "auto-generate old when const() is used" in withQE { _ =>
    proveBy("x^2+y^2=1 ==> [{x'=y,y'=-w}]x^2+y^2=1".asSequent, dC("x^2+y^2=const()".asFormula)(1)).
      subgoals should contain theSameElementsAs List(
      "old=1, old=x^2+y^2 ==> [{x'=y,y'=-w&true&x^2+y^2=old}]x^2+y^2=1".asSequent,
      "old=1, old=x^2+y^2 ==> [{x'=y,y'=-w}]x^2+y^2=old".asSequent
    )
  }

  it should "work when not sole formula in succedent" in withMathematica { _ =>
    //@todo fix unstable positions in discreteGhost/assign/stutter
    proveBy("t=0  ==> x!=1, [{t'=1,x'=-x&t=0}]x=1, x!=3".asSequent, dC("(x-old(x))^2<=2*((x-old(x))*(-x))*(t-0)".asFormula)(2)).
      subgoals should contain theSameElementsInOrderAs List(
      "t=0, x_0=x ==> x_0!=1, x_0!=3, [{t'=1,x'=-x&t=0&(x-x_0)^2<=2*((x-x_0)*(-x))*(t-0)}]x=1".asSequent,
      "t=0, x_0=x ==> x_0!=1, x_0!=3, [{t'=1,x'=-x&t=0}](x-x_0)^2<=2*((x-x_0)*(-x))*(t-0)".asSequent
    )
    proveBy("==> x!=1, t=0 -> [{t'=1,x'=-x&t=0}]x=1, x!=3".asSequent, dC("(x-old(x))^2<=2*((x-old(x))*(-x))*(t-0)".asFormula)(2, 1::Nil)).
      subgoals should contain theSameElementsInOrderAs List(
      "==> x!=1, t=0 -> \\forall x_0 (x_0=x -> [{t'=1,x'=-x&t=0&(x-x_0)^2<=2*((x-x_0)*(-x))*(t-0)}]x=1), x!=3".asSequent,
      "==> x!=1, x!=3, t=0 -> \\forall x_0 (x_0=x -> [{t'=1,x'=-x&t=0}](x-x_0)^2<=2*((x-x_0)*(-x))*(t-0))".asSequent
    )
  }

  it should "cut in multiple formulas" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent, dC("v>=0".asFormula :: "x>=old(x)".asFormula :: Nil)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "v>=0, x_0>0, x_0=x ==> [{x'=v,v'=2 & (true & v>=0) & x>=x_0}]x>=0".asSequent
    result.subgoals(1) shouldBe "v>=0, x>0 ==> [{x'=v,v'=2}]v>=0".asSequent
    result.subgoals(2) shouldBe "v>=0, x_0>0, x_0=x ==> [{x'=v,v'=2 & true & v>=0}]x>=x_0".asSequent
  }

  it should "not duplicate cuts" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent,
      dC("v>=0".asFormula :: "v>=0".asFormula :: Nil)(1) <(dC("v>=0".asFormula)(1), skip))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "v>=0, x>0 ==> [{x'=v,v'=2 & true & v>=0}]x>=0".asSequent
    result.subgoals(1) shouldBe "v>=0, x>0 ==> [{x'=v,v'=2}]v>=0".asSequent
  }

  it should "not duplicate old cuts" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent,
      dC("v>=old(v)".asFormula :: "v>=old(v)".asFormula :: Nil)(1) <(dC("v>=old(v)".asFormula)(1), skip))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "v_0>=0, x>0, v_0=v ==> [{x'=v,v'=2 & true & v>=v_0}]x>=0".asSequent
    result.subgoals(1) shouldBe "v_0>=0, x>0, v_0=v ==> [{x'=v,v'=2}]v>=v_0".asSequent
  }

  it should "expand old() ghosts in context" in withQE { _ =>
    val result = proveBy("[x:=0;][{x'=1}]x>=0".asFormula, dC("x>=old(x)".asFormula)(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> [x:=0;]\\forall x_0 (x_0=x -> [{x'=1 & true & x>=x_0}]x>=0)".asSequent
  }

  it should "compute the followup position correctly" in withQE { _ =>
    val result = proveBy("y=1 ==> [x:=0;][{x'=1,y'=-1}]x>=0".asSequent, dC("x>=old(x) & y<=old(y)".asFormula)(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "y=1 ==> [x:=0;]\\forall y_0 (y_0=y -> \\forall x_0 (x_0=x -> [{x'=1,y'=-1 & true & (x>=x_0 & y<=y_0)}]x>=0))".asSequent
  }

  it should "FEATURE_REQUEST: keep positioning stable in succedent" taggedAs TodoTest in withQE { _ =>
    //@todo useAt has unstable positioning (when fixing: some tactics - e.g., ODE - may change midway from using pos to 'Rlast as a workaround)
    val result = proveBy("x=0 ==> !y!=3, [{x'=y}]x>=-1, !y<0".asSequent, dC("x>=0".asFormula)(2))
    result.subgoals(0) shouldBe "x=0 ==> !y!=3, [{x'=y & true & x>=0}]x>=-1, !y<0".asSequent
    result.subgoals(1) shouldBe "x=0 ==> !y!=3, [{x'=y}]x>=0, !y<0".asSequent
  }

  it should "keep positioning stable in antecedent" in withQE { _ =>
    val result = proveBy("y=3, [{x'=y}]x>=-1, x=0 ==> !y<0".asSequent, dC("x>=0".asFormula)(-2))
    result.subgoals(0) shouldBe "y=3, [{x'=y & true & x>=0}]x>=-1, x=0 ==> !y<0".asSequent
    result.subgoals(1) shouldBe "y=3, x=0 ==> !y<0, [{x'=y}]x>=0".asSequent
  }

  it should "not expand definitions" in withMathematica { _ =>
    val entry = ArchiveParser.parse(
      """ArchiveEntry "DI"
        |  Definitions Bool unitCircle(Real x, Real y) <-> x^2+y^2=1; End.
        |  ProgramVariables Real x, y; End.
        |  Problem unitCircle(x,y) -> [{x'=y, y'=-x}]unitCircle(x,y) End.
        |End.""".stripMargin).head
    proveByS(entry.sequent, implyR(1) & dC("unitCircle(x,y)".asFormula)(1), entry.defs).
      subgoals should contain theSameElementsAs List(
      "unitCircle(x,y) ==> [{x'=y, y'=-x & true & unitCircle(x,y)}]unitCircle(x,y)".asSequent,
      "unitCircle(x,y) ==> [{x'=y, y'=-x}]unitCircle(x,y)".asSequent
    )
  }

  "Diamond differential cut" should "cut in a simple formula" in withQE { _ =>
    val result = proveBy("x>0 ==> <{x'=2}>x>=0".asSequent, dC("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>0 ==> <{x'=2 & true & x>0}>x>=0".asSequent
    result.subgoals(1) shouldBe "x>0 ==> [{x'=2}]x>0".asSequent
  }

  it should "retain context for showing condition" in withQE { _ =>
    val result = proveBy("x>0 ==> y<0, <{x'=2}>x>=0, z=0".asSequent, dC("x>0".asFormula)(2))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>0 ==> y<0, <{x'=2 & true & x>0}>x>=0, z=0".asSequent
    result.subgoals(1) shouldBe "x>0 ==> y<0, z=0, [{x'=2}]x>0".asSequent
  }

  it should "not branch formulas in context" in withQE { _ =>
    val result = proveBy("x>0->x>0 ==> y<0&z=1, <{x'=2}>x>=0, z=0".asSequent, dC("x>0".asFormula)(2))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>0->x>0 ==> y<0&z=1, <{x'=2 & true & x>0}>x>=0, z=0".asSequent
    result.subgoals(1) shouldBe "x>0->x>0 ==> y<0&z=1, z=0, [{x'=2}]x>0".asSequent
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ODEProduct" in withQE { _ =>
    val result = proveBy("x>1 ==> <{x'=2, y'=3, z'=4 & y>4}>x>0".asSequent, dC("x>1".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>1 ==> <{x'=2,y'=3,z'=4 & (y>4&x>1)}>x>0".asSequent
    result.subgoals(1) shouldBe "x>1 ==> [{x'=2,y'=3,z'=4 & y>4}]x>1".asSequent
  }
  it should "cut formula into rightmost ODE in ODEProduct, even if constraint empty" in withQE { _ =>
    val result = proveBy("x>1 ==> <{x'=2, y'=3}>x>0".asSequent, dC("x>1".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>1 ==> <{x'=2,y'=3 & (true&x>1)}>x>0".asSequent
    result.subgoals(1) shouldBe "x>1 ==> [{x'=2,y'=3}]x>1".asSequent
  }
  it should "preserve existing evolution domain constraint" in withQE { _ =>
    val result = proveBy("x>0 ==> <{x'=2 & x>=0 | y<z}>x>=0".asSequent, dC("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>0 ==> <{x'=2 & (x>=0 | y<z) & x>0}>x>=0".asSequent
    result.subgoals(1) shouldBe "x>0 ==> [{x'=2 & (x>=0 | y<z)}]x>0".asSequent
  }

  it should "introduce ghosts when special function old is used" in withQE { _ =>
    val result = proveBy("<{x'=2 & x>=0 | y<z}>x>=0".asFormula, dC("x>=old(x)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x_0=x ==> <{x'=2 & (x>=0 | y<z) & x>=x_0}>x>=0".asSequent
    result.subgoals(1) shouldBe "x_0=x ==> [{x'=2 & (x>=0 | y<z)}]x>=x_0".asSequent
  }

  it should "auto-generate names for term-ghosts when special function old is used" in withQE { _ =>
    val result = proveBy("<{x'=2 & x>=0 | y<z}>x>=0".asFormula, dC("x>=old(x^2+4)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "old=x^2+4 ==> <{x'=2 & (x>=0 | y<z) & x>=old}>x>=0".asSequent
    result.subgoals(1) shouldBe "old=x^2+4 ==> [{x'=2 & (x>=0 | y<z)}]x>=old".asSequent
  }

  it should "already rewrite existing conditions and introduce ghosts when special function old is used" in withQE { _ =>
    val result = proveBy("x>0 ==> <{x'=2}>x>=0".asSequent, dC("x>=old(x)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x_0>0, x_0=x ==> <{x'=2 & true & x>=x_0}>x>=0".asSequent
    result.subgoals(1) shouldBe "x_0>0, x_0=x ==> [{x'=2}]x>=x_0".asSequent
  }

  it should "cut in single formula with multiple old variables" in withQE { _ =>
    val result = proveBy("dx^2+dy^2=1 ==> <{dx'=0,dy'=0}>dx^2+dy^2=1".asSequent,
      dC("dx=old(dx) & dy=old(dy)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "dx_0^2+dy_0^2=1, dx_0=dx, dy_0=dy ==> <{dx'=0,dy'=0&true&dx=dx_0&dy=dy_0}>dx^2+dy^2=1".asSequent
    result.subgoals(1) shouldBe "dx_0^2+dy_0^2=1, dx_0=dx, dy_0=dy ==> [{dx'=0,dy'=0}](dx=dx_0&dy=dy_0)".asSequent
  }

  it should "cut in multiple formulas" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> <{x'=v,v'=2}>x>=0".asSequent, dC("v>=0".asFormula :: "x>=old(x)".asFormula :: Nil)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "v>=0, x_0>0, x_0=x ==> <{x'=v,v'=2 & (true & v>=0) & x>=x_0}>x>=0".asSequent
    result.subgoals(1) shouldBe "v>=0, x>0 ==> [{x'=v,v'=2}]v>=0".asSequent
    result.subgoals(2) shouldBe "v>=0, x_0>0, x_0=x ==> [{x'=v,v'=2 & true & v>=0}]x>=x_0".asSequent
  }

  "Inverse diffCut" should "remove a simple formula" in withQE { _ =>
    val result = proveBy("==> [{x'=1 & x>=0}]true".asSequent, DifferentialTactics.inverseDiffCut(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "==> [{x'=1}]true".asSequent
    result.subgoals(1) shouldBe "==> x>=0".asSequent
  }

  it should "remove the last conjunct" in withQE { _ =>
    val result = proveBy("==> [{x'=1 & y>=0 & x>=0}]true".asSequent, DifferentialTactics.inverseDiffCut(1))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "==> [{x'=1 & y>=0}]true".asSequent
    result.subgoals(1) shouldBe "==> x>=0".asSequent
  }

  it should "keep position stable" in withQE { _ =>
    val result = proveBy("x>=0 ==> y>=0, [{x'=1 & y>=0 & x>=0}]true, z>1".asSequent, DifferentialTactics.inverseDiffCut(2))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "x>=0 ==> y>=0, [{x'=1 & y>=0}]true, z>1".asSequent
    result.subgoals(1) shouldBe "x>=0 ==> y>=0, z>1, x>=0".asSequent
  }

  it should "work in context" in withQE { _ =>
    val result = proveBy("==> [x:=1;][{x'=1 & y>=0 & x>=0}]true".asSequent, DifferentialTactics.inverseDiffCut(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "==> [x:=1;][{x'=1 & y>=0}]true".asSequent
    result.subgoals(1) shouldBe "==> [x:=1;]x>=0".asSequent
  }

  "diffRefine" should "refine at succedent positions" in withQE { _ =>
    val result = proveBy("x>=0 ==> <{x'=v,v'=2}>x>=0, [{x'=x+y,y'=2}]y>=0".asSequent,
      dR("x<=5".asFormula)(1) <(dR("y>=5".asFormula,hide=false)(2), skip)
    )
    result.subgoals should have size 3
    //Subgoal after both refinements
    result.subgoals(0) shouldBe "x>=0 ==> <{x'=v,v'=2&x<=5}>x>=0, [{x'=x+y,y'=2&y>=5}]y>=0".asSequent
    //The other goal arising from refinement steps
    result.subgoals(1) shouldBe "x>=0 ==> [{x'=v,v'=2&x<=5}]true".asSequent
    result.subgoals(2) shouldBe "x>=0 ==> <{x'=v,v'=2&x<=5}>x>=0, [{x'=x+y,y'=2&true}]y>=5".asSequent
  }

  it should "refine at antecedent positions" in withQE { _ =>
    val result = proveBy("<{x'=v,v'=2}>x>=0, [{x'=x+y,y'=2}]y>=0 ==> x>=0 ".asSequent,
      dR("x<=5".asFormula)(-1) <(dR("y>=5".asFormula)(-2), skip)
    )
    result.subgoals should have size 3
    //Subgoal after both refinements
    result.subgoals(0) shouldBe "<{x'=v,v'=2&x<=5}>x>=0, [{x'=x+y,y'=2&y>=5}]y>=0 ==> x>=0".asSequent
    //The other goal arising from refinement steps
    result.subgoals(1) shouldBe "[{x'=x+y,y'=2&true}]y>=0 ==> [{x'=v,v'=2&true}]x<=5".asSequent
    result.subgoals(2) shouldBe "<{x'=v,v'=2&x<=5}>x>=0 ==> [{x'=x+y,y'=2&y>=5}]true".asSequent
  }

  "diffInvariant" should "cut in a simple formula" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2}]x>=0".asSequent, diffInvariant("x>0".asFormula)(1))
    result.subgoals.loneElement shouldBe "x>0 ==> [{x'=2 & true & x>0}]x>=0".asSequent
  }

  it should "cut in a simple formula in context" in withQE { _ =>
    val result = proveBy("x>0 -> [{x'=2}]x>=0".asFormula, diffInvariant("x>0".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> x>0 -> [{x'=2 & true & x>0}]x>=0".asSequent
  }

  it should "cut in single formulas with old" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent, diffInvariant("v>=old(v)".asFormula)(1))
    result.subgoals.loneElement shouldBe "v_0>=0, x>0, v_0=v ==> [{x'=v,v'=2 & (true & v>=v_0)}]x>=0".asSequent
  }

  it should "cut in single formula with multiple old variables" in withQE { _ =>
    val result = proveBy("dx^2+dy^2=1 ==> [{dx'=0,dy'=0}]dx^2+dy^2=1".asSequent,
      diffInvariant("dx=old(dx) & dy=old(dy)".asFormula)(1))
    result.subgoals.loneElement shouldBe "dx_0^2+dy_0^2=1, dx_0=dx, dy_0=dy ==> [{dx'=0,dy'=0&true&dx=dx_0&dy=dy_0}]dx^2+dy^2=1".asSequent
  }

  it should "cut in multiple formulas" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent, diffInvariant("v>=0".asFormula :: "x>0".asFormula :: Nil)(1))
    result.subgoals.loneElement shouldBe "v>=0, x>0 ==> [{x'=v,v'=2 & (true & v>=0) & x>0}]x>=0".asSequent
  }

  it should "cut in multiple formulas with old" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent, diffInvariant("v>=0".asFormula :: "x>=old(x)".asFormula :: Nil)(1))
    result.subgoals.loneElement shouldBe "v>=0, x_0>0, x_0=x ==> [{x'=v,v'=2 & (true & v>=0) & x>=x_0}]x>=0".asSequent
  }

  it should "cut in time as needed by diffSolve" in withQE { _ =>
    val result = proveBy("t=0 ==> [{x'=2,t'=0*t+1}]x>=0".asSequent, diffInvariant("t>=0".asFormula)(1))
    result.subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=0*t+1 & true & t>=0}]x>=0".asSequent
  }

  it should "fail if any of the formulas is not an invariant" in withQE { _ =>
    a [BelleThrowable] should be thrownBy proveBy("x>0 ==> [{x'=v,v'=2}]x>=0".asSequent,
      diffInvariant("v>=0".asFormula :: "x>=old(x)".asFormula :: Nil)(1))
  }

  it should "let us directly prove variable x+y^2*3-z = x+y^2*3-z by abbreviation" in withQE { _ =>
    proveBy("x+y^2*3-z=x+y^2*3-z".asFormula, let(FuncOf(Function("s_",None,Unit,Real),Nothing), "x+y^2*3-z".asTerm, by(Ax.equalReflexive))) shouldBe 'proved
  }

  it should "prove const [x':=5;](x+c())'>=0 directly" in withQE { _ =>
    proveBy("[x':=5;](x+c())'>=0".asFormula, derive(1,1::0::Nil) & Dassignb(1) & QE) shouldBe 'proved
  }

  it should "probably not prove variable [x':=5;](x+y)'>=0 unless derive is too powerful" in withQE { _ =>
    val result = proveBy("[x':=5;](x+y)'>=0".asFormula, derive(1,1::0::Nil) & Dassignb(1))
    result.isProved shouldBe false
    result.subgoals.loneElement shouldBe "==> 5+y'>=0".asSequent
  }

  it should "prove const [x':=5;](x+c())'>=0" in withQE { _ =>
    proveBy("[x':=5;](x+c())'>=0".asFormula,
      derive(1,1::0::Nil) & Dassignb(1) & QE) shouldBe 'proved
  }

  it should "let us prove variable [x':=5;](x+y)'>=0" in withQE { _ =>
    //@note proof waited too long. Should have gone constant before diffind
    TactixLibrary.proveBy("[x':=5;](x+y)'>=0".asFormula,
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), derive(1,1::0::Nil) & Dassignb(1) & QE)) shouldBe 'proved
  }

  it should "prove const [{x'=5}](x+c())'>=0" in withQE { _ =>
    proveBy("[{x'=5}](x+c())'>=0".asFormula,
      derive(1,1::0::Nil) & DE(1) & G(1) & Dassignb(1) & QE) shouldBe 'proved
  }

  it should "let us prove variable [{x'=5}](x+y)'>=0" in withQE { _ =>
    //@note proof waited too long. Should have gone constant before diffind
    TactixLibrary.proveBy("[{x'=5}](x+y)'>=0".asFormula,
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), derive(1,1::0::Nil) & DE(1) & G(1) & Dassignb(1) & QE)) shouldBe 'proved
  }

  it should "prove const x+c()>=0 -> [{x'=5}]x+c()>=0" in withQE { _ =>
    proveBy("x+c()>=0 -> [{x'=5}]x+c()>=0".asFormula,
      implyR(1) & dI('full)(1)) shouldBe 'proved
  }

  it should "prove const x+c()>=0 -> [{x'=5}]x+c()>=0 manual" in withQE { _ =>
    proveBy("x+c()>=0 -> [{x'=5}]x+c()>=0".asFormula,
      implyR(1) & dI('none)(1) <(close , derive(1,1::Nil) & DE(1) & G(1) & Dassignb(1) & QE)) shouldBe 'proved
  }

  it should "let us prove variable x+y>=0 -> [{x'=5}]x+y>=0 manual" in withQE { _ =>
    proveBy("x+y>=0 -> [{x'=5}]x+y>=0".asFormula, implyR(1) &
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), dI('none)(1) <(close , derive(1,1::Nil) & DE(1) & G(1) & Dassignb(1) & QE))) shouldBe 'proved
  }

  it should "let us prove variable x+y>=0 -> [{x'=5}]x+y>=0" in withQE { _ =>
    proveBy("x+y>=0 -> [{x'=5}]x+y>=0".asFormula, implyR(1) &
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), dI('full)(1))) shouldBe 'proved
  }

  it should "let us prove variable x+y+z>=0 -> [{x'=5,y'=2}]x+y+z>=0" in withQE { _ =>
    proveBy("x+y+z>=0 -> [{x'=5,y'=2}]x+y+z>=0".asFormula, implyR(1) &
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("z"), dI('full)(1))) shouldBe 'proved
  }

  it should "let us prove variable x+z>=0&y+z>=0 -> [{x'=5,y'=2}](x+z>=0&y+z>=0)" in withQE { _ =>
    proveBy("x+z>=0&y+z>=0 -> [{x'=5,y'=2}](x+z>=0&y+z>=0)".asFormula, implyR(1) &
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("z"), dI('full)(1))) shouldBe 'proved
  }

  it should "prove const a()>=0 & x>=0 & v>=0 -> [{x'=v,v'=a()}]v>=0 directly" in withQE { _ =>
    proveBy("a()>=0 & x>=0 & v>=0 -> [{x'=v,v'=a()}]v>=0".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }

  it should "let us prove variable x>=0 & v>=0 -> [{x'=v}]x>=0" in withQE { _ =>
    proveBy("x>=0 & v>=0 -> [{x'=v}]x>=0".asFormula, implyR(1) &
      let(FuncOf(Function("v",None,Unit,Real),Nothing), Variable("v"), dI('full)(1))) shouldBe 'proved
  }

  it should "let us prove variable a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0" in withQE { _ =>
    proveBy("a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0".asFormula, implyR(1) & let(FuncOf(Function("a",None,Unit,Real),Nothing), Variable("a"), dI('full)(1))) shouldBe 'proved
  }

  it should "perhaps prove variable a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0 directly if diffInd were powerful enough" in withQE { _ =>
    proveBy("a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0".asFormula, implyR(1) & dI('full)(1)) shouldBe 'proved
  }

  it should "let us prove variable a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0 despite silly names" in withQE { _ =>
    proveBy("a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0".asFormula, implyR(1) & let(FuncOf(Function("gobananas",None,Unit,Real),Nothing), Variable("a"), dI('full)(1))) shouldBe 'proved
  }

  it should "FEATURE_REQUEST: expand definitions only temporarily in dI but not in result" taggedAs TodoTest in withMathematica { _ =>
    val entry = ArchiveParser.parse(
      """ArchiveEntry "DI"
        |  Definitions Bool unitCircle(Real x, Real y) <-> x^2+y^2=1; End.
        |  ProgramVariables Real x, y; End.
        |  Problem unitCircle(x,y) -> [{x'=y, y'=-x}]unitCircle(x,y) End.
        |End.""".stripMargin).head
    //@todo want unitCircle unexpanded in result, but that requires internal delayed merging of provables
    proveByS(entry.sequent, implyR(1) & diffInvariant("unitCircle(x, y)".asFormula)(1), entry.defs).subgoals.
      loneElement shouldBe "unitCircle(x,y) ==> [{x'=y, y'=-x & unitCircle(x,y)}]unitCircle(x,y)".asSequent
  }

  private val dconstifyTests = Table(("Name", "Sequent", "Expected"),
    ("replace a with a() in v'=a",
      "==> [{v'=a}]v=v0()+a*t()",
      "==> [{v'=a()}]v=v0()+a()*t()"),
    ("not self-replace a() with a() in v'=a()",
      "==> [{v'=a()}]v=v0()+a()*t()",
      "==> [{v'=a()}]v=v0()+a()*t()"),
    ("not replace a with a() when a is not free in p",
      "==> [{v'=a}]v>0",
      "==> [{v'=a}]v>0"),
    ("replace every free occurrence of a with a() everywhere in the sequent",
      "v>=0, a=0, \\forall a a<0 ==> [{v'=a}]v=v_0()+a*t(), a>=0, [a:=2;]v>0",
      "v>=0, a()=0, \\forall a a<0 ==> [{v'=a()}]v=v_0()+a()*t(), a()>=0, [a:=2;]v>0"),
    ("replace every free occurrence of b (theSameElementsAs List(in p) with b() everywhere in the sequent",
      "v>=0, a=0, b=2, \\forall b b<0 ==> [{v'=a}](v>0 & b<0), a>=0, [a:=2;]v>0",
      "v>=0, a=0, b()=2, \\forall b b<0 ==> [{v'=a}](v>0& b()<0), a>=0, [a:=2;]v>0")
  )

  "Differential introduce constants" should "replace a with a()" in withTactics {
    def checkSequentTactic(expected: Sequent) = new SingleGoalDependentTactic("mock") {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        sequent shouldBe expected
        throw new BelleAbort("Success", "Sequent as expected, now aborting")
      }
    }

    forEvery (dconstifyTests) {
      (name, input, expectedResult) => withClue(name) {
        the [BelleAbort] thrownBy proveBy(input.asSequent, DifferentialTactics.Dconstify(
          checkSequentTactic(expectedResult.asSequent))(1)) should have message "Sequent as expected, now aborting"
      }
    }
  }

  it should "not constify bound postcondition" in withTactics {
    proveBy("x>=0, y>=1, z=2 ==> [{x'=5&y>=1}][{x'=z} ++ y:=z+1;](x>=0 & y>=1)".asSequent, DifferentialTactics.Dconstify(skip)(1)).
      subgoals.loneElement shouldBe "x>=0, y>=1, z()=2 ==> [{x'=5&y>=1}][{x'=z()}++y:=z()+1;](x>=0&y>=1)".asSequent
  }

  "DG" should "add y'=1 to [x'=2]x>0" in withTactics {
    val result = proveBy("[{x'=2}]x>0".asFormula, dG("{y'=0*y+1}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=1}]x>0".asSequent
  }

  it should "add y'=1 to [x'=2]x>0 from parsed tactic" in withTactics {
    proveBy("[{x'=2}]x>0".asFormula, BelleParser("""dG("{y'=0*y+1}", 1)""")).subgoals.
      loneElement shouldBe "==> \\exists y [{x'=2,y'=1}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, BelleParser("""dG("y'=1", 1)""")).subgoals.
      loneElement shouldBe "==> \\exists y [{x'=2,y'=1}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, BelleParser("""dG("{y'=1}", 1)""")).subgoals.
      loneElement shouldBe "==> \\exists y [{x'=2,y'=1}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, BelleParser("""dG("{y'=1&true}", 1)""")).subgoals.
      loneElement shouldBe "==> \\exists y [{x'=2,y'=1}]x>0".asSequent
  }

  it should "add z'=1 to [y'=2]y>0" in withTactics {
    val result = proveBy("[{y'=2}]y>0".asFormula, dG("{z'=0*z+1}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists z [{y'=2,z'=1}]y>0".asSequent
  }

  it should "add x'=1 to [y'=2]y>0" in withTactics {
    val result = proveBy("[{y'=2}]y>0".asFormula, dG("{x'=0*x+1}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists x [{y'=2,x'=1}]y>0".asSequent
  }

  it should "add y'=3*y+10 to [x'=2]x>0" in withTactics {
    val result = proveBy("[{x'=2}]x>0".asFormula, dG("{y'=3*y+10}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=3*y+10}]x>0".asSequent
  }

  it should "add y'=3*y+z() to [x'=2]x>0" in withTactics {
    val result = proveBy("[{x'=2}]x>0".asFormula, dG("{y'=3*y+z()}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=3*y+z()}]x>0".asSequent
  }

  it should "preserve evolution domain" in withTactics {
    val result = proveBy("[{x'=2 & x>=0}]x>0".asFormula, dG("{y'=3*y+10}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=3*y+10 & x>=0}]x>0".asSequent
  }

  it should "work with other formulas around" in withTactics {
    val result = proveBy("a>1 ==> [{x'=2 & x>=0}]x>0, b=2".asSequent, dG("{y'=3*y+10}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "a>1 ==> \\exists y [{x'=2,y'=3*y+10 & x>=0}]x>0, b=2".asSequent
  }

  it should "do basic unification" in withTactics {
    //ay+b,ay-b,-ay+b,-ay-b
    proveBy("[{x'=2}]x>0".asFormula, dG("{y'=2*y+3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "y=0 ==> [{x'=2,y'=2*y+3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{y'=2*y-3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "y=0 ==> [{x'=2,y'=2*y+-3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{y'=-2*y+3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "y=0 ==> [{x'=2,y'=-2*y+3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{y'=-2*y-z}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "y=0 ==> [{x'=2,y'=-2*y+-z}]x>0".asSequent

    //ay,-ay
    proveBy("[{x'=2}]x>0".asFormula, dG("{y'=2*y}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "y=0 ==> [{x'=2,y'=2*y+0}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{y'=-2*y}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "y=0 ==> [{x'=2,y'=-2*y+0}]x>0".asSequent

    //+b,-b
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=1}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=1}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=-1}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=-1}]x>0".asSequent

    //y+b,y-b,-y+b,-y-b
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=t+3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=1*t+3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=t-3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=1*t+-3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=-t+3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=-1*t+3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=-t-3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=-1*t+-3}]x>0".asSequent

    //division
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=t/2+3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=1/2*t+3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=t/2-3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=1/2*t+-3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=-t/2+3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=(- 1/2)*t+3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=-t/2-3}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=(- 1/2)*t+-3}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=t/2}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=1/2*t+0}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=-t/2}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=(-1/2)*t+0}]x>0".asSequent

    // supported simplifications so far
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=0*t+1}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=1}]x>0".asSequent
    proveBy("[{x'=2}]x>0".asFormula, dG("{t'=0*t}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)).
      subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=0}]x>0".asSequent

    // @todo simplify a*y+0, 1*y+b, a*y+-(b)
  }

  it should "auto-cut avoid singularities" in withMathematica { _ =>
    proveBy("x>1 ==> [{x'=x+1}]x>1".asSequent, dG("{y'=(-1/2*(x+1)/(x-1))*y}".asDifferentialProgram, Some("(x-1)*y^2=1".asFormula))(1)).
      subgoals.loneElement shouldBe "x>1 ==> \\exists y [{x'=x+1,y'=(-1)/2*(x+1)/(x-1)*y+0&true&x-1!=0}](x-1)*y^2=1".asSequent
  }

  it should "not allow non-linear ghosts (1)" in withTactics {
    a [BelleThrowable] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, dG("{y'=y*y+1}".asDifferentialProgram, None)(1))
  }

  it should "not allow non-linear ghosts (2)" in withTactics {
    a [BelleThrowable] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, dG("{y'=1*y+y}".asDifferentialProgram, None)(1))
  }

  it should "not allow ghosts that are already present in the ODE" in withTactics {
    a [BelleThrowable] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, dG("{x'=0*x+1}".asDifferentialProgram, None)(1))
  }

  it should "give useful error messages on shape mismatch" in withTactics {
    the [BelleThrowable] thrownBy proveBy("[{x'=2}]x>0".asFormula, dG("{t'=x*t*x^2}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1)) should
      have message "Ghost {t'=x*t*x^2} is not of the form y'=a*y+b or y'=a*y or y'=b or y'=a*y-b or y'=y"
  }

  it should "unify ghost shapes correctly" in withMathematica { _ =>
    proveBy("==> [{x'=v}]x>0".asSequent, dG("z'=1*v".asDifferentialProgram, None)(1)).subgoals.loneElement shouldBe
      "==> \\exists z [{x'=v, z'=1*v}]x>0".asSequent
  }

  it should "give a useful error message on invalid transformation of postcondition" in withMathematica { _ =>
    the [BelleUserCorrectableException] thrownBy proveBy("==> [{x'=v}]x>0".asSequent,
      dG("z'=v".asDifferentialProgram, Some("z>=0".asFormula))(1)) should have message
      """Formula
        |  z>=0
        |does not imply postcondition
        |  x>0
        |or necessary facts might not be preserved automatically; try to preserve with differential cuts before using dG
        |
        |Provable{
        |==> 1:  [{x'=v}]x>0	Box
        |  from
        |==> 1:  \exists z [{x'=v,z'=v}](true->z>=0)	Exists
        |  with
        |==> 1:  false	False$}""".stripMargin
  }

  it should "give a useful error message when facts cannot be preserved for postcondition transformation" in withMathematica { _ =>
    the [BelleUserCorrectableException] thrownBy proveBy("==> [b:=1;][{x'=v}]x>b".asSequent,
      dG("z'=v".asDifferentialProgram, Some("x/b>1".asFormula))(1, 1::Nil)) should have message
      """Formula
        |  x/b>1
        |does not imply postcondition
        |  x>b
        |or necessary facts might not be preserved automatically; try to preserve with differential cuts before using dG
        |
        |Provable{
        |==> 1:  [b:=1;][{x'=v}]x>b	Box
        |  from
        |==> 1:  [b:=1;]\exists z [{x'=v,z'=v}](true->x/b>1)	Box
        |  with
        |==> 1:  false	False$}""".stripMargin
  }

  it should "use facts preserved by dC when transforming postcondition" in withMathematica { _ =>
    proveBy("==> [b:=1;][{x'=v}]x>b".asSequent,
      dC("b=1".asFormula)(1, 1::Nil) <(
        dG("z'=v".asDifferentialProgram, Some("x/b>1".asFormula))(1, 1::Nil),
        skip
      )).subgoals should contain theSameElementsInOrderAs(
      "==> [b:=1;]\\exists z [{x'=v,z'=v&true&b=1}]x/b>1".asSequent ::
      "==> [b:=1;][{x'=v}]b=1".asSequent :: Nil)
  }

  "DA" should "add y'=1 to [x'=2]x>0" in withQE { _ =>
    val s = "==> [{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+1}".asDifferentialProgram, Some("y>0 & x*y>0".asFormula))(1)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=1}](y>0 & x*y>0)".asSequent
  }

  it should "work in a simple context" in withQE { _ =>
    val s = "x>0 ==> a=2 -> [{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+1}".asDifferentialProgram, Some("y>0 & x*y>0".asFormula))(1, 1::Nil)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "x>0 ==> a=2 -> \\exists y [{x'=2,y'=1}](y>0 & x*y>0)".asSequent
  }

  it should "work in a complicated context" in withQE { _ =>
    val s = "x>0 ==> a=2 -> [b:=3;]<?c=5;{c'=2}>[{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+1}".asDifferentialProgram, Some("y>0 & x*y>0".asFormula))(1, 1::1::1::Nil)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "x>0 ==> a=2 -> [b:=3;]<?c=5;{c'=2}>\\exists y [{x'=2,y'=1}](y>0 & x*y>0)".asSequent
  }

  it should "add y'=-a() to [x'=2]x>0" in withQE { _ =>
    val s = "a()>0, x>0 ==> [{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+(-a())}".asDifferentialProgram, Some("x>0 & y<0".asFormula))(1)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "a()>0, x>0 ==> \\exists y [{x'=2,y'=-a()}](x>0 & y<0)".asSequent
  }

  it should "add arbitrary shape" in withQE { _ =>
    val s = "x<0 ==> [{x'=-x}]x<0".asSequent
    val fml = Some("x*y^2=-1".asFormula)
    val expected = "x<0 ==> \\exists y [{x'=-x,y'=1/2*y+0}]x*y^2=-1".asSequent
    proveBy(s, dG("{y'=y*0.5}".asDifferentialProgram, fml)(1)).subgoals.loneElement shouldBe expected
    proveBy(s, dG("{y'=1/2*y}".asDifferentialProgram, fml)(1)).subgoals.loneElement shouldBe expected
    proveBy(s, dG("{y'=y/2}".asDifferentialProgram, fml)(1)).subgoals.loneElement shouldBe expected
    proveBy(s, dG("{y'=0.5*y}".asDifferentialProgram, fml)(1)).subgoals.loneElement shouldBe "x<0 ==> \\exists y [{x'=-x,y'=0.5*y+0}]x*y^2=-1".asSequent
    proveBy(s, dG("{y'=4*y/8}".asDifferentialProgram, fml)(1)).subgoals.loneElement shouldBe expected
    proveBy(s, dG("{y'=4*y^5/(8*y^4)}".asDifferentialProgram, fml)(1)).subgoals.loneElement shouldBe expected
  }

  it should "solve x'=x" in withMathematica { _ =>
    val s = "==> x>0 -> [{x'=x}]x>0".asSequent
    val t = prop & dG("{z'=(-1/2)*z+0}".asDifferentialProgram, Some("x*z^2=1".asFormula))(1) &
      existsR("1/x^(1/2)".asTerm)(1) & dI()(1) & QE
    proveBy(s, t) shouldBe 'proved
  }

  it should "do fancy unification for proving x>0->[{x'=-x}]x>0 positionally" in withMathematica { _ =>
    val result = proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
      dG("{y'=(1/2)*y}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) & dI()(1, 0::Nil) & QE)
    result shouldBe 'proved
  }

  it should "do fancy unification for proving x>0->[{x'=-x}]x>0" in withMathematica { _ =>
    val result = proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
      dG("{y'=(1/2)*y+0}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) & existsR("1/x^(1/2)".asTerm)(1) & dI()(1) & QE)
    result shouldBe 'proved
  }

  it should "do fancy unification for proving x>0->[{x'=x}]x>0" in withMathematica { _ =>
    val result = proveBy("x>0->[{x'=x}]x>0".asFormula, implyR(1) &
      dG("{y'=(-1/2)*y+0}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) & dI()(1, 0::Nil) & existsR("1/x^(1/2)".asTerm)(1) & QE)
    result shouldBe 'proved
  }

  it should "prove x>0->[{x'=-x+1}]x>0 by ghosts" in withMathematica { _ =>
    val result = proveBy("x>0->[{x'=-x+1}]x>0".asFormula, implyR(1) &
      dG("{y'=(1/2)*y+0}".asDifferentialProgram, Some("x*y^2>0".asFormula))(1) & dI()(1, 0::Nil) & QE)
    result shouldBe 'proved
  }

  it should "prove x>0&a<0&b>=0->[{x'=a*x+b}]x>0 by ghosts" in withMathematica { _ =>
    val result = proveBy("x>0&a<0&b>=0->[{x'=a*x+b}]x>0".asFormula, implyR(1) &
      dG("{y'=(-a/2)*y+0}".asDifferentialProgram, Some("x*y^2>0".asFormula))(1) & dI()(1, 0::Nil) & QE)
    result shouldBe 'proved
  }

  it should "prove x>0&a>0&b>=0->[{x'=a*x+b}]x>0 by ghosts" in withMathematica { _ =>
    val result = proveBy("x>0&a>0&b>=0->[{x'=a*x+b}]x>0".asFormula, implyR(1) &
      dG("{y'=(-a/2)*y+0}".asDifferentialProgram, Some("x*y^2>0".asFormula))(1) & dI()(1, 0::Nil) & QE)
    result shouldBe 'proved
  }

  "DA by DG+transform" should "add y'=1 to [x'=2]x>0" in withQE { _ =>
    val s = "==> [{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+1}".asDifferentialProgram, None)(1) & transform("y>0 & x*y>0".asFormula)(1, 0::1::Nil)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=1}](y>0 & x*y>0)".asSequent
  }

  "Inverse Differential Ghost" should "remove the left-most DE" in withQE { _ =>
    val result = proveBy("==> [{y'=1,x'=2}]p(x)".asSequent, DifferentialTactics.inverseDiffGhost(1))
    result.subgoals.loneElement shouldBe "==> [{x'=2}]p(x)".asSequent
  }

  it should "remove the left-most DE in context" in withQE { _ =>
    val result = proveBy("==> [x:=2;][{y'=1,x'=2}]p(x)".asSequent, DifferentialTactics.inverseDiffGhost(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=2;][{x'=2}]p(x)".asSequent
  }

  "diffSolve" should "find a solution" in withQE { _ =>
    val result = proveBy("x>b ==> [{x'=2,t'=1}]x>b".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>b ==> \\forall t_ (t_>=0 -> 2*t_+x>b)".asSequent
  }

  it should "disregard other modalities" in withQE { _ =>
    val result = proveBy("x>b, [y:=3;]y>=3 ==> <z:=3;>z=3, [{x'=2}]x>b".asSequent, solve(2))
    result.subgoals.loneElement shouldBe "x>b, [y:=3;]y>=3 ==> <z:=3;>z=3, \\forall t_ (t_>=0 -> 2*t_+x>b)".asSequent
  }

  it should "add time" in withQE { _ =>
    val result = proveBy("x>b ==> [{x'=2}]x>b".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>b ==> \\forall t_ (t_>=0 -> 2*t_+x>b)".asSequent
  }

  it should "work if not sole formula in succedent" in withQE { _ =>
    val result = proveBy("x>b ==> a=5, [{x'=2}]x>b, c>2".asSequent, solve(2))
    result.subgoals.loneElement shouldBe "x>b ==> a=5, \\forall t_ (t_>=0 -> 2*t_+x>b), c>2".asSequent
  }

  it should "add time if not present and ask Mathematica if no solution provided as part of master" in withQE { _ =>
    proveBy("x>b ==> [{x'=2}]x>b".asSequent, master()) shouldBe 'proved
  }

  it should "diffSolve add time if not present and ask Mathematica" in withQE { _ =>
    proveBy("x>b ==> [{x'=2}]x>b".asSequent, solve(1) & QE) shouldBe 'proved
  }

  it should "work with box property" in withQE { _ =>
    val result = proveBy("[{x'=2}][y:=x;]y>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> [y:=2*(0+1*t_-0)+x;]y>0)".asSequent
  }

  it should "work with maybe bound" in withQE { _ =>
    val result = proveBy("[{x'=2}][{x:=x+3;}* ++ y:=x;]y>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> \\forall x (x=2*t_+x_1 -> [{x:=x+3;}* ++ y:=x;]y>0))".asSequent
  }

  it should "work with sequence of ODEs" in withQE { _ =>
    val result = proveBy("[{x'=2}][{x'=3}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> \\forall x (x=2*t_+x_1 -> [{x'=3}]x>0))".asSequent
  }

  it should "find solution for x'=v" in withQE { _ =>
    val result = proveBy("x>0 & v>=0 ==> [{x'=v}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 & v>=0 ==> \\forall t_ (t_>=0 -> v*t_+x>0)".asSequent
  }

  it should "find solution for x'=v with evolution domain constraint" in withQE { _ =>
    val result = proveBy("x>0 & v>=0 ==> [{x'=v&x>=0}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 & v>=0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_&s_<=t_ -> v*s_+x>=0) -> v*t_+x>0)".asSequent
  }

  it should "find solution for x'=v, v'=a" in withQE { _ =>
    val result = proveBy("x>0 & v>=0 & a>0 ==> [{x'=v,v'=a}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 & v>=0 & a>0 ==> \\forall t_ (t_>=0 -> a*(t_^2/2)+v*t_+x>0)".asSequent
  }

  it should "solve ODE with const factor" in withQE { _ =>
    val result = proveBy("[{x'=c*v}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> c*v*t_+x>0)".asSequent
  }

  it should "solve ODE system with const factor" in withQE { _ =>
    val result = proveBy("[{x'=c*v,v'=a}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> c*(a*(t_^2/2)+v*t_)+x>0)".asSequent
  }

  it should "solve ODE system with number factor" in withQE { _ =>
    val result = proveBy("[{x'=3*v,v'=a}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> 3*(a*(t_^2/2)+v*t_)+x>0)".asSequent
  }

  it should "solve straight 2D driving" in withQE { _ =>
    val result = proveBy("[{v'=a,x'=v*dx,y'=v*dy}]x^2+y^2<=r^2".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> (dx*(a*(t_^2/2)+v*t_)+x)^2+(dy*(a*(t_^2/2)+v*t_)+y)^2<=r^2)".asSequent
  }

  it should "solve straight 2D driving when only x is mentioned in p" in withQE { _ =>
    val result = proveBy("[{v'=a,x'=v*dx,y'=v*dy}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> dx*(a*(t_^2/2)+v*t_)+x>0)".asSequent
  }

  it should "solve more complicated constants" in withQE { _ =>
    val result = proveBy("[{v'=a+c,t'=1,x'=(v+5)*dx^2,y'=v*(3-dy)*c}]x^2+y^2<=r^2".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> (dx^2*((a+c)*(t_^2/2)+v*t_+5*t_)+x)^2+(c*((3-dy)*((a+c)*(t_^2/2)+v*t_))+y)^2<=r^2)".asSequent
  }

  it should "solve more complicated constants with explicit c'=0" in withQE { _ =>
    //@note dx'=0 omitted intentionally to test for mixed explicit/non-explicit constants
    val result = proveBy("[{v'=a+c,t'=1,c'=0,x'=(v+5)*dx^2,y'=v*(3-dy)*c,dy'=0}]x^2+y^2<=r^2".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> (dx^2*((a+c)*(t_^2/2)+v*t_+5*t_)+x)^2+(c*((3-dy)*((a+c)*(t_^2/2)+v*t_))+y)^2<=r^2)".asSequent
  }

  it should "work when ODE is not sole formula in succedent" in withQE { _ =>
    val result = proveBy("x>0 & v>=0 & a>0 ==> y=1, [{x'=v,v'=a}]x>0, z=3".asSequent, solve(2))
    result.subgoals.loneElement shouldBe "x>0 & v>=0 & a>0 ==> y=1, \\forall t_ (t_>=0 -> a*(t_^2/2)+v*t_+x>0), z=3".asSequent
  }

  it should "work when safety property is abstract" in withQE { _ =>
    val result = proveBy("J(x,v) ==> [{x'=v,v'=a}]J(x,v)".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "J(x,v) ==> \\forall t_ (t_>=0->J((a*(t_^2/2)+v*t_+x,a*t_+v)))".asSequent
  }

  it should "solve the simplest of all ODEs" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=1}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 ==> \\forall t_ (t_>=0 -> t_+x>0)".asSequent

  }

  it should "solve simple box after ODE" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2}][x:=3;]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 ==> \\forall t_ (t_>=0 -> [x:=3;] x>0)".asSequent
  }

  it should "solve simple nested ODEs" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2}][{x'=3}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x_1>0 ==> \\forall t_ (t_>=0 -> \\forall x (x=2*t_+x_1 -> [{x'=3}]x>0))".asSequent
  }

  it should "solve outer nested ODEs even when innermost cannot be solved" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2}][{x'=3}][{x'=x}]x>0".asSequent, solve(1) & solve(1, 0::1::0::1::Nil))
    result.subgoals.loneElement shouldBe "x_1>0 ==> \\forall t__0 (t__0>=0->\\forall x_2 (x_2=2*t__0+x_1->\\forall t_ (t_>=0->\\forall x (x=3*t_+x_2->[{x'=x}]x>0))))".asSequent
  }

  it should "not try to preserve t_>=0 in evolution domain constraint when solving nested ODEs" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2}][{x'=3}][{x'=x}]x>0".asSequent, solve(1) & (allR(1) & implyR(1))*2 & solve(1))
    result.subgoals.loneElement shouldBe "x_1>0, t_>=0, x_2=2*t_+x_1 ==> \\forall t_ (t_>=0->\\forall x (x=3*t_+x_2->[{x'=x}]x>0))".asSequent
  }

  it should "solve complicated nested ODEs" in withQE { _ =>
    val result = proveBy("v=0 & x<s & 0<T, t=0, a_0=(s-x)/T^2 ==> [{x'=v,v'=a_0,t'=1&v>=0&t<=T}](t>0->\\forall a (a = (v^2/(2 *(s - x)))->[{x'=v,v'=-a,t'=1 & v>=0}](x + v^2/(2*a) <= s & (x + v^2/(2*a)) >= s)))".asSequent,
      solve(1))
    result.subgoals.loneElement shouldBe "v_1=0 & x_1<s & 0<T, t_1=0, a_0=(s-x_1)/T^2 ==> \\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->a_0*s_+v_1>=0&s_+t_1<=T)->\\forall t (t=t_+t_1->\\forall v (v=a_0*t_+v_1->\\forall x (x=a_0*(t_^2/2)+v_1*t_+x_1->t>0->\\forall a (a=v^2/(2*(s-x))->[{x'=v,v'=-a,t'=1&v>=0}](x+v^2/(2*a)<=s&x+v^2/(2*a)>=s))))))".asSequent
  }

  it should "not touch index of existing other occurrences of initial values" in withQE { _ =>
    val result = proveBy("x>0, x_0=b ==> [{x'=1}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0, x_0=b ==> \\forall t_ (t_>=0 -> t_+x>0)".asSequent
  }

  it should "retain initial evolution domain for the sake of contradictions" in withQE { _ =>
    val result = proveBy("x<=0 ==> [{x'=1&x>0}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x<=0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> s_+x>0) -> t_+x>0)".asSequent
  }

  it should "preserve contradictions in constants" in withQE { _ =>
    val result = proveBy("y>0 ==> [{x'=1&y<=0}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "y>0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> y <= 0) -> t_+x>0)".asSequent
  }

  it should "retain initial evolution domain for the sake of contradictions (2)" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=1&x<0}]x>=0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> s_+x<0) -> t_+x>=0)".asSequent
  }

  it should "solve explicit-form ODE" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=0*x+1}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 ==> \\forall t_ (t_>=0 -> t_+x>0)".asSequent
  }

  it should "FEATURE_REQUEST: solve diamond explicit-form ODE" taggedAs TodoTest in withQE { _ =>
    val result = proveBy("x>0 ==> <{x'=0*x+1}>x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 ==> \\exists t_ (t_>=0 & t_+x>0)".asSequent
  }

  it should "solve diamond ODE" in withQE { _ =>
    val result = proveBy("x>0 ==> <{x'=1}>x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 ==> \\exists t_ (t_>=0 & t_+x>0)".asSequent
  }

  it should "solve diamond ODE in context" in withQE { _ =>
    val result = proveBy("x>0, v>=0 ==> [v:=v;]<{x'=v}>x>0".asSequent, solve(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x>0, v>=0 ==> [v:=v;]\\exists t_ (t_>=0 & v*t_+x>0)".asSequent
  }

  it should "not lose constant facts" in withQE { _ =>
    val result = proveBy("r>0 -> [{v'=1/r}]v>0".asFormula, implyR(1) & solve(1))
    result.subgoals.loneElement shouldBe "r>0 ==> \\forall t_ (t_>=0 -> 1/r*t_+v>0)".asSequent
  }

  it should "not choke on constant fact 'true'" in withQE { _ =>
    val result = proveBy("r>0 & true -> [{v'=1/r}]v>0".asFormula, implyR(1) & andL('L) & solve(1))
    result.subgoals.loneElement shouldBe "r>0, true ==> \\forall t_ (t_>=0 -> 1/r*t_+v>0)".asSequent
  }

  it should "not choke on constant conjunct with 'true'" in withQE { _ =>
    val result = proveBy("r>0 & true -> [{v'=1/r}]v>0".asFormula, implyR(1) & solve(1))
    result.subgoals.loneElement shouldBe "r>0&true ==> \\forall t_ (t_>=0 -> 1/r*t_+v>0)".asSequent
  }

  it should "retain quantified facts without trying to diffcut" in withQE { _ =>
    val result = proveBy("\\forall v v>0 ==> [{v'=1}]v>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "\\forall v v>0 ==> \\forall t_ (t_>=0 -> t_+v>0)".asSequent
  }

  it should "solve in context" in withQE { _ =>
    val result = proveBy("A>0 -> [a:=A;][{v'=a}]v>0".asFormula, implyR(1) & solve(1, 1::Nil))
    result.subgoals.loneElement shouldBe "A>0 ==> [a:=A;]\\forall t_ (t_>=0 -> a*t_+v>0)".asSequent
  }

  it should "preserve const facts when solving in context" in withQE { _ =>
    val result = proveBy("A>0 -> [a:=A;][{v'=1/A}]v>0".asFormula, implyR(1) & solve(1, 1::Nil))
    result.subgoals.loneElement shouldBe "A>0 ==> [a:=A;]\\forall t_ (t_>=0 -> 1/A*t_+v>0)".asSequent
  }

  it should "solve triple integrator with division" in withMathematica { _ =>
    val result = proveBy("x>=0&v>=0&a>=0&s>=0&g()>0 -> [{x'=v,v'=a/g(),a'=s}]x>=0".asFormula, implyR(1) & solve(1))
    result.subgoals.loneElement shouldBe "x>=0&v>=0&a>=0&s>=0&g()>0 ==> \\forall t_ (t_>=0->(s*(t_^3/6)+a*(t_^2/2))/g()+v*t_+x>=0)".asSequent
  }

  it should "solve double integrator with sum of constants" in withQE { _ =>
    val result = proveBy("y<b, x<=0, Y()>=0, Z()<Y() ==> [{y'=x, x'=-Y()+Z()}]y<b".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "y<b, x<=0, Y()>=0, Z()<Y() ==> \\forall t_ (t_>=0 -> (-Y()+Z())*(t_^2/2)+x*t_+y<b)".asSequent
  }

  "endODEHeuristic" should "instantiate with duration in positive polarity in succedent" in withQE { _ =>
    proveBy("x>=0 ==> [{x'=1 & x<=5}]x>=0".asSequent, solve(1) & DifferentialTactics.endODEHeuristic).subgoals.loneElement shouldBe "x>=0 ==> \\forall t_ (t_>=0->t_+x<=5->t_+x>=0)".asSequent
  }

  it should "not try to instantiate in negative polarity in succedent" in withQE { _ =>
    proveBy(" ==> ![{x'=1 & x<=5}]x>=0".asSequent, solve(1, 0::Nil) & DifferentialTactics.endODEHeuristic).subgoals.loneElement shouldBe "==> !\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->s_+x<=5)->t_+x<=5&t_+x>=0)".asSequent
  }

  it should "instantiate in negative polarity in antecedent" in withQE { _ =>
    proveBy("![{x'=1 & x<=5}]x>=0, x>=0 ==> ".asSequent, solve(-1, 0::Nil) & DifferentialTactics.endODEHeuristic).subgoals.loneElement shouldBe "!\\forall t_ (t_>=0->t_+x<=5->t_+x>=0), x>=0 ==> ".asSequent
  }

  it should "not try to instantiate in positive polarity in antecedent" in withQE { _ =>
    proveBy("[{x'=1 & x<=5}]x>=0 ==> ".asSequent, solve(-1) & DifferentialTactics.endODEHeuristic).subgoals.loneElement shouldBe "\\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->s_+x<=5)->t_+x<=5&t_+x>=0) ==> ".asSequent
  }

  "diffUnpackEvolutionDomainInitially" should "unpack the evolution domain of an ODE as fact at time zero" in withTactics {
    val result = proveBy("[{x'=3&x>=0}]x>=0".asFormula, DifferentialTactics.diffUnpackEvolutionDomainInitially(1))
    result.subgoals.loneElement shouldBe "x>=0 ==> [{x'=3&x>=0}]x>=0".asSequent
  }

  "Differential Invariants" should "FEATURE_REQUEST: prove random differential invariant equations" taggedAs TodoTest in withMathematica { tool =>
    //@note test is supposed/very likely to fail until feature is implemented (^0)
    for (i <- 1 to randomTrials) {
      val vars = IndexedSeq(Variable("x"),Variable("y"),Variable("z")) //rand.nextNames("z", 4)
      //@todo avoid divisions by zero
      val inv = rand.nextT(vars, randomComplexity, dots=false, diffs=false, funcs=false)
      val randClue = "Invariant produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed + "\n"

      val invString = withSafeClue("Error printing random invariant\n\n" + randClue) {
        KeYmaeraXPrettyPrinter.stringify(inv)
      }

      withSafeClue("Random invariant " + invString + "\n" + randClue) {
        println("Random invariant " + inv.prettyString)
        val x = vars(0)
        val y = vars(1)
        val parts = {
          try {
            Some((tool.deriveBy(Neg(inv), y),
              tool.deriveBy(inv, x)))
          }
          catch {
            // errors during partial derivative computation to set up the problem are ignored, usually x/0 issues
            case ex: ToolException => None
          }
        }
        parts match {
          case None => // skip
          case Some((diffy:Term, diffx:Term)) =>
            val sys = ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x), diffy),
              AtomicODE(DifferentialSymbol(y), diffx)), True)
            val cmp = rand.rand.nextInt(6) match {
              case 0 => Equal
              case 1 => GreaterEqual
              case 2 => Greater
              case 3 => LessEqual
              case 4 => Less
              case 5 => NotEqual
            }
            val swapit = if (rand.rand.nextBoolean()) (a:Term,b:Term) => cmp(a,b) else (a:Term,b:Term) => cmp(b,a)
            val opit = if (rand.rand.nextBoolean()) (a:Term,b:Term) => cmp(a,b) else {
              val delta = rand.nextT(vars, randomComplexity, dots=false, diffs=false, funcs=false)
              (a:Term,b:Term) => cmp(Plus(a,delta), Plus(b,delta))
            }
            val fml = opit(inv, Number(rand.rand.nextInt(200) - 100))
            val conjecture = Imply(fml, Box(sys, fml))
            withSafeClue("Random differential invariant " + conjecture + "\n" + randClue) {
              print(conjecture)
              val result = proveBy(conjecture,
                implyR(1) & dI()(1))
              result shouldBe 'proved
            }
        }
      }
    }
  }

  it should "prove boring case" in withQE { _ =>
    proveBy("z*4>=-8 -> [{x'=0,y'=0}]z*4>=-8".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }
  it should "FEATURE_REQUEST: prove ^0 case" taggedAs TodoTest in withQE { _ =>
    //@note test is supposed to fail until feature is implemented
    proveBy("x^0+x>=68->[{x'=0,y'=1&true}]x^0+x>=68".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }
  it should "FEATURE_REQUEST: prove crazy ^0 case" taggedAs TodoTest in withQE { _ =>
    //@note test is supposed to fail until feature is implemented
    proveBy("x+(y-y-(0-(0+0/1)+(41+x)^0))>=68->[{x'=0,y'=1&true}]x+(y-y-(0-(0+0/1)+(41+x)^0))>=68".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }
  it should "FEATURE_REQUEST: prove crazy case" taggedAs TodoTest in withQE { _ =>
    //@note test is supposed to fail until feature is implemented
    proveBy("(z+y+x)*(41/(67/x+((0+0)/y)^1))!=94->[{x'=-41/67*x,y'=41/67*x+41/67*(x+y+z)&true}](z+y+x)*(41/(67/x+((0+0)/y)^1))!=94".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }

  "Open Differential Invariant" should "prove x^3>5 -> [{x'=x^3+x^4}]x^3>5" in withQE { _ =>
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "FEATURE_REQUEST: prove x^3>5 -> [{x'=x^3+x^4}]x^3>5 incontext" taggedAs TodoTest in withQE { _ =>
    //@note test is supposed to fail until feature is implemented
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, openDiffInd(1, 1::Nil)) shouldBe 'proved
  }

  it should "prove 5<x^3 -> [{x'=x^3+x^4}]5<x^3" in withQE { _ =>
    proveBy("5<x^3 -> [{x'=x^3+x^4}]5<x^3".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "prove x^3>5 -> [{x'=7*x^3+x^8}]x^3>5" in withQE { _ =>
    proveBy("x^3>5 -> [{x'=7*x^3+x^8}]x^3>5".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "open diff ind x>b() |- [{x'=2}]x>b()" in withQE { _ =>
    proveBy(Sequent(IndexedSeq("x>b()".asFormula), IndexedSeq("[{x'=2}]x>b()".asFormula)), openDiffInd(1)) shouldBe 'proved
  }

  it should "open diff ind x>b |- [{x'=2}]x>b" in withQE { _ =>
    proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)), openDiffInd(1)) shouldBe 'proved
  }

  it should "disregard other modalities" in withQE { _ =>
    proveBy("x>b, [y:=3;]y<=3 ==> <z:=2;>z=2, [{x'=2}]x>b".asSequent, openDiffInd(2)) shouldBe 'proved
  }

  it should "directly prove x>0 -> [{x'=x}]x>0" in withQE { _ =>
    proveBy("x>0 -> [{x'=x}]x>0".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  /**
    * Test cases for the Darboux ghost tactics
    */

  "ODE Darboux" should "prove equational darboux" in withQE { _ =>
    //(x+z)' = (x*A+B)(x+z)
    val seq = "x+z=0 ==> [{x'=(A*y+B()*x), z' = A*z*x+B()*z & y = x^2}] x+z=0".asSequent
    val pr = proveBy(seq,
      DifferentialTactics.dgDbx("x*A+B()".asTerm)(1))

    println(pr)
    pr shouldBe 'proved
  }

  it should "prove equational darboux with consts" in withQE { _ =>
    //(x+z)' = (x*A+B)(x+z)
    val seq = "x=0 & a = 5 & b=0 ==> [{x'=a*x+b}] x-b=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbx("5".asTerm)(1)) shouldBe 'proved
  }

  it should "prove fractional darboux" in withMathematica { _ =>
    //(x+z)' = ((x*A+B)/z^2)(x+z), where z^2 > 0
    //assumes z^2 non-zero already in evol domain
    val seq = "x+z=0 ==> [{x'=(A*y+B()*x)/z^2, z' = (A*x+B())/z & y = x^2 & z^2 > 0}] x+z=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbx("(x*A+B())/z^2".asTerm)(1)) shouldBe 'proved
  }

  it should "prove >= darboux" in withQE { _ =>
    //(x+z)' =  x^2 + z*x + x^2 >= x*(x+z)
    //Maybe this should leave open that the remainder is >= 0?
    val seq = "x+z>=0 ==> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbx("x".asTerm)(1)) shouldBe 'proved
  }

  it should "prove <= darboux" in withQE { _ =>
    //(x+z)' =  x^2 + z*x + x^2 >= x*(x+z)
    //Maybe this should leave open that the remainder is >= 0?
    val seq = "-(x+z)<=0 ==> [{x'=x^2, z' = z*x+y & y = x^2}] -(x+z)<=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbx("x".asTerm)(1)) shouldBe 'proved
  }

  it should "auto-prove >= darboux" in withMathematica { _ =>
    //(x+z)' =  x^2 + z*x + x^2 >= x*(x+z)
    //Maybe this should leave open that the remainder is >= 0?
    val seq = "x+z>=0 ==> [{x'=x^2, z' = z*x+y & y = x^2}] x+z>=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbxAuto(1)) shouldBe 'proved
  }

  it should "prove >= fractional darboux" in withQE { _ =>
    //(x+z)' =  (1/z^2)(x+z) + x^2 >= (1/z^2)(x+z)
    //Maybe this should leave open that the remainder is >= 0?
    val seq = "x+z>=0 ==> [{x'=1/z, z' = x/z^2 + y & z^2 > 0 & y = x^2}] x+z>=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbx("1/z^2".asTerm)(1)) shouldBe 'proved
  }

  it should "prove < darboux" in withMathematica { _ =>
    //(x+z)' =  x^2 + z*x - x^2 <= x*(x+z)
    val seq = "x+z<0 ==> [{x'=x^2, z' = z*x+y & y = -x^2}] x+z<0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbx("x".asVariable)(1)) shouldBe 'proved
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbxAuto(1)) shouldBe 'proved
  }

  it should "prove > darboux" in withMathematica { _ =>
    //(x+z)' =  x^2 + z*x - x^2 <= x*(x+z)
    val seq = "-(x+z)>0 ==> [{x'=x^2, z' = z*x+y & y = -x^2}] -(x+z)>0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbx("x".asVariable)(1)) shouldBe 'proved
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbxAuto(1)) shouldBe 'proved
  }

  it should "automatically find equational darboux" in withMathematica { _ =>
    //(x+z)' = (x*A+B)(x+z)
    val seq = "x+z=0 ==> [{x'=(A*x^2+B()*x), z' = A*z*x+B()*z}] 0=-x-z".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbxAuto(1)) shouldBe 'proved
  }

  it should "fail with evolution domain constraints" in withMathematica { _ =>
    //(x+z)' = (x*A+B)(x+z)
    val seq = "x+z=0 ==> [{x'=(A*y+B()*x), z'=A*z*x+B()*z & y=x^2}]x+z=0".asSequent
    val pr = TactixLibrary.proveBy(seq, Idioms.?(DifferentialTactics.dgDbxAuto(1)))
    pr should not be 'proved
    //The automatically generated remainder term goal is left open
    pr.subgoals.loneElement shouldBe "x+z=0 ==> [{x'=(A*y+B()*x), z'=A*z*x+B()*z & y=x^2}]x+z=0".asSequent
  }

  it should "prove work with constified" in withMathematica { _ =>
    val seq = "y=0, x > 0 ==> [{x'=k*x+y}] x+y>0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgDbx("k".asVariable)(1)) shouldBe 'proved
  }

  "ODE Barrier" should "prove a strict barrier certificate" in withMathematica { _ =>
    //This one doesn't actually need the full power of strict barriers because it's also an inequational dbx
    val seq = "-x<=0 ==> [{x'=100*x^4+y*x^3-x^2+x+c, c'=x+y+z & c > x}] -x<=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgBarrier(1)) shouldBe 'proved
  }

  it should "prove a strict barrier certificate 1" in withMathematica {qeTool =>
    val seq = "(87*x^2)/200 - (7*x*y)/180 >= -(209*y^2)/1080 + 10 ==> [{x'=(5*x)/4 - (5*y)/6, y'=(9*x)/4 + (5*y)/2}] (87*x^2)/200 - (7*x*y)/180>= -(209*y^2)/1080 + 10 ".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgBarrier(1)) shouldBe 'proved
  }

  it should "prove a strict barrier certificate 2" in withMathematica {qeTool =>
    val seq = "(23*x^2)/11 + (34*x*y)/11 + (271*y^2)/66 - 5 <= 0 ==> [{x'=(x/2) + (7*y)/3 , y'=-x - y}] (23*x^2)/11 + (34*x*y)/11 + (271*y^2)/66 - 5<=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgBarrier(1)) shouldBe 'proved
  }

  it should "prove a strict barrier certificate (Z3)" in withZ3 { _ =>
    //This one doesn't actually need the full power of strict barriers because it's also an inequational dbx
    val seq = "-x<=0 ==> [{x'=100*x^4+y*x^3-x^2+x+c, c'=x+y+z & c > x}] -x<=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgBarrier(1)) shouldBe 'proved
  }

  it should "prove a strict barrier certificate 1 (Z3)" in withZ3 { _ =>
    val seq = "(87*x^2)/200 - (7*x*y)/180 >= -(209*y^2)/1080 + 10 ==> [{x'=(5*x)/4 - (5*y)/6, y'=(9*x)/4 + (5*y)/2}] (87*x^2)/200 - (7*x*y)/180>= -(209*y^2)/1080 + 10 ".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgBarrier(1)) shouldBe 'proved
  }

  it should "prove a strict barrier certificate 2 (Z3)" in withZ3 { _ =>
    val seq = "(23*x^2)/11 + (34*x*y)/11 + (271*y^2)/66 - 5 <= 0 ==> [{x'=(x/2) + (7*y)/3 , y'=-x - y}] (23*x^2)/11 + (34*x*y)/11 + (271*y^2)/66 - 5<=0".asSequent
    TactixLibrary.proveBy(seq, DifferentialTactics.dgBarrier(1)) shouldBe 'proved
  }

  it should "correctly Dconstify" in withQE { _ =>
    val seq = "b=1,x>b==> [{x'=-1 & x > 1}] x>b".asSequent
    TactixLibrary.proveBy(seq,  DifferentialTactics.dgBarrier(1)) shouldBe 'proved
  }

  it should "correctly Dconstify 2" in withQE { _ =>
    val seq = "b=1,x>b,a=-1==> [{x'=a & x > 1}] x*a^2>b".asSequent
    withTacticProgress(DifferentialTactics.dgBarrier(1), "barrier" :: Nil) {
      TactixLibrary.proveBy(seq,  _)
    } shouldBe 'proved
  }

  it should "handle Z3 ghost cuts correctly" in withQE { _ =>
    val seq = " (-1/3 + x)^2 + 2*(-1/3 + y)^2 < 1/25  ==> y=1,  [{x'=x*(2-x-y), y'=x-y & x >0 & y > 0}] (3/8*x+23/56*x^2-123/56*y+3/14*x*y+29/28*y^2-1<0)".asSequent
    val pr = proveBy(seq, DifferentialTactics.dgBarrier(2))
    println(pr)
    pr shouldBe 'proved
  }

  "DConstV" should "extend domain constraint with const assumptions" in withMathematica {_ =>
    val seq = "f()>0 , v>0, a>0, b>0, <{x'=c+f()}> x>0, c<0 ==> z=1, a>0, [{v'=a+b,x'=y+f() & x>=v | x>=5}]v>0, x=5, y=1".asSequent
    val pr = TactixLibrary.proveBy(seq,DifferentialTactics.DconstV(3) & DifferentialTactics.DconstV(-5))
    pr.subgoals.loneElement shouldBe
      "f()>0, v>0, a>0, b>0, <{x'=c+f()&f()>0&c < 0&true}>x>0, c < 0 ==> z=1, a>0, [{v'=a+b,x'=y+f()&f()>0&a>0&b>0&(x>=v|x>=5)}]v>0, x=5, y=1".asSequent
  }

  it should "extend with assumptions hidden in conjuncts" in withMathematica {_ =>
    val seq = "f()>0 & v>0 & x=0 & a>0, <{x'=c+f()}> x>0, x=0&c<0&(v<0 | x>0) ==> z=1 | a>0, !x=5, [{v'=a+b,x'=y+f() & x>=v | x>=5}]v>0, x=5 -> y=1".asSequent
    val pr = TactixLibrary.proveBy(seq,
      //This changes positions!: SaturateTactic(alphaRule)
      SaturateTactic(andL('L)) & DifferentialTactics.DconstV(3))
    pr.subgoals.loneElement shouldBe
      "<{x'=c+f()&true}>x>0, f()>0, x=0, v>0, c < 0, v < 0|x>0, x=0, a>0 ==> z=1|a>0, !x=5, [{v'=a+b,x'=y+f()&f()>0&a>0&(x>=v|x>=5)}]v>0, x=5->y=1".asSequent
  }

  it should "work on a trivial ODE" in withMathematica { _ =>
    val pr = proveBy("==> [{x'=x}]1=1".asSequent, DifferentialTactics.DconstV(1))
    pr.subgoals.loneElement shouldBe
      "==> [{x'=x}]1=1".asSequent
  }

  "domSimplify" should "simplify box succedent with domain constraint" in withMathematica {_ =>
    val seq = "==> a<0,[{x'=1 & f()>0 & b<0}](b<0 & f()>1)".asSequent
    val pr = TactixLibrary.proveBy(seq,DifferentialTactics.domSimplify(2))
    println(pr)
    pr.subgoals.loneElement shouldBe
    "==>  a < 0, [{x'=1&f()>0&b < 0}]f()>1".asSequent
  }

  it should "correctly handle reordering of domain constraints" in withMathematica {_ =>
    val seq = "==> a<0,[{x'=1 & ((d = 0 & c > 0 | a < 0 & (a >0 & b>0) & c>0) & (b<0 & (f()>0 | b>=0)))}](b<0 & f()>1)".asSequent
    val pr = TactixLibrary.proveBy(seq,DifferentialTactics.domSimplify(2))
    println(pr)
    pr.subgoals.loneElement shouldBe
      "==>  a < 0, [{x'=1&((d = 0 & c > 0 | a < 0 & (a >0 & b>0) & c>0) & (b<0 & (f()>0 | b>=0)))}]f()>1".asSequent
  }

  "dCClosure" should "strengthen the postcondition to its interior and cut in the closure" in withMathematica { _ =>
    val result = proveBy("t = 0, x = 1 ==> [{t'=1, x'=x & t <= 1}](x>0&x<=3)".asSequent, DifferentialTactics.dCClosure(true)(1))
    val result2 = proveBy("t = 0, x = 1 ==> [{t'=1, x'=x & t <= 1}](x>0&x<=3)".asSequent, DifferentialTactics.dCClosure(false)(1))

    result.subgoals should have size 2
    result.subgoals.head shouldBe "t = 0, x = 1 ==> x>0&3-x>0".asSequent
    result.subgoals(1) shouldBe "t = 0, x = 1 ==> [{t'=1,x'=x&t<=1&x>=0&3-x>=0}](x>0&3-x>0)".asSequent
    result2.subgoals should have size 2
    result2.subgoals.head shouldBe "t = 0, x = 1 ==> x>=0&3-x>=0".asSequent
    result2.subgoals(1) shouldBe "t = 0, x = 1 ==> [{t'=1,x'=x&t<=1&x>=0&3-x>=0}](x>0&3-x>0)".asSequent
  }

  it should "add syntactic closure to domain" in withMathematica { _ =>
    val res = proveBy("a=1,b()=2 ==> x>=0,y>=0,[{x'=a,y'=b()}](x<=0&y<0)".asSequent,
      DifferentialTactics.dCClosure(true)(3)
        <(
        QE,
        skip
      ))
    res.subgoals.loneElement shouldBe
    "a=1, b()=2 ==> x>=0, y>=0, [{x'=a,y'=b()&true&0-x>=0&0-y>=0}](0-x>0&0-y>0)".asSequent
  }

  it should "add work with function symbols" in withMathematica { _ =>
    val result = proveBy("a=1,b()=2 ==> x>=0,y>=0,[{x'=a,y'=b()}](f(x,y)>1)".asSequent,
      DifferentialTactics.dCClosure(true)(3)
        <(
        skip,
        skip
      ))

    result.subgoals should have size 2
    result.subgoals.head shouldBe "a=1, b()=2  ==>  x>=0, y>=0, f(x,y)-1>0".asSequent
    result.subgoals(1) shouldBe "a=1, b()=2  ==>  x>=0, y>=0, [{x'=a,y'=b()&true&f(x,y)-1>=0}]f(x,y)-1>0".asSequent
  }

  "dIClosed" should "assume closure of postcondition for proof of invariant interior" in withMathematica { qeTool =>
    val ode = DifferentialTactics.ODESpecific("{t'=1, x'=x}".asDifferentialProgram)
    val prv = proveBy("t = 0, x = 1 ==> [{t'=1, x'=x & t <= 1/2}](x>=1&x<=1+3*t)".asSequent, ode.dIClosed(1))
    prv.subgoals should have size 2
    // initial condition
    prv.subgoals.head shouldBe "t=0, x=1 ==> x>=1 & x<=1+3*t".asSequent
    // differential invariant
    prv.subgoals(1).succ.loneElement shouldBe "t<=1/2&x>=1&x<=1+3*t->min((x,0+3*1-x))>0".asFormula
    proveBy(prv, Idioms.<(QE, QE)) shouldBe 'proved
  }

  "taylorB" should "prove second order Taylor bound for exponential function" in withMathematica { _ =>
    val prv = proveBy("x0=x & t=0 ==> [{x'=x,t'=1&x>=0}]x0+x0*t+x0/2*t^2<=x".asSequent, DifferentialTactics.taylorB(1))
    prv shouldBe 'proved
  }

  "taylorStep" should "correctly execute a step on the exponential function" in withMathematica { _ =>
    val prv = proveBy("x0=x & t=0 ==> [{x'=-x,t'=1&x>=0}]x0-x0*t<=x".asSequent, DifferentialTactics.taylorStep(1))
    prv.subgoals should have size 1
    prv.subgoals.head shouldBe "x0()=x&t=0 ==>  [{x'=-x,t'=1&x>=0}]-x0()<=-x".asSequent
  }

  "DCC" should "correctly apply in succ" in withTactics {
    val seq = "G(x) ==> S(x), [{x'=f(x)&r(x)}](p(x)->q(x)), T(x)".asSequent
    val res = proveBy(seq, dCC(2))
    res.subgoals.length shouldBe 2
    res.subgoals(0) shouldBe "G(x) ==> S(x), [{x'=f(x)&r(x)&p(x)}]q(x), T(x)".asSequent
    //@todo stable positioning in succedent
    res.subgoals(1) shouldBe "G(x_0), r(x), !p(x) ==> T(x_0), S(x_0), [{x'=f(x)&r(x)}](!p(x))".asSequent
  }

  "Derive" should "correctly derive" taggedAs IgnoreInBuildTest in withMathematica { tool =>
    val vx = Variable("x")
    val vy = Variable("y")
    val vz = Variable("z")
    val vars = IndexedSeq(vx,vy,vz)

    for (i <- 1 to randomTrials) {
      //@todo avoid divisions by zero
      val inv = rand.nextT(vars, randomComplexity, dots=false, diffs=false, funcs=false)

      val dx = rand.nextT(vars, randomComplexity, dots=false, diffs=false, funcs=false)
      val dy = rand.nextT(vars, randomComplexity, dots=false, diffs=false, funcs=false)
      val dz = rand.nextT(vars, randomComplexity, dots=false, diffs=false, funcs=false)

      val ode =
        DifferentialProduct(
          AtomicODE(DifferentialSymbol(vx), dx),
          DifferentialProduct(
          AtomicODE(DifferentialSymbol(vy), dy),
          AtomicODE(DifferentialSymbol(vz), dz))
        )

      //Uses dI
      val l1 =
        try {
          Some(DifferentialHelper.lieDerivative(ode,inv))
        }
        catch {
          case ex: BelleThrowable => None
        }
      val l2 =
        try {
          Some(DifferentialHelper.simplifiedLieDerivative(ode,inv,None))
        }
        catch {
          case ex: ToolException => None
        }
      val l3 =
        try {
          Some(Plus(
            Times(tool.deriveBy(inv, vx), dx),
            Plus(Times(tool.deriveBy(inv, vy), dy), Times(tool.deriveBy(inv, vz), dz))))
        }
        catch {
          case ex: ToolException => None
        }

      (l1,l2,l3) match {
        case (Some(r1),Some(r2),Some(r3)) =>
          try {
            val pr1 = proveBy(Equal(r1, r2), QE)
            val pr2 = proveBy(Equal(r2, r3), QE)
            val pr3 = proveBy(Equal(r3, r1), QE) //this should be unnecessary

            (pr1.isProved,pr2.isProved,pr3.isProved) shouldBe (true,true,true)
          }
          catch {
            case ex: BelleThrowable =>
              // Ignores failures due to division by 0
              println("Lie derivatives mismatch (QE fails) on: ", ode, inv)
              println(l1,l2,l3)
          }
        case _ =>
          // Ignores failures due to ^0
          println("Lie derivatives mismatch (Calculation) on: ",ode,inv)
          println(l1,l2,l3)
      }
    }
  }
}
