package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.ToolException
import testHelper.CustomAssertions._
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable.IndexedSeq
import org.scalatest.LoneElement._
import org.scalatest.prop.TableDrivenPropertyChecks.forEvery
import org.scalatest.prop.Tables._

/**
 * Tests
 * [[edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics]],
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.DW]], and
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.DC]]
 */
@SummaryTest
@UsualTest
class DifferentialTests extends TacticTestBase {
  val randomTrials = 500
  val randomComplexity = 6
  val rand = new RandomFormula()

  "DW" should "pull out evolution domain constraint" in {
    val result = proveBy("[{x'=1 & x>2}]x>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{x'=1&x>2}](x>2 -> x>0)".asSequent
  }

  it should "pull out evolution domain constraint in some context" in {
    val result = proveBy("[x:=0;][{x'=1 & x>2}]x>0".asFormula, DW(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=0;][{x'=1 & x>2}](x>2 -> x>0)".asSequent
  }

  it should "perform alpha renaming if necessary" in {
    val result = proveBy("[{y'=y & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{y'=y & y>2 & z<0}](y>2 & z<0 -> y>0)".asSequent
  }

  it should "introduce true if there is no evolution domain constraint" in {
    val result = proveBy("[{x'=1}]x>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{x'=1}](true -> x>0)".asSequent
  }

  it should "pull out evolution domain constraints from system of ODEs" in {
    val result = proveBy("[{x'=x, y'=1 & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{x'=x, y'=1 & y>2 & z<0}](y>2 & z<0 -> y>0)".asSequent
  }

  it should "also work when the ODEs are interdependent" in {
    val result = proveBy("[{x'=x+y, y'=1, z'=2 & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals.loneElement shouldBe "==> [{x'=x+y, y'=1, z'=2 & y>2 & z<0}](y>2 & z<0 -> y>0)".asSequent
  }

  "diffWeaken" should "perform alpha renaming if necessary" in {
    val result = proveBy("[{y'=y & y>2 & z<0}]y>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "==>y>2 & z<0 -> y>0".asSequent
  }

  it should "introduce true if there is no evolution domain constraint" in {
    val result = proveBy("[{x'=1}]x>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "==> true -> x>0".asSequent
  }

  it should "pull out evolution domain constraint from system of ODEs" in {
    val result = proveBy("[{x'=x, y'=1 & y>2 & z<0}]y>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "==> y>2 & z<0 -> y>0".asSequent
  }

  it should "also work when the ODEs are interdependent" in {
    val result = proveBy("[{x'=x+y, y'=1, z'=2 & y>2 & z<0}]y>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "==> y>2 & z<0 -> y>0".asSequent
  }

  it should "weaken if ODE afterwards" in {
    val result = proveBy("[{x'=1}][{x'=2}]x>0".asFormula, dW(1))
    result.subgoals.loneElement shouldBe "==> true -> [{x'=2}]x>0".asSequent
  }

  it should "retain single context formula" in withQE { _ =>
    val result = proveBy("A>0, x=4 ==> [{x'=1&x>0}]x>0".asSequent, dW(1))
    result.subgoals.loneElement shouldBe "A>0 ==> x>0 -> x>0".asSequent
  }

  it should "retain context" in withQE { _ =>
    val result = proveBy("A>0&A>1, B=1, C=2&D=3, x=4 ==> [{x'=1&x>0}]x>0".asSequent, dW(1))
    result.subgoals.loneElement shouldBe "A>0&A>1, B=1, C=2&D=3 ==> x>0 -> x>0".asSequent
  }

  it should "work if not sole formula in succedent" in withQE { _ =>
    val result = proveBy("A>0&A>1, B=1, C=2&D=3, x=4 ==> Blah=1, [{x'=1&x>2}]x>0, Blub=3".asSequent, dW(2))
    result.subgoals.loneElement shouldBe "A>0&A>1, B=1, C=2&D=3, x_0=4 ==> Blah=1, Blub=3, x>2 -> x>0".asSequent
  }

  "Differential effect" should "introduce a differential assignment" in {
    val result = proveBy("[{x'=5 & x>2}]x>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5 & x>2}][x':=5;]x>0".asSequent
  }

  it should "introduce differential assignments exhaustively" in {
    val result = proveBy("[{x'=5, y'=x}]x>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5, y'=x}][y':=x;][x':=5;]x>0".asSequent
  }

  it should "introduce differential assignments whatever the names (manual useAt)" in {
    val result = proveBy("[{z'=5, y'=z}]z>0".asFormula, useAt("DE differential effect (system)")(1))
    result.subgoals.loneElement shouldBe "==> [{y'=z,z'=5}][z':=5;]z>0".asSequent
  }

  it should "introduce differential assignments in long cases whatever the names (manual useAt)" in {
    val result = proveBy("[{z'=5, y'=z, u'=v}]z>0".asFormula, useAt("DE differential effect (system)")(1))
    result.subgoals.loneElement shouldBe "==> [{y'=z,u'=v,z'=5}][z':=5;]z>0".asSequent
  }

  it should "introduce differential assignments exhaustively whatever the names" in {
    val result = proveBy("[{z'=5, y'=3}]z>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{z'=5, y'=3}][y':=3;][z':=5;]z>0".asSequent
  }

  it should "introduce differential assignments exhaustively for x" in {
    val result = proveBy("[{x'=5, y'=3}]x>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5, y'=3}][y':=3;][x':=5;]x>0".asSequent
  }

  it should "introduce differential assignments exhaustively whatever the names even mutually recursive" in {
    val result = proveBy("[{z'=5, y'=z}]z>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{z'=5, y'=z}][y':=z;][z':=5;]z>0".asSequent
  }

  it should "introduce differential assignments exhaustively despite evolution domain" in {
    val result = proveBy("[{x'=5, y'=x & x>2}]x>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5, y'=x & x>2}][y':=x;][x':=5;]x>0".asSequent
  }

  it should "introduce a differential assignment when the postcondition is primed" in {
    val result = proveBy("[{x'=5 & x>2}](x>0)'".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5 & x>2}][x':=5;](x>0)'".asSequent
  }

  it should "introduce differential assignments when the postcondition is primed" in {
    val result = proveBy("[{x'=5, y'=2 & x>2}](x>0)'".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{x'=5, y'=2 & x>2}][y':=2;][x':=5;](x>0)'".asSequent
  }

  it should "introduce a differential assignment in context" in {
    val result = proveBy("[x:=0;][{x'=5 & x>2}]x>0".asFormula, DE(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=0;][{x'=5 & x>2}][x':=5;]x>0".asSequent
  }

  it should "alpha rename if necessary" in {
    val result = proveBy("[{y'=5 & y>2}]y>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{y'=5 & y>2}][y':=5;]y>0".asSequent
  }

  it should "alpha rename with remaining ODEs mentioning original x from axiom" in {
    val result = proveBy("[{y'=5,x'=2 & y>2 & x>0}]y>0".asFormula, DE(1))
    result.subgoals.loneElement shouldBe "==> [{y'=5, x'=2 & y>2 & x>0}][x':=2;][y':=5;]y>0".asSequent
  }

  "Dassignb" should "assign isolated single variable" in {
    val result = proveBy("[x':=v;]x'>=0".asFormula, Dassignb(1))
    result.subgoals.loneElement shouldBe "==> v>=0".asSequent
  }

  it should "assign isolated single const" in {
    val result = proveBy("[u':=b();]u'>=0".asFormula, Dassignb(1))
    result.subgoals.loneElement shouldBe "==> b()>=0".asSequent
  }
  it should "assign isolated single const 2" in {
    val result = proveBy("[x':=v();]x'>=0".asFormula, Dassignb(1))
    result.subgoals.loneElement shouldBe "==> v()>=0".asSequent
  }

  it should "assign single const" in {
    val result = proveBy("[{x'=v()}][x':=v();]x'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v()}]v()>=0".asSequent
  }
  it should "assign single variable" in {
    val result = proveBy("[{x'=v}][x':=v;]x'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v}]v>=0".asSequent
  }

  it should "prove single variable" in withQE { _ =>
    proveBy("v>=0 -> [{x'=v}][x':=v;]x'>=0".asFormula, Dassignb(1, 1::1::Nil) & implyR(1) & abstractionb(1) & QE) shouldBe 'proved
  }

  it should "prove single const" in withQE { _ =>
    proveBy("v()>=0 -> [{x'=v()}][x':=v();]x'>=0".asFormula, Dassignb(1, 1::1::Nil) & implyR(1) & abstractionb(1) & QE) shouldBe 'proved
  }

  it should "assign flat variable" in {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::1::Nil) & Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a&true}]a>=0".asSequent
  }

  it should "assign flat const" in {
    val result = proveBy("[{x'=v,v'=a()}][v':=a();][x':=v;]v'>=0".asFormula, Dassignb(1, 1::1::Nil) & Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a()&true}]a()>=0".asSequent
  }

  it should "assign nested variabe" in {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a&true}][x':=v;]a>=0".asSequent
  }

  it should "assign nested variable" in {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a&true}][x':=v;]a>=0".asSequent
  }

  it should "assign nested const" in {
    val result = proveBy("[{x'=v,v'=a()}][v':=a();][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,v'=a()&true}][x':=v;]a()>=0".asSequent
  }

  it should "assign nested separate variable" in {
    val result = proveBy("[{x'=v,y'=a}][y':=a;][x':=v;]y'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,y'=a&true}][x':=v;]a>=0".asSequent
  }

  it should "assign nested separate const" in {
    val result = proveBy("[{x'=v,y'=a()}][y':=a();][x':=v;]y'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [{x'=v,y'=a()&true}][x':=v;]a()>=0".asSequent
  }

  "diffInd" should "auto-prove x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withQE { _ =>
    proveBy("x>=5 -> [{x'=2}]x>=5".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
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

  it should "x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in {
    val result = proveBy("x>=5 ==> [{x'=2}]x>=5".asSequent, DifferentialTactics.diffInd('none)(1))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>=5, true ==> x>=5".asSequent
    result.subgoals.last shouldBe "x>=5, true ==> [{x'=2}](x>=5)'".asSequent
  }

  it should "x>=5 -> [{x'=2}]x>=5 in context" taggedAs KeYmaeraXTestTags.SummaryTest in {
    val result = proveBy("x>=5 ==> [x:=x+1;][{x'=2}]x>=5".asSequent, DifferentialTactics.diffInd('none)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x>=5 ==> [x:=x+1;](true->x>=5&[{x'=2}](x>=5)')".asSequent
  }

  it should "autoprove x>=5 -> [{x'=2}]x>=5 in context" taggedAs KeYmaeraXTestTags.SummaryTest in {
    val result = proveBy("x>=5 ==> [x:=x+1;][{x'=2}]x>=5".asSequent, DifferentialTactics.diffInd('full)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x>=5 ==> [x:=x+1;](true->x>=5&2>=0)".asSequent
  }

  it should "autoprove x>=5&y>=0 -> [{x'=y}]x>=5 in context" taggedAs KeYmaeraXTestTags.SummaryTest in {
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

    proveBy(KeYmaeraXProblemParser(input), implyR(1) & dI('full)(1)) shouldBe 'proved
  }

  it should "prove with and without frame constraint y'=0" in withQE { _ =>
    proveBy("x=y ==> [{x'=2 & x>=0}]x>=y".asSequent, dI('full)('R)) shouldBe 'proved
    proveBy("x=y ==> [{x'=2, y'=0 & x>=0}]x>=y".asSequent, dI('full)('R)) shouldBe 'proved
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

  it should "work in a context that binds x" in {
    val result = proveBy("[z:=1;](z)'=1".asFormula, Derive.Dvar(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> [z:=1;]z'=1".asSequent
  }

  it should "work with other formulas around" in {
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

  it should "cut in multiple formulas" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent, dC("v>=0".asFormula, "x>=old(x)".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "v>=0, x_0>0, x_0=x ==> [{x'=v,v'=2 & (true & v>=0) & x>=x_0}]x>=0".asSequent
    result.subgoals(1) shouldBe "v>=0, x>0 ==> [{x'=v,v'=2}]v>=0".asSequent
    result.subgoals(2) shouldBe "v>=0, x_0>0, x_0=x ==> [{x'=v,v'=2 & true & v>=0}]x>=x_0".asSequent
  }

  it should "not expand old() ghosts in context" in withQE { _ =>
    val result = proveBy("[x:=0;][{x'=1}]x>=0".asFormula, dC("x>=old(x)".asFormula)(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "==> [x:=0;][x_0:=x;][{x'=1 & true & x>=x_0}]x>=0".asSequent
  }

  it should "compute the followup position correctly" in withQE { _ =>
    val result = proveBy("y=1 ==> [x:=0;][{x'=1,y'=-1}]x>=0".asSequent, dC("x>=old(x) & y<=old(y)".asFormula)(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals.head shouldBe "y=1 ==> [x:=0;][y_0:=y;][x_0:=x;][{x'=1,y'=-1 & true & (x>=x_0 & y<=y_0)}]x>=0".asSequent
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
    val result = proveBy("v>=0, x>0 ==> <{x'=v,v'=2}>x>=0".asSequent, dC("v>=0".asFormula, "x>=old(x)".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "v>=0, x_0>0, x_0=x ==> <{x'=v,v'=2 & (true & v>=0) & x>=x_0}>x>=0".asSequent
    result.subgoals(1) shouldBe "v>=0, x>0 ==> [{x'=v,v'=2}]v>=0".asSequent
    result.subgoals(2) shouldBe "v>=0, x_0>0, x_0=x ==> [{x'=v,v'=2 & true & v>=0}]x>=x_0".asSequent
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
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent, diffInvariant("v>=0".asFormula, "x>0".asFormula)(1))
    result.subgoals.loneElement shouldBe "v>=0, x>0 ==> [{x'=v,v'=2 & (true & v>=0) & x>0}]x>=0".asSequent
  }

  it should "cut in multiple formulas with old" in withQE { _ =>
    val result = proveBy("v>=0, x>0 ==> [{x'=v,v'=2}]x>=0".asSequent, diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1))
    result.subgoals.loneElement shouldBe "v>=0, x_0>0, x_0=x ==> [{x'=v,v'=2 & (true & v>=0) & x>=x_0}]x>=0".asSequent
  }

  it should "cut in time as needed by diffSolve" in withQE { _ =>
    val result = proveBy("t=0 ==> [{x'=2,t'=0*t+1}]x>=0".asSequent, diffInvariant("t>=0".asFormula)(1))
    result.subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=0*t+1 & true & t>=0}]x>=0".asSequent
  }

  it should "fail if any of the formulas is not an invariant" in withQE { _ =>
    a [BelleThrowable] should be thrownBy proveBy("x>0 ==> [{x'=v,v'=2}]x>=0".asSequent,
      diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1))
  }

  it should "let us directly prove variable x+y^2*3-z = x+y^2*3-z by abbreviation" in withQE { _ =>
    proveBy("x+y^2*3-z=x+y^2*3-z".asFormula, let(FuncOf(Function("s_",None,Unit,Real),Nothing), "x+y^2*3-z".asTerm, by(DerivedAxioms.equalReflex))) shouldBe 'proved
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

  it should "let us prove variable [x':=5;](x+y)'>=0" ignore withQE { _ =>
    //@note proof waited too long. Should have gone constant before diffind
    proveBy("[x':=5;](x+y)'>=0".asFormula,
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), derive(1,1::0::Nil) & Dassignb(1) & QE)) shouldBe 'proved
  }

  it should "prove const [{x'=5}](x+c())'>=0" in withQE { _ =>
    proveBy("[{x'=5}](x+c())'>=0".asFormula,
      derive(1,1::0::Nil) & DE(1) & G(1) & Dassignb(1) & QE) shouldBe 'proved
  }

  it should "let us prove variable [{x'=5}](x+y)'>=0" ignore withQE { _ =>
    //@note proof waited too long. Should have gone constant before diffind
    proveBy("[{x'=5}](x+y)'>=0".asFormula,
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


  private def mockTactic(expected: Sequent) = new SingleGoalDependentTactic("mock") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      sequent shouldBe expected
      skip
    }
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

  "Differential introduce constants" should "replace a with a()" in {
    forEvery (dconstifyTests) {
      (name, input, expected) => withClue(name) {
        try {
          proveBy(input.asSequent, DifferentialTactics.Dconstify(mockTactic(expected.asSequent))(1))
        } catch {
          // proveBy may throw an expected exception sometimes -> filter the expected one
          case ex: Throwable if ex.getCause != null && ex.getCause.getMessage.contains("Unless proved, uniform substitutions instances cannot introduce free variables") => // expected
          case ex: Throwable => throw ex
        }
      }
    }
  }

  "DG" should "add y'=1 to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, dG("{y'=0*y+1}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=0*y+1}]x>0".asSequent
  }

  it should "add z'=1 to [y'=2]y>0" in {
    val result = proveBy("[{y'=2}]y>0".asFormula, dG("{z'=0*z+1}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists z [{y'=2,z'=0*z+1}]y>0".asSequent
  }

  it should "add x'=1 to [y'=2]y>0" in {
    val result = proveBy("[{y'=2}]y>0".asFormula, dG("{x'=0*x+1}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists x [{y'=2,x'=0*x+1}]y>0".asSequent
  }

  it should "add y'=3*y+10 to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, dG("{y'=3*y+10}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=3*y+10}]x>0".asSequent
  }

  it should "add y'=3*y+z() to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, dG("{y'=3*y+z()}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=3*y+z()}]x>0".asSequent
  }

  it should "preserve evolution domain" in {
    val result = proveBy("[{x'=2 & x>=0}]x>0".asFormula, dG("{y'=3*y+10}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=3*y+10 & x>=0}]x>0".asSequent
  }

  it should "work with other formulas around" in {
    val result = proveBy("a>1 ==> [{x'=2 & x>=0}]x>0, b=2".asSequent, dG("{y'=3*y+10}".asDifferentialProgram, None)(1))
    result.subgoals.loneElement shouldBe "a>1 ==> \\exists y [{x'=2,y'=3*y+10 & x>=0}]x>0, b=2".asSequent
  }

  it should "do basic unification" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, dG("{t'=0*t+1}".asDifferentialProgram, None)(1) & existsR("0".asTerm)(1))
    result.subgoals.loneElement shouldBe "t=0 ==> [{x'=2,t'=0*t+1}]x>0".asSequent
  }

  it should "not allow non-linear ghosts (1)" in {
    a [BelleThrowable] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, dG("{y'=y*y+1}".asDifferentialProgram, None)(1))
  }

  it should "not allow non-linear ghosts (2)" in {
    a [BelleThrowable] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, dG("{y'=1*y+y}".asDifferentialProgram, None)(1))
  }

  it should "not allow ghosts that are already present in the ODE" in {
    a [BelleThrowable] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, dG("{x'=0*x+1}".asDifferentialProgram, None)(1))
  }

  "DA" should "add y'=1 to [x'=2]x>0" in withQE { _ =>
    val s = "==> [{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+1}".asDifferentialProgram, Some("y>0 & x*y>0".asFormula))(1)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=0*y+1}](y>0 & x*y>0)".asSequent
  }

  it should "work in a simple context" in withQE { _ =>
    val s = "x>0 ==> a=2 -> [{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+1}".asDifferentialProgram, Some("y>0 & x*y>0".asFormula))(1, 1::Nil)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "x>0 ==> a=2 -> \\exists y [{x'=2,y'=0*y+1}](y>0 & x*y>0)".asSequent
  }

  it should "work in a complicated context" in withQE { _ =>
    val s = "x>0 ==> a=2 -> [b:=3;]<?c=5;{c'=2}>[{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+1}".asDifferentialProgram, Some("y>0 & x*y>0".asFormula))(1, 1::1::1::Nil)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "x>0 ==> a=2 -> [b:=3;]<?c=5;{c'=2}>\\exists y [{x'=2,y'=0*y+1}](y>0 & x*y>0)".asSequent
  }

  it should "add y'=-a() to [x'=2]x>0" in withQE { _ =>
    val s = "a()>0, x>0 ==> [{x'=2}]x>0".asSequent
    val tactic = dG("{y'=0*y+(-a())}".asDifferentialProgram, Some("x>0 & y<0".asFormula))(1)
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe "a()>0, x>0 ==> \\exists y [{x'=2,y'=0*y+-a()}](x>0 & y<0)".asSequent
  }

  it should "solve x'=x" in withQE { _ =>
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

  it should "do fancy unification for proving x>0->[{x'=-x}]x>0" in withQE { _ =>
    val result = proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) &
      dG("{y'=(1/2)*y+0}".asDifferentialProgram, Some("x*y^2=1".asFormula))(1) & existsR("1/x^(1/2)".asTerm)(1) & dI()(1) & QE)
    result shouldBe 'proved
  }

  it should "do fancy unification for proving x>0->[{x'=x}]x>0" in withQE { _ =>
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
    result.subgoals.loneElement shouldBe "==> \\exists y [{x'=2,y'=0*y+1}](y>0 & x*y>0)".asSequent
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
    result.subgoals.loneElement shouldBe "x>0 & v>=0 & a>0 ==> \\forall t_ (t_>=0 -> a/2*t_^2+v*t_+x>0)".asSequent
  }

  it should "solve ODE with const factor" in withQE { _ =>
    val result = proveBy("[{x'=c*v}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> c*v*t_+x>0)".asSequent
  }

  it should "solve ODE system with const factor" in withQE { _ =>
    val result = proveBy("[{x'=c*v,v'=a}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> c*(a/2*t_^2+v*t_)+x>0)".asSequent
  }

  it should "solve ODE system with number factor" in withQE { _ =>
    val result = proveBy("[{x'=3*v,v'=a}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> 3*(a/2*t_^2+v*t_)+x>0)".asSequent
  }

  it should "solve straight 2D driving" in withQE { _ =>
    val result = proveBy("[{v'=a,x'=v*dx,y'=v*dy}]x^2+y^2<=r^2".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> (dx*(a/2*t_^2+v*t_)+x)^2+(dy*(a/2*t_^2+v*t_)+y)^2<=r^2)".asSequent
  }

  it should "solve straight 2D driving when only x is mentioned in p" in withQE { _ =>
    val result = proveBy("[{v'=a,x'=v*dx,y'=v*dy}]x>0".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> dx*(a/2*t_^2+v*t_)+x>0)".asSequent
  }

  it should "solve more complicated constants" in withQE { _ =>
    val result = proveBy("[{v'=a+c,t'=1,x'=(v+5)*dx^2,y'=v*(3-dy)*c}]x^2+y^2<=r^2".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> (dx^2*((a+c)/2*t_^2+v*t_+5*t_)+x)^2+(c*((3-dy)*((a+c)/2*t_^2+v*t_))+y)^2<=r^2)".asSequent
  }

  it should "solve more complicated constants with explicit c'=0" in withQE { _ =>
    //@note dx'=0 omitted intentionally to test for mixed explicit/non-explicit constants
    val result = proveBy("[{v'=a+c,t'=1,c'=0,x'=(v+5)*dx^2,y'=v*(3-dy)*c,dy'=0}]x^2+y^2<=r^2".asFormula, solve(1))
    result.subgoals.loneElement shouldBe "==> \\forall t_ (t_>=0 -> (dx^2*(a/2*t_^2+c/2*t_^2+v*t_+5*t_)+x)^2+(c*((3-dy)*(a/2*t_^2+c/2*t_^2+v*t_))+y)^2<=r^2)".asSequent
  }

  it should "work when ODE is not sole formula in succedent" in withQE { _ =>
    val result = proveBy("x>0 & v>=0 & a>0 ==> y=1, [{x'=v,v'=a}]x>0, z=3".asSequent, solve(2))
    result.subgoals.loneElement shouldBe "x>0 & v>=0 & a>0 ==> y=1, \\forall t_ (t_>=0 -> a/2*t_^2+v*t_+x>0), z=3".asSequent
  }

  it should "work when safety property is abstract" in withQE { _ =>
    val result = proveBy("J(x,v) ==> [{x'=v,v'=a}]J(x,v)".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "J(x,v) ==> \\forall t_ (t_>=0->J((a/2*t_^2+v*t_+x,a*t_+v)))".asSequent
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
    result.subgoals.loneElement shouldBe "x_1>0 ==> \\forall t_ (t_>=0->\\forall x_2 (x_2=2*t_+x_1->\\forall t_ (t_>=0->\\forall x (x=3*t_+x_2->[{x'=x}]x>0))))".asSequent
  }

  it should "not try to preserve t_>=0 in evolution domain constraint when solving nested ODEs" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=2}][{x'=3}][{x'=x}]x>0".asSequent, solve(1) & (allR(1) & implyR(1))*2 & solve(1))
    result.subgoals.loneElement shouldBe "x_1>0, t_>=0, x_3=2*t_+x_1 ==> \\forall t_ (t_>=0->\\forall x (x=3*t_+x_3->[{x'=x}]x>0))".asSequent
  }

  it should "solve complicated nested ODEs" in withQE { _ =>
    val result = proveBy("v=0 & x<s & 0<T, t=0, a_0=(s-x)/T^2 ==> [{x'=v,v'=a_0,t'=1&v>=0&t<=T}](t>0->\\forall a (a = (v^2/(2 *(s - x)))->[{x'=v,v'=-a,t'=1 & v>=0}](x + v^2/(2*a) <= s & (x + v^2/(2*a)) >= s)))".asSequent,
      solve(1))
    result.subgoals.loneElement shouldBe "v_1=0 & x_1<s & 0<T, t_1=0, a_0=(s-x_1)/T^2 ==> \\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->a_0*s_+v_1>=0&s_+t_1<=T)->\\forall t (t=t_+t_1->\\forall v (v=a_0*t_+v_1->\\forall x (x=a_0/2*t_^2+v_1*t_+x_1->t>0->\\forall a (a=v^2/(2*(s-x))->[{x'=v,v'=-a,t'=1&v>=0}](x+v^2/(2*a)<=s&x+v^2/(2*a)>=s))))))".asSequent
  }

  it should "not touch index of existing other occurrences of initial values" in withQE { _ =>
    val result = proveBy("x>0, x_0=b ==> [{x'=1}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0, x_0=b ==> \\forall t_ (t_>=0 -> t_+x>0)".asSequent
  }

  it should "retain initial evolution domain for the sake of contradictions" in withQE { _ =>
    val result = proveBy("x<=0 ==> [{x'=1&x>0}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x<=0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> s_+x>0) -> t_+x>0)".asSequent
  }

  it should "preserve contradictions in constants as false" in withQE { _ =>
    val result = proveBy("y>0 ==> [{x'=1&y<=0}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "y>0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> false) -> t_+x>0)".asSequent
  }

  it should "retain initial evolution domain for the sake of contradictions (2)" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=1&x<0}]x>=0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> s_+x<0) -> t_+x>=0)".asSequent
  }

  it should "solve explicit-form ODE" in withQE { _ =>
    val result = proveBy("x>0 ==> [{x'=0*x+1}]x>0".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "x>0 ==> \\forall t_ (t_>=0 -> t_+x>0)".asSequent
  }

  it should "solve diamond explicit-form ODE" ignore withQE { _ =>
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
    result.subgoals.loneElement shouldBe "x>=0&v>=0&a>=0&s>=0&g()>0 ==> \\forall t_ (t_>=0->(s/2/3*t_^3+a/2*t_^2)/g()+v*t_+x>=0)".asSequent
  }

  it should "solve double integrator with sum of constants" in withQE { _ =>
    val result = proveBy("y<b, x<=0, Y()>=0, Z()<Y() ==> [{y'=x, x'=-Y()+Z()}]y<b".asSequent, solve(1))
    result.subgoals.loneElement shouldBe "y<b, x<=0, Y()>=0, Z()<Y() ==> \\forall t_ (t_>=0 -> (-Y()+Z())/2*t_^2+x*t_+y<b)".asSequent
  }

  "diffUnpackEvolutionDomainInitially" should "unpack the evolution domain of an ODE as fact at time zero" in {
    val result = proveBy("[{x'=3&x>=0}]x>=0".asFormula, DifferentialTactics.diffUnpackEvolutionDomainInitially(1))
    result.subgoals.loneElement shouldBe "x>=0 ==> [{x'=3&x>=0}]x>=0".asSequent
  }

  "Differential Invariants" should "prove random differential invariant equations" taggedAs IgnoreInBuildTest in withMathematica { tool =>
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

  it should "prove boring case" taggedAs IgnoreInBuildTest in withQE { _ =>
    proveBy("z*4>=-8 -> [{x'=0,y'=0}]z*4>=-8".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }
  it should "prove ^0 case" taggedAs IgnoreInBuildTest in withQE { _ =>
    proveBy("x^0+x>=68->[{x'=0,y'=1&true}]x^0+x>=68".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }
  it should "prove crazy ^0 case" taggedAs IgnoreInBuildTest in withQE { _ =>
    proveBy("x+(y-y-(0-(0+0/1)+(41+x)^0))>=68->[{x'=0,y'=1&true}]x+(y-y-(0-(0+0/1)+(41+x)^0))>=68".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }
  it should "prove crazy case" taggedAs IgnoreInBuildTest in withQE { _ =>
    proveBy("(z+y+x)*(41/(67/x+((0+0)/y)^1))!=94->[{x'=-41/67*x,y'=41/67*x+41/67*(x+y+z)&true}](z+y+x)*(41/(67/x+((0+0)/y)^1))!=94".asFormula, implyR(1) & dI()(1)) shouldBe 'proved
  }

  "Open Differential Invariant" should "prove x^3>5 -> [{x'=x^3+x^4}]x^3>5" in withQE { _ =>
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "prove x^3>5 -> [{x'=x^3+x^4}]x^3>5 incontext" taggedAs IgnoreInBuildTest in withQE { _ =>
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, openDiffInd(1, 1::Nil)) shouldBe 'proved
  }

  it should "prove 5<x^3 -> [{x'=x^3+x^4}]5<x^3" in withQE { _ =>
    proveBy("5<x^3 -> [{x'=x^3+x^4}]5<x^3".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "prove x^3>5 -> [{x'=7*x^3+x^8}]x^3>5" in withQE { _ =>
    proveBy("x^3>5 -> [{x'=7*x^3+x^8}]x^3>5".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "prove x^3>=5 -> [{x'=7*x^3+x^8}]x^3>=5" in withQE { _ =>
    proveBy("x^3>=5 -> [{x'=7*x^3+x^8}]x^3>=5".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "prove 5<=x^3 -> [{x'=7*x^3+x^8}]5<=x^3" in withQE { _ =>
    proveBy("5<=x^3 -> [{x'=7*x^3+x^8}]5<=x^3".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
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

  "Differential Variant" should "diff var a()>0 |- <{x'=a()}>x>=b()" in withQE { _ =>
    proveBy(Sequent(IndexedSeq("a()>0".asFormula), IndexedSeq("<{x'=a()}>x>=b()".asFormula)), diffVar(1)) shouldBe 'proved
  }

  it should "diff var flat flight progress [function]" in withMathematica { _ =>
    proveBy("b>0 -> \\exists d (d^2<=b^2 & <{x'=d}>x>=p())".asFormula, diffVar(1, 1::0::1::Nil)) shouldBe 'proved
  }

  it should "diff var flat flight progress [variable]" taggedAs IgnoreInBuildTest in withQE { _ =>
    proveBy("b>0 -> \\forall p \\exists d (d^2<=b^2 & <{x'=d}>x>=p)".asFormula, diffVar(1, 1::0::0::1::Nil)) shouldBe 'proved
  }

}
