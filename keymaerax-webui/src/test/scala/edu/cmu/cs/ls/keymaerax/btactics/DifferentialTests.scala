package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
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
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=1&x>2}](x>2 -> x>0)".asFormula
  }

  it should "pull out evolution domain constraint in some context" in {
    val result = proveBy("[x:=0;][{x'=1 & x>2}]x>0".asFormula, DW(1, 1::Nil))

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=0;][{x'=1 & x>2}](x>2 -> x>0)".asFormula
  }

  it should "perform alpha renaming if necessary" in {
    val result = proveBy("[{y'=y & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{y'=y & y>2 & z<0}](y>2 & z<0 -> y>0)".asFormula
  }

  it should "introduce true if there is no evolution domain constraint" in {
    val result = proveBy("[{x'=1}]x>0".asFormula, DW(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=1}](true -> x>0)".asFormula
  }

  it should "pull out evolution domain constraints from system of ODEs" in {
    val result = proveBy("[{x'=x, y'=1 & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=x, y'=1 & y>2 & z<0}](y>2 & z<0 -> y>0)".asFormula
  }

  it should "also work when the ODEs are interdependent" in {
    val result = proveBy("[{x'=x+y, y'=1, z'=2 & y>2 & z<0}]y>0".asFormula, DW(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=x+y, y'=1, z'=2 & y>2 & z<0}](y>2 & z<0 -> y>0)".asFormula
  }

  "diffWeaken" should "perform alpha renaming if necessary" in {
    val result = proveBy("[{y'=y & y>2 & z<0}]y>0".asFormula, diffWeaken(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>2 & z<0 -> y>0".asFormula
  }

  it should "introduce true if there is no evolution domain constraint" in {
    val result = proveBy("[{x'=1}]x>0".asFormula, diffWeaken(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "true -> x>0".asFormula
  }

  it should "pull out evolution domain constraint from system of ODEs" in {
    val result = proveBy("[{x'=x, y'=1 & y>2 & z<0}]y>0".asFormula, diffWeaken(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>2 & z<0 -> y>0".asFormula
  }

  it should "also work when the ODEs are interdependent" in {
    val result = proveBy("[{x'=x+y, y'=1, z'=2 & y>2 & z<0}]y>0".asFormula, diffWeaken(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>2 & z<0 -> y>0".asFormula
  }

  it should "weaken if ODE afterwards" in {
    val result = proveBy("[{x'=1}][{x'=2}]x>0".asFormula, diffWeaken(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "true -> [{x'=2}]x>0".asFormula
  }

  it should "retain single context formula" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("A>0".asFormula, "x=4".asFormula), IndexedSeq("[{x'=1&x>0}]x>0".asFormula)), diffWeaken(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "A>0".asFormula
    result.subgoals.head.succ should contain only "x>0 -> x>0".asFormula
  }

  it should "retain context" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("A>0&A>1".asFormula, "B=1".asFormula, "C=2&D=3".asFormula, "x=4".asFormula), IndexedSeq("[{x'=1&x>0}]x>0".asFormula)), diffWeaken(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("A>0&A>1".asFormula, "B=1".asFormula, "C=2&D=3".asFormula)
    result.subgoals.head.succ should contain only "x>0 -> x>0".asFormula
  }

  it should "work if not sole formula in succedent" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("A>0&A>1".asFormula, "B=1".asFormula, "C=2&D=3".asFormula, "x=4".asFormula), IndexedSeq("Blah=1".asFormula, "[{x'=1&x>0}]x>0".asFormula, "Blub=3".asFormula)), diffWeaken(2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("A>0&A>1".asFormula, "B=1".asFormula, "C=2&D=3".asFormula)
    result.subgoals.head.succ should contain only ("Blah=1".asFormula, "Blub=3".asFormula, "x>0 -> x>0".asFormula)
  }

  "Differential effect" should "introduce a differential assignment" in {
    val result = proveBy("[{x'=5 & x>2}]x>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=5 & x>2}][x':=5;]x>0".asFormula
  }

  it should "introduce differential assignments exhaustively" in {
    val result = proveBy("[{x'=5, y'=x}]x>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=5, y'=x}][y':=x;][x':=5;]x>0".asFormula
  }

  it should "introduce differential assignments whatever the names (manual useAt)" in {
    val result = proveBy("[{z'=5, y'=z}]z>0".asFormula, useAt("DE differential effect (system)")(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{y'=z,z'=5}][z':=5;]z>0".asFormula
  }

  it should "introduce differential assignments in long cases whatever the names (manual useAt)" in {
    val result = proveBy("[{z'=5, y'=z, u'=v}]z>0".asFormula, useAt("DE differential effect (system)")(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{y'=z,u'=v,z'=5}][z':=5;]z>0".asFormula
  }

  it should "introduce differential assignments exhaustively whatever the names" in {
    val result = proveBy("[{z'=5, y'=3}]z>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{z'=5, y'=3}][y':=3;][z':=5;]z>0".asFormula
  }

  it should "introduce differential assignments exhaustively for x" in {
    val result = proveBy("[{x'=5, y'=3}]x>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=5, y'=3}][y':=3;][x':=5;]x>0".asFormula
  }

  it should "introduce differential assignments exhaustively whatever the names even mutually recursive" in {
    val result = proveBy("[{z'=5, y'=z}]z>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{z'=5, y'=z}][y':=z;][z':=5;]z>0".asFormula
  }

  it should "introduce differential assignments exhaustively despite evolution domain" in {
    val result = proveBy("[{x'=5, y'=x & x>2}]x>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=5, y'=x & x>2}][y':=x;][x':=5;]x>0".asFormula
  }

  it should "introduce a differential assignment when the postcondition is primed" in {
    val result = proveBy("[{x'=5 & x>2}](x>0)'".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=5 & x>2}][x':=5;](x>0)'".asFormula
  }

  it should "introduce differential assignments when the postcondition is primed" in {
    val result = proveBy("[{x'=5, y'=2 & x>2}](x>0)'".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=5, y'=2 & x>2}][y':=2;][x':=5;](x>0)'".asFormula
  }

  it should "introduce a differential assignment in context" in {
    val result = proveBy("[x:=0;][{x'=5 & x>2}]x>0".asFormula, DE(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=0;][{x'=5 & x>2}][x':=5;]x>0".asFormula
  }

  it should "alpha rename if necessary" in {
    val result = proveBy("[{y'=5 & y>2}]y>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{y'=5 & y>2}][y':=5;]y>0".asFormula
  }

  it should "alpha rename with remaining ODEs mentioning original x from axiom" in {
    val result = proveBy("[{y'=5,x'=2 & y>2 & x>0}]y>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{y'=5, x'=2 & y>2 & x>0}][x':=2;][y':=5;]y>0".asFormula
  }

  "Dassignb" should "assign isolated single variable" in {
    val result = proveBy("[x':=v;]x'>=0".asFormula, Dassignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "v>=0".asFormula
  }

  it should "assign isolated single const" in {
    val result = proveBy("[u':=b();]u'>=0".asFormula, Dassignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "b()>=0".asFormula
  }
  it should "assign isolated single const 2" in {
    val result = proveBy("[x':=v();]x'>=0".asFormula, Dassignb(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "v()>=0".asFormula
  }

  it should "assign single const" in {
    val result = proveBy("[{x'=v()}][x':=v();]x'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v()}]v()>=0".asFormula
  }
  it should "assign single variable" in {
    val result = proveBy("[{x'=v}][x':=v;]x'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v}]v>=0".asFormula
  }

  it should "prove single variable" in withMathematica { qeTool =>
    proveBy("v>=0 -> [{x'=v}][x':=v;]x'>=0".asFormula, Dassignb(1, 1::1::Nil) & implyR(1) & abstractionb(1) & QE) shouldBe 'proved
  }

  it should "prove single const" in withMathematica { qeTool =>
    proveBy("v()>=0 -> [{x'=v()}][x':=v();]x'>=0".asFormula, Dassignb(1, 1::1::Nil) & implyR(1) & abstractionb(1) & QE) shouldBe 'proved
  }

  it should "assign flat variable" in {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::1::Nil) & Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v,v'=a&true}]a>=0".asFormula
  }

  it should "assign flat const" in {
    val result = proveBy("[{x'=v,v'=a()}][v':=a();][x':=v;]v'>=0".asFormula, Dassignb(1, 1::1::Nil) & Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v,v'=a()&true}]a()>=0".asFormula
  }

  it should "assign nested variabe" in {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v,v'=a&true}][x':=v;]a>=0".asFormula
  }

  it should "assign nested variable" in {
    val result = proveBy("[{x'=v,v'=a}][v':=a;][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v,v'=a&true}][x':=v;]a>=0".asFormula
  }

  it should "assign nested const" in {
    val result = proveBy("[{x'=v,v'=a()}][v':=a();][x':=v;]v'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v,v'=a()&true}][x':=v;]a()>=0".asFormula
  }

  it should "assign nested separate variable" in {
    val result = proveBy("[{x'=v,y'=a}][y':=a;][x':=v;]y'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v,y'=a&true}][x':=v;]a>=0".asFormula
  }

  it should "assign nested separate const" in {
    val result = proveBy("[{x'=v,y'=a()}][y':=a();][x':=v;]y'>=0".asFormula, Dassignb(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=v,y'=a()&true}][x':=v;]a()>=0".asFormula
  }

  "diffInd" should "auto-prove x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) & diffInd()(1)
    ) shouldBe 'proved
  }

  it should "behave as DI rule on x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) & diffInd('none)(1)
    )
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>=5".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "x>=5".asFormula
    result.subgoals.last.ante should contain only ("x>=5".asFormula, "true".asFormula)
    result.subgoals.last.succ should contain only "[{x'=2}](x>=5)'".asFormula
  }

  it should "behave as diffInd rule on x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) & diffInd('diffInd)(1)
    )
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>=5".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "x>=5".asFormula
    result.subgoals.last.ante should contain only ("x>=5".asFormula, "true".asFormula)
    result.subgoals.last.succ should contain only "[x':=2;]x'>=0".asFormula
  }

  it should "auto-prove x>=5 -> [{x'=2&x<=10}](5<=x)" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=10}](5<=x)".asFormula)),
      implyR(1) & diffInd()(1)
    ) shouldBe 'proved
  }

  it should "auto-prove x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula)),
      implyR(1) & diffInd()(1)
    ) shouldBe 'proved
  }

  it should "behave as DI on x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula)),
      implyR(1) & diffInd('none)(1)
    )
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x*x+y*y>=8".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "x*x+y*y>=8".asFormula
    result.subgoals.last.ante should contain only ("x*x+y*y>=8".asFormula, "true".asFormula)
    result.subgoals.last.succ should contain only "[{x'=5*y,y'=-5*x}](x*x+y*y>=8)'".asFormula
  }

  it should "behave as diffInd on x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula)),
      implyR(1) & diffInd('diffInd)(1)
    )
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x*x+y*y>=8".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "x*x+y*y>=8".asFormula
    result.subgoals.last.ante should contain only ("x_0*x_0+y_0*y_0>=8".asFormula, "true".asFormula)
    result.subgoals.last.succ should contain only "[y':=-5*x;][x':=5*y;]x'*x+x*x'+(y'*y+y*y')>=0".asFormula
  }

  it should "prove x>=5 |- [x:=x+1][{x'=2}]x>=5" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq("x>=5".asFormula), IndexedSeq("[x:=x+1;][{x'=2}]x>=5".asFormula)),
      assignb(1) & diffInd()(1)
    ) shouldBe 'proved
  }

  it should "prove x>=5 |- [x:=x+1][{x'=2}]x>=5 in reverse" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq("x>=5".asFormula), IndexedSeq("[x:=x+1;][{x'=2}]x>=5".asFormula)),
      diffInd()(1, 1::Nil) &
        assignb(1) & // handle updates
        QE
    ) shouldBe 'proved
  }

  it should "x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in {
    val result = proveBy(Sequent(IndexedSeq("x>=5".asFormula), IndexedSeq("[{x'=2}]x>=5".asFormula)),
      DifferentialTactics.diffInd('none)(1)
    )
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>=5".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "x>=5".asFormula
    result.subgoals.last.ante should contain only ("x>=5".asFormula, "true".asFormula)
    result.subgoals.last.succ should contain only "[{x'=2}](x>=5)'".asFormula
  }

  it should "x>=5 -> [{x'=2}]x>=5 in context" taggedAs KeYmaeraXTestTags.SummaryTest in {
    val result = proveBy(Sequent(IndexedSeq("x>=5".asFormula), IndexedSeq("[x:=x+1;][{x'=2}]x>=5".asFormula)),
      DifferentialTactics.diffInd('none)(1, 1::Nil)
    )
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>=5".asFormula
    result.subgoals.head.succ should contain only "[x:=x+1;](true->x>=5&[{x'=2}](x>=5)')".asFormula
  }

  it should "x>=5 -> [{x'=2&x>7}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x>=5".asFormula), IndexedSeq("[{x'=2 & x>7}]x>=5".asFormula)),
      DifferentialTactics.diffInd('diffInd)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>=5".asFormula, "x>7".asFormula)
    result.subgoals.head.succ should contain only "x>=5".asFormula
    result.subgoals.last.ante should contain only ("x_0>=5".asFormula, "x_0>7".asFormula, "x>7".asFormula)
    result.subgoals.last.succ should contain only "[x':=2;]x'>=0".asFormula
  }

  it should "keep context around" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("x>=5&A()>0 -> [{x'=A()}]x>=5".asFormula)),
      implyR(1) & diffInd('diffInd)(1)
    )
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>=5&A()>0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "x>=5".asFormula
    result.subgoals.last.ante should contain only ("x>=5&A()>0".asFormula, "true".asFormula)
    result.subgoals.last.succ should contain only "[x':=A();]x'>=0".asFormula
  }

  it should "prove x >= 0 & y >= 0 & z >= 0 -> [{x'=y, y'=z, z'=x^2 & y >=0}]x>=0" in withMathematica { qeTool =>
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

    proveBy(KeYmaeraXProblemParser(input), implyR(1) & diffInd('full)(1)) shouldBe 'proved
  }

  it should "prove with and without frame constraint y'=0" in withMathematica { tool =>
    proveBy(Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=2 & x>=0}]x>=y".asFormula)), diffInd('full)('R)) shouldBe 'proved
    proveBy(Sequent(IndexedSeq("x=y".asFormula), IndexedSeq("[{x'=2, y'=0 & x>=0}]x>=y".asFormula)), diffInd('full)('R)) shouldBe 'proved
  }

  "Dvariable" should "work when the Differential() occurs in a formula without []'s" in withMathematica { qeTool =>
    // Equal(Differential(Variable("x")), "1".asTerm)
    val result = proveBy("(x)'=1".asFormula, Derive.Dvar(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    // Equal(DifferentialSymbol(Variable("x")), "1".asTerm)
    result.subgoals.head.succ should contain only "x'=1".asFormula
  }

  it should "alpha rename if necessary" in withMathematica { qeTool =>
    val result = proveBy("(z)'=1".asFormula, Derive.Dvar(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "z'=1".asFormula
  }

  it should "work in context" in withMathematica { qeTool =>
    val result = proveBy("[y:=1;](z)'=1".asFormula, Derive.Dvar(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y:=1;]z'=1".asFormula
  }

  it should "work in a context that binds the differential symbol" in withMathematica { qeTool =>
    val result = proveBy("[z':=1;](z)'=1".asFormula, Derive.Dvar(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z':=1;]z'=1".asFormula
  }

  it should "work in a context that binds x" in {
    val result = proveBy("[z:=1;](z)'=1".asFormula, Derive.Dvar(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z:=1;]z'=1".asFormula
  }

  it should "work with other formulas around" in {
    val result = proveBy(Sequent(IndexedSeq("a>0".asFormula), IndexedSeq("b<0".asFormula, "[z:=1;](z)'=1".asFormula, "c=0".asFormula)), Derive.Dvar(2, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a>0".asFormula
    result.subgoals.head.succ should contain only ("b<0".asFormula, "[z:=1;]z'=1".asFormula, "c=0".asFormula)
  }

  "DC" should "cut in a simple formula" in withMathematica { qeTool =>
    val result = proveBy("[{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2 & true & x>0}]x>=0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[{x'=2}]x>0".asFormula
  }

  it should "retain context for showing condition" in withMathematica { qeTool =>
    val result = proveBy(
      Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("y<0".asFormula, "[{x'=2}]x>=0".asFormula, "z=0".asFormula)),
      DC("x>0".asFormula)(2))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only ("y<0".asFormula, "[{x'=2 & true & x>0}]x>=0".asFormula, "z=0".asFormula)
    result.subgoals(1).ante should contain only "x>0".asFormula
    result.subgoals(1).succ should contain only ("y<0".asFormula, "[{x'=2}]x>0".asFormula, "z=0".asFormula)
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ODEProduct" in withMathematica { qeTool =>
    val result = proveBy("[{x'=2, y'=3, z'=4 & y>4}]x>0".asFormula, DC("x>1".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2,y'=3,z'=4 & (y>4&x>1)}]x>0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[{x'=2,y'=3,z'=4 & y>4}]x>1".asFormula
  }

  it should "cut formula into rightmost ODE in ODEProduct, even if constraint empty" in withMathematica { qeTool =>
    val result = proveBy("[{x'=2, y'=3}]x>0".asFormula, DC("x>1".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2,y'=3 & (true&x>1)}]x>0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[{x'=2, y'=3}]x>1".asFormula
  }
  it should "preserve existing evolution domain constraint" in withMathematica { qeTool =>
    val result = proveBy("[{x'=2 & x>=0 | y<z}]x>=0".asFormula, DC("x>0".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2 & (x>=0 | y<z) & x>0}]x>=0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[{x'=2 & x>=0 | y<z}]x>0".asFormula
  }

  it should "work in context" ignore withMathematica { qeTool =>
    val result = proveBy("[x:=3;][{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1, 1::Nil))

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=3;][{x'=2}]x>0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[x:=3;][{x'=2 & true & x>0}]x>=0".asFormula
  }

  "diffCut" should "cut in a simple formula" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>=0".asFormula)),
      diffCut("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & true & x>0}]x>=0".asFormula
    result.subgoals(1).ante should contain only "x>0".asFormula
    result.subgoals(1).succ should contain only "[{x'=2}]x>0".asFormula
  }

  //@todo requires better UnifyUSCalculus CMon ->
  it should "cut in a simple formula in context" ignore withMathematica { qeTool =>
    val result = proveBy("x>0 -> [{x'=2}]x>=0".asFormula, diffCut("x>0".asFormula)(1, 1::Nil))
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0 -> [{x'=2 & true & x>0}]x>=0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "x>0 -> [{x'=2}]x>0".asFormula
  }

  it should "retain context for showing condition" in withMathematica { qeTool =>
    val result = proveBy(
      Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("y<0".asFormula, "[{x'=2}]x>=0".asFormula, "z=0".asFormula)),
      diffCut("x>0".asFormula)(2))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only ("y<0".asFormula, "[{x'=2 & true & x>0}]x>=0".asFormula, "z=0".asFormula)
    result.subgoals(1).ante should contain only "x>0".asFormula
    result.subgoals(1).succ should contain only ("y<0".asFormula, "[{x'=2}]x>0".asFormula, "z=0".asFormula)
  }

  it should "not branch formulas in context" in withMathematica { qeTool =>
    val result = proveBy(
      Sequent(IndexedSeq("x>0->x>0".asFormula), IndexedSeq("y<0&z=1".asFormula, "[{x'=2}]x>=0".asFormula, "z=0".asFormula)),
      diffCut("x>0".asFormula)(2))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0->x>0".asFormula
    result.subgoals.head.succ should contain only ("y<0&z=1".asFormula, "[{x'=2 & true & x>0}]x>=0".asFormula, "z=0".asFormula)
    result.subgoals(1).ante should contain only "x>0->x>0".asFormula
    result.subgoals(1).succ should contain only ("y<0&z=1".asFormula, "[{x'=2}]x>0".asFormula, "z=0".asFormula)
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ODEProduct" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x>1".asFormula), IndexedSeq("[{x'=2, y'=3, z'=4 & y>4}]x>0".asFormula)),
      diffCut("x>1".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "[{x'=2,y'=3,z'=4 & (y>4&x>1)}]x>0".asFormula
    result.subgoals(1).ante should contain only "x>1".asFormula
    result.subgoals(1).succ should contain only "[{x'=2,y'=3,z'=4 & y>4}]x>1".asFormula
  }
  it should "cut formula into rightmost ODE in ODEProduct, even if constraint empty" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x>1".asFormula), IndexedSeq("[{x'=2, y'=3}]x>0".asFormula)),
      diffCut("x>1".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "[{x'=2,y'=3 & (true&x>1)}]x>0".asFormula
    result.subgoals(1).ante should contain only "x>1".asFormula
    result.subgoals(1).succ should contain only "[{x'=2,y'=3}]x>1".asFormula
  }
  it should "preserve existing evolution domain constraint" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2 & x>=0 | y<z}]x>=0".asFormula)),
      diffCut("x>0".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & (x>=0 | y<z) & x>0}]x>=0".asFormula
    result.subgoals(1).ante should contain only "x>0".asFormula
    result.subgoals(1).succ should contain only "[{x'=2 & (x>=0 | y<z)}]x>0".asFormula
  }

  it should "introduce ghosts when special function old is used" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("[{x'=2 & x>=0 | y<z}]x>=0".asFormula)),
      diffCut("x>=old(x)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x_0=x".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & (x>=0 | y<z) & x>=x_0}]x>=0".asFormula
    result.subgoals(1).ante should contain only "x_0=x".asFormula
    result.subgoals(1).succ should contain only "[{x'=2 & (x>=0 | y<z)}]x>=x_0".asFormula
  }

  it should "auto-generate names for term-ghosts when special function old is used" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq("[{x'=2 & x>=0 | y<z}]x>=0".asFormula)),
      diffCut("x>=old(x^2+4)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "old=x^2+4".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & (x>=0 | y<z) & x>=old}]x>=0".asFormula
    result.subgoals(1).ante should contain only "old=x^2+4".asFormula
    result.subgoals(1).succ should contain only "[{x'=2 & (x>=0 | y<z)}]x>=old".asFormula
  }

  it should "retain existing conditions and introduce ghosts when special function old is used" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>=0".asFormula)),
      diffCut("x>=old(x)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>0".asFormula, "x_0=x".asFormula)
    result.subgoals.head.succ should contain only "[{x'=2 & true & x>=x_0}]x>=0".asFormula
    result.subgoals(1).ante should contain only ("x>0".asFormula, "x_0=x".asFormula)
    result.subgoals(1).succ should contain only "[{x'=2}]x>=x_0".asFormula
  }

  it should "cut in single formula with multiple old variables" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("dx^2+dy^2=1".asFormula), IndexedSeq("[{dx'=0,dy'=0}]dx^2+dy^2=1".asFormula)),
      diffCut("dx=old(dx) & dy=old(dy)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("dx^2+dy^2=1".asFormula, "dx_0=dx".asFormula, "dy_0=dy".asFormula)
    result.subgoals.head.succ should contain only "[{dx'=0,dy'=0&true&dx=dx_0&dy=dy_0}]dx^2+dy^2=1".asFormula
    result.subgoals(1).ante should contain only ("dx^2+dy^2=1".asFormula, "dx_0=dx".asFormula, "dy_0=dy".asFormula)
    result.subgoals(1).succ should contain only "[{dx'=0,dy'=0}](dx=dx_0&dy=dy_0)".asFormula
  }

  it should "cut in multiple formulas" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("v>=0".asFormula, "x>0".asFormula), IndexedSeq("[{x'=v,v'=2}]x>=0".asFormula)),
      diffCut("v>=0".asFormula, "x>=old(x)".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals.head.ante should contain only ("v>=0".asFormula, "x>0".asFormula, "x_0=x".asFormula)
    result.subgoals.head.succ should contain only "[{x'=v,v'=2 & (true & v>=0) & x>=x_0}]x>=0".asFormula
    result.subgoals(1).ante should contain only ("v>=0".asFormula, "x>0".asFormula)
    result.subgoals(1).succ should contain only "[{x'=v,v'=2}]v>=0".asFormula
    result.subgoals(2).ante should contain only ("v>=0".asFormula, "x>0".asFormula, "x_0=x".asFormula)
    result.subgoals(2).succ should contain only "[{x'=v,v'=2 & true & v>=0}]x>=x_0".asFormula
  }

  "diffInvariant" should "cut in a simple formula" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>=0".asFormula)),
      diffInvariant("x>0".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & true & x>0}]x>=0".asFormula
  }

  //@todo requires better UnifyUSCalculus CMon ->
  it should "cut in a simple formula in context" ignore withMathematica { qeTool =>
    val result = proveBy("x>0 -> [{x'=2}]x>=0".asFormula, diffInvariant("x>0".asFormula)(1, 1::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0 -> [{x'=2 & true & x>0}]x>=0".asFormula
  }

  it should "cut in single formulas with old" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("v>=0".asFormula, "x>0".asFormula), IndexedSeq("[{x'=v,v'=2}]x>=0".asFormula)),
      diffInvariant("v>=old(v)".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("v>=0".asFormula, "x>0".asFormula, "v_0=v".asFormula)
    result.subgoals.head.succ should contain only "[{x'=v,v'=2 & (true & v>=v_0)}]x>=0".asFormula
  }

  it should "cut in single formula with multiple old variables" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("dx^2+dy^2=1".asFormula), IndexedSeq("[{dx'=0,dy'=0}]dx^2+dy^2=1".asFormula)),
      diffInvariant("dx=old(dx) & dy=old(dy)".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("dx^2+dy^2=1".asFormula, "dx_0=dx".asFormula, "dy_0=dy".asFormula)
    result.subgoals.head.succ should contain only "[{dx'=0,dy'=0&true&dx=dx_0&dy=dy_0}]dx^2+dy^2=1".asFormula
  }

  it should "cut in multiple formulas" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("v>=0".asFormula, "x>0".asFormula), IndexedSeq("[{x'=v,v'=2}]x>=0".asFormula)),
      diffInvariant("v>=0".asFormula, "x>0".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("v>=0".asFormula, "x>0".asFormula)
    result.subgoals.head.succ should contain only "[{x'=v,v'=2 & (true & v>=0) & x>0}]x>=0".asFormula
  }

  it should "cut in multiple formulas with old" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("v>=0".asFormula, "x>0".asFormula), IndexedSeq("[{x'=v,v'=2}]x>=0".asFormula)),
      diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("v>=0".asFormula, "x>0".asFormula, "x_0=x".asFormula)
    result.subgoals.head.succ should contain only "[{x'=v,v'=2 & (true & v>=0) & x>=x_0}]x>=0".asFormula
  }

  it should "cut in time as needed by diffSolve" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("t=0".asFormula), IndexedSeq("[{x'=2,t'=0*t+1}]x>=0".asFormula)),
      diffInvariant("t>=0".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "t=0".asFormula
    result.subgoals.head.succ should contain only "[{x'=2,t'=0*t+1 & true & t>=0}]x>=0".asFormula
  }

  it should "fail if any of the formulas is not an invariant" in withMathematica { qeTool =>
    a [BelleError] should be thrownBy proveBy(
      Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=v,v'=2}]x>=0".asFormula)),
      diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1))
  }

  it should "let us directly prove variable x+y^2*3-z = x+y^2*3-z by abbreviation" in withMathematica { qeTool =>
    proveBy("x+y^2*3-z=x+y^2*3-z".asFormula, let(FuncOf(Function("s_",None,Unit,Real),Nothing), "x+y^2*3-z".asTerm, by(DerivedAxioms.equalReflex))) shouldBe 'proved
  }

  it should "prove const [x':=5;](x+c())'>=0 directly" in withMathematica { qeTool =>
    proveBy("[x':=5;](x+c())'>=0".asFormula, derive(1,1::0::Nil) & Dassignb(1) & QE) shouldBe 'proved
  }

  it should "probably not prove variable [x':=5;](x+y)'>=0 unless derive is too powerful" in withMathematica { qeTool =>
    val result = proveBy("[x':=5;](x+y)'>=0".asFormula, derive(1,1::0::Nil) & Dassignb(1))
    result.isProved shouldBe false
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "5+y'>=0".asFormula
  }

  it should "prove const [x':=5;](x+c())'>=0" in withMathematica { qeTool =>
    proveBy("[x':=5;](x+c())'>=0".asFormula,
      derive(1,1::0::Nil) & Dassignb(1) & QE) shouldBe 'proved
  }

  it should "let us prove variable [x':=5;](x+y)'>=0" ignore withMathematica { qeTool =>
    //@note proof waited too long. Should have gone constant before diffind
    proveBy("[x':=5;](x+y)'>=0".asFormula,
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), derive(1,1::0::Nil) & Dassignb(1) & QE)) shouldBe 'proved
  }

  it should "prove const [{x'=5}](x+c())'>=0" in withMathematica { qeTool =>
    proveBy("[{x'=5}](x+c())'>=0".asFormula,
      derive(1,1::0::Nil) & DE(1) & G(1) & Dassignb(1) & QE) shouldBe 'proved
  }

  it should "let us prove variable [{x'=5}](x+y)'>=0" ignore withMathematica { qeTool =>
    //@note proof waited too long. Should have gone constant before diffind
    proveBy("[{x'=5}](x+y)'>=0".asFormula,
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), derive(1,1::0::Nil) & DE(1) & G(1) & Dassignb(1) & QE)) shouldBe 'proved
  }

  it should "prove const x+c()>=0 -> [{x'=5}]x+c()>=0" in withMathematica { qeTool =>
    proveBy("x+c()>=0 -> [{x'=5}]x+c()>=0".asFormula,
      implyR(1) & diffInd('full)(1)) shouldBe 'proved
  }

  it should "prove const x+c()>=0 -> [{x'=5}]x+c()>=0 manual" in withMathematica { qeTool =>
    proveBy("x+c()>=0 -> [{x'=5}]x+c()>=0".asFormula,
      implyR(1) & diffInd('none)(1) <(close , derive(1,1::Nil) & DE(1) & G(1) & Dassignb(1) & QE)) shouldBe 'proved
  }

  it should "let us prove variable x+y>=0 -> [{x'=5}]x+y>=0 manual" in withMathematica { qeTool =>
    proveBy("x+y>=0 -> [{x'=5}]x+y>=0".asFormula, implyR(1) &
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), diffInd('none)(1) <(close , derive(1,1::Nil) & DE(1) & G(1) & Dassignb(1) & QE))) shouldBe 'proved
  }

  it should "let us prove variable x+y>=0 -> [{x'=5}]x+y>=0" in withMathematica { qeTool =>
    proveBy("x+y>=0 -> [{x'=5}]x+y>=0".asFormula, implyR(1) &
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("y"), diffInd('full)(1))) shouldBe 'proved
  }

  it should "let us prove variable x+y+z>=0 -> [{x'=5,y'=2}]x+y+z>=0" in withMathematica { qeTool =>
    proveBy("x+y+z>=0 -> [{x'=5,y'=2}]x+y+z>=0".asFormula, implyR(1) &
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("z"), diffInd('full)(1))) shouldBe 'proved
  }

  it should "let us prove variable x+z>=0&y+z>=0 -> [{x'=5,y'=2}](x+z>=0&y+z>=0)" in withMathematica { qeTool =>
    proveBy("x+z>=0&y+z>=0 -> [{x'=5,y'=2}](x+z>=0&y+z>=0)".asFormula, implyR(1) &
      let(FuncOf(Function("c",None,Unit,Real),Nothing), Variable("z"), diffInd('full)(1))) shouldBe 'proved
  }

  it should "prove const a()>=0 & x>=0 & v>=0 -> [{x'=v,v'=a()}]v>=0 directly" in withMathematica { qeTool =>
    proveBy("a()>=0 & x>=0 & v>=0 -> [{x'=v,v'=a()}]v>=0".asFormula, implyR(1) & diffInd()(1)) shouldBe 'proved
  }

  it should "let us prove variable x>=0 & v>=0 -> [{x'=v}]x>=0" in withMathematica { qeTool =>
    proveBy("x>=0 & v>=0 -> [{x'=v}]x>=0".asFormula, implyR(1) &
      let(FuncOf(Function("v",None,Unit,Real),Nothing), Variable("v"), diffInd('full)(1))) shouldBe 'proved
  }

  it should "let us prove variable a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0" in withMathematica { qeTool =>
    proveBy("a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0".asFormula, implyR(1) & let(FuncOf(Function("a",None,Unit,Real),Nothing), Variable("a"), diffInd('full)(1))) shouldBe 'proved
  }

  it should "perhaps prove variable a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0 directly if diffInd were powerful enough" in withMathematica { qeTool =>
    proveBy("a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0".asFormula, implyR(1) & diffInd('full)(1)) shouldBe 'proved
  }

  it should "let us prove variable a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0 despite silly names" in withMathematica { qeTool =>
    proveBy("a>=0 & x>=0 & v>=0 -> [{x'=v,v'=a}]v>=0".asFormula, implyR(1) & let(FuncOf(Function("gobananas",None,Unit,Real),Nothing), Variable("a"), diffInd('full)(1))) shouldBe 'proved
  }


  private def mockTactic(expected: Sequent) = new SingleGoalDependentTactic("mock") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      sequent shouldBe expected
      skip
    }
  }

  private def dconstifyTest(in: Sequent, expected: Sequent) = {
    try {
      proveBy(in, DifferentialTactics.Dconstify(mockTactic(expected))(1))
    } catch {
      // proveBy may throw an expected exception sometimes -> filter the expected one
      case ex: Throwable if ex.getCause != null && ex.getCause.getMessage.contains("Unless proved, uniform substitutions instances cannot introduce free variables") => // expected
      case ex: Throwable => throw ex
    }
  }

  "Differential introduce constants" should "replace a with a() in v'=a" in {
    dconstifyTest(
      Sequent(IndexedSeq(), IndexedSeq("[{v'=a}]v=v0()+a*t()".asFormula)),
      Sequent(IndexedSeq(), IndexedSeq("[{v'=a()}]v=v0()+a()*t()".asFormula)))
  }

  it should "not self-replace a() with a() in v'=a()" in {
    dconstifyTest(
      Sequent(IndexedSeq(), IndexedSeq("[{v'=a()}]v=v0()+a()*t()".asFormula)),
      Sequent(IndexedSeq(), IndexedSeq("[{v'=a()}]v=v0()+a()*t()".asFormula)))
  }

  it should "not replace a with a() when a is not free in p" in {
    dconstifyTest(
      Sequent(IndexedSeq(), IndexedSeq("[{v'=a}]v>0".asFormula)),
      Sequent(IndexedSeq(), IndexedSeq("[{v'=a}]v>0".asFormula)))
  }

  it should "replace every free occurrence of a with a() everywhere in the sequent" in {
    dconstifyTest(
      Sequent(IndexedSeq("v>=0".asFormula, "a=0".asFormula, "\\forall a a<0".asFormula), IndexedSeq("[{v'=a}]v=v_0()+a*t()".asFormula, "a>=0".asFormula, "[a:=2;]v>0".asFormula)),
      Sequent(IndexedSeq("v>=0".asFormula, "a()=0".asFormula, "\\forall a a<0".asFormula), IndexedSeq("[{v'=a()}]v=v_0()+a()*t()".asFormula, "a()>=0".asFormula, "[a:=2;]v>0".asFormula)))
  }

  it should "replace every free occurrence of b (only in p) with b() everywhere in the sequent" in {
    dconstifyTest(
      Sequent(IndexedSeq("v>=0".asFormula, "a=0".asFormula, "b=2".asFormula, "\\forall b b<0".asFormula), IndexedSeq("[{v'=a}](v>0 & b<0)".asFormula, "a>=0".asFormula, "[a:=2;]v>0".asFormula)),
      Sequent(IndexedSeq("v>=0".asFormula, "a=0".asFormula, "b()=2".asFormula, "\\forall b b<0".asFormula), IndexedSeq("[{v'=a}](v>0& b()<0)".asFormula, "a>=0".asFormula, "[a:=2;]v>0".asFormula))
    )
  }

  "DG" should "add y'=1 to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, DG("{y'=0*y+1}".asDifferentialProgram)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=0*y+1}]x>0".asFormula
  }

  it should "add z'=1 to [y'=2]y>0" in {
    val result = proveBy("[{y'=2}]y>0".asFormula, DG("{z'=0*z+1}".asDifferentialProgram)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists z [{y'=2,z'=0*z+1}]y>0".asFormula
  }

  it should "add x'=1 to [y'=2]y>0" in {
    val result = proveBy("[{y'=2}]y>0".asFormula, DG("{x'=0*x+1}".asDifferentialProgram)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists x [{y'=2,x'=0*x+1}]y>0".asFormula
  }

  it should "add y'=3*y+10 to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, DG("{y'=3*y+10}".asDifferentialProgram)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=3*y+10}]x>0".asFormula
  }

  it should "add y'=3*y+z() to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, DG("{y'=3*y+z()}".asDifferentialProgram)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=3*y+z()}]x>0".asFormula
  }

  it should "preserve evolution domain" in {
    val result = proveBy("[{x'=2 & x>=0}]x>0".asFormula, DG("{y'=3*y+10}".asDifferentialProgram)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=3*y+10 & x>=0}]x>0".asFormula
  }

  it should "work with other formulas around" in {
    val result = proveBy(Sequent(IndexedSeq("a>1".asFormula), IndexedSeq("[{x'=2 & x>=0}]x>0".asFormula, "b=2".asFormula)),
      DG("{y'=3*y+10}".asDifferentialProgram)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a>1".asFormula
    result.subgoals.head.succ should contain only ("\\exists y [{x'=2,y'=3*y+10 & x>=0}]x>0".asFormula, "b=2".asFormula)
  }

  it should "do basic unification" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, DifferentialTactics.diffGhost("{t'=0*t+1}".asDifferentialProgram, "0".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "t=0".asFormula
    result.subgoals.head.succ should contain only "[{x'=2,t'=0*t+1}]x>0".asFormula
  }

  it should "do fancy unification for proving x>0->[{x'=-x}]x>0 positionally" in withMathematica { qeTool =>
    val result = proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) & DA("{y'=(1/2)*y}".asDifferentialProgram, "x*y^2=1".asFormula)(1) <(
      QE
      ,
      diffInd()(1, 1::Nil) & QE
      ))
    result shouldBe 'proved
  }

  it should "do fancy unification for proving x>0->[{x'=-x}]x>0" in withMathematica { qeTool =>
    val result = proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) & DA("{y'=(1/2)*y+0}".asDifferentialProgram, "x*y^2=1".asFormula)(1) <(
      QE
      ,
      implyR(1) & diffInd()(1) & QE
      ))
    result shouldBe 'proved
  }

  it should "do fancy unification for proving x>0->[{x'=-x}]x>0 twist" in withMathematica { qeTool =>
    val result = proveBy("x>0->[{x'=-x}]x>0".asFormula, implyR(1) & DA("{y'=(1/2)*y+0}".asDifferentialProgram, "x*y^2=1".asFormula)(1) <(
      QE
      ,
      implyR(1) & diffInd()(1) & QE
      ))
    result shouldBe 'proved
  }

  it should "do fancy unification for proving x>0->[{x'=x}]x>0" in withMathematica { qeTool =>
    val result = proveBy("x>0->[{x'=x}]x>0".asFormula, implyR(1) & DA("{y'=(-1/2)*y+0}".asDifferentialProgram, "x*y^2=1".asFormula)(1)
      <(
      QE
      ,
      implyR(1) & diffInd()(1) & QE
      ))
    result shouldBe 'proved
  }

  it should "prove x>0->[{x'=-x+1}]x>0 by ghosts" in withMathematica { qeTool =>
    val result = proveBy("x>0->[{x'=-x+1}]x>0".asFormula, implyR(1) & DA("{y'=(1/2)*y+0}".asDifferentialProgram, "x*y^2>0".asFormula)(1) <(
      QE
      ,
      diffInd()(1, 1::Nil) & QE
      ))
    result shouldBe 'proved
  }

  it should "prove x>0&a<0&b>=0->[{x'=a*x+b}]x>0 by ghosts" in withMathematica { qeTool =>
    val result = proveBy("x>0&a<0&b>=0->[{x'=a*x+b}]x>0".asFormula, implyR(1) & DA("{y'=(-a/2)*y+0}".asDifferentialProgram, "x*y^2>0".asFormula)(1) <(
      QE
      ,
      diffInd()(1, 1::Nil) & QE
      ))
    result shouldBe 'proved
  }

  it should "prove x>0&a>0&b>=0->[{x'=a*x+b}]x>0 by ghosts" in withMathematica { qeTool =>
    val result = proveBy("x>0&a>0&b>=0->[{x'=a*x+b}]x>0".asFormula, implyR(1) & DA("{y'=(-a/2)*y+0}".asDifferentialProgram, "x*y^2>0".asFormula)(1) <(
      QE
      ,
      diffInd()(1, 1::Nil) & QE
      ))
    result shouldBe 'proved
  }

  it should "not allow non-linear ghosts (1)" in {
    a [BelleError] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, DG("{y'=y*y+1}".asDifferentialProgram)(1))
  }

  it should "not allow non-linear ghosts (2)" in {
    a [BelleError] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, DG("{y'=1*y+y}".asDifferentialProgram)(1))
  }

  it should "not allow ghosts that are already present in the ODE" in {
    a [BelleError] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, DG("{x'=0*x+1}".asDifferentialProgram)(1))
  }

  "DA" should "add y'=1 to [x'=2]x>0" in withMathematica { tool =>
    val s = Sequent(IndexedSeq(), IndexedSeq("[{x'=2}]x>0".asFormula))
    val tactic = DA("{y'=0*y+1}".asDifferentialProgram, "y>0 & x*y>0".asFormula)(1)
    val result = proveBy(s, tactic)

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>0".asFormula
    result.subgoals.last.ante shouldBe empty
    result.subgoals.last.succ should contain only "y>0 & x*y>0 -> [{x'=2,y'=0*y+1}](y>0 & x*y>0)".asFormula
  }

  it should "also cut in x>0 if already present in antecedent when adding y'=1 to [x'=2]x>0" in withMathematica { tool =>
    val s = Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>0".asFormula))
    val tactic = DA("{y'=0*y+1}".asDifferentialProgram, "y>0 & x*y>0".asFormula)(1)
    val result = proveBy(s, tactic)

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
    result.subgoals.last.ante should contain only "x>0".asFormula
    result.subgoals.last.succ should contain only "y>0 & x*y>0 -> [{x'=2,y'=0*y+1}](y>0 & x*y>0)".asFormula
  }

  it should "work in a simple context" ignore withMathematica { tool =>
    val s = Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("a=2 -> [{x'=2}]x>0".asFormula))
    val tactic = DA("{y'=0*y+1}".asDifferentialProgram, "y>0 & x*y>0".asFormula)(1, 1::Nil)
    val result = proveBy(s, tactic)

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
    result.subgoals.last.ante shouldBe empty
    result.subgoals.last.succ should contain only "y>0 & x*y>0 -> (a=2 -> [{x'=2,y'=0*y+1}](y>0 & x*y>0))".asFormula
  }

  it should "work in a complicated context" ignore {
    val s = Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("a=2 -> [b:=3;]<?c=5;{c'=2}>[{x'=2}]x>0".asFormula))
    val tactic = DA("{y'=0*y+1}".asDifferentialProgram, "y>0 & x*y>0".asFormula)(1, 1::1::1::Nil)
    val result = proveBy(s, tactic)

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
    result.subgoals.last.ante shouldBe empty
    result.subgoals.last.succ should contain only "y>0 & x*y>0 -> (a=2 -> [b:=3;]<?c=5;{c'=2}>[{x'=2,y'=0*y+1}](y>0 & x*y>0))".asFormula
  }

  it should "add y'=-a() to [x'=2]x>0" in withMathematica { tool =>
    val s = Sequent(IndexedSeq("a()>0".asFormula, "x>0".asFormula), IndexedSeq("[{x'=2}]x>0".asFormula))
    val tactic = DA("{y'=0*y+(-a())}".asDifferentialProgram, "x>0 & y<0".asFormula)(1)
    val result = proveBy(s, tactic)

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("a()>0".asFormula, "x>0".asFormula)
    result.subgoals.head.succ should contain only "x>0".asFormula
    result.subgoals.head.ante should contain only ("a()>0".asFormula, "x>0".asFormula)
    result.subgoals.last.succ should contain only "x>0 & y<0 -> [{x'=2,y'=0*y+-a()}](x>0 & y<0)".asFormula
  }

  it should "solve x'=x" in withMathematica { tool =>
    //val s = Sequent(IndexedSeq(), IndexedSeq("t=0 & x=1 -> [{x'=x, t'=1 & t<1}] x>0".asFormula))
    val s = Sequent(IndexedSeq(), IndexedSeq("x>0 -> [{x'=x}]x>0".asFormula))
    val t = implyR(1) & (andL('_)*) & DA("{z'=(-1/2)*z+0}".asDifferentialProgram, "x*z^2=1".asFormula)(1) <(
      closeId, implyR(1) & diffInd('full)(1))
    proveBy(s, t) shouldBe 'proved
  }

  "diffSolve" should "use provided solution" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2,t'=1}]x>b".asFormula)),
      diffSolve(Some("t=t_0+t_ & x=x_0+2*t_".asFormula))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>b".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "((true&t_>=0)&t=t_0+t_)&x=x_0+2*t_ -> x>b".asFormula
  }

  it should "add time if not present" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)),
      diffSolve(Some("x=x_0+2*t_".asFormula))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>b".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "(true&t_>=0)&x=x_0+2*t_ -> x>b".asFormula
  }

  it should "ask Mathematica if no solution provided and add time regardless" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2,t'=1}]x>b".asFormula)),
      diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>b".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "((true&t_>=0)&x=2*t_+x_0)&t=t_0+t_ -> x>b".asFormula
  }

  it should "add time if not present and ask Mathematica if no solution provided" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)),
      diffSolve(None)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>b".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "(true&t_>=0)&x=2*t_+x_0 -> x>b".asFormula
  }

  it should "add time if not present and ask Mathematica if no solution provided as part of master" in withMathematica { tool =>
    proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)), master()) shouldBe 'proved
  }

  it should "diffSolve add time if not present and ask Mathematica" in withMathematica { tool =>
    proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)), diffSolve()(1) & QE) shouldBe 'proved
  }

  it should "open diff ind x>b() |- [{x'=2}]x>b()" in withMathematica { tool =>
    proveBy(Sequent(IndexedSeq("x>b()".asFormula), IndexedSeq("[{x'=2}]x>b()".asFormula)), openDiffInd(1)) shouldBe 'proved
  }

  it should "open diff ind x>b |- [{x'=2}]x>b" in withMathematica { tool =>
    proveBy(Sequent(IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2}]x>b".asFormula)), openDiffInd(1)) shouldBe 'proved
  }

  it should "find solution for x'=v if None is provided" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0 & v>=0".asFormula), IndexedSeq("[{x'=v}]x>0".asFormula)),
      diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0 & v>=0".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "(true&t_>=0)&x=t_*v+x_0 -> x>0".asFormula
  }

  it should "use provided solution for x'=v, v'=a" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0 & v>=0 & a>0".asFormula), IndexedSeq("[{x'=v,v'=a}]x>0".asFormula)),
      diffSolve(Some("v=a*t_+v_0&x=1/2*(a*t_*t_+2*t_*v_0+2*x_0)".asFormula))(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0 & v_0>=0 & a>0".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "((true&t_>=0)&v=a*t_+v_0)&x=1/2*(a*t_*t_+2*t_*v_0+2*x_0) -> x>0".asFormula
  }

  it should "find solution for x'=v, v'=a if None is provided" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0 & v>=0 & a>0".asFormula), IndexedSeq("[{x'=v,v'=a}]x>0".asFormula)),
      diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0 & v_0>=0 & a>0".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "((true&t_>=0)&v=a*t_+v_0)&x=1/2*(a*t_^2+2*t_*v_0+2*x_0) -> x>0".asFormula
  }

  it should "work when ODE is not sole formula in succedent" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0 & v>=0 & a>0".asFormula), IndexedSeq("y=1".asFormula, "[{x'=v,v'=a}]x>0".asFormula, "z=3".asFormula)),
      diffSolve()(2))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0 & v_0>=0 & a>0".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only (
      "y=1".asFormula,
      "z=3".asFormula,
      "((true&t_>=0)&v=a*t_+v_0)&x=1/2*(a*t_^2+2*t_*v_0+2*x_0) -> x>0".asFormula)
  }

  it should "work when safety property is abstract" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("J(x,v)".asFormula), IndexedSeq("[{x'=v,v'=a}]J(x,v)".asFormula)),
      diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("J(x_0,v_0)".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "((true&t_>=0)&v=a*t_+v_0)&x=1/2*(a*t_^2+2*t_*v_0+2*x_0) -> J(x,v)".asFormula
  }

  it should "solve the simplest of all ODEs" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=1}]x>0".asFormula)), diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "(true&t_>=0)&x=t_+x_0 -> x>0".asFormula
  }

  it should "solve simple nested ODEs" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}][{x'=3}]x>0".asFormula)), diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "(true&t_>=0)&x=2*t_+x_0 -> [{x'=3}]x>0".asFormula
  }

  it should "solve complicated nested ODEs" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("v=0 & x<s & 0<T".asFormula, "t=0".asFormula, "a_0=(s-x)/T^2".asFormula), IndexedSeq("[{x'=v,v'=a_0,t'=1&v>=0&t<=T}](t>0->\\forall a (a = (v^2/(2 *(s - x)))->[{x'=v,v'=-a,t'=1 & v>=0}](x + v^2/(2*a) <= s & (x + v^2/(2*a)) >= s)))".asFormula)),
      diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("v_0=0 & x_0<s & 0<T".asFormula, "t_0=0".asFormula, "a_0=(s-x_0)/T^2".asFormula, "t__0=0".asFormula, "v_0>=0&t_0<=T".asFormula)
    result.subgoals.head.succ should contain only "((((v>=0&t<=T)&t_>=0)&t=t_0+t_)&v=a_0*t_+v_0)&x=1/2*(a_0*t_^2+2*t_*v_0+2*x_0)->t>0->\\forall a (a=v^2/(2*(s-x))->[{x'=v,v'=-a,t'=1&v>=0}](x+v^2/(2*a)<=s&x+v^2/(2*a)>=s))".asFormula
  }

  it should "increase index of existing other occurrences of initial values" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula, "x_0=b".asFormula), IndexedSeq("[{x'=1}]x>0".asFormula)), diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0".asFormula, "x_1=b".asFormula, "t__0=0".asFormula, "true".asFormula)
    result.subgoals.head.succ should contain only "(true&t_>=0)&x=t_+x_0 -> x>0".asFormula
  }

  it should "retain initial evolution domain for the sake of contradictions" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("y>0".asFormula), IndexedSeq("[{x'=1&y<=0}]x>0".asFormula)), diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("y>0".asFormula, "t__0=0".asFormula, "y<=0".asFormula)
    result.subgoals.head.succ should contain only "(y<=0&t_>=0)&x=t_+x_0 -> x>0".asFormula
  }

  it should "retain initial evolution domain for the sake of contradictions (2)" in withMathematica { tool =>
    val result = proveBy(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=1&x<0}]x>=0".asFormula)), diffSolve()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0>0".asFormula, "x_0=b".asFormula, "t__0=0".asFormula, "x_0<0".asFormula)
    result.subgoals.head.succ should contain only "(x<0&t_>=0)&x=t_+x_0 -> x>=0".asFormula
  }

  "diffUnpackEvolutionDomainInitially" should "unpack the evolution domain of an ODE as fact at time zero" in {
    val result = proveBy("[{x'=3&x>=0}]x>=0".asFormula, DifferentialTactics.diffUnpackEvolutionDomainInitially(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>=0".asFormula
    result.subgoals.head.succ should contain only "[{x'=3&x>=0}]x>=0".asFormula
  }

  "Differential Invariants" should "prove random differential invariant equations" taggedAs KeYmaeraXTestTags.IgnoreInBuildTest in withMathematica { qeTool =>
    for (i <- 1 to randomTrials) {
      val vars = IndexedSeq(Variable("x"),Variable("y"),Variable("z")) //rand.nextNames("z", 4)
      //@todo avoid divisions by zero
      val inv = rand.nextT(vars, randomComplexity, false, false, false)
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
            Some((qeTool.deriveBy(Neg(inv), y),
              qeTool.deriveBy(inv, x)))
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
              val delta = rand.nextT(vars, randomComplexity, false, false, false)
              (a:Term,b:Term) => cmp(Plus(a,delta), Plus(b,delta))
            }
            val fml = opit(inv, Number(rand.rand.nextInt(200) - 100))
            val conjecture = Imply(fml, Box(sys, fml))
            withSafeClue("Random differential invariant " + conjecture + "\n" + randClue) {
              print(conjecture)
              val result = proveBy(conjecture,
                implyR(1) & diffInd()(1))
              result shouldBe 'proved
            }
        }
      }
    }
  }

  it should "prove boring case" taggedAs KeYmaeraXTestTags.IgnoreInBuildTest in withMathematica { qeTool =>
    proveBy("z*4>=-8 -> [{x'=0,y'=0}]z*4>=-8".asFormula, implyR(1) & diffInd()(1)) shouldBe 'proved
  }
  it should "prove ^0 case" taggedAs KeYmaeraXTestTags.IgnoreInBuildTest in withMathematica { qeTool =>
    proveBy("x^0+x>=68->[{x'=0,y'=1&true}]x^0+x>=68".asFormula, implyR(1) & diffInd()(1)) shouldBe 'proved
  }
  it should "prove crazy ^0 case" taggedAs KeYmaeraXTestTags.IgnoreInBuildTest in withMathematica { qeTool =>
    proveBy("x+(y-y-(0-(0+0/1)+(41+x)^0))>=68->[{x'=0,y'=1&true}]x+(y-y-(0-(0+0/1)+(41+x)^0))>=68".asFormula, implyR(1) & diffInd()(1)) shouldBe 'proved
  }
  it should "prove crazy case" taggedAs KeYmaeraXTestTags.IgnoreInBuildTest in withMathematica { qeTool =>
    proveBy("(z+y+x)*(41/(67/x+((0+0)/y)^1))!=94->[{x'=-41/67*x,y'=41/67*x+41/67*(x+y+z)&true}](z+y+x)*(41/(67/x+((0+0)/y)^1))!=94".asFormula, implyR(1) & diffInd()(1)) shouldBe 'proved
  }

  "Open Differential Invariant" should "prove x^3>5 -> [{x'=x^3+x^4}]x^3>5" in withMathematica { qeTool =>
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "prove x^3>5 -> [{x'=x^3+x^4}]x^3>5 incontext" taggedAs(IgnoreInBuildTest) in withMathematica { qeTool =>
    proveBy("x^3>5 -> [{x'=x^3+x^4}]x^3>5".asFormula, openDiffInd(1, 1::Nil)) shouldBe 'proved
  }

  it should "prove 5<x^3 -> [{x'=x^3+x^4}]5<x^3" in withMathematica { qeTool =>
    proveBy("5<x^3 -> [{x'=x^3+x^4}]5<x^3".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  it should "prove x^3>5 -> [{x'=7*x^3+x^8}]x^3>5" in withMathematica { qeTool =>
    proveBy("x^3>5 -> [{x'=7*x^3+x^8}]x^3>5".asFormula, implyR(1) & openDiffInd(1)) shouldBe 'proved
  }

  "Differential Variant" should "diff var a()>0 |- <{x'=a()}>x>=b()" in withMathematica { tool =>
    proveBy(Sequent(IndexedSeq("a()>0".asFormula), IndexedSeq("<{x'=a()}>x>=b()".asFormula)), diffVar(1)) shouldBe 'proved
  }

  it should "diff var flat flight progress [function]" in withMathematica { tool =>
    proveBy("b>0 -> \\exists d (d^2<=b^2 & <{x'=d}>x>=p())".asFormula, diffVar(1, 1::0::1::Nil)) shouldBe 'proved
  }

  it should "diff var flat flight progress [variable]" taggedAs(IgnoreInBuildTest) in withMathematica { tool =>
    proveBy("b>0 -> \\forall p \\exists d (d^2<=b^2 & <{x'=d}>x>=p)".asFormula, diffVar(1, 1::0::0::1::Nil)) shouldBe 'proved
  }
}
