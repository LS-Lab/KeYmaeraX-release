package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleError
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable.IndexedSeq

/**
 * Tests
 * [[edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics]],
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.DW]], and
 * [[edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.DC]]
 */
class DifferentialTests extends TacticTestBase {
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

  "Differential effect" should "introduce a differential assignment" in {
    val result = proveBy("[{x'=5 & x>2}]x>0".asFormula, DE(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=5 & x>2}][x':=5;]x>0".asFormula
  }

  it should "introduce differential assignments exhaustively" in {
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

  "diffInd" should "auto-prove x>=5 -> [{x'=2}]x>=5" taggedAs KeYmaeraXTestTags.SummaryTest in withMathematica { implicit qeTool =>
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) & diffInd(qeTool)(1)
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [{x'=2&x<=10}](5<=x)" in withMathematica { implicit qeTool =>
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=10}](5<=x)".asFormula)),
      implyR(1) & diffInd(qeTool)(1)
    ) shouldBe 'proved
  }

  it should "auto-prove x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in withMathematica { implicit qeTool =>
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula)),
      implyR(1) & diffInd(qeTool)(1)
    ) shouldBe 'proved
  }

  it should "prove x>=5 |- [x:=x+1][{x'=2}]x>=5" in withMathematica { implicit qeTool =>
    proveBy(Sequent(Nil, IndexedSeq("x>=5".asFormula), IndexedSeq("[x:=x+1;][{x'=2}]x>=5".asFormula)),
      assignb(1) & diffInd(qeTool)(1)
    ) shouldBe 'proved
  }

  it should "prove x>=5 |- [x:=x+1][{x'=2}]x>=5 in reverse" in withMathematica { implicit qeTool =>
    proveBy(Sequent(Nil, IndexedSeq("x>=5".asFormula), IndexedSeq("[x:=x+1;][{x'=2}]x>=5".asFormula)),
      diffInd(qeTool)(1, 1::Nil) & debug("Foo") &
        assignb(1) & // handle updates
        QE
    ) shouldBe 'proved
  }

  "Dvariable" should "work when the Differential() occurs in a formula without []'s" in withMathematica { implicit qeTool =>
    // Equal(Differential(Variable("x")), "1".asTerm)
    val result = proveBy("(x)'=1".asFormula, Dvariable(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    // Equal(DifferentialSymbol(Variable("x")), "1".asTerm)
    result.subgoals.head.succ should contain only "x'=1".asFormula
  }

  it should "alpha rename if necessary" in withMathematica { implicit qeTool =>
    val result = proveBy("(z)'=1".asFormula, Dvariable(1, 0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "z'=1".asFormula
  }

  it should "work in context" in withMathematica { implicit qeTool =>
    val result = proveBy("[y:=1;](z)'=1".asFormula, Dvariable(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[y:=1;]z'=1".asFormula
  }

  it should "work in a context that binds the differential symbol" in withMathematica { implicit qeTool =>
    val result = proveBy("[z':=1;](z)'=1".asFormula, Dvariable(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z':=1;]z'=1".asFormula
  }

  it should "work in a context that binds x" in {
    val result = proveBy("[z:=1;](z)'=1".asFormula, Dvariable(1, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[z:=1;]z'=1".asFormula
  }

  it should "work with other formulas around" in {
    val result = proveBy(Sequent(Nil,
      IndexedSeq("a>0".asFormula),
      IndexedSeq("b<0".asFormula, "[z:=1;](z)'=1".asFormula, "c=0".asFormula)), Dvariable(2, 1::0::Nil))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a>0".asFormula
    result.subgoals.head.succ should contain only ("b<0".asFormula, "[z:=1;]z'=1".asFormula, "c=0".asFormula)
  }

  "DC" should "cut in a simple formula" in withMathematica { implicit qeTool =>
    val result = proveBy("[{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2 & true & x>0}]x>=0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[{x'=2}]x>0".asFormula
  }

  it should "retain context for showing condition" in withMathematica { implicit qeTool =>
    val result = proveBy(
      Sequent(Nil, IndexedSeq("x>0".asFormula), IndexedSeq("y<0".asFormula, "[{x'=2}]x>=0".asFormula, "z=0".asFormula)),
      DC("x>0".asFormula)(2))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only ("y<0".asFormula, "[{x'=2 & true & x>0}]x>=0".asFormula, "z=0".asFormula)
    result.subgoals(1).ante should contain only "x>0".asFormula
    result.subgoals(1).succ should contain only ("y<0".asFormula, "[{x'=2}]x>0".asFormula, "z=0".asFormula)
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ODEProduct" in withMathematica { implicit qeTool =>
    val result = proveBy("[{x'=2, y'=3, z'=4 & y>4}]x>0".asFormula, DC("x>1".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2,y'=3,z'=4 & (y>4&x>1)}]x>0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[{x'=2,y'=3,z'=4 & y>4}]x>1".asFormula
  }

  it should "cut formula into rightmost ODE in ODEProduct, even if constraint empty" in withMathematica { implicit qeTool =>
    val result = proveBy("[{x'=2, y'=3}]x>0".asFormula, DC("x>1".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2,y'=3 & (true&x>1)}]x>0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[{x'=2, y'=3}]x>1".asFormula
  }
  it should "preserve existing evolution domain constraint" in withMathematica { implicit qeTool =>
    val result = proveBy("[{x'=2 & x>=0 | y<z}]x>=0".asFormula, DC("x>0".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{x'=2 & (x>=0 | y<z) & x>0}]x>=0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[{x'=2 & x>=0 | y<z}]x>0".asFormula
  }

  ignore should "work in context" in withMathematica { implicit qeTool =>
    val result = proveBy("[x:=3;][{x'=2}]x>=0".asFormula, DC("x>0".asFormula)(1, 1::Nil))

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[x:=3;][{x'=2}]x>0".asFormula
    result.subgoals(1).ante shouldBe empty
    result.subgoals(1).succ should contain only "[x:=3;][{x'=2 & true & x>0}]x>=0".asFormula
  }

  "diffCut" should "cut in a simple formula" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>=0".asFormula)),
      diffCut("x>0".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & true & x>0}]x>=0".asFormula
    result.subgoals(1).ante should contain only "x>0".asFormula
    result.subgoals(1).succ should contain only "[{x'=2}]x>0".asFormula
  }
  it should "retain context for showing condition" in withMathematica { implicit qeTool =>
    val result = proveBy(
      Sequent(Nil, IndexedSeq("x>0".asFormula), IndexedSeq("y<0".asFormula, "[{x'=2}]x>=0".asFormula, "z=0".asFormula)),
      diffCut("x>0".asFormula)(2))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only ("y<0".asFormula, "[{x'=2 & true & x>0}]x>=0".asFormula, "z=0".asFormula)
    result.subgoals(1).ante should contain only "x>0".asFormula
    result.subgoals(1).succ should contain only ("y<0".asFormula, "[{x'=2}]x>0".asFormula, "z=0".asFormula)
  }
  it should "cut formula into evolution domain constraint of rightmost ODE in ODEProduct" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>1".asFormula), IndexedSeq("[{x'=2, y'=3, z'=4 & y>4}]x>0".asFormula)),
      diffCut("x>1".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "[{x'=2,y'=3,z'=4 & (y>4&x>1)}]x>0".asFormula
    result.subgoals(1).ante should contain only "x>1".asFormula
    result.subgoals(1).succ should contain only "[{x'=2,y'=3,z'=4 & y>4}]x>1".asFormula
  }
  it should "cut formula into rightmost ODE in ODEProduct, even if constraint empty" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>1".asFormula), IndexedSeq("[{x'=2, y'=3}]x>0".asFormula)),
      diffCut("x>1".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>1".asFormula
    result.subgoals.head.succ should contain only "[{x'=2,y'=3 & (true&x>1)}]x>0".asFormula
    result.subgoals(1).ante should contain only "x>1".asFormula
    result.subgoals(1).succ should contain only "[{x'=2,y'=3}]x>1".asFormula
  }
  it should "preserve existing evolution domain constraint" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2 & x>=0 | y<z}]x>=0".asFormula)),
      diffCut("x>0".asFormula)(1))

    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & (x>=0 | y<z) & x>0}]x>=0".asFormula
    result.subgoals(1).ante should contain only "x>0".asFormula
    result.subgoals(1).succ should contain only "[{x'=2 & (x>=0 | y<z)}]x>0".asFormula
  }

  it should "introduce ghosts when special function old is used" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=2 & x>=0 | y<z}]x>=0".asFormula)),
      diffCut("x>=old(x)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x_0=x".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & (x>=0 | y<z) & x>=x_0}]x>=0".asFormula
    result.subgoals(1).ante should contain only "x_0=x".asFormula
    result.subgoals(1).succ should contain only "[{x'=2 & (x>=0 | y<z)}]x>=x_0".asFormula
  }

  it should "retain existing conditions and introduce ghosts when special function old is used" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>=0".asFormula)),
      diffCut("x>=old(x)".asFormula)(1))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only ("x>0".asFormula, "x_0=x".asFormula)
    result.subgoals.head.succ should contain only "[{x'=2 & true & x>=x_0}]x>=0".asFormula
    result.subgoals(1).ante should contain only ("x>0".asFormula, "x_0=x".asFormula)
    result.subgoals(1).succ should contain only "[{x'=2}]x>=x_0".asFormula
  }

  it should "cut in multiple formulas" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("v>=0".asFormula, "x>0".asFormula), IndexedSeq("[{x'=v,v'=2}]x>=0".asFormula)),
      diffCut("v>=0".asFormula, "x>=old(x)".asFormula)(1))
    result.subgoals should have size 3
    result.subgoals.head.ante should contain only ("v>=0".asFormula, "x>0".asFormula, "x_0=x".asFormula)
    result.subgoals.head.succ should contain only "[{x'=v,v'=2 & (true & v>=0) & x>=x_0}]x>=0".asFormula
    result.subgoals(1).ante should contain only ("v>=0".asFormula, "x>0".asFormula)
    result.subgoals(1).succ should contain only "[{x'=v,v'=2}]v>=0".asFormula
    result.subgoals(2).ante should contain only ("v>=0".asFormula, "x>0".asFormula, "x_0=x".asFormula)
    result.subgoals(2).succ should contain only "[{x'=v,v'=2 & true & v>=0}]x>=x_0".asFormula
  }

  "diffInvariant" should "cut in a simple formula" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=2}]x>=0".asFormula)),
      diffInvariant("x>0".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "[{x'=2 & true & x>0}]x>=0".asFormula
  }

  it should "cut in multiple formulas" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("v>=0".asFormula, "x>0".asFormula), IndexedSeq("[{x'=v,v'=2}]x>=0".asFormula)),
      diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("v>=0".asFormula, "x>0".asFormula, "x_0=x".asFormula)
    result.subgoals.head.succ should contain only "[{x'=v,v'=2 & (true & v>=0) & x>=x_0}]x>=0".asFormula
  }

  it should "fail if any of the formulas is not an invariant" in withMathematica { implicit qeTool =>
    a [BelleError] should be thrownBy proveBy(
      Sequent(Nil, IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=v,v'=2}]x>=0".asFormula)),
      diffInvariant("v>=0".asFormula, "x>=old(x)".asFormula)(1))
  }

  "Differential introduce constants" should "replace a with a() in v'=a" in {
    val result = proveBy("[{v'=a}]v=v0()+a*t()".asFormula, Dconstify(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{v'=a()}]v=v0()+a()*t()".asFormula
  }

  it should "not self-replace a() with a() in v'=a()" in {
    val result = proveBy("[{v'=a()}]v=v0()+a()*t()".asFormula, Dconstify(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{v'=a()}]v=v0()+a()*t()".asFormula
  }

  it should "not replace a with a() when a is not free in p" in {
    val result = proveBy("[{v'=a}]v>0".asFormula, Dconstify(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "[{v'=a}]v>0".asFormula
  }

  it should "replace every free occurrence of a with a() everywhere in the sequent" in {
    val s = Sequent(Nil,
      IndexedSeq("v>=0".asFormula, "a=0".asFormula, "\\forall a a<0".asFormula),
      IndexedSeq("[{v'=a}]v=v_0()+a*t()".asFormula, "a>=0".asFormula, "[a:=2;]v>0".asFormula))
    val result = proveBy(s, Dconstify(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("v>=0".asFormula, "a()=0".asFormula, "\\forall a a<0".asFormula)
    result.subgoals.head.succ should contain only ("[{v'=a()}]v=v_0()+a()*t()".asFormula, "a()>=0".asFormula, "[a:=2;]v>0".asFormula)
  }

  it should "replace every free occurrence of b (only in p) with b() everywhere in the sequent" in {
    val s = Sequent(Nil,
      IndexedSeq("v>=0".asFormula, "a=0".asFormula, "b=2".asFormula, "\\forall b b<0".asFormula),
      IndexedSeq("[{v'=a}](v>0 & b<0)".asFormula, "a>=0".asFormula, "[a:=2;]v>0".asFormula))
    val result = proveBy(s, Dconstify(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("v>=0".asFormula, "a=0".asFormula, "b()=2".asFormula, "\\forall b b<0".asFormula)
    result.subgoals.head.succ should contain only ("[{v'=a}](v>0& b()<0)".asFormula, "a>=0".asFormula, "[a:=2;]v>0".asFormula)
  }

  "DG" should "add y'=1 to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, DG("y".asVariable, "0".asTerm, "1".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=0*y+1}]x>0".asFormula
  }

  it should "add z'=1 to [y'=2]y>0" in {
    val result = proveBy("[{y'=2}]y>0".asFormula, DG("z".asVariable, "0".asTerm, "1".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists z [{y'=2,z'=0*z+1}]y>0".asFormula
  }

  it should "add x'=1 to [y'=2]y>0" in {
    val result = proveBy("[{y'=2}]y>0".asFormula, DG("x".asVariable, "0".asTerm, "1".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists x [{y'=2,x'=0*x+1}]y>0".asFormula
  }

  it should "add y'=3*y+10 to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, DG("y".asVariable, "3".asTerm, "10".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=3*y+10}]x>0".asFormula
  }

  it should "add y'=3*y+z() to [x'=2]x>0" in {
    val result = proveBy("[{x'=2}]x>0".asFormula, DG("y".asVariable, "3".asTerm, "z()".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=3*y+z()}]x>0".asFormula
  }

  it should "preserve evolution domain" in {
    val result = proveBy("[{x'=2 & x>=0}]x>0".asFormula, DG("y".asVariable, "3".asTerm, "10".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\exists y [{x'=2,y'=3*y+10 & x>=0}]x>0".asFormula
  }

  it should "work with other formulas around" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("a>1".asFormula), IndexedSeq("[{x'=2 & x>=0}]x>0".asFormula, "b=2".asFormula)),
      DG("y".asVariable, "3".asTerm, "10".asTerm)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "a>1".asFormula
    result.subgoals.head.succ should contain only ("\\exists y [{x'=2,y'=3*y+10 & x>=0}]x>0".asFormula, "b=2".asFormula)
  }

  it should "not allow non-linear ghosts (1)" in {
    a [BelleError] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, DG("y".asVariable, "y".asTerm, "1".asTerm)(1))
  }

  it should "not allow non-linear ghosts (2)" in {
    a [BelleError] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, DG("y".asVariable, "1".asTerm, "y".asTerm)(1))
  }

  it should "not allow ghosts that are already present in the ODE" in {
    a [BelleError] should be thrownBy proveBy("[{x'=2}]x>0".asFormula, DG("x".asVariable, "0".asTerm, "1".asTerm)(1))
  }

  "diffSolve" should "use provided solution" in withMathematica { tool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2,t'=1}]x>b".asFormula)),
      diffSolve(Some("x=x_0+2*t".asFormula))(tool)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>b".asFormula
    result.subgoals.head.succ should contain only "(true&t>=t_0)&x=x_0+2*(t-t_0) -> x>b".asFormula
  }

  it should "ask Mathematica if no solution provided" in withMathematica { tool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>b".asFormula), IndexedSeq("[{x'=2,t'=1}]x>b".asFormula)),
      diffSolve()(tool)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>b".asFormula
    result.subgoals.head.succ should contain only "(true&t>=t_0)&x=2*(t-t_0)+x_0 -> x>b".asFormula
  }

  it should "find solution for x'=v if None is provided" in withMathematica { tool =>
    //@todo requires v() instead of v, because derived axiom DlinearRight fails with substitution clash
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0 & v()>=0".asFormula), IndexedSeq("[{x'=v(),t'=1}]x>0".asFormula)),
      diffSolve()(tool)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>0 & v()>=0".asFormula
    result.subgoals.head.succ should contain only "(true&t>=t_0)&x=v()*(t-t_0)+x_0 -> x>0".asFormula
  }

  /**@todo derive not fully implemented yet */
  ignore should "find solutions for x'=v, v'=a if None is provided" in withMathematica { tool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x>0 & v>=0 & a()>0".asFormula), IndexedSeq("[{x'=v,v'=a(),t'=1}]x>0".asFormula)),
      diffSolve()(tool)(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x_0>0 & v_0>=0 & a()>0".asFormula
    result.subgoals.head.succ should contain only "true".asFormula
  }
}
