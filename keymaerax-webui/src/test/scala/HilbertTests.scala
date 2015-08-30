/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/


import edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms._

import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.ApplyRule
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica, Tool}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.ProvabilityTestHelper

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * Tests Hilbert Calculus.
 * @author Andre Platzer
 */
class HilbertTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  import HilbertCalculus._

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

  "Hilbert calculus" should "prove x>=5 -> [{x'=2&x<=9}]x<=9" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}]x<=9".asFormula)),
      implyR(1) &
        DW(1) &
        TacticLibrary.abstractionT(1) & allR(1) & prop
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=2&x<=9}]x<=10" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}]x<=10".asFormula)),
      implyR(1) &
        DW(1) &
        TacticLibrary.abstractionT(1) & QE
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=2}](x>=5)'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}](x>=5)'".asFormula)),
      implyR(1) &
        DE(1) &
        Dgreaterequal(1, 1::1::Nil) &
        Dvariable(1, 1::1:: 0::Nil) &
        Dconst(1, 1::1:: 1::Nil) &
        Dassignb(SuccPosition(0, 1::Nil)) &
          TacticLibrary.abstractionT(1) & QE
    ) shouldBe 'proved
  }

  it should "prove (x+2*y)'=x'+2*y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x+2*y)'=x'+2*y'".asFormula)),
    Dplus(SuccPosition(0, 0::Nil)) &
      Dvariable(SuccPosition(0, 0::0::Nil)) &
      useAt(Dlinear)(SuccPosition(0, 0::1::Nil)) & // Dtimes(SuccPosition(0, 0::1::Nil))
      Dvariable(SuccPosition(0, 0::1::1::Nil)) &
      byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "prove (y)'=y forward" in {
    val x = Variable("y")
    TactixLibrary.proveBy(
      Sequent(Nil,IndexedSeq(), IndexedSeq(Equal(Differential(x), DifferentialSymbol(x)))),
      Dvariable(SuccPosition(0,0::Nil)) & byUS("= reflexive")) shouldBe 'proved
    TactixLibrary.proveBy(
      Sequent(Nil,IndexedSeq(), IndexedSeq(Equal(Differential(x), DifferentialSymbol(x)))),
      Dvariable(SuccPosition(0,0::Nil)) & byUS("= reflexive")) shouldBe 'proved
  }

  it should "derive (y)'=y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(y)'=y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x+y)'=x'+y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x+y)'=x'+y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x*y)'=x'*y+x*y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x*y)'=x'*y+x*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x+2*y)'=x'+2*y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x+2*y)'=x'+2*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  ignore should "derive (5*3+2*9)'=0*3+5*0+(0*9+2*0) unless optimized" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*3+2*9)'=0*3+5*0+(0*9+2*0)".asFormula)),
      derive(1,0::Nil)  //@todo & QE
    ) shouldBe 'proved
  }

  ignore should "derive (5*3+2*9)'=5*0+2*0 if optimized (left linear preferred but not const optimized)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*3+2*9)'=5*0+2*0".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*3+2*9)'=0 if optimized (const optimized)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*3+2*9)'=0".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*x+2*y)'=5*x'+2*y'" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*x+2*y)'=5*x'+2*y'".asFormula)),
      derive(1,0::Nil) & byUS("= reflexive")
    ) shouldBe 'proved
  }

  it should "derive (5*x+2*y>=6)' <-> 5*x'+2*y'>=0" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(5*x+2*y>=6)' <-> 5*x'+2*y'>=0".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive (7*x<2*y & 22*x=4*y+8)' <-> (7*x'<=2*y' & 22*x'=4*y'+0)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(7*x<2*y & 22*x=4*y+8)' <-> (7*x'<=2*y' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive (x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> (x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("(x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> (x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "derive [{x'=7,y'=-9,z'=2}](x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> [{x'=7,y'=-9,z'=2}](x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=7,y'=-9,z'=2}](x*x<2*y & 5*x+2*y>=6+z & 22*x=4*y+8)' <-> [{x'=7,y'=-9,z'=2}](x'*x+x*x'<=2*y' & 5*x'+2*y'>=0+z' & 22*x'=4*y'+0)".asFormula)),
      derive(1,0::1::Nil) & byUS("<-> reflexive")
    ) shouldBe 'proved
  }

  it should "reduce [{x'=7}](5*x>=6)' to [{x'=7}]5*x'>=0" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=7}](5*x>=6)'".asFormula)),
      derive(1,1::Nil)
    ).subgoals shouldBe List(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=7}]5*x'>=0".asFormula)))
  }

  it should "reduce [{x'=99,y'=-3}](7*x<2*y & 22*x=4*y+8)' to [{x'=99,y'=-3}](7*x'<=2*y' & 22*x'=4*y'+0)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=99,y'=-3}](7*x<2*y & 22*x=4*y+8)'".asFormula)),
      derive(1,1::Nil)
    ).subgoals shouldBe List(Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=99,y'=-3}](7*x'<=2*y' & 22*x'=4*y'+0)".asFormula)))
  }

  it should "prove x>=5 -> [{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) &
        DI(1) & (step(1) & step(1)) && (
        prop,
        DE(1) &
          Dgreaterequal(1, 1::1::Nil) &
          Dvariable(1, 1::1:: 0::Nil) &
          Dconst(1, 1::1:: 1::Nil) &
          Dassignb(SuccPosition(0, 1::Nil)) & TacticLibrary.abstractionT(1) & QE
      )
    ) shouldBe 'proved
  }

  it should "prove/derive x>=5 -> [{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) &
        DI(1) & (step(1) & step(1)) && (
        prop,
        DE(1) & derive(1, 1::1::Nil) &
          Dassignb(SuccPosition(0, 1::Nil)) & TacticLibrary.abstractionT(1) & QE
        )
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2}]x>=5".asFormula)),
      implyR(1) & diffInd(1)
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [{x'=2&x<=10}](5<=x)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=10}](5<=x)".asFormula)),
      implyR(1) & diffInd(1)
    ) shouldBe 'proved
  }

//  it should "auto-prove x>=5 -> [{x'=2&x<=10}](5<=x&x<=10)" in {
//    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=10}](5<=x&x<=10)".asFormula)),
//      implyR(1) & diffCut(1)
//    ) shouldBe 'proved
//  }

  it should "auto-prove x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x*x+y*y>=8 -> [{x'=5*y,y'=-5*x}]x*x+y*y>=8".asFormula)),
      implyR(1) & diffInd(1)
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1;]x>0 by chase" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1;]x>0".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1 by chase" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1;]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove [?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;}}]x>=1 by chase" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=99; ++ ?x>=0;{{x:=x+1;++x:=x+2;};{y:=0;++y:=1;}}]x>=1".asFormula)),
      chase(1,Nil) & QE
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)".asFormula)),
      implyR(1) &
        DC("5<=x".asFormula)(1) & debug("after DC") &
        //@todo needs more branching to handle DI
        //@todo DC should not do absolute proof of implication but contextual
        DW(1) & debug("after DW") &
        TacticLibrary.abstractionT(1) & debug("after abstraction") & QE
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [{x'=2&x<=9}](5<=x&x<=10) with DC" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [{x'=2&x<=9}](5<=x&x<=10)".asFormula)),
      implyR(1) &
        DC("5<=x".asFormula)(1) && (
        diffInd(1),
        DW(1) & TacticLibrary.abstractionT(1) & QE
        )
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [x:=x+1;{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [x:=x+1;{x'=2}]x>=5".asFormula)),
    implyR(1) & //ind
    useAt("[;] compose")(1) &
    useAt("[:=] assign equational")(1) &
    step(1) & step(1) &
    useAt("DI differential invariant")(1) & //@todo diffInd(1)
      (l(step)*) & TacticLibrary.abstractionT(1) & master
    ) shouldBe 'proved
  }

  it should "chase [?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=0;x:=x+1; ++ x:=1;?x>=2;]x>=1" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("[?x>0;x:=x+1; ++ ?x=0;x:=1; ++ x:=0;x:=x+1; ++ x:=1;?x>=2;]x>=1".asFormula)),
      // chaseWide(3) works like an update calculus
      chaseWide(3)(1) &
        QE
    ) shouldBe 'proved
  }

  it should "prove x>=5 |- [x:=x+1][{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq("x>=5".asFormula), IndexedSeq("[x:=x+1;][{x'=2}]x>=5".asFormula)),
      //@todo need to locate diffInd to after update prefix
      diffInd(1, 1::Nil)
    ) shouldBe 'proved
  }

  it should "auto-prove x>=5 -> [x:=x+1;{x'=2}]x>=5" in {
    proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq("x>=5 -> [x:=x+1;{x'=2}]x>=5".asFormula)),
      implyR(1) &
        chaseWide(3)(1) &
        //@todo need to locate diffInd to after update prefix
        diffInd(1, 1::Nil)
    ) shouldBe 'proved
  }
}
