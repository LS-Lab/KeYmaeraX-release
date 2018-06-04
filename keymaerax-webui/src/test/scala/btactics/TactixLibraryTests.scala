/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics


import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, SlowTest, TodoTest}

import scala.collection.immutable._
import scala.language.postfixOps
import org.scalatest.LoneElement._
import org.scalatest.concurrent._
import org.scalatest.time.SpanSugar._

/**
 * Tactix Library Test.
 * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class TactixLibraryTests extends TacticTestBase with Timeouts /* TimeLimits does not abort test */ {
  private val someList: () => Iterator[Formula] = () =>
      ("x>=4".asFormula :: "x>=6".asFormula :: "x<2".asFormula :: "x>=5".asFormula :: "x>=0".asFormula :: Nil).iterator

  "DoLoneSome not ChooseSome" should "follow the right cut for x>=7 -> x>=5" in withMathematica { _ =>
    proveBy("x>=7 -> x>=5".asFormula,
      implyR(1) &
        cutR("x>=6".asFormula)(SuccPosition(1).top) & OnAll(QE)
    )
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 by invariant" in withMathematica { _ =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        diffInvariant("x>=5".asFormula)(1) & dW(1) & QE
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{{x'=2}}*]x>=5 by loop invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        loop("x>=5".asFormula)(1) <(
          QE
          ,
          QE
          ,
            solve(1) & OnAll(QE)
      )
    ) shouldBe 'proved
  }

  "ChooseSome" should "find the right cut for x>=7 -> x>=5" in withMathematica { _ =>
    proveBy("x>=7 -> x>=5".asFormula,
      implyR(1) &
        ChooseSome(someList, (c:Formula) => cutR(c)(SuccPosition(1).top) & OnAll(QE & done))
    )
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 from one invariant" in withMathematica { _ =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        ChooseSome(() => ("x>=5".asFormula :: Nil).iterator, (inv:Formula) => diffInvariant(inv)(1) & dW(1) & QE & done)
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 from list of invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
      ChooseSome(someList, (inv:Formula) => diffInvariant(inv)(1) & dW(1) & QE & done)
    ) shouldBe 'proved
  }

  it should "generate and master prove x>=5 -> [{x'=x^2}]x>=5 from list of invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        //@note master() together with ChooseSome leaves goals open, if first alternative doesn't QE --> demand QE after master
        ChooseSome(someList, (inv:Formula) => diffInvariant(inv)(1) & dW(1) & (master() & QE & done))
    ) shouldBe 'proved
  }


  it should "prove x>=5 -> [{{x'=2}}*]x>=5 from one loop invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        ChooseSome(() => ("x>=5".asFormula :: Nil).iterator, (inv:Formula) => loop(inv)(1) <(
          QE & done
          ,
          QE & done
          ,
          solve(1) & OnAll(QE & done)
          ))
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{{x'=2}}*]x>=5 from list of loop invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        ChooseSome(someList, (inv:Formula) => loop(inv)(1) <(
            QE & done
            ,
            QE & done
            ,
            solve(1) & OnAll(QE & done)
            ))
    ) shouldBe 'proved
  }

  it should "generate and master prove x>=5 -> [{{x'=2}}*]x>=5 from list of loop invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        //@note master() together with ChooseSome leaves goals open, if first alternative doesn't QE --> demand QE after master
        ChooseSome(someList, (inv:Formula) => loop(inv)(1) & (master() & QE & done))
    ) shouldBe 'proved
  }

  "LetInspect" should "post-hoc instantiate a j closing \\exists j 5+3=j" in withMathematica{qeTool =>
    val proof = proveBy("\\exists jj 5+3=jj".asFormula,
      LetInspect("j()".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => l
        }
        ,
        existsR("j()".asTerm)(1) &
          (step(1, 0::Nil)*)
      ) & byUS("= reflexive")
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj 5+3=jj".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc instantiate a j(||) closing \\exists j 5+3=j" taggedAs(TodoTest,IgnoreInBuildTest) ignore withMathematica{ qeTool =>
    val proof = proveBy("\\exists jj 5+3=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => l
        }
        ,
        existsR("j(||)".asTerm)(1) &
          (step(1, 0::Nil)*)
      ) & byUS("= reflexive")
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj 5+3=jj".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc instantiate a j closing \\exists j (x+x)'=j" ignore withMathematica{qeTool =>
    val proof = proveBy("\\exists jj (x+x)'=jj".asFormula,
      LetInspect("j(.)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => l
        }
        ,
        existsR("j(x)".asTerm)(1) &
        derive(1, 0::Nil))
        & byUS("= reflexive"))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x)'=jj".asFormula))
    proof shouldBe 'proved
  }

  /** @see UnificationMatchTest should "unify j()=x+y with s()=s()" unifiable but not by mere matching, needs a proper unifier instead of a single sided matcher */
  it should "post-hoc find a j() closing (x+x*y)'=j()" taggedAs(TodoTest,IgnoreInBuildTest) ignore withMathematica{_ =>
    val proof = proveBy("\\exists jj (x+x*y)'=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l,_) => l
        }
        ,
        existsR("j()".asTerm)(1) &
          derive(1, 0::Nil))
        & byUS("= reflexive"))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x*y)'=jj".asFormula))
    proof shouldBe 'proved
  }

  /** @see UnificationMatchTest should "unify j()=x+y with s()=s()" */
  it should "post-hoc find a j() closing j()=(x+x*y)'" taggedAs(TodoTest,IgnoreInBuildTest) ignore withMathematica{qeTool =>
    val proof = proveBy("\\exists jj jj=(x+x*y)'".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => r
        }
        ,
        existsR("j()".asTerm)(1) &
        derive(1, 1::Nil))
        & byUS("= reflexive"))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj jj=(x+x*y)'".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc find a j(||) closing (x+x*y)'=j(||)" taggedAs(TodoTest,IgnoreInBuildTest) ignore withMathematica{qeTool =>
    val proof = proveBy("\\exists jj (x+x*y)'=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => l
        }
        ,
        existsR("j(||)".asTerm)(1) &
          derive(1, 0::Nil))
        & byUS("= reflexive"))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x*y)'=jj".asFormula))
    proof shouldBe 'proved
  }

  def feedOneAfterTheOther[A<:Expression](list: List[A]) : (ProvableSig,ProverException)=>Seq[Expression] = {
    var rem = list
    (_,e) => println("SnR loop status " + e)
      rem match {
        case hd::tail => rem = tail; hd :: Nil
        case nil => throw new BelleThrowable("SearchAndRescueAgain ran out of alternatives among: " + list)
      }
  }

  "sAI" should "prove x>=0 -> [{x'=x^2+x+1}]x>=0" in withMathematica{qeTool =>
    val fml = "x>=0 -> [{x'=x^2+x+1}]x>=0".asFormula
    proveBy(fml, implyR(1) & ODEInvariance.sAIclosedPlus()(1)) shouldBe 'proved
  }

  "loopPostMaster" should "find an invariant for x=5-> [{x:=x+2;{x'=1}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;{x'=1}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }



  "SnR Loop Invariant" should "find an invariant for x=5-> [{x:=x+2;}*]x>=0" in withMathematica{qeTool =>
    val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val jj = "j(.)".asFormula
    val proof = proveBy(fml,
      implyR(1) & SearchAndRescueAgain(jj :: Nil,
        loop(USubst(Seq(SubstitutionPair(".".asTerm,"x".asTerm)))(jj))(1) <(nil, nil, chase(1)),
        feedOneAfterTheOther(invs),
        OnAll(master()) & done
      )
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
    proveBy(fml, implyR(1) & loopSR((seq,pos)=>invs.toStream)(1)) shouldBe 'proved
  }


  "Normalize" should "prove simple formula" in {
    val f = "y>0 -> [x:=y;]x>0".asFormula
    proveBy(f, normalize) shouldBe 'proved
  }

  it should "unfold simple formula" in {
    val f = "y>0 -> [x:=2;]x>0".asFormula
    val proof = proveBy(f, normalize)
    proof.subgoals should have size 1
    proof.subgoals.head.ante should contain only "y>0".asFormula
    proof.subgoals.head.succ should contain only "2>0".asFormula
  }

  it should "unfold simple formula when other formulas are around" in {
    val f = "y>0 -> y>=0 | [x:=2;]x>0".asFormula
    val proof = proveBy(f, normalize)
    proof.subgoals should have size 1
    proof.subgoals.head.ante should contain only "y>0".asFormula
    proof.subgoals.head.succ should contain only ("y>=0".asFormula, "2>0".asFormula)
  }

  it should "unfold with ODE when other formulas are around" in {
    val f = "y>0 -> y>=0 | [x:=2;{x'=3}]x>0".asFormula
    val proof = proveBy(f, normalize)
    proof.subgoals should have size 1
    proof.subgoals.head.ante should contain only ("y>0".asFormula, "x=2".asFormula)
    proof.subgoals.head.succ should contain only ("y>=0".asFormula, "[{x'=3}]x>0".asFormula)
  }

  "QE" should "reset timeout when done" in withQE {
    case tool: ToolOperationManagement =>
      val origTimeout = tool.getOperationTimeout
      origTimeout shouldBe Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_MAX))
      proveBy("x>1 -> x>0".asFormula, QE(Nil, None, Some(7)) & new BuiltInTactic("ANON") {
        def result(provable: ProvableSig): ProvableSig = {
          tool.getOperationTimeout shouldBe origTimeout // timeout should be reset after QE
          provable
        }
      }) shouldBe 'proved
    case _ => // nothing to test
  }

  it should "reset timeout when failing" in withQE {
    case tool: ToolOperationManagement =>
      val origTimeout = tool.getOperationTimeout
      origTimeout shouldBe Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_MAX))
      proveBy("x>0 -> x>1".asFormula, QE(Nil, None, Some(7)) | new BuiltInTactic("ANON") {
        def result(provable: ProvableSig): ProvableSig = {
          tool.getOperationTimeout shouldBe origTimeout // timeout should be reset after QE
          provable
        }
      }) should (not be 'proved)
    case _ => // nothing to test
  }

  it should "not change timeout before being run" in withQE {
    case tool: ToolOperationManagement =>
      val origTimeout = tool.getOperationTimeout
      origTimeout shouldBe Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_MAX))
      proveBy("x>0 -> x>1".asFormula, (DebuggingTactics.assert(_ => false, "Fail")
          & QE(Nil, None, Some(7))) | new BuiltInTactic("ANON") {
        def result(provable: ProvableSig): ProvableSig = {
          tool.getOperationTimeout shouldBe origTimeout // timeout should be reset after QE
          provable
        }
      }) should (not be 'proved)
    case _ => // nothing to test
  }

  "Tactic chase" should "not infinite recurse" in {
    var i = 0
    val count = "ANON" by ((pos: Position, seq: Sequent) => { i=i+1; skip })

    failAfter(1 second) {
      val result = proveBy("[{x'=1}]x>0".asFormula, master(loopauto(), count, keepQEFalse=false))
      result.subgoals.loneElement shouldBe "==> [{x'=1}]x>0".asSequent
    }

    i shouldBe 1
  }

  it should "exhaustively apply propositional" in {
    proveBy("true<->(p()<->q())&q()->p()".asFormula, prop) shouldBe 'proved
  }

  "Loop convergence" should "prove x>=0 -> <{x:=x-1;}*>x<1 with conRule" in withMathematica {qeTool =>
    val fml = "x>=0 -> <{x:=x-1;}*>x<1".asFormula
    val vari = "x<v+1".asFormula
    proveBy(fml, implyR(1) & DLBySubst.conRule("v".asVariable, vari)(1)).subgoals shouldBe (IndexedSeq(
      Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq("\\exists v x<v+1".asFormula)),
      Sequent(IndexedSeq("v<=0".asFormula, "x<v+1".asFormula), IndexedSeq("x<1".asFormula)),
      Sequent(IndexedSeq("v>0".asFormula, "x<v+1".asFormula), IndexedSeq("<x:=x-1;>x<(v-1)+1".asFormula))
    ))
    proveBy(fml, implyR(1) & DLBySubst.conRule("v".asVariable, vari)(1) <(
      debug("init") & QE(),
      debug("use") & QE(),
      debug("step") & assignd(1) & QE()
      ))
  }

  it should "prove x>=0 -> <{x:=x-1;}*>x<1 with con" in withMathematica {qeTool =>
    val fml = "x>=0 -> <{x:=x-1;}*>x<1".asFormula
    val vari = "x<v+1".asFormula
    proveBy(fml, implyR(1) & con("v".asVariable, vari)(1)).subgoals shouldBe (IndexedSeq(
      Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq("\\exists v x<v+1".asFormula)),
      Sequent(IndexedSeq("v<=0".asFormula, "x<v+1".asFormula), IndexedSeq("x<1".asFormula)),
      Sequent(IndexedSeq("v>0".asFormula, "x<v+1".asFormula), IndexedSeq("<x:=x-1;>x<(v-1)+1".asFormula))
    ))
    proveBy(fml, implyR(1) & DLBySubst.conRule("v".asVariable, vari)(1) <(
      debug("init") & QE(),
      debug("use") & QE(),
      debug("step") & assignd(1) & QE()
      ))
  }

  it should "prove x>=0 & c=1 -> <{x:=x-c;}*>x<1 with con" in withMathematica {qeTool =>
    val fml = "x>=0 & c=1 -> <{x:=x-c;}*>x<1".asFormula
    val vari = "x<z+1".asFormula
    proveBy(fml, implyR(1) & andL(-1) & con("z".asVariable, vari)(1)).subgoals shouldBe (IndexedSeq(
      Sequent(IndexedSeq("x>=0".asFormula, "c=1".asFormula), IndexedSeq("\\exists z x<z+1".asFormula)),
      Sequent(IndexedSeq("z<=0".asFormula, "x<z+1".asFormula, "c=1".asFormula), IndexedSeq("x<1".asFormula)),
      Sequent(IndexedSeq("z>0".asFormula, "x<z+1".asFormula, "c=1".asFormula), IndexedSeq("<x:=x-c;>x<(z-1)+1".asFormula))
    ))
    proveBy(fml, implyR(1) & con("z".asVariable, vari)(1) <(
      debug("init") & QE(),
      debug("use") & QE(),
      debug("step") & assignd(1) & QE()
      ))
  }
}
