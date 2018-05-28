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

  "sAI" should "prove x>=0 -> [{x'=2}]x>=0" in withMathematica{qeTool =>
    val fml = "x>=0 -> [{x'=2}]x>=0".asFormula
    proveBy(fml, implyR(1) & ODEInvariance.sAIclosedPlus()(1)) shouldBe 'proved
  }

  "loopPostMaster" should "find an invariant for x=5-> [{x:=x+2;{x'=1}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;{x'=1}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x=5-> [{{x'=2}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{{x'=2}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "prove x>=5 & y>=0 -> [{{x'=x+y};}*]x>=0 by invariant x>=0 & y>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{{x'=x+y}}*]x>=0".asFormula
    proveBy(fml, implyR(1) & loop("x>=0 & y>=0".asFormula)(1) <(QE, QE, odeInvariant(1))) shouldBe 'proved
  }

  it should "prove x>=5 & y>=0 -> [{{x'=x+y};}*]x>=0 by invariant x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{{x'=x+y}}*]x>=0".asFormula
    proveBy(fml, implyR(1) & loop("x>=0".asFormula)(1) <(QE, QE, odeInvariant(1))) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=0 -> [{{x'=x+y};}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{{x'=x+y}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find a invariant for x=4-> [{{x'=-x};}*]x>=0 with other init" in withMathematica { _ =>
    val fml = "x=4 -> [{{x'=-x}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find a invariant for x=5-> [{{x'=-x};}*]x>=0" in withMathematica { _ =>
    val fml = "x=5 -> [{{x'=-x}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find a invariant for x=5-> [{{x'=-x};}*]x>0" in withMathematica { _ =>
    val fml = "x=5 -> [{{x'=-x}}*]x>0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x>0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "at least not loop forever when finding an invariant for x=5-> [{x:=x+2;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x=5-> [{{x'=0} ++ {x'=5}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{{x'=0} ++ {x'=5}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x=5-> [{x:=x+1;{x'=x}}*]x>=4 by counting up" in withMathematica { _ =>
    val fml = "x=5-> [{x:=x+1;{x'=x}}*]x>=4".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x>=-5".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "prove x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]v>=0 by invariant v>=0" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]v>=0".asFormula
    proveBy(fml, implyR(1) &  loop("v>=0".asFormula)(1) <(QE,QE, chase(1) & unfoldProgramNormalize & OnAll(odeInvariant(1)))) shouldBe 'proved
  }

  it should "find an invariant for x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]v>=0" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]v>=0".asFormula
    val invs = List("x>=-1".asFormula, "v>=1".asFormula, "x>=0&v>1".asFormula, "v>=-1".asFormula,
      "v>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]x>=0" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "v>=1".asFormula, "x>=0&v>1".asFormula, "v>=-1".asFormula, "v>=0".asFormula,
      "x>=0&v>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  //@todo time not in inv so odeInvariant won't work
  it should "prove x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10 by invariant x<=10" ignore withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    proveBy(fml, implyR(1) & loop("x<=10".asFormula)(1) <(QE,QE, chase(1) & unfoldProgramNormalize & OnAll(solve(1) & QE()))) shouldBe 'proved
    proveBy(fml, implyR(1) & loop("x<=10".asFormula)(1) <(QE,QE, chase(1) & unfoldProgramNormalize & OnAll(odeInvariant(1)))) shouldBe 'proved
  }

  //@todo time not in inv so odeInvariant won't work
  it should "find an invariant for x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" ignore withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = List("x>=-1".asFormula, "v>=1".asFormula, "x>=0&v>1".asFormula, "v>=-1".asFormula, "v>=0".asFormula,
      "v<=5".asFormula, "x<=10".asFormula, "v<=5 & x<=10".asFormula, "x>=0&v>=0".asFormula, "v*v<10-x".asFormula,
      "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
  }

  //@todo
  it should "find one invariant for x=0&v=0-> [{{?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula, "x<10".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs.toStream)(1)) shouldBe 'proved
  }

  //@todo
  it should "find one invariant for x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;t:=t; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in withMathematica { _ =>
    val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;t:=t; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs.toStream)(1)) shouldBe 'proved
  }

  //@todo
  it should "find one invariant for x=0&v=0&t=0-> [{{?x<9;v:=1; ++ ?false;t:=t; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in withMathematica { _ =>
    val fml = "x=0&v=0&t=0-> [{{?x<9;v:=1; ++ ?false;t:=t; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs.toStream)(1)) shouldBe 'proved
  }

  //@todo
  it should "find one invariant for x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in withMathematica { _ =>
    val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs.toStream)(1)) shouldBe 'proved
  }

  //@todo
  it should "find one invariant for x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs.toStream)(1)) shouldBe 'proved
  }

  //@todo time not in inv so odeInvariant won't work
  it should "find an invariant for x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" ignore withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = List("x>=-1".asFormula, "v>=1".asFormula, "x>=0&v>1".asFormula, "v>=-1".asFormula, "v>=0".asFormula,
      "v<=5".asFormula, "x<=10".asFormula, "v<=5 & x<=10".asFormula, "x>=0&v>=0".asFormula, "v*v<10-x".asFormula,
      "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
  }

  it should "prove x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10 by invariant x<=10" in withMathematica { _ =>
    val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    //proveBy(fml, implyR(1) & loop("x<=10".asFormula)(1) <(QE,QE, chase(1) & unfoldProgramNormalize & OnAll(solve(1) & QE()))) shouldBe 'proved
    proveBy(fml, implyR(1) & loop("x<=10".asFormula)(1) <(QE,QE,
      chase(1) & unfoldProgramNormalize <(
      odeInvariant(1),
      dC("x<=9+t".asFormula)(1) <( dW(1) & QE, odeInvariant(1))
    ))) shouldBe 'proved
  }

  it should "prove x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10 by invariant x<=10-t" ignore withMathematica { _ =>
    val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    proveBy(fml, implyR(1) & loop("x<=10-t&t>=0".asFormula)(1) <(QE,QE, chase(1) & unfoldProgramNormalize & OnAll(solve(1) & QE()))) shouldBe 'proved
    //x<=10-t&t>=0 not an ODE invariant
    proveBy(fml, implyR(1) & loop("x<=10-t&t>=0".asFormula)(1) <(QE,QE, chase(1) & unfoldProgramNormalize & OnAll(odeInvariant(1)))) shouldBe 'proved
  }

  it should "find an invariant for x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10 with more invariants" ignore withMathematica { _ =>
    val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    //x<=10-t&t>=0 not an ODE invariant
    val invs = List("x>=-1".asFormula, "v>=1".asFormula, "x>=0&v>1".asFormula, "v>=-1".asFormula, "v>=0".asFormula,
      "v<=5".asFormula, "x<=10".asFormula, "v<=5 & x<=10".asFormula, "x>=0&v>=0".asFormula, "x<=10-t".asFormula,
      "x<=10-t&t>=0".asFormula, "v*v<10-x".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;{x'=x^2+y}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;{x'=x^2+y}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "y>=1".asFormula, "x>=0&y>=0".asFormula, "x=7".asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for circular motion" in withMathematica { _ =>
    val fml = "x=0 & y=1 -> [{{x'=y,y'=-x}}*]x<=1".asFormula
    val invs = ("x=0" :: "x^2+y^2=1" :: "x^2+y^2=2" :: Nil).map(_.asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@todo not yet supported
    //proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariantCandidates)(1)) shouldBe 'proved
  }

  it should "find an invariant when first branch informative" in withMathematica { _ =>
    val fml = "x=0&v=0 -> [{{?x<9;v:=1; ++ v:=-1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "y=0" :: Nil).map(_.asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    println("Prove again because it was so much fun")
    //todo: should be calling pegasusInvariants
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusCandidates)(1)) shouldBe 'proved
  }

  it should "find an invariant when first branch uninformative" in withMathematica { _ =>
    val fml = "x=0&v=0 -> [{{v:=0; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "y=0" :: Nil).map(_.asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    println("Prove again because it was so much fun")
    //todo: should be calling pegasusInvariants
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusCandidates)(1)) shouldBe 'proved
  }

  it should "directly prove with solve" in withMathematica { _ =>
    val fml = "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1&t<=1 & v>=0}}*]x<=10".asFormula
    val pr = proveBy(fml, implyR(1) &
      loop("10-x>=v*v".asFormula)(1)<(QE,QE,chase(1) & unfoldProgramNormalize & OnAll(solve(1) & QE)))
    println(pr)
    pr shouldBe 'proved
  }

  it should "prove using invariants" in withMathematica { _ =>
    //This controller is tighter: 10-x>=v^2/2 +2*v+1
    //The v>=0 in domain constraint is not necessary, but makes the invariance argument easier
    val fml = "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1&t<=1 & v>=0}}*]x<=10".asFormula
    val pr = proveBy(fml, implyR(1) &
      loop("10-x>=v*v".asFormula)(1)<(QE,QE,chase(1) & unfoldProgramNormalize<(
        dC("t>=0&(10-x>=2*(1-t)^2+(4*(1-t)+v)*v)".asFormula)(1)<(
          dW(1)&QE,odeInvariant(1)),
        dC("v=0".asFormula)(1)<(odeInvariant(1),odeInvariant(1)),
        odeInvariant(1)
        )))
    println(pr)
    pr shouldBe 'proved
  }

  it should "prove the invariants of first a branch informative (scripted)" in withMathematica { _ =>
    val fml = "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{{x'=v,v'=a,t'=1&t<=1&v>=0}@invariant((10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0),(v*v<=10-x),(v=0&x<=10))}}*]x<=10".asFormula
    proveBy(fml, implyR(1) & loop("v*v<=10-x".asFormula)(1) <(QE(), QE(), master())) shouldBe 'proved
  }

  it should "prove the invariants of first a branch informative (scripted) 2" in withMathematica { _ =>
    val fml = "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{{x'=v,v'=a,t'=1&t<=1&v>=0}@invariant((a=1->10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0),(a=-1->v*v<=10-x),(a=0->v=0&x<=10))}}*]x<=10".asFormula
    proveBy(fml, implyR(1) & loop("v*v<=10-x".asFormula)(1) <(QE(), QE(), master())) shouldBe 'proved
  }

  it should "find an invariant when first a branch informative (scripted)" in withMathematica { _ =>
    val fml = "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1&t<=1&v>=0}}*]x<=10".asFormula
    val invs = ("10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0" :: "v*v<=10-x" :: "v=0&x<=10" :: "x<=10" :: "x=0" :: Nil).map(_.asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
  }

  it should "find an invariant when first a branch informative" in withMathematica { _ =>
    val fml = "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1&t<=1&v>=0}}*]x<=10".asFormula
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe 'proved
  }

  it should "find an invariant when middle branch informative" in withMathematica { _ =>
    val fml = "x=0&v=0&a=0 -> [{{a:=-1; ++ ?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0;};t:=0;{x'=v,v'=a,t'=1&t<=1&v>=0}}*]x<=10".asFormula
    val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "x=0" :: Nil).map(_.asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe 'proved
    println("Prove again because it was so much fun")
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
  }

  it should "find an invariant when first a branch uninformative" in withMathematica { _ =>
    val fml = "x=0&v=0&a=0 -> [{{v:=0;a:=0; ++ a:=-1; ++ ?10-x>=2+(4+v)*v; a:=1;};t:=0;{x'=v,v'=a,t'=1&t<=1&v>=0}}*]x<=10".asFormula
    val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "x=0" :: Nil).map(_.asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe 'proved
    println("Prove again because it was so much fun")
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
  }

  it should "find an invariant for the Ahmadi Parillo Kristic benchmark example" in withMathematica { _ =>
    val fml = "1/2*x<=x & x<=7/10 & 0<=y & y<=3/10 -> [{{x'=-x+x*y, y'=-y}}*]!(-8/10>=x & x>=-1 & -7/10>=y & y>=-1)".asFormula
    val invs = ("y<=0" :: "y>=0" :: "y=0" :: Nil).map(_.asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    println("Prove again because it was so much fun")
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe 'proved
  }

  it should "find an invariant for a simple time-triggered example" ignore withMathematica { _ =>
    val fml =
      """v=0 & A>=0 & b>0 & x<=m & ep>=0
        | -> [
        |      {
        |        {?(2*b*(m-x) >= v^2+(A+b)*(A*ep^2+2*ep*v)); a:=A; ++ a:=-b; }
        |        t := 0;
        |        {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
        |      }*
        |    ] x <= m
      """.stripMargin.asFormula
    val invs = ("v<=0" :: "v^2<=2*b*(m-x)" :: Nil).map(_.asFormula).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=0 -> [{y:=y+1;{x'=x+y}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{y:=y+1;{x'=x+y}}*]x>=1".asFormula
    val invs = List("x>=-1".asFormula, "y>=1".asFormula, "x>=0&y>=0".asFormula, "x>=1&y>=1".asFormula, "x>=1&y>=0".asFormula, "x=7".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((seq,pos)=>invs.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x+y}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x+y}}*]x>=1".asFormula
    val invs = List("x>=-1".asFormula, "y>=1".asFormula, "x>=0&y>=0".asFormula, "x>=1&y>=1".asFormula, "x>=1&y>=0".asFormula, "x=7".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((seq,pos)=>invs.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=0 -> [{y:=y+1;{x'=x+y,y'=5}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{y:=y+1;{x'=x+y,y'=5}}*]x>=1".asFormula
    val invs = List("x>=-1".asFormula, "y>=1".asFormula, "x>=0&y>=0".asFormula, "x>=1&y>=1".asFormula, "x>=1&y>=0".asFormula, "x=7".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((seq,pos)=>invs.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x+y,y'=5}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x+y,y'=5}}*]x>=1".asFormula
    val invs = List("x>=-1".asFormula, "y>=1".asFormula, "x>=0&y>=0".asFormula, "x>=1&y>=1".asFormula, "x>=1&y>=0".asFormula, "x=7".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((seq,pos)=>invs.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=1 -> [{y:=y+1;{x'=x^2+2*y+x,y'=y^2+y}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=1 -> [{y:=y+1;{x'=x^2+2*y+x,y'=y^2+y}}*]x>=1".asFormula
    val invs = List("x>=-1".asFormula, "y>=1".asFormula, "x>=0&y>=0".asFormula, "x>=1&y>=1".asFormula, "x>=1&y>=0".asFormula, "x=7".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((seq,pos)=>invs.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=1 -> [{x:=x+y;y:=y+1;{x'=x^2+2*y+x,y'=y^2+y}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=1 -> [{x:=x+y;y:=y+1;{x'=x^2+2*y+x,y'=y^2+y}}*]x>=1".asFormula
    val invs = List("x>=-1".asFormula, "y>=1".asFormula, "x>=0&y>=0".asFormula, "x>=1&y>=1".asFormula, "x>=1&y>=0".asFormula, "x=7".asFormula)
    proveBy(fml, implyR(1) & loopPostMaster((seq,pos)=>invs.toStream)(1)) shouldBe 'proved
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

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;}*]x>=0" in withMathematica { qeTool =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;}*]x>=0".asFormula
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
    //Note: dependency analysis generates (x,y) instead of just x
    val invs2: List[Formula] = invs.map(USubst(Seq(SubstitutionPair(DotTerm(),DotTerm(Real,Some(0)))))(_))
    proveBy(fml, implyR(1) & loopSR((seq,pos)=>invs2.toStream)(1)) shouldBe 'proved
  }

 it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;y:=y+1;}*]x>=0" in withMathematica{qeTool =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;}*]x>=0".asFormula
    val invs = List("._0>=-1 & ._1>=0".asFormula, "._0=5  & ._1>=0".asFormula, "._0>=0 & ._1>=0".asFormula)
    val jj = "j(._0,._1)".asFormula
    val proof = proveBy(fml,
      implyR(1) & SearchAndRescueAgain(jj :: Nil,
        loop(USubst(Seq(SubstitutionPair("._0".asTerm,"x".asTerm), SubstitutionPair("._1".asTerm, "y".asTerm)))(jj))(1) <(nil, nil, chase(1)),
        feedOneAfterTheOther(invs),
        OnAll(master()) & done
      )
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
    proveBy(fml, implyR(1) & loopSR((seq,pos)=>invs.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;{x'=x^2+y}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;{x'=x^2+y}}*]x>=0".asFormula
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
    val invs2: List[Formula] = invs.map(USubst(Seq(SubstitutionPair(DotTerm(),DotTerm(Real,Some(0)))))(_))
    proveBy(fml, implyR(1) & loopSR((seq,pos)=>invs2.toStream)(1)) shouldBe 'proved
  }

  it should "prove x>=5 & y>=0 -> [{{x'=x^2+y,y'=x+1}}*]x>=0 by invariant x>=0&y>=0" in withMathematica{qeTool =>
    val fml = "x>=5 & y>=0 -> [{{x'=x^2+y,y'=x+1}}*]x>=0".asFormula
    proveBy(fml, implyR(1) & loop("x>=0&y>=0".asFormula)(1) <(QE(), QE(), odeInvariant(1))) shouldBe 'proved
  }

  it should "prove x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x+1}}*]x>=0 by invariant x>=0&y>=0" in withMathematica{qeTool =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x+1}}*]x>=0".asFormula
    proveBy(fml, implyR(1) & loop("x>=0&y>=0".asFormula)(1) <(QE(), QE(), composeb(1) & assignb(1) & composeb(1) & assignb(1) &
      odeInvariant(1))) shouldBe 'proved
  }

  it should "prove x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x}}*]x>=0 by invariant x>=0&y>=0" ignore withMathematica{qeTool =>
    // Failing test case because of equilibrium at x=0,y=0
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x}}*]x>=0".asFormula
    proveBy(fml, implyR(1) & loop("x>=0&y>=0".asFormula)(1) <(QE(), QE(), composeb(1) & assignb(1) & composeb(1) & assignb(1) &
      odeInvariant(1))) shouldBe 'proved
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x}}*]x>=0" taggedAs SlowTest ignore withMathematica { _ =>
    // Failing test case
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x}}*]x>=0".asFormula
    val invs = List("._0>=-1 & ._1>=0".asFormula, "._0=5  & ._1>=0".asFormula, "._0>=0 & ._1>=0".asFormula)
    proveBy(fml, implyR(1) & loopSR((seq,pos)=>invs.toStream)(1)) shouldBe 'proved

    val jj = "j(._0,._1)".asFormula
    val proof = proveBy(fml,
      implyR(1) & SearchAndRescueAgain(jj :: Nil,
        loop(USubst(Seq(SubstitutionPair("._0".asTerm,"x".asTerm), SubstitutionPair("._1".asTerm, "y".asTerm)))(jj))(1) <(nil, nil, chase(1)),
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
}
