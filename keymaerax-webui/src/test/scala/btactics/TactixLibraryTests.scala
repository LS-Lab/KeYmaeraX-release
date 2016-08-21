/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics


import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable._

/**
 * Tactix Library Test.
 * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class TactixLibraryTests extends TacticTestBase {
  private val someList: () => Iterator[Formula] = () =>
      ("x>=4".asFormula :: "x>=6".asFormula :: "x<2".asFormula :: "x>=5".asFormula :: "x>=0".asFormula :: Nil).iterator

  "DoLoneSome not ChooseSome" should "follow the right cut for x>=7 -> x>=5" in withMathematica { qeTool =>
    proveBy("x>=7 -> x>=5".asFormula,
      implyR(1) &
        cutR("x>=6".asFormula)(SuccPosition(1).top) & OnAll(QE)
    )
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 by invariant" in withMathematica { qeTool =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        diffInvariant("x>=5".asFormula)(1) & diffWeaken(1) & QE
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{{x'=2}}*]x>=5 by loop invariants" in withMathematica { qeTool =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        loop("x>=5".asFormula)(1) <(
          QE
          ,
          QE
          ,
            diffSolve()(1) & OnAll(QE)
      )
    ) shouldBe 'proved
  }

  "ChooseSome" should "find the right cut for x>=7 -> x>=5" in withMathematica { qeTool =>
    proveBy("x>=7 -> x>=5".asFormula,
      implyR(1) &
        ChooseSome(someList, (c:Formula) => cutR(c)(SuccPosition(1).top) & OnAll(QE))
    )
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 from one invariant" in withMathematica { qeTool =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        ChooseSome(() => ("x>=5".asFormula :: Nil).iterator, (inv:Formula) => diffInvariant(inv)(1) & diffWeaken(1) & QE)
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 from list of invariants" in withMathematica { qeTool =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
      ChooseSome(someList, (inv:Formula) => diffInvariant(inv)(1) & diffWeaken(1) & QE)
    ) shouldBe 'proved
  }

  it should "generate and master prove x>=5 -> [{x'=x^2}]x>=5 from list of invariants" in withMathematica { qeTool =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        //@note master() together with ChooseSome leaves goals open, if first alternative doesn't QE --> demand QE after master
        ChooseSome(someList, (inv:Formula) => diffInvariant(inv)(1) & diffWeaken(1) & (master() & QE))
    ) shouldBe 'proved
  }


  it should "prove x>=5 -> [{{x'=2}}*]x>=5 from one loop invariants" in withMathematica { qeTool =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        ChooseSome(() => ("x>=5".asFormula :: Nil).iterator, (inv:Formula) => loop(inv)(1) <(
          QE
          ,
          QE
          ,
          diffSolve()(1) & OnAll(QE)
          ))
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{{x'=2}}*]x>=5 from list of loop invariants" in withMathematica { qeTool =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        ChooseSome(someList, (inv:Formula) => loop(inv)(1) <(
            QE
            ,
            QE
            ,
            diffSolve()(1) & OnAll(QE)
            ))
    ) shouldBe 'proved
  }

  it should "generate and master prove x>=5 -> [{{x'=2}}*]x>=5 from list of loop invariants" in withMathematica { qeTool =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        //@note master() together with ChooseSome leaves goals open, if first alternative doesn't QE --> demand QE after master
        ChooseSome(someList, (inv:Formula) => loop(inv)(1) & (master() & QE))
    ) shouldBe 'proved
  }

  "LetInspect" should "post-hoc instantiate a j closing \\exists j 5+3=j" in withMathematica{qeTool =>
    val proof = proveBy("\\exists jj 5+3=jj".asFormula,
      LetInspect("j()".asTerm,
        (pr:Provable) => pr.subgoals.head.succ.head match {
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

  it should "post-hoc instantiate a j(||) closing \\exists j 5+3=j" in withMathematica{qeTool =>
    val proof = proveBy("\\exists jj 5+3=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:Provable) => pr.subgoals.head.succ.head match {
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

  ignore should "post-hoc instantiate a j closing \\exists j (x+x)'=j" in withMathematica{qeTool =>
    val proof = proveBy("\\exists jj (x+x)'=jj".asFormula,
      LetInspect("j(.)".asTerm,
        (pr:Provable) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => l
        }
        ,
        existsR("j(x)".asTerm)(1) &
        derive(1, 0::Nil))
        & byUS("= reflexive"))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x)'=jj".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc find a j() closing (x+x*y)'=j()" in withMathematica{qeTool =>
    val proof = proveBy("\\exists jj (x+x*y)'=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:Provable) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => l
        }
        ,
        existsR("j()".asTerm)(1) &
          derive(1, 0::Nil))
        & byUS("= reflexive"))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x*y)'=jj".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc find a j() closing j()=(x+x*y)'" in withMathematica{qeTool =>
    val proof = proveBy("\\exists jj jj=(x+x*y)'".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:Provable) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => r
        }
        ,
        existsR("j()".asTerm)(1) &
        derive(1, 1::Nil))
        & byUS("= reflexive"))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj jj=(x+x*y)'".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc find a j(||) closing (x+x*y)'=j(||)" in withMathematica{qeTool =>
    val proof = proveBy("\\exists jj (x+x*y)'=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:Provable) => pr.subgoals.head.succ.head match {
          case Equal(l,r) => l
        }
        ,
        existsR("j(||)".asTerm)(1) &
          derive(1, 0::Nil))
        & byUS("= reflexive"))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x*y)'=jj".asFormula))
    proof shouldBe 'proved
  }
}
