/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics


import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, Context, TactixLibrary, UnifyUSCalculus}
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

  "No DoSome" should "follow the right cut for x>=7 -> x>=5" in withMathematica { implicit qeTool =>
    proveBy("x>=7 -> x>=5".asFormula,
      implyR(1) &
        cutR("x>=6".asFormula)(SuccPosition(1).top) & DoAll(QE)
    )
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 by invariant" in withMathematica { implicit qeTool =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        diffInvariant("x>=5".asFormula)(1) & diffWeaken(1) & QE
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{{x'=2}}*]x>=5 by loop invariants" in withMathematica { implicit qeTool =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        loop("x>=5".asFormula)(1) <(
          QE
          ,
          QE
          ,
            diffSolve()(1) & DoAll(QE)
      )
    ) shouldBe 'proved
  }

  "DoSome" should "find the right cut for x>=7 -> x>=5" in withMathematica { implicit qeTool =>
    proveBy("x>=7 -> x>=5".asFormula,
      implyR(1) &
        DoSome(someList, (c:Formula) => cutR(c)(SuccPosition(1).top) & DoAll(QE))
    )
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 from one invariant" in withMathematica { implicit qeTool =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        DoSome(() => ("x>=5".asFormula :: Nil).iterator, (inv:Formula) => diffInvariant(inv)(1) & diffWeaken(1) & QE)
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 from list of invariants" in withMathematica { implicit qeTool =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
      DoSome(someList, (inv:Formula) => diffInvariant(inv)(1) & diffWeaken(1) & QE)
    ) shouldBe 'proved
  }

  it should "generate and master prove x>=5 -> [{x'=x^2}]x>=5 from list of invariants" in withMathematica { implicit qeTool =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        DoSome(someList, (inv:Formula) => diffInvariant(inv)(1) & master())
    ) shouldBe 'proved
  }


  it should "prove x>=5 -> [{{x'=2}}*]x>=5 from one loop invariants" in withMathematica { implicit qeTool =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        DoSome(() => ("x>=5".asFormula :: Nil).iterator, (inv:Formula) => loop(inv)(1) <(
          QE
          ,
          QE
          ,
          diffSolve()(1) & DoAll(QE)
          ))
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{{x'=2}}*]x>=5 from list of loop invariants" in withMathematica { implicit qeTool =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        DoSome(someList, (inv:Formula) => loop(inv)(1) <(
            QE
            ,
            QE
            ,
            diffSolve()(1) & DoAll(QE)
            ))
    ) shouldBe 'proved
  }

  it should "generate and master prove x>=5 -> [{{x'=2}}*]x>=5 from list of loop invariants" in withMathematica { implicit qeTool =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        DoSome(someList, (inv:Formula) => loop(inv)(1) & master())
    ) shouldBe 'proved
  }
}
