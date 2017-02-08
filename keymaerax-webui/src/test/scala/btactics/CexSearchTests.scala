package btactics.cexsearch

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.cexsearch._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.{CounterExampleTool, ToolBase, ToolEvidence}

/**
  * Test cases for counterexample search. We generally don't care what the counterexample is as long as it's  a counterexample.
  * Actually evaluating whether a particular example is really a counterexample is nontrivial, so let's just focus on whether
  * it returns a counterexample on false formulas or not.
  * We also care how long different search algos take and how many of our examples they can get right in a given amount of time.
  * Let's make it easy to compare lots of different combinations of search algos and heuristics so we can have some nice graphs
  * for the report.
  * Created by bbohrer on 4/24/16.
  */
class CexSearchTests  extends TacticTestBase {
  val algos: List[(SearchNode => Option[ConcreteState])] =
    List(BreadthFirstSearch)

  /* We should strive for a variety of different difficulty levels, and make sure all formulas have the shape P -> [a] Q for
  * program-free P, or else none of this will work.
  * These are "easy" in the sense that no searching of infinite stuff is required and therefore no search heuristics are
  * necessary, let alone good ways. Still hard in the sense of we need to implement symbolic execution correctly before
  * these will work.
  * */
  val easyTrueFmls = List(
    "false -> [?true;] true",
    "x = 2 -> [?true;] x > 1",
    "x = 2 -> [x := 5;] x > 3",
    "x = 2 -> [?false;] x = 3",
    "x = 2 -> [?x < 1;] x = 3",
    "(x = 7 & y < 3) -> [x := x + 1; y := y + x;](x >= 7.3 & y <= 12)",
    "(x = 0 | (x > 0 -> y = 7)) -> [x := x - 1; y := -y;] (x <= -1 | y = -7)",
    "y = x + 2 -> [x := (x + 2)^2 ;++ ?y >= 2;] x >= 0",
    "y' = x' + 2 -> [x' := (x' + 2)^2 ;++ ?y' >= 2;] x' >= 0",
    "true -> [x :=*;] ((x + 2)^8 >= 0)"
  ).map({case str => str.asFormula})

  val easyFalseFmls = List(
    "true -> [?true;] false",
    "x = 2 -> [?true;] x < 1",
    "x = 2 -> [x := 5;] x < 3",
    "x = 2 -> [?true;] x = 3",
    "x = 2 -> [?x > 1;] x = 3",
    "(x = 7 & y < 3) -> [x := x + 1; y := y + x;](x <= 7.3 | y > 12)",
    "(x = 2 | (x > 10 -> y = 7)) -> [x := x - 1; y := -y;] (x <= -1 | y = -7)",
    "y = x + 2 -> [x := (x + 2)^2 ;++ ?y < -10;] x >= 0",
    "y' = x' + 2 -> [x' := (x' + 2)^2 ;++ ?y' < -10;] x' >= 0"
  ).map({case str => str.asFormula})

  val loopFalseFmls = List(
    "true -> [{?true;}*] false",
    "true -> [x :=*;] x > 0",
    "x=0 -> [{x := x + 1;}*] x < 5"
  ).map({case str => str.asFormula})

  /* Can't hope for a counterexample on most of these */
  val loopTrueFmls = List(
    "x=0 -> [{x := x + 1;}*] x >= 5".asFormula
  )

  "Every algorithm" should "get the easy true cases right" in withMathematica(implicit qeTool => {
    algos.foreach({case algo =>
      easyTrueFmls.foreach({case fml =>
        algo(ProgramSearchNode(fml)).isDefined shouldBe false
      })
    })
  })

  it should "get the easy false cases right" in withMathematica(implicit qeTool => {
    algos.foreach({case algo =>
      easyFalseFmls.foreach({case fml =>
        val result = algo(ProgramSearchNode(fml))
        print("Testing algo " + algo.getClass.getSimpleName + " for falseness of " + fml + "\n")
        result.isDefined shouldBe true
      })
    })
  })

  it should "get the false loop cases right" in withMathematica(implicit qeTool => {
    algos.foreach({ case algo =>
      loopFalseFmls.foreach({ case fml =>
        val result = algo(ProgramSearchNode(fml))
        print("Testing algo " + algo.getClass.getSimpleName + " for falseness of " + fml + "\n")
        result.isDefined shouldBe true
      })
    })
  })

  it should "loop on this test" in withMathematica(implicit qeTool => {
    algos.foreach({ case algo =>
      loopTrueFmls.foreach({ case fml =>
        val result = algo(ProgramSearchNode(fml))
        print("Testing algo " + algo.getClass.getSimpleName + " for falseness of " + fml + "\n")
        result.isDefined shouldBe true
      })
    })
  })

}
