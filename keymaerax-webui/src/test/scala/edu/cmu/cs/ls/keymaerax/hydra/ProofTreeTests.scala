package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, SequentialInterpreter, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.{FormulaArg, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.IndexedSeq

import org.scalatest.LoneElement._

/**
  * Tests the proof tree data structure.
  * Created by smitsch on 3/31/17.
  */
class ProofTreeTests extends TacticTestBase {

  "Empty tree" should "have a single goal" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))
    tree.root.children shouldBe empty
    tree.root.goal shouldBe tree.openGoals.head.goal
    tree.locate("()").get.goal shouldBe tree.root.goal
    tree.tactic shouldBe nil
  }

  "Tactic execution" should "create a tree with one open goal from implyR" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR")::Nil
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.localProvable.subgoals should have size 1
    tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.localProvable.subgoals should have size 1
    tree.root.children.head.localProvable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.makerShortName shouldBe Some("implyR")
    tree.locate("(1,0)").get.goal shouldBe tree.root.children.head.goal

    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.provable.subgoals should have size 1
    tree.root.provable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))

    tree.tactic shouldBe implyR(1)
  }

  it should "create a proved tree from QE" in withDatabase { db => withMathematica { _ =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, QE, "QE", wait=true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("QE")::Nil
    tree.openGoals shouldBe empty
    tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.localProvable.subgoals should have size 1
    tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.localProvable.subgoals shouldBe empty
    tree.root.children.head.makerShortName shouldBe Some("QE")
    tree.root.children.head shouldBe 'done
    tree.locate("(1,0)").get.goal shouldBe tree.root.children.head.goal

    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.provable.subgoals shouldBe empty
    tree.root.provable shouldBe 'proved

    tree shouldBe 'verifyClosed

    tree.tactic shouldBe QE
  }}

  it should "not forget about open goals when a step fails" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> [x:=x+1;]x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.goal shouldBe Some("x>0 ==> [x:=x+1;]x>0".asSequent)
    tree.openGoals.loneElement.runTactic("guest", SequentialInterpreter, solve(1), "solve", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.goal shouldBe Some("x>0 ==> [x:=x+1;]x>0".asSequent)
  }

  it should "create a proved tree from implyR ; QE" in withDatabase { db => withMathematica { _ =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, QE, "QE", wait=true)

    val rt = DbProofTree(db.db, proofId.toString)
    rt.nodes should have size 3
    rt.openGoals shouldBe empty
    rt.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    rt.root.localProvable.subgoals should have size 1
    rt.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    rt.root.children should have size 1
    val c1 = rt.root.children.head
    c1.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    c1.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    c1.localProvable.subgoals should have size 1
    c1.makerShortName shouldBe Some("implyR")
    rt.locate("(1,0)").get.goal shouldBe c1.goal
    c1.children should have size 1
    val c2 = c1.children.head
    c2.localProvable.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    c2.goal shouldBe 'empty
    c2.localProvable.subgoals shouldBe empty
    c2.makerShortName shouldBe Some("QE")
    rt.locate("(2,0)").get.goal shouldBe c2.goal

    rt.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    rt.root.provable.subgoals shouldBe empty
    rt.root.provable shouldBe 'proved

    rt shouldBe 'verifyClosed

    rt.tactic shouldBe implyR(1) & QE
  }}

  it should "create a tree with two open goals with a cut" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, cut("y=37".asFormula), "cut", wait = true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 3
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("cut")::Some("cut")::Nil
    tree.openGoals should have size 2
    val g1 = tree.openGoals.head
    g1.goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula), IndexedSeq("x>0->x>0".asFormula)))
    g1.makerShortName shouldBe Some("cut")
    tree.locate("(1,0)").get.goal shouldBe g1.goal

    val g2 = tree.openGoals(1)
    g2.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula, "y=37".asFormula)))
    g2.makerShortName shouldBe Some("cut")
    tree.locate("(1,1)").get.goal shouldBe g2.goal

    val p = tree.root.provable
    p.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula))
    p.subgoals should have size 2
    p.subgoals(0) shouldBe g1.goal.get
    p.subgoals(1) shouldBe g2.goal.get
  }

  it should "continue on the correct subgoal after a cut" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, cut("y=37".asFormula), "cut", wait = true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait = true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 4
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("cut")::Some("cut")::Some("implyR")::Nil
    tree.openGoals should have size 2
    val g1 = tree.openGoals.head
    g1.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula, "y=37".asFormula)))
    g1.makerShortName shouldBe Some("cut")
    tree.locate("(1,1)").get.goal shouldBe g1.goal

    val g2 = tree.openGoals(1)
    g2.goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula, "x>0".asFormula), IndexedSeq("x>0".asFormula)))
    g2.makerShortName shouldBe Some("implyR")
    tree.locate("(1,0)").get.goal shouldBe Some(g2.conclusion)
    tree.locate("(2,0)").get.goal shouldBe g2.goal

    val p = tree.root.provable
    p.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula))
    p.subgoals should have size 2
    //@todo subgoals and open goals keep switching order
    p.subgoals(0) shouldBe g2.goal.get
    p.subgoals(1) shouldBe g1.goal.get

    tree.tactic shouldBe cut("y=37".asFormula) <(implyR(1), nil)
  }

  "Tactic suggestion" should "return single-pos tactics" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    val tactics = tree.openGoals.head.applicableTacticsAt(SuccPosition(1))
    tactics should have size 1
    tactics.head._1.codeName shouldBe "implyR"
  }

  it should "return single-pos tactics with input suggestions" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. [{x:=x+1;}*@invariant(x>7)]x>5 End."
    val proofId = db.createProof(modelContent)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    val tactics = tree.openGoals.head.applicableTacticsAt(SuccPosition(1))
    tactics should have size 4
    tactics.map(_._1.codeName) should contain theSameElementsAs "loop"::"iterateb"::"GV"::"boxd"::Nil
    val inputSuggestions = tree.openGoals.head.tacticInputSuggestions(SuccPosition(1))
    inputSuggestions should have size 1
    inputSuggestions.head shouldBe (FormulaArg("j(x)") -> "x>7".asFormula)
  }

  it should "return two-pos tactics" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0->x>0 End."
    val proofId = db.createProof(modelContent)
    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    val tactics = tree.openGoals.head.applicableTacticsAt(AntePosition(1), Some(SuccPosition(1)))
    tactics should have size 1
    tactics.head._1.codeName shouldBe "closeId"
  }

  "Proof loading" should "create the same tree as ripple loading from empty proof" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0->x>0 End."
    val proofId = db.createProof(modelContent)
    val st = DbProofTree(db.db, proofId.toString)
    val ft = st.load(withProvables=true)

    ft.root.parent shouldBe st.root.parent
    ft.openGoals should have size st.openGoals.size
    ft.openGoals.zip(st.openGoals).foreach({ case (ftn, stn) => ftn.goal shouldBe stn.goal })
  }

  it should "create the same tree as ripple loading from proof with steps" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0->x>0 End."
    val proofId = db.createProof(modelContent)

    val numStepsPerProof = 5
    for (i <- 0 until numStepsPerProof) {
      val st = DbProofTree(db.db, proofId.toString)
      val ft = st.load(withProvables=true)

      ft.root.parent shouldBe st.root.parent
      ft.openGoals should have size st.openGoals.size
      ft.openGoals.zip(st.openGoals).foreach({ case (ftn, stn) => ftn.goal shouldBe stn.goal })
      ft.openGoals.head.applicableTacticsAt(SuccPosition(1)) shouldBe st.openGoals.head.applicableTacticsAt(SuccPosition(1))

      if (i % 2 == 1) ft.openGoals.head.runTactic("guest", SequentialInterpreter, implyRi, "implyRi", wait = true)
      else ft.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait = true)
    }
  }

  it should "create the same tree as ripple loading from proof with steps that do not have provables" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0->x>0 End."
    val proofId = db.createProof(modelContent)

    val numStepsPerProof = 5
    for (i <- 0 until numStepsPerProof) {
      val st = DbProofTree(db.db, proofId.toString)
      val ft = st.load(withProvables=false)

      ft.root.parent shouldBe st.root.parent
      ft.openGoals should have size st.openGoals.size
      ft.openGoals.zip(st.openGoals).foreach({ case (ftn, stn) => ftn.goal shouldBe stn.goal })

      ft.openGoals.head.applicableTacticsAt(SuccPosition(1)) shouldBe st.openGoals.head.applicableTacticsAt(SuccPosition(1))

      if (i % 2 == 1) ft.openGoals.head.runTactic("guest", SequentialInterpreter, implyRi, "implyRi", wait = true)
      else ft.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait = true)
    }
  }

  "Pruning" should "work at the root" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR")::Nil
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.root.pruneBelow()
    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 1
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Nil
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))
  }

  it should "prune all subgoals when pruning a cut" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, cut("y=37".asFormula), "cut", wait = true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait = true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 4
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("cut")::Some("cut")::Some("implyR")::Nil
    tree.openGoals should have size 2
    val g1 = tree.openGoals.head
    g1.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula, "y=37".asFormula)))
    g1.makerShortName shouldBe Some("cut")

    val g2 = tree.openGoals(1)
    g2.goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula, "x>0".asFormula), IndexedSeq("x>0".asFormula)))
    g2.makerShortName shouldBe Some("implyR")

    tree.root.pruneBelow()
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))
    tree.tactic shouldBe nil
  }

  it should "prune only one subgoal of a cut" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, cut("y=37".asFormula), "cut", wait = true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait = true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 4
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("cut")::Some("cut")::Some("implyR")::Nil
    tree.openGoals should have size 2
    val g1 = tree.openGoals.head
    g1.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula, "y=37".asFormula)))
    g1.makerShortName shouldBe Some("cut")

    val g2 = tree.openGoals(1)
    g2.goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula, "x>0".asFormula), IndexedSeq("x>0".asFormula)))
    g2.makerShortName shouldBe Some("implyR")

    g2.parent.get.pruneBelow()
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 2
    tree.openGoals(0).goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula), IndexedSeq("x>0->x>0".asFormula)))
    tree.openGoals(1).goal shouldBe g1.goal
    tree.tactic shouldBe cut("y=37".asFormula) <(nil, nil)
  }

  "Performance" should "not degrade when doing the usual interaction (without tactic extraction) in a loop" in withDatabase { db =>
    val modelContent = "Variables. R x. End.\nProblem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val numStepsPerProof = 1000
    var durations = Array.fill(numStepsPerProof)(0.0)

    for (i <- 0 until numStepsPerProof) {
      val start = System.currentTimeMillis()
      val tree = DbProofTree(db.db, proofId.toString)
      val treeConstructed = System.currentTimeMillis()
      val goals = tree.openGoals
      val openGoalsFetched = System.currentTimeMillis()
      goals should have size 1
      if (i%2==1) goals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
      else goals.head.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))

      val tactics = goals.head.applicableTacticsAt(SuccPosition(1))
      goals.head.tacticInputSuggestions(SuccPosition(1)) shouldBe empty

      if (i%2==1) tactics shouldBe empty
      else { tactics should have size 1; tactics.head._1.codeName shouldBe "implyR" }

      val tacticSuggestionFetch = System.currentTimeMillis()

      if (i%2==1) goals.head.runTactic("guest", SequentialInterpreter, implyRi, "implyRi", wait=true)
      else goals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)
      val tacticExecuted = System.currentTimeMillis()

      val end = System.currentTimeMillis()

      println(s"Run $i, duration ${end-start}: construction=${treeConstructed-start}, goals=${openGoalsFetched-treeConstructed}, suggestion=${tacticSuggestionFetch-openGoalsFetched}, execution=${tacticExecuted-tacticSuggestionFetch}")

      durations(i) = end-start
    }

    DbProofTree(db.db, proofId.toString).tacticString

    val medianDuration = median(durations.toList)
    val averageDuration = durations.sum/numStepsPerProof
    println("Median duration " + medianDuration)
    println("Average duration " + averageDuration)
    println("Minimum duration " + durations.min + " (iteration " + durations.indexOf(durations.min) + ")")
    println("Maximum duration " + durations.max + " (iteration " + durations.indexOf(durations.max) + ")")
  }

  it should "not degrade too much when doing the usual interaction with tactic extraction in a loop" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val numStepsPerProof = 200
    var durations = Array.fill(numStepsPerProof)(0.0)

    for (i <- 0 until numStepsPerProof) {
      val start = System.currentTimeMillis()
      val tree = DbProofTree(db.db, proofId.toString)

      tree.tacticString

      val goals = tree.openGoals
      goals should have size 1
      if (i%2==1) goals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
      else goals.head.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))

      val tactics = goals.head.applicableTacticsAt(SuccPosition(1))
      goals.head.tacticInputSuggestions(SuccPosition(1)) shouldBe empty

      if (i%2==1) tactics shouldBe empty
      else { tactics should have size 1; tactics.head._1.codeName shouldBe "implyR" }

      if (i%2==1) goals.head.runTactic("guest", SequentialInterpreter, implyRi, "implyRi", wait=true)
      else goals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)

      val end = System.currentTimeMillis()
      durations(i) = end-start
    }

    DbProofTree(db.db, proofId.toString).tacticString

    val medianDuration = median(durations.toList)
    val averageDuration = durations.sum/numStepsPerProof
    println("Median duration " + medianDuration)
    println("Average duration " + averageDuration)
    println("Minimum duration " + durations.min)
    println("Maximum duration " + durations.max)
  }

  it should "not degrade over multiple proofs" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."

    val numProofs = 10
    val numStepsPerProof = 100

    val avg = Array.fill(numProofs)(0.0)
    val max = Array.fill(numProofs)(0.0)

    for (proof <- 0 until numProofs) {
      val proofId = db.createProof(modelContent, "Proof"+proof)
      for (i <- 1 to numStepsPerProof) {
        val start = System.currentTimeMillis()
        val tree = DbProofTree(db.db, proofId.toString)

        val goals = tree.openGoals
        goals should have size 1
        if (i%2==0) goals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
        else goals.head.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))

        val tactics = goals.head.applicableTacticsAt(SuccPosition(1))
        goals.head.tacticInputSuggestions(SuccPosition(1)) shouldBe empty

        if (i%2==0) tactics shouldBe empty
        else { tactics should have size 1; tactics.head._1.codeName shouldBe "implyR" }

        if (i%2==0) goals.head.runTactic("guest", SequentialInterpreter, implyRi, "implyRi", wait=true)
        else goals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)

        val end = System.currentTimeMillis()
        avg(proof) = (avg(proof)*(i-1) + (end-start))/i
        max(proof) = Math.max(max(proof), end-start)
      }
    }

    println("Average durations " + avg.map(_.toInt).mkString(","))
    println("Maximum durations " + max.map(_.toInt).mkString(","))

    val medianAverages = median(avg.toList)
    val avgAverages = avg.sum/avg.length
    println("Average averages " + avgAverages)
    println("Median averages " + medianAverages)
  }

  private def median(s: List[Double]): Double = {
    val (lower, upper) = s.sortWith(_<_).splitAt(s.size/2)
    if (s.size%2 == 0) (lower.last + upper.head)/2.0 else upper.head
  }
}
