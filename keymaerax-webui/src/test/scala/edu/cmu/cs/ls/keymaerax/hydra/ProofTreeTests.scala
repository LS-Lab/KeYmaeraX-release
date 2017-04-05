package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.SequentialInterpreter
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.IndexedSeq

/**
  * Tests the proof tree data structure.
  * Created by smitsch on 3/31/17.
  */
class ProofTreeTests extends TacticTestBase {

  "Empty tree" should "have a single goal" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))
    tree.root.children shouldBe empty
    tree.root.goal shouldBe tree.openGoals.head.goal
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
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.localProvable.subgoals should have size 1
    tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.localProvable.subgoals should have size 1
    tree.root.children.head.localProvable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.makerShortName shouldBe "implyR"

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
    //tree.nodes should have size 2
    tree.openGoals shouldBe empty
    tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.localProvable.subgoals should have size 1
    tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.localProvable.subgoals shouldBe empty
    tree.root.children.head.makerShortName shouldBe "QE"
    tree.root.children.head shouldBe 'done

    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.provable.subgoals shouldBe empty
    tree.root.provable shouldBe 'proved

    tree shouldBe 'verifyClosed

    tree.tactic shouldBe QE
  }}

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
    c1.makerShortName shouldBe "implyR"
    c1.children should have size 1
    val c2 = c1.children.head
    c2.localProvable.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    c2.goal shouldBe 'empty
    c2.localProvable.subgoals shouldBe empty
    c2.makerShortName shouldBe "QE"

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
    tree.nodes should have size 2 //@todo does not include open goals
    tree.openGoals should have size 2
    val g1 = tree.openGoals.head
    g1.goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula), IndexedSeq("x>0->x>0".asFormula)))
    g1.makerShortName shouldBe "cut"

    val g2 = tree.openGoals(1)
    g2.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula, "y=37".asFormula)))
    g2.makerShortName shouldBe "cut"

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
    tree.nodes should have size 3 //@todo does not include open goals
    tree.openGoals should have size 2
    val g1 = tree.openGoals.head
    g1.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula, "y=37".asFormula)))
    g1.makerShortName shouldBe "cut"

    val g2 = tree.openGoals(1)
    g2.goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula, "x>0".asFormula), IndexedSeq("x>0".asFormula)))
    g2.makerShortName shouldBe "implyR"

    val p = tree.root.provable
    p.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula))
    p.subgoals should have size 2
    //@todo subgoals and open goals keep switching order
    p.subgoals(0) shouldBe g2.goal.get
    p.subgoals(1) shouldBe g1.goal.get

    tree.tactic shouldBe cut("y=37".asFormula) <(implyR(1), nil)
  }

  "Pruning" should "work at the root" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 2
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.root.pruneBelow()
    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 1
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
    tree.nodes should have size 3 //@todo does not include open goals
    tree.openGoals should have size 2
    val g1 = tree.openGoals.head
    g1.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula, "y=37".asFormula)))
    g1.makerShortName shouldBe "cut"

    val g2 = tree.openGoals(1)
    g2.goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula, "x>0".asFormula), IndexedSeq("x>0".asFormula)))
    g2.makerShortName shouldBe "implyR"

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
    tree.nodes should have size 3 //@todo does not include open goals
    tree.openGoals should have size 2
    val g1 = tree.openGoals.head
    g1.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula, "y=37".asFormula)))
    g1.makerShortName shouldBe "cut"

    val g2 = tree.openGoals(1)
    g2.goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula, "x>0".asFormula), IndexedSeq("x>0".asFormula)))
    g2.makerShortName shouldBe "implyR"

    g2.parent.get.pruneBelow()
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 2
    tree.openGoals(0).goal shouldBe Some(Sequent(IndexedSeq("y=37".asFormula), IndexedSeq("x>0->x>0".asFormula)))
    tree.openGoals(1).goal shouldBe g1.goal
    tree.tactic shouldBe cut("y=37".asFormula) <(nil, nil)
  }

  "Performance" should "not degrade when doing the usual interaction in a loop" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    var avg = 0.0
    var max = 0.0

    for (i <- 1 to 200) {
      val start = System.currentTimeMillis()
      val tree = DbProofTree(db.db, proofId.toString)

      val goals = tree.openGoals //@todo openGoals still slows down with number of steps
      goals should have size 1
      if (i%2==0) goals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
      else goals.head.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))

      if (i%2==0) goals.head.runTactic("guest", SequentialInterpreter, implyRi, "implyRi", wait=true)
      else goals.head.runTactic("guest", SequentialInterpreter, implyR(1), "implyR", wait=true)

      val end = System.currentTimeMillis()
      avg = (avg*(i-1) + (end-start))/i
      max = Math.max(max, end-start)
    }

    DbProofTree(db.db, proofId.toString).tacticString

    println("Average duration " + avg)
    println("Maximum duration " + max)
  }

}
