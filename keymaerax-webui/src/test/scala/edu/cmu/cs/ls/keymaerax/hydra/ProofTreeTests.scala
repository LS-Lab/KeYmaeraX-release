package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, ExhaustiveSequentialInterpreter, LazySequentialInterpreter, Let, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.btactics.{BelleLabels, Idioms, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, SuccPosition}
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import edu.cmu.cs.ls.keymaerax.btactics.macros._

import scala.collection.immutable.{IndexedSeq, List}
import org.scalatest.LoneElement._
import testHelper.KeYmaeraXTestTags.TodoTest

/**
  * Tests the proof tree data structure.
  * Created by smitsch on 3/31/17.
  */
class ProofTreeTests extends TacticTestBase {

  "Empty tree" should "have a single goal" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))
    tree.root.children shouldBe empty
    tree.root.goal shouldBe tree.openGoals.head.goal
    tree.locate("()").get.goal shouldBe tree.root.goal
    tree.tactic shouldBe todo
  }}

  "Tactic execution" should "create a tree with one open goal from implyR" in withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)

    tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR")::Nil
    tree.openGoals.loneElement.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
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
    tree.root.provable.subgoals.loneElement shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))

    tree.tactic shouldBe implyR('R, "x>0 -> x>0".asFormula) & todo
  }

  it should "create a proved tree from QE" in withDatabase { db => withMathematica { _ =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), QE, "QE", wait=true)

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
    tree.root.children.head shouldBe 'proved
    tree.locate("(1,0)").get.goal shouldBe tree.root.children.head.goal

    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.provable.subgoals shouldBe empty
    tree.root.provable shouldBe 'proved

    tree shouldBe 'proved

    tree.tactic shouldBe QE
  }}

  it should "not forget about open goals when a step fails" in withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> [x:=x+1;]x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.goal shouldBe Some("x>0 ==> [x:=x+1;]x>0".asSequent)
    the [TacticInapplicableFailure] thrownBy
      tree.openGoals.loneElement.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), solve(1), "solve", wait=true) should
      have message "Position 1 does not point to a differential equation, but to [x:=x+1;]x>0"
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.goal shouldBe Some("x>0 ==> [x:=x+1;]x>0".asSequent)
  }

  it should "create a proved tree from implyR ; QE" in withDatabase { db => withMathematica { _ =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), QE, "QE", wait=true)

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

    rt shouldBe 'proved

    rt.tactic shouldBe implyR('R, "x>0 -> x>0".asFormula) & QE
  }}

  it should "create a tree with two open goals with a cut" in withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), cut("y=37".asFormula), "cut", wait = true)

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
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), cut("y=37".asFormula), "cut", wait = true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait = true)

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

    tree.tactic shouldBe cut("y=37".asFormula) & Idioms.<(BelleLabels.cutUse -> (implyR('R, "x>0->x>0".asFormula) & todo), BelleLabels.cutShow -> todo)
  }

  "Tactic suggestion" should "return single-pos tactics" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    val tactics = tree.openGoals.head.applicableTacticsAt(SuccPosition(1))
    tactics should have size 2
    tactics(0)._1.codeName shouldBe "implyR"
    tactics(1)._1.codeName shouldBe "chaseAt"
  }}

  it should "return single-pos tactics with input suggestions" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem [{x:=x+1;}*@invariant(x>7)]x>5 End. End."""
    val proofId = db.createProof(modelContent)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    val tactics = tree.openGoals.head.applicableTacticsAt(SuccPosition(1))
    tactics should have size 3
    tactics.map(_._1.codeName) should contain theSameElementsAs "loop"::"iterateb"::"GV"::Nil
    tree.openGoals.head.tacticInputSuggestions(SuccPosition(1)).loneElement shouldBe (FormulaArg("J") -> "x>7".asFormula)
  }}

  it should "return two-pos tactics" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0->x>0 End. End."""
    val proofId = db.createProof(modelContent)
    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.applicableTacticsAt(AntePosition(1), Some(SuccPosition(1))).loneElement._1.codeName shouldBe "closeId"
  }}

  "Proof loading" should "create the same tree as ripple loading from empty proof" in withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0->x>0 End. End."""
    val proofId = db.createProof(modelContent)
    val st = DbProofTree(db.db, proofId.toString)
    val ft = st.load(withProvables=true)

    ft.root.parent shouldBe st.root.parent
    ft.openGoals should have size st.openGoals.size
    ft.openGoals.zip(st.openGoals).foreach({ case (ftn, stn) => ftn.goal shouldBe stn.goal })
  }

  it should "create the same tree as ripple loading from proof with steps" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0->x>0 End. End."""
    val proofId = db.createProof(modelContent)

    val numStepsPerProof = 5
    for (i <- 0 until numStepsPerProof) {
      val st = DbProofTree(db.db, proofId.toString)
      val ft = st.load(withProvables=true)

      ft.root.parent shouldBe st.root.parent
      ft.openGoals should have size st.openGoals.size
      ft.openGoals.zip(st.openGoals).foreach({ case (ftn, stn) => ftn.goal shouldBe stn.goal })
      ft.openGoals.head.applicableTacticsAt(SuccPosition(1)) shouldBe st.openGoals.head.applicableTacticsAt(SuccPosition(1))

      if (i % 2 == 1) ft.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyRi, "implyRi", wait = true)
      else ft.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait = true)
    }
  }}

  it should "create the same tree as ripple loading from proof with steps that do not have provables" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0->x>0 End. End."""
    val proofId = db.createProof(modelContent)

    val numStepsPerProof = 5
    for (i <- 0 until numStepsPerProof) {
      val st = DbProofTree(db.db, proofId.toString)
      val ft = st.load(withProvables=false)

      ft.root.parent shouldBe st.root.parent
      ft.openGoals should have size st.openGoals.size
      ft.openGoals.zip(st.openGoals).foreach({ case (ftn, stn) => ftn.goal shouldBe stn.goal })

      ft.openGoals.head.applicableTacticsAt(SuccPosition(1)) shouldBe st.openGoals.head.applicableTacticsAt(SuccPosition(1))

      if (i % 2 == 1) ft.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyRi, "implyRi", wait = true)
      else ft.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait = true)
    }
  }}

  "Pruning" should "work at the root" in withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)

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
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), cut("y=37".asFormula), "cut", wait = true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait = true)

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
    tree.tactic shouldBe todo
  }

  it should "prune only one subgoal of a cut" in withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    var tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), cut("y=37".asFormula), "cut", wait = true)
    tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait = true)

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
    tree.tactic shouldBe cut("y=37".asFormula) & Idioms.<(BelleLabels.cutUse -> todo, BelleLabels.cutShow -> todo)
  }

  private def checkTree(db: DBAbstraction, proofId: Int, tactic: BelleExpr, expected: Sequent,
                        expectOpenGoals: List[Sequent] = Nil): ProvableSig = {
    var tree = DbProofTree(db, proofId.toString)
    tree.openGoals.loneElement.runTactic("guest",
      LazySequentialInterpreter(_, throwWithDebugInfo = false), tactic, "proof", wait = true)
    tree = DbProofTree(db, proofId.toString)
    val p = tree.root.provable
    if (expectOpenGoals.isEmpty) {
      p shouldBe 'proved
      tree.openGoals shouldBe 'empty
    } else {
      tree.openGoals.flatMap(_.goal) should contain theSameElementsInOrderAs expectOpenGoals
    }
    p.conclusion shouldBe expected
    p
  }

  "Delayed substitution" should "create a provable with expanded definitions from expand/expandAllDefs" in withTactics { withDatabase { db => withMathematica { _ =>
    val modelContent =
      """
        |ArchiveEntry "Delayed Substitution"
        |
        |Definitions
        |  Real sq(Real x) = x*x;
        |  Bool init(Real x) <-> sq(x)=0;
        |  Bool inv(Real x)  <-> x>=0;
        |  Bool safe(Real x) <-> x>=0;
        |  HP inc ::= { x:=x+1; };
        |End.
        |
        |ProgramVariables
        |  Real x;
        |End.
        |
        |Problem
        |  init(x) -> [{inc;inc;inc;}*@invariant(inv(x))]safe(x)
        |End.
        |
        |Tactic "Delayed Substitution Test: Proof"
        |implyR(1) ; loop("inv(x)", 1) ; <(
        |  expandAllDefs(); QE,
        |  expand("inv"); expand("safe"); id,
        |  expand("inv"); expand("inc"); unfold ; QE
        |  )
        |End.
        |
        |End.
        |""".stripMargin
    val proofId = db.createProof(modelContent)

    val tactic = ArchiveParser(modelContent).loneElement.tactics.loneElement._3
    checkTree(db.db, proofId, tactic, "==> x*x=0 -> [{x:=x+1;x:=x+1;x:=x+1;}*]x>=0".asSequent)
  }}}

  it should "create a provable with expanded definitions from US tactic" in withDatabase { db => withMathematica { _ =>
    val modelContent =
      """
        |ArchiveEntry "Delayed Substitution"
        |
        |Definitions
        |  Real sq(Real x) = x*x;
        |  Bool init(Real x) <-> sq(x)=0;
        |  Bool inv(Real x)  <-> x>=0;
        |  Bool safe(Real x) <-> x>=0;
        |  HP inc ::= { x:=x+1; };
        |End.
        |
        |ProgramVariables
        |  Real x;
        |End.
        |
        |Problem
        |  init(x) -> [{inc;inc;inc;}*@invariant(inv(x))]safe(x)
        |End.
        |
        |Tactic "Delayed Substitution Test: Proof"
        |implyR(1) ; loop("inv(x)", 1) ; <(
        |  US("init(•)~>sq(•)=0") ; US("inv(•)~>•>=0") ; US("sq(•)~>•*•") ; QE,
        |  US("inv(•)~>•>=0") ; US("safe(•)~>•>=0") ; id,
        |  US("inv(•)~>•>=0") ; US("inc{|^@|};~>x:=x+1;") ; unfold ; QE
        |  )
        |End.
        |
        |End.
        |""".stripMargin
    val proofId = db.createProof(modelContent)

    val tactic = ArchiveParser(modelContent).loneElement.tactics.loneElement._3
    checkTree(db.db, proofId, tactic, "==> x*x=0 -> [{x:=x+1;x:=x+1;x:=x+1;}*]x>=0".asSequent)
  }}

  it should "create a provable with expanded definitions with the lazy interpreter" in withDatabase { db => withMathematica { _ =>
    val modelContent =
      """
        |ArchiveEntry "Delayed Substitution"
        |
        |Definitions
        |  Real sq(Real x) = x*x;
        |  Bool init(Real x) <-> sq(x)=0;
        |  Bool inv(Real x)  <-> x>=0;
        |  Bool safe(Real x) <-> x>=0;
        |  HP inc ::= { x:=x+1; };
        |End.
        |
        |ProgramVariables
        |  Real x;
        |End.
        |
        |Problem
        |  init(x) -> [{inc;inc;inc;}*@invariant(inv(x))]safe(x)
        |End.
        |
        |Tactic "Delayed Substitution Test: Proof"
        |implyR(1) ; loop("inv(x)", 1) ; <(
        |  US("init(•)~>sq(•)=0") ; US("inv(•)~>•>=0") ; US("sq(•)~>•*•") ; QE,
        |  US("inv(•)~>•>=0") ; US("safe(•)~>•>=0") ; id,
        |  US("inv(•)~>•>=0") ; US("inc{|^@|};~>x:=x+1;") ; unfold ; QE
        |  )
        |End.
        |
        |End.
        |""".stripMargin
    val proofId = db.createProof(modelContent)

    val tactic = ArchiveParser(modelContent).loneElement.tactics.loneElement._3
    checkTree(db.db, proofId, tactic, "==> x*x=0 -> [{x:=x+1;x:=x+1;x:=x+1;}*]x>=0".asSequent)
  }}

  it should "work with lemmas that expand all definitions" in withDatabase { db => withMathematica { _ =>
    val modelContent =
      """SharedDefinitions
        |  Real sq(Real x) = x*x;
        |  Bool gt(Real x, Real y) <-> x>y;
        |End.
        |
        |Lemma "user/tests/Lemma 1"
        |
        |ProgramVariables
        |  Real x, y;
        |End.
        |
        |Problem
        |  gt(x,sq(y)) -> gt(x,sq(y))
        |End.
        |
        |Tactic "Lemma Proof"
        |  expandAllDefs(); implyR(1); id
        |End.
        |
        |End.
        |
        |ArchiveEntry "user/tests/Delayed Substitution"
        |
        |ProgramVariables
        |  Real x, y;
        |End.
        |
        |Problem
        |  gt(x,sq(y)) -> gt(x,sq(y)) & x>=sq(y)
        |End.
        |
        |Tactic "Delayed Substitution Test with Lemmas: Proof"
        |implyR(1) ; andR(1) ; <(
        |  useLemma("tests/Lemma 1", "prop"),
        |  expand("gt"); abbrv("sq(y)"); hideL('Llast); QE
        |  )
        |End.
        |
        |End.
        |""".stripMargin

    val lemma :: theorem :: Nil = ArchiveParser(modelContent)

    val lemmaId = db.createProof(lemma.fileContent)
    val provedLemma = checkTree(db.db, lemmaId, lemma.tactics.loneElement._3, "==> x>y*y -> x>y*y".asSequent)
    LemmaDBFactory.lemmaDB.add(Lemma(provedLemma, Lemma.requiredEvidence(provedLemma, ToolEvidence(List(
      "tool" -> "KeYmaera X",
      "model" -> lemma.fileContent,
      "tactic" -> lemma.tactics.loneElement._2
    )) :: Nil), Some("user/tests/Lemma 1")))

    val theoremId = db.createProof(theorem.fileContent)
    checkTree(db.db, theoremId, theorem.tactics.loneElement._3, "==> x>y*y -> x>y*y & x>=y*y".asSequent)
  }}

  it should "work with lemmas that partially expand" in withDatabase { db => withMathematica { _ =>
    val modelContent =
      """SharedDefinitions
        |  Real sq(Real x) = x*x;
        |  Bool gt(Real x, Real y) <-> x>y;
        |End.
        |
        |Lemma "user/tests/Lemma 1"
        |
        |ProgramVariables
        |  Real x, y;
        |End.
        |
        |Problem
        |  gt(x,sq(y)) -> gt(x,sq(y))
        |End.
        |
        |Tactic "Lemma Proof"
        |  implyR(1); expand("sq"); id
        |End.
        |
        |End.
        |
        |ArchiveEntry "user/tests/Delayed Substitution"
        |
        |ProgramVariables
        |  Real x, y;
        |End.
        |
        |Problem
        |  gt(x,sq(y)) -> gt(x,sq(y)) & x>=sq(y)
        |End.
        |
        |Tactic "Delayed Substitution Test with Lemmas: Proof"
        |implyR(1) ; andR(1) ; <(
        |  useLemma("tests/Lemma 1", "prop"),
        |  expand("gt"); abbrv("sq(y)"); hideL('Llast); QE
        |  )
        |End.
        |
        |End.
        |""".stripMargin

    val lemma :: theorem :: Nil = ArchiveParser(modelContent)

    val lemmaId = db.createProof(lemma.fileContent)
    val provedLemma = checkTree(db.db, lemmaId, lemma.tactics.loneElement._3, "==> gt(x,y*y) -> gt(x,y*y)".asSequent)
    LemmaDBFactory.lemmaDB.add(Lemma(provedLemma, Lemma.requiredEvidence(provedLemma, ToolEvidence(List(
      "tool" -> "KeYmaera X",
      "model" -> lemma.fileContent,
      "tactic" -> lemma.tactics.loneElement._2
    )) :: Nil), Some("user/tests/Lemma 1")))

    val theoremId = db.createProof(theorem.fileContent)
    checkTree(db.db, theoremId, theorem.tactics.loneElement._3, "==> x>y*y -> x>y*y & x>=y*y".asSequent)
  }}

  it should "work when expanding to different extent" in withDatabase { db => withMathematica { _ =>
    val modelContent =
      """SharedDefinitions
        |  Real sq(Real x) = x*x;
        |  Bool gt(Real x, Real y) <-> x>y;
        |  Bool gtsq(Real x, Real y) <-> gt(x,sq(y));
        |End.
        |
        |ArchiveEntry "user/tests/Delayed Substitution"
        |
        |ProgramVariables
        |  Real x, y;
        |End.
        |
        |Problem
        |  gt(x,sq(y)) -> gt(x,sq(y)) & x>sq(y)
        |End.
        |
        |Tactic "Delayed Substitution Test with Lemmas: Proof"
        |implyR(1) ; andR(1) ; <(
        |  expand("gtsq"); id,
        |  expand("gtsq"); expand("gt"); id
        |  )
        |End.
        |
        |End.
        |""".stripMargin

    val theorem :: Nil = ArchiveParser(modelContent)

    val theoremId = db.createProof(theorem.fileContent)
    checkTree(db.db, theoremId, theorem.tactics.loneElement._3, "==> x>sq(y) -> x>sq(y) & x>sq(y)".asSequent)
  }}

  it should "FEATURE_REQUEST: work with delayed let substitution" taggedAs TodoTest in withDatabase { db => withMathematica { _ =>
    val proofId = db.createProof(
      """ArchiveEntry "Simple"
        |Problem y+z>=0 -> [x:=y+z;]x>=0 End.
        |End.""".stripMargin)
    // do some steps
    checkTree(db.db, proofId, implyR(1),
      "==> y+z>=0 -> [x:=y+z;]x>=0".asSequent, "y+z>=0 ==> [x:=y+z;]x>=0".asSequent :: Nil)
    checkTree(db.db, proofId, Let("y()".asTerm, "y".asTerm, Let("z()".asTerm, "z".asTerm, assignb(1))),
      "==> y+z>=0 -> [x:=y+z;]x>=0".asSequent, "y()+z()>=0 ==> y()+z()>=0".asSequent :: Nil)
    // now finish the proof
    checkTree(db.db, proofId, id, "==> y+z>=0 -> [x:=y+z;]x>=0".asSequent, Nil)
  }}

  it should "FEATURE_REQUEST: work when delayed let substitution is not the first step in a tactic" taggedAs TodoTest in withDatabase { db => withMathematica { _ =>
    val proofId = db.createProof(
      """ArchiveEntry "Simple"
        |Problem y>=0 -> [x:=y;]x>=0 End.
        |End.""".stripMargin)
    // stop in the middle
    checkTree(db.db, proofId, implyR(1) & Let("y()".asTerm, "y".asTerm, assignb(1)),
      "==> y>=0 -> [x:=y;]x>=0".asSequent, "y()>=0 ==> y()>=0".asSequent :: Nil)
    // now finish the proof
    checkTree(db.db, proofId, id, "==> y>=0 -> [x:=y;]x>=0".asSequent, Nil)
  }}

  "Performance" should "not degrade when doing the usual interaction (without tactic extraction) in a loop" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    val numStepsPerProof = 1000
    val durations = Array.fill(numStepsPerProof)(0.0)

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

      if (i%2==1) { tactics should have size 1; tactics(0)._1.codeName shouldBe "chaseAt" }
      else { tactics should have size 2; tactics(0)._1.codeName shouldBe "implyR"; tactics(1)._1.codeName shouldBe "chaseAt" }

      val tacticSuggestionFetch = System.currentTimeMillis()

      if (i%2==1) goals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyRi, "implyRi", wait=true)
      else goals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)
      val tacticExecuted = System.currentTimeMillis()

      val end = System.currentTimeMillis()

      println(s"Run $i, duration ${end-start}: construction=${treeConstructed-start}, goals=${openGoalsFetched-treeConstructed}, suggestion=${tacticSuggestionFetch-openGoalsFetched}, execution=${tacticExecuted-tacticSuggestionFetch}")

      durations(i) = end-start
    }

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tacticString(new VerbatimTraceToTacticConverter(tree.info.defs(db.db)))

    val medianDuration = median(durations.toList)
    val averageDuration = durations.sum/numStepsPerProof
    println("Median duration " + medianDuration)
    println("Average duration " + averageDuration)
    println("Minimum duration " + durations.min + " (iteration " + durations.indexOf(durations.min) + ")")
    println("Maximum duration " + durations.max + " (iteration " + durations.indexOf(durations.max) + ")")
  }}

  it should "not degrade too much when doing the usual interaction with tactic extraction in a loop" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""
    val proofId = db.createProof(modelContent)

    val numStepsPerProof = 200
    val durations = Array.fill(numStepsPerProof)(0.0)

    for (i <- 0 until numStepsPerProof) {
      val start = System.currentTimeMillis()
      val tree = DbProofTree(db.db, proofId.toString)

      tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db.db)))

      val goals = tree.openGoals
      goals should have size 1
      if (i%2==1) goals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
      else goals.head.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0->x>0".asFormula)))

      val tactics = goals.head.applicableTacticsAt(SuccPosition(1))
      goals.head.tacticInputSuggestions(SuccPosition(1)) shouldBe empty

      if (i%2==1) { tactics should have size 1; tactics(0)._1.codeName shouldBe "chaseAt" }
      else { tactics should have size 2; tactics(0)._1.codeName shouldBe "implyR"; tactics(1)._1.codeName shouldBe "chaseAt" }

      if (i%2==1) goals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyRi, "implyRi", wait=true)
      else goals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)

      val end = System.currentTimeMillis()
      durations(i) = end-start
    }

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db.db)))

    val medianDuration = median(durations.toList)
    val averageDuration = durations.sum/numStepsPerProof
    println("Median duration " + medianDuration)
    println("Average duration " + averageDuration)
    println("Minimum duration " + durations.min)
    println("Maximum duration " + durations.max)
  }}

  it should "not degrade over multiple proofs" in withTactics { withDatabase { db =>
    val modelContent = """ArchiveEntry "Test" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."""

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

        if (i%2==0) { tactics should have size 1; tactics(0)._1.codeName shouldBe "chaseAt" }
        else { tactics should have size 2; tactics(0)._1.codeName shouldBe "implyR"; tactics(1)._1.codeName shouldBe "chaseAt" }

        if (i%2==0) goals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyRi, "implyRi", wait=true)
        else goals.head.runTactic("guest", ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR", wait=true)

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
  }}

  private def median(s: List[Double]): Double = {
    val (lower, upper) = s.sortWith(_<_).splitAt(s.size/2)
    if (s.size%2 == 0) (lower.last + upper.head)/2.0 else upper.head
  }
}
