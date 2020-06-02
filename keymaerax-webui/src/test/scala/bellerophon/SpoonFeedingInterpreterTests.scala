package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, Idioms, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import testHelper.KeYmaeraXTestTags.{SlowTest, TodoTest}

import scala.collection.immutable._
import scala.language.postfixOps
import org.scalatest.LoneElement._

/**
  * Tests the spoon-feeding interpreter.
  * Created by smitsch on 8/24/16.
  */
class SpoonFeedingInterpreterTests extends TacticTestBase {

  "Atomic tactic" should "be simply forwarded to the inner interpreter" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    val tactic = implyR(1)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some("x>0 ==> x>0".asSequent)
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Nil
    tree.root.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.goal shouldBe Some("==> x>0 -> x>0".asSequent)
    tree.root.provable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.provable.subgoals.loneElement shouldBe "x>0 ==> x>0".asSequent
    tree.root.localProvable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.localProvable.subgoals.loneElement shouldBe "==> x>0 -> x>0".asSequent
    tree.root.makerShortName shouldBe None
    tree.root.children.loneElement.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.children.loneElement.goal shouldBe Some("x>0 ==> x>0".asSequent)
    tree.root.children.loneElement.localProvable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.children.loneElement.localProvable.subgoals.loneElement shouldBe "x>0 ==> x>0".asSequent
    tree.root.children.loneElement.makerShortName shouldBe Some("implyR(1)")

    tree.tactic shouldBe tactic
  }

  it should "record pending if not applicable" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    val tactic = andR(1)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.goal shouldBe Some("==> x>0 -> x>0".asSequent)
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("""pending("andR(1)")""")::Nil
    tree.root.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.goal shouldBe Some("==> x>0 -> x>0".asSequent)
    tree.root.provable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.provable.subgoals.loneElement shouldBe "==> x>0 -> x>0".asSequent
    tree.root.localProvable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.localProvable.subgoals.loneElement shouldBe "==> x>0 -> x>0".asSequent
    tree.root.makerShortName shouldBe None
    tree.root.children.loneElement.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.children.loneElement.goal shouldBe Some("==> x>0 -> x>0".asSequent)
    tree.root.children.loneElement.localProvable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.children.loneElement.localProvable.subgoals.loneElement shouldBe "==> x>0 -> x>0".asSequent
    tree.root.children.loneElement.makerShortName shouldBe Some("""pending("andR(1)")""")
  }

  "Sequential tactic" should "be split into atomics before being fed to inner" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = implyR(1) & closeId
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 3
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("id")::Nil
    tree.root.provable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.provable shouldBe 'proved
    tree.root.localProvable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.localProvable.subgoals.loneElement shouldBe "==> x>0 -> x>0".asSequent
    tree.root.makerShortName shouldBe None
    tree.root.children.loneElement.localProvable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.children.loneElement.localProvable.subgoals.loneElement shouldBe "x>0 ==> x>0".asSequent
    tree.root.children.loneElement.makerShortName shouldBe Some("implyR(1)")
    tree.root.children.loneElement.children.loneElement.localProvable.conclusion shouldBe "x>0 ==> x>0".asSequent
    tree.root.children.loneElement.children.loneElement.localProvable.subgoals shouldBe empty
    tree.root.children.loneElement.children.loneElement.makerShortName shouldBe Some("id")
    tree.root.children.loneElement.children.loneElement.children shouldBe empty

    tree.tactic shouldBe tactic
  }

  it should "be recorded as pending on failure" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 & x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = implyR(1) & TactixLibrary.loop("x>0".asFormula)(1)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))
    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("""pending("implyR(1) ; loop(\"x>0\", 1)")""")
  }

  it should "record only RHS as pending on failure" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = implyR(1) & TactixLibrary.loop("x>0".asFormula)(1)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))
    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("""implyR(1) ; pending("loop(\"x>0\", 1)")""")
  }

  "Either tactic" should "be explored and only successful outcome stored in database" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & (andR(1) | closeId), BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 3
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("id")::Nil
    tree.root.provable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.provable shouldBe 'proved
    tree.root.localProvable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.localProvable.subgoals.loneElement shouldBe "==> x>0 -> x>0".asSequent
    tree.root.makerShortName shouldBe None
    tree.root.children.loneElement.localProvable.conclusion shouldBe "==> x>0 -> x>0".asSequent
    tree.root.children.loneElement.localProvable.subgoals.loneElement shouldBe "x>0 ==> x>0".asSequent
    tree.root.children.loneElement.makerShortName shouldBe Some("implyR(1)")
    tree.root.children.loneElement.children.loneElement.localProvable.conclusion shouldBe "x>0 ==> x>0".asSequent
    tree.root.children.loneElement.children.loneElement.localProvable.subgoals shouldBe empty
    tree.root.children.loneElement.children.loneElement.makerShortName shouldBe Some("id")
    tree.root.children.loneElement.children.loneElement.children shouldBe empty

    tree.tactic shouldBe implyR(1) & closeId
  }

  it should "be explored and stored pending if failing" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & (andR(1) | orR(1)), BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 3
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("""pending("andR(1) | orR(1)")""")::Nil
  }

  it should "discard previously recorded tactic steps when recording alternatives" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>=0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & (prop & done | done), BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 3
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("""pending("prop ; done | done")""")::Nil
  }

  "Branch tactic" should "work simple top-level" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0&x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId, closeId),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(id, id)")
  }

  it should "work nested branching top-level" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0&x>0&x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId, andR(1) & Idioms.<(closeId, closeId)),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(id, andR(1) ; <(id, id))")
    db.db.getExecutionTrace(proofId).steps.map(_.rule) should contain theSameElementsInOrderAs
      "implyR(1)" :: "andR(1)" :: "andR(1)" :: "id" :: "id" :: "id" :: Nil
  }

  it should "support nested branching with unconventional closing" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0&x>0&x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & andR(1) & Idioms.<(nil, andR(1) & Idioms.<(closeId, nil) & closeId) & closeId,
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    // tactic extraction rewrites into nicer shape
    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(id, andR(1) ; <(id, id))")
    db.db.getExecutionTrace(proofId).steps.map(_.rule) should contain theSameElementsInOrderAs
      "implyR(1)" :: "andR(1)" :: "andR(1)" :: "nil" :: "id" :: "id" :: "nil" :: "id" :: Nil
  }

  it should "work top-level" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId & done, skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 6
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("andR(1)")::
      Some("andR(1)")::Some("nil")::Some("id")::Nil
    tree.root.provable.conclusion shouldBe "==> x>0 -> x>0&x>=0".asSequent
    tree.root.provable.subgoals.loneElement shouldBe "x>0 ==> x>=0".asSequent
    tree.root.makerShortName shouldBe None
    tree.root.conclusion shouldBe "==> x>0 -> x>0&x>=0".asSequent
    tree.root.goal shouldBe Some("==> x>0 -> x>0&x>=0".asSequent)
    tree.root.children should have size 1

    val n10 = tree.root.children.head
    n10.makerShortName shouldBe Some("implyR(1)")
    n10.conclusion shouldBe "==> x>0 -> x>0&x>=0".asSequent
    n10.goal shouldBe Some("x>0 ==> x>0&x>=0".asSequent)
    n10.children should have size 2

    val n20 = n10.children.head
    n20.makerShortName shouldBe Some("andR(1)")
    n20.conclusion shouldBe "x>0 ==> x>0&x>=0".asSequent
    n20.goal shouldBe Some("x>0 ==> x>0".asSequent)
    n20.children should have size 1

    val n4 = n20.children.head
    n4.makerShortName shouldBe Some("id")
    n4.conclusion shouldBe "x>0 ==> x>0".asSequent
    n4.goal shouldBe empty

    val n21 = n10.children(1)
    n21.makerShortName shouldBe Some("andR(1)")
    n21.conclusion shouldBe "x>0 ==> x>0&x>=0".asSequent
    n21.goal shouldBe Some("x>0 ==> x>=0".asSequent)
    n21.children should have size 1

    val n31 = n21.children.head
    n31.makerShortName shouldBe Some("nil")
    n31.conclusion shouldBe "x>0 ==> x>=0".asSequent
    n31.goal shouldBe Some("x>0 ==> x>=0".asSequent)
    n31.children shouldBe empty

    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(id, nil)")
  }

  it should "work top-level and support complicated branch tactics" taggedAs(SlowTest) in withMathematica { _ => withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>0&[{x'=1&x>=0}]x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId & done, dW(1) & prop & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 7
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
      None::Some("implyR(1)")::Some("andR(1)")::Some("andR(1)")::Some("dW(1)")::Some("prop")::Some("id")::Nil
    tree.root.provable.conclusion shouldBe "==> x>0 -> x>0&[{x'=1&x>=0}]x>=0".asSequent
    //tree.root.provable shouldBe 'proved
    tree.root.conclusion shouldBe "==> x>0 -> x>0&[{x'=1&x>=0}]x>=0".asSequent
    tree.root.goal shouldBe Some(" ==> x>0 -> x>0&[{x'=1&x>=0}]x>=0".asSequent)
    tree.root.children should have size 1

    val n10 = tree.root.children.head
    n10.makerShortName shouldBe Some("implyR(1)")
    n10.conclusion shouldBe " ==> x>0 -> x>0&[{x'=1&x>=0}]x>=0".asSequent
    n10.goal shouldBe Some("x>0 ==> x>0&[{x'=1&x>=0}]x>=0".asSequent)
    n10.children should have size 2

    val n20 = n10.children.head
    n20.makerShortName shouldBe Some("andR(1)")
    n20.conclusion shouldBe "x>0 ==> x>0&[{x'=1&x>=0}]x>=0".asSequent
    n20.goal shouldBe Some("x>0 ==> x>0".asSequent)
    n20.children should have size 1

    val n50 = n20.children.head
    n50.makerShortName shouldBe Some("id")
    n50.conclusion shouldBe "x>0 ==> x>0".asSequent
    n50.goal shouldBe None
    n50.children shouldBe empty

    val n21 = n10.children(1)
    n21.makerShortName shouldBe Some("andR(1)")
    n21.conclusion shouldBe "x>0 ==> x>0&[{x'=1&x>=0}]x>=0".asSequent
    n21.goal shouldBe Some("x>0 ==> [{x'=1&x>=0}]x>=0".asSequent)
    n21.children should have size 1

    val n30 = n21.children.head
    n30.makerShortName shouldBe Some("dW(1)")
    n30.conclusion shouldBe "x>0 ==> [{x'=1&x>=0}]x>=0".asSequent
    n30.goal shouldBe Some("==> x>=0->x>=0".asSequent)
    n30.children should have size 1

    val n40 = n30.children.head
    n40.makerShortName shouldBe Some("prop")
    n40.conclusion shouldBe "==> x>=0->x>=0".asSequent
    n40.goal shouldBe None
    n40.children shouldBe empty

    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(id, dW(1) ; prop)")
  }}

  it should "work with nested branching when every branch is closed" in withMathematica { _ => withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0|x>1 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(closeId & done, QE & done), QE & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.load()
    tree.nodes should have size 9
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("andR(1)")::
      Some("andR(1)")::Some("QE")::Some("orL(-1)")::Some("orL(-1)")::Some("QE")::Some("id")::Nil
    tree.root.provable.conclusion shouldBe "==> x>0|x>1 -> x>0&x>=0".asSequent
    tree.root.provable shouldBe 'proved
    // nodes after orL
    tree.locate("(4,0)").flatMap(_.goal) shouldBe Some("x>0 ==> x>0".asSequent)
    tree.locate("(4,1)").flatMap(_.goal) shouldBe Some("x>1 ==> x>0".asSequent)
    tree.openGoals shouldBe empty
    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(orL(-1) ; <(id, QE), QE)")
  }}

  it should "work when early branches remain open and later ones close" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>1|x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & orL(-1) & Idioms.<(skip, closeId & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.root.provable.subgoals should have size 1
    tree.root.provable.subgoals.head shouldBe "x>1 ==> x>0".asSequent
    tree.nodes should have size 6
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
      None::Some("implyR(1)")::Some("orL(-1)")::Some("orL(-1)")::Some("id")::Some("nil")::Nil
    tree.locate("(2,0)").flatMap(_.goal) shouldBe Some("x>1 ==> x>0".asSequent)
    tree.locate("(2,1)").flatMap(_.goal) shouldBe Some("x>0 ==> x>0".asSequent)
    tree.openGoals should have size 1
    tree.tactic shouldBe BelleParser("implyR(1) & orL(-1) & <(nil, id)")
  }

  it should "work with nested branching when branches stay open 1" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>1|x>0 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(skip, closeId), skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 2
    tree.tactic shouldBe BelleParser("implyR(1) & andR(1) & <(orL(-1) & <(nil, id), nil)")
  }

  it should "work with nested branching when branches stay open 2" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End.\n\n Problem. x>0|x>1 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(closeId, skip), skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 2
    tree.tactic shouldBe BelleParser("implyR(1) & andR(1) & <(orL(-1) & <(id, nil), nil)")
  }

  it should "work with nested branching when branching stay open 3" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & orL(-1) & Idioms.<(andR(1) & Idioms.<(closeId, skip), andR(1)),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 3
    tree.tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(andR(1) ; <(id, nil), andR(1) ; <(nil, nil))")
  }

  it should "work with nested branching when branching stay open 4" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & orL(-1) & Idioms.<(andR(1) & Idioms.<(closeId, skip), andR(1) & Idioms.<(skip, closeId)),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 2
    tree.tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(andR(1) ; <(id, nil), andR(1) ; <(nil, id))")
  }

  it should "work with nested branching and repeat" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&(x>=0&x<y)"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & orL(-1) <((andR(1) <(closeId, skip))*2, andR(1) <(skip, andR(1) <(skip, closeId))),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 3
    tree.tactic shouldBe BelleParser("implyR(1); orL(-1); <(andR(1); <(id, andR(1); <(id, nil)), andR(1); <(nil, andR(1); <(nil, id)))")
  }

  it should "work with loop tactic" in withDatabase { db =>
    withMathematica { qeTool =>
    val problem = "x>=0 -> [{x:=x+1;}*]x>=0"
    val modelContent = s"ProgramVariables. R x. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1, convertPending=false))
    interpreter(implyR(1) & loop("x>=0".asFormula)(1),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 3
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; cutR("[{x:=x+1;}*](x>=0&!false)", 1) ; <(
        |I(1) ; andR(1) ; <(
        |andR(1) ; <(
        |  label("Init"),
        |    notR(1) ; close
        |  ),
        |  cohide(1) ; Goedel ; implyR(1) ; boxAnd(1) ; andR(1) ; <(
        |  andL('Llast) ; hideL('Llast) ; label("Step"),
        |    andL(-1) ; hideL(-1=="x>=0") ; V(1) ; id
        |  )
        |),
        |cohide(1) ; CMonCongruence(".1") ; implyR(1) ; andL('Llast) ; hideL('Llast) ; label("Post")
        |)""".stripMargin)
    }
  }

  it should "work with loop tactic that preserves constants" in withDatabase { db =>
    withMathematica { _ =>
    val problem = "x>=0 & A>0&B>0&C>0 -> [{x:=x+B;}*]x>=0"
    val modelContent = s"Definitions Real A,B,C; End. ProgramVariables Real x; End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1, convertPending=false))
    interpreter(implyR(1) & loop("x>=0".asFormula)(1),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 3
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; andL('L) ; andL('L) ; cutR("[{x:=x+B;}*](x>=0&A>0&B>0&C>0&!false)", 1) ; <(
        |I(1) ; andR(1) ; <(
        |andR(1) ; <(
        |  label("Init"),
        |    andR(1) ; <(
        |    idWith(1),
        |      andR(1) ; <(
        |      idWith(1),
        |        andR(1) ; <(
        |        idWith(1),
        |          notR(1) ; close
        |        )
        |      )
        |    )
        |  ),
        |  cohide(1) ; Goedel ; implyR(1) ; boxAnd(1) ; andR(1) ; <(
        |  andL('Llast) ; andL('Llast) ; andL('Llast) ; andL('Llast) ; hideL('Llast) ; label("Step"),
        |    andL(-1) ; hideL(-1=="x>=0") ; V(1) ; id
        |  )
        |),
        |cohide(1) ; CMonCongruence(".1") ; implyR(1) ; andL('Llast) ; andL('Llast) ; andL('Llast) ; andL('Llast) ; hideL('Llast) ; label("Post")
        |)""".stripMargin)
    }
  }

  it should "close left-over branching with follow-up branches" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x>=0&x>=0|x<y"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & orL(-1) & onAll(orR(1)) & Idioms.<(andR(1) & Idioms.<(closeId, andR(1)), closeId) & onAll(closeId),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals shouldBe empty
    tree.tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(orR(1) ; andR(1) ; <(id, andR(1) ; <(id, id) ), orR(1) ; id)")
    proveBy(problem.asFormula, tree.tactic) shouldBe 'proved
  }

  it should "close left-over branching with follow-up branches (2)" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x>=0&x>=0|x<y"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & orL(-1) & onAll(orR(1)) & Idioms.<(andR(1) & Idioms.<(closeId, andR(1)), skip) & onAll(closeId),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals shouldBe empty
    tree.tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(orR(1) ; andR(1) ; <(id, andR(1); <(id, id) ), orR(1) ; id)")
    proveBy(problem.asFormula, tree.tactic) shouldBe 'proved
  }

  it should "close left-over branching with follow-up branches (3)" taggedAs TodoTest ignore withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x>=0&x>=0|x<y"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & orL(-1) & onAll(orR(1)) & Idioms.<(andR(1) & Idioms.<(closeId, andR(1)), skip) &
      Idioms.<(skip, cut("x^2>=0".asFormula), skip) & DebuggingTactics.print("Foo") & Idioms.<(skip, skip, closeId, cohideR('Rlast)) &
      DebuggingTactics.print("WTF") & Idioms.<(skip, closeId, QE) & closeId,
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals shouldBe empty
    //tree.tactic shouldBe BelleParser("")
    proveBy(problem.asFormula, tree.tactic) shouldBe 'proved
  }

  "Saturation" should "record each iteration as step" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0&x>1&x>2 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & SaturateTactic(andL('L)), BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 4
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
      None::Some("implyR(1)")::Some("andL('L)")::Some("andL('L)")::Nil
    tree.root.conclusion shouldBe "==> x>0&x>1&x>2 -> x>0".asSequent
    tree.root.provable.subgoals should contain theSameElementsInOrderAs "x>0, x>1, x>2 ==> x>0".asSequent :: Nil
    tree.root.children should have size 1
    val n10 = tree.root.children.head
    n10.makerShortName shouldBe Some("implyR(1)")
    n10.goal shouldBe Some("x>0&x>1&x>2 ==> x>0".asSequent)
    n10.children should have size 1

    val n20 = n10.children.head
    n20.makerShortName shouldBe Some("andL('L)")
    n20.goal shouldBe Some("x>0, x>1&x>2 ==> x>0".asSequent)
    n20.children should have size 1

    val n30 = n20.children.head
    n30.makerShortName shouldBe Some("andL('L)")
    n30.goal shouldBe Some("x>0, x>1, x>2 ==> x>0".asSequent)
    n30.children shouldBe empty
  }

  it should "not recurse on nil" in withMathematica { _ => withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>1 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(SaturateTactic(nil), BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 3

    // final nil: SpoonFeedingInterpreter inserts a nil when saturation is done
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("nil")::Some("nil")::Nil
    tree.root.conclusion shouldBe "==> x>0 -> x>1".asSequent
    tree.root.provable.subgoals should contain theSameElementsInOrderAs "==> x>0 -> x>1".asSequent::Nil
    tree.root.children should have size 1

    val n1 = tree.root.children.head
    n1.makerShortName shouldBe Some("nil")
    n1.goal shouldBe Some("==> x>0 -> x>1".asSequent)
    n1.children.loneElement.makerShortName shouldBe Some("nil")
  }}

  it should "recurse only on change" in withMathematica { _ => withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>1 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(SaturateTactic(Idioms.?(QE)), BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 4

    // final nil: SpoonFeedingInterpreter inserts a nil when saturation is done
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("QE")::Some("QE")::Some("nil")::Nil
    tree.root.conclusion shouldBe "==> x>0 -> x>1".asSequent
    tree.root.provable.subgoals should contain theSameElementsInOrderAs "==> false".asSequent::Nil
    tree.root.children should have size 1

    val n1 = tree.root.children.head
    n1.makerShortName shouldBe Some("QE")
    n1.goal shouldBe Some("==> false".asSequent)
    n1.children should have size 1

    val n2 = n1.children.head
    n2.makerShortName shouldBe Some("QE")
    n2.goal shouldBe Some("==> false".asSequent)
    n2.children.loneElement.makerShortName shouldBe Some("nil")
  }}

  "Repeat" should "record each iteration as step" in withDatabase {db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0&x>1&x>2&x>3 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & (andL('L)*2), BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 4
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
      None::Some("implyR(1)")::Some("andL('L)")::Some("andL('L)")::Nil
    tree.root.conclusion shouldBe "==> x>0&x>1&x>2&x>3 -> x>0".asSequent
    tree.root.provable.subgoals should contain theSameElementsInOrderAs "x>0, x>1, x>2&x>3 ==> x>0".asSequent::Nil
    tree.root.children should have size 1
    val n10 = tree.root.children.head
    n10.makerShortName shouldBe Some("implyR(1)")
    n10.goal shouldBe Some("x>0&x>1&x>2&x>3 ==> x>0".asSequent)
    n10.children should have size 1

    val n20 = n10.children.head
    n20.makerShortName shouldBe Some("andL('L)")
    n20.goal shouldBe Some("x>0, x>1&x>2&x>3 ==> x>0".asSequent)
    n20.children should have size 1

    val n30 = n20.children.head
    n30.makerShortName shouldBe Some("andL('L)")
    n30.goal shouldBe Some("x>0, x>1, x>2&x>3 ==> x>0".asSequent)
    n30.children shouldBe empty
  }

  "Let" should "be recorded plain" in withDatabase { db =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>0&x>1&x>2&x>3 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof,
      listener(db.db), ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(let("X()".asTerm, "x".asVariable, prop),
      BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))
    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("let(X()=x in prop)") :: Nil
  }

  "Listeners" should "not be informed when doing auxiliary inner proofs" in withMathematica { _ =>
    val mockListener = new IOListener() {
      var beginnings: List[(BelleValue, BelleExpr)] = Nil
      override def begin(input: BelleValue, expr: BelleExpr): Unit = beginnings = beginnings :+ (input -> expr)
      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
      override def kill(): Unit = {}
    }
    val mockListenerFactory: Int => (String, Int, Int) => scala.collection.immutable.Seq[IOListener] =
      (_: Int) => (_: String, _: Int, _: Int) => mockListener::Nil

    val interpreter = SpoonFeedingInterpreter(1, -1, (_: ProvableSig) => 1, mockListenerFactory,
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false))
    BelleInterpreter.setInterpreter(interpreter)
    BelleInterpreter(implyR(1) & dC("x>0".asFormula)(1, 1::Nil), BelleProvable(ProvableSig.startProof("y>0 -> [x:=3;][{x'=4}]x>0".asFormula)))
    //@note auxiliary inner proofs started by UnifyUSCalculus ruin database trace if reported to listeners
    mockListener.beginnings shouldNot contain (BelleProvable(ProvableSig.startProof("[{x'=4}]x>0".asFormula)) -> (QE & done))
    mockListener.beginnings shouldNot contain (BelleProvable(ProvableSig.startProof("(p_()<->q_())&q_()->p_()<->true".asFormula)) -> prop)
    //@note should also not contain the following, but not testable without huge effort since closeTrue is private and so is ProofRuleTactics
    //mockListener.beginnings shouldNot contain (BelleProvable(ProvableSig.startProof("[a{|^@|};]true <-> true".asFormula)) -> (equivR(1) <(closeTrue(SuccPos(1)), cohideR(1) & byUS("[]T system"))))
  }

  "Parsed tactic" should "record STTT tutorial example 1 steps" taggedAs SlowTest in withDatabase { db => withMathematica { _ =>
    val modelContent = KeYmaeraXArchiveParser.getEntry("STTT Tutorial Example 1", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString).get.fileContent
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tacticText = """implyR('R) & andL('L) & dC("v>=0", 1) & <(dW(1) & prop, dI(1))"""
    val tactic = BelleParser(tacticText)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val extractedTactic = db.extractTactic(proofId)
    extractedTactic shouldBe BelleParser(tacticText)
  }}

  it should "record STTT tutorial example 2 steps" taggedAs SlowTest  in withMathematica { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("STTT Tutorial Example 2", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString).get
    val modelContent = entry.fileContent
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = entry.tactics.head._3
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val extractedTactic = db.extractTactic(proofId)
    extractedTactic shouldBe BelleParser(
      """
        |implyR(1) & andL('L) & andL('L) & loop("v>=0",1) & <(
        |  QE,
        |  QE,
        |  composeb(1) & choiceb(1) & andR(1) & <(
        |    assignb(1) & ODE(1),
        |    choiceb(1) & andR(1) & <(
        |      assignb(1) & ODE(1),
        |      assignb(1) & ODE(1)
        |    )
        |  )
        |)
      """.stripMargin)
  }}

  it should "record STTT tutorial example 3a steps" taggedAs SlowTest in withMathematica { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("STTT Tutorial Example 3a", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString).get
    val modelContent = entry.fileContent
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = entry.tactics.head._3
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; andL('L) ; andL('L) ; loop("v >= 0 & x+v^2/(2*B()) <= S()", 1) ; <(
        |  QE,
        |  QE,
        |  composeb(1) ; choiceb(1) ; andR(1) ; <(
        |    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; choiceb(1) ; andR(1) ; <(ODE(1), ODE(1)),
        |    choiceb(1) ; andR(1) ; <(
        |      composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; choiceb(1) ; andR(1) ; <(ODE(1), ODE(1)),
        |      assignb(1) ; choiceb(1) ; andR(1) ; <(ODE(1), ODE(1))
        |    )
        |  )
        |)
      """.stripMargin)
  }}

  it should "record STTT tutorial example 4a steps" taggedAs SlowTest in withMathematica { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("STTT Tutorial Example 4a", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString).get
    val modelContent = entry.fileContent
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = entry.tactics.head._3
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; loop("v<=V()", 1) ; <(
        |  QE,
        |  QE,
        |  composeb(1) ; choiceb(1) ; andR(1) ; <(
        |    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; ODE(1),
        |    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; ODE(1)
        |  )
        |)
      """.stripMargin)
  }}

  it should "record STTT tutorial example 4b steps" taggedAs SlowTest in withMathematica { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("STTT Tutorial Example 4b", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString).get
    val modelContent = entry.fileContent
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = entry.tactics.head._3
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 11
    tree.nodes.map(_.makerShortName) should contain theSameElementsAs None::Some("implyR(1)")::Some("andL('L)")::
      Some("""loop("v<=V()",1)""")::Some("""loop("v<=V()",1)""")::Some("""loop("v<=V()",1)""")::
      Some("composeb(1)")::Some("assignb(1)")::Some("ODE(1)")::Some("QE")::Some("QE")::Nil
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; loop("v<=V()", 1) ; <(
        |  QE,
        |  QE,
        |  composeb(1) ; assignb(1) ; ODE(1)
        |)
      """.stripMargin)
  }}

  it should "record STTT tutorial example 9b steps" taggedAs SlowTest in withMathematica { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("STTT Tutorial Example 9b", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString).get
    val modelContent = entry.fileContent
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = entry.tactics.head._3
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tacticString
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ;
        |loop("v >= 0 & xm <= x & xr = (xm + S())/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S() - xm)/2)^2", 1) ; <(
        |  QE,
        |  QE,
        |  andL('L) ; andL('L) ; andL('L) ; composeb(1) ; choiceb(1) ; andR(1) ; <(
        |    composeb(1) ; assignb(1) ; composeb(1) ; assignb(1) ; testb(1) ; implyR(1) ;
        |      dC("xm <= x", 1) ; <(
        |        dC("5/4*(x-(xm+S())/2)^2 + (x-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2", 1) ; <(
        |          dW(1) ; QE,
        |          dI(1)
        |        ),
        |        dI(1)
        |      ),
        |    testb(1) ; implyR(1) ;
        |      dC("xm <= x", 1) ; <(
        |        dC("5/4*(x-(xm+S())/2)^2 + (x-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2", 1) ; <(
        |          dW(1) ; QE,
        |          dI(1)
        |        ),
        |        dI(1)
        |      )
        |  )
        |)
        |
      """.stripMargin)
  }}

  it should "record STTT tutorial example 10 steps" taggedAs SlowTest in withMathematica { _ => withDatabase { db =>
    val entry = KeYmaeraXArchiveParser.getEntry("STTT Tutorial Example 10", io.Source.fromInputStream(
      getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString).get
    val modelContent = entry.fileContent
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))

    val tactic = entry.tactics.head._3
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelContent))))

    //db.extractTactic(proofId) shouldBe tactic //@note not exactly the same, because repetitions are unrolled etc.
    val tree = DbProofTree(db.db, proofId.toString)
    tree.tacticString
    tree.tactic shouldBe BelleParser(
      """
        |implyR(1) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ;
        |loop("v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly()) + v^2/(2*b()) < lw()", 1) ; <(
        |  QE,
        |  QE,
        |  chase('R) ; normalize ; <(
        |    hideL(-15=="abs(y-ly())+v^2/(2*b()) < lw()") ; dC("c>=0", 1) ; <(
        |      dC("dx^2+dy^2=1", 1) ; <(
        |        dC("v=old(v)+a*c", 1) ; <(
        |          dC("-c*(v-a/2*c) <= y - old(y) & y - old(y) <= c*(v-a/2*c)", 1) ; <(
        |            dW(1) ; implyR('R) ;
        |            andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ;
        |            andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ;
        |            transformEquality("ep()=c",-13=="abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()") ;
        |            prop ; smartQE
        |            ,
        |            dI(1)
        |          ),
        |          dI(1)
        |        ),
        |        dI(1)
        |        ),
        |      dI(1)
        |      ),
        |    dC("c>=0", 1) ; <(
        |      dC("dx^2+dy^2=1", 1) ; <(
        |        dC("v=old(v)", 1) ; <(
        |          dC("-c*v <= y - old(y) & y - old(y) <= c*v", 1) ; <(
        |            dW(1) ; prop ; smartQE,
        |            dI(1)
        |            ),
        |          dI(1)
        |          ),
        |        dI(1)
        |        ),
        |      dI(1)
        |      ),
        |    dC("c>=0", 1) ; <(
        |      dC("dx^2+dy^2=1", 1) & <(
        |        dC("v=old(v)+a*c", 1) & <(
        |          dC("-c*(v-a/2*c) <= y - old(y) & y - old(y) <= c*(v-a/2*c)", 1) & <(
        |            dW(1) ; prop ; smartQE,
        |            dI(1)
        |            ),
        |          dI(1)
        |          ),
        |        dI(1)
        |        ),
        |      dI(1)
        |      )
        |  )
        |)
        |
      """.stripMargin)
  }}

  it should "work for branching tactic that results in a sole open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    val tactic = BelleParser("""implyR(1); dC("x>=old(x)", 1); <(nil, dI(1))""")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("""implyR(1); dC("x>=old(x)",1); <(nil, dI(1))""")
  }}

  it should "work for branching tactic when following sole open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    val tactic = BelleParser("""implyR(1); dC("x>=old(x)", 1); <(nil, dI(1)); dW(1); QE""")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("""implyR(1); dC("x>=old(x)", 1); <(dW(1); QE, dI(1))""")
  }}

  it should "work for branching tactic when continuing on sole open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    val tactic = BelleParser("""implyR(1); dC("x>=old(x)", 1); <(dW(1), dI(1)); QE""")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("""implyR(1); dC("x>=old(x)", 1); <(dW(1); QE, dI(1))""")
  }}

  it should "work for branching tactic when continuing on sole open goal of a nested branching tactic" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    val tactic = BelleParser("""implyR(1); dC("x>=old(x)", 1); <(cut("0<=1"); <(dW(1), cohideR(2); QE), dI(1)); QE""")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("""implyR(1); dC("x>=old(x)", 1); <(cut("0<=1"); <(dW(1); QE, cohideR(2); QE), dI(1))""")
  }}

  it should "work for branching tactic when following sole second open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    val tactic = BelleParser("""implyR(1); dC("x>=old(x)", 1); <(dW(1); QE, nil); dI(1)""")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("""implyR(1); dC("x>=old(x)", 1); <(dW(1); QE, dI(1))""")
  }}

  it should "work for branching tactic when following sole middle open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x:=x+1;}*]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    val tactic = BelleParser("""implyR(1); loop("x>=0", 1); <(QE, nil, master); QE""")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes
    tree.tactic shouldBe BelleParser("""implyR(1); loop("x>=0", 1); <(QE, QE, master)""")
  }}

  "Continuing a proof" should "work for atomic tactic" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val tree = DbProofTree(db.db, proofId.toString)
    tree.locate("()") match {
      case Some(n) => n.runTactic(db.user.userName, ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), implyR(1), "implyR(1)", wait=true)
    }

    tree.locate("(1,0)") match {
      case Some(n) =>
        val startStepIndex = n.id match {
          case DbStepPathNodeId(id, _) => db.db.getExecutionSteps(proofId.toInt).indexWhere(_.stepId == id)
        }
        val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, startStepIndex, db.db.createProof,
          listener(db.db), ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
        val tactic = BelleParser("""dC("x>=old(x)", 1)""")
        n.stepTactic(db.user.userName, interpreter, tactic, wait=true)
    }

    tree.tactic shouldBe BelleParser("""implyR(1); dC("x>=old(x)", 1); <(nil, nil)""")
  }}

  "Revealing internal steps" should "should work for diffInvariant" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR('R) & diffInvariant("x>=old(x)".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("""implyR('R) ; dC("x>=old(x)",1) ; <(nil, dI(1))""")
  }}

  //@todo nil;nil?
  it should "should work for multiple levels of diffInvariant without let" ignore withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2))
    interpreter(implyR('R) & diffInvariant("x>=0".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    //@note not reprovable, because we record steps at level 2 and lose inputs (DC axiom without input)
    tree.tactic shouldBe BelleParser(
      """implyR('R) ; DC(1) ; <(
        |  nil,
        |  DI(1) ; implyR(1) ; andR(1) ; <(
        |    QE,
        |    derive(1.1) ; DE(1) ; Dassignb(1.1) ; GV(1) ; QE
        |  )
        |)
      """.stripMargin)
  }}

  it should "should work for multiple levels of diffInvariant" ignore withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"ProgramVariables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2))
    interpreter(implyR('R) & diffInvariant("x>=old(x)".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser(
      """
        |implyR('R) & (dCaxiom(1) & <(
        |  (nil&nil),
        |  (nil & (DI(1) & (implyR(1) & (andR(1) & <(
        |    close,
        |    partial(((derive(1.1)&DE(1))&(((((Dassignb(1.1))*1)&nil)&GV(1))&(close|QE)))) ))))) ))
      """.stripMargin)

    //@todo reprove
  }}

  it should "should work for simple diffWeaken" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1 & x>0}]x>=0"
    val modelContent = s"ProgramVariables Real x; End. Problem $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & dW(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    val trace = db.db.getExecutionTrace(proofId)
    trace.steps should have size 4
    trace.steps.head.rule shouldBe "implyR(1)"
    tree.tactic shouldBe BelleParser("implyR(1) ; (DW(1) ; G(1))")
  }}

  it should "should work for diffWeaken" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 & y>=0 & z>=0 -> [{x'=y+z & x>=0}]x>=0"
    val modelContent = s"ProgramVariables Real x, y, z; End. Problem $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & SaturateTactic(andL('Llast)) & dW(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    val trace = db.db.getExecutionTrace(proofId)
    trace.steps.map(_.rule) should contain theSameElementsInOrderAs List("implyR(1)", "andL('Llast)", "andL('Llast)",
      "dC(\"y>=0&z>=0\",1)", "V(1)", "prop", "nil", "DW(1)", "G(1)")
    tree.tactic shouldBe BelleParser(
      "implyR(1) ; (andL('Llast) ; (andL('Llast) ; (dC(\"y>=0&z>=0\",1) ; <( DW(1) ; G(1), V(1) ; prop ))))")
  }}

  it should "should work for Bouncing Ball diffWeaken" in withMathematica { _ => withDatabase { db =>
    val problem = "2*g*x<=2*g*H-v_0^2 & x>=0 & g>0 & 1>=c & c>=0 & r>=0 & x=0 & v=-c*v_0 -> [{x'=v,v'=-g-r*v^2 & x>=0&v>=0}](2*g*x<=2*g*H-v^2 & x>=0)"
    val modelContent = s"Definitions Real c, g, r, H; End. ProgramVariables Real x, v, v_0; End. Problem $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & SaturateTactic(andL('Llast)) & dW(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    val trace = db.db.getExecutionTrace(proofId)
    trace.steps.map(_.rule) should contain theSameElementsInOrderAs List("implyR(1)", "andL('Llast)", "andL('Llast)",
      "andL('Llast)", "andL('Llast)", "andL('Llast)", "andL('Llast)", "andL('Llast)", "dC(\"g>0&1>=c&c>=0&r>=0\",1)",
      "V(1)", "prop", "nil", "DW(1)", "G(1)")
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; (andL('Llast) ; (andL('Llast) ; (andL('Llast) ; (andL('Llast) ; (andL('Llast) ; (andL('Llast) ;
        |(andL('Llast) ; (dC("g>0&1>=c&c>=0&r>=0",1) ; <( DW(1) ; G(1), V(1) ; prop )))))))))""".stripMargin)
  }}

  it should "work with assertions/print/debug on multi-subgoal provables" in withDatabase { db =>
    val problem = "x>=0|!x<0 -> x>=0"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1))
    interpreter(implyR(1) & orL(-1) & DebuggingTactics.assertProvableSize(2) <(closeId, nil), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(closeId, nil)")

    val proofId2 = db.createProof(modelContent, "proof2")
    registerInterpreter(SpoonFeedingInterpreter(proofId2, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2, strict=false))(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    DbProofTree(db.db, proofId2.toString).tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(closeId, notL(-1))")
  }

  it should "work for prop on a simple example" in withDatabase { db =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2))
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    //@todo tactic extraction must be strict too (now removes nil)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; id")

    val proofId2 = db.createProof(modelContent, "proof2")
    registerInterpreter(SpoonFeedingInterpreter(proofId2, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2, strict=false))(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    DbProofTree(db.db, proofId2.toString).tactic shouldBe BelleParser("implyR(1) ; id")
  }

  it should "work with onAll without branches" in withDatabase { db =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1, strict=false))
    interpreter(implyR(1) & closeId & onAll(nil), BelleProvable(ProvableSig.startProof(problem.asFormula)))
    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; id")
  }

  it should "should work for master on a simple example" in withDatabase { db => withMathematica { _ =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2, strict=false))
    interpreter(master(), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; id")
  }}

  it should "should work for prop on a left-branching example" in withDatabase { db =>
    val problem = "x>=0|!x<y -> x>=0"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2))
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(id, notL(-1))")

    val proofId2 = db.createProof(modelContent, "proof2")
    registerInterpreter(SpoonFeedingInterpreter(proofId2, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2, strict=false))(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))
    DbProofTree(db.db, proofId2.toString).tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(id, notL(-1))")
  }

  it should "should work for prop with nested branching" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2, strict=false))
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    DbProofTree(db.db, proofId.toString).tactic shouldBe BelleParser(
      """implyR(1) ; orL(-1) ; <(
        |  andR(1) ; <(
        |    id,
        |    nil
        |  )
        |  ,
        |  andR(1) ; <(
        |    nil,
        |    id
        |  )
        |)
      """.stripMargin)
  }

  it should "work for master on failing QE" in withDatabase { db => withMathematica { _ =>
    val problem = "x>=0 -> x>=2"
    val modelContent = s"ProgramVariables Real x; End.\n\n Problem $problem End."
    val proofId = db.createProof(modelContent, "proof")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = true), 1, strict=false))
    interpreter(master(), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals.loneElement.goal shouldBe Some("==> false".asSequent)
    tree.tactic shouldBe BelleParser("implyR(1) ; QE")
  }}

  private def stepInto(node: ProofTreeNode, expectedStep: String, depth: Int = 1)(db: DBAbstraction): (Int, BelleExpr) = {
    val (localProvable, step) = (ProvableSig.startProof(node.conclusion), node.maker.getOrElse("nil"))
    step shouldBe expectedStep
    val localProofId = db.createProof(localProvable)
    val innerInterpreter = registerInterpreter(SpoonFeedingInterpreter(localProofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), depth, strict=false))
    innerInterpreter(BelleParser(step), BelleProvable(localProvable))
    val innerId = innerInterpreter.innerProofId.getOrElse(localProofId)
    (localProofId, DbProofTree(db, innerId.toString).tactic)
  }

  it should "work in the middle of a proof" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"ProgramVariables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), strict=false))
    interpreter(implyR(1) & prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString).load()
    tree.locate("(2,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop", 2)(db.db)
        tactic shouldBe BelleParser(
          """andR(1) ; <(
            |  orL(-1) ; <(
            |    id,
            |    nil
            |  )
            |  ,
            |  orL(-1) ; <(
            |    nil,
            |    id
            |  )
            |)
          """.stripMargin)
    }
  }

  it should "work in the middle of a proof with the in-memory DB" in {
    val problem = "x>=0|x<y -> x>=0&x<y"
    val provable = ProvableSig.startProof(problem.asFormula)
    val db = new InMemoryDB()
    val proofId = db.createProof(provable)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & prop, BelleProvable(provable))

    val tree = DbProofTree(db, proofId.toString).load()
    tree.locate("(1,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop", 2)(db)
        tactic shouldBe BelleParser(
          """andR(1) ; <(
            |  orL(-1) ; <(
            |    id,
            |    nil
            |  )
            |  ,
            |  orL(-1) ; <(
            |    nil,
            |    id
            |  )
            |)
          """.stripMargin)
    }
  }

  it should "work on a branch in the middle of a proof" in {
    val problem = "x>=0|x<y -> x>=0&x<y"
    val db = new InMemoryDB()

    val provable = ProvableSig.startProof(problem.asFormula)
    val proofId = db.createProof(provable)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & orL(-1) & onAll(prop), BelleProvable(provable))

    val tree = DbProofTree(db, proofId.toString).load()
    tree.locate("(3,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop", 2)(db)
        tactic shouldBe BelleParser(
          """
            |andR(1) ; <(
            |  id,
            |  nil
            |)
          """.stripMargin)
    }

    tree.locate("(2,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop", 2)(db)
        tactic shouldBe BelleParser(
          """
            |andR(1) & <(
            |  nil,
            |  id
            |)
          """.stripMargin)
    }
  }

  //@todo print/parse assert
  it should "should work on a typical example" ignore withDatabase { db => withMathematica { _ =>
    val problem = "x>=0 & y>=1 & z<=x+y & 3>2  -> [x:=x+y;]x>=z"
    val modelContent = s"ProgramVariables. R x. R y. R z. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(prop & unfoldProgramNormalize & QE, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("prop ; unfold ; QE")

    val tree = DbProofTree(db.db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(node) =>
        stepInto(node, "prop")(db.db)._2 shouldBe BelleParser("implyR(1) ; andL(-1) ; andL(-2) ; andL(-3)")
    }

    tree.locate("(2,0)") match {
      case Some(node) =>
        stepInto(node, "unfold")(db.db)._2 shouldBe BelleParser("step(1)")
    }

    tree.locate("(3,0)") match {
      case Some(node) =>
        stepInto(node, "QE")(db.db)._2 shouldBe BelleParser("toSingleFormula ; universalClosure(1) ; rcf")
    }
  }}

  it should "work for dC+DI" in withMathematica { _ =>
    val problem =
      """
        |w()^2*x^2 + y^2 <= c()^2
        |  & d>=0
        |->
        |  [{x'=y, y'=-w()^2*x-2*d*w()*y, d'=7 & w()>=0}]w()^2*x^2 + y^2 <= c()^2
      """.stripMargin
    val p = ProvableSig.startProof(problem.asFormula)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & diffInvariant("d>=0".asFormula)(1), BelleProvable(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (id1, tactic1) = stepInto(n1, """diffInvariant("d>=0", 1)""")(db)
        tactic1 shouldBe BelleParser("""dC("d>=0",1) & <(nil, dI(1))""")
        //diffCut
        DbProofTree(db, id1.toString).locate("(2,0)") match {
          case Some(n2) =>
            val (_, tactic2) = stepInto(n2, """dC("d>=0", 1)""")(db)
            val tacticString = "DC(1) ; <(nil, nil)"
            tactic2 shouldBe BelleParser(tacticString)
            BellePrettyPrinter(tactic2) should equal (tacticString) (after being whiteSpaceRemoved)
        }
        //diffInd
        DbProofTree(db, id1.toString).locate("(3,1)") match {
          case Some(n2) =>
            val (_, tactic) = stepInto(n2, "dI(1)")(db)
            val tacticString = """DI(1) ; implyR(1) ; andR('Rlast) ; <(
                                 |  QE,
                                 |  derive('Rlast.1) ; DE('Rlast) ;
                                 |  Dassignb('Rlast.1) ;
                                 |  Dassignb('Rlast.1) ;
                                 |  Dassignb('Rlast.1) ;
                                 |  DW('Rlast) ;
                                 |  GV('Rlast) ; QE
                                 |)
                               """.stripMargin
            tactic shouldBe BelleParser(tacticString)
            BellePrettyPrinter(tactic) should equal (tacticString) (after being whiteSpaceRemoved)
        }
    }
  }

  it should "work for simple dI" in withMathematica { _ =>
    val problem = "x>0 -> [{x'=3}]x>0".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & dI()(1), BelleProvable(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        val tacticString = """DI(1) ; implyR(1) ; andR('Rlast) ; <(
                             |  QE,
                             |  derive('Rlast.1) ; DE('Rlast) ; Dassignb('Rlast.1) ; GV('Rlast) ; QE
                             |)""".stripMargin
        tactic shouldBe BelleParser(tacticString)
        BellePrettyPrinter(tactic) should equal (tacticString) (after being whiteSpaceRemoved)
        proveBy(problem, implyR(1) & tactic) shouldBe 'proved
    }
  }

  it should "work for simple dI with constants" in withMathematica { _ =>
    val problem = "x>0 & a>=0 -> [{x'=a}]x>0".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & dI()(1), BelleProvable(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        val tacticString = """DI(1) ; implyR(1) ; andR('Rlast) ; <(
                             |  QE,
                             |  derive('Rlast.1) ; DE('Rlast) ; Dassignb('Rlast.1) ; GV('Rlast) ; QE
                             |)""".stripMargin
        tactic shouldBe BelleParser(tacticString)
        BellePrettyPrinter(tactic) should equal (tacticString) (after being whiteSpaceRemoved)
        proveBy(problem, implyR(1) & tactic) shouldBe 'proved
    }
  }

  it should "work for simple dI with non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "x>a -> [{x'=5}]x>a".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(implyR(1) & dI()(1), BelleProvable(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        val tacticString = """DI(1) ; implyR(1) ; andR('Rlast) ; <(
                             |  QE,
                             |  derive('Rlast.1) ; DE('Rlast) ; Dassignb('Rlast.1) ; GV('Rlast) ; QE
                             |)
                           """.stripMargin
        tactic shouldBe BelleParser(tacticString)
        BellePrettyPrinter(tactic) should equal (tacticString) (after being whiteSpaceRemoved)
    }
  }

  it should "work when dI fails with non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "[{x'=5}]x>a".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1, strict = false))
    interpreter(dI()(1), BelleProvable(p))

    val innerId = interpreter.innerProofId.getOrElse(proofId)
    val tree = DbProofTree(db, innerId.toString)
    val tactic = tree.tactic
    //@todo want pending("QE") or pending("QE & done | done") instead of nil
    val tacticString = """DI(1) ; implyR(1) ; andR('Rlast) ; <(
                         |  nil,
                         |  derive('Rlast.1) ; DE('Rlast) ; Dassignb('Rlast.1) ; GV('Rlast) ; QE
                         |)""".stripMargin
    tactic shouldBe BelleParser(tacticString)
    BellePrettyPrinter(tactic) should equal (tacticString) (after being whiteSpaceRemoved)
  }

  it should "work when dI fails with multiple non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "[{x'=5}]x>a+b".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1, strict = false))
    interpreter(dI()(1), BelleProvable(p))

    val innerId = interpreter.innerProofId.getOrElse(proofId)
    val tactic = DbProofTree(db, innerId.toString).tactic
    //@todo want pending("QE") or pending("QE & done | done") instead of nil
    val tacticString = """DI(1) ; implyR(1) ; andR('Rlast) ; <(
                         |  nil,
                         |  derive('Rlast.1) ; DE('Rlast) ; Dassignb('Rlast.1) ; GV('Rlast) ; QE
                         |)""".stripMargin
    tactic shouldBe BelleParser(tacticString)
    BellePrettyPrinter(tactic) should equal (tacticString) (after being whiteSpaceRemoved)
  }

  it should "work for partial prop" in withMathematica { _ => withDatabase { sql =>
    val problem = "x=1 & y=2 -> x=3".asFormula
    val modelFile = s"ProgramVariables R x. R y. End.\n Problem. $problem End."
    val p = ProvableSig.startProof(problem)
    val pId = sql.createProof(modelFile, "model1")
    val tactic = prop & done
    intercept[BelleThrowable] { proveBy(problem, tactic) }.getMessage should startWith ("[Bellerophon Runtime] expected to have proved, but got open goals")
    sql.extractTactic(pId) shouldBe BelleParser("nil")

    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2, strict=false))
    interpreter(tactic, BelleProvable(p))
    DbProofTree(db, proofId.toString).tactic shouldBe BelleParser("""implyR(1) ; andL(-1) ; pending("done")""")
  }}

  "Pending" should "execute and record successful tactic" in withQE { _ => withDatabase { db =>
    val problem = "x>0 -> x>0".asFormula
    val modelFile = s"ProgramVariables Real x. End.\n Problem $problem End."
    val p = ProvableSig.startProof(problem)
    val proofId = db.createProof(modelFile, "model1")
    val tactic = BelleParser("""pending("implyR(1) ; id")""")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2, strict=false))
    interpreter(tactic, BelleProvable(p))
    db.extractTactic(proofId) shouldBe BelleParser("implyR(1) ; id")
  }}

  it should "try execute and record again as pending on failure" in withQE { _ => withDatabase { db =>
    val problem = "x>0 -> x>0".asFormula
    val modelFile = s"ProgramVariables Real x. End.\n Problem $problem End."
    val p = ProvableSig.startProof(problem)
    val proofId = db.createProof(modelFile, "model1")
    val tactic = BelleParser("""pending("implyR(1) ; andR(1)")""")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 2, strict=false))
    interpreter(tactic, BelleProvable(p))
    db.extractTactic(proofId) shouldBe BelleParser("""implyR(1) ; pending("andR(1)")""")
  }}

  it should "not fail on nested tactic with arguments" in withQE { _ => withDatabase { db =>
    val problem = "x>0 -> [x:=x+1;]x>0".asFormula
    val modelFile = s"ProgramVariables Real x. End.\n Problem $problem End."
    val p = ProvableSig.startProof(problem)
    val proofId = db.createProof(modelFile, "model1")
    val tactic = BelleParser("""pending("implyR(1) ; loop(\"x>0\", 1)")""")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 1, strict=false, convertPending=true))
    interpreter(tactic, BelleProvable(p))
    db.extractTactic(proofId) shouldBe BelleParser("""implyR(1) ; pending("loop(\"x>0\", 1)")""")
  }}
}
