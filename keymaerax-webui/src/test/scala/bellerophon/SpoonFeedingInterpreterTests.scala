package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{Idioms, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import testHelper.KeYmaeraXTestTags.SlowTest

import scala.collection.immutable._

/**
  * Tests the spoon-feeding interpreter.
  * Created by smitsch on 8/24/16.
  */
class SpoonFeedingInterpreterTests extends TacticTestBase {

  "Atomic tactic" should "be simply forwarded to the inner interpreter" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    val tactic = implyR(1)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 1
    tree.openGoals.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.nodes should have size 2
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Nil
    tree.root.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula)))
    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.provable.subgoals should have size 1
    tree.root.provable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.localProvable.subgoals should have size 1
    tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.makerShortName shouldBe None
    tree.root.children should have size 1
    tree.root.children.head.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.localProvable.subgoals should have size 1
    tree.root.children.head.localProvable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.makerShortName shouldBe Some("implyR(1)")

    tree.tactic shouldBe tactic
  }

  "Sequential tactic" should "be split into atomics before being fed to inner" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))

    val tactic = implyR(1) & closeId
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 3
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("closeId")::Nil
    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.provable shouldBe 'proved
    tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.localProvable.subgoals should have size 1
    tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.makerShortName shouldBe None
    tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.localProvable.subgoals should have size 1
    tree.root.children.head.localProvable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.makerShortName shouldBe Some("implyR(1)")
    tree.root.children.head.children should have size 1
    tree.root.children.head.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children.head.localProvable.subgoals shouldBe empty
    tree.root.children.head.children.head.makerShortName shouldBe Some("closeId")
    tree.root.children.head.children.head.children shouldBe empty

    tree.tactic shouldBe tactic
  }

  "Either tactic" should "be explored and only successful outcome stored in database" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & (andR(1) | closeId), BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 3
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("closeId")::Nil
    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.provable shouldBe 'proved
    tree.root.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.localProvable.subgoals should have size 1
    tree.root.localProvable.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.makerShortName shouldBe None
    tree.root.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children.head.localProvable.subgoals should have size 1
    tree.root.children.head.localProvable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.makerShortName shouldBe Some("implyR(1)")
    tree.root.children.head.children should have size 1
    tree.root.children.head.children.head.localProvable.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children.head.localProvable.subgoals shouldBe empty
    tree.root.children.head.children.head.makerShortName shouldBe Some("closeId")
    tree.root.children.head.children.head.children shouldBe empty

    tree.tactic shouldBe implyR(1) & closeId
  }

  "Branch tactic" should "work top-level" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId & done, skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 6
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("andR(1)")::
      Some("andR(1)")::Some("nil")::Some("closeId")::Nil
    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&x>=0".asFormula))
    tree.root.provable.subgoals should have size 1
    tree.root.provable.subgoals.head shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>=0".asFormula))
    tree.root.makerShortName shouldBe None
    tree.root.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&x>=0".asFormula))
    tree.root.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&x>=0".asFormula)))
    tree.root.children should have size 1

    val n10 = tree.root.children.head
    n10.makerShortName shouldBe Some("implyR(1)")
    n10.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&x>=0".asFormula))
    n10.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&x>=0".asFormula)))
    n10.children should have size 2

    val n20 = n10.children.head
    n20.makerShortName shouldBe Some("andR(1)")
    n20.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&x>=0".asFormula))
    n20.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    n20.children should have size 1

    val n4 = n20.children.head
    n4.makerShortName shouldBe Some("closeId")
    n4.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    n4.goal shouldBe empty

    val n21 = n10.children(1)
    n21.makerShortName shouldBe Some("andR(1)")
    n21.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&x>=0".asFormula))
    n21.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>=0".asFormula)))
    n21.children should have size 1

    val n31 = n21.children.head
    n31.makerShortName shouldBe Some("nil")
    n31.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>=0".asFormula))
    n31.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>=0".asFormula)))
    n31.children shouldBe empty

    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(closeId, nil)")
  }

  it should "work top-level and support complicated branch tactics" in withMathematica { _ => withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0&[{x'=1&x>=0}]x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId & done, dW(1) & prop & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 7
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
      None::Some("implyR(1)")::Some("andR(1)")::Some("andR(1)")::Some("dW(1)")::Some("prop")::Some("closeId")::Nil
    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&[{x'=1&x>=0}]x>=0".asFormula))
    //tree.root.provable shouldBe 'proved
    tree.root.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&[{x'=1&x>=0}]x>=0".asFormula))
    tree.root.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&[{x'=1&x>=0}]x>=0".asFormula)))
    tree.root.children should have size 1

    val n10 = tree.root.children.head
    n10.makerShortName shouldBe Some("implyR(1)")
    n10.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&[{x'=1&x>=0}]x>=0".asFormula))
    n10.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&[{x'=1&x>=0}]x>=0".asFormula)))
    n10.children should have size 2

    val n20 = n10.children.head
    n20.makerShortName shouldBe Some("andR(1)")
    n20.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&[{x'=1&x>=0}]x>=0".asFormula))
    n20.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    n20.children should have size 1

    val n50 = n20.children.head
    n50.makerShortName shouldBe Some("closeId")
    n50.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    n50.goal shouldBe None
    n50.children shouldBe empty

    val n21 = n10.children(1)
    n21.makerShortName shouldBe Some("andR(1)")
    n21.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&[{x'=1&x>=0}]x>=0".asFormula))
    n21.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=1&x>=0}]x>=0".asFormula)))
    n21.children should have size 1

    val n30 = n21.children.head
    n30.makerShortName shouldBe Some("dW(1)")
    n30.conclusion shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=1&x>=0}]x>=0".asFormula))
    n30.goal shouldBe Some(Sequent(IndexedSeq(), IndexedSeq("x>=0->x>=0".asFormula)))
    n30.children should have size 1

    val n40 = n30.children.head
    n40.makerShortName shouldBe Some("prop")
    n40.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>=0->x>=0".asFormula))
    n40.goal shouldBe None
    n40.children shouldBe empty

    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(closeId, dW(1) ; prop)")
  }}

  it should "work with nested branching when every branch is closed" in withMathematica { _ => withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0|x>1 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(closeId & done, QE & done), QE & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.load()
    tree.nodes should have size 9
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None::Some("implyR(1)")::Some("andR(1)")::
      Some("andR(1)")::Some("QE")::Some("orL(-1)")::Some("orL(-1)")::Some("QE")::Some("closeId")::Nil
    tree.root.provable.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0|x>1 -> x>0&x>=0".asFormula))
    tree.root.provable shouldBe 'proved
    // nodes after orL
    tree.locate("(4,0)").flatMap(_.goal) shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.locate("(4,1)").flatMap(_.goal) shouldBe Some(Sequent(IndexedSeq("x>1".asFormula), IndexedSeq("x>0".asFormula)))
    tree.openGoals shouldBe empty
    tree.tactic shouldBe BelleParser("implyR(1) ; andR(1) ; <(orL(-1) ; <(closeId, QE), QE)")
  }}

  it should "work when early branches remain open and later ones close" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>1|x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & orL(-1) & Idioms.<(skip, closeId & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.root.provable.subgoals should have size 1
    tree.root.provable.subgoals.head shouldBe Sequent(IndexedSeq("x>1".asFormula), IndexedSeq("x>0".asFormula))
    tree.nodes should have size 6
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
      None::Some("implyR(1)")::Some("orL(-1)")::Some("orL(-1)")::Some("closeId")::Some("nil")::Nil
    tree.locate("(2,0)").flatMap(_.goal) shouldBe Some(Sequent(IndexedSeq("x>1".asFormula), IndexedSeq("x>0".asFormula)))
    tree.locate("(2,1)").flatMap(_.goal) shouldBe Some(Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula)))
    tree.openGoals should have size 1
    tree.tactic shouldBe BelleParser("implyR(1) & orL(-1) & <(nil, closeId)")
  }

  it should "work with nested branching when branches stay open 1" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>1|x>0 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(skip, closeId), skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 2
    tree.tactic shouldBe BelleParser("implyR(1) & andR(1) & <(orL(-1) & <(nil, closeId), nil)")
  }

  it should "work with nested branching when branches stay open 2" in withDatabase { db =>
    val modelContent = "Variables. R x. End.\n\n Problem. x>0|x>1 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(closeId, skip), skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 2
    tree.tactic shouldBe BelleParser("implyR(1) & andR(1) & <(orL(-1) & <(closeId, nil), nil)")
  }

  it should "work with nested branching when branching stay open 3" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1))
    interpreter(implyR(1) & orL(-1) & Idioms.<(andR(1) & Idioms.<(closeId, skip), andR(1)),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.openGoals should have size 3
    tree.tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(andR(1) ; <(closeId, nil), andR(1) ; <(nil, nil))")
  }

  "Saturation" should "record each iteration as step" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0&x>1&x>2 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & (andL('L)*), BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 4
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
      None::Some("implyR(1)")::Some("andL('L)")::Some("andL('L)")::Nil
    tree.root.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0&x>1&x>2 -> x>0".asFormula))
    tree.root.provable.subgoals should contain theSameElementsInOrderAs
      Sequent(IndexedSeq("x>0".asFormula, "x>1".asFormula, "x>2".asFormula), IndexedSeq("x>0".asFormula))::Nil
    tree.root.children should have size 1
    val n10 = tree.root.children.head
    n10.makerShortName shouldBe Some("implyR(1)")
    n10.goal shouldBe Some(Sequent(IndexedSeq("x>0&x>1&x>2".asFormula), IndexedSeq("x>0".asFormula)))
    n10.children should have size 1

    val n20 = n10.children.head
    n20.makerShortName shouldBe Some("andL('L)")
    n20.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula, "x>1&x>2".asFormula), IndexedSeq("x>0".asFormula)))
    n20.children should have size 1

    val n30 = n20.children.head
    n30.makerShortName shouldBe Some("andL('L)")
    n30.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula, "x>1".asFormula, "x>2".asFormula), IndexedSeq("x>0".asFormula)))
    n30.children shouldBe empty
  }

  "Repeat" should "record each iteration as step" in withDatabase {db =>
    val modelContent = "Variables. R x. End. Problem. x>0&x>1&x>2&x>3 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & (andL('L)*2), BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 4
    tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
      None::Some("implyR(1)")::Some("andL('L)")::Some("andL('L)")::Nil
    tree.root.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0&x>1&x>2&x>3 -> x>0".asFormula))
    tree.root.provable.subgoals should contain theSameElementsInOrderAs
      Sequent(IndexedSeq("x>0".asFormula, "x>1".asFormula, "x>2&x>3".asFormula), IndexedSeq("x>0".asFormula))::Nil
    tree.root.children should have size 1
    val n10 = tree.root.children.head
    n10.makerShortName shouldBe Some("implyR(1)")
    n10.goal shouldBe Some(Sequent(IndexedSeq("x>0&x>1&x>2&x>3".asFormula), IndexedSeq("x>0".asFormula)))
    n10.children should have size 1

    val n20 = n10.children.head
    n20.makerShortName shouldBe Some("andL('L)")
    n20.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula, "x>1&x>2&x>3".asFormula), IndexedSeq("x>0".asFormula)))
    n20.children should have size 1

    val n30 = n20.children.head
    n30.makerShortName shouldBe Some("andL('L)")
    n30.goal shouldBe Some(Sequent(IndexedSeq("x>0".asFormula, "x>1".asFormula, "x>2&x>3".asFormula), IndexedSeq("x>0".asFormula)))
    n30.children shouldBe empty
  }

  "Parsed tactic" should "record STTT tutorial example 1 steps" taggedAs SlowTest in withDatabase { db => withMathematica { _ =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))

    val tacticText = "implyR('R) & andL('L) & dC({`v>=0`}, 1) & <(dW(1) & prop, dI(1))"
    val tactic = BelleParser(tacticText)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val extractedTactic = db.extractTactic(proofId)
    extractedTactic shouldBe BelleParser(tacticText)
  }}

  it should "record STTT tutorial example 2 steps" taggedAs SlowTest  in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val extractedTactic = db.extractTactic(proofId)
    extractedTactic shouldBe BelleParser(
      """
        |implyR(1) & andL('L) & andL('L) & loop({`v>=0`},1) & <(
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
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; andL('L) ; andL('L) ; loop({`v >= 0 & x+v^2/(2*B()) <= S()`}, 1) ; <(
        |  QE,
        |  QE,
        |  composeb(1) ; choiceb(1) ; andR(1) ; <(
        |    composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; choiceb(1) ; andR(1) ; <(ODE(1), ODE(1)),
        |    choiceb(1) ; andR(1) ; <(
        |      composeb(1) ; testb(1) ; implyR(1) ; assignb(1) ; choiceb(1) ; andR(1) ; <(ODE(1), ODE(1);QE),
        |      assignb(1) ; choiceb(1) ; andR(1) ; <(ODE(1), ODE(1))
        |    )
        |  )
        |)
      """.stripMargin)
  }}

  it should "record STTT tutorial example 4a steps" taggedAs SlowTest in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; loop({`v<=V()`}, 1) ; <(
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
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes should have size 11
    tree.nodes.map(_.makerShortName) should contain theSameElementsAs None::Some("implyR(1)")::Some("andL('L)")::
      Some("loop({`v<=V()`},1)")::Some("loop({`v<=V()`},1)")::Some("loop({`v<=V()`},1)")::
      Some("composeb(1)")::Some("assignb(1)")::Some("ODE(1)")::Some("QE")::Some("QE")::Nil
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; loop({`v<=V()`}, 1) ; <(
        |  QE,
        |  QE,
        |  composeb(1) ; assignb(1) ; ODE(1)
        |)
      """.stripMargin)
  }}

  it should "record STTT tutorial example 9b steps" taggedAs SlowTest in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tacticString
    tree.tactic shouldBe BelleParser(
      """implyR(1) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ;
        |loop({`v >= 0 & xm <= x & xr = (xm + S())/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S() - xm)/2)^2`}, 1) ; <(
        |  QE,
        |  QE,
        |  andL('L) ; andL('L) ; andL('L) ; composeb(1) ; choiceb(1) ; andR(1) ; <(
        |    composeb(1) ; assignb(1) ; composeb(1) ; assignb(1) ; testb(1) ; implyR(1) ;
        |      dC({`xm <= x`}, 1) ; <(
        |        dC({`5/4*(x-(xm+S())/2)^2 + (x-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2`}, 1) ; <(
        |          dW(1) ; QE,
        |          dI(1)
        |        ),
        |        dI(1)
        |      ),
        |    testb(1) ; implyR(1) ;
        |      dC({`xm <= x`}, 1) ; <(
        |        dC({`5/4*(x-(xm+S())/2)^2 + (x-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2`}, 1) ; <(
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
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    //db.extractTactic(proofId) shouldBe tactic //@note not exactly the same, because repetitions are unrolled etc.
    val tree = DbProofTree(db.db, proofId.toString)
    tree.tacticString
    tree.tactic shouldBe BelleParser(
      """
        |implyR(1) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ;
        |loop({`v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly()) + v^2/(2*b()) < lw()`}, 1) ; <(
        |  QE,
        |  QE,
        |  chase('R) ; normalize ; <(
        |    hideL(-9) ; dC({`c>=0`}, 1) ; <(
        |      dC({`dx^2+dy^2=1`}, 1) ; <(
        |        dC({`v=old(v)+a*c`}, 1) ; <(
        |          dC({`-c*(v-a/2*c) <= y - old(y) & y - old(y) <= c*(v-a/2*c)`}, 1) ; <(
        |            dW(1) ;
        |            implyR('R) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ; andL('L) ;
        |            transformEquality({`ep()=c`}, -8) ; prop ; smartQE,
        |            dI(1)
        |          ),
        |          dI(1)
        |        ),
        |        dI(1)
        |        ),
        |      dI(1)
        |      ),
        |    dC({`c>=0`}, 1) ; <(
        |      dC({`dx^2+dy^2=1`}, 1) ; <(
        |        dC({`v=old(v)`}, 1) ; <(
        |          dC({`-c*v <= y - old(y) & y - old(y) <= c*v`}, 1) ; <(
        |            dW(1) ; prop ; smartQE,
        |            dI(1)
        |            ),
        |          dI(1)
        |          ),
        |        dI(1)
        |        ),
        |      dI(1)
        |      ),
        |    dC({`c>=0`}, 1) ; <(
        |      dC({`dx^2+dy^2=1`}, 1) & <(
        |        dC({`v=old(v)+a*c`}, 1) & <(
        |          dC({`-c*(v-a/2*c) <= y - old(y) & y - old(y) <= c*(v-a/2*c)`}, 1) & <(
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
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    val tactic = BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(nil, dI(1))")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1); dC({`x>=old(x)`},1); <(nil, dI(1))")
  }}

  it should "work for branching tactic when following sole open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    val tactic = BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(nil, dI(1)); dW(1); QE")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(dW(1); QE, dI(1))")
  }}

  it should "work for branching tactic when continuing on sole open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    val tactic = BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(dW(1), dI(1)); QE")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(dW(1); QE, dI(1))")
  }}

  it should "work for branching tactic when continuing on sole open goal of a nested branching tactic" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    val tactic = BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(cut({`0<=1`}); <(dW(1), cohideR(2); QE), dI(1)); QE")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(cut({`0<=1`}); <(dW(1); QE, cohideR(2); QE), dI(1))")
  }}

  it should "work for branching tactic when following sole second open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    val tactic = BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(dW(1); QE, nil); dI(1)")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    val foo = tree.nodes
    tree.tactic shouldBe BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(dW(1); QE, dI(1))")
  }}

  it should "work for branching tactic when following sole middle open goal" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x:=x+1;}*]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    val tactic = BelleParser("implyR(1); loop({`x>=0`}, 1); <(QE, nil, master); QE")
    interpreter(tactic, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.nodes
    tree.tactic shouldBe BelleParser("implyR(1); loop({`x>=0`}, 1); <(QE, QE, master)")
  }}

  "Continuing a proof" should "work for atomic tactic" in withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)

    val tree = DbProofTree(db.db, proofId.toString)
    tree.locate("()") match {
      case Some(n) => n.runTactic(db.user.userName, SequentialInterpreter, implyR(1), "implyR(1)", wait=true)
    }

    tree.locate("(1,0)") match {
      case Some(n) =>
        val startStepIndex = n.id match {
          case DbStepPathNodeId(id, _) => db.db.getExecutionSteps(proofId.toInt).indexWhere(_.stepId == id)
        }
        val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, startStepIndex, db.db.createProof, listener(db.db), SequentialInterpreter))
        val tactic = BelleParser("dC({`x>=old(x)`}, 1)")
        n.stepTactic(db.user.userName, interpreter, tactic, wait=true)
    }

    tree.tactic shouldBe BelleParser("implyR(1); dC({`x>=old(x)`}, 1); <(nil, nil)")
  }}

  "Revealing internal steps" should "should work for diffInvariant" in withMathematica { tool => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1))
    interpreter(implyR('R) & diffInvariant("x>=old(x)".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR('R) ; dC({`x>=old(x)`},1) ; <(nil, dI(1))")
  }}

  //@todo nil;nil?
  it should "should work for multiple levels of diffInvariant without let" ignore withMathematica { _ => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 2))
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

  it should "should work for multiple levels of diffInvariant" ignore withMathematica { tool => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 2))
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

  it should "should work for prop on a simple example" in withDatabase { db =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1))
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    //@todo tactic extraction must be strict too (now removes nil)
    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; closeId")

    val proofId2 = db.createProof(modelContent, "proof2")
    registerInterpreter(SpoonFeedingInterpreter(proofId2, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1, strict=false))(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    DbProofTree(db.db, proofId2.toString).tactic shouldBe BelleParser("implyR(1) ; closeId")
  }

  it should "work with onAll without branches" in withDatabase { db =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1, strict=false))
    interpreter(implyR(1) & closeId & onAll(nil), BelleProvable(ProvableSig.startProof(problem.asFormula)))
    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; closeId")
  }

  it should "should work for master on a simple example" in withDatabase { db => withMathematica { _ =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1, strict=false))
    interpreter(master(), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; closeId")
    tree.locate("(2,0)") match { //@note master tries close as step 1, which fails
      case Some(node) => stepInto(node, "implyR(1)")(db.db)._2 shouldBe BelleParser("implyR(1)")
    }
  }}

  it should "should work for prop on a left-branching example" in withDatabase { db =>
    val problem = "x>=0|!x<y -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1))
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString)
    tree.tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(closeId, notL(-1))")

    val proofId2 = db.createProof(modelContent, "proof2")
    registerInterpreter(SpoonFeedingInterpreter(proofId2, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1, strict=false))(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))
    DbProofTree(db.db, proofId2.toString).tactic shouldBe BelleParser("implyR(1) ; orL(-1) ; <(closeId, notL(-1))")
  }

  it should "should work for prop with nested branching" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter, 1, strict=false))
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    DbProofTree(db.db, proofId.toString).tactic shouldBe BelleParser(
      """implyR(1) ; orL(-1) ; <(
        |  andR(1) ; <(
        |    closeId,
        |    nil
        |  )
        |  ,
        |  andR(1) ; <(
        |    nil,
        |    closeId
        |  )
        |)
      """.stripMargin)
  }

  private def stepInto(node: ProofTreeNode, expectedStep: String, depth: Int = 1)(db: DBAbstraction): (Int, BelleExpr) = {
    val (localProvable, step) = (ProvableSig.startProof(node.conclusion), node.maker.getOrElse("nil"))
    step shouldBe expectedStep
    val localProofId = db.createProof(localProvable)
    val innerInterpreter = registerInterpreter(SpoonFeedingInterpreter(localProofId, -1, db.createProof, listener(db),
      SequentialInterpreter, depth, strict=false))
    innerInterpreter(BelleParser(step), BelleProvable(localProvable))
    val innerId = innerInterpreter.innerProofId.getOrElse(localProofId)
    (localProofId, DbProofTree(db, innerId.toString).tactic)
  }

  it should "work in the middle of a proof" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(implyR(1) & prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tree = DbProofTree(db.db, proofId.toString).load()
    tree.locate("(2,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop")(db.db)
        tactic shouldBe BelleParser(
          """orL(-1) ; <(
            |  andR(1) ; <(
            |    closeId,
            |    nil
            |  )
            |  ,
            |  andR(1) ; <(
            |    nil,
            |    closeId
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
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter))
    interpreter(implyR(1) & prop, BelleProvable(provable))

    val tree = DbProofTree(db, proofId.toString).load()
    tree.locate("(1,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop")(db)
        tactic shouldBe BelleParser(
          """orL(-1) ; <(
            |  andR(1) ; <(
            |    closeId,
            |    nil
            |  )
            |  ,
            |  andR(1) ; <(
            |    nil,
            |    closeId
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

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter))
    interpreter(implyR(1) & orL(-1) & onAll(prop), BelleProvable(provable))

    val tree = DbProofTree(db, proofId.toString).load()
    tree.locate("(3,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop")(db)
        tactic shouldBe BelleParser(
          """
            |andR(1) ; <(
            |  closeId,
            |  nil
            |)
          """.stripMargin)
    }

    tree.locate("(2,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop")(db)
        tactic shouldBe BelleParser(
          """
            |andR(1) & <(
            |  nil,
            |  closeId
            |)
          """.stripMargin)
    }
  }

  //@todo print/parse assert
  it should "should work on a typical example" ignore withDatabase { db => withMathematica { tool =>
    val problem = "x>=0 & y>=1 & z<=x+y & 3>2  -> [x:=x+y;]x>=z"
    val modelContent = s"Variables. R x. R y. R z. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
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
    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter))
    interpreter(implyR(1) & diffInvariant("d>=0".asFormula)(1), BelleProvable(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (id1, tactic1) = stepInto(n1, "diffInvariant({`d>=0`}, 1)")(db)
        tactic1 shouldBe BelleParser("dC({`d>=0`},1) & <(nil, dI(1))")
        //diffCut
        DbProofTree(db, id1.toString).locate("(2,0)") match {
          case Some(n2) =>
            val (id2, tactic2) = stepInto(n2, "dC({`d>=0`}, 1)")(db)
            tactic2 shouldBe BelleParser("DC(1) ; <(nil, nil)")
        }
        //diffInd
        DbProofTree(db, id1.toString).locate("(3,1)") match {
          case Some(n2) =>
            val (_, tactic) = stepInto(n2, "dI(1)")(db)
            tactic shouldBe BelleParser(
              """DI(1) ; implyR(1) ; andR(1) ; <(
                |  QE,
                |  derive(1.1) ; DE(1) ; Dassignb(1.1) ; Dassignb(1.1) ; Dassignb(1.1) ; DW(1) ; GV(1) ; QE
                |)
              """.stripMargin)
        }
    }
  }

  it should "work for simple dI" in withMathematica { _ =>
    val problem = "x>0 -> [{x'=3}]x>0".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter))
    interpreter(implyR(1) & dI()(1), BelleProvable(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        tactic shouldBe BelleParser(
          """DI(1) ; implyR(1) ; andR(1) ; <(
            |  QE,
            |  derive(1.1) ; DE(1) ; Dassignb(1.1) ; GV(1) ; QE
            |)""".stripMargin)
        proveBy(problem, implyR(1) & tactic) shouldBe 'proved
    }
  }

  it should "work for simple dI with constants" in withMathematica { _ =>
    val problem = "x>0 & a>=0 -> [{x'=a}]x>0".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter))
    interpreter(implyR(1) & dI()(1), BelleProvable(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        tactic shouldBe BelleParser(
          """DI(1) ; implyR(1) ; andR(1) ; <(
            |  QE,
            |  derive(1.1) ; DE(1) ; Dassignb(1.1) ; GV(1) ; QE
            |)""".stripMargin)
        proveBy(problem, implyR(1) & tactic) shouldBe 'proved
    }
  }

  it should "work for simple dI with non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "x>a -> [{x'=5}]x>a".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter))
    interpreter(implyR(1) & dI()(1), BelleProvable(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        tactic shouldBe BelleParser(
          """DI(1) ; implyR(1) ; andR(1) ; <(
            |  QE,
            |  derive(1.1) ; DE(1) ; Dassignb(1.1) ; GV(1) ; QE
            |)
            """.stripMargin)
    }
  }

  it should "work when dI fails with non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "[{x'=5}]x>a".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter, 1, strict = false))
    val input = BelleProvable(p)
    a [BelleThrowable] should be thrownBy interpreter(dI()(1), input)

    val innerId = interpreter.innerProofId.getOrElse(proofId)
    val tree = DbProofTree(db, innerId.toString)
    val tactic = tree.tactic
    tactic shouldBe BelleParser(
      """DI(1) ; (implyR(1) ; (andR(1) ; <(
        |  QE,
        |  derive(1.1) ; (DE(1) ; (Dassignb(1.1) ; (GV(1) ; QE)))
        |)))
        """.stripMargin)
  }

  it should "work when dI fails with multiple non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "[{x'=5}]x>a+b".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter, 1, strict = false))
    val input = BelleProvable(p)
    a [BelleThrowable] should be thrownBy interpreter(dI()(1), input)

    val innerId = interpreter.innerProofId.getOrElse(proofId)
    val tactic = DbProofTree(db, innerId.toString).tactic
    tactic shouldBe BelleParser(
      """DI(1) ; implyR(1) ; andR(1) ; <(
        |  QE,
        |  derive(1.1) ; DE(1) ; Dassignb(1.1) ; GV(1) ; QE
        |)
      """.stripMargin)
  }

  it should "work for partial prop" in withMathematica { _ => withDatabase { sql =>
    val problem = "x=1 & y=2 -> x=3".asFormula
    val modelFile = s"Variables R x. R y. End.\n Problem. $problem End."
    val p = ProvableSig.startProof(problem)
    val pId = sql.createProof(modelFile, "model1")
    val tactic = prop & done
    intercept[BelleThrowable] { proveBy(problem, tactic) }.getMessage should startWith ("[Bellerophon Runtime] Expected proved provable")
    sql.extractTactic(pId) shouldBe BelleParser("nil")

    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.createProof, listener(db), SequentialInterpreter, 1, strict=false))
    intercept[BelleThrowable] { interpreter(tactic, BelleProvable(p)) }.getMessage should startWith ("[Bellerophon Runtime] Expected proved provable")
    DbProofTree(db, proofId.toString).tactic shouldBe BelleParser("implyR(1) ; andL(-1)")
  }}
}
