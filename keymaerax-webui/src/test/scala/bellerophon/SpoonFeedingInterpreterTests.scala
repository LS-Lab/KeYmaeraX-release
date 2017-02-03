package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleProvable, SequentialInterpreter, SpoonFeedingInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.{Idioms, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.{ExtractTacticFromTrace, InMemoryDB, ProofTree, TreeNode}
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

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1), BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = false)
    tree.nodes should have size 2
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
  }

  "Sequential tactic" should "be split into atomics before being fed to inner" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    interpreter(implyR(1) & closeId, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 3
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 1
    tree.root.children.head.children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children.head.rule shouldBe "closeId"
  }

  "Either tactic" should "be explored and only successful outcome stored in database" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & (andR(1) | closeId), BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 3
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 1
    tree.root.children.head.children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children.head.rule shouldBe "closeId"
  }

  "Branch tactic" should "work top-level" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId & done, skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & andR(1) & <(closeId, nil)")

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 7
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&x>=0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&x>=0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 2
    tree.root.children.head.children(0).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children(0).rule shouldBe "andR(1)"
    tree.root.children.head.children(0).children should have size 1
    tree.root.children.head.children(0).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(0).children.head.rule shouldBe "closeId"
    tree.root.children.head.children(0).children.head.children shouldBe empty
    tree.root.children.head.children(1).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>=0".asFormula))
    tree.root.children.head.children(1).rule shouldBe "andR(1)"
    tree.root.children.head.children(1).children should have size 1
    tree.root.children.head.children(1).children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>=0".asFormula))
    tree.root.children.head.children(1).children.head.rule shouldBe "nil"
  }

  it should "work top-level and support complicated branch tactics" in withMathematica { tool => withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>0&[{x'=1&x>=0}]x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(closeId & done, diffWeaken(1) & prop & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 7
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0 -> x>0&[{x'=1&x>=0}]x>=0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0&[{x'=1&x>=0}]x>=0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 2
    tree.root.children.head.children(0).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children(0).rule shouldBe "andR(1)"
    tree.root.children.head.children(0).children should have size 1
    tree.root.children.head.children(0).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(0).children.head.rule shouldBe "closeId"
    tree.root.children.head.children(0).children.head.children shouldBe empty
    tree.root.children.head.children(1).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("[{x'=1&x>=0}]x>=0".asFormula))
    tree.root.children.head.children(1).rule shouldBe "andR(1)"
    tree.root.children.head.children(1).children should have size 1
    tree.root.children.head.children(1).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>=0->x>=0".asFormula))
    tree.root.children.head.children(1).children.head.rule shouldBe "dW(1)"
    tree.root.children.head.children(1).children.head.children should have size 1
    tree.root.children.head.children(1).children.head.children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(1).children.head.children.head.rule shouldBe "prop"
  }}

  it should "work with nested branching when every branch is closed" in withMathematica { tool => withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>0|x>1 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(closeId & done, QE & done), QE & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 9
    tree.root.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("x>0|x>1 -> x>0&x>=0".asFormula))
    tree.root.children should have size 1
    tree.root.children.head.sequent shouldBe Sequent(IndexedSeq("x>0|x>1".asFormula), IndexedSeq("x>0&x>=0".asFormula))
    tree.root.children.head.rule shouldBe "implyR(1)"
    tree.root.children.head.children should have size 2
    tree.root.children.head.children(0).sequent shouldBe Sequent(IndexedSeq("x>0|x>1".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children(0).rule shouldBe "andR(1)"
    tree.root.children.head.children(0).children should have size 2
    tree.root.children.head.children(0).children(0).sequent shouldBe Sequent(IndexedSeq("x>0".asFormula), IndexedSeq("x>0".asFormula))
    tree.root.children.head.children(0).children(0).rule shouldBe "orL(-1)"
    tree.root.children.head.children(0).children(0).children should have size 1
    tree.root.children.head.children(0).children(0).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(0).children(0).children.head.rule shouldBe "closeId"
    tree.root.children.head.children(1).sequent shouldBe Sequent(IndexedSeq("x>0|x>1".asFormula), IndexedSeq("x>=0".asFormula))
    tree.root.children.head.children(1).rule shouldBe "andR(1)"
    tree.root.children.head.children(1).children should have size 1
    tree.root.children.head.children(1).children.head.sequent shouldBe Sequent(IndexedSeq(), IndexedSeq("true".asFormula))
    tree.root.children.head.children(1).children.head.rule shouldBe "QE"
  }}

  it should "work when early branches remain open and later ones close" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>1|x>0 -> x>0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & orL(-1) & Idioms.<(skip, closeId & done),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & orL(-1) & <(nil, closeId)")
  }

  it should "work with nested branching when branches stay open 1" in withDatabase { db =>
    val modelContent = "Variables. R x. End. Problem. x>1|x>0 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(skip, closeId), skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & andR(1) & <(orL(-1) & <(nil, closeId), nil)")
  }

  it should "work with nested branching when branches stay open 2" in withDatabase { db =>
    val modelContent = "Variables. R x. End.\n\n Problem. x>0|x>1 -> x>0&x>=0 End."
    val proofId = db.createProof(modelContent)

    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(closeId, skip), skip),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & andR(1) & <(orL(-1) & <(closeId, nil), nil)")
  }

  it should "should work with nested branching when branching stay open 3" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(implyR(1) & orL(-1) & Idioms.<(andR(1) & Idioms.<(closeId, skip), andR(1)),
      BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & orL(-1) & <(andR(1) & <(closeId, nil), andR(1))")
  }

  "Parsed tactic" should "record STTT tutorial example 1 steps" taggedAs SlowTest in withDatabase { db => withMathematica { _ =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tacticText = "implyR('R) & andL('L) & DC({`v>=0`}, 1) & <(dW(1) & prop, dI(1))"
    val tactic = BelleParser(tacticText)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val extractedTactic = db.extractTactic(proofId)
    extractedTactic shouldBe BelleParser(tacticText)
  }}

  it should "record STTT tutorial example 2 steps" taggedAs SlowTest  in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example2.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

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

  it should "record STTT tutorial example 3a steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example3a.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 42 // no further testing necessary with this answer ;-)
  }}

  it should "record STTT tutorial example 4a steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4a.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 22
  }}

  it should "record STTT tutorial example 4b steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example4b.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    val tree: ProofTree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt), proofFinished = true)
    tree.nodes should have size 11
  }}

  it should "record STTT tutorial example 9b steps" taggedAs SlowTest in withMathematica { _ => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example9b.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    // db.extractTactic(proofId) shouldBe tactic //@note not exactly the same, because repetitions are unrolled etc.
    db.extractTactic(proofId) shouldBe BelleParser("(implyR(1)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(loop({`v>=0&xm<=x&xr=(xm+S)/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S-xm)/2)^2`},1)&<( QE, QE, (andL('L)&(andL('L)&(andL('L)&(composeb(1)&(choiceb(1)&(andR(1)&<( (composeb(1)&(assignb(1)&(composeb(1)&(assignb(1)&(testb(1)&(implyR(1)&(DC({`xm<=x`},1)&<( (DC({`5/4*(x-(xm+S)/2)^2+(x-(xm+S)/2)*v/2+v^2/4 < ((S-xm)/2)^2`},1)&<( (dW(1)&QE), dI(1) )), dI(1) )))))))), (testb(1)&(implyR(1)&(DC({`xm<=x`},1)&<( (DC({`5/4*(x-(xm+S)/2)^2+(x-(xm+S)/2)*v/2+v^2/4 < ((S-xm)/2)^2`},1)&<( (dW(1)&QE), dI(1) )), dI(1) )))) ))))))) )))))))))")
  }}

  it should "record STTT tutorial example 10 steps" taggedAs SlowTest in withMathematica { tool => withDatabase { db =>
    val modelContent = io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyx")).mkString
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)

    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example10.kyt")).mkString)
    interpreter(tactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))

    //db.extractTactic(proofId) shouldBe tactic //@note not exactly the same, because repetitions are unrolled etc.
    db.extractTactic(proofId) shouldBe BelleParser("(implyR(1)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(loop({`v>=0&dx^2+dy^2=1&r!=0&abs(y-ly)+v^2/(2*b) < lw`},1)&<( QE, QE, (chase('R)&(normalize&<( (HideL(-9)&(DC({`c>=0`},1)&<( (DC({`dx^2+dy^2=1`},1)&<( (DC({`v=old(v)+a*c`},1)&<( (DC({`-c*(v-a/2*c)<=y-old(y)&y-old(y)<=c*(v-a/2*c)`},1)&<( (dW(1)&(implyR('R)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(andL('L)&(transformEquality({`ep=c`},-8)&(prop&smartQE)))))))))), dI(1) )), dI(1) )), dI(1) )), dI(1) ))), (DC({`c>=0`},1)&<( (DC({`dx^2+dy^2=1`},1)&<( (DC({`v=old(v)`},1)&<( (DC({`-c*v<=y-old(y)&y-old(y)<=c*v`},1)&<( (dW(1)&(prop&smartQE)), dI(1) )), dI(1) )), dI(1) )), dI(1) )), (DC({`c>=0`},1)&<( (DC({`dx^2+dy^2=1`},1)&<( (DC({`v=old(v)+a*c`},1)&<( (DC({`-c*(v-a/2*c)<=y-old(y)&y-old(y)<=c*(v-a/2*c)`},1)&<( (dW(1)&(prop&smartQE)), dI(1) )), dI(1) )), dI(1) )), dI(1) )) ))) ))))))))))))")
  }}

  "Revealing internal steps" should "should work for diffInvariant" in withMathematica { tool => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(implyR('R) & diffInvariant("x>=old(x)".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR('R) & DC({`x>=old(x)`},1) & <(nil, dI(1))")
  }}

  it should "should work for multiple levels of diffInvariant without let" in withMathematica { tool => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 2)
    interpreter(implyR('R) & diffInvariant("x>=0".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser(
      """
        |implyR('R) & (DCdiffcut({`x>=0`},1) & <(
        |  (nil&nil),
        |  (nil & (DIa(1) & (implyR(1) & (andR(1) & <(
        |    close,
        |    (derive(1.1)&(DE(1)&(Dassignb(1.1)&(nil&(GV(1)&QE))))) ))))) ))
      """.stripMargin)

    val reprove = proveBy(problem.asFormula, tactic)
    reprove.subgoals should have size 1
    reprove.subgoals.head.ante should contain only "x>=0".asFormula
    reprove.subgoals.head.succ should contain only "[{x'=1&true&x>=0}]x>=0".asFormula
  }}

  it should "should work for multiple levels of diffInvariant" ignore withMathematica { tool => withDatabase { db =>
    val problem = "x>=0 -> [{x'=1}]x>=0"
    val modelContent = s"Variables. R x. End. Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 2)
    interpreter(implyR('R) & diffInvariant("x>=old(x)".asFormula)(1), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser(
      """
        |implyR('R) & (DCaxiom(1) & <(
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
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("nil & implyR(1) & closeId")

    val proofId2 = db.createProof(modelContent, "proof2")
    SpoonFeedingInterpreter(listener(db.db, proofId2), SequentialInterpreter, 1, strict=false)(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))
    db.extractTactic(proofId2) shouldBe BelleParser("implyR(1) & closeId")
  }

  it should "work with onAll without branches" in withDatabase { db =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1, strict=false)
    interpreter(implyR(1) & closeId & onAll(nil), BelleProvable(ProvableSig.startProof(problem.asFormula)))
    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("implyR(1) & closeId")
  }

  it should "should work for master on a simple example" in withDatabase { db => withMathematica { _ =>
    val problem = "x>=0 -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1, strict=false)
    interpreter(master(), BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("normalize")
    ProofTree.ofTrace(db.db.getExecutionTrace(proofId)).findNode("1") match {
      case Some(node) => stepInto(node, "normalize")._2 shouldBe BelleParser("implyR(1) & closeId")
    }
  }}

  it should "should work for prop on a left-branching example" in withDatabase { db =>
    val problem = "x>=0|!x<y -> x>=0"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("nil & implyR(1) & orL(-1) & <(closeId, notL(-1) & nil & nil)")

    val proofId2 = db.createProof(modelContent, "proof2")
    SpoonFeedingInterpreter(listener(db.db, proofId2), SequentialInterpreter, 1, strict=false)(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))
    db.extractTactic(proofId2) shouldBe BelleParser("implyR(1) & orL(-1) & <(closeId, notL(-1))")
  }

  it should "should work for prop with nested branching" in withDatabase { db =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val modelContent = s"Variables. R x. R y. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent, "proof1")
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter, 1)
    interpreter(prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser(
      """
        |nil & implyR(1) & orL(-1) & <(
        |  nil & andR(1) & <(
        |    closeId,
        |    nil
        |  )
        |  ,
        |  nil & andR(1) & <(
        |    nil,
        |    closeId
        |  )
        |)
      """.stripMargin)

    val proofId2 = db.createProof(modelContent, "proof2")
    SpoonFeedingInterpreter(listener(db.db, proofId2), SequentialInterpreter, 1, strict=false)(
      prop, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    db.extractTactic(proofId2) shouldBe BelleParser(
      """
        |implyR(1) & orL(-1) & <(
        |  andR(1) & <(
        |    closeId,
        |    nil
        |  )
        |  ,
        |  andR(1) & <(
        |    nil,
        |    closeId
        |  )
        |)
      """.stripMargin)
  }

  private def stepInto(node: TreeNode, expectedStep: String, depth: Int = 1)(implicit db: InMemoryDB = new InMemoryDB): (Int, BelleExpr) = {
    val (localProvable, step) = node.endStep match {
      case Some(end) => (ProvableSig.startProof(end.input.subgoals(end.branch)), end.rule)
    }
    step shouldBe expectedStep
    val localProofId = db.createProof(localProvable)
    val innerInterpreter = SpoonFeedingInterpreter(listener(db, localProofId, Some(localProvable)),
      SequentialInterpreter, depth, strict=false)
    innerInterpreter(BelleParser(step), BelleProvable(localProvable))
    val tactic = new ExtractTacticFromTrace(db).apply(db.getExecutionTrace(localProofId))
    (localProofId, tactic)
  }

  it should "work in the middle of a proof" in {
    val problem = "x>=0|x<y -> x>=0&x<y"
    val provable = ProvableSig.startProof(problem.asFormula)
    val db = new InMemoryDB()
    val proofId = db.createProof(provable)
    val interpreter = SpoonFeedingInterpreter(listener(db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & prop, BelleProvable(provable))

    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
    tree.findNode("2") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop")
        tactic shouldBe BelleParser(
          """
            |orL(-1) & <(
            |  andR(1) & <(
            |    closeId,
            |    nil
            |  )
            |  ,
            |  andR(1) & <(
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

    val interpreter = SpoonFeedingInterpreter(listener(db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & orL(-1) & onAll(prop), BelleProvable(provable))

    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId))
    tree.findNode("3") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop")
        tactic shouldBe BelleParser(
          """
            |andR(1) & <(
            |  closeId,
            |  nil
            |)
          """.stripMargin)
    }

    tree.findNode("4") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop")
        tactic shouldBe BelleParser(
          """
            |andR(1) & <(
            |  nil,
            |  closeId
            |)
          """.stripMargin)
    }
  }

  it should "should work on a typical example" in withDatabase { db => withMathematica { tool =>
    val problem = "x>=0 & y>=1 & z<=x+y & 3>2  -> [x:=x+y;]x>=z"
    val modelContent = s"Variables. R x. R y. R z. End.\n\n Problem. $problem End."
    val proofId = db.createProof(modelContent)
    val interpreter = SpoonFeedingInterpreter(listener(db.db, proofId), SequentialInterpreter)
    interpreter(prop & unfoldProgramNormalize & QE, BelleProvable(ProvableSig.startProof(problem.asFormula)))

    val tactic = db.extractTactic(proofId)
    tactic shouldBe BelleParser("prop & unfold & QE")

    val tree = ProofTree.ofTrace(db.db.getExecutionTrace(proofId.toInt))
    tree.findNode("1") match {
      case Some(node) =>
        stepInto(node, "prop")._2 shouldBe BelleParser("implyR(1) & andL(-1) & andL(-2) & andL(-3)")
    }

    tree.findNode("2") match {
      case Some(node) =>
        val expected =
          stepInto(node, "unfold")._2 shouldBe BelleParser("chase('R) & normalize")
    }

    tree.findNode("3") match {
      case Some(node) =>
        stepInto(node, "QE")._2 shouldBe BelleParser("toSingleFormula & universalClosure(1) & rcf")
    }
  }}

  it should "work for DC+DI" in withMathematica { tool =>
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
    val interpreter = SpoonFeedingInterpreter(listener(db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & diffInvariant("d>=0".asFormula)(1), BelleProvable(p))

    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
    tree.findNode("2") match {
      case Some(n1) =>
        val (id1, tactic1) = stepInto(n1, "diffInvariant({`d>=0`},1)")
        tactic1 shouldBe BelleParser("DC({`d>=0`},1) & <(nil, dI(1))")
        //diffCut
        ProofTree.ofTrace(db.getExecutionTrace(id1)).findNode("1") match {
          case Some(n2) =>
            val (id2, tactic2) = stepInto(n2, "DC({`d>=0`},1)")
            tactic2 shouldBe BelleParser("DCdiffcut({`d>=0`},1)")
            ProofTree.ofTrace(db.getExecutionTrace(id2)).findNode("1") match {
              case Some(n3) =>
                val (_, tactic3) = stepInto(n3, "DCdiffcut({`d>=0`},1)")
                tactic3 shouldBe BelleParser("DCa(1)")
            }
        }
        //diffInd
        ProofTree.ofTrace(db.getExecutionTrace(id1)).findNode("3") match {
          case Some(n2) =>
            val (_, tactic) = stepInto(n2, "dI(1)")
            tactic shouldBe BelleParser(
              """
                |DIa(1) & implyR(1) & andR(1) & <(
                |  QE,
                |  derive(1.1) & DE(1) & Dassignb(1.1) & Dassignb(1.1) & Dassignb(1.1) & DWa(1) & GV(1) & QE
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
    val interpreter = SpoonFeedingInterpreter(listener(db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & diffInd()(1), BelleProvable(p))

    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
    tree.findNode("2") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")
        tactic shouldBe BelleParser(
          """DIa(1) & implyR(1) & andR(1) & <(
            |  close,
            |  derive(1.1) & DE(1) & Dassignb(1.1) & GV(1) & QE
            |)""".stripMargin)
        proveBy(problem, implyR(1) & tactic) shouldBe 'proved
    }
  }

  it should "work for simple dI with constants" in withMathematica { _ =>
    val problem = "x>0 & a>=0 -> [{x'=a}]x>0".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = SpoonFeedingInterpreter(listener(db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & diffInd()(1), BelleProvable(p))

    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
    tree.findNode("2") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")
        tactic shouldBe BelleParser(
          """DIa(1) & implyR(1) & andR(1) & <(
            |  QE,
            |  derive(1.1) & DE(1) & Dassignb(1.1) & GV(1) & QE
            |)""".stripMargin)
        proveBy(problem, implyR(1) & tactic) shouldBe 'proved
    }
  }

  it should "work for simple dI with non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "x>a -> [{x'=5}]x>a".asFormula
    val p = ProvableSig.startProof(problem)
    implicit val db = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = SpoonFeedingInterpreter(listener(db, proofId), SequentialInterpreter)
    interpreter(implyR(1) & diffInd()(1), BelleProvable(p))

    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
    tree.findNode("2") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")
        tactic shouldBe BelleParser(
          """let ({`a()=a`}) in (
            |  ((DIa(1) ; implyR(1)) ; andR(1)) ; <(
            |    (close | QE) ; done,
            |    (derive(1.1) ; DE(1)) ; (((Dassignb(1.1)*1 ; nil) ; GV(1)) ; (close | QE)) ; done
            |  )
            |)""".stripMargin)
        proveBy(problem, implyR(1) & tactic) shouldBe 'proved
    }
  }
}
