/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.{
  DebuggingTactics,
  DifferentialEquationCalculus,
  Idioms,
  SimplifierV3,
  TacticTestBase,
  TactixLibrary,
}
import edu.cmu.cs.ls.keymaerax.core.{Bool, Formula, Function, Real, Tuple, Unit}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tagobjects.{SlowTest, TodoTest}
import org.scalatest.LoneElement._
import org.scalatest.OptionValues._

import scala.collection.immutable._
import scala.language.{postfixOps, reflectiveCalls}

/** Tests the spoon-feeding interpreter. Created by smitsch on 8/24/16. */
class SpoonFeedingInterpreterTests extends TacticTestBase {

  private lazy val tacticParser = ArchiveParser.tacticParser

  private def createInterpreter(
      proofId: Int,
      db: DBAbstraction,
      constructGlobalProvable: Boolean = true,
      defs: Declaration = Declaration(Map.empty),
  ) = registerInterpreter(SpoonFeedingInterpreter(
    proofId,
    -1,
    db.createProof,
    defs,
    listener(db, constructGlobalProvable),
    ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
    0,
    strict = true,
    convertPending = true,
    recordInternal = true,
  ))

  "Atomic tactic" should "be simply forwarded to the inner interpreter" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      val tactic = implyR(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 1
      tree.openGoals.head.goal shouldBe Some("x>0 ==> x>0".asSequent)
      tree.nodes should have size 2
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("implyR(1)") :: Nil
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

      tree.tactic shouldBe tacticParser("implyR('R==\"x>0->x>0\");todo")
    }
  }

  it should "record pending if not applicable" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      val tactic = andR(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals.loneElement.goal shouldBe Some("==> x>0 -> x>0".asSequent)
      tree.nodes should have size 2
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some(
        """pending("andR(1)")"""
      ) :: Nil
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
  }

  it should "FEATURE_REQUEST: apply print to all subgoals" taggedAs TodoTest in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>0&x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & DebuggingTactics.printX("Two goals"),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        "implyR('R==\"x>0->x>0&x>0&x>0\"); andR('R==\"x>0&x>0&x>0\"); print(\"Two goals\"); <(\"x>0\": todo, \"x>0&x>0\": todo)"
      )
      db.db.getExecutionTrace(proofId).steps.map(_.rule) should contain theSameElementsInOrderAs
        "implyR(1)" :: "andR(1)" :: "print(\"Two goals\")" :: Nil
    }
  }

  it should "FEATURE_REQUEST: apply nil to all subgoals" taggedAs TodoTest in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>0&x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & nil,
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0->x>0&x>0&x>0");
          |andR('R=="x>0&x>0&x>0"); <(
          |  "x>0": todo,
          |  "x>0&x>0": todo
          |)""".stripMargin
      )
      db.db.getExecutionTrace(proofId).steps.map(_.rule) should contain theSameElementsInOrderAs
        "implyR(1)" :: "andR(1)" :: "nil" :: Nil
    }
  }

  "Sequential tactic" should "be split into atomics before being fed to inner" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)

      val tactic = implyR(1) & id
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 3
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("implyR(1)") :: Some(
        "id"
      ) :: Nil
      tree.root.provable.conclusion shouldBe "==> x>0 -> x>0".asSequent
      tree.root.provable shouldBe Symbol("proved")
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

      tree.tactic shouldBe tacticParser("implyR('R==\"x>0->x>0\"); id")
    }
  }

  it should "be recorded as pending on failure" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 & x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)

      val tactic = implyR(1) & TactixLibrary.loop("x>0".asFormula)(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))
      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser("""pending("implyR(1)") ; pending("loop(\"x>0\", 1)") ; todo""")
    }
  }

  it should "record only RHS as pending on failure" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)

      val tactic = implyR(1) & TactixLibrary.loop("x>0".asFormula)(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))
      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser("""implyR('R=="x>0->x>0"); pending("loop(\"x>0\", 1)") ; todo""")
    }
  }

  "Either tactic" should "be explored and only successful outcome stored in database" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & (andR(1) | id),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 3
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("implyR(1)") :: Some(
        "id"
      ) :: Nil
      tree.root.provable.conclusion shouldBe "==> x>0 -> x>0".asSequent
      tree.root.provable shouldBe Symbol("proved")
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

      tree.tactic shouldBe tacticParser("""implyR('R=="x>0->x>0"); id""")
    }
  }

  it should "be explored and stored pending if failing" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & (andR(1) | orR(1)),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 3
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("implyR(1)") :: Some(
        """pending("andR(1) | orR(1)")"""
      ) :: Nil
    }
  }

  it should "discard previously recorded tactic steps when recording alternatives" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>=0 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & (prop & done | done),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 3
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("implyR(1)") :: Some(
        """pending("prop ; done | done")"""
      ) :: Nil
    }
  }

  "Branch tactic" should "work simple top-level" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & Idioms.<(id, id),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0->x>0&x>0"); andR('R=="x>0&x>0"); <("L//x>0": id, "R//x>0": id)"""
      )
    }
  }

  it should "preserve labels" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>(-1) End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      ) match {
        case BelleProvable(p, l) =>
          p.subgoals should contain theSameElementsAs List("x>0 ==> x>0".asSequent, "x>0 ==> x>(-1)".asSequent)
          l.value should contain theSameElementsAs List("x>0".asLabel, "x>(-1)".asLabel)
      }

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        "implyR('R==\"x>0->x>0&x>(-1)\"); andR('R==\"x>0&x>(-1)\"); <( \"x>0\": todo, \"x>(-1)\": todo )"
      )
    }
  }

  it should "preserve nested labels" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>(-1) End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & CaseTactic(List("x>0".asLabel -> id, "x>(-1)".asLabel -> cut("x>=0".asFormula))),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      ) match {
        case BelleProvable(p, l) =>
          p.subgoals should contain theSameElementsAs List(
            "x>0 ==> x>(-1), x>=0".asSequent,
            "x>0, x>=0 ==> x>(-1)".asSequent,
          )
          l.value should contain theSameElementsAs List("x>(-1)//Use".asLabel, "x>(-1)//Show".asLabel)
      }

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0->x>0&x>(-1)");
          |andR('R=="x>0&x>(-1)"); <(
          |  "x>0": id,
          |  "x>(-1)":
          |    cut("x>=0"); <(
          |     "Use": todo,
          |     "Show": todo
          |    )
          |)""".stripMargin
      )
    }
  }

  it should "delete labels of closed branches" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>(-1) End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & CaseTactic(List(
          "x>0".asLabel -> id,
          "x>(-1)".asLabel -> (cut("x>0".asFormula) & CaseTactic(
            List("Use".asLabel -> (hideL(-1) & QE), "Show".asLabel -> (hideR(1) & propClose))
          )),
        )),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      ) match {
        case BelleProvable(p, l) =>
          p shouldBe Symbol("proved")
          l shouldBe Symbol("empty")
      }

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0->x>0&x>(-1)");
          |andR('R=="x>0&x>(-1)"); <(
          |  "x>0": id,
          |  "x>(-1)":
          |    cut("x>0"); <(
          |     "Use": hideL('L=="x>0"); QE,
          |     "Show": hideR('R=="x>(-1)"); propClose
          |    )
          |)""".stripMargin
      )
    }
  }

  it should "delete labels of auto-closed goals" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent =
        "ArchiveEntry \"Test\" ProgramVariables Real x,v,a; End. Problem x>=0 -> [{x'=v & v>=0 & a<=-5}](v>=0 & a<=0) End. End."
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        tacticParser.tacticParser("auto"),
        BelleProvable.labeled(
          ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent)),
          Some(List(BelleTopLevelLabel("A label"))),
        ),
      ) match {
        case BelleProvable(p, l) =>
          p shouldBe Symbol("proved")
          l.toList.flatten shouldBe Symbol("empty")
      }
    }
  }

  it should "delete labels of closed goals" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent =
        "ArchiveEntry \"Test\" ProgramVariables Real x, eps; End. Problem true & !(-2<x&x<=1) & x<=1 -> !-2<x End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & label("Delete") & propClose,
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      ) match {
        case BelleProvable(p, l) =>
          p shouldBe Symbol("proved")
          l.value shouldBe Symbol("empty")
      }

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="true & !(-2<x&x<=1) & x<=1 -> !-2<x"); label("Delete"); propClose"""
      )
    }
  }

  it should "work nested branching top-level" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>0&x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & Idioms.<(id, andR(1) & Idioms.<(id, id)),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0->x>0&x>0&x>0");
          |andR('R=="x>0&x>0&x>0"); <(
          |  "x>0": id,
          |  "x>0&x>0": andR('R=="x>0&x>0"); <(
          |    "L//x>0": id,
          |    "R//x>0": id
          |  )
          |)""".stripMargin
      )
      db.db.getExecutionTrace(proofId).steps.map(_.rule) should contain theSameElementsInOrderAs
        "implyR(1)" :: "andR(1)" :: "andR(1)" :: "id" :: "id" :: "id" :: Nil
    }
  }

  it should "support nested branching with unconventional closing" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>0&x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & Idioms.<(nil, andR(1) & Idioms.<(id, nil) & id) & id,
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0->x>0&x>0&x>0");
          |andR('R=="x>0&x>0&x>0");<(
          |  "x>0": id,
          |  "x>0&x>0": andR('R=="x>0&x>0"); <(
          |    "L//x>0": id,
          |    "R//x>0": id
          |  )
          |)""".stripMargin
      )
      db.db.getExecutionTrace(proofId).steps.map(_.rule) should contain theSameElementsInOrderAs
        "implyR(1)" :: "andR(1)" :: "andR(1)" :: "nil" :: "id" :: "id" :: "nil" :: "id" :: Nil
    }
  }

  it should "work top-level" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&x>=0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & Idioms.<(id & done, skip),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 6
      /*
       * List(None, Some("implyR(1)"), Some("andR(1)"), Some("andR(1)"), Some("skip"), Some("id"))
       * List(None, Some("implyR(1)"), Some("andR(1)"), Some("andR(1)"), Some("nil"), Some("id"))
       * did not contain the same elements in the same (iterated) order as

       */
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("implyR(1)") :: Some(
        "andR(1)"
      ) ::
        Some("andR(1)") :: Some("skip") :: Some("id") :: Nil
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
      n31.makerShortName shouldBe Some("skip")
      n31.conclusion shouldBe "x>0 ==> x>=0".asSequent
      n31.goal shouldBe Some("x>0 ==> x>=0".asSequent)
      n31.children shouldBe empty

      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0->x>0&x>=0");
          |andR('R=="x>0&x>=0"); <(
          |  "x>0": id,
          |  "x>=0": todo
          |)""".stripMargin
      )
    }
  }

  it should "work top-level and support complicated branch tactics" taggedAs SlowTest in withMathematica { _ =>
    withDatabase { db =>
      val modelContent =
        "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>0&[{x'=1&x>=0}]x>=0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & Idioms.<(id & done, dW(1) & prop & done),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 7
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
        None :: Some("implyR(1)") :: Some("andR(1)") :: Some("andR(1)") :: Some("dW(1)") :: Some("prop") :: Some(
          "id"
        ) :: Nil
      tree.root.provable.conclusion shouldBe "==> x>0 -> x>0&[{x'=1&x>=0}]x>=0".asSequent
      // tree.root.provable shouldBe 'proved
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
      n30.goal shouldBe Some("x>=0 ==> x>=0".asSequent)
      n30.children should have size 1

      val n40 = n30.children.head
      n40.makerShortName shouldBe Some("prop")
      n40.conclusion shouldBe "x>=0 ==> x>=0".asSequent
      n40.goal shouldBe None
      n40.children shouldBe empty

      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0->x>0&[{x'=1&x>=0}]x>=0");
          |andR('R=="x>0&[{x'=1&x>=0}]x>=0"); <(
          |  "x>0": id,
          |  "[{x'=1&x>=0}]x>=0": dW('R=="[{x'=1&x>=0}]x>=0"); prop
          |)""".stripMargin
      )
    }
  }

  it should "work with nested branching when every branch is closed" in withMathematica { _ =>
    withDatabase { db =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0|x>1 -> x>0&x>=0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(id & done, QE & done), QE & done),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.load()
      tree.nodes should have size 9
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("implyR(1)") :: Some(
        "andR(1)"
      ) ::
        Some("andR(1)") :: Some("QE") :: Some("orL(-1)") :: Some("orL(-1)") :: Some("QE") :: Some("id") :: Nil
      tree.root.provable.conclusion shouldBe "==> x>0|x>1 -> x>0&x>=0".asSequent
      tree.root.provable shouldBe Symbol("proved")
      // nodes after orL
      tree.locate("(4,0)").flatMap(_.goal) shouldBe Some("x>0 ==> x>0".asSequent)
      tree.locate("(4,1)").flatMap(_.goal) shouldBe Some("x>1 ==> x>0".asSequent)
      tree.openGoals shouldBe empty
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0|x>1->x>0&x>=0");
          |andR('R=="x>0&x>=0"); <(
          |  "x>0": orL('L=="x>0|x>1"); <(
          |    "x>0": id,
          |    "x>1": QE
          |  ),
          |  "x>=0": QE
          |)
          |""".stripMargin
      )
    }
  }

  it should "work when early branches remain open and later ones close" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>1|x>0 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & orL(-1) & Idioms.<(skip, id & done),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.root.provable.subgoals should have size 1
      tree.root.provable.subgoals.head shouldBe "x>1 ==> x>0".asSequent
      tree.nodes should have size 6

      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
        None :: Some("implyR(1)") :: Some("orL(-1)") :: Some("orL(-1)") :: Some("id") :: Some("skip") :: Nil
      tree.locate("(2,0)").flatMap(_.goal) shouldBe Some("x>1 ==> x>0".asSequent)
      tree.locate("(2,1)").flatMap(_.goal) shouldBe Some("x>0 ==> x>0".asSequent)
      tree.openGoals should have size 1
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>1|x>0->x>0");
          |orL('L=="x>1|x>0"); <(
          |  "x>1": todo,
          |  "x>0": id
          |)""".stripMargin
      )
    }
  }

  it should "work with nested branching when branches stay open 1" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>1|x>0 -> x>0&x>=0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) & Idioms.<(orL(-1) & Idioms.<(skip, id), skip),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 2
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>1|x>0->x>0&x>=0");
          |andR('R=="x>0&x>=0"); <(
          |  "x>0": orL('L=="x>1|x>0"); <(
          |    "x>1": todo,
          |    "x>0": id
          |  ),
          |  "x>=0": todo
          |)""".stripMargin
      )
    }
  }

  it should "work with nested branching when branches stay open 2" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End.\n\n Problem x>0|x>1 -> x>0&x>=0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & andR(1) < (orL(-1) < (id, skip), skip),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 2
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>0|x>1->x>0&x>=0");
          |andR('R=="x>0&x>=0"); <(
          |  "x>0": orL('L=="x>0|x>1"); <(
          |    "x>0": id,
          |    "x>1": todo
          |  ),
          |  "x>=0": todo
          |)""".stripMargin
      )
    }
  }

  it should "work with nested branching when branching stay open 3" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|x<y -> x>=0&x<y"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & orL(-1) < (andR(1) < (id, nil), andR(1)),
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 3
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0|x < y->x>=0&x < y");
          |orL('L=="x>=0|x < y"); <(
          |  "x>=0": andR('R=="x>=0&x < y"); <(
          |    "x>=0": id,
          |    "x < y": todo
          |  ),
          |  "x < y": andR('R=="x>=0&x < y"); <(
          |    "x>=0": todo,
          |    "x < y": todo
          |  )
          |)""".stripMargin
      )
    }
  }

  it should "work with nested branching when branching stay open 4" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|x<y -> x>=0&x<y"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & orL(-1) < (andR(1) < (id, skip), andR(1) < (skip, id)),
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 2
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0|x < y->x>=0&x < y");
          |orL('L=="x>=0|x < y"); <(
          |  "x>=0": andR('R=="x>=0&x < y"); <(
          |    "x>=0": id,
          |    "x < y": todo
          |  ),
          |  "x < y": andR('R=="x>=0&x < y"); <(
          |    "x>=0": todo,
          |    "x < y": id
          |  )
          |)""".stripMargin
      )
    }
  }

  it should "work with nested branching and repeat" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|x<y -> x>=0&(x>=0&x<y)"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & orL(-1) < ((andR(1) < (id, skip)) * 2, andR(1) < (skip, andR(1) < (skip, id))),
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 3
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0|x < y->x>=0&x>=0&x < y");
          |orL('L=="x>=0|x < y"); <(
          |  "x>=0": andR('R=="x>=0&x>=0&x < y"); <(
          |    "x>=0": id,
          |    "x>=0&x < y": andR('R=="x>=0&x < y"); <(
          |      "x>=0": id,
          |      "x < y": todo
          |    )
          |  ),
          |  "x < y": andR('R=="x>=0&x>=0&x < y"); <(
          |    "x>=0": todo,
          |    "x>=0&x < y": andR('R=="x>=0&x < y"); <(
          |      "x>=0": todo,
          |      "x < y": id
          |    )
          |  )
          |)""".stripMargin
      )
    }
  }

  it should "work with loop tactic" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0 -> [{x:=x+1;}*]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = false,
        recordInternal = true,
      ))
      interpreter(
        implyR(1) & loop("x>=0".asFormula)(1),
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 3
      // println("What: " + tree.tactic.length  + " vs. " + bp)
      val tl = tree.tactic
      val tr = tacticParser(
        """implyR('R=="x>=0->[{x:=x+1;}*]x>=0");
          |cutR("[{x:=x+1;}*](x>=0&!false)", 'R=="[{x:=x+1;}*]x>=0"); <(
          |  I('R=="[{x:=x+1;}*](x>=0&!false)");
          |  andR('R=="(x>=0&!false)&[{x:=x+1;}*](x>=0&!false->[x:=x+1;](x>=0&!false))"); <(
          |    "x>=0&!false":
          |      andR('R=="x>=0&!false"); <(
          |        "x>=0": label("Init"); todo,
          |        "!false": notR('R=="!false"); close
          |      ),
          |    "[{x:=x+1;}*](x>=0&!false->[x:=x+1;](x>=0&!false))":
          |      cohide('R=="[{x:=x+1;}*](x>=0&!false->[x:=x+1;](x>=0&!false))");
          |      Goedel;
          |      implyR('R=="x>=0&!false->[x:=x+1;](x>=0&!false)");
          |      boxAnd('R=="[x:=x+1;](x>=0&!false)");
          |      andR('R=="[x:=x+1;]x>=0&[x:=x+1;](!false)"); <(
          |        "[x:=x+1;]x>=0":
          |          andL('Llast);
          |          hideL('Llast);
          |          label("Step");
          |          todo,
          |        "[x:=x+1;](!false)":
          |          andL('L=="x>=0&!false");
          |          hideL('L=="x>=0");
          |          V('R=="[x:=x+1;](!false)");
          |          closeId(-1,1)
          |      )
          |  ),
          |  cohide('R=="[{x:=x+1;}*](x>=0&!false)->[{x:=x+1;}*]x>=0");
          |  CMonCongruence(".1");
          |  implyR('R=="x>=0&!false->x>=0");
          |  andL('Llast);
          |  hideL('Llast);
          |  label("Post");
          |  todo
          |)""".stripMargin
      )
      tl.prettyString shouldBe tr.prettyString
    }
  }

  it should "work with loop tactic that preserves constants" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0 & A>0&B>0&C>0 -> [{x:=x+B;}*]x>=0"
      val modelContent =
        s"""ArchiveEntry "Test" Definitions Real A,B,C; End. ProgramVariables Real x; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = false,
        recordInternal = true,
      ))
      interpreter(
        implyR(1) & loop("x>=0".asFormula)(1),
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals should have size 3
      val (tl, tr) = (
        tree.tactic,
        tacticParser(
          """
            |implyR('R=="x>=0&A()>0&B()>0&C()>0->[{x:=x+B();}*]x>=0");
            |alphaRule; /*andL('L=="x>=0&A>0&B>0&C>0");*/
            |alphaRule; /*andL('L=="A>0&B>0&C>0");*/
            |alphaRule; /*andL('L=="B>0&C>0");*/
            |cutR("[{x:=x+B;}*](x>=0&A>0&B>0&C>0&!false)", 'R=="[{x:=x+B;}*]x>=0"); <(
            |  I('R=="[{x:=x+B;}*](x>=0&A>0&B>0&C>0&!false)");
            |  andR('R=="(x>=0&A>0&B>0&C>0&!false)&[{x:=x+B;}*](x>=0&A>0&B>0&C>0&!false->[x:=x+B;](x>=0&A>0&B>0&C>0&!false))"); <(
            |    "x>=0&A>0&B>0&C>0&!false": andR('R=="x>=0&A>0&B>0&C>0&!false"); <(
            |      "x>=0": label("Init"); todo,
            |      "A>0&B>0&C>0&!false": andR('R=="A>0&B>0&C>0&!false"); <(
            |        "A>0": idWith('R=="A>0"),
            |        "B>0&C>0&!false": andR('R=="B>0&C>0&!false"); <(
            |          "B>0": idWith('R=="B>0"),
            |          "C>0&!false": andR('R=="C>0&!false"); <(
            |            "C>0": idWith('R=="C>0"),
            |            "!false": notR('R=="!false"); close
            |          )
            |        )
            |      )
            |    ),
            |    "[{x:=x+B;}*](x>=0&A>0&B>0&C>0&!false->[x:=x+B;](x>=0&A>0&B>0&C>0&!false))":
            |      cohide('R=="[{x:=x+B;}*](x>=0&A>0&B>0&C>0&!false->[x:=x+B;](x>=0&A>0&B>0&C>0&!false))");
            |      Goedel;
            |      implyR('R=="x>=0&A>0&B>0&C>0&!false->[x:=x+B;](x>=0&A>0&B>0&C>0&!false)");
            |      boxAnd('R=="[x:=x+B;](x>=0&A>0&B>0&C>0&!false)");
            |      andR('R=="[x:=x+B;]x>=0&[x:=x+B;](A>0&B>0&C>0&!false)"); <(
            |        "[x:=x+B;]x>=0":
            |          andL('Llast);
            |          andL('Llast);
            |          andL('Llast);
            |          andL('Llast);
            |          hideL('Llast);
            |          label("Step");
            |          todo,
            |        "[x:=x+B;](A>0&B>0&C>0&!false)":
            |          andL('L=="x>=0&A>0&B>0&C>0&!false");
            |          hideL('L=="x>=0");
            |          V('R=="[x:=x+B;](A>0&B>0&C>0&!false)");
            |          closeId(-1,1)
            |      )
            |  ),
            |  cohide('R=="[{x:=x+B;}*](x>=0&A>0&B>0&C>0&!false)->[{x:=x+B;}*]x>=0");
            |  CMonCongruence(".1");
            |  implyR('R=="x>=0&A>0&B>0&C>0&!false->x>=0");
            |  andL('Llast);
            |  andL('Llast);
            |  andL('Llast);
            |  andL('Llast);
            |  hideL('Llast);
            |  label("Post");
            |  todo
            |)""".stripMargin
        ),
      )
      tl.prettyString shouldBe tr.prettyString
    }
  }

  it should "record id step" in withDatabase { db =>
    withMathematica { _ =>
      val p = "x>=0 -> x>=0".asFormula
      val ps = ProvableSig.startPlainProof(p)
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $p End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      val tac = implyR(1) & id
      interpreter(tac, BelleProvable.plain(ps))
      val tree = DbProofTree(db.db, proofId.toString)
      val tt = tree.tactic
      tree.openGoals shouldBe empty
      tt shouldBe tacticParser("implyR('R==\"x>=0->x>=0\"); id")
      proveBy(p, tree.tactic) shouldBe Symbol("proved")
    }
  }

  it should "close left-over branching with follow-up branches" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|x<y -> x>=0&x>=0&x>=0|x<y"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & orL(-1) & onAll(orR(1)) < (andR(1) < (id, andR(1)), id) & onAll(id),
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals shouldBe empty
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0|x < y->x>=0&x>=0&x>=0|x < y");
          |orL('L=="x>=0|x < y"); <(
          |  "x>=0":
          |    orR('R=="x>=0&x>=0&x>=0|x < y");
          |    andR('R=="x>=0&x>=0&x>=0"); <(
          |      "x>=0": id,
          |      "x>=0&x>=0": andR('R=="x>=0&x>=0"); <(
          |        "L//x>=0": id,
          |        "R//x>=0": id
          |      )
          |    ),
          |  "x < y": orR('R=="x>=0&x>=0&x>=0|x < y"); id
          |)""".stripMargin
      )
      proveBy(problem.asFormula, tree.tactic) shouldBe Symbol("proved")
    }
  }

  it should "close left-over branching with follow-up branches (2)" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|x<y -> x>=0&x>=0&x>=0|x<y"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & orL(-1) & onAll(orR(1)) < (andR(1) < (id, andR(1)), skip) & onAll(id),
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals shouldBe empty
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0|x < y->x>=0&x>=0&x>=0|x < y");
          |orL('L=="x>=0|x < y"); <(
          |  "x>=0":
          |    orR('R=="x>=0&x>=0&x>=0|x < y");
          |    andR('R=="x>=0&x>=0&x>=0"); <(
          |      "x>=0": id,
          |      "x>=0&x>=0": andR('R=="x>=0&x>=0"); <(
          |        "L//x>=0": id,
          |        "R//x>=0": id
          |      )
          |    ),
          |  "x < y":
          |    orR('R=="x>=0&x>=0&x>=0|x < y");
          |    id
          |)""".stripMargin
      )
      proveBy(problem.asFormula, tree.tactic) shouldBe Symbol("proved")
    }
  }

  it should "close left-over branching with follow-up branches (3)" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|x<y -> x>=0&x>=0&x>=0|x<y"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & orL(-1) & onAll(orR(1)) < (andR(1) < (id, andR(1)), skip)
          < (skip, cut("x^2>=0".asFormula), skip) < (skip, skip, id, cohideR(Symbol("Rlast"))) < (skip, id, QE) & id,
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals shouldBe empty
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0|x < y->x>=0&x>=0&x>=0|x < y");
          |orL('L=="x>=0|x < y"); <(
          |  "x>=0":
          |    orR('R=="x>=0&x>=0&x>=0|x < y");
          |    andR('R=="x>=0&x>=0&x>=0"); <(
          |      "x>=0": id,
          |      "x>=0&x>=0":
          |        andR('R=="x>=0&x>=0"); <(
          |          "L//x>=0": id,
          |          "R//x>=0": id
          |        )
          |    ),
          |  "x < y":
          |    orR('R=="x>=0&x>=0&x>=0|x < y");
          |    cut("x^2>=0"); <(
          |      "Use": id,
          |      "Show": cohideR('Rlast); QE
          |    )
          |)""".stripMargin
      )
      proveBy(problem.asFormula, tree.tactic) shouldBe Symbol("proved")
    }
  }

  it should "combine substitutions" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "eq(x,1) -> eq(x,x) & p(x)"
      val defs = "one()~>1 :: eq(x,y)~>x=y :: sq(x)~>x^2 :: p(x)~>eq(x,sq(x)) :: nil".asDeclaration
      val modelContent =
        s"""ArchiveEntry "Test" Definitions Real one() = 1; Real sq(Real x)=x^2; Bool eq(Real x, Real y) <-> x=y; Bool p(Real x) <-> eq(x,sq(x)); End. ProgramVariables Real x, y; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db, constructGlobalProvable = false, defs = defs)
      val eq = Function("eq", None, Tuple(Real, Real), Bool)
      interpreter(
        implyR(1) & andR(1) < (
          cut("eq(x,one())".asFormula) < (
            QE, // Expand(eq, None) & Using(List("x=x".asFormula), SimplifierV3.fullSimplify) & closeT,
            QE
          ),
          QE // Expand(eq, None) & Expand(Function("one", None, Unit, Real), None) & QE
        ),
        BelleProvable.plain(ProvableSig.startProof(problem.asFormula, defs)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals shouldBe empty
      tree.isProved shouldBe true
    }
  }

  it should "combine substitutions (2)" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "eq(x,one()) -> eq(x,x) & p(x)"
      val defs = "one()~>1 :: eq(x,y)~>x=y :: sq(x)~>x^2 :: p(x)~>eq(x,sq(x)) :: nil".asDeclaration
      val modelContent =
        s"""ArchiveEntry "Test" Definitions Real one() = 1; Real sq(Real x)=x^2; Bool eq(Real x, Real y) <-> x=y; Bool p(Real x) <-> eq(x,sq(x)); End. ProgramVariables Real x, y; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db, constructGlobalProvable = false, defs = defs)
      val eq = Function("eq", None, Tuple(Real, Real), Bool)
      interpreter(
        implyR(1) & andR(1) < (
          cut("eq(x,1)".asFormula) < (
            expandFw(eq, None) & Using(List("x=x".asFormula), SimplifierV3.fullSimplify) & closeT,
            Using("eq(x,one()), eq(x,1)".asFormulaList, QE)
          ),
          expandFw(eq, None) & expandFw(Function("one", None, Unit, Real), None) & QE
        ),
        BelleProvable.plain(ProvableSig.startProof(problem.asFormula, defs)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals shouldBe empty
      tree.isProved shouldBe true
    }
  }

  "Saturation" should "record each iteration as step" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0&x>1&x>2 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & SaturateTactic(andL(Symbol("L"))),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 4
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
        None :: Some("implyR(1)") :: Some("andL('L)") :: Some("andL('L)") :: Nil
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
  }

  it should "not recurse on nil" in withMathematica { _ =>
    withDatabase { db =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>1 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        SaturateTactic(nil),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 2

      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("nil") :: Nil
      tree.root.conclusion shouldBe "==> x>0 -> x>1".asSequent
      tree.root.provable.subgoals.loneElement shouldBe "==> x>0 -> x>1".asSequent

      val n1 = tree.root.children.loneElement
      n1.makerShortName shouldBe Some("nil")
      n1.goal.value shouldBe "==> x>0 -> x>1".asSequent
    }
  }

  it should "recurse only on change" in withMathematica { _ =>
    withDatabase { db =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0 -> x>1 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        SaturateTactic(Idioms.?(QE)),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 3

      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("QE") :: Some("nil") :: Nil
      tree.root.conclusion shouldBe "==> x>0 -> x>1".asSequent
      tree.root.provable.subgoals should contain theSameElementsInOrderAs "==> false".asSequent :: Nil

      val n1 = tree.root.children.loneElement
      n1.makerShortName shouldBe Some("QE")
      n1.goal.value shouldBe "==> false".asSequent

      val n2 = n1.children.loneElement
      n2.makerShortName shouldBe Some("nil")
      n2.goal.value shouldBe "==> false".asSequent
    }
  }

  "Repeat" should "record each iteration as step" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0&x>1&x>2&x>3 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        implyR(1) & (andL(Symbol("L")) * 2),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 4
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs
        None :: Some("implyR(1)") :: Some("andL('L)") :: Some("andL('L)") :: Nil
      tree.root.conclusion shouldBe "==> x>0&x>1&x>2&x>3 -> x>0".asSequent
      tree.root.provable.subgoals should contain theSameElementsInOrderAs "x>0, x>1, x>2&x>3 ==> x>0".asSequent :: Nil
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
  }

  "Let" should "be recorded plain" in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = "ArchiveEntry \"Test\" ProgramVariables Real x; End. Problem x>0&x>1&x>2&x>3 -> x>0 End. End."
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        let("X()".asTerm, "x".asVariable, prop),
        BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))),
      )
      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 2
      tree.nodes.map(_.makerShortName) should contain theSameElementsInOrderAs None :: Some("let(X()=x in prop)") :: Nil
    }
  }

  "Listeners" should "not be informed when doing auxiliary inner proofs" in withMathematica { _ =>
    val mockListener = new IOListener() {
      var beginnings: List[(BelleValue, BelleExpr)] = Nil
      override def begin(input: BelleValue, expr: BelleExpr): Unit = beginnings = beginnings :+ (input -> expr)
      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
      override def kill(): Unit = {}
    }
    val mockListenerFactory: Int => (String, Int, Int) => scala.collection.immutable.Seq[IOListener] =
      (_: Int) => (_: String, _: Int, _: Int) => mockListener :: Nil

    val interpreter = SpoonFeedingInterpreter(
      1,
      -1,
      (_: ProvableSig) => 1,
      Declaration(Map.empty),
      mockListenerFactory,
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
      0,
      strict = false,
      convertPending = true,
      recordInternal = false,
    )
    BelleInterpreter.setInterpreter(interpreter)
    BelleInterpreter(
      implyR(1) & dC("x>0".asFormula)(1, 1 :: Nil),
      BelleProvable.plain(ProvableSig.startPlainProof("y>0 -> [x:=3;][{x'=4}]x>0".asFormula)),
    )
    // @note auxiliary inner proofs started by UnifyUSCalculus ruin database trace if reported to listeners
    mockListener.beginnings shouldNot contain(
      BelleProvable.plain(ProvableSig.startPlainProof("[{x'=4}]x>0".asFormula)) -> (QE & done)
    )
    mockListener.beginnings shouldNot contain(
      BelleProvable.plain(ProvableSig.startPlainProof("(p_()<->q_())&q_()->p_()<->true".asFormula)) -> prop
    )
    // @note should also not contain the following, but not testable without huge effort since closeTrue is private and so is ProofRuleTactics
    // mockListener.beginnings shouldNot contain (BelleProvable(ProvableSig.startProof("[a{|^@|};]true <-> true".asFormula)) -> (equivR(1) <(closeTrue(SuccPos(1)), cohideR(1) & byUS("[]T system"))))
  }

  "Parsed tactic" should "record STTT tutorial example 1 steps" taggedAs SlowTest in withDatabase { db =>
    withMathematica { _ =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 1",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)

      val tacticText = """implyR('R) & andL('L) & dC("v>=0", 1) & <(dW(1) & prop, dI(1))"""
      val tactic = tacticParser(tacticText)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val extractedTactic = db.extractTactic(proofId)
      extractedTactic shouldBe tacticParser(
        """implyR('R=="v>=0&A()>0->[{x'=v,v'=A()}]v>=0");
          |andL('L=="v>=0&A()>0");
          |dC("v>=0", 'R=="[{x'=v,v'=A()}]v>=0"); <(
          |  "Use": dW('R=="[{x'=v,v'=A()&true&v>=0}]v>=0"); prop,
          |  "Show": dI('R=="[{x'=v,v'=A()}]v>=0")
          |)""".stripMargin
      )
    }
  }

  it should "record STTT tutorial example 2 steps" taggedAs SlowTest in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 2",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
      val modelContent = entry.fileContent
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)

      val tactic = entry.tactics.head._3
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val extractedTactic = db.extractTactic(proofId)
      extractedTactic shouldBe tacticParser(
        """implyR('R=="v>=0&A()>0&B()>0->[{{a:=A();++a:=0;++a:=-B();}{x'=v,v'=a&v>=0}}*]v>=0");
          |andL('L=="v>=0&A()>0&B()>0");
          |andL('L=="A()>0&B()>0");
          |loop("v>=0", 'R=="[{{a:=A();++a:=0;++a:=-B();}{x'=v,v'=a&v>=0}}*]v>=0"); <(
          |  "Init": QE,
          |  "Post": QE,
          |  "Step":
          |    composeb('R=="[{a:=A();++a:=0;++a:=-B();}{x'=v,v'=a&v>=0}]v>=0");
          |    choiceb('R=="[a:=A();++a:=0;++a:=-B();][{x'=v,v'=a&v>=0}]v>=0");
          |    andR('R=="[a:=A();][{x'=v,v'=a&v>=0}]v>=0&[a:=0;++a:=-B();][{x'=v,v'=a&v>=0}]v>=0"); <(
          |      "[a:=A();][{x'=v,v'=a&v>=0}]v>=0":
          |        assignb('R=="[a:=A();][{x'=v,v'=a&v>=0}]v>=0");
          |        ODE('R=="[{x'=v,v'=A()&v>=0}]v>=0"),
          |      "[a:=0;++a:=-B();][{x'=v,v'=a&v>=0}]v>=0":
          |        choiceb('R=="[a:=0;++a:=-B();][{x'=v,v'=a&v>=0}]v>=0");
          |        andR('R=="[a:=0;][{x'=v,v'=a&v>=0}]v>=0&[a:=-B();][{x'=v,v'=a&v>=0}]v>=0"); <(
          |          "[a:=0;][{x'=v,v'=a&v>=0}]v>=0":
          |            assignb('R=="[a:=0;][{x'=v,v'=a&v>=0}]v>=0");
          |            ODE('R=="[{x'=v,v'=0&v>=0}]v>=0"),
          |          "[a:=-B();][{x'=v,v'=a&v>=0}]v>=0":
          |            assignb('R=="[a:=-B();][{x'=v,v'=a&v>=0}]v>=0");
          |            ODE('R=="[{x'=v,v'=-B()&v>=0}]v>=0")
          |        )
          |    )
          |)""".stripMargin
      )
    }
  }

  it should "record STTT tutorial example 3a steps" taggedAs SlowTest in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 3a",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
      val modelContent = entry.fileContent
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)

      val tactic = entry.tactics.head._3
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="v>=0&A()>0&B()>0&x+v^2/(2*B()) < S()->[{{?x+v^2/(2*B()) < S();a:=A();++?v=0;a:=0;++a:=-B();}{{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}}}*]x<=S()");
          |andL('L=="v>=0&A()>0&B()>0&x+v^2/(2*B()) < S()");
          |andL('L=="A()>0&B()>0&x+v^2/(2*B()) < S()");
          |andL('L=="B()>0&x+v^2/(2*B()) < S()");
          |loop("v>=0&x+v^2/(2*B())<=S()", 'R=="[{{?x+v^2/(2*B()) < S();a:=A();++?v=0;a:=0;++a:=-B();}{{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}}}*]x<=S()"); <(
          |  "Init": QE,
          |  "Post": QE,
          |  "Step":
          |    composeb('R=="[{?x+v^2/(2*B()) < S();a:=A();++?v=0;a:=0;++a:=-B();}{{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}}](v>=0&x+v^2/(2*B())<=S())");
          |    choiceb('R=="[?x+v^2/(2*B()) < S();a:=A();++?v=0;a:=0;++a:=-B();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |    andR('R=="[?x+v^2/(2*B()) < S();a:=A();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())&[?v=0;a:=0;++a:=-B();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())"); <(
          |      "[?x+v^2/(2*B()) < S();a:=A();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())":
          |        composeb('R=="[?x+v^2/(2*B()) < S();a:=A();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |        testb('R=="[?x+v^2/(2*B()) < S();][a:=A();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |        implyR('R=="x+v^2/(2*B()) < S()->[a:=A();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |        assignb('R=="[a:=A();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |        choiceb('R=="[{x'=v,v'=A()&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=A()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |        andR('R=="[{x'=v,v'=A()&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())&[{x'=v,v'=A()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())"); <(
          |          "[{x'=v,v'=A()&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())":
          |            ODE('R=="[{x'=v,v'=A()&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())"),
          |          "[{x'=v,v'=A()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())":
          |            ODE('R=="[{x'=v,v'=A()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())")
          |        ),
          |      "[?v=0;a:=0;++a:=-B();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())":
          |        choiceb('R=="[?v=0;a:=0;++a:=-B();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |        andR('R=="[?v=0;a:=0;][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())&[a:=-B();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())"); <(
          |          "[?v=0;a:=0;][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())":
          |            composeb('R=="[?v=0;a:=0;][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |            testb('R=="[?v=0;][a:=0;][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |            implyR('R=="v=0->[a:=0;][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |            assignb('R=="[a:=0;][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |            choiceb('R=="[{x'=v,v'=0&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=0&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |            andR('R=="[{x'=v,v'=0&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())&[{x'=v,v'=0&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())"); <(
          |              "[{x'=v,v'=0&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())":
          |                ODE('R=="[{x'=v,v'=0&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())"),
          |              "[{x'=v,v'=0&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())":
          |                ODE('R=="[{x'=v,v'=0&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())")
          |            ),
          |          "[a:=-B();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())":
          |            assignb('R=="[a:=-B();][{x'=v,v'=a&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=a&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |            choiceb('R=="[{x'=v,v'=-B()&v>=0&x+v^2/(2*B())<=S()}++{x'=v,v'=-B()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())");
          |            andR('R=="[{x'=v,v'=-B()&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())&[{x'=v,v'=-B()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())"); <(
          |              "[{x'=v,v'=-B()&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())":
          |                ODE('R=="[{x'=v,v'=-B()&v>=0&x+v^2/(2*B())<=S()}](v>=0&x+v^2/(2*B())<=S())"),
          |              "[{x'=v,v'=-B()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())":
          |                ODE('R=="[{x'=v,v'=-B()&v>=0&x+v^2/(2*B())>=S()}](v>=0&x+v^2/(2*B())<=S())")
          |            )
          |        )
          |     )
          |)""".stripMargin
      )
    }
  }

  it should "record STTT tutorial example 4a steps" taggedAs SlowTest in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 4a",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
      val modelContent = entry.fileContent
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)

      val tactic = entry.tactics.head._3
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="v<=V()&A()>0->[{{?v=V();a:=0;++?v!=V();a:=A();}{x'=v,v'=a&v<=V()}}*]v<=V()");
          |andL('L=="v<=V()&A()>0");
          |loop("v<=V()", 'R=="[{{?v=V();a:=0;++?v!=V();a:=A();}{x'=v,v'=a&v<=V()}}*]v<=V()"); <(
          |  "Init": QE,
          |  "Post": QE,
          |  "Step":
          |    composeb('R=="[{?v=V();a:=0;++?v!=V();a:=A();}{x'=v,v'=a&v<=V()}]v<=V()");
          |    choiceb('R=="[?v=V();a:=0;++?v!=V();a:=A();][{x'=v,v'=a&v<=V()}]v<=V()");
          |    andR('R=="[?v=V();a:=0;][{x'=v,v'=a&v<=V()}]v<=V()&[?v!=V();a:=A();][{x'=v,v'=a&v<=V()}]v<=V()"); <(
          |      "[?v=V();a:=0;][{x'=v,v'=a&v<=V()}]v<=V()":
          |        composeb('R=="[?v=V();a:=0;][{x'=v,v'=a&v<=V()}]v<=V()");
          |        testb('R=="[?v=V();][a:=0;][{x'=v,v'=a&v<=V()}]v<=V()");
          |        implyR('R=="v=V()->[a:=0;][{x'=v,v'=a&v<=V()}]v<=V()");
          |        assignb('R=="[a:=0;][{x'=v,v'=a&v<=V()}]v<=V()");
          |        ODE('R=="[{x'=v,v'=0&v<=V()}]v<=V()"),
          |      "[?v!=V();a:=A();][{x'=v,v'=a&v<=V()}]v<=V()":
          |        composeb('R=="[?v!=V();a:=A();][{x'=v,v'=a&v<=V()}]v<=V()");
          |        testb('R=="[?v!=V();][a:=A();][{x'=v,v'=a&v<=V()}]v<=V()");
          |        implyR('R=="v!=V()->[a:=A();][{x'=v,v'=a&v<=V()}]v<=V()");
          |        assignb('R=="[a:=A();][{x'=v,v'=a&v<=V()}]v<=V()");
          |        ODE('R=="[{x'=v,v'=A()&v<=V()}]v<=V()")
          |    )
          |)""".stripMargin
      )
    }
  }

  it should "record STTT tutorial example 4b steps" taggedAs SlowTest in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 4b",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
      val modelContent = entry.fileContent
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)

      val tactic = entry.tactics.head._3
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes should have size 11
      tree.nodes.head.makerShortName shouldBe None
      tree.nodes.tail.map(_.makerShortName.value) should contain theSameElementsInOrderAs "implyR(1)" :: "andL('L)" ::
        """loop("v<=V()", 1)""" :: """loop("v<=V()", 1)""" :: """loop("v<=V()", 1)""" ::
        "composeb(1)" :: "assignb(1)" :: "ODE(1)" :: "QE" :: "QE" :: Nil
      tree.tactic shouldBe tacticParser(
        """implyR('R=="v<=V()&A()>0->[{a:=A();{x'=v,v'=a&v<=V()}}*]v<=V()");
          |andL('L=="v<=V()&A()>0");
          |loop("v<=V()", 'R=="[{a:=A();{x'=v,v'=a&v<=V()}}*]v<=V()"); <(
          |  "Init": QE,
          |  "Post": QE,
          |  "Step":
          |    composeb('R=="[a:=A();{x'=v,v'=a&v<=V()}]v<=V()");
          |    assignb('R=="[a:=A();][{x'=v,v'=a&v<=V()}]v<=V()");
          |    ODE('R=="[{x'=v,v'=A()&v<=V()}]v<=V()")
          |)""".stripMargin
      )
    }
  }

  it should "record STTT tutorial example 9b steps" taggedAs SlowTest in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 9b",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
      val modelContent = entry.fileContent
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)

      val tactic = entry.tactics.head._3
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db.db)))
      tree.tactic shouldBe tacticParser(
        """implyR('R=="v>=0&xm<=x&x<=S()&xr=(xm+S())/2&Kp()=2&Kd()=3&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2->[{{xm:=x;xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;++?true;}{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}}*]x<=S()");
          |andL('L=="v>=0&xm<=x&x<=S()&xr=(xm+S())/2&Kp()=2&Kd()=3&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |andL('L=="xm<=x&x<=S()&xr=(xm+S())/2&Kp()=2&Kd()=3&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |andL('L=="x<=S()&xr=(xm+S())/2&Kp()=2&Kd()=3&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |andL('L=="xr=(xm+S())/2&Kp()=2&Kd()=3&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |andL('L=="Kp()=2&Kd()=3&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |andL('L=="Kd()=3&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |loop("v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2", 'R=="[{{xm:=x;xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;++?true;}{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}}*]x<=S()"); <(
          |  "Init": QE,
          |  "Post": QE,
          |  "Step":
          |    andL('L=="v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |    andL('L=="xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |    andL('L=="xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2");
          |    composeb('R=="[{xm:=x;xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;++?true;}{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |    choiceb('R=="[xm:=x;xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;++?true;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |    andR('R=="[xm:=x;xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)&[?true;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)"); <(
          |      "[xm:=x;xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)":
          |        composeb('R=="[xm:=x;xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |        assignb('R=="[xm:=x;][xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |        composeb('R=="[xr:=(xm+S())/2;?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |        assignb('R=="[xr:=(xm+S())/2;][?5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |        testb('R=="[?5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2;][{x'=v,v'=-Kp()*(x-(xm+S())/2)-Kd()*v&v>=0}](v>=0&xm<=x&(xm+S())/2=(xm+S())/2&5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |        implyR('R=="5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2->[{x'=v,v'=-Kp()*(x-(xm+S())/2)-Kd()*v&v>=0}](v>=0&xm<=x&(xm+S())/2=(xm+S())/2&5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |        dC("xm<=x", 'R=="[{x'=v,v'=-Kp()*(x-(xm+S())/2)-Kd()*v&v>=0}](v>=0&xm<=x&(xm+S())/2=(xm+S())/2&5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2)"); <(
          |          "Use":
          |            dC("5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2", 'R=="[{x'=v,v'=-Kp()*(x-(xm+S())/2)-Kd()*v&v>=0&xm<=x}](v>=0&xm<=x&(xm+S())/2=(xm+S())/2&5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2)"); <(
          |              "Use":
          |                dW('R=="[{x'=v,v'=-Kp()*(x-(xm+S())/2)-Kd()*v&(v>=0&xm<=x)&5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2}](v>=0&xm<=x&(xm+S())/2=(xm+S())/2&5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |                QE,
          |              "Show":
          |                dI('R=="[{x'=v,v'=-Kp()*(x-(xm+S())/2)-Kd()*v&v>=0&xm<=x}]5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2")
          |            ),
          |          "Show":
          |            dI('R=="[{x'=v,v'=-Kp()*(x-(xm+S())/2)-Kd()*v&v>=0}]xm<=x")
          |        ),
          |      "[?true;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)":
          |        testb('R=="[?true;][{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |        implyR('R=="true->[{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |        dC("xm<=x", 'R=="[{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)"); <(
          |          "Use":
          |            dC("5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2", 'R=="[{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0&xm<=x}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)"); <(
          |              "Use":
          |                dW('R=="[{x'=v,v'=-Kp()*(x-xr)-Kd()*v&(v>=0&xm<=x)&5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2}](v>=0&xm<=x&xr=(xm+S())/2&5/4*(x-xr)^2+(x-xr)*v/2+v^2/4 < ((S()-xm)/2)^2)");
          |                QE,
          |              "Show":
          |                dI('R=="[{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0&xm<=x}]5/4*(x-(xm+S())/2)^2+(x-(xm+S())/2)*v/2+v^2/4 < ((S()-xm)/2)^2")
          |            ),
          |          "Show":
          |            dI('R=="[{x'=v,v'=-Kp()*(x-xr)-Kd()*v&v>=0}]xm<=x")
          |        )
          |     )
          |)""".stripMargin
      )
    }
  }

  it should "record STTT tutorial example 10 steps" taggedAs SlowTest ignore withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 10",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
      val modelContent = entry.fileContent
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)

      val tactic = entry.tactics.head._3
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(modelContent))))

      // db.extractTactic(proofId) shouldBe tactic //@note not exactly the same, because repetitions are unrolled etc.
      val tree = DbProofTree(db.db, proofId.toString)
      tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db.db)))
      tree.tactic shouldBe tacticParser(
        """implyR('R=="v>=0&A()>0&B()>=b()&b()>0&ep()>0&lw()>0&y=ly()&r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()->[{{?abs(y-ly())+v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < lw();a:=*;?-B()<=a&a<=A();w:=*;r:=*;?r!=0&w*r=v;++?v=0;a:=0;w:=0;++a:=*;?-B()<=a&a<=-b();}c:=0;{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}}*]abs(y-ly()) < lw()");
          |andL('L=="v>=0&A()>0&B()>=b()&b()>0&ep()>0&lw()>0&y=ly()&r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |andL('L=="A()>0&B()>=b()&b()>0&ep()>0&lw()>0&y=ly()&r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |andL('L=="B()>=b()&b()>0&ep()>0&lw()>0&y=ly()&r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |andL('L=="b()>0&ep()>0&lw()>0&y=ly()&r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |andL('L=="ep()>0&lw()>0&y=ly()&r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |andL('L=="lw()>0&y=ly()&r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |andL('L=="y=ly()&r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |andL('L=="r!=0&dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |andL('L=="dx^2+dy^2=1&abs(y-ly())+v^2/(2*b()) < lw()");
          |loop("v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw()", 'R=="[{{?abs(y-ly())+v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < lw();a:=*;?-B()<=a&a<=A();w:=*;r:=*;?r!=0&w*r=v;++?v=0;a:=0;w:=0;++a:=*;?-B()<=a&a<=-b();}c:=0;{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}}*]abs(y-ly()) < lw()"); <(
          |  "Init": QE,
          |  "Post": QE,
          |  "Step":
          |    chase('R=="[{?abs(y-ly())+v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < lw();a:=*;?-B()<=a&a<=A();w:=*;r:=*;?r!=0&w*r=v;++?v=0;a:=0;w:=0;++a:=*;?-B()<=a&a<=-b();}c:=0;{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())");
          |    normalize; <(
          |      "abs(y-ly())+v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < lw()->\forall a (-B()<=a&a<=A()->\forall w \forall r (r!=0&w*r=v->\forall c (c=0->[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw()))))":
          |        hideL('L=="abs(y-ly())+v^2/(2*b()) < lw()");
          |        dC("c>=0", 'R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |          "Use":
          |            dC("dx^2+dy^2=1", 'R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&(v>=0&c<=ep())&c>=0}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |              "Use":
          |                dC("v=old(v)+a*c", 'R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |                  "Use":
          |                    dC("-c*(v-a/2*c)<=y-old(y)&y-old(y)<=c*(v-a/2*c)", 'R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&(((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |                      "Use":
          |                        dW('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&((((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c)&-c*(v-a/2*c)<=y-y_0&y-y_0<=c*(v-a/2*c)}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())");
          |                        andL('L=="(((((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c)&-c*(v-a/2*c)<=y-y_0&y-y_0<=c*(v-a/2*c))&A()>0&B()>=b()&b()>0&ep()>0&lw()>0&abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()&v_0>=0&-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="((((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c)&-c*(v-a/2*c)<=y-y_0&y-y_0<=c*(v-a/2*c)");
          |                        andL('L=="A()>0&B()>=b()&b()>0&ep()>0&lw()>0&abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()&v_0>=0&-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="(((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c");
          |                        andL('L=="-c*(v-a/2*c)<=y-y_0&y-y_0<=c*(v-a/2*c)");
          |                        andL('L=="B()>=b()&b()>0&ep()>0&lw()>0&abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()&v_0>=0&-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1");
          |                        andL('L=="b()>0&ep()>0&lw()>0&abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()&v_0>=0&-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="(v>=0&c<=ep())&c>=0");
          |                        andL('L=="ep()>0&lw()>0&abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()&v_0>=0&-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="v>=0&c<=ep()");
          |                        andL('L=="lw()>0&abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()&v_0>=0&-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()&v_0>=0&-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="v_0>=0&-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="-B()<=a&a<=A()&r!=0&r_0!=0");
          |                        andL('L=="a<=A()&r!=0&r_0!=0");
          |                        andL('L=="r!=0&r_0!=0");
          |                        transformEquality("ep()=c", 'L=="abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()");
          |                        prop;
          |                        smartQE,
          |                      "Show":
          |                        dI('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&(((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c}](-c*(v-a/2*c)<=y-y_0&y-y_0<=c*(v-a/2*c))")
          |                    ),
          |                  "Show":
          |                    dI('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1}]v=v_0+a*c")
          |                ),
          |              "Show":
          |                dI('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&(v>=0&c<=ep())&c>=0}]dx^2+dy^2=1")
          |            ),
          |          "Show":
          |            dI('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}]c>=0")
          |        ),
          |      "v=0->\forall w (w=0->\forall c (c=0->[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())))":
          |        dC("c>=0", 'R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |          "Use":
          |            dC("dx^2+dy^2=1", 'R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&(v>=0&c<=ep())&c>=0}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |              "Use":
          |                dC("v=old(v)", 'R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |                  "Use":
          |                    dC("-c*v<=y-old(y)&y-old(y)<=c*v", 'R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&(((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |                      "Use":
          |                        dW('R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&((((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0)&-c*v<=y-y_0&y-y_0<=c*v}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())");
          |                        prop;
          |                        smartQE,
          |                      "Show":
          |                        dI('R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&(((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0}](-c*v<=y-y_0&y-y_0<=c*v)")
          |                    ),
          |                  "Show":
          |                    dI('R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1}]v=v_0")
          |                ),
          |              "Show":
          |                dI('R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&(v>=0&c<=ep())&c>=0}]dx^2+dy^2=1")
          |            ),
          |          "Show":
          |            dI('R=="[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&v>=0&c<=ep()}]c>=0")
          |        ),
          |      "\forall a (-B()<=a&a<=-b()->\forall c (c=0->[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())))":
          |        dC("c>=0", 'R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |          "Use":
          |            dC("dx^2+dy^2=1", 'R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&(v>=0&c<=ep())&c>=0}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |              "Use":
          |                dC("v=old(v)+a*c", 'R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |                  "Use":
          |                    dC("-c*(v-a/2*c)<=y-old(y)&y-old(y)<=c*(v-a/2*c)", 'R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&(((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())"); <(
          |                      "Use":
          |                        dW('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&((((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c)&-c*(v-a/2*c)<=y-y_0&y-y_0<=c*(v-a/2*c)}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())");
          |                        prop;
          |                        smartQE,
          |                      "Show":
          |                        dI('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&(((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1)&v=v_0+a*c}](-c*(v-a/2*c)<=y-y_0&y-y_0<=c*(v-a/2*c))")
          |                    ),
          |                  "Show":
          |                    dI('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&((v>=0&c<=ep())&c>=0)&dx^2+dy^2=1}]v=v_0+a*c")
          |                ),
          |              "Show":
          |                dI('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&(v>=0&c<=ep())&c>=0}]dx^2+dy^2=1")
          |            ),
          |          "Show":
          |            dI('R=="[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}]c>=0")
          |        )
          |    )
          |)""".stripMargin
      )
    }
  }

  it should "work for branching tactic that results in a sole open goal" in withMathematica { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      val tactic = tacticParser("""implyR(1); dC("x>=old(x)", 1); <(nil, dI(1))""")
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1}]x>=0");
          |dC("x>=old(x)", 'R=="[{x'=1}]x>=0"); <(
          |  "Use": todo,
          |  "Show": dI('R=="[{x'=1}]x>=x_0")
          |)""".stripMargin
      )
    }
  }

  it should "work for branching tactic when following sole open goal" in withMathematica { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      val tactic = tacticParser("""implyR(1); dC("x>=old(x)", 1); <(nil, dI(1)); dW(1); QE""")
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1}]x>=0");
          |dC("x>=old(x)", 'R=="[{x'=1}]x>=0"); <(
          |  "Use":
          |    dW('R=="[{x'=1&true&x>=x_0}]x>=0");
          |    QE,
          |  "Show": dI('R=="[{x'=1}]x>=x_0")
          |)""".stripMargin
      )
    }
  }

  it should "work for branching tactic when continuing on sole open goal" in withMathematica { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      val tactic = tacticParser("""implyR(1); dC("x>=old(x)", 1); <(dW(1), dI(1)); QE""")
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1}]x>=0");
          |dC("x>=old(x)", 'R=="[{x'=1}]x>=0"); <(
          |  "Use": dW('R=="[{x'=1&true&x>=x_0}]x>=0"); QE,
          |  "Show": dI('R=="[{x'=1}]x>=x_0")
          |)""".stripMargin
      )
    }
  }

  it should "work for branching tactic when continuing on sole open goal of a nested branching tactic" in withMathematica {
    _ =>
      withDatabase { db =>
        val problem = "x>=0 -> [{x'=1}]x>=0"
        val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
        val proofId = db.createProof(modelContent)

        val interpreter = createInterpreter(proofId, db.db)
        val tactic =
          tacticParser("""implyR(1); dC("x>=old(x)", 1); <(cut("0<=1"); <(dW(1), cohideR(2); QE), dI(1)); QE""")
        interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

        val tree = DbProofTree(db.db, proofId.toString)
        tree.tactic shouldBe tacticParser(
          """implyR('R=="x>=0->[{x'=1}]x>=0");
            |dC("x>=old(x)", 'R=="[{x'=1}]x>=0"); <(
            |  "Use":
            |    cut("0<=1"); <(
            |      "Use": dW('R=="[{x'=1&true&x>=x_0}]x>=0"); QE,
            |      "Show": cohideR('R=="0<=1"); QE
            |    ),
            |  "Show": dI('R=="[{x'=1}]x>=x_0")
            |)""".stripMargin
        )
      }
  }

  it should "work for branching tactic when following sole second open goal" in withMathematica { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      val tactic = tacticParser("""implyR(1); dC("x>=old(x)", 1); <(dW(1); QE, nil); dI(1)""")
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1}]x>=0");
          |dC("x>=old(x)", 'R=="[{x'=1}]x>=0"); <(
          |  "Use": dW('R=="[{x'=1&true&x>=x_0}]x>=0"); QE,
          |  "Show": dI('R=="[{x'=1}]x>=x_0")
          |)""".stripMargin
      )
    }
  }

  it should "work for branching tactic when following sole middle open goal" in withMathematica { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x:=x+1;}*]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)

      val interpreter = createInterpreter(proofId, db.db)
      val tactic = tacticParser("""implyR(1); loop("x>=0", 1); <(QE, nil, master); QE""")
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.nodes
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x:=x+1;}*]x>=0");
          |loop("x>=0", 'R=="[{x:=x+1;}*]x>=0"); <(
          |  "Init": QE,
          |  "Post": QE,
          |  "Step": master
          |)""".stripMargin
      )
    }
  }

  "Continuing a proof" should "work for atomic tactic" in withMathematica { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)

      val tree = DbProofTree(db.db, proofId.toString)
      tree.locate("()") match {
        case Some(n) => n.runTactic(
            db.user.userName,
            ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
            implyR(1),
            "implyR(1)",
            wait = true,
          )
      }

      tree.locate("(1,0)") match {
        case Some(n) =>
          val startStepIndex =
            n.id match { case DbStepPathNodeId(id, _) => db.db.getExecutionSteps(proofId).indexWhere(_.stepId == id) }
          val interpreter = registerInterpreter(SpoonFeedingInterpreter(
            proofId,
            startStepIndex,
            db.db.createProof,
            Declaration(Map.empty),
            listener(db.db, constructGlobalProvable = true),
            ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
            0,
            strict = false,
            convertPending = true,
            recordInternal = false,
          ))
          val tactic = tacticParser("""dC("x>=old(x)", 1)""")
          n.stepTactic(db.user.userName, interpreter, tactic, wait = true)
      }

      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1}]x>=0");
          |dC("x>=old(x)", 'R=="[{x'=1}]x>=0"); <(
          |  "Use": todo,
          |  "Show": todo
          |)""".stripMargin
      )
    }
  }

  "Revealing internal steps" should "work for diffInvariant" in withMathematica { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = true,
        recordInternal = true,
      ))
      interpreter(
        implyR(Symbol("R")) & diffInvariant("x>=old(x)".asFormula)(1),
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1}]x>=0");
          |dC("x>=old(x)", 'R=="[{x'=1}]x>=0"); <(
          |  "Use": todo,
          |  "Show": dI('R=="[{x'=1}]x>=x_0")
          |)""".stripMargin
      )
    }
  }

  it should "work for multiple levels of diffInvariant without let" in withZ3 { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        2,
        strict = true,
        convertPending = false,
        recordInternal = true,
      ))
      val fml = problem.asFormula
      val tactic = implyR(Symbol("R")) & diffInvariant("x>=0".asFormula)(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(fml)))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1}]x>=0");
          |DC("x>=0", 'R=="[{x'=1}]x>=0"); <(
          |  "Use": todo,
          |  "Show":
          |    DI('R=="[{x'=1}]x>=0");
          |    implyR('R=="true->x>=0&[{x'=1}](x>=0)'");
          |    andR('Rlast); <(
          |      "x>=0": QE,
          |      "[{x'=1}](x>=0)'":
          |        derive('Rlast.1);
          |        DE('Rlast);
          |        Dassignb('Rlast.1);
          |        GV('Rlast);
          |        QE
          |    )
          |)""".stripMargin
      )
      proveBy(fml, tree.tactic) shouldBe proveBy(fml, tactic)
    }
  }

  it should "FEATURE_REQUEST: work for multiple levels of diffInvariant" taggedAs TodoTest in withZ3 { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        2,
        strict = true,
        convertPending = true,
        recordInternal = true,
      ))
      val fml = problem.asFormula
      val tactic = implyR(Symbol("R")) & diffInvariant("x>=old(x)".asFormula)(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(fml)))

      // @todo let does not serialize
      val extractedTactic = db.extractTactic(proofId)
      extractedTactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1}]x>=0");
          |discreteGhost("x","x_0", 'R=="[{x'=1}]x>=0");
          |DC("x>=x_0", 'Rlast); <(
          |  "Use": todo,
          |  /* let x_0=x_0() in */
          |  "Show":
          |    DI(1) ; implyR(1) ; andR('Rlast) ; <(
          |      QE,
          |      derive('Rlast.1) ; DE('Rlast) ; Dassignb('Rlast.1) ; GV('Rlast) ; QE
          |    )
          |)""".stripMargin
      )
      proveBy(fml, extractedTactic) shouldBe proveBy(fml, tactic)
    }
  }

  it should "work for simple diffWeaken" in withZ3 { _ =>
    withDatabase { db =>
      val problem = "x>=0 -> [{x'=1 & x>0}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = true,
        recordInternal = true,
      ))
      val fml = problem.asFormula
      val tactic = implyR(1) & dW(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(fml)))

      val tree = DbProofTree(db.db, proofId.toString)
      val trace = db.db.getExecutionTrace(proofId)
      trace.steps should have size 4
      trace.steps.head.rule shouldBe "implyR(1)"
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0->[{x'=1&x>0}]x>=0");
          |DW('R=="[{x'=1&x>0}]x>=0");
          |G('R=="[{x'=1&x>0}](x>0->x>=0)");
          |implyR('R=="x>0->x>=0");
          |todo""".stripMargin
      )
      proveBy(fml, tree.tactic).subgoals shouldBe proveBy(fml, tactic).subgoals
    }
  }

  it should "work for diffWeaken" in withZ3 { _ =>
    withDatabase { db =>
      val problem = "x>=0 & y>=0 & z>=0 -> [{x'=y+z & x>=0}]x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x, y, z; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = true,
        recordInternal = true,
      ))
      val fml = problem.asFormula
      val tactic = implyR(1) & SaturateTactic(andL(Symbol("Llast"))) & dW(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(fml)))

      val tree = DbProofTree(db.db, proofId.toString)
      val trace = db.db.getExecutionTrace(proofId)
      trace.steps.map(_.rule) should contain theSameElementsInOrderAs List(
        "implyR(1)",
        "andL('Llast)",
        "andL('Llast)",
        "dC(\"y>=0&z>=0\", 1)",
        "V('Rlast)",
        "prop",
        "skip",
        "DW(1)",
        "G(1)",
        "implyR('R==\"x>=0&y>=0&z>=0->x>=0\")",
      )

      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0&y>=0&z>=0->[{x'=y+z&x>=0}]x>=0");
          |andL('Llast);
          |andL('Llast);
          |dC("y>=0&z>=0", 'R=="[{x'=y+z&x>=0}]x>=0"); <(
          |  "Use":
          |    DW('R=="[{x'=y+z&x>=0&y>=0&z>=0}]x>=0");
          |    G('R=="[{x'=y+z&x>=0&y>=0&z>=0}](x>=0&y>=0&z>=0->x>=0)");
          |    implyR('R=="x>=0&y>=0&z>=0->x>=0");
          |    todo,
          |  "Show":
          |    V('Rlast);
          |    prop
          |)""".stripMargin
      )
      proveBy(fml, tree.tactic).subgoals shouldBe proveBy(fml, tactic).subgoals
    }
  }

  it should "work for Bouncing Ball diffWeaken" in withZ3 { _ =>
    withDatabase { db =>
      val problem =
        "2*g*x<=2*g*H-v_0^2 & x>=0 & g>0 & 1>=c & c>=0 & r>=0 & x=0 & v=-c*v_0 -> [{x'=v,v'=-g-r*v^2 & x>=0&v>=0}](2*g*x<=2*g*H-v^2 & x>=0)"
      val modelContent =
        s"""ArchiveEntry "Test" Definitions Real c, g, r, H; End. ProgramVariables Real x, v, v_0; End. Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = true,
        recordInternal = true,
      ))
      val fml = ArchiveParser.parseAsFormula(modelContent)
      val tactic = implyR(1) & SaturateTactic(andL(Symbol("Llast"))) & dW(1)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(fml)))

      val tree = DbProofTree(db.db, proofId.toString)
      val trace = db.db.getExecutionTrace(proofId)

      trace.steps.map(_.rule) should contain theSameElementsInOrderAs List(
        "implyR(1)",
        "andL('Llast)",
        "andL('Llast)",
        "andL('Llast)",
        "andL('Llast)",
        "andL('Llast)",
        "andL('Llast)",
        "andL('Llast)",
        "dC(\"g()>0&1>=c()&c()>=0&r()>=0\", 1)",
        "V('Rlast)",
        "prop",
        "skip",
        "DW(1)",
        "G(1)",
        "implyR('R==\"(x>=0&v>=0)&g()>0&1>=c()&c()>=0&r()>=0->2*g()*x<=2*g()*H()-v^2&x>=0\")",
      )
      tree.tactic shouldBe tacticParser(
        """implyR('R=="2*g()*x<=2*g()*H()-v_0^2&x>=0&g()>0&1>=c()&c()>=0&r()>=0&x=0&v=-c()*v_0->[{x'=v,v'=-g()-r()*v^2&x>=0&v>=0}](2*g()*x<=2*g()*H()-v^2&x>=0)");
          |andL('Llast);andL('Llast);andL('Llast);andL('Llast);andL('Llast);andL('Llast);andL('Llast);
          |dC("g()>0&1>=c()&c()>=0&r()>=0", 'R=="[{x'=v,v'=-g()-r()*v^2&x>=0&v>=0}](2*g()*x<=2*g()*H()-v^2&x>=0)"); <(
          |  "Use":
          |    DW('R=="[{x'=v,v'=-g()-r()*v^2&(x>=0&v>=0)&g()>0&1>=c()&c()>=0&r()>=0}](2*g()*x<=2*g()*H()-v^2&x>=0)");
          |    G('R=="[{x'=v,v'=-g()-r()*v^2&(x>=0&v>=0)&g()>0&1>=c()&c()>=0&r()>=0}]((x>=0&v>=0)&g()>0&1>=c()&c()>=0&r()>=0->2*g()*x<=2*g()*H()-v^2&x>=0)");
          |    implyR('R=="(x>=0&v>=0)&g()>0&1>=c()&c()>=0&r()>=0->2*g()*x<=2*g()*H()-v^2&x>=0");
          |    todo,
          |  "Show": V('Rlast); prop
          |)""".stripMargin
      )
      proveBy(fml, tree.tactic).subgoals shouldBe proveBy(fml, tactic).subgoals
    }
  }

  it should "FEATURE_REQUEST: work with assertions/print/debug on multi-subgoal provables" taggedAs TodoTest in withDatabase {
    db =>
      withMathematica { _ =>
        val problem = "x>=0|!x<0 -> x>=0"
        val modelContent =
          s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
        val proofId = db.createProof(modelContent, "proof1")
        val interpreter = createInterpreter(proofId, db.db)
        interpreter(
          implyR(1) & orL(-1) & DebuggingTactics.assertProvableSize(2) < (id, nil),
          BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
        )

        val tree = DbProofTree(db.db, proofId.toString)
        tree.tactic shouldBe tacticParser(
          """implyR('R=="x>=0|!x < 0->x>=0");
            |orL('L=="x>=0|!x < 0"); <(
            |  "x>=0": id,
            |  "!x < 0": todo
            |)""".stripMargin
        )

        val proofId2 = db.createProof(modelContent, "proof2")
        registerInterpreter(SpoonFeedingInterpreter(
          proofId2,
          -1,
          db.db.createProof,
          Declaration(Map.empty),
          listener(db.db, constructGlobalProvable = true),
          ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
          1,
          strict = false,
          convertPending = true,
          recordInternal = true,
        ))(prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

        DbProofTree(db.db, proofId2.toString).tactic shouldBe tacticParser(
          """implyR('R=="x>=0|!x < 0->x>=0");
            |orL('L=="x>=0|!x < 0"); <(
            |  "x>=0": id,
            |  "!x < 0": notL('L=="!x < 0"); todo
            |)""".stripMargin
        )
      }
  }

  it should "work for prop on a simple example" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0 -> x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent, "proof1")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = true,
        recordInternal = true,
      ))
      interpreter(prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      // @todo tactic extraction must be strict too (now removes nil)
      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser("alphaRule /*implyR('R==\"x>=0->x>=0\")*/; id")

      val proofId2 = db.createProof(modelContent, "proof2")
      registerInterpreter(SpoonFeedingInterpreter(
        proofId2,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        2,
        strict = false,
        convertPending = true,
        recordInternal = false,
      ))(prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      DbProofTree(db.db, proofId2.toString).tactic shouldBe tacticParser("alphaRule /*implyR('R==\"x>=0->x>=0\")*/; id")
    }
  }

  it should "work with onAll without branches" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0 -> x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent, "proof1")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = false,
        convertPending = true,
        recordInternal = true,
      ))
      interpreter(implyR(1) & id & onAll(nil), BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))
      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser("implyR('R==\"x>=0->x>=0\"); id")
    }
  }

  it should "work for master on a simple example" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0 -> x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent, "proof1")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        2,
        strict = false,
        convertPending = false,
        recordInternal = true,
      ))
      interpreter(master(), BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser("implyR('R==\"x>=0->x>=0\"); id")
    }
  }

  it should "FEATURE_REQUEST: work for prop on a left-branching example" taggedAs TodoTest in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|!x<y -> x>=0"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent, "proof1")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = false,
        recordInternal = true,
      ))
      interpreter(prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula))) match {
        case BelleProvable(p, l) =>
          p.subgoals should contain theSameElementsAs List("==> x>=0, x<y".asSequent)
          l.value should contain theSameElementsAs List("!x<y".asFormula.prettyString.asLabel)
      }

      val tree = DbProofTree(db.db, proofId.toString)
      tree.tactic shouldBe tacticParser(
        """implyR('R=="x>=0|!x < y->x>=0");
          |orL('L=="x>=0|!x < y"); <(
          |  "x>=0": id,
          |  "!x < y": notL('L=="!x < y"); todo
          |)""".stripMargin
      )

      val proofId2 = db.createProof(modelContent, "proof2")
      registerInterpreter(SpoonFeedingInterpreter(
        proofId2,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = true,
        convertPending = false,
        recordInternal = true,
      ))(prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))
      DbProofTree(db.db, proofId2.toString).tactic shouldBe tacticParser(
        """implyR('R=="x>=0|!x < y->x>=0");
          |orL('L=="x>=0|!x < y"); <(
          |  "x>=0": id,
          |  "!x < y": notL('L=="!x < y"); todo
          |)""".stripMargin
      )
    }
  }

  it should "FEATURE_REQUEST: work for prop on a left-branching example with depth 2" taggedAs TodoTest in withDatabase {
    db =>
      withMathematica { _ =>
        val problem = "x>=0|!x<y -> x>=0"
        val modelContent =
          s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
        val proofId = db.createProof(modelContent, "proof1")
        val interpreter = registerInterpreter(SpoonFeedingInterpreter(
          proofId,
          -1,
          db.db.createProof,
          Declaration(Map.empty),
          listener(db.db, constructGlobalProvable = true),
          ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
          2,
          strict = true,
          convertPending = false,
          recordInternal = true,
        ))
        interpreter(prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula))) match {
          case BelleProvable(p, l) =>
            p.subgoals should contain theSameElementsAs List("==> x>=0, x<y".asSequent)
            l.value should contain theSameElementsAs List("!x<y".asFormula.prettyString.asLabel)
        }

        val tree = DbProofTree(db.db, proofId.toString)
        tree.tactic shouldBe tacticParser(
          """implyR('R=="x>=0|!x < y->x>=0");
            |orLRule('L=="x>=0|!x < y"); <(
            |  label("x>=0"); id,
            |  label("!x < y"); notL('L=="!x < y"); todo
            |)""".stripMargin
        )

        val proofId2 = db.createProof(modelContent, "proof2")
        registerInterpreter(SpoonFeedingInterpreter(
          proofId2,
          -1,
          db.db.createProof,
          Declaration(Map.empty),
          listener(db.db, constructGlobalProvable = true),
          ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
          2,
          strict = false,
          convertPending = false,
          recordInternal = true,
        ))(prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))
        DbProofTree(db.db, proofId2.toString).tactic shouldBe tacticParser(
          """implyR('R=="x>=0|!x < y->x>=0");
            |orLRule('L=="x>=0|!x < y"); <(
            |  label("x>=0"); id,
            |  label("!x < y"); notL('L=="!x < y"); todo
            |)""".stripMargin
        )
      }
  }

  it should "FEATURE_REQUEST: work for prop with nested branching" taggedAs TodoTest in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|x<y -> x>=0&x<y"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent, "proof")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = false,
        convertPending = true,
        recordInternal = true,
      ))
      interpreter(prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      DbProofTree(db.db, proofId.toString).tactic shouldBe tacticParser(
        """implyR('R=="x>=0|x < y->x>=0&x < y");
          |andR('R=="x>=0&x < y"); <(
          |  "x>=0":
          |    orL('L=="x>=0|x < y"); <(
          |      "x>=0": id,
          |      "x < y": todo
          |    ),
          |  "x < y":
          |    orL('L=="x>=0|x < y"); <(
          |      "x>=0": todo,
          |      "x < y": id
          |    )
          |)""".stripMargin
      )
    }
  }

  it should "work for master on failing QE" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0 -> x>=2"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent, "proof")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = true),
        1,
        strict = false,
        convertPending = true,
        recordInternal = true,
      ))
      interpreter(master(), BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      val tree = DbProofTree(db.db, proofId.toString)
      tree.openGoals.loneElement.goal shouldBe Some("==> false".asSequent)
      tree.tactic shouldBe tacticParser("implyR('R==\"x>=0->x>=2\"); expandAllDefs(\"nil\"); applyEqualities; QE; todo")
    }
  }

  private def stepInto(node: ProofTreeNode, expectedStep: String, depth: Int = 1)(
      db: DBAbstraction
  ): (Int, BelleExpr) = {
    val (localProvable, step) = (ProvableSig.startPlainProof(node.conclusion), node.maker.getOrElse("nil"))
    step shouldBe expectedStep
    val localProofId = db.createProof(localProvable)
    val innerInterpreter = registerInterpreter(SpoonFeedingInterpreter(
      localProofId,
      -1,
      db.createProof,
      Declaration(Map.empty),
      listener(db, constructGlobalProvable = true),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
      depth,
      strict = false,
      convertPending = true,
      recordInternal = true,
    ))
    innerInterpreter(tacticParser(step), BelleProvable.plain(localProvable))
    val innerId = innerInterpreter.innerProofId.getOrElse(localProofId)
    (localProofId, DbProofTree(db, innerId.toString).tactic)
  }

  it should "work in the middle of a proof" in withDatabase { db =>
    withMathematica { _ =>
      val problem = "x>=0|x<y -> x>=0&x<y"
      val modelContent = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent, "proof1")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        0,
        strict = false,
        convertPending = true,
        recordInternal = true,
      ))
      interpreter(implyR(1) & prop, BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)))

      val tree = DbProofTree(db.db, proofId.toString).load()
      tree.locate("(2,0)") match {
        case Some(node) =>
          val (_, tactic) = stepInto(node, "prop", 1)(db.db)
          tactic shouldBe tacticParser(
            """andR('R=="x>=0&x < y"); <(
              |  "x>=0":
              |    orL('L=="x>=0|x < y"); <(
              |      "x>=0": id,
              |      "x < y": todo
              |    ),
              |  "x < y":
              |    orL('L=="x>=0|x < y"); <(
              |      "x>=0": todo,
              |      "x < y": id
              |    )
              |)""".stripMargin
          )
      }
    }
  }

  it should "work in the middle of a proof with the in-memory DB" in withMathematica { _ =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val provable = ProvableSig.startPlainProof(problem.asFormula)
    val db = new InMemoryDB()
    val proofId = db.createProof(provable)
    val interpreter = createInterpreter(proofId, db)
    interpreter(implyR(1) & prop, BelleProvable.plain(provable))

    val tree = DbProofTree(db, proofId.toString).load()
    tree.locate("(1,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop", 1)(db)
        tactic shouldBe tacticParser(
          """andR('R=="x>=0&x < y"); <(
            |  "x>=0":
            |    orL('L=="x>=0|x < y"); <(
            |      "x>=0": id,
            |      "x < y": todo
            |    ),
            |  "x < y":
            |    orL('L=="x>=0|x < y"); <(
            |      "x>=0": todo,
            |      "x < y": id
            |    )
            |)""".stripMargin
        )
    }
  }

  it should "work on a branch in the middle of a proof" in withMathematica { _ =>
    val problem = "x>=0|x<y -> x>=0&x<y"
    val db = new InMemoryDB()

    val provable = ProvableSig.startPlainProof(problem.asFormula)
    val proofId = db.createProof(provable)

    val interpreter = createInterpreter(proofId, db)
    interpreter(implyR(1) & orL(-1) & onAll(prop), BelleProvable.plain(provable))

    val tree = DbProofTree(db, proofId.toString).load()
    tree.locate("(3,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop", 1)(db)
        tactic shouldBe tacticParser(
          """andR('R=="x>=0&x < y"); <(
            |  "x>=0": id,
            |  "x < y": todo
            |)""".stripMargin
        )
    }

    tree.locate("(2,0)") match {
      case Some(node) =>
        val (_, tactic) = stepInto(node, "prop", 1)(db)
        tactic shouldBe tacticParser(
          """andR('R=="x>=0&x < y"); <(
            |  "x>=0": todo,
            |  "x < y": id
            |)""".stripMargin
        )
    }
  }

  it should "FEATURE_REQUEST: work on a typical example" taggedAs TodoTest in withDatabase { db =>
    withZ3 { _ =>
      val problem = "x>=0 & y>=1 & z<=x+y & 3>2  -> [x:=x+y;]x>=z"
      val modelContent =
        s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; Real z; End.\n\n Problem $problem End. End."""
      val proofId = db.createProof(modelContent)
      val interpreter = createInterpreter(proofId, db.db)
      interpreter(
        prop & unfoldProgramNormalize & QE,
        BelleProvable.plain(ProvableSig.startPlainProof(problem.asFormula)),
      )

      val tactic = db.extractTactic(proofId)
      tactic shouldBe tacticParser("prop ; unfold ; QE")

      val tree = DbProofTree(db.db, proofId.toString)
      tree.locate("(1,0)") match {
        case Some(node) => stepInto(node, "prop")(db.db)._2 shouldBe tacticParser(
            """implyR('R=="x>=0&y>=1&z<=x+y&3>2->[x:=x+y;]x>=z");
              |andL('L=="x>=0&y>=1&z<=x+y&3>2");
              |andL('L=="y>=1&z<=x+y&3>2");
              |andL('L=="z<=x+y&3>2");
              |todo""".stripMargin
          )
      }

      tree.locate("(2,0)") match {
        case Some(node) => stepInto(node, "unfold")(db.db)._2 shouldBe tacticParser("""step('R=="[x:=x+y;]x>=z")""")
      }

      // @todo QE uses AnonymousLemmas.cacheTacticResult, which is neither serializable nor executes internal steps visible to the spoonfeeding interpreter
      // (either looks up a lemma or starts a new nested proof; would want to re-execute its tactic for spoonfeeding, instead of useLemma)
      tree.locate("(3,0)") match {
        case Some(node) => stepInto(node, "QE")(db.db)
            ._2 shouldBe tacticParser("toSingleFormula ; universalClosure(1) ; rcf")
      }
    }
  }

  it should "work for dC+DI" in withZ3 { _ =>
    val problem = """w()^2*x^2 + y^2 <= c()^2
                    |  & d>=0
                    |->
                    |  [{x'=y, y'=-w()^2*x-2*d*w()*y, d'=7 & w()>=0}]w()^2*x^2 + y^2 <= c()^2
      """.stripMargin
    val p = ProvableSig.startPlainProof(problem.asFormula)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = createInterpreter(proofId, db)
    interpreter(implyR(1) & diffInvariant("d>=0".asFormula)(1), BelleProvable.plain(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (id1, tactic1) = stepInto(n1, """diffInvariant("d>=0", 1)""")(db)
        tactic1 shouldBe tacticParser(
          """dC("d>=0", 'R=="[{x'=y,y'=-w()^2*x-2*d*w()*y,d'=7&w()>=0}]w()^2*x^2+y^2<=c()^2"); <(
            |  "Use": todo,
            |  "Show": dI('R=="[{x'=y,y'=-w()^2*x-2*d*w()*y,d'=7&w()>=0}]d>=0")
            |)""".stripMargin
        )
        // diffCut
        DbProofTree(db, id1.toString).locate("(2,0)") match {
          case Some(n2) =>
            val (_, tactic2) = stepInto(n2, """dC("d>=0", 1)""")(db)
            val tacticString = """DC("d>=0", 'R=="[{x'=y,y'=-w()^2*x-2*d*w()*y,d'=7&w()>=0}]w()^2*x^2+y^2<=c()^2"); <(
                                 |  "Use": todo,
                                 |  "Show": todo
                                 |)""".stripMargin
            tactic2 shouldBe tacticParser(tacticString)
            BellePrettyPrinter(tactic2) should equal(tacticString)(after being whiteSpaceRemoved)
        }
        // diffInd
        DbProofTree(db, id1.toString).locate("(3,1)") match {
          case Some(n2) =>
            val (_, tactic) = stepInto(n2, "dI(1)")(db)
            val tacticString = """DI('R=="[{x'=y,y'=-w()^2*x-2*d*w()*y,d'=7&w()>=0}]d>=0");
                                 |implyR('R=="w()>=0->d>=0&[{x'=y,y'=-w()^2*x-2*d*w()*y,d'=7&w()>=0}](d>=0)'");
                                 |andR('Rlast); <(
                                 |  "d>=0": QE,
                                 |  "[{x'=y,y'=-w()^2*x-2*d*w()*y,d'=7&w()>=0}](d>=0)'":
                                 |    derive('Rlast.1);
                                 |    DE('Rlast);
                                 |    Dassignb('Rlast.1);Dassignb('Rlast.1);Dassignb('Rlast.1);
                                 |    DW('Rlast);
                                 |    GV('Rlast);
                                 |    QE
                                 |)""".stripMargin
            tactic shouldBe tacticParser(tacticString)
            BellePrettyPrinter(tactic) should equal(tacticString)(after being whiteSpaceRemoved)
        }
    }
  }

  it should "work for simple dI" in withMathematica { _ =>
    val problem = "x>0 -> [{x'=3}]x>0".asFormula
    val p = ProvableSig.startPlainProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = createInterpreter(proofId, db)
    interpreter(implyR(1) & DifferentialEquationCalculus.dIX(1), BelleProvable.plain(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        val tacticString = """DI('R=="[{x'=3}]x>0");
                             |implyR('R=="true->x>0&[{x'=3}](x>0)'");
                             |andR('Rlast); <(
                             |  "x>0": QE,
                             |  "[{x'=3}](x>0)'":
                             |    derive('Rlast.1);
                             |    DE('Rlast);
                             |    Dassignb('Rlast.1);
                             |    GV('Rlast);
                             |    QE
                             |)""".stripMargin
        tactic shouldBe tacticParser(tacticString)
        BellePrettyPrinter(tactic) should equal(tacticString)(after being whiteSpaceRemoved)
        proveBy(problem, implyR(1) & tactic) shouldBe Symbol("proved")
    }
  }

  it should "work for simple dI with constants" in withMathematica { _ =>
    val problem = "x>0 & a>=0 -> [{x'=a}]x>0".asFormula
    val p = ProvableSig.startPlainProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = createInterpreter(proofId, db)
    interpreter(implyR(1) & DifferentialEquationCalculus.dIX(1), BelleProvable.plain(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        val tacticString = """DI('R=="[{x'=a}]x>0");
                             |implyR('R=="true->x>0&[{x'=a}](x>0)'");
                             |andR('Rlast); <(
                             |  "x>0": QE,
                             |  "[{x'=a}](x>0)'":
                             |    derive('Rlast.1);
                             |    DE('Rlast);
                             |    Dassignb('Rlast.1);
                             |    GV('Rlast);
                             |    QE
                             |)""".stripMargin
        tactic shouldBe tacticParser(tacticString)
        BellePrettyPrinter(tactic) should equal(tacticString)(after being whiteSpaceRemoved)
        proveBy(problem, implyR(1) & tactic) shouldBe Symbol("proved")
    }
  }

  it should "work for simple dI with non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "x>a -> [{x'=5}]x>a".asFormula
    val p = ProvableSig.startPlainProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)
    val interpreter = createInterpreter(proofId, db)
    interpreter(implyR(1) & DifferentialEquationCalculus.dIX(1), BelleProvable.plain(p))

    val tree = DbProofTree(db, proofId.toString)
    tree.locate("(1,0)") match {
      case Some(n1) =>
        val (_, tactic) = stepInto(n1, "dI(1)")(db)
        val tacticString = """DI('R=="[{x'=5}]x>a()");
                             |implyR('R=="true->x>a()&[{x'=5}](x>a())'");
                             |andR('Rlast); <(
                             |  "x>a()": QE,
                             |  "[{x'=5}](x>a())'":
                             |    derive('Rlast.1);
                             |    DE('Rlast);
                             |    Dassignb('Rlast.1);
                             |    GV('Rlast);
                             |    QE
                             |)""".stripMargin
        tactic shouldBe tacticParser(tacticString)
        BellePrettyPrinter(tactic) should equal(tacticString)(after being whiteSpaceRemoved)
    }
  }

  it should "work when dI fails with non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "[{x'=5}]x>a".asFormula
    val p = ProvableSig.startPlainProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(
      proofId,
      -1,
      db.createProof,
      Declaration(Map.empty),
      listener(db, constructGlobalProvable = true),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
      1,
      strict = false,
      convertPending = true,
      recordInternal = true,
    ))
    interpreter(DifferentialEquationCalculus.dIX(1), BelleProvable.plain(p))

    val innerId = interpreter.innerProofId.getOrElse(proofId)
    val tree = DbProofTree(db, innerId.toString)
    val tactic = tree.tactic
    val tacticString = """DI('R=="[{x'=5}]x>a()");
                         |implyR('R=="true->x>a()&[{x'=5}](x>a())'");
                         |andR('Rlast); <(
                         |  "x>a()":
                         |    QE;
                         |    todo,
                         |  "[{x'=5}](x>a())'":
                         |    derive('Rlast.1);
                         |    DE('Rlast);
                         |    Dassignb('Rlast.1);
                         |    GV('Rlast);
                         |    QE
                         |)""".stripMargin
    tactic shouldBe tacticParser(tacticString)
    BellePrettyPrinter(tactic) should equal(tacticString)(after being whiteSpaceRemoved)
  }

  it should "work when dI fails with multiple non-primed variables in postcondition" in withMathematica { _ =>
    val problem = "[{x'=5}]x>a+b".asFormula
    val p = ProvableSig.startPlainProof(problem)
    implicit val db: DBAbstraction = new InMemoryDB()
    val proofId = db.createProof(p)

    val interpreter = registerInterpreter(SpoonFeedingInterpreter(
      proofId,
      -1,
      db.createProof,
      Declaration(Map.empty),
      listener(db, constructGlobalProvable = true),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
      1,
      strict = false,
      convertPending = true,
      recordInternal = true,
    ))
    interpreter(DifferentialEquationCalculus.dIX(1), BelleProvable.plain(p))

    val innerId = interpreter.innerProofId.getOrElse(proofId)
    val tactic = DbProofTree(db, innerId.toString).tactic
    // @todo want pending("QE") or pending("QE & done | done") instead of nil
    val tacticString = """DI('R=="[{x'=5}]x>a()+b()");
                         |implyR('R=="true->x>a()+b()&[{x'=5}](x>a()+b())'");
                         |andR('Rlast); <(
                         |  "x>a()+b()":
                         |    QE;
                         |    todo,
                         |  "[{x'=5}](x>a()+b())'":
                         |    derive('Rlast.1);
                         |    DE('Rlast);
                         |    Dassignb('Rlast.1);
                         |    GV('Rlast);
                         |    QE
                         |)""".stripMargin
    tactic shouldBe tacticParser(tacticString)
    BellePrettyPrinter(tactic) should equal(tacticString)(after being whiteSpaceRemoved)
  }

  it should "FEATURE_REQUEST: work for partial prop" taggedAs TodoTest in withMathematica { _ =>
    withDatabase { sql =>
      val problem = "x=1 & y=2 -> x=3".asFormula
      val modelFile = s"""ArchiveEntry "Test" ProgramVariables Real x; Real y; End.\n Problem $problem End. End."""
      val p = ProvableSig.startPlainProof(problem)
      val pId = sql.createProof(modelFile, "model1")
      val tactic = prop & done
      intercept[BelleThrowable] { proveBy(problem, tactic) }
        .getMessage should startWith("expected to have proved, but got open goals")
      sql.extractTactic(pId) shouldBe tacticParser("todo")

      implicit val db: DBAbstraction = new InMemoryDB()
      val proofId = db.createProof(p)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.createProof,
        Declaration(Map.empty),
        listener(db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        2,
        strict = false,
        convertPending = true,
        recordInternal = true,
      ))
      interpreter(tactic, BelleProvable.plain(p))
      DbProofTree(db, proofId.toString)
        .tactic shouldBe tacticParser("""implyR('R=="x=1&y=2->x=3"); andL('L=="x=1&y=2"); pending("done"); todo""")
    }
  }

  "Pending" should "execute and record successful tactic" in withQE { _ =>
    withDatabase { db =>
      val problem = "x>0 -> x>0".asFormula
      val modelFile = s"""ArchiveEntry "Test" ProgramVariables Real x; End.\n Problem $problem End. End."""
      val p = ProvableSig.startPlainProof(problem)
      val proofId = db.createProof(modelFile, "model1")
      val tactic = tacticParser("""pending("implyR(1) ; id"); todo""")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        2,
        strict = false,
        convertPending = true,
        recordInternal = false,
      ))
      interpreter(tactic, BelleProvable.plain(p))
      db.extractTactic(proofId) shouldBe tacticParser("implyR('R==\"x>0->x>0\"); id")
    }
  }

  it should "try execute and record again as pending on failure" in withQE { _ =>
    withDatabase { db =>
      val problem = "x>0 -> x>0".asFormula
      val modelFile = s"""ArchiveEntry "Test" ProgramVariables Real x; End.\n Problem $problem End. End."""
      val p = ProvableSig.startPlainProof(problem)
      val proofId = db.createProof(modelFile, "model1")
      val tactic = tacticParser("""pending("implyR(1) ; andR(1)"); todo""")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        2,
        strict = false,
        convertPending = true,
        recordInternal = false,
      ))
      interpreter(tactic, BelleProvable.plain(p))
      db.extractTactic(proofId) shouldBe tacticParser("""implyR('R=="x>0->x>0"); pending("andR(1)"); todo""")
    }
  }

  it should "not fail on nested tactic with arguments" in withQE { _ =>
    withDatabase { db =>
      val problem = "x>0 -> [x:=x+1;]x>0".asFormula
      val modelFile = s"""ArchiveEntry "Test" ProgramVariables Real x; End.\n Problem $problem End. End."""
      val p = ProvableSig.startPlainProof(problem)
      val proofId = db.createProof(modelFile, "model1")
      val tactic = tacticParser("""pending("implyR(1) ; loop(\"x>0\", 1)"); todo""")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        1,
        strict = false,
        convertPending = true,
        recordInternal = false,
      ))
      interpreter(tactic, BelleProvable.plain(p))
      db.extractTactic(proofId) shouldBe tacticParser(
        """implyR('R=="x>0->[x:=x+1;]x>0"); pending("loop(\"x>0\", 1)"); todo"""
      )
    }
  }

  it should "record innermost failed tactic as pending" in withQE { _ =>
    withDatabase { db =>
      val problem = "x>0 -> [x:=x+1;]x>0".asFormula
      val modelFile = s"""ArchiveEntry "Test" ProgramVariables Real x; End.\n Problem $problem End. End."""
      val p = ProvableSig.startPlainProof(problem)
      val proofId = db.createProof(modelFile, "model1")
      val tactic = tacticParser("""implyR(1); cut("x>=0"); <("Use": hideL(-1); loop("x>0", 1), "Show": hideR(1); QE)""")
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        0,
        strict = false,
        convertPending = true,
        recordInternal = false,
      ))
      interpreter(tactic, BelleProvable.plain(p))
      db.extractTactic(proofId) shouldBe tacticParser(
        """implyR('R=="x>0->[x:=x+1;]x>0");
          |cut("x>=0"); <(
          |  "Use": hideL('L=="x>0"); pending("loop(\"x>0\", 1)"); todo,
          |  "Show": hideR('R=="[x:=x+1;]x>0"); QE
          |)""".stripMargin
      )
    }
  }

  it should "record innermost failed tactic as pending (2)" in withQE { _ =>
    withDatabase { db =>
      val problem = "x>0 -> [x:=x+1;]x>0".asFormula
      val modelFile = s"""ArchiveEntry "Test" ProgramVariables Real x; End.\n Problem $problem End. End."""
      val p = ProvableSig.startPlainProof(problem)
      val proofId = db.createProof(modelFile, "model1")
      val tactic = tacticParser(
        """implyR(1); cut("x>=0"); <(
          |  "Use": loop("x>0", 1); <("Init": id, "Post": id, "Step": auto),
          |  "Show": hideR(1); QE
          |)""".stripMargin
      )
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        Declaration(Map.empty),
        listener(db.db, constructGlobalProvable = true),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        0,
        strict = false,
        convertPending = true,
        recordInternal = false,
      ))
      interpreter(tactic, BelleProvable.plain(p))
      db.extractTactic(proofId) shouldBe tacticParser(
        """implyR('R=="x>0->[x:=x+1;]x>0");
          |cut("x>=0"); <(
          |  "Use":
          |    pending("loop(\"x>0\", 1) ; <(
          |    \"Init\": id,
          |    \"Post\": id,
          |    \"Step\": auto
          |  )");
          |    todo,
          |  "Show": hideR('R=="[x:=x+1;]x>0"); QE
          |)""".stripMargin
      )
    }
  }

  "Delayed substitution" should "support introducing variables for function symbols of closed provables" in withMathematica {
    _ =>
      withDatabase { db =>
        val entry = ArchiveParser
          .parser(
            """ArchiveEntry "Delayed Substitution from dIRule"
              |ProgramVariables Real x, y, r; End.
              |Problem x^2+y^2=r -> [{x'=r*y,y'=-r*x}]x^2+y^2=r End.
              |End.""".stripMargin
          )
          .head

        val proofId = db.createProof(entry.problemContent)

        val interpreter = createInterpreter(proofId, db.db, constructGlobalProvable = false)
        val tactic = tacticParser(
          """implyR(1); cut("r>0"); <(
            |  dC("x^2+y^2=r", 1); <(
            |    cut("r>1"),
            |    dIRule(1); <(
            |      QE,
            |      unfold; QE
            |    )
            |  ),
            |  ODE(1)
            |)""".stripMargin
        )
        interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(entry.model.asInstanceOf[Formula]))) match {
          case BelleProvable(p, _) => p.subgoals should contain theSameElementsInOrderAs List(
              "x^2+y^2=r, r>0, r>1 ==> [{x'=r*y,y'=-r*x&true&x^2+y^2=r}]x^2+y^2=r".asSequent,
              "x^2+y^2=r, r>0 ==> [{x'=r*y,y'=-r*x&true&x^2+y^2=r}]x^2+y^2=r, r>1".asSequent,
            )
        }
      }
  }

  it should "work if steps modify the subgoal and dIRule constifies after" in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .parser(
          """ArchiveEntry "Delayed Substitution from dIRule"
            |ProgramVariables Real x, y, r; End.
            |Problem x^2+y^2=r -> [{x'=r*y,y'=-r*x}]x^2+y^2=r End.
            |End.""".stripMargin
        )
        .head

      val proofId = db.createProof(entry.problemContent)

      val interpreter = createInterpreter(proofId, db.db, constructGlobalProvable = false)
      val tactic = tacticParser(
        """implyR(1); cut("r>0"); <(
          |  dC("x^2+y^2=r", 1); <(
          |    cut("r>1"),
          |    /* steps before dIRule need to be merged with dIRule result after dIRule branches are finished */
          |    edit("r>=-7", 'L=="r>0"); hideL('L=="r>=-7"); dIRule(1); <(
          |      QE,
          |      unfold; QE
          |    )
          |  ),
          |  ODE(1)
          |)""".stripMargin
      )
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(entry.model.asInstanceOf[Formula]))) match {
        case BelleProvable(p, _) => p.subgoals should contain theSameElementsInOrderAs List(
            "x^2+y^2=r, r>0, r>1 ==> [{x'=r*y,y'=-r*x&true&x^2+y^2=r}]x^2+y^2=r".asSequent,
            "x^2+y^2=r, r>0 ==> [{x'=r*y,y'=-r*x&true&x^2+y^2=r}]x^2+y^2=r, r>1".asSequent,
          )
      }
    }
  }

  it should "support unfinished dIRule if sole open goal" in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .parser(
          """ArchiveEntry "Delayed Substitution from dIRule"
            |ProgramVariables Real x, y, r; End.
            |Problem x^2+y^2=r -> [{x'=r*y,y'=-r*x}]x^2+y^2=r End.
            |End.""".stripMargin
        )
        .head

      val proofId = db.createProof(entry.problemContent)

      val interpreter = createInterpreter(proofId, db.db, constructGlobalProvable = false)
      val tactic = tacticParser(
        """implyR(1); dIRule(1); <(
          |  nil,
          |  unfold; QE
          |)""".stripMargin
      )
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(entry.model.asInstanceOf[Formula]))) match {
        case BelleProvable(p, _) => p.subgoals.loneElement shouldBe "x^2+y^2=r(), true ==> x^2+y^2=r()".asSequent
      }
    }
  }

  it should "FEATURE_REQUEST: expand definitions after applying backsubstitutions from constification" taggedAs TodoTest in withMathematica {
    _ =>
      withDatabase { db =>
        val entry = ArchiveParser
          .parser(
            """ArchiveEntry "Delayed Substitution from dIRule"
              |Definitions Real sqsum(Real x, Real y) = x^2+y^2; End.
              |ProgramVariables Real x, y, r; End.
              |Problem sqsum(x,y)=r -> [{x'=r*y,y'=-r*x}]sqsum(x,y)=r End.
              |End.""".stripMargin
          )
          .head

        val proofId = db.createProof(entry.problemContent)

        val interpreter = registerInterpreter(SpoonFeedingInterpreter(
          proofId,
          -1,
          db.db.createProof,
          entry.defs,
          listener(db.db, constructGlobalProvable = false),
          ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
          0,
          strict = true,
          convertPending = true,
          recordInternal = false,
        ))
        val tactic = tacticParser(
          """implyR(1); cut("r>0"); <(
            |  dC("sqsum(x, y)=r", 1); <(
            |    nil,
            |    edit("r>=-7", 'L=="r>0"); hideL('L=="r>=-7"); expand("sqsum"); dIRule(1); <(
            |      QE,
            |      unfold; QE
            |    )
            |  ),
            |  expandAllDefs; ODE(1)
            |)""".stripMargin,
          defs = entry.defs,
        )
        interpreter(
          tactic,
          BelleProvable.plain(ProvableSig.startProof(entry.model.asInstanceOf[Formula], entry.defs)),
        ) match {
          case BelleProvable(p, _) =>
            p.subgoals.loneElement shouldBe "x^2+y^2=r, r>0 ==> [{x'=r*y,y'=-r*x&true&x^2+y^2=r}]x^2+y^2=r".asSequent
        }
      }
  }

  it should "FEATURE_REQUEST: expand definitions exhaustively after applying backsubstitutions from constification" taggedAs TodoTest in withMathematica {
    _ =>
      withDatabase { db =>
        val entry = ArchiveParser
          .parser(
            """ArchiveEntry "Delayed Substitution from dIRule"
              |Definitions Real dosqsum(Real x, Real y) = x^2+y^2; Real sqsum(Real x, Real y) = dosqsum(x,y); End.
              |ProgramVariables Real x, y, r; End.
              |Problem sqsum(x,y)=r -> [{x'=r*y,y'=-r*x}]sqsum(x,y)=r End.
              |End.""".stripMargin
          )
          .head

        val proofId = db.createProof(entry.problemContent)

        val interpreter = registerInterpreter(SpoonFeedingInterpreter(
          proofId,
          -1,
          db.db.createProof,
          entry.defs,
          listener(db.db, constructGlobalProvable = false),
          ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
          0,
          strict = true,
          convertPending = true,
          recordInternal = false,
        ))
        val tactic = tacticParser(
          """implyR(1); cut("r>0"); <(
            |  dC("sqsum(x, y)=r", 1); <(
            |    nil,
            |    edit("r>=-7", 'L=="r>0"); hideL('L=="r>=-7"); expand("sqsum"); expand("dosqsum"); dIRule(1); <(
            |      QE,
            |      unfold; QE
            |    )
            |  ),
            |  expandAllDefs; ODE(1)
            |)""".stripMargin,
          defs = entry.defs,
        )
        interpreter(
          tactic,
          BelleProvable.plain(ProvableSig.startProof(entry.model.asInstanceOf[Formula], entry.defs)),
        ) match {
          case BelleProvable(p, _) =>
            p.subgoals.loneElement shouldBe "x^2+y^2=r, r>0 ==> [{x'=r*y,y'=-r*x&true&x^2+y^2=r}]x^2+y^2=r".asSequent
        }
      }
  }

  it should "support nested constifications" in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .parser(
          """ArchiveEntry "Delayed Substitution from dIRule"
            |ProgramVariables Real x, y, r, s; End.
            |Problem x^2+y^2+s=r -> [{x'=r*y,y'=-r*x}]x^2+y^2+s=r End.
            |End.""".stripMargin
        )
        .head

      val proofId = db.createProof(entry.problemContent)

      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        entry.defs,
        listener(db.db, constructGlobalProvable = false),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        0,
        strict = true,
        convertPending = true,
        recordInternal = false,
      ))
      // @note dIRule constifies r,s
      val tactic = tacticParser("""implyR(1); dIRule(1)""".stripMargin, defs = entry.defs)
      interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(entry.model.asInstanceOf[Formula]))) match {
        case BelleProvable(p, _) => p.subgoals should contain theSameElementsAs List(
            "x^2+y^2+s()=r(), true ==> x^2+y^2+s()=r()".asSequent,
            "x_0^2+y_0^2+s()=r(), true ==> [y':=-r()*x;][x':=r()*y;]2*x^(2-1)*x'+2*y^(2-1)*y'+0=0".asSequent,
          )
      }
    }
  }

  it should "support tactic-internal definition expansion" in withMathematica { _ =>
    withDatabase { db =>
      val s = """ArchiveEntry "Test"
                |Definitions
                |  import kyx.math.{abs,max};
                |  Real wUp()= -1;
                |  Real wLo()=  1;
                |  Real alo, hp, rp;
                |  Real maxI(Real v, Real w, Real vlo) = max(0, w*(vlo-v));
                |End.
                |ProgramVariables
                |  Real h, w, v, vlo, r, rv;
                |End.
                |Problem
                |(w=wUp()|w=wLo()) &
                |(0 < maxI(v,w,vlo)/alo() | 0>=maxI(v,w,vlo)/alo() & 0=-w*maxI(v,w,vlo)^2/(2*alo())
                |   -> abs(r)>rp()|w*h < -hp()) &
                |rp()>=0 & hp()>0 & rv>=0 & alo()>0
                |->
                |abs(r)>rp() | abs(h)>hp()
                |End.
                |End.
                |""".stripMargin

      val entry = ArchiveParser.parse(s).head

      val proofId = db.createProof(s)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        entry.defs,
        listener(db.db, constructGlobalProvable = false),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        0,
        strict = true,
        convertPending = true,
        recordInternal = false,
      ))
      // @note QE expands wUp and wLo
      val tactic = tacticParser("""implyR(1); andL('L)*; implyL('L); <(QE, QE)""".stripMargin, defs = entry.defs)
      interpreter(
        tactic,
        BelleProvable.plain(ProvableSig.startProof(entry.model.asInstanceOf[Formula], entry.defs)),
      ) match { case BelleProvable(p, _) => p shouldBe Symbol("proved") }
    }
  }

  it should "correctly plug into branch parents when tactics expand definitions internally" in withMathematica { _ =>
    withDatabase { db =>
      val s = """ArchiveEntry "Test"
                |Definitions
                |  Real f;
                |  Real one = 1;
                |End.
                |ProgramVariables Real a, b, x, y, z; End.
                |Problem
                |y>=0 & f()=1 ->
                |((x>=0 -> y*x>=0) & (a=0 -> y*a=0)) &
                |(z>=1&z<=2 -> (y/(z*one())>=0 & (b=0 -> b/z=0)))
                |End.
                |End.
                |""".stripMargin

      val entry = ArchiveParser.parse(s).head

      val proofId = db.createProof(s)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        entry.defs,
        listener(db.db, constructGlobalProvable = false),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        0,
        strict = true,
        convertPending = true,
        recordInternal = false,
      ))
      // @note QE expands one()
      val tactic = tacticParser(
        """implyR(1); andL('L)*; andR(1); <(
          | prop; doall(QE)
          | ,
          | implyR(1);
          | andL('Llast);
          | QE using "y>=0 :: z>=1 :: y/(z*one())>=0 & (b=0 -> b/z=0) :: nil"
          |)""".stripMargin,
        defs = entry.defs,
      )
      interpreter(
        tactic,
        BelleProvable.plain(ProvableSig.startProof(entry.model.asInstanceOf[Formula], entry.defs)),
      ) match { case BelleProvable(p, _) => p shouldBe Symbol("proved") }
    }
  }

  it should "FEATURE_REQUEST: return delayed substitution on unfinished dIRule when mixed with unconstified branches" taggedAs TodoTest in withMathematica {
    _ =>
      withDatabase { db =>
        val entry = ArchiveParser
          .parser(
            """ArchiveEntry "Delayed Substitution from dIRule"
              |ProgramVariables Real x, y, r; End.
              |Problem x^2+y^2=r -> [{x'=r*y,y'=-r*x}]x^2+y^2=r End.
              |End.""".stripMargin
          )
          .head

        val proofId = db.createProof(entry.problemContent)

        val interpreter = createInterpreter(proofId, db.db)
        val tactic = tacticParser(
          """implyR(1); cut("r>0"); <(
            |  dIRule(1); <(
            |    nil,
            |    unfold; QE
            |  ),
            |  nil
            |)""".stripMargin
        )
        // @todo see Interpreter.applySubDerivation which returns subderivation verbatim without applying to parent (because
        // it can't until constification is backsubstituted)
        interpreter(tactic, BelleProvable.plain(ProvableSig.startPlainProof(entry.model.asInstanceOf[Formula]))) match {
          case p: BelleDelayedSubstProvable => p.p.subgoals should contain theSameElementsInOrderAs List()
        }
      }
  }

  it should "support interpreted functions in expandAllDefs" in withMathematica { _ =>
    withDatabase { db =>
      val entry = ArchiveParser(
        """ArchiveEntry "Implicit interpreted function definition"
          |Definitions
          |  import kyx.math.exp;
          |  implicit Real tanh(Real t) = {{tanh:=0;}; {tanh'=1-tanh^2}};
          |  Real tau;
          |  Real lambda;
          |End.
          |  ProgramVariables Real x,y,old; End.
          |Problem
          |tau()>0 & t=0 & x^2+y^2=old & old>0
          |  ->  [{t'=1,x'=-x/tau()+tanh(lambda()*x)-tanh(lambda()*y),y'=-y/tau()+tanh(lambda()*x)+tanh(lambda()*y)&true&x^2+y^2>0}]exp(-t/tau())*old^(1/2)+2*tau()*(1-exp(-t/tau()))-(x^2+y^2)^(1/2)>=0
          |End.
          |Tactic "Steps"
          |unfold;
          |dbx("(-1)/tau()", 1); /* causes a delayed substitution step, has a "delayed" parent */
          |expandAllDefs         /* creates a child delayed substitution provable, does not have a "delayed" parent */
          |End.
          |End.
          |""".stripMargin
      ).head

      val proofId = db.createProof(entry.fileContent)
      val interpreter = registerInterpreter(SpoonFeedingInterpreter(
        proofId,
        -1,
        db.db.createProof,
        entry.defs,
        listener(db.db, constructGlobalProvable = false),
        ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
        0,
        strict = true,
        convertPending = true,
        recordInternal = false,
      ))
      interpreter(entry.tactics.head._3, BelleProvable.plain(ProvableSig.startProof(entry.sequent, entry.defs))) match {
        case BelleProvable(p, _) => p.subgoals.loneElement shouldBe
            """tau()>0, t=0, x^2+y^2=old(), old()>0
              |  ==>  \forall t \forall x \forall y (true&x^2+y^2>0->exp(-t/tau())*(-(1*tau()-t*0)/tau()^2)*old()^(1/2)+2*tau()*(0-exp(-t/tau())*(-(1*tau()-t*0)/tau()^2))-1/2*(x^2+y^2)^(1/2-1)*(2*x^(2-1)*(-x/tau()+tanh<< <{tanh:=._0;t:=._1;}{{tanh'=-(1-tanh^2),t'=-1}++{tanh'=1-tanh^2,t'=1}}>(tanh=0&t=0) >>(lambda()*x)-tanh<< <{tanh:=._0;t:=._1;}{{tanh'=-(1-tanh^2),t'=-1}++{tanh'=1-tanh^2,t'=1}}>(tanh=0&t=0) >>(lambda()*y))+2*y^(2-1)*(-y/tau()+tanh<< <{tanh:=._0;t:=._1;}{{tanh'=-(1-tanh^2),t'=-1}++{tanh'=1-tanh^2,t'=1}}>(tanh=0&t=0) >>(lambda()*x)+tanh<< <{tanh:=._0;t:=._1;}{{tanh'=-(1-tanh^2),t'=-1}++{tanh'=1-tanh^2,t'=1}}>(tanh=0&t=0) >>(lambda()*y)))>=(-1)/tau()*(exp(-t/tau())*old()^(1/2)+2*tau()*(1-exp(-t/tau()))-(x^2+y^2)^(1/2)))
              |""".stripMargin.asSequent
      }
    }
  }
}
