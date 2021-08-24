package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerator, FixedGenerator, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Real, USubst}
import edu.cmu.cs.ls.keymaerax.infrastruct.SuccPosition
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, Name, Signature, UnknownLocation}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import org.scalatest.LoneElement._
import org.scalatest.Inside._
import spray.json.{JsArray, JsBoolean, JsString}
import org.scalatest.prop.TableDrivenPropertyChecks._

/**
  * Tests the server-side web API with scripted requests.
  * Created by smitsch on 4/13/17.
  */
class ScriptedRequestTests extends TacticTestBase {

  "Model upload" should "work with a simple file" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End.\n Problem x=0->[x:=x+1;]x=1 End."
    val request = new UploadArchiveRequest(db.db, "guest", modelContents, Some("Simple"))
    request.resultingResponses() should contain theSameElementsAs ModelUploadResponse(Some("1"), None)::Nil
    db.db.getModelList("guest").loneElement should have(
      'name ("Simple"),
      'keyFile (modelContents))
  }

  it should "report parse errors" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End.\n Problem x=0->[x:=x+1]x=1 End."
    val request = new UploadArchiveRequest(db.db, "guest", modelContents, Some("Simple"))
    val response = request.resultingResponses().loneElement
    response shouldBe a [ParseErrorResponse]
    response should have (
      'msg ("Unexpected token cannot be parsed"),
      'found ("]"),
      'expect (";")
    )
    db.db.getModelList("guest") shouldBe empty
  }

  "Proof step execution" should "make a simple step" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=0 -> x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1)) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, leaves, _, _, _, _) =>
        root should have ('goal (Some("==> x>=0 -> x>=0".asSequent)))
        leaves.loneElement should have ('goal (Some("x>=0 ==> x>=0".asSequent)))
    }
  }}

  it should "solve simple diamond ODE in context" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x, v; End. Problem x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1))
    tacticRunner("(1,0)", solve(1, 1::Nil))
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, leaves, _, _, _, _) =>
        root should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
        leaves.loneElement should have ('goal (Some("x>=0&v>=0 ==> [v:=v;]\\exists t_ (t_>=0 & v*t_+x>=0)".asSequent)))
    }
  }}

  it should "make a branching input step at a position" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=2 -> [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1))
    tacticRunner("(1,0)", loop("x>=1".asFormula)(1))
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, l1::l2::l3::Nil, _, _, _, _) =>
        root should have ('goal (Some("==> x>=2 -> [{x:=x+1;}*]x>=0".asSequent)))
        l1 should have ('goal (Some("x>=2 ==> x>=1".asSequent)))
        l2 should have ('goal (Some("x>=1 ==> x>=0".asSequent)))
        l3 should have ('goal (Some("x>=1 ==> [x:=x+1;]x>=1".asSequent)))
    }
  }}

  it should "record hiding with formula checks" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=0 -> x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", hideR(1)) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, leaves, _, _, _, _) =>
        root should have ('goal (Some("==> x>=0 -> x>=0".asSequent)))
        leaves.loneElement should have ('goal (Some(" ==> ".asSequent)))
    }
    inside (new ExtractTacticRequest(db.db, db.user.userName, proofId.toString, verbose=true).getResultingResponses(t).loneElement) {
      case GetTacticResponse(tacticText, _) => tacticText shouldBe """hideR('R=="x>=0->x>=0")"""
    }
  }}

  it should "record andR case labels" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x^2>=0 & x^4>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", andR(1)) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new ExtractTacticRequest(db.db, db.user.userName, proofId.toString, verbose=true).getResultingResponses(t).loneElement) {
      case GetTacticResponse(tacticText, _) => tacticText should equal(
        """andR('R=="x^2>=0 & x^4>=0"); <(
          |"x^2>=0": nil,
          |"x^4>=0": nil
          |)""".stripMargin) (after being whiteSpaceRemoved)
    }
  }}

  it should "record unique prop case labels" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x=3 & (x > 2 | x < -2 -> x^2>=4 & x^4>=16) End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", andR(1) <(nil, prop)) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new ExtractTacticRequest(db.db, db.user.userName, proofId.toString, verbose=true).getResultingResponses(t).loneElement) {
      case GetTacticResponse(tacticText, _) => tacticText should equal (
        // first branching tactic does not have labels because it was the user-supplied tactic andR(1) <(nil, prop)
        """andR(1); <(nil, prop); <(
          |"x=3": nil,
          |"x^2>=4//x>2": nil,
          |"x^4>=16//x>2": nil,
          |"x^4>=16//x < (-2)": nil,
          |"x^2>=4//x < (-2)": nil
          |)""".stripMargin) (after being whiteSpaceRemoved)
    }
  }}

  it should "record unique prop case labels (2)" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x=3 & (x > 2 | x < -2 -> x^2>=4 & x^4>=16) End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", andR(1))
    tacticRunner("(1,1)", prop)
    inside (new ExtractTacticRequest(db.db, db.user.userName, proofId.toString, verbose=true).getResultingResponses(t).loneElement) {
      case GetTacticResponse(tacticText, _) => tacticText should equal (
        """andR('R=="x=3&(x>2|x < (-2)->x^2>=4&x^4>=16)"); <(
          |"x=3": nil,
          |"x>2|x < (-2)->x^2>=4&x^4>=16":
          |  prop; <(
          |    "x^2>=4//x>2": nil,
          |    "x^4>=16//x>2": nil,
          |    "x^4>=16//x < (-2)": nil,
          |    "x^2>=4//x < (-2)": nil
          |  )
          |)""".stripMargin) (after being whiteSpaceRemoved)
    }
  }}

  it should "prove an easy model with loop invariant generator" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real v,x; End. Problem x>=0 -> [{v:=*;?v>=0; {x'=v}}*] x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString,
      TactixLibrary.invGenerator, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", master()) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, leaves, _, _, _, _) =>
        root should have ('goal (Some("==> x>=0 -> [{v:=*;?v>=0; {x'=v}}*] x>=0".asSequent)))
        leaves shouldBe 'empty
    }
  }}

  it should "not split formula arguments at comma in predicates or ODEs" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem [{x'=4}]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", dC("[{x'=2,y'=3}]P(x,y)".asFormula :: Nil)(1)) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, leaves, _, _, _, _) =>
        root should have ('goal (Some("==> [{x'=4}]x>=0".asSequent)))
        leaves(0) should have ('goal (Some("==> [{x'=4 & true & [{x'=2,y'=3}]P(x,y)}]x>=0".asSequent)))
        leaves(1) should have ('goal (Some("==> [{x'=4}][{x'=2,y'=3}]P(x,y)".asSequent)))
    }
  }}

  it should "split variable list arguments" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x,y; End. Problem x>0 & y>0 -> x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", BelleParser("""universalClosure("x::y::nil",1)""")) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, l0::Nil, _, _, _, _) =>
        root should have ('goal (Some("==> x>0 & y>0 -> x>=0".asSequent)))
        l0 should have ('goal (Some("==> \\forall x \\forall y (x>0 & y>0 -> x>=0)".asSequent)))
    }
  }}

  it should "split formula list arguments" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem [{x'=2}]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", BelleParser("""dC("x>=1::x>=2::nil",1)""")) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, l0::l1::l2::Nil, _, _, _, _) =>
        root should have ('goal (Some("==> [{x'=2}]x>=0".asSequent)))
        l0 should have ('goal (Some("==> [{x'=2 & (true & x>=1) & x>=2}]x>=0".asSequent)))
        l1 should have ('goal (Some("==> [{x'=2}]x>=1".asSequent)))
        l2 should have ('goal (Some("==> [{x'=2 & true & x>=1}]x>=2".asSequent)))
    }
  }}

  "Custom tactic execution" should "expand tactic definitions" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=2 -> [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTacticString(db, t, proofId)(_: String, _: String, consultAxiomInfo=false, None, None, Nil)

    tacticRunner("()", "tactic myImply as (implyR(1);nil); myImply")
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, root, l1::Nil, _, _, _, _) =>
        root should have ('goal (Some("==> x>=2 -> [{x:=x+1;}*]x>=0".asSequent)))
        l1 should have ('goal (Some("x>=2 ==> [{x:=x+1;}*]x>=0".asSequent)))
    }
  }}

  it should "record new symbols correctly" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=0 -> [{x'=1}]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map(Name("x", None) -> Signature(None, Real, None, None, UnknownLocation))))
    val proofSession = () => SessionManager.session(t)(proofId.toString).asInstanceOf[ProofSession]
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1) & cut("\\exists x0 x0=x".asFormula))
    // proof session should pick up new variable introduced by cut
    proofSession().defs.decls.keySet should contain (Name("x0", None))
    proofSession().defs.decls(Name("x0", None)) shouldBe Signature(None, Real, None, None, UnknownLocation)
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, _, leaves, _, _, _, _) =>
        leaves.flatMap(_.goal) should contain theSameElementsInOrderAs List(
          "x>=0, \\exists x0 x0=x ==> [{x'=1}]x>=0".asSequent,
          "x>=0 ==> [{x'=1}]x>=0, \\exists x0 x0=x".asSequent)
    }

    tacticRunner("(1,0)", existsL(-2) & dC("x>=x0".asFormula)(1))
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, _, leaves, _, _, _, _) =>
        leaves.flatMap(_.goal) should contain theSameElementsInOrderAs List(
          "x>=0 ==> [{x'=1}]x>=0, \\exists x0 x0=x".asSequent,
          "x>=0, x0=x ==> [{x'=1 & true&x>=x0}]x>=0".asSequent,
          "x>=0, x0=x ==> [{x'=1}]x>=x0".asSequent)
    }

    tacticRunner("(2,1)", dIRule(1))
    // proof session should not pick up elaborated variables
    proofSession().defs.decls(Name("x0", None)).domain should not be 'defined
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, _, leaves, _, _, _, _) =>
        leaves.flatMap(_.goal) should contain theSameElementsInOrderAs List(
          "x>=0 ==> [{x'=1}]x>=0, \\exists x0 x0=x".asSequent,
          "x>=0, x0=x ==> [{x'=1 & true&x>=x0}]x>=0".asSequent,
          "x>=0, x0()=x, true ==> x>=x0()".asSequent,
          "x>=0, x0()=x, true ==> [x':=1;]x'>=0".asSequent)
    }
  }}

  "Step misapplication" should "give a useful error message on non-existing sequent top-level position" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", implyR(2))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("implyR(2): applied at position 2 may point outside the positions of the goal Provable{\n==> 1:  x>=0->[x:=x+1;]x>=0\tImply\n  from\n==> 1:  x>=0->[x:=x+1;]x>=0\tImply}"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, _, leaves, _, _, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0 -> [x:=x+1;]x>=0".asSequent)))
    }
  }}

  it should "report a readable error message when useAt tactic fails unification match" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x, v; End. Problem x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", choiceb(1, 1::Nil))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("""Axiom choiceb [a;++b;]p(||)<->[a;]p(||)&[b;]p(||) cannot be applied: The shape of
                                  |  expression               [v:=v;]<{x'=v}>x>=0
                                  |  does not match axiom key [a;++b;]p(||)""".stripMargin))

    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, _, leaves, _, _, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  it should "report a readable error message when useAt tactic points outside sequent" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x, v; End. Problem x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", choiceb(2))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("Unable to execute tactic 'choiceb', cause: requirement failed: Cannot apply at undefined position 2 in sequent   ==>  x>=0&v>=0->[v:=v;]<{x'=v}>x>=0"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, _, leaves, _, _, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  it should "report a readable error message when match in tactic does not provide one for wrong position" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x, v; End. Problem x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", dG("y'=0*y+2".asDifferentialProgram, None)(1, 1::Nil))
    response shouldBe a [ErrorResponse]
    //@note dG immediately calls an ANON tactic, which is the one that actually raises the error
    response should have ('msg ("dG only applicable to box ODEs, but got [v:=v;]<{x'=v}>x>=0"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, _, leaves, _, _, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  "Step details" should "work on a simple example" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1))
    inside(new ProofTaskExpandRequest(db.db, db.user.userName, proofId.toString, "(1,0)", false).getResultingResponses(t).loneElement) {
      case ExpandTacticResponse(_, _, _, parentTactic, stepsTactic, _, _, _, _) =>
        parentTactic shouldBe "implyR"
        stepsTactic shouldBe ""
      case e: ErrorResponse if e.exn != null => fail(e.msg, e.exn)
      case e: ErrorResponse if e.exn == null => fail(e.msg)
    }
  }}

  it should "expand prop" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables Real x, y; End. Problem x>=0&y>0 -> [x:=x+y;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", prop)
    inside(new ProofTaskExpandRequest(db.db, db.user.userName, proofId.toString, "(1,0)", false).getResultingResponses(t).loneElement) {
      case ExpandTacticResponse(_, _, _, parentTactic, stepsTactic, _, _, _, _) =>
        parentTactic shouldBe "prop"
        BelleParser(stepsTactic) shouldBe BelleParser("implyR('R==\"x>=0&y>0->[x:=x+y;]x>=0\") ; andL('L==\"x>=0&y>0\")")
      case e: ErrorResponse if e.exn != null => fail(e.msg, e.exn)
      case e: ErrorResponse if e.exn == null => fail(e.msg)
    }
  }}

  it should "expand auto" in withMathematica { _ => withDatabase { db =>
    val modelContents = "ProgramVariables Real x, y, z; End. Problem x>=0&y>0&z=0 -> [x:=x+y;]x>=z End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", master())
    inside(new ProofTaskExpandRequest(db.db, db.user.userName, proofId.toString, "(1,0)", false).getResultingResponses(t).loneElement) {
      case ExpandTacticResponse(_, _, _, parentTactic, stepsTactic, _, _, _, _) =>
        parentTactic shouldBe "auto"
        BelleParser(stepsTactic) shouldBe BelleParser(
          """implyR('R=="x>=0&y>0&z=0->[x:=x+y;]x>=z");
            |andL('L=="x>=0&y>0&z=0");
            |andL('L=="y>0&z=0");
            |assignbAxiom('R=="[x:=x+y;]x>=z");
            |expandAllDefs;
            |applyEqualities;
            |QE""".stripMargin)
      case e: ErrorResponse if e.exn != null => fail(e.msg, e.exn)
      case e: ErrorResponse if e.exn == null => fail(e.msg)
    }
  }}

  it should "expand auto with branches" in withMathematica { _ => withDatabase { db =>
    val modelContents = "ProgramVariables Real x, y, z; End. Problem x>=0&y>0&z=0 -> [x:=x+y; ++ x:=x*y;]x>=z End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", master())
    inside(new ProofTaskExpandRequest(db.db, db.user.userName, proofId.toString, "(1,0)", false).getResultingResponses(t).loneElement) {
      case ExpandTacticResponse(_, _, _, parentTactic, stepsTactic, _, _, _, _) =>
        parentTactic shouldBe "auto"
        BelleParser(stepsTactic) shouldBe BelleParser(
          """implyR('R=="x>=0&y>0&z=0->[x:=x+y;++x:=x*y;]x>=z");
            |andL('L=="x>=0&y>0&z=0");
            |andL('L=="y>0&z=0");
            |step('R=="[x:=x+y;++x:=x*y;]x>=z");
            |andR('R=="[x:=x+y;]x>=z&[x:=x*y;]x>=z"); <(
            |  "[x:=x+y;]x>=z":
            |    step('R=="[x:=x+y;]x>=z");
            |    applyEqualities;
            |    QE
            |  ,
            |  "[x:=x*y;]x>=z":
            |    step('R=="[x:=x*y;]x>=z");
            |    applyEqualities;
            |    QE
            |)""".stripMargin)
      case e: ErrorResponse if e.exn != null => fail(e.msg, e.exn)
      case e: ErrorResponse if e.exn == null => fail(e.msg)
    }
  }}

  "Applicable axioms" should "not choke on wrong positions" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))

    val response = new GetApplicableAxiomsRequest(db.db, db.user.userName, proofId.toString, "()", SuccPosition(5)).
      getResultingResponses(t).loneElement
    response should have ('derivationInfos (Nil), 'suggestedInput (Map.empty))
  }

  it should "work on a simple example without input suggestion" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End. Problem x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))

    val response = new GetApplicableAxiomsRequest(db.db, db.user.userName, proofId.toString, "()", SuccPosition(1)).
      getResultingResponses(t).loneElement
    response should have (
      'derivationInfos ((DerivationInfo("implyR"), None) :: (DerivationInfo("chaseAt"), None) :: Nil),
      'suggestedInput (Map.empty))
  }

  it should "work with input suggestion" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End. Problem [{x:=x+1;}*@invariant(x>-1)]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))

    val response = new GetApplicableAxiomsRequest(db.db, db.user.userName, proofId.toString, "()", SuccPosition(1)).
      getResultingResponses(t).loneElement
    response should have (
      'derivationInfos ((DerivationInfo("loop"), None)::(DerivationInfo("[*] iterate"), None)::
        (DerivationInfo("GV"), None)::Nil),
      'suggestedInput (Map(FormulaArg("J") -> "x>-1".asFormula)))
  }

  "Tactic input checking" should "pass correct input" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End. Problem [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "J", "formula", "x>1").
      getResultingResponses(t).loneElement
    response should have ('flag (true))
  }

  it should "fail incorrect type" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End. Problem [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "J", "formula", "x").
      getResultingResponses(t).loneElement
    response should have (
      'flag (false),
      'errorText (Some("Expected: formula, found: Term x"))
    )
  }

  it should "fail fresh symbols" in withTactics { withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End. Problem [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map()))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "J", "formula", "x+y>0").
      getResultingResponses(t).loneElement
    response should have (
      'flag (false),
      'errorText (Some("argument J uses new names that do not occur in the sequent: y, is it a typo?"))
    )
  }}

  it should "allow defined functions" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End. Problem [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      FixedGenerator(Nil), Declaration(Map(Name("f", None) -> Signature(None, Real, None, Some("3+5".asTerm), null))))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "J", "formula", "x+f()>0").
      getResultingResponses(t).loneElement
    response should have ('flag (true))
  }

  it should "fail when defined functions are used without ()" in withDatabase { db =>
    val modelContents = "ProgramVariables Real x; End. Problem [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), FixedGenerator(Nil),
      Declaration(Map(Name("f", None) -> Signature(Some(edu.cmu.cs.ls.keymaerax.core.Unit), Real, None, Some("3+5".asTerm), null))))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "J", "formula", "x+f>0").
      getResultingResponses(t).loneElement
    response should have ('flag (true))
  }

  "OpenProofRequest" should "populate the invariant supplier from annotations" in withTactics { withDatabase { db =>
    val userName = "opr"
    db.db.createUser(userName, "", "1")
    val t = SessionManager.token(SessionManager.add(db.db.getUser(userName).get))
    val content =
      """Theorem "Theorem 1"
        |Definitions
        |  HP a ::= { {x:=2;}*@invariant(x=2) };
        |End.
        |ProgramVariables Real x; End.
        |Problem
        |  x>=1 -> [{ x:=x+1; a; }*@invariant(x>=0)]x>=-1
        |End.
        |Tactic "Proof"
        |  auto
        |End.
        |End.""".stripMargin
    inside(new UploadArchiveRequest(db.db, userName, content, None).getResultingResponses(t).loneElement) {
      case ModelUploadResponse(Some(id), _) =>
        inside (new CreateModelTacticProofRequest(db.db, userName, id).getResultingResponses(t).loneElement) {
          case CreatedIdResponse(proofId) =>
            inside (new OpenProofRequest(db.db, userName, proofId).getResultingResponses(t).loneElement) {
              case OpenProofResponse(_, _) =>
                val session = SessionManager.session(t)
                session(proofId).asInstanceOf[ProofSession].invSupplier match {
                  case s: ConfigurableGenerator[GenProduct] =>
                    s.products shouldBe Map(
                      "{x:=2;}*".asProgram -> (("x=2".asFormula, None)::Nil),
                      "{x:=x+1; a{|^@|};}*".asProgram -> (("x>=0".asFormula, None)::Nil),
                      "{x:=x+1; {x:=2;}*}*".asProgram -> (("x>=0".asFormula, None)::Nil)
                    )
                }
            }
        }
    }
  }}

  private def importExamplesIntoDB(db: TempDBTools): Unit = {
    val userName = "maxLevelUser"
    db.db.createUser(userName, "", "1") // industry mode - return all examples
    val t = SessionManager.token(SessionManager.add(db.db.getUser(userName).get))
    val examplesResponse = new ListExamplesRequest(db.db, userName).getResultingResponses(t).loneElement.getJson
    examplesResponse shouldBe a [JsArray]
    val urls = examplesResponse.asInstanceOf[JsArray].elements.map(_.asJsObject.fields("url").asInstanceOf[JsString].value)
    urls should have size 8 // change when ListExamplesRequest is updated
    val urlsTable = Table("url", urls:_*)
    forEvery(urlsTable) { url =>
      val content = DatabasePopulator.loadResource(url)
      val response = new UploadArchiveRequest(db.db, userName, content, None).getResultingResponses(t).loneElement
      response should have ('flag (true), 'errorText (None))
    }
  }

  "Shipped tutorial import" should "import all tutorials correctly" in withDatabase { importExamplesIntoDB }

  it should "execute all imported tutorial tactics correctly" in withMathematica { tool => withDatabase { db =>
    val userName = "maxLevelUser"
    // import all tutorials, creates user too
    importExamplesIntoDB(db)
    val t = SessionManager.token(SessionManager.add(db.db.getUser(userName).get))
    val models = new GetModelListRequest(db.db, userName, None).getResultingResponses(t).loneElement.getJson
    val modelInfos = models.asInstanceOf[JsArray].elements.
      filter(_.asJsObject.fields("hasTactic").asInstanceOf[JsBoolean].value).
      map(m => m.asJsObject.fields("name").asInstanceOf[JsString].value -> m.asJsObject.fields("id").asInstanceOf[JsString].value)
    modelInfos should have size 85  // change when ListExamplesRequest is updated

    // STTT16/Tutorial Example 10
    // FM16/Tutorial Example 5

    val modelInfosTable = Table(("name", "id"), modelInfos.filter(_._1=="FM16/Tutorial Example 5"):_*)
    forEvery(modelInfosTable) { (name, id) =>
      whenever(tool.isInitialized) {
        val start = System.currentTimeMillis()
        println("Importing and opening " + name + "...")
        val r1 = new CreateModelTacticProofRequest(db.db, userName, id).getResultingResponses(t).loneElement
        r1 shouldBe a[CreatedIdResponse]
        val proofId = r1.getJson.asJsObject.fields("id").asInstanceOf[JsString].value
        val r2 = new OpenProofRequest(db.db, userName, proofId).getResultingResponses(t).loneElement
        r2 shouldBe a[OpenProofResponse]
        val r3 = new InitializeProofFromTacticRequest(db.db, userName, proofId).getResultingResponses(t).loneElement
        r3 shouldBe a[RunBelleTermResponse]
        val nodeId = r3.getJson.asJsObject.fields("nodeId").asInstanceOf[JsString].value
        val taskId = r3.getJson.asJsObject.fields("taskId").asInstanceOf[JsString].value
        var status = "running"
        do {
          val r4 = new TaskStatusRequest(db.db, userName, proofId, nodeId, taskId).getResultingResponses(t).loneElement
          r4 shouldBe a[TaskStatusResponse]
          status = r4.getJson.asJsObject.fields("status").asInstanceOf[JsString].value
        } while (status != "done")
        new TaskResultRequest(db.db, userName, proofId, nodeId, taskId).getResultingResponses(t).loneElement match {
          case _: TaskResultResponse => // ok
          case e: ErrorResponse => fail(e.msg, e.exn)
        }
        val r5 = new GetAgendaAwesomeRequest(db.db, userName, proofId).getResultingResponses(t).loneElement
        r5 shouldBe a[AgendaAwesomeResponse]
        val entry = ArchiveParser.parse(db.db.getModel(id).keyFile).head
        BelleParser.parseWithInvGen(db.db.getModel(id).tactic.get, None, entry.defs) match {
          case _: PartialTactic =>
            r5.getJson.asJsObject.fields("closed").asInstanceOf[JsBoolean].value shouldBe false withClue "closed"
          case _ =>
            r5.getJson.asJsObject.fields("agendaItems").asJsObject.getFields() shouldBe empty
            r5.getJson.asJsObject.fields("closed").asInstanceOf[JsBoolean].value shouldBe true withClue "closed"
            val r6 = new CheckIsProvedRequest(db.db, userName, proofId).getResultingResponses(t).loneElement
            r6 shouldBe a [ProofVerificationResponse] withClue r6.getJson.prettyPrint
            r6.getJson.asJsObject.fields("proofId").asInstanceOf[JsString].value shouldBe proofId
            r6.getJson.asJsObject.fields("isProved").asInstanceOf[JsBoolean].value shouldBe true withClue "isProved"
            val extractedTacticString = r6.getJson.asJsObject.fields("tactic").asInstanceOf[JsString].value
            // double check extracted tactic
            println("Reproving extracted tactic...")
            val extractedTactic = BelleParser.parseWithInvGen(extractedTacticString, None, entry.defs)
            proveBy(entry.model.asInstanceOf[Formula], extractedTactic, defs = entry.defs) shouldBe 'proved
            println("Done reproving")
        }
        println("Done (" + (System.currentTimeMillis()-start)/1000 + "s)")
      }
    }
  }}

  private def runTactic(db: TempDBTools, token: SessionToken, proofId: Int)(nodeId: String, tactic: BelleExpr): Response = {
    def createInputs(name: String, inputs: Seq[Any]): Seq[BelleTermInput] = {
      val info = DerivationInfo(name)
      val expectedInputs = info.inputs
      inputs.zipWithIndex.flatMap({
        case (in: Expression, i) => Some(BelleTermInput(in.prettyString, Some(expectedInputs(i))))
        case (es: List[Expression], i) => Some(BelleTermInput(es.map(_.prettyString).mkString(","), Some(expectedInputs(i))))
        case (_: Generator[GenProduct], _) => None //@todo pass on once supported
        case (Some(e: Expression), i) => Some(BelleTermInput(e.prettyString, Some(expectedInputs(i))))
        case (Some(es: List[Expression]), i) => Some(BelleTermInput(es.map(_.prettyString).mkString(","), Some(expectedInputs(i))))
        case (None, _) => None
        case (in, i) => Some(BelleTermInput(in.toString, Some(expectedInputs(i))))
      })
    }

    val (tacticString: String, inputs: List[BelleTermInput], pos1: Option[PositionLocator],
         pos2: Option[PositionLocator], consultAxiomInfo: Boolean) = tactic match {
      case AppliedPositionTactic(t, p) => (t.prettyString, Nil, Some(p), None, true)
      case t: AppliedDependentPositionTactic => t.pt match {
        case inner: DependentPositionWithAppliedInputTactic =>
          if (inner.inputs.isEmpty) (inner.name, Nil, Some(t.locator), None, true)
          else (inner.name, createInputs(inner.name, inner.inputs), Some(t.locator), None, true)
        case _ => (t.pt.name, Nil, Some(t.locator), None, true)
      }
      case NamedTactic(name, _) => (name, Nil, None, None, true)
      case InputTactic(name, inputs) => (name, createInputs(name, inputs), None, None, true)
      case t: AppliedDependentPositionTacticWithAppliedInput => t.pt match {
        case inner: DependentPositionWithAppliedInputTactic =>
          if (inner.inputs.isEmpty) (inner.name, Nil, Some(t.locator), None, true)
          else (inner.name, createInputs(inner.name, inner.inputs), Some(t.locator), None, true)
        case _ => (t.pt.name, Nil, Some(t.locator), None, true)
      }
      case t => (BellePrettyPrinter(t), Nil, None, None, false)
    }
    runTacticString(db, token, proofId)(nodeId, tacticString, consultAxiomInfo, pos1, pos2, inputs)
  }

  private def runTacticString(db: TempDBTools, token: SessionToken, proofId: Int)
                             (nodeId: String, tactic: String, consultAxiomInfo: Boolean,
                              pos1: Option[PositionLocator], pos2: Option[PositionLocator],
                              inputs: List[BelleTermInput]): Response = {
    val proofIdString = proofId.toString
    val request = new RunBelleTermRequest(db.db, db.user.userName, proofIdString, nodeId, tactic, pos1, pos2, inputs,
      consultAxiomInfo = consultAxiomInfo)
    request.getResultingResponses(token).loneElement match {
      case response: RunBelleTermResponse =>
        response should have (
          'proofId (proofIdString),
          'nodeId (nodeId)
        )
        val taskId = response.asInstanceOf[RunBelleTermResponse].taskId
        while (new TaskStatusRequest(db.db, db.user.userName, proofIdString, nodeId, taskId).getResultingResponses(token).
          loneElement.asInstanceOf[TaskStatusResponse].status == "running") {
          Thread.sleep(100)
        }
        new TaskStatusRequest(db.db, db.user.userName, proofIdString, nodeId, taskId).getResultingResponses(token).loneElement should have ('status ("done"))
        new TaskResultRequest(db.db, db.user.userName, proofIdString, nodeId, taskId).getResultingResponses(token).loneElement
      case response: ErrorResponse if response.exn != null => fail(response.msg, response.exn)
      case response: ErrorResponse if response.exn == null => fail(response.msg)
      case response => fail("Running tactic failed with response " + response)
    }
  }

}
