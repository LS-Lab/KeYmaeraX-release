package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.{DerivationInfo, FixedGenerator, FormulaArg, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.LoneElement._
import org.scalatest.Inside._

/**
  * Tests the server-side web API with scripted requests.
  * Created by smitsch on 4/13/17.
  */
class ScriptedRequestTests extends TacticTestBase {

  "Model upload" should "work with a simple file" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End.\n Problem. x=0->[x:=x+1;]x=1 End."
    val request = new CreateModelRequest(db.db, "guest", "Simple", modelContents)
    request.resultingResponses() should contain theSameElementsAs BooleanResponse(flag=true)::Nil
    db.db.getModelList("guest").loneElement should have(
      'name ("Simple"),
      'keyFile (modelContents))
  }

  it should "report parse errors" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End.\n Problem. x=0->[x:=x+1]x=1 End."
    val request = new CreateModelRequest(db.db, "guest", "Simple", modelContents)
    val response = request.resultingResponses().loneElement
    response shouldBe a [ParseErrorResponse]
    response should have (
      'msg ("Unexpected token cannot be parsed"),
      'found ("] (RBOX$)"),
      'expect ("; (SEMI$)")
    )
    db.db.getModelList("guest") shouldBe empty
  }

  "Proof step execution" should "make a simple step" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1)) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, root, leaves, _, _) =>
        root should have ('goal (Some("==> x>=0 -> x>=0".asSequent)))
        leaves.loneElement should have ('goal (Some("x>=0 ==> x>=0".asSequent)))
    }
  }}

  it should "solve simple diamond ODE in context" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. R v. End. Problem. x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1))
    tacticRunner("(1,0)", solve(1, 1::Nil))
    inside (new GetAgendaAwesomeRequest(db.db, db.user, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, root, leaves, _, _) =>
        root should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
        leaves.loneElement should have ('goal (Some("x>=0&v>=0 ==> [v:=v;]\\exists t_ (t_>=0 & v*t_+x>=0)".asSequent)))
    }
  }}

  "Step misapplication" should "give a useful error message on non-existing sequent top-level position" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", implyR(2))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("Tactic failed with error: [Bellerophon Runtime] Position Fixed(2,None,true) may point outside the positions of the goal NoProofTermProvable(Provable(==> 1:  x>=0->[x:=x+1;]x>=0\tImply\n  from   ==> 1:  x>=0->[x:=x+1;]x>=0\tImply))"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, leaves, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0 -> [x:=x+1;]x>=0".asSequent)))
    }
  }

  it should "report a readable error message when useAt tactic fails unification match" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. R v. End. Problem. x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", choiceb(1, 1::Nil))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("Tactic failed with error: [Bellerophon Runtime] Tactic choiceb(1.1) may point to wrong position, found Some([v:=v;]<{x'=v&true}>x>=0) at position Fixed(1.1,None,true)"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, leaves, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  it should "report a readable error message when useAt tactic points outside sequent" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. R v. End. Problem. x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", choiceb(2))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("Tactic failed with error: [Bellerophon Runtime] Tactic choiceb(2) may point to wrong position, found None at position Fixed(2,None,true)"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, leaves, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  it should "report a readable error message when match in tactic does not provide one for wrong position" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. R v. End. Problem. x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", dG("y'=0*y+2".asDifferentialProgram, None)(1, 1::Nil))
    response shouldBe a [ErrorResponse]
    //@note dG immediately calls an ANON tactic, which is the one that actually raises the error
    response should have ('msg ("Tactic failed with error: [Bellerophon Runtime] Tactic ANON({`y`},{`0`},{`2`},1.1) may point to wrong position, found Some([v:=v;]<{x'=v&true}>x>=0) at position Fixed(1.1,None,true)"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, leaves, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  "Step details" should "work on a simple example" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1))
    inside(new ProofTaskExpandRequest(db.db, db.user, proofId.toString, "()").getResultingResponses(t).loneElement) {
      case ExpandTacticResponse(_, tactic, _, _, _) =>
        tactic shouldBe "implyR"
    }
  }

  "Applicable axioms" should "not choke on wrong positions" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)

    val response = new GetApplicableAxiomsRequest(db.db, db.user, proofId.toString, "()", SuccPosition(5)).
      getResultingResponses(t).loneElement
    response should have ('derivationInfos (Nil), 'suggestedInput (Map.empty))
  }

  it should "work on a simple example without input suggestion" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)

    val response = new GetApplicableAxiomsRequest(db.db, db.user, proofId.toString, "()", SuccPosition(1)).
      getResultingResponses(t).loneElement
    response should have ('derivationInfos ((DerivationInfo("implyR"), None)::Nil), 'suggestedInput (Map.empty))
  }

  it should "work with input suggestion" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. [{x:=x+1;}*@invariant(x>-1)]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Nil)

    val response = new GetApplicableAxiomsRequest(db.db, db.user, proofId.toString, "()", SuccPosition(1)).
      getResultingResponses(t).loneElement
    response should have (
      'derivationInfos ((DerivationInfo("loop"), None)::(DerivationInfo("[*] iterate"), None)::
        (DerivationInfo("GV"), None)::(DerivationInfo("MR"), None)::Nil),
      'suggestedInput (Map(FormulaArg("j(x)") -> "x>-1".asFormula)))
  }

  private def runTactic(db: DbTacticTester, token: SessionToken, proofId: Int)(nodeId: String, tactic: BelleExpr): Response = {
    val (tacticString: String, inputs: List[BelleTermInput], pos1: Option[PositionLocator], pos2: Option[PositionLocator]) = tactic match {
      case AppliedPositionTactic(t, p) => (t.prettyString, Nil, Some(p), None)
      case t: AppliedDependentPositionTactic => t.pt match {
        case inner: DependentPositionWithAppliedInputTactic =>
          val info = DerivationInfo(t.pt.name)
          val expectedInputs = info.inputs
          val inputs = inner.inputs.zipWithIndex.map({ case (in, i) => BelleTermInput(in.prettyString, Some(expectedInputs(i))) })
          (inner.name, inputs, Some(t.locator), None)
        case _ => (t.pt.name, Nil, Some(t.locator), None)
      }
      //@todo extend on demand
    }
    val proofIdString = proofId.toString
    val request = new RunBelleTermRequest(db.db, db.user, proofIdString, nodeId, tacticString, pos1, pos2, inputs)
    val response = request.getResultingResponses(token).loneElement
    response shouldBe a [RunBelleTermResponse]
    response should have (
      'proofId (proofIdString),
      'nodeId (nodeId)
    )
    val taskId = response.asInstanceOf[RunBelleTermResponse].taskId
    while (new TaskStatusRequest(db.db, db.user, proofIdString, nodeId, taskId).getResultingResponses(token).
      loneElement.asInstanceOf[TaskStatusResponse].status == "running") {
      Thread.sleep(100)
    }
    new TaskStatusRequest(db.db, db.user, proofIdString, nodeId, taskId).getResultingResponses(token).loneElement should have ('status ("done"))
    new TaskResultRequest(db.db, db.user, proofIdString, nodeId, taskId).getResultingResponses(token).loneElement
  }

}
