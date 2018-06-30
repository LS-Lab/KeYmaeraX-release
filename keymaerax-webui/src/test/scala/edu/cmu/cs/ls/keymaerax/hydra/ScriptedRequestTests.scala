package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.{DerivationInfo, FixedGenerator, FormulaArg, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Real}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXDeclarationsParser.Declaration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
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
    val modelContents = "ProgramVariables. R x. End.\n Problem. x=0->[x:=x+1;]x=1 End."
    val request = new CreateModelRequest(db.db, "guest", "Simple", modelContents)
    request.resultingResponses() should contain theSameElementsAs ModelUploadResponse(Some("1"), None)::Nil
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
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1)) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, root, leaves, _, _) =>
        root should have ('goal (Some("==> x>=0 -> x>=0".asSequent)))
        leaves.loneElement should have ('goal (Some("x>=0 ==> x>=0".asSequent)))
    }
  }}

  it should "solve simple diamond ODE in context" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. R v. End. Problem. x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1))
    tacticRunner("(1,0)", solve(1, 1::Nil))
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, root, leaves, _, _) =>
        root should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
        leaves.loneElement should have ('goal (Some("x>=0&v>=0 ==> [v:=v;]\\exists t_ (t_>=0 & v*t_+x>=0)".asSequent)))
    }
  }}

  it should "make a branching input step at a position" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=2 -> [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1))
    tacticRunner("(1,0)", loop("x>=1".asFormula)(1))
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, root, l1::l2::l3::Nil, _, _) =>
        root should have ('goal (Some("==> x>=2 -> [{x:=x+1;}*]x>=0".asSequent)))
        l1 should have ('goal (Some("x>=2 ==> x>=1".asSequent)))
        l2 should have ('goal (Some("x>=1 ==> x>=0".asSequent)))
        l3 should have ('goal (Some("x>=1 ==> [x:=x+1;]x>=1".asSequent)))
    }
  }}

  it should "record hiding with formula checks" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", hideR(1)) should have (
      'proofId (proofId.toString),
      'parent (DbProofTree(db.db, proofId.toString).root),
      'progress (true)
    )
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, root, leaves, _, _) =>
        root should have ('goal (Some("==> x>=0 -> x>=0".asSequent)))
        leaves.loneElement should have ('goal (Some(" ==> ".asSequent)))
    }
    inside (new ExtractTacticRequest(db.db, proofId.toString).getResultingResponses(t).loneElement) {
      case ExtractTacticResponse(tacticText) => tacticText shouldBe "hideR(1=={`x>=0->x>=0`})"
    }
  }}

  "Custom tactic execution" should "expand tactic definitions" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=2 -> [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTacticString(db, t, proofId)(_: String, _: String, consultAxiomInfo=false, None, None, Nil)

    tacticRunner("()", "tactic myImply as (implyR(1);nil); myImply")
    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, root, l1::Nil, _, _) =>
        root should have ('goal (Some("==> x>=2 -> [{x:=x+1;}*]x>=0".asSequent)))
        l1 should have ('goal (Some("x>=2 ==> [{x:=x+1;}*]x>=0".asSequent)))
    }
  }

  "Step misapplication" should "give a useful error message on non-existing sequent top-level position" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", implyR(2))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("Tactic failed with error: [Bellerophon Runtime] Position Fixed(2,None,true) may point outside the positions of the goal ElidingProvable(Provable{\n==> 1:  x>=0->[x:=x+1;]x>=0\tImply\n  from\n==> 1:  x>=0->[x:=x+1;]x>=0\tImply})"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, leaves, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0 -> [x:=x+1;]x>=0".asSequent)))
    }
  }

  it should "report a readable error message when useAt tactic fails unification match" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. R v. End. Problem. x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", choiceb(1, 1::Nil))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("Tactic failed with error: [Bellerophon Runtime] Tactic choiceb(1.1) is not applicable for\n    [v:=v;]<{x'=v&true}>x>=0\nat position Fixed(1.1,None,true)\nbecause No substitution found by unification, try to patch locally with own substitution"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, leaves, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  it should "report a readable error message when useAt tactic points outside sequent" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. R v. End. Problem. x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", choiceb(2))
    response shouldBe a [ErrorResponse]
    response should have ('msg ("Tactic failed with error: [Bellerophon Runtime] Tactic choiceb(2) is not applicable for\n    position outside sequent: expected -1...-0 or 1...1\nat position Fixed(2,None,true)\nbecause requirement failed: Cannot apply at undefined position 2 in sequent   ==>  x>=0&v>=0->[v:=v;]<{x'=v&true}>x>=0"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, leaves, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  it should "report a readable error message when match in tactic does not provide one for wrong position" in withDatabase { db => withMathematica { _ =>
    val modelContents = "ProgramVariables. R x. R v. End. Problem. x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    val response = tacticRunner("()", dG("y'=0*y+2".asDifferentialProgram, None)(1, 1::Nil))
    response shouldBe a [ErrorResponse]
    //@note dG immediately calls an ANON tactic, which is the one that actually raises the error
    response should have ('msg ("Tactic failed with error: [Bellerophon Runtime] Tactic ANON(1.1) is not applicable for\n    [v:=v;]<{x'=v&true}>x>=0\nat position Fixed(1.1,None,true)\nbecause Some([v:=v;]<{x'=v&true}>x>=0) (of class scala.Some)"))

    inside (new GetAgendaAwesomeRequest(db.db, db.user.userName, proofId.toString).getResultingResponses(t).loneElement) {
      case AgendaAwesomeResponse(_, _, leaves, _, _) =>
        leaves.loneElement should have ('goal (Some("==> x>=0&v>=0 -> [v:=v;]<{x'=v}>x>=0".asSequent)))
    }
  }}

  "Step details" should "work on a simple example" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", implyR(1))
    inside(new ProofTaskExpandRequest(db.db, db.user.userName, proofId.toString, "()").getResultingResponses(t).loneElement) {
      case ExpandTacticResponse(_, parentTactic, stepsTactic, _, _) =>
        parentTactic shouldBe "implyR"
        stepsTactic shouldBe ""
    }
  }

  it should "expand prop" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. R y. End. Problem. x>=0&y>0 -> [x:=x+y;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", prop)
    inside(new ProofTaskExpandRequest(db.db, db.user.userName, proofId.toString, "()").getResultingResponses(t).loneElement) {
      case ExpandTacticResponse(_, parentTactic, stepsTactic, _, _) =>
        parentTactic shouldBe "prop"
        stepsTactic shouldBe "implyR(1) ; andL(-1)"
    }
  }

  it should "expand master" in withMathematica { _ => withDatabase { db =>
    val modelContents = "ProgramVariables. R x. R y. End. Problem. x>=0&y>0 -> [x:=x+y;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))
    val tacticRunner = runTactic(db, t, proofId) _

    tacticRunner("()", master())
    inside(new ProofTaskExpandRequest(db.db, db.user.userName, proofId.toString, "()").getResultingResponses(t).loneElement) {
      case ExpandTacticResponse(_, parentTactic, stepsTactic, _, _) =>
        parentTactic shouldBe "master"
        stepsTactic shouldBe "implyR(1) ; andL(-1) ; step(1) ; QE"
    }
  }}

  "Applicable axioms" should "not choke on wrong positions" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))

    val response = new GetApplicableAxiomsRequest(db.db, db.user.userName, proofId.toString, "()", SuccPosition(5)).
      getResultingResponses(t).loneElement
    response should have ('derivationInfos (Nil), 'suggestedInput (Map.empty))
  }

  it should "work on a simple example without input suggestion" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. x>=0 -> [x:=x+1;]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))

    val response = new GetApplicableAxiomsRequest(db.db, db.user.userName, proofId.toString, "()", SuccPosition(1)).
      getResultingResponses(t).loneElement
    response should have ('derivationInfos ((DerivationInfo("implyR"), None)::Nil), 'suggestedInput (Map.empty))
  }

  it should "work with input suggestion" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. [{x:=x+1;}*@invariant(x>-1)]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))

    val response = new GetApplicableAxiomsRequest(db.db, db.user.userName, proofId.toString, "()", SuccPosition(1)).
      getResultingResponses(t).loneElement
    response should have (
      'derivationInfos ((DerivationInfo("loop"), None)::(DerivationInfo("[*] iterate"), None)::
        (DerivationInfo("GV"), None)::(DerivationInfo("boxd"), None)::Nil),
      'suggestedInput (Map(FormulaArg("j(x)") -> "x>-1".asFormula)))
  }

  "Tactic input checking" should "pass correct input" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "j(x)", "formula", "x>1").
      getResultingResponses(t).loneElement
    response should have ('flag (true))
  }

  it should "fail incorrect type" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "j(x)", "formula", "x").
      getResultingResponses(t).loneElement
    response should have (
      'flag (false),
      'errorText (Some("Expected formula, but got Term x"))
    )
  }

  it should "fail fresh symbols" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil), Declaration(Map()))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "j(x)", "formula", "x+y>0").
      getResultingResponses(t).loneElement
    response should have (
      'flag (false),
      'errorText (Some("Argument j(x) uses new names that do not occur in the sequent: y, is it a typo?"))
    )
  }

  it should "allow defined functions" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      Declaration(Map(("f", None) -> (None, Real, Some("3+5".asTerm), null))))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "j(x)", "formula", "x+f()>0").
      getResultingResponses(t).loneElement
    response should have ('flag (true))
  }

  it should "fail when defined functions are used without ()" in withDatabase { db =>
    val modelContents = "ProgramVariables. R x. End. Problem. [{x:=x+1;}*]x>=0 End."
    val proofId = db.createProof(modelContents)
    val t = SessionManager.token(SessionManager.add(db.user))
    SessionManager.session(t) += proofId.toString -> ProofSession(proofId.toString, FixedGenerator(Nil),
      Declaration(Map(("f", None) -> (None, Real, Some("3+5".asTerm), null))))

    val response = new CheckTacticInputRequest(db.db, db.user.userName, proofId.toString, "()", "loop", "j(x)", "formula", "x+f>0").
      getResultingResponses(t).loneElement
    response should have (
      'flag (false),
      'errorText (Some("Argument j(x) uses new names that do not occur in the sequent: f, is it a typo?"))
    )
  }

  private def importExamplesIntoDB(db: TempDBTools) = {
    val userName = "maxLevelUser"
    db.db.createUser(userName, "", "1") // industry mode - return all examples
    val t = SessionManager.token(SessionManager.add(db.db.getUser(userName).get))
    val examplesResponse = new ListExamplesRequest(db.db, userName).getResultingResponses(t).loneElement.getJson
    examplesResponse shouldBe a [JsArray]
    val urls = examplesResponse.asInstanceOf[JsArray].elements.map(_.asJsObject.fields("url").asInstanceOf[JsString].value)
    urls should have size 5 // change when ListExamplesRequest is updated
    val urlsTable = Table("url", urls:_*)
    forEvery(urlsTable) { (url) =>
      val response = new ImportExampleRepoRequest(db.db, userName, url).getResultingResponses(t).loneElement
      response should have ('flag (true), 'errorText (None))
    }
  }

  "Shipped tutorial import" should "import all tutorials correctly" in withDatabase { importExamplesIntoDB }

  it should "execute all imported tutorial tactics correctly" in withMathematica { _ => withDatabase { db =>
    val userName = "maxLevelUser"
    // import all tutorials, creates user too
    importExamplesIntoDB(db)
    val t = SessionManager.token(SessionManager.add(db.db.getUser(userName).get))
    val models = new GetModelListRequest(db.db, userName).getResultingResponses(t).loneElement.getJson
    val modelInfos = models.asInstanceOf[JsArray].elements.
      filter(_.asJsObject.fields("hasTactic").asInstanceOf[JsBoolean].value).
      map(m => m.asJsObject.fields("name").asInstanceOf[JsString].value -> m.asJsObject.fields("id").asInstanceOf[JsString].value)
    modelInfos should have size 59  // change when ListExamplesRequest is updated
    val modelInfosTable = Table(("name", "id"), modelInfos:_*)
    forEvery(modelInfosTable) { (name, id) =>
      println("Importing and opening " + name + "...")
      val r1 = new CreateModelTacticProofRequest(db.db, userName, id).getResultingResponses(t).loneElement
      r1 shouldBe a[CreatedIdResponse]
      val proofId = r1.getJson.asJsObject.fields("id").asInstanceOf[JsString].value
      val r2 = new OpenProofRequest(db.db, userName, proofId).getResultingResponses(t).loneElement
      r2 shouldBe a [OpenProofResponse]
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
      BelleParser(db.db.getModel(id).tactic.get) match {
        case _: PartialTactic =>
          r5.getJson.asJsObject.fields("closed").asInstanceOf[JsBoolean].value shouldBe false
        case _ =>
          r5.getJson.asJsObject.fields("agendaItems").asJsObject.getFields() shouldBe empty
          r5.getJson.asJsObject.fields("closed").asInstanceOf[JsBoolean].value shouldBe true
          val r6 = new CheckIsProvedRequest(db.db, userName, proofId).getResultingResponses(t).loneElement
          r6 shouldBe a[ProofVerificationResponse]
          r6.getJson.asJsObject.fields("proofId").asInstanceOf[JsString].value shouldBe proofId
          r6.getJson.asJsObject.fields("isProved").asInstanceOf[JsBoolean].value shouldBe true
          // double check extracted tactic
          println("Reproving extracted tactic...")
          val extractedTactic = BelleParser(r6.getJson.asJsObject.fields("tactic").asInstanceOf[JsString].value)
          proveBy(KeYmaeraXArchiveParser.parse(db.db.getModel(id).keyFile).head.model.asInstanceOf[Formula],
            extractedTactic) shouldBe 'proved
      }
      println("Done")
    }
  }}

  private def runTactic(db: TempDBTools, token: SessionToken, proofId: Int)(nodeId: String, tactic: BelleExpr): Response = {
    val (tacticString: String, inputs: List[BelleTermInput], pos1: Option[PositionLocator], pos2: Option[PositionLocator]) = tactic match {
      case AppliedPositionTactic(t, p) => (t.prettyString, Nil, Some(p), None)
      case t: AppliedDependentPositionTactic => t.pt match {
        case inner: DependentPositionWithAppliedInputTactic if inner.inputs.isEmpty =>
          (inner.name, Nil, Some(t.locator), None)
        case inner: DependentPositionWithAppliedInputTactic if inner.inputs.nonEmpty =>
          val info = DerivationInfo(t.pt.name)
          val expectedInputs = info.inputs
          val inputs = inner.inputs.zipWithIndex.map({
            case (in: Expression, i) => BelleTermInput(in.prettyString, Some(expectedInputs(i)))
            case (in, i) => BelleTermInput(in.toString, Some(expectedInputs(i)))
          })
          (inner.name, inputs, Some(t.locator), None)
        case _ => (t.pt.name, Nil, Some(t.locator), None)
      }
      case NamedTactic(name, _) => (name, Nil, None, None)
      //@todo extend on demand
    }
    runTacticString(db, token, proofId)(nodeId, tacticString, consultAxiomInfo = true, pos1, pos2, inputs)
  }

  private def runTacticString(db: TempDBTools, token: SessionToken, proofId: Int)
                             (nodeId: String, tactic: String, consultAxiomInfo: Boolean,
                              pos1: Option[PositionLocator], pos2: Option[PositionLocator],
                              inputs: List[BelleTermInput]): Response = {
    val proofIdString = proofId.toString
    val request = new RunBelleTermRequest(db.db, db.user.userName, proofIdString, nodeId, tactic, pos1, pos2, inputs,
      consultAxiomInfo = consultAxiomInfo)
    val response = request.getResultingResponses(token).loneElement
    response shouldBe a [RunBelleTermResponse]
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
  }

}
