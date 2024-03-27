/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.restapi

import akka.http.scaladsl.server.Route
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import spray.json._
import edu.cmu.cs.ls.keymaerax.core.Formula
import akka.http.scaladsl.server.Directives._
import edu.cmu.cs.ls.keymaerax.infrastruct.Position

import edu.cmu.cs.ls.keymaerax.hydra.RestApi.{
  completeRequest,
  completeResponse,
  database,
  standardCompletion,
  userPrefix,
}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.hydra.requests.proofs._

import scala.language.postfixOps

object Proofs {

  val deleteModelProofSteps: SessionToken => Route = (t: SessionToken) =>
    userPrefix { userId =>
      pathPrefix("model" / Segment / "deleteProofSteps") { modelId =>
        pathEnd {
          post {
            val r = new DeleteModelProofStepsRequest(database, userId, modelId)
            completeRequest(r, t)
          }
        }
      }
    }

  val deleteProof: SessionToken => Route = (t: SessionToken) =>
    userPrefix { userId =>
      pathPrefix("proof" / Segment / "delete") { proofId =>
        pathEnd {
          post {
            val r = new DeleteProofRequest(database, userId, proofId)
            completeRequest(r, t)
          }
        }
      }
    }

  val modelTactic: SessionToken => Route = (t: SessionToken) =>
    path("user" / Segment / "model" / Segment / "tactic") { (userId, modelId) =>
      pathEnd {
        get {
          val request = new GetModelTacticRequest(database, userId, modelId)
          completeRequest(request, t)
        } ~ post {
          entity(as[String]) { contents =>
            {
              val request = new AddModelTacticRequest(database, userId, modelId, contents)
              completeRequest(request, t)
            }
          }
        }
      }
    }

  /** Extracts and stores a tactic from the recorded proof steps. */
  val extractTactic: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "extract" / Map("verbose" -> true, "succinct" -> false)) {
      (userName, proofId, verbose) =>
        {
          pathEnd {
            get {
              val request = new ExtractTacticRequest(database, userName, proofId, verbose)
              completeRequest(request, t)
            }
          }
        }
    }

  /** Reads a previously extracted tactic. */
  val getTactic: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "tactic") { (userName, proofId) =>
      {
        pathEnd {
          get {
            val request = new GetTacticRequest(database, userName, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val tacticDiff: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "tacticDiff") { (_, proofId) =>
      {
        pathEnd {
          post {
            entity(as[String]) { contents =>
              {
                val tactics = contents.parseJson.asJsObject
                val request = new TacticDiffRequest(
                  database,
                  proofId,
                  tactics.fields("old").asInstanceOf[JsString].value,
                  tactics.fields("new").asInstanceOf[JsString].value,
                )
                completeRequest(request, t)
              }
            }
          }
        }
      }
    }

  val extractLemma: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "lemma") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new ExtractLemmaRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val downloadProblemSolution: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "download") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new ExtractProblemSolutionRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val downloadModelProofs: SessionToken => Route = (t: SessionToken) =>
    path("models" / "user" / Segment / "model" / Segment / "downloadProofs") { (userId, modelId) =>
      {
        pathEnd {
          get {
            val request = new ExtractModelSolutionsRequest(
              database,
              userId,
              Integer.parseInt(modelId) :: Nil,
              withProofs = true,
              exportEmptyProof = true,
            )
            completeRequest(request, t)
          }
        }
      }
    }

  val downloadAllProofs: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / "downloadAllProofs") { userId =>
      {
        pathEnd {
          get {
            // @note potential performance bottleneck: loads all models just to get ids
            val allModels = database.getModelList(userId).map(_.modelId)
            val request =
              new ExtractModelSolutionsRequest(database, userId, allModels, withProofs = true, exportEmptyProof = false)
            completeRequest(request, t)
          }
        }
      }
    }

  val createProof: SessionToken => Route = (t: SessionToken) =>
    path("models" / "users" / Segment / "model" / Segment / "createProof") { (userId, modelId) =>
      {
        pathEnd {
          post {
            entity(as[String]) { x =>
              {
                val obj = x.parseJson
                val submittedProofName = obj.asJsObject.getFields("proofName").last.asInstanceOf[JsString].value
                val proofDescription = obj.asJsObject.getFields("proofDescription").last.asInstanceOf[JsString].value
                val request = new CreateProofRequest(database, userId, modelId, submittedProofName, proofDescription)
                completeRequest(request, t)
              }
            }
          }
        }
      }
    }

  val openOrCreateLemmaProof: SessionToken => Route = (t: SessionToken) =>
    path("models" / "users" / Segment / "model" / Segment / "openOrCreateLemmaProof") { (userId, modelName) =>
      {
        pathEnd {
          post {
            entity(as[String]) { x =>
              {
                val obj = x.parseJson
                val parentProofId = obj.asJsObject.getFields("parentProofId").last.asInstanceOf[JsString].value
                val parentTaskId = obj.asJsObject.getFields("parentTaskId").last.asInstanceOf[JsString].value

                val request =
                  new OpenOrCreateLemmaProofRequest(database, userId, modelName, parentProofId, parentTaskId)
                completeRequest(request, t)
              }
            }
          }
        }
      }
    }

  val createModelTacticProof: SessionToken => Route = (t: SessionToken) =>
    path("models" / "users" / Segment / "model" / Segment / "createTacticProof") { (userId, modelId) =>
      {
        pathEnd {
          post {
            entity(as[String]) { _ =>
              {
                val request = new CreateModelTacticProofRequest(database, userId, modelId)
                completeRequest(request, t)
              }
            }
          }
        }
      }
    }

  val proofListForModel: SessionToken => Route = (t: SessionToken) =>
    path("models" / "users" / Segment / "model" / Segment / "proofs") { (userId, modelId) =>
      {
        pathEnd {
          get {
            val request = new ProofsForModelRequest(database, userId, modelId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofList: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "users" / Segment) { userId =>
      {
        pathEnd {
          get {
            val request = new ProofsForUserRequest(database, userId)
            completeRequest(request, t)
          }
        }
      }
    }

  val userLemmas: SessionToken => Route = (t: SessionToken) =>
    path("lemmas" / "users" / Segment) { userId =>
      {
        pathEnd {
          get {
            val request = new UserLemmasRequest(database, userId)
            completeRequest(request, t)
          }
        }
      }
    }

  val openProof: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment) { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new OpenProofRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val initProofFromTactic: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "initfromtactic") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new InitializeProofFromTacticRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val getProofLemmas: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "usedLemmas") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new GetProofLemmasRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val browseProofRoot: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "browseagenda") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new GetProofRootAgendaRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val browseNodeChildren: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "browseChildren") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new GetProofNodeChildrenRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofTasksNew: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "agendaawesome") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new GetAgendaAwesomeRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofTasksNode: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "node") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new ProofTaskNodeRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofTasksParent: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "parent") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new ProofTaskParentRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofTasksPathAll: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "pathall") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = GetPathAllRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofTasksBranchRoot: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "branchroot") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = GetBranchRootRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofTaskExpand: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "expand") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            parameters(Symbol("strict").as[Boolean]) { strict =>
              val request = new ProofTaskExpandRequest(database, userId, proofId, nodeId, strict)
              completeRequest(request, t)
            }
          }
        }
      }
    }

  val proofNodeSequent: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "sequent") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new ProofNodeSequentRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val stepwiseTrace: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "trace") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new StepwiseTraceRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  /* Strictly positive position = SuccPosition, strictly negative = AntePosition, 0 not used */
  def parseFormulaId(id: String): Position = {
    val positionStringParts = id.split(',').toList
    val idx :: inExprs = positionStringParts.map(str =>
      try { str.toInt }
      catch {
        case _: NumberFormatException =>
          // HACK: if position is top-level (no inExpr) and unspecified, then "Hint" web ui was probably used. In this case, assume top-level succ.
          // @todo This is a hack that *should* be fixed in the front-end by telling the "Hint: ...|...|...|" portion of the web ui to please specify a position. See sequent.js and collapsiblesequent.html
          if (str.equals("null") && positionStringParts.length == 1) 1
          else throw new Exception("Invalid formulaId " + str + " when parsing positions")
      }
    )

    try { Position(idx, inExprs) }
    catch {
      case e: IllegalArgumentException => throw new Exception("Invalid formulaId " + id + " in axiomList").initCause(e)
    }
  }

  val axiomList: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "list") { (userId, proofId, nodeId, formulaId) =>
      {
        pathEnd {
          get {
            val request = new GetApplicableAxiomsRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId))
            completeRequest(request, t)
          }
        }
      }
    }

  val definitionsList: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "listDefinitions") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new GetApplicableDefinitionsRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val setDefinition: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "definitions") { (userId, proofId) =>
      {
        pathEnd {
          post {
            entity(as[String]) { params =>
              {
                val (what: JsString) :: (repl: JsString) :: Nil = JsonParser(params)
                  .asJsObject
                  .getFields("what", "repl")
                  .toList
                val request = new SetDefinitionsRequest(database, userId, proofId, what.value, repl.value)
                completeRequest(request, t)
              }
            }
          }
        }
      }
    }

  val sequentList: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "listStepSuggestions") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new GetSequentStepSuggestionRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val twoPosList: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "twoposlist") {
      (userId, proofId, nodeId, fml1Id, fml2Id) =>
        {
          pathEnd {
            get {
              val request = new GetApplicableTwoPosTacticsRequest(
                database,
                userId,
                proofId,
                nodeId,
                parseFormulaId(fml1Id),
                parseFormulaId(fml2Id),
              )
              completeRequest(request, t)
            }
          }
        }
    }

  val derivationInfo: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "derivationInfos" / Segment.?) {
      (userId, proofId, _, axiomId) =>
        {
          pathEnd {
            get {
              val request = new GetDerivationInfoRequest(database, userId, proofId, axiomId)
              completeRequest(request, t)
            }
          }
        }
    }

  val exportSequent: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / "export" / Segment / Segment / Segment) { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new ExportCurrentSubgoal(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val doAt: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "doAt" / Segment) {
      (userId, proofId, nodeId, formulaId, tacticId) =>
        {
          pathEnd {
            get {
              parameters(Symbol("stepwise").as[Boolean]) { stepwise =>
                val request = new RunBelleTermRequest(
                  database,
                  userId,
                  proofId,
                  nodeId,
                  tacticId,
                  Some(Fixed(parseFormulaId(formulaId))),
                  None,
                  Nil,
                  consultAxiomInfo = true,
                  stepwise = stepwise,
                )
                completeRequest(request, t)
              }
            }
          }
        }
    }

  val getStep: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "whatStep") {
      (userId, proofId, nodeId, formulaId) =>
        {
          pathEnd {
            get {
              val request = new GetStepRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId))
              completeRequest(request, t)
            }
          }
        }
    }

  val searchLemmas: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "lemmas" / Segment) {
      (userId, proofId, nodeId, formulaId, partialLemmaName) =>
        {
          pathEnd {
            get {
              val request =
                new GetLemmasRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId), partialLemmaName)
              completeRequest(request, t)
            }
          }
        }
    }

  val formulaPrettyString: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "prettyString") {
      (userId, proofId, nodeId, formulaId) =>
        {
          pathEnd {
            get {
              val request =
                new GetFormulaPrettyStringRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId))
              completeRequest(request, t)
            }
          }
        }
    }

  val checkInput: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "checkInput" / Segment) {
      (userId, proofId, nodeId, tacticId) =>
        {
          pathEnd {
            post {
              entity(as[String]) { params =>
                val (pName: JsString) :: (pType: JsString) :: (pValue: JsString) :: Nil = JsonParser(params)
                  .asJsObject
                  .getFields("param", "type", "value")
                  .toList
                completeRequest(
                  new CheckTacticInputRequest(
                    database,
                    userId,
                    proofId,
                    nodeId,
                    tacticId,
                    pName.value,
                    pType.value,
                    pValue.value,
                  ),
                  t,
                )
              }
            }
          }
        }
    }

  val doInputAt: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "doInputAt" / Segment) {
      (userId, proofId, nodeId, formulaId, tacticId) =>
        {
          pathEnd {
            post {
              parameters(Symbol("stepwise").as[Boolean]) { stepwise =>
                entity(as[String]) { params =>
                  {
                    val info = DerivationInfo(tacticId)
                    val expectedInputs = info.inputs
                    // Input has format [{"type":"formula","param":"j(x)","value":"v >= 0"}]
                    val paramArray = JsonParser(params).asInstanceOf[JsArray].elements.map(_.asJsObject())
                    val illFormedParams = paramArray.filter({ obj =>
                      val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
                      val paramInfo = expectedInputs.find(_.name == paramName)
                      paramInfo.isEmpty ||
                      (paramInfo match {
                        case Some(_: OptionArg) => false
                        case Some(_: ListArg) => false
                        case _ => obj.getFields("value").isEmpty
                      })
                    })
                    if (illFormedParams.isEmpty) {
                      val inputs = paramArray
                        .map({ obj =>
                          val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
                          expectedInputs.find(_.name == paramName) match {
                            case Some(OptionArg(paramInfo)) => obj.getFields("value").headOption match {
                                case Some(JsString(paramValue)) => Some(BelleTermInput(paramValue, Some(paramInfo)))
                                case _ => None
                              }
                            case Some(ListArg(paramInfo)) => obj.getFields("value").headOption match {
                                case Some(JsString(paramValue)) => Some(BelleTermInput(paramValue, Some(paramInfo)))
                                case _ => Some(BelleTermInput("nil", Some(paramInfo)))
                              }
                            case paramInfo =>
                              val paramValue = obj.getFields("value").head.asInstanceOf[JsString].value
                              Some(BelleTermInput(paramValue, paramInfo))
                          }
                        })
                        .filter(_.isDefined)
                        .map(_.get)
                      val request = new RunBelleTermRequest(
                        database,
                        userId,
                        proofId,
                        nodeId,
                        tacticId,
                        Some(Fixed(parseFormulaId(formulaId))),
                        None,
                        inputs.toList,
                        consultAxiomInfo = true,
                        stepwise = stepwise,
                      )
                      completeRequest(request, t)
                    } else {
                      val missing = illFormedParams
                        .map(_.getFields("param").head.asInstanceOf[JsString].value)
                        .mkString(", ")
                      completeRequest(
                        new FailedRequest(userId, "Ill-formed tactic arguments, missing parameters " + missing),
                        t,
                      )
                    }
                  }
                }
              }
            }
          }
        }
    }

  val doTwoPosAt: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "doAt" / Segment) {
      (userId, proofId, nodeId, fml1Id, fml2Id, tacticId) =>
        {
          pathEnd {
            get {
              parameters(Symbol("stepwise").as[Boolean]) { stepwise =>
                val request = new RunBelleTermRequest(
                  database,
                  userId,
                  proofId,
                  nodeId,
                  tacticId,
                  Some(Fixed(parseFormulaId(fml1Id))),
                  Some(Fixed(parseFormulaId(fml2Id))),
                  Nil,
                  consultAxiomInfo = true,
                  stepwise = stepwise,
                )
                completeRequest(request, t)
              }
            }
          }
        }
    }

  val doTactic: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "do" / Segment) { (userId, proofId, nodeId, tacticId) =>
      {
        pathEnd {
          get {
            parameters(Symbol("stepwise").as[Boolean]) { stepwise =>
              val request = new RunBelleTermRequest(
                database,
                userId,
                proofId,
                nodeId,
                tacticId,
                None,
                None,
                Nil,
                consultAxiomInfo = true,
                stepwise = stepwise,
              )
              completeRequest(request, t)
            }
          }
        }
      }
    }

  val doInputTactic: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "doInput" / Segment) { (userId, proofId, nodeId, tacticId) =>
      {
        pathEnd {
          post {
            parameters(Symbol("stepwise").as[Boolean]) { stepwise =>
              entity(as[String]) { params =>
                {
                  val info = DerivationInfo(tacticId)
                  val expectedInputs = info.inputs
                  // Input has format [{"type":"formula","param":"j(x)","value":"v >= 0"}]
                  val paramArray = JsonParser(params).asInstanceOf[JsArray]
                  val inputs = paramArray
                    .elements
                    .map({ elem =>
                      val obj = elem.asJsObject()
                      val (paramName: JsString) :: (paramValue: JsString) :: Nil =
                        obj.getFields("param", "value").toList
                      val paramInfo = expectedInputs.find(_.name == paramName.value)
                      BelleTermInput(paramValue.value, paramInfo)
                    })
                  val request = new RunBelleTermRequest(
                    database,
                    userId,
                    proofId,
                    nodeId,
                    tacticId,
                    None,
                    None,
                    inputs.toList,
                    consultAxiomInfo = true,
                    stepwise = stepwise,
                  )
                  completeRequest(request, t)
                }
              }
            }
          }
        }
      }
    }

  val doCustomTactic: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "doCustomTactic") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          post {
            parameters(Symbol("stepwise").as[Boolean]) { stepwise =>
              entity(as[String]) { tactic =>
                {
                  val request = new RunBelleTermRequest(
                    database,
                    userId,
                    proofId,
                    nodeId,
                    tactic.trim.stripPrefix(";"),
                    None,
                    consultAxiomInfo = false,
                    stepwise = stepwise,
                  )
                  completeRequest(request, t)
                }
              }
            }
          }
        }
      }
    }

  private def posLocator(where: String) = where match {
    case "R" => Find.FindRFirst
    case "L" => Find.FindLFirst
    case loc => throw new IllegalArgumentException("Unknown position locator " + loc)
  }

  val doSearch: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "doSearch" / Segment / Segment) {
      (userId, proofId, goalId, where, tacticId) =>
        {
          pathEnd {
            get {
              parameters(Symbol("stepwise").as[Boolean]) { stepwise =>
                val pos = posLocator(where)
                val request = new RunBelleTermRequest(
                  database,
                  userId,
                  proofId,
                  goalId,
                  tacticId,
                  Some(pos),
                  None,
                  Nil,
                  consultAxiomInfo = true,
                  stepwise = stepwise,
                )
                completeRequest(request, t)
              }
            } ~ post {
              parameters(Symbol("stepwise").as[Boolean]) { stepwise =>
                entity(as[String]) { params =>
                  {
                    val info = DerivationInfo(tacticId)
                    val expectedInputs = info.inputs
                    // Input has format [{"type":"formula","param":"j(x)","value":"v >= 0"}]
                    val paramArray = JsonParser(params).asInstanceOf[JsArray]
                    val inputs = paramArray
                      .elements
                      .map({ elem =>
                        val obj = elem.asJsObject()
                        val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
                        val paramValue = obj.getFields("value").head.asInstanceOf[JsString].value
                        val paramInfo = expectedInputs.find(_.name == paramName)
                        BelleTermInput(paramValue, paramInfo)
                      })
                    val pos = posLocator(where)
                    val request = new RunBelleTermRequest(
                      database,
                      userId,
                      proofId,
                      goalId,
                      tacticId,
                      Some(pos),
                      None,
                      inputs.toList,
                      consultAxiomInfo = true,
                      stepwise = stepwise,
                    )
                    completeRequest(request, t)
                  }
                }
              }
            }
          }
        }
    }

  val taskStatus: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "status") { (userId, proofId, nodeId, taskId) =>
      {
        pathEnd {
          get {
            val request = new TaskStatusRequest(database, userId, proofId, nodeId, taskId)
            completeRequest(request, t)
          }
        }
      }
    }

  val taskResult: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "result") { (userId, proofId, nodeId, taskId) =>
      {
        pathEnd {
          get {
            val request = new TaskResultRequest(database, userId, proofId, nodeId, taskId)
            completeRequest(request, t)
          }
        }
      }
    }

  val stopTask: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / Segment / "stop") { (userId, proofId, nodeId, taskId) =>
      {
        pathEnd {
          get {
            val request = new StopTaskRequest(database, userId, proofId, nodeId, taskId)
            completeRequest(request, t)
          }
        }
      }
    }

  val pruneBelow: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "pruneBelow") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new PruneBelowRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val undoLastProofStep: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "undoLastStep") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new UndoLastProofStepRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofProgressStatus: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "progress") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new GetProofProgressStatusRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val proofCheckIsProved: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "validatedStatus") { (userId, proofId) =>
      {
        pathEnd {
          get {
            val request = new CheckIsProvedRequest(database, userId, proofId)
            completeRequest(request, t)
          }
        }
      }
    }

  val changeProofName: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / "name" / Segment) { (userId, proofId, newName) =>
      {
        pathEnd {
          post {
            entity(as[String]) { _ =>
              { completeRequest(new UpdateProofNameRequest(database, userId, proofId, newName), t) }
            }
          }
        }
      }
    }

  /** Validates the proof of a lemma. */
  val validateProof: Route = path("validate") {
    pathEnd {
      post {
        entity(as[String]) { archiveFileContents =>
          {
            val entries = ArchiveParser.parse(archiveFileContents)

            if (entries.length != 1) complete(completeResponse(
              new ErrorResponse(s"Expected exactly one model in the archive but found ${entries.length}") :: Nil
            ))
            else if (entries.head.tactics.length != 1) complete(completeResponse(
              new ErrorResponse(
                s"Expected exactly one proof in the archive but found ${entries.head.tactics.length} proofs. Make sure you export from the Proofs page, not the Models page."
              ) :: Nil
            ))
            else {
              val entry = entries.head
              val model = entry.model.asInstanceOf[Formula]
              val tactic = entry.tactics.head._3
              complete(standardCompletion(new ValidateProofRequest(database, model, tactic, entry.defs), EmptyToken()))
            }
          }
        }
      }
    }
  }

  val checkProofValidation: Route = path("validate" / Segment) { taskId =>
    { get { complete(standardCompletion(new CheckValidationRequest(database, taskId), EmptyToken())) } }
  }

}
