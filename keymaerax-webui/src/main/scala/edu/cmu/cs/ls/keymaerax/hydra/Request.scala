/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * HyDRA API Requests
  *
  * @author Nathan Fulton
 * @author Ran Ji
 */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.hydra.SQLite.SQLiteDB
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXProblemParser, ParseException}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter, HackyInlineErrorMsgPrinter}
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import Augmentors._
import edu.cmu.cs.ls.keymaerax.tools._

import spray.json._
import spray.json.DefaultJsonProtocol._

import java.io.{File, FileInputStream, FileOutputStream, FileNotFoundException}
import java.text.SimpleDateFormat
import java.util.{Calendar, Locale}

import scala.io.Source
import scala.collection.immutable._

/**
 * A Request should handle all expensive computation as well as all
 * possible side-effects of a request (e.g. updating the database), but should
 * not modify the internal state of the HyDRA server (e.g. do not update the
 * event queue).
 *
 * Requests objects should do work after getResultingUpdates is called,
 * not during object construction.
 *
 * Request.getResultingUpdates might be run from a new thread.
 */
sealed trait Request {
  /** Returns true iff a user authenticated with name userName is allowed to access this resource. */
  def permission(t: SessionToken): Boolean = true

  final def getResultingResponses(t: SessionToken): List[Response] = {
    assert(permission(t), "Permission denied but still responses queried (see completeRequest)")
    resultingResponses()
  }

  def resultingResponses(): List[Response] //see Response.scala.

  def currentDate(): String = {
    val format = new SimpleDateFormat("d-M-y")
    format.format(Calendar.getInstance().getTime)
  }
}

/**
  * @todo we don't always check that the username is in fact associated with the other data that's touched by a request.
  *       For example, openProof might not insist that the proofId actually belongs to the associated userId in the request.
  *       The best solution to this in the long term is a re-design of the API, probably.
  * @param username The username of the current user.
  */
abstract class UserRequest(username: String) extends Request {
  override def permission(t: SessionToken) = t belongsTo username
}

abstract class LocalhostOnlyRequest() extends Request {
  override def permission(t: SessionToken) = !HyDRAServerConfig.isHosted //@todo change this to a literal false prior to deployment.
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Users
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateUserRequest(db : DBAbstraction, username : String, password:String) extends Request {
  override def resultingResponses() = {
    val userExists = db.userExists(username)
    val sessionToken =
      if (!userExists) {
        db.createUser(username,password)
        Some(SessionManager.add(username))
      } else None
    new LoginResponse(!userExists, username, sessionToken) ::  Nil
  }
}

class LoginRequest(db : DBAbstraction, username : String, password : String) extends Request {
  override def resultingResponses(): List[Response] = {
    val check = db.checkPassword(username, password)
    val sessionToken =
      if(check) Some(SessionManager.add(username))
      else None
    new LoginResponse(check, username, sessionToken) ::  Nil
  }
}

class ProofsForUserRequest(db : DBAbstraction, userId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val proofs = db.getProofsForUser(userId).map(proof =>
      (proof._1, "loaded"/*KeYmaeraInterface.getTaskLoadStatus(proof._1.proofId.toString).toString.toLowerCase*/))
    new ProofListResponse(proofs) :: Nil
  }
}

class UpdateProofNameRequest(db : DBAbstraction, userId: String, proofId : String, newName : String) extends UserRequest(userId) {
  def resultingResponses() = {
    val proof = db.getProofInfo(proofId)
    db.updateProofName(proofId, newName)
    new UpdateProofNameResponse(proofId, newName) :: Nil
  }
}

/**
 * Returns an object containing all information necessary to fill out the global template (e.g., the "new events" bubble)
  *
  * @param db
 * @param userId
 */
class DashInfoRequest(db : DBAbstraction, userId : String) extends UserRequest(userId) {
  override def resultingResponses() : List[Response] = {
    val openProofCount : Int = db.openProofs(userId).length
    val allModelsCount: Int = db.getModelList(userId).length
    val provedModelsCount: Int = db.getModelList(userId).count(m => db.getProofsForModel(m.modelId).exists(_.closed))

    new DashInfoResponse(openProofCount, allModelsCount, provedModelsCount) :: Nil
  }
}

class CounterExampleRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserRequest(userId) {
  override def resultingResponses(): List[Response] = {
    val trace = db.getExecutionTrace(proofId.toInt)
    val tree = ProofTree.ofTrace(trace)
    val node =
      tree.findNode(nodeId) match {
        case None => throw new ProverException("Invalid node " + nodeId)
        case Some(n) => n
      }

    //@note not a tactic because we don't want to change the proof tree just by looking for counterexamples
    val fml = node.sequent.toFormula
    if (fml.isFOL) {
      try {
        ToolProvider.cexTool() match {
          case Some(cexTool) => cexTool.findCounterExample(fml) match {
            //@todo return actual sequent, use collapsiblesequentview to display counterexample
            case Some(cex) => new CounterExampleResponse("cex.found", fml, cex) :: Nil
            case None => new CounterExampleResponse("cex.none") :: Nil
          }
          case None => new CounterExampleResponse("cex.nonfo") :: Nil
        }
      } catch {
        case ex: MathematicaComputationAbortedException => new CounterExampleResponse("cex.timeout") :: Nil
      }
    } else {
      new CounterExampleResponse("cex.nonfo") :: Nil
    }
  }
}

class SetupSimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserRequest(userId) {
  override def resultingResponses(): List[Response] = {
    val trace = db.getExecutionTrace(proofId.toInt)
    val tree = ProofTree.ofTrace(trace)
    val node = tree.findNode(nodeId) match {
      case None => throw new ProverException("Invalid node " + nodeId)
      case Some(n) => n
    }

    //@note not a tactic because we don't want to change the proof tree just by simulating
    val fml = if (node.sequent.ante.nonEmpty) node.sequent.toFormula else { val Imply(True, succ) = node.sequent.toFormula; succ }
    if (ToolProvider.odeTool().isDefined) fml match {
      case Imply(initial, b@Box(prg, _)) =>
        // all symbols because we need frame constraints for constants
        val vars = (StaticSemantics.symbols(prg) ++ StaticSemantics.symbols(initial)).filter(_.isInstanceOf[Variable])
        val Box(prgPre, _) = vars.foldLeft[Formula](b)((b, v) => b.replaceAll(v, Variable("pre" + v.name, v.index, v.sort)))
        val stateRelEqs = vars.map(v => Equal(v.asInstanceOf[Term], Variable("pre" + v.name, v.index, v.sort))).reduceRightOption(And).getOrElse(True)
        val simSpec = Diamond(solveODEs(prgPre), stateRelEqs)
        new SetupSimulationResponse(addNonDetInitials(initial, vars), transform(simSpec)) :: Nil
      case _ => new ErrorResponse("Simulation only supported for formulas of the form initial -> [program]safe") :: Nil
    }
    else new ErrorResponse("No simulation tool available, please configure Mathematica") :: Nil
  }

  private def addNonDetInitials(initial: Formula, vars: Set[NamedSymbol]): Formula = {
    val nonDetInitials = vars -- StaticSemantics.freeVars(initial).symbols
    nonDetInitials.foldLeft(initial)((f, v) => And(f, Equal(v.asInstanceOf[Term], v.asInstanceOf[Term])))
  }

  private def transform(simSpec: Diamond): Formula = {
    val stateRelation = TactixLibrary.proveBy(simSpec, TactixLibrary.chase(3, 3, (e: Expression) => e match {
      // no equational assignments
      case Box(Assign(_,_),_) => "[:=] assign" :: "[:=] assign update" :: Nil
      case Diamond(Assign(_,_),_) => "<:=> assign" :: "<:=> assign update" :: Nil
      // remove loops
      case Diamond(Loop(_), _) => "<*> approx" :: Nil
      //@note: do nothing, should be gone already
      case Diamond(ODESystem(_, _), _) => Nil
      case _ => AxiomIndex.axiomsFor(e)
    })('R))
    assert(stateRelation.subgoals.size == 1 &&
      stateRelation.subgoals.head.ante.isEmpty &&
      stateRelation.subgoals.head.succ.size == 1, "Simulation expected to result in a single formula")
    stateRelation.subgoals.head.succ.head
  }

  private def solveODEs(prg: Program): Program = ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
    override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
      case ODESystem(ode, evoldomain) =>
        Right(Compose(Test(evoldomain), solve(ode, evoldomain)))
      case _ => Left(None)
    }
  }, prg).get

  private def solve(ode: DifferentialProgram, evoldomain: Formula): Program = {
    val iv: Map[Variable, Variable] =
      primedSymbols(ode).map(v => v -> Variable(v.name + "0", v.index, v.sort)).toMap
    val time: Variable = Variable("t_", None, Real)
    //@note replace initial values with original variable, since we turn them into assignments
    val solution = replaceFree(ToolProvider.odeTool().get.diffSol(ode, time, iv).get, iv.map(_.swap))
    val flatSolution = flattenConjunctions(solution).
      sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size)
    Compose(
      flatSolution.map({ case Equal(v: Variable, r) => Assign(v, r) }).reduceRightOption(Compose).getOrElse(Test(True)),
      Test(evoldomain))
  }

  private def replaceFree(f: Formula, vars: Map[Variable, Variable]) = {
    vars.keySet.foldLeft[Formula](f)((b, v) => b.replaceFree(v, vars.get(v).get))
  }

  private def primedSymbols(ode: DifferentialProgram) = {
    var primedSymbols = Set[Variable]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case DifferentialSymbol(ps) => primedSymbols += ps; Left(None)
        case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
        case _ => Left(None)
      }
    }, ode)
    primedSymbols
  }

  private def flattenConjunctions(f: Formula): List[Formula] = {
    var result: List[Formula] = Nil
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = f match {
        case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
        case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
      }
    }, f)
    result
  }
}

class SimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, initial: Formula, stateRelation: Formula, steps: Int, n: Int, stepDuration: Term) extends UserRequest(userId) {
  override def resultingResponses(): List[Response] = {
    ToolProvider.simulationTool() match {
      case Some(s) =>
        val timedStateRelation = stateRelation.replaceFree(Variable("t_"), stepDuration)
        val simulation = s.simulate(initial, timedStateRelation, steps, n)
        new SimulationResponse(simulation, stepDuration) :: Nil
      case _ => new ErrorResponse("No simulation tool configured, please setup Mathematica") :: Nil
    }
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// System Configuration
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class KyxConfigRequest(db: DBAbstraction) extends LocalhostOnlyRequest {
  val newline = "\n"
  override def resultingResponses() : List[Response] = {
    val mathConfig = db.getConfiguration("mathematica").config
    // keymaera X version
    val kyxConfig = "KeYmaera X version: " + VERSION + newline +
      "Java version: " + System.getProperty("java.runtime.version") + " with " + System.getProperty("sun.arch.data.model") + " bits" + newline +
      "OS: " + System.getProperty("os.name") + " " + System.getProperty("os.version") + newline +
      "LinkName: " + mathConfig.apply("linkName") + newline +
      "jlinkLibDir: " + mathConfig.apply("jlinkLibDir")
    new KyxConfigResponse(kyxConfig) :: Nil
  }
}

class KeymaeraXVersionRequest() extends Request {
  override def resultingResponses() : List[Response] = {
    val keymaeraXVersion = VERSION
    val (upToDate, latestVersion) = UpdateChecker.getVersionStatus() match {
      case Some((upToDate, latestVersion)) => (Some(upToDate), Some(latestVersion))
      case _ => (None, None)
    }
    new KeymaeraXVersionResponse(keymaeraXVersion, upToDate, latestVersion) :: Nil
  }
}

class ConfigureMathematicaRequest(db : DBAbstraction, linkName : String, jlinkLibFileName : String) extends LocalhostOnlyRequest {
  private def isLinkNameCorrect(linkNameFile: java.io.File): Boolean = {
    linkNameFile.getName == "MathKernel" || linkNameFile.getName == "MathKernel.exe"
  }

  private def isJLinkLibFileCorrect(jlinkFile: java.io.File, jlinkLibDir : java.io.File): Boolean = {
    (jlinkFile.getName == "libJLinkNativeLibrary.jnilib" || jlinkFile.getName == "JLinkNativeLibrary.dll" ||
      jlinkFile.getName == "libJLinkNativeLibrary.so") && jlinkLibDir.exists() && jlinkLibDir.isDirectory
  }

  override def resultingResponses(): List[Response] = {
    //check to make sure the indicated files exist and point to the correct files.
    val linkNameFile = new java.io.File(linkName)
    val jlinkLibFile = new java.io.File(jlinkLibFileName)
    val jlinkLibDir: java.io.File = jlinkLibFile.getParentFile
    val linkNameExists = isLinkNameCorrect(linkNameFile) && linkNameFile.exists()
    val jlinkLibFileExists = isJLinkLibFileCorrect(jlinkLibFile, jlinkLibDir) && jlinkLibFile.exists()
    var linkNamePrefix = linkNameFile
    var jlinkLibNamePrefix = jlinkLibFile

    if (!linkNameExists) {
      // look for the largest prefix that does exist
      while (!linkNamePrefix.exists && linkNamePrefix.getParent != null) {
        linkNamePrefix = new java.io.File(linkNamePrefix.getParent)
      }
    }
    if (!jlinkLibFileExists) {
      // look for the largest prefix that does exist
      while (!jlinkLibNamePrefix.exists && jlinkLibNamePrefix.getParent != null) {
        jlinkLibNamePrefix = new java.io.File(jlinkLibNamePrefix.getParent)
      }
    }
    if (!linkNameExists || !jlinkLibFileExists) {
      new ConfigureMathematicaResponse(
        if (linkNamePrefix.exists()) linkNamePrefix.toString else "",
        if (jlinkLibNamePrefix.exists()) jlinkLibNamePrefix.toString else "", false) :: Nil
    }
    else {
      val originalConfig = db.getConfiguration("mathematica")
      val configMap = scala.collection.immutable.Map("linkName" -> linkName, "jlinkLibDir" -> jlinkLibDir.getAbsolutePath)
      val newConfig = new ConfigurationPOJO("mathematica", configMap)

      db.updateConfiguration(newConfig)

      try {
        new ConfigureMathematicaResponse(linkName, jlinkLibDir.getAbsolutePath, true) :: Nil
      } catch {
        /* @todo Is this exception ever actually raised? */
        case e : FileNotFoundException =>
          db.updateConfiguration(originalConfig)
          e.printStackTrace()
          new ConfigureMathematicaResponse(linkName, jlinkLibDir.getAbsolutePath, false) :: Nil
      }
    }
  }
}

class GetMathematicaConfigSuggestionRequest(db : DBAbstraction) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    val reader = this.getClass.getResourceAsStream("/config/potentialMathematicaPaths.json")
    val contents : String = Source.fromInputStream(reader).getLines().foldLeft("")((file, line) => file + "\n" + line)
    val source : JsArray = contents.parseJson.asInstanceOf[JsArray]

    // TODO provide classes and spray JSON protocol to convert
    val os = System.getProperty("os.name")
    val osKey = osKeyOf(os.toLowerCase)
    val osPathGuesses = source.elements.find(osCfg => osCfg.asJsObject.getFields("os").head.convertTo[String] == osKey) match {
      case Some(opg) => opg.asJsObject.getFields("mathematicaPaths").head.convertTo[List[JsObject]]
      case None => throw new IllegalStateException("No default configuration for Unknown OS")
    }

    val pathTuples = osPathGuesses.map(osPath =>
      (osPath.getFields("version").head.convertTo[String],
       osPath.getFields("kernelPath").head.convertTo[String],
       osPath.getFields("kernelName").head.convertTo[String],
       osPath.getFields("jlinkPath").head.convertTo[String],
       osPath.getFields("jlinkName").head.convertTo[String]))

    val suggestion = pathTuples.find(path => new java.io.File(path._2 + path._3).exists &&
        new java.io.File(path._4 + path._5).exists) match {
      case Some(s) => s
      case None => pathTuples.head // use the first configuration as suggestion when nothing else matches
    }

    new MathematicaConfigSuggestionResponse(os, suggestion._1, suggestion._2, suggestion._3, suggestion._4, suggestion._5) :: Nil
  }

  private def osKeyOf(osName: String): String = {
    if (osName.contains("win")) "Windows"
    else if (osName.contains("mac")) "MacOS"
    else if (osName.contains("nix") || osName.contains("nux") || osName.contains("aix")) "Unix"
    else "Unknown"
  }
}

class GetMathematicaConfigurationRequest(db : DBAbstraction) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration("mathematica").config
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    val jlinkLibFile = {
      if(osName.contains("win")) "JLinkNativeLibrary.dll"
      else if(osName.contains("mac")) "libJLinkNativeLibrary.jnilib"
      else if(osName.contains("nix") || osName.contains("nux") || osName.contains("aix")) "libJLinkNativeLibrary.so"
      else "Unknown"
    }
    if (config.contains("linkName") && config.contains("jlinkLibDir")) {
      new MathematicaConfigurationResponse(config("linkName"), config("jlinkLibDir") + File.separator + jlinkLibFile) :: Nil
    } else {
      new MathematicaConfigurationResponse("", "") :: Nil
    }
  }
}

class MathematicaStatusRequest(db : DBAbstraction) extends Request {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration("mathematica").config
    new MathematicaStatusResponse(config.contains("linkName") && config.contains("jlinkLibDir")) :: Nil
  }
}

class ListExamplesRequest(db: DBAbstraction) extends Request {
  override def resultingResponses(): List[Response] = {
    //@todo read from the database/some web page?
    val examples =
      new ExamplePOJO(0, "STTT Tutorial",
        "Automated stop sign braking for cars",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/sttt/sttt.json",
        "/examples/tutorials/sttt/sttt.png") ::
      new ExamplePOJO(1, "CPSWeek 2016 Tutorial",
        "Proving ODEs",
        "http://www.ls.cs.cmu.edu/KeYmaeraX/KeYmaeraX-tutorial.pdf",
        "classpath:/examples/tutorials/cpsweek/cpsweek.json",
        "/examples/tutorials/cpsweek/cpsweek.png") ::
      Nil
    new ListExamplesResponse(examples) :: Nil
  }
}


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Models
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateModelRequest(db : DBAbstraction, userId : String, nameOfModel : String, keyFileContents : String) extends UserRequest(userId) {
  private var createdId : Option[String] = None

  def resultingResponses() = {
    try {
      //Return the resulting response.
      KeYmaeraXProblemParser(keyFileContents) match {
        case f : Formula => {
          if(db.getModelList(userId).map(_.name).contains(nameOfModel)) {
            //Nope. Give a good error message.
            new BooleanResponse(false, Some("A model with that name already exists.")) :: Nil
          }
          else {
            println(s"${nameOfModel} is unique in: ${db.getModelList(userId).map(_.name).mkString(",")}")
            createdId = db.createModel(userId, nameOfModel, keyFileContents, currentDate()).map(x => x.toString)
            println(s"ID of model ${nameOfModel}: ${createdId}")
            new BooleanResponse(createdId.isDefined) :: Nil
          }
        }
      }
    } catch {
      case e: ParseException => new ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
    }
  }

  def getModelId = createdId match {
    case Some(s) => s
    case None => throw new IllegalStateException("Requested created model ID before calling resultingResponses, or else an error occurred during creation.")
  }
}

class ImportExampleRepoRequest(db: DBAbstraction, userId: String, repoUrl: String) extends UserRequest(userId) {
  override def resultingResponses(): List[Response] = {
    DatabasePopulator.importJson(db, userId, repoUrl, prove=false)
    new BooleanResponse(true) :: Nil
  }
}

class DeleteModelRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) {
  //@todo check the model belongs to the user.
  override def resultingResponses(): List[Response] = {
    val id = Integer.parseInt(modelId)
    //db.getProofsForModel(id).foreach(proof => TaskManagement.forceDeleteTask(proof.proofId.toString))
    val success = db.deleteModel(id)
    new BooleanResponse(success) :: Nil
  }
}

class DeleteProofRequest(db: DBAbstraction, userId: String, proofId: String) extends UserRequest(userId) {
  override def resultingResponses() : List[Response] = {
    //TaskManagement.forceDeleteTask(proofId)
    val success = db.deleteProof(Integer.parseInt(proofId))
    new BooleanResponse(success) :: Nil
  }
}

class GetModelListRequest(db : DBAbstraction, userId : String) extends UserRequest(userId) {
  def resultingResponses() = {
    new ModelListResponse(db.getModelList(userId)) :: Nil
  }
}

class GetModelRequest(db : DBAbstraction, userId : String, modelId : String) extends UserRequest(userId) {
  val model = db.getModel(modelId)
  insist(model.userId == userId, s"model ${modelId} does not belong to ${userId}")
  def resultingResponses() = {
    new GetModelResponse(model) :: Nil
  }
}

class GetModelTacticRequest(db : DBAbstraction, userId : String, modelId : String) extends UserRequest(userId) {
  def resultingResponses() = {
    val model = db.getModel(modelId)
    new GetModelTacticResponse(model) :: Nil
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proofs of models
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateProofRequest(db : DBAbstraction, userId : String, modelId : String, name : String, description : String)
  extends UserRequest(userId) {
  private var proofId : Option[String] = None

  def getProofId = proofId match {
    case Some(s) => s
    case None => throw new IllegalStateException("The ID of the created proof was requested before resultingResponses was called.")
  }
  def resultingResponses() = {
    proofId = Some(db.createProofForModel(modelId, name, description, currentDate()))

    // Create a "task" for the model associated with this proof.
    val keyFile = db.getModel(modelId).keyFile
    //KeYmaeraInterface.addTask(proofId.get, keyFile)

    new CreatedIdResponse(proofId.get) :: Nil
  }
}

class ProveFromTacticRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val model = db.getModel(modelId)
    model.tactic match {
      case Some(tacticText) =>
        val proofId = db.createProofForModel(Integer.parseInt(modelId), model.name + " from tactic", "Proof from tactic", currentDate())
        DatabasePopulator.executeTactic(db, model.keyFile, proofId, tacticText)
        new CreatedIdResponse(proofId.toString) :: Nil
      case None => ???
    }

  }
}

class ProofsForModelRequest(db : DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val proofs = db.getProofsForModel(modelId).map(proof =>
      (proof, "loaded"/*KeYmaeraInterface.getTaskLoadStatus(proof.proofId.toString).toString.toLowerCase*/))
    new ProofListResponse(proofs) :: Nil
  }
}

class OpenProofRequest(db : DBAbstraction, userId : String, proofId : String, wait : Boolean = false) extends UserRequest(userId) {
  insist(db.getModel(db.getProofInfo(proofId).modelId).userId == userId, s"User $userId does not own the model associated with proof $proofId")
  def resultingResponses() = {
    val proofInfo = db.getProofInfo(proofId)
    new OpenProofResponse(db.getProofInfo(proofId), "loaded"/*TaskManagement.TaskLoadStatus.Loaded.toString.toLowerCase()*/) :: Nil
  }
}

/**
  * Gets all tasks of the specified proof. A task is some work the user has to do. It is not a KeYmaera task!
  *
  * @param db Access to the database.
  * @param userId Identifies the user.
  * @param proofId Identifies the proof.
  */
class GetAgendaAwesomeRequest(db : DBAbstraction, userId : String, proofId : String) extends UserRequest(userId) {
  def resultingResponses() = {
    val items = db.agendaItemsForProof(proofId.toInt)
    val closed = db.getProofInfo(proofId).closed
    val response = new AgendaAwesomeResponse(ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt), agendaItems = items, proofFinished = closed))
    response :: Nil
  }
}

case class GetAgendaItemRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val closed = db.getProofInfo(proofId).closed
    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt), proofFinished = closed)
    val possibleItems = db.agendaItemsForProof(proofId.toInt)
    var currNode:Option[Int] = Some(nodeId.toInt)
    tree.agendaItemForNode(nodeId, possibleItems) match {
      case Some(item) => new GetAgendaItemResponse (item) :: Nil
      case None => new ErrorResponse("No information stored for agenda item " + nodeId) :: Nil
    }
  }
}

case class SetAgendaItemNameRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, displayName: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val closed = db.getProofInfo(proofId).closed
    val node =
      ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt), proofFinished = closed)
      .nodes.find({case node => node.id.toString == nodeId})
    node match {
      case None => throw new Exception("Node not found")
      case Some(node) =>
        var currNode = node
        var done = false
        while (currNode.parent.nonEmpty && !done) {
          val nextNode = currNode.parent.get
          /* Don't stop at the first node just because it branches (it may be the end of one branch and the start of the
          * next), but if we see branching anywhere else we've found the end of our branch. */
          if (currNode.children.size > 1) {
            done = true
          } else {
            currNode = nextNode
          }
        }
        db.getAgendaItem(proofId.toInt, currNode.id) match {
          case Some(item) =>
            val newItem = AgendaItemPOJO(item.itemId, item.proofId, item.initialProofNode, displayName)
            db.updateAgendaItem(newItem)
            new SetAgendaItemNameResponse(newItem) :: Nil
          case None =>
            val id = db.addAgendaItem(proofId.toInt, currNode.id, displayName)
            new SetAgendaItemNameResponse(AgendaItemPOJO(id, proofId.toInt, currNode.id, displayName)) :: Nil
        }
    }
  }
}

class ProofTaskParentRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val closed = db.getProofInfo(proofId).closed
    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt), proofFinished = closed)
    tree.findNode(nodeId).flatMap(_.parent) match {
      case None => throw new Exception("Tried to get parent of node " + nodeId + " which has no parent")
      case Some(parent) =>
        val response = new ProofTaskParentResponse(parent)
        response :: Nil
    }
  }
}

case class GetPathAllRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val closed = db.getProofInfo(proofId).closed
    val tree: ProofTree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt), proofFinished = closed)
    var node: Option[TreeNode] = tree.findNode(nodeId)
    var path: List[TreeNode] = Nil
    while (node.nonEmpty) {
      path = node.get :: path
      node = node.get.parent
    }
    /* To start with, always send the whole path. */
    val parentsRemaining = 0
    val response = new GetPathAllResponse(path.reverse, parentsRemaining)
    response :: Nil
  }
}

case class GetBranchRootRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val closed = db.getProofInfo(proofId).closed
    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt), proofFinished = closed)
    val node = tree.nodes.find({case node => node.id.toString == nodeId})
    node match {
      case None => throw new Exception("Node not found")
      case Some(node) =>
        var currNode = node
        var done = false
        while (currNode.parent.nonEmpty && !done) {
          currNode = currNode.parent.get
          /* Don't stop at the first node just because it branches (it may be the end of one branch and the start of the
          * next), but if we see branching anywhere else we've found the end of our branch. */
          if (currNode.children.size > 1) {
            done = true
          }
        }
          new GetBranchRootResponse(currNode) :: Nil
    }
  }
}


class GetApplicableAxiomsRequest(db:DBAbstraction, userId: String, proofId: String, nodeId: String, pos:Position) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    import Augmentors._
    val closed = db.getProofInfo(proofId).closed
    if (closed)
      return new ApplicableAxiomsResponse(Nil, None) :: Nil
    val proof = db.getProofInfo(proofId)
    val sequent = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt)).findNode(nodeId).get.sequent
    sequent.sub(pos) match {
      case Some(subFormula) =>
        val axioms = UIIndex.allStepsAt(subFormula, Some(pos), Some(sequent)).
          map{axiom => (
            DerivationInfo(axiom),
            UIIndex.comfortOf(axiom).map(DerivationInfo(_)))}
        val generator = new ConfigurableGenerator(db.getInvariants(proof.modelId))
        val suggestedInput = generator(sequent, pos)
        new ApplicableAxiomsResponse(axioms, if (suggestedInput.hasNext) Some(suggestedInput.next) else None) :: Nil
      case None => new ApplicableAxiomsResponse(Nil, None) :: Nil
    }
  }
}

class GetApplicableTwoPosTacticsRequest(db:DBAbstraction, userId: String, proofId: String, nodeId: String, pos1: Position, pos2: Position) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val closed = db.getProofInfo(proofId).closed
    if (closed) return new ApplicableAxiomsResponse(Nil, None) :: Nil
    val sequent = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt)).findNode(nodeId).get.sequent
    val tactics = UIIndex.allTwoPosSteps(pos1, pos2, sequent).map({case step =>
      (DerivationInfo(step), UIIndex.comfortOf(step).map(DerivationInfo(_)))})
    new ApplicableAxiomsResponse(tactics, None) :: Nil
  }
}

class GetDerivationInfoRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, axiomId: String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val info = (DerivationInfo(axiomId), UIIndex.comfortOf(axiomId).map(DerivationInfo(_))) :: Nil
    new ApplicableAxiomsResponse(info, None) :: Nil
  }
}

class ExportCurrentSubgoal(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserRequest(userId) {
  override def resultingResponses(): List[Response] = {
    if(!db.getProofsForUser(userId).exists(p => p._1.proofId == proofId.toInt)) {
      new PossibleAttackResponse("You do not have permission to access this resource.") :: Nil
    }
    else {
      val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
      tree.findNode(nodeId) match {
        case Some(node) => {
          val provable = Provable.startProof(node.sequent)
          val lemma = Lemma.apply(provable, List(ToolEvidence(List("tool" -> "mock"))), None)
          new KvpResponse("sequent", "Provable: \n" + provable.prettyString + "\n\nLemma:\n" + lemma.toString) :: Nil
        }
        case None => new ErrorResponse(s"Could not find a node with id ${nodeId} associated with ${userId}.${proofId}.\nThis error should NOT occur; please report it.") :: Nil
      }
    }
  }
}

class ExportFormula(db: DBAbstraction, userId: String, proofId: String, nodeId: String, formulaId: String) extends UserRequest(userId) {
  override def resultingResponses(): List[Response] = {
    if(!db.getProofsForUser(userId).exists(p => p._1.proofId == proofId.toInt)) {
      new PossibleAttackResponse("You do not have permission to access this resource.") :: Nil
    }
    else {
      val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
      tree.findNode(nodeId) match {
        case Some(node) => {
          try {
            val formula = node.sequent(SeqPos(formulaId.toInt))
            new KvpResponse("formula", formula.prettyString) :: Nil
          } finally {
            new ErrorResponse(s"Could not find formula with formulaId ${formulaId} in node ${nodeId}")
          }
        }
        case None => new ErrorResponse(s"Could not find a node with id ${nodeId} associated with ${userId}.${proofId}.\nThis error should NOT occur; please report it.") :: Nil
      }
    }
  }
}

case class BelleTermInput(value: String, spec:Option[ArgInfo])

/* If pos is Some then belleTerm must parse to a PositionTactic, else if pos is None belleTerm must parse
* to a Tactic */
class RunBelleTermRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, belleTerm: String,
                         pos: Option[PositionLocator], pos2: Option[PositionLocator] = None, inputs:List[BelleTermInput] = Nil, consultAxiomInfo: Boolean = true) extends UserRequest(userId) {
  /** Turns belleTerm into a specific tactic expression, including input arguments */
  private def fullExpr(node: TreeNode) = {
    val paramStrings: List[String] = inputs.map{
      case BelleTermInput(value, Some(_:TermArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(_:FormulaArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(_:VariableArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(ListArg(_, "formula"))) => "[" + value.split(",").map("{`"+_+"`}").mkString(",") + "]"
      case BelleTermInput(value, None) => value
    }
    val specificTerm = if (consultAxiomInfo) getSpecificName(belleTerm, node.sequent, pos, pos2, _.codeName) else belleTerm
    if (inputs.isEmpty && pos.isEmpty) { assert(pos2.isEmpty, "Undefined pos1, but defined pos2"); specificTerm }
    else if (inputs.isEmpty && pos.isDefined && pos2.isEmpty) { specificTerm + "(" + pos.get.prettyString + ")" }
    else if (inputs.isEmpty && pos.isDefined && pos2.isDefined) { specificTerm + "(" + pos.get.prettyString + "," + pos2.get.prettyString + ")" }
    else specificTerm + "(" + paramStrings.mkString(",") + ")"
  }

  /* Try to figure out the most intuitive inference rule to display for this tactic. If the user asks us "StepAt" then
   * we should use the StepAt logic to figure out which rule is actually being applied. Otherwise just ask TacticInfo */
  private def getSpecificName(tacticId: String, sequent:Sequent, l1: Option[PositionLocator], l2: Option[PositionLocator], what: DerivationInfo => String): String = {
    val pos = l1 match {case Some(Fixed(p, _, _)) => Some(p) case _ => None}
    val pos2 = l2 match {case Some(Fixed(p, _, _)) => Some(p) case _ => None}
    tacticId.toLowerCase match {
      case ("step" | "stepat") if pos.isDefined && pos2.isEmpty =>
        sequent.sub(pos.get) match {
          case Some(fml: Formula) =>
            UIIndex.theStepAt(fml, pos) match {
              case Some(step) => what(DerivationInfo(step))
              case None => tacticId
            }
          case _ => what(DerivationInfo.ofCodeName(tacticId))
        }
      case ("step" | "stepat") if pos.isDefined && pos2.isDefined =>
        sequent.sub(pos.get) match {
          case Some(fml: Formula) =>
            UIIndex.theStepAt(pos.get, pos2.get, sequent) match {
              case Some(step) => what(DerivationInfo(step))
              case None => tacticId
            }
        }
      case _ => what(DerivationInfo.ofCodeName(tacticId))
    }
  }

  private class TacticPositionError(val msg:String,val pos: edu.cmu.cs.ls.keymaerax.parser.Location,val inlineMsg: String) extends Exception

  def resultingResponses(): List[Response] = {
    val closed = db.getProofInfo(proofId).closed
    if (closed) {
      return new ErrorResponse("Can't execute tactics on a closed proof") :: Nil
    }
    val proof = db.getProofInfo(proofId)
    val model = db.getModel(proof.modelId)
    val generator = new ConfigurableGenerator(db.getInvariants(proof.modelId))
    val trace = db.getExecutionTrace(proofId.toInt)
    val tree = ProofTree.ofTrace(trace)
    val node =
      tree.findNode(nodeId) match {
        case None => throw new ProverException("Invalid node " + nodeId)
        case Some(n) => n
      }

    try {
      val expr = BelleParser.parseWithInvGen(fullExpr(node), Some(generator))

      val appliedExpr:BelleExpr = (pos, pos2, expr) match {
        case (None, None, _:AtPosition[BelleExpr]) =>
          throw new TacticPositionError("Can't run a positional tactic without specifying a position", expr.getLocation, "Expected position in argument list but found none")
        case (None, None, _) => expr
        case (Some(position), None, expr: AtPosition[BelleExpr]) => expr(position)
        case (Some(position), None, expr: BelleExpr) => expr
        case (Some(Fixed(p1, None, _)), Some(Fixed(p2, None, _)), expr: BuiltInTwoPositionTactic) => expr(p1, p2)
        case (Some(_), Some(_), expr: BelleExpr) => expr
        case _ => println ("pos " + pos.getClass.getName + ", expr " +  expr.getClass.getName); throw new ProverException("Match error")
      }

      val branch = tree.goalIndex(nodeId)
      val ruleName =
        if (consultAxiomInfo) getSpecificName(belleTerm, node.sequent, pos, pos2, _.display.name)
        else "custom"
      val localProvable = Provable.startProof(node.sequent)
      val globalProvable = trace.lastProvable
      assert(globalProvable.subgoals(branch).equals(node.sequent), "Inconsistent branches in RunBelleTerm")
      val listener = new TraceRecordingListener(db, proofId.toInt, trace.executionId.toInt, trace.lastStepId, globalProvable, trace.alternativeOrder, branch, recursive = false, ruleName)
      val executor = BellerophonTacticExecutor.defaultExecutor
      val taskId = executor.schedule (userId, appliedExpr, BelleProvable(localProvable), List(listener))
      new RunBelleTermResponse(proofId, nodeId, taskId) :: Nil

    } catch {
      case e: ProverException if e.getMessage == "No step possible" => new ErrorResponse("No step possible") :: Nil
      case e: TacticPositionError => new TacticErrorResponse(e.msg, HackyInlineErrorMsgPrinter(belleTerm, e.pos, e.inlineMsg), e) :: Nil
    }
  }
}

class TaskStatusRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    val (isDone, lastStep) = executor.synchronized {
      //@todo need intermediate step recording and query to get meaningful progress reports
      val latestExecutionStep = db.getExecutionSteps(proofId.toInt).sortBy(s => s.stepId).lastOption
      //@note below is the conceptually correct implementation of latestExecutionStep, but getExecutionTrace doesn't work
      //when there's not yet an associated profableId for the step (which is the case here since we are mid-step and the
      //provable isn't computed yet).
//      db.getExecutionTrace(proofId.toInt).lastStepId match {
//        case Some(id) => db.getExecutionSteps(proofId.toInt, None).find(p => p.stepId == id)
//        case None => None
//      }

      (!executor.contains(taskId) || executor.isDone(taskId), latestExecutionStep)
    }
    new TaskStatusResponse(proofId, nodeId, taskId, if (isDone) "done" else "running", lastStep) :: Nil
  }
}

class TaskResultRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String) extends UserRequest(userId) {
  /* It's very important not to report a branch as closed when it isn't. Other wise the user will carry on in blissful
  * ignorance thinking the hardest part of their proof is over when it's not. This is actually a bit difficult to get
  * right, so check the actual provables to make sure we're closing a branch. */
  private def noBogusClosing(tree: ProofTree, parent: TreeNode): Boolean = {
    if (parent.children.nonEmpty || parent.isFake)
      return true
    if (parent.endStep.isEmpty)
      return false
    val endStep = parent.endStep.get
    if (endStep.output.get.subgoals.length != endStep.input.subgoals.length - 1)
      return false

    for (i <- endStep.input.subgoals.indices) {
      if(i < endStep.branch && !endStep.output.get.subgoals(i).equals(endStep.input.subgoals(i)))  {
        return false
      }
      if(i > endStep.branch && !endStep.output.get.subgoals(i-1).equals(endStep.input.subgoals(i))) {
        return false
      }
    }
    true
  }

  def resultingResponses() = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    executor.synchronized {
      val response = executor.wait(taskId) match {
        case Some(Left(BelleProvable(_, _))) =>
          val finalTree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt))
          val parentNode = finalTree.findNode(nodeId).get
          assert(noBogusClosing(finalTree, parentNode), "Server thinks a goal has been closed when it clearly has not")
          new TaskResultResponse(parentNode, parentNode.children, progress = true)
        case Some(Right(error: BelleError)) => new ErrorResponse("Tactic failed with error: " + error.getMessage, error.getCause)
        case None => new ErrorResponse("Could not get tactic result - execution cancelled? ")
      }
      //@note may have been cancelled in the meantime
      executor.tryRemove(taskId)
      response :: Nil
    }
  }
}

class StopTaskRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    //@note may have completed in the meantime
    executor.tasksForUser(userId).foreach(executor.tryRemove(_, force = true))
    new GenericOKResponse() :: Nil
  }
}


class PruneBelowRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : String) extends UserRequest(userId) {
  /**
    * Replay [trace] minus the steps specified in [prune]. The crux of the problem is branch renumbering: determining
    * which branch a kept step (as in not-pruned) will act on once other nodes have been pruned. We compute this by
    * maintaining at each step which goals were or were not produced by a pruned step. The branch number of an kept
    * step is the number of kept goals that proceeds its old branch number, with a potential bonus of +1 if the pruned
    * branch was closed in one of the pruned steps.
    *
    * @param trace The steps to replay (both pruned and kept steps)
    * @param pruned ID's of the pruned steps in trace
    * @return The kept steps of trace with updated branch numbers
    */
  def prune(trace: ExecutionTrace, pruned:Set[Int]): ExecutionTrace = {
    val tr = trace.steps.filter{case step => step.stepId >= pruned.min}
    val pruneRoot = tr.head
    val prunedGoals = Array.tabulate(pruneRoot.input.subgoals.length){case i => i == pruneRoot.branch}
    val (_ ,outputSteps) =
      tr.foldLeft((prunedGoals, Nil:List[ExecutionStep])){case ((prunedGoals, acc), step) =>
        val delta = step.output.get.subgoals.length - step.input.subgoals.length
        val branch = step.branch
        assert(prunedGoals(branch) == pruned.contains(step.stepId), "Pruning algorithm has got its branches confused")
        val updatedGoals =
          if (delta == 0) prunedGoals
          else if (delta == -1) {
            prunedGoals.slice(0, branch) ++ prunedGoals.slice(branch + 1, prunedGoals.length)
          } else {
            prunedGoals ++ Array.tabulate(delta){case _ => pruned.contains(step.stepId)}
          }
        val outputBranch =
          prunedGoals.zipWithIndex.count{case(b,i) => i < branch && !b}  + (if(step.branch >= pruneRoot.branch) 1 else 0)
        if(pruned.contains(step.stepId)) {
          (updatedGoals, acc)
        } else {
          // @todo This is a messy mix of the old trace (ID, Provables) and new trace (branch numbers). Perhaps add a new
          // data structure to avoid the messiness.
          (updatedGoals, ExecutionStep(step.stepId, step.executionId, step.input, step.output, outputBranch, step.alternativeOrder, step.rule, step.executableId, step.isUserExecuted) :: acc)
        }
      }
    ExecutionTrace(trace.proofId, trace.executionId, trace.conclusion, outputSteps.reverse)
  }

  def truncateTrace(trace: ExecutionTrace, firstDroppedStep: Int) = {
    ExecutionTrace(trace.proofId, trace.executionId, trace.conclusion, trace.steps.filter(_.stepId < firstDroppedStep))
  }

  def resultingResponses(): List[Response] = {
    val closed = db.getProofInfo(proofId).closed
    if (closed) {
      return new ErrorResponse("Pruning not allowed on closed proofs") :: Nil
    }
    val trace = db.getExecutionTrace(proofId.toInt)
    val tree = ProofTree.ofTrace(trace, includeUndos = true)
    val prunedSteps = tree.allDescendants(nodeId).flatMap{case node => node.endStep.toList}
    if(prunedSteps.isEmpty) {
      return new ErrorResponse("No steps under node. Nothing to do.") :: Nil
    }
    val prunedStepIds = prunedSteps.map{case step => step.stepId}.toSet
    val prunedTrace = prune(trace, prunedStepIds)
    val previousTrace = truncateTrace(trace, prunedStepIds.min)
    val inputProvable = previousTrace.lastProvable
    db.addAlternative(prunedStepIds.min, inputProvable, prunedTrace)
    val goalNode = tree.findNode(nodeId).get
    val allItems = db.agendaItemsForProof(proofId.toInt)
    val itemName = tree.agendaItemForNode(goalNode.id.toString, allItems).map(_.displayName).getOrElse("Unnamed Item")
    val item = AgendaItem(goalNode.id.toString, itemName, proofId.toString, goalNode)
    val response = new PruneBelowResponse(item)
    response :: Nil
  }
}

class GetProofProgressStatusRequest(db: DBAbstraction, userId: String, proofId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    // @todo return Loading/NotLoaded when appropriate
    val proof = db.getProofInfo(proofId)
    new ProofProgressResponse(proofId, isClosed = proof.closed) :: Nil
  }
}

class CheckIsProvedRequest(db: DBAbstraction, userId: String, proofId: String) extends UserRequest(userId) {
  def resultingResponses() = {
    val proof = db.getProofInfo(proofId)
    val model = db.getModel(proof.modelId)
    val conclusionFormula = KeYmaeraXProblemParser(model.keyFile)
    val conclusion = Sequent(IndexedSeq(), IndexedSeq(conclusionFormula))
    val trace = db.getExecutionTrace(proofId.toInt)
    val provable = trace.lastProvable
    val isProved = provable.isProved && provable.conclusion == conclusion
    new ProofVerificationResponse(proofId, isProved) :: Nil
  }
}

class IsLicenseAcceptedRequest(db : DBAbstraction) extends Request {
  def resultingResponses() = {
    new BooleanResponse(
      db.getConfiguration("license").config.contains("accepted") && db.getConfiguration("license").config.get("accepted").get.equals("true")
    ) :: Nil
  }
}

class AcceptLicenseRequest(db : DBAbstraction) extends Request {
  def resultingResponses() = {
    val newConfiguration = new ConfigurationPOJO("license", Map("accepted" -> "true"))
    db.updateConfiguration(newConfiguration)
    new BooleanResponse(true) :: Nil
  }
}

class RunScalaFileRequest(db: DBAbstraction, proofId: String, proof: File) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = ???
}

/////
// Requests for shutting down KeYmaera if KeYmaera is hosted locally.
/////

class IsLocalInstanceRequest() extends Request {
  override def resultingResponses(): List[Response] = new BooleanResponse(!HyDRAServerConfig.isHosted) :: Nil
}

class ExtractDatabaseRequest() extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    if(HyDRAServerConfig.isHosted)
      throw new Exception("Cannot extract the database on a hosted instance of KeYmaera X")

    val productionDatabase = edu.cmu.cs.ls.keymaerax.hydra.SQLite.ProdDB
    productionDatabase.syncDatabase()

    val today = Calendar.getInstance().getTime()
    val fmt = new SimpleDateFormat("MDY")

    val extractionPath = System.getProperty("user.home") + File.separator + s"extracted_${fmt.format(today)}.sqlite"
    val dbPath         = productionDatabase.dblocation

    val src = new File(dbPath)
    val dest = new File(extractionPath)
    new FileOutputStream(dest) getChannel() transferFrom(
      new FileInputStream(src) getChannel, 0, Long.MaxValue )


    //@todo Maybe instead do this in the production database and then have a catch all that undoes it.
    //That way we don't have to sync twice. Actually, I'm also not sure if this sync is necessary or not...
    val extractedDatabase = new SQLiteDB(extractionPath)
    extractedDatabase.updateConfiguration(new ConfigurationPOJO("extractedflag", Map("extracted" -> "true")))
    extractedDatabase.syncDatabase()

    new ExtractDatabaseResponse(extractionPath) :: Nil
  }
}

class ShutdownReqeuest() extends LocalhostOnlyRequest {
  override def resultingResponses() : List[Response] = {
    new Thread() {
      override def run() = {
        try {
          //Tell all scheduled tactics to stop.
          //@todo figure out which of these are actually necessary.
          System.out.flush()
          System.err.flush()
          ToolProvider.shutdown()
          System.out.flush()
          System.err.flush()
          HyDRAServerConfig.system.shutdown()
          System.out.flush()
          System.err.flush()
          this.synchronized {
            this.wait(4000)
          }
          System.out.flush()
          System.err.flush()
          System.exit(0) //should've already stopped the application by now.
        }
        catch {
          case _ : Exception => System.exit(-1)
        }

      }
    }.start

    new BooleanResponse(true) :: Nil
  }
}

class ExtractTacticRequest(db: DBAbstraction, proofIdStr: String) extends Request {
  private val proofId = Integer.parseInt(proofIdStr)

  override def resultingResponses(): List[Response] = {
    val exprText = BellePrettyPrinter(new ExtractTacticFromTrace(db).apply(proofId))
    new ExtractTacticResponse(exprText) :: Nil
  }
}

class ExtractProblemSolutionRequest(db: DBAbstraction, proofIdStr: String) extends Request {
  private val proofId = Integer.parseInt(proofIdStr)

  override def resultingResponses(): List[Response] = {
    val exprText = BellePrettyPrinter(new ExtractTacticFromTrace(db).apply(proofId))
    val problem = db.getModel(db.getProofInfo(proofId).modelId).keyFile
    new ExtractProblemSolutionResponse(problem + "\n" + "Solution.\n" + exprText + "\nEnd.") :: Nil
  }
}

class MockRequest(resourceName: String) extends Request {
  override def resultingResponses(): List[Response] = new MockResponse(resourceName) :: Nil
}
