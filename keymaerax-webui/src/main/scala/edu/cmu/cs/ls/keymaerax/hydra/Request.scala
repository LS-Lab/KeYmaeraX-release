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
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
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
import java.io.{File, FileInputStream, FileNotFoundException, FileOutputStream}
import java.text.SimpleDateFormat
import java.util.{Calendar, Locale}

import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.pt.{NoProofTermProvable, ProvableSig}

import scala.io.Source
import scala.collection.immutable._
import scala.collection.mutable
import edu.cmu.cs.ls.keymaerax.btactics.cexsearch
import edu.cmu.cs.ls.keymaerax.btactics.cexsearch.{BoundedDFS, BreadthFirstSearch, ProgramSearchNode, SearchNode}

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
    if (!permission(t)) new PossibleAttackResponse("Permission denied")::Nil
    else {
      assert(permission(t), "Permission denied but still responses queried (see completeRequest)")
      try {
        theSession = SessionManager.session(t)
        resultingResponses()
      } catch {
        //@note Avoids "Boxed Error" without error message by wrapping unchecked exceptions here.
        //      The web server translates exception into 500 response, the web UI picks them up in the error alert dialog
        // assert, ensuring
        case a: AssertionError => throw new Exception(
          "We're sorry, an internal safety check was violated, which may point to a bug. The safety check reports " + a.getMessage, a)
        // require
        case e: IllegalArgumentException => throw new Exception(
          "We're sorry, an internal safety check was violated, which may point to a bug. The safety check reports " + e.getMessage, e)
      }
    }
  }

  private var theSession: SessionManager.Session = _
  def session: SessionManager.Session = theSession

  def resultingResponses(): List[Response]

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
  override def permission(t: SessionToken): Boolean = t belongsTo username
}

/** A proof session storing information between requests. */
case class ProofSession(proofId: String, invGenerator: Generator[Formula], defs: KeYmaeraXDeclarationsParser.Declaration)

abstract class UserProofRequest(db: DBAbstraction, username: String, proofId: String) extends UserRequest(username) {
  override final def resultingResponses(): List[Response] = {
    if (proofId == "undefined" || proofId == "null") throw new Exception("The user interface lost track of the proof, please try reloading the page.") //@note Web UI bug
    //@todo faster query for existence
    else if(!db.userOwnsProof(username, proofId)) {
      new PossibleAttackResponse("Permission denied") :: Nil
    }
    else doResultingResponses()
  }

  protected def doResultingResponses(): List[Response]
}

abstract class LocalhostOnlyRequest() extends Request {
  override def permission(t: SessionToken): Boolean = !HyDRAServerConfig.isHosted //@todo change this to a literal false prior to deployment.
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Users
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateUserRequest(db: DBAbstraction, username: String, password: String, mode: String) extends Request {
  override def resultingResponses(): List[Response] = {
    val userExists = db.userExists(username)
    val sessionToken =
      if (!userExists) {
        db.createUser(username, password, mode)
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
  def resultingResponses(): List[Response] = {
    val proofs = db.getProofsForUser(userId).filterNot(_._1.temporary).map(proof =>
      (proof._1, "loaded"/*KeYmaeraInterface.getTaskLoadStatus(proof._1.proofId.toString).toString.toLowerCase*/))
    new ProofListResponse(proofs) :: Nil
  }
}

class UpdateProofNameRequest(db : DBAbstraction, userId: String, proofId : String, newName : String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    db.updateProofName(proofId, newName)
    new UpdateProofNameResponse(proofId, newName) :: Nil
  }
}

class FailedRequest(userId: String, msg: String, cause: Throwable = null) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = { new ErrorResponse(msg, cause) :: Nil }
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

class CounterExampleRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserProofRequest(db, userId, proofId) {
  def allFnToVar(fml: Formula, fn: Function): Formula = {
    fml.find(t => t match {
        case FuncOf(func, _) if fn.sort == Real => func == fn
        case PredOf(func, _) if fn.sort == Bool => func == fn
        case _ => false }) match {
      case Some((_, e: Term)) => allFnToVar(fml.replaceAll(e, Variable(fn.name, fn.index, Real)), fn)
      case Some((_, e: Formula)) => allFnToVar(fml.replaceAll(e, PredOf(Function(fn.name, fn.index, Unit, Bool), Nothing)), fn) //@todo beware of name clashes
      case None => fml
    }
  }

  def findCounterExample(fml: Formula, cexTool: CounterExampleTool): Option[Map[NamedSymbol, Expression]] = {
    val signature = StaticSemantics.signature(fml).filter({
      case Function(_, _, _, _, false) => true case _ => false }).map(_.asInstanceOf[Function])
    val lmf = signature.foldLeft[Formula](fml)((f, t) => allFnToVar(f, t))
    cexTool.findCounterExample(lmf) match {
      case Some(cex) => Some(cex.map({case (k, v) => signature.find(s => s.name == k.name && s.index == k.index).getOrElse(k) -> v }))
      case None => None
    }
  }

  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId)::Nil
      case Some(node) =>
        //@note not a tactic because we don't want to change the proof tree just by looking for counterexamples
        val sequent = node.goal.get
        val fml = sequent.toFormula
        def nonfoError = {
          val nonFOAnte = sequent.ante.filterNot(_.isFOL)
          val nonFOSucc = sequent.succ.filterNot(_.isFOL)
          new CounterExampleResponse("cex.nonfo", (nonFOSucc ++ nonFOAnte).head) :: Nil
        }
        try {
          ToolProvider.cexTool() match {
            case Some(cexTool) =>
              if (fml.isFOL) {
                findCounterExample(fml, cexTool) match {
                  //@todo return actual sequent, use collapsiblesequentview to display counterexample
                  case Some(cex) =>
                    new CounterExampleResponse("cex.found", fml, cex) :: Nil
                  case None => new CounterExampleResponse("cex.none") :: Nil
                }
              } else {
                /* TODO: Case on this instead */
                val qeTool:QETool = ToolProvider.qeTool().get
                val snode: SearchNode = ProgramSearchNode(fml)(qeTool)
                val search = new BoundedDFS(10)
                try {
                  search(snode) match {
                    case None => nonfoError
                    case Some(cex) =>
                      new CounterExampleResponse("cex.found", fml, cex.map) :: Nil
                  }
                } catch {
                  // Counterexample generation is quite hard for, e.g. ODEs, so expect some cases to be unimplemented.
                  // When that happens, just tell the user they need to simplify the formula more.
                  case _ : NotImplementedError => nonfoError
                }
              }
            case None => new CounterExampleResponse("cex.notool") :: Nil
          }
        } catch {
          case ex: MathematicaComputationAbortedException => new CounterExampleResponse("cex.timeout") :: Nil
        }
    }
  }
}

class SetupSimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(node) =>
        //@note not a tactic because we don't want to change the proof tree just by simulating
        val sequent = node.goal.get
        val fml = sequent.toFormula match {
          case Imply(True, succ) => succ //@todo really? below we error response if not an implication
          case f => f
        }
        if (ToolProvider.odeTool().isDefined) fml match {
          case Imply(initial, b@Box(prg, _)) =>
            // all symbols because we need frame constraints for constants
            val vars = (StaticSemantics.symbols(prg) ++ StaticSemantics.symbols(initial)).filter(_.isInstanceOf[Variable])
            val Box(prgPre, _) = vars.foldLeft[Formula](b)((b, v) => b.replaceAll(v, Variable("pre" + v.name, v.index, v.sort)))
            val stateRelEqs = vars.map(v => Equal(v.asInstanceOf[Term], Variable("pre" + v.name, v.index, v.sort))).reduceRightOption(And).getOrElse(True)
            val simSpec = Diamond(solveODEs(prgPre), stateRelEqs)
            new SetupSimulationResponse(addNonDetInitials(initial, vars), transform(simSpec)) :: Nil
          case _ => new ErrorResponse("Simulation only supported for formulas of the form initial -> [program]safe") :: Nil
        } else new ErrorResponse("No simulation tool available, please configure Mathematica") :: Nil
    }
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
    val solution = replaceFree(ToolProvider.odeTool().get.odeSolve(ode, time, iv).get, iv.map(_.swap))
    val flatSolution = flattenConjunctions(solution).
      sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size)
    Compose(
      flatSolution.map({ case Equal(v: Variable, r) => Assign(v, r) }).reduceRightOption(Compose).getOrElse(Test(True)),
      Test(evoldomain))
  }

  private def replaceFree(f: Formula, vars: Map[Variable, Variable]) = {
    vars.keySet.foldLeft[Formula](f)((b, v) => b.replaceFree(v, vars(v)))
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

class SimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, initial: Formula, stateRelation: Formula, steps: Int, n: Int, stepDuration: Term) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
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
      case Some((upd, lv)) => (Some(upd), Some(lv))
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
    val contents: String = Source.fromInputStream(reader).mkString
    val source: JsArray = contents.parseJson.asInstanceOf[JsArray]

    // TODO provide classes and spray JSON protocol to convert
    val os = System.getProperty("os.name")
    val osKey = osKeyOf(os.toLowerCase)
    val jvmBits = System.getProperty("sun.arch.data.model")
    val osPathGuesses = source.elements.find(osCfg => osCfg.asJsObject.getFields("os").head.convertTo[String] == osKey) match {
      case Some(opg) => opg.asJsObject.getFields("mathematicaPaths").head.convertTo[List[JsObject]]
      case None => throw new IllegalStateException("No default configuration for Unknown OS")
    }

    val pathTuples = osPathGuesses.map(osPath =>
      (osPath.getFields("version").head.convertTo[String],
       osPath.getFields("kernelPath").head.convertTo[String],
       osPath.getFields("kernelName").head.convertTo[String],
       osPath.getFields("jlinkPath").head.convertTo[String] +
         (if (jvmBits == "64") "-" + jvmBits else "") + File.separator,
       osPath.getFields("jlinkName").head.convertTo[String]))

    val (suggestionFound, suggestion) = pathTuples.find(path => new java.io.File(path._2 + path._3).exists &&
        new java.io.File(path._4 + path._5).exists) match {
      case Some(s) => (true, s)
      case None => (false, pathTuples.head) // use the first configuration as suggestion when nothing else matches
    }

    new MathematicaConfigSuggestionResponse(os, jvmBits, suggestionFound, suggestion._1, suggestion._2, suggestion._3, suggestion._4, suggestion._5, pathTuples) :: Nil
  }

  private def osKeyOf(osName: String): String = {
    if (osName.contains("win")) "Windows"
    else if (osName.contains("mac")) "MacOS"
    else if (osName.contains("nix") || osName.contains("nux") || osName.contains("aix")) "Unix"
    else "Unknown"
  }
}

class SystemInfoRequest(db: DBAbstraction) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    new SystemInfoResponse(
      System.getProperty("os.name"),
      System.getProperty("os.version"),
      System.getProperty("java.home"),
      System.getProperty("java.vendor"),
      System.getProperty("java.version"),
      System.getProperty("sun.arch.data.model")) :: Nil
  }
}

class GetToolRequest(db: DBAbstraction) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    //@todo more/different tools
    new KvpResponse("tool", db.getConfiguration("tool").config("qe")) :: Nil
  }
}

class SetToolRequest(db: DBAbstraction, tool: String) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    //@todo more/different tools
    if (tool != "mathematica" && tool != "z3") new ErrorResponse("Unknown tool " + tool + ", expected either 'mathematica' or 'z3'")::Nil
    else {
      assert(tool == "mathematica" || tool == "z3", "Expected either Mathematica or Z3 tool")
      val toolConfig = new ConfigurationPOJO("tool", Map("qe" -> tool))
      db.updateConfiguration(toolConfig)
      new KvpResponse("tool", tool) :: Nil
    }
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

class GetUserThemeRequest(db: DBAbstraction, userName: String) extends UserRequest(userName) {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration(userName).config
    new PlainResponse("theme" -> JsString(config.getOrElse("theme", "app"))) :: Nil
  }
}

class SetUserThemeRequest(db: DBAbstraction, userName: String, theme: String) extends UserRequest(userName) {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration(userName)
    db.updateConfiguration(new ConfigurationPOJO(userName, config.config.updated("theme", theme)))
    new BooleanResponse(true) :: Nil
  }
}


class MathematicaStatusRequest(db : DBAbstraction) extends Request {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration("mathematica").config
    new ToolStatusResponse("Mathematica", config.contains("linkName") && config.contains("jlinkLibDir")) :: Nil
  }
}

class Z3StatusRequest(db : DBAbstraction) extends Request {
  override def resultingResponses(): List[Response] = new ToolStatusResponse("Z3", true) :: Nil
}

class ListExamplesRequest(db: DBAbstraction, userId: String) extends UserRequest(userId) {
  override def resultingResponses(): List[Response] = {
    //@todo read from the database/some web page?
    val examples =
      new ExamplePOJO(0, "STTT Tutorial",
        "Automated stop sign braking for cars",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/sttt/sttt.json",
        "/examples/tutorials/sttt/sttt.png", 1) ::
      new ExamplePOJO(1, "CPSWeek 2016 Tutorial",
        "Proving ODEs",
        "http://www.ls.cs.cmu.edu/KeYmaeraX/KeYmaeraX-tutorial.pdf",
        "classpath:/examples/tutorials/cpsweek/cpsweek.json",
        "/examples/tutorials/cpsweek/cpsweek.png", 1) ::
      new ExamplePOJO(2, "FM 2016 Tutorial",
        "Tactics and Proofs",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/fm/fm.json",
        "/examples/tutorials/fm/fm.png", 1) ::
      new ExamplePOJO(3, "Beginner's Tutorial",
        "Feature Tour Tutorial",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/basic/basic.json",
        "/examples/tutorials/fm/fm.png", 0) ::
      Nil

    val user = db.getUser(userId)
    new ListExamplesResponse(examples.filter(_.level <= user.level)) :: Nil
  }
}


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Models
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/** Creates a model from a formula without variable declarations.
  * Separate from CreateModelRequest so that we don't end up swallowing parse errors or returning the wrong parse error. */
class CreateModelFromFormulaRequest(db: DBAbstraction, userId: String, nameOfModel: String, formula: String) extends UserRequest(userId) {
  private var createdId : Option[String] = None

  def resultingResponses(): List[Response] = try {
    KeYmaeraXParser(formula) match {
      case _: Formula =>
        if(db.getModelList(userId).map(_.name).contains(nameOfModel))
          new BooleanResponse(false, Some("A model with name " + nameOfModel + " already exists, please choose a different name")) :: Nil
        else {
          createdId = db.createModel(userId, nameOfModel, formula, currentDate()).map(_.toString)
          new BooleanResponse(createdId.isDefined) :: Nil
        }
      case t => new ErrorResponse("Expected a formula, but got the " + t.kind + " " + formula) :: Nil
    }
  } catch {
    case e: ParseException => new ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
  }

  def getModelId: String = createdId match {
    case Some(s) => s
    case None => throw new IllegalStateException("Requested created model ID before calling resultingResponses, or else an error occurred during creation.")
  }
}

class CreateModelRequest(db : DBAbstraction, userId : String, nameOfModel : String, keyFileContents : String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    try {
      KeYmaeraXProblemParser.parseAsProblemOrFormula(keyFileContents) match {
        case _: Formula =>
          if (db.getModelList(userId).map(_.name).contains(nameOfModel)) {
            new BooleanResponse(false, Some("A model with name " + nameOfModel + " already exists, please choose a different name")) :: Nil
          } else {
            val createdId = db.createModel(userId, nameOfModel, keyFileContents, currentDate()).map(x => x.toString)
            new BooleanResponse(createdId.isDefined) :: Nil
          }
        case t => new ErrorResponse("Expected a model formula, but got a file with a " + t.kind) :: Nil
      }
    } catch {
      case e: ParseException => new ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
    }
  }
}

class UpdateModelRequest(db: DBAbstraction, userId: String, modelId: String, name: String, title: String,
                         description: String) extends UserRequest(userId) {
  private def emptyToOption(s: String): Option[String] = if (s.isEmpty) None else Some(s)

  def resultingResponses(): List[Response] = {
    db.updateModel(modelId.toInt, name, emptyToOption(title), emptyToOption(description))
    new BooleanResponse(true) :: Nil
  }
}

class UploadArchiveRequest(db: DBAbstraction, userId: String, kyaFileContents: String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    try {
      val archiveEntries = KeYmaeraXArchiveParser.read(kyaFileContents)
      val (failedModels, succeededModels) = archiveEntries.foldLeft((List[String](), List[String]()))({ case ((failedImports, succeededImports), (name, modelFileContent, _, tactic)) =>
        val uniqueModelName = db.getUniqueModelName(userId, name)
        db.createModel(userId, uniqueModelName, modelFileContent, currentDate(), None, None, None,
          tactic.headOption.map(_._2)) match {
          case None =>
            // really should not get here. print and continue importing the remainder of the archive
            println(s"Model import failed: model $name already exists in the database and attempt of importing under uniquified name $uniqueModelName failed. Continuing with remainder of the archive.")
            (failedImports :+ name, succeededImports)
          case Some(modelId) =>
            tactic.foreach({ case (tname, ttext) =>
              db.createProofForModel(modelId, tname, "Proof from archive", currentDate(), Some(ttext))
            })
            (failedImports, succeededImports :+ name)
        }
      })
      if (failedModels.isEmpty) new BooleanResponse(true) :: Nil
      else throw new Exception("Failed to import the following models\n" + failedModels.mkString("\n") +
        "\nSucceeded importing:\n" + succeededModels.mkString("\n") +
        "\nModel import may have failed because of model name clashed. Try renaming the failed models in the archive to names that do not yet exist in your model list.")
    } catch {
      case e: ParseException => new ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
    }
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

class DeleteProofRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    //TaskManagement.forceDeleteTask(proofId)
    val success = db.deleteProof(Integer.parseInt(proofId))
    new BooleanResponse(success) :: Nil
  }
}

class GetModelListRequest(db : DBAbstraction, userId : String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    new ModelListResponse(db.getModelList(userId).filterNot(_.temporary)) :: Nil
  }
}

class GetModelRequest(db : DBAbstraction, userId : String, modelId : String) extends UserRequest(userId) {
  private val model: ModelPOJO = db.getModel(modelId)
  insist(model.userId == userId, s"model $modelId does not belong to $userId")
  def resultingResponses(): List[Response] = {
    new GetModelResponse(model) :: Nil
  }
}

class GetModelTacticRequest(db : DBAbstraction, userId : String, modelId : String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val model = db.getModel(modelId)
    new GetModelTacticResponse(model) :: Nil
  }
}

class AddModelTacticRequest(db : DBAbstraction, userId : String, modelId : String, tactic: String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val tacticId = db.addModelTactic(modelId, tactic)
    new BooleanResponse(tacticId.isDefined) :: Nil
  }
}

class ModelPlexMandatoryVarsRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val model = db.getModel(modelId)
    val modelFml = KeYmaeraXProblemParser.parseAsProblemOrFormula(model.keyFile)
    new ModelPlexMandatoryVarsResponse(model, StaticSemantics.boundVars(modelFml).symbols.filter(_.isInstanceOf[BaseVariable])) :: Nil
  }
}

class ModelPlexRequest(db: DBAbstraction, userId: String, modelId: String, monitorKind: String, monitorShape: String,
                       conditionKind: String, additionalVars: List[String]) extends UserRequest(userId) {
  def resultingResponses(): List[Response]  = {
    val model = db.getModel(modelId)
    val modelFml = KeYmaeraXProblemParser.parseAsProblemOrFormula(model.keyFile)
    val vars = (StaticSemantics.boundVars(modelFml).symbols.filter(_.isInstanceOf[BaseVariable])
      ++ additionalVars.map(_.asVariable)).toList
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(modelFml, vars:_*)
    val monitorCond = (monitorKind, ToolProvider.simplifierTool()) match {
      case ("controller", tool) =>
        val foResult = TactixLibrary.proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
        try {
          TactixLibrary.proveBy(foResult.subgoals.head,
            SaturateTactic(ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)))
        } catch {
          case _: Throwable => foResult
        }
      case ("model", tool) => TactixLibrary.proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) &
        ModelPlex.optimizationOneWithSearch(tool, assumptions)(1) /*& SimplifierV2.simpTac(1)*/)
    }

    if (monitorCond.subgoals.size == 1) (conditionKind, monitorShape) match {
      case ("kym", "boolean") => new ModelPlexResponse(model, monitorCond.subgoals.head.toFormula) :: Nil
      case ("kym", "metric") => new ModelPlexResponse(model, ModelPlex.toMetric(monitorCond.subgoals.head.toFormula)) :: Nil
      case ("c", "boolean") => new ModelPlexCCodeResponse(model, monitorCond.subgoals.head.toFormula) :: Nil
    }
    else new ErrorResponse("ModelPlex failed") :: Nil
  }
}

class TestSynthesisRequest(db: DBAbstraction, userId: String, modelId: String, monitorKind: String, testKinds: Map[String, Boolean],
                           amount: Int, timeout: Option[Int]) extends UserRequest(userId) {
  def resultingResponses(): List[Response]  = {
    println("Got Test Synthesis Request")
    val model = db.getModel(modelId)
    val modelFml = KeYmaeraXProblemParser.parseAsProblemOrFormula(model.keyFile)
    val vars = StaticSemantics.boundVars(modelFml).symbols.filter(_.isInstanceOf[BaseVariable]).toList
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(modelFml, vars:_*)
    val monitorCond = (monitorKind, ToolProvider.simplifierTool()) match {
      case ("controller", tool) =>
        val foResult = TactixLibrary.proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
        try {
          TactixLibrary.proveBy(foResult.subgoals.head,
            SaturateTactic(ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)))
        } catch {
          case _: Throwable => foResult
        }
      case ("model", tool) => TactixLibrary.proveBy(modelplexInput,
        ModelPlex.modelMonitorByChase(1) &
        SimplifierV3.simpTac(Nil, SimplifierV3.defaultFaxs, SimplifierV3.arithBaseIndex)(1) &
        ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)
      )
    }

    def variance(vals: Map[Term, Term]): Number = {
      val (pre, post) = vals.partition({ case (v, _) => v.isInstanceOf[BaseVariable] })
      val postByPre: Map[Term, BigDecimal] = post.map({
        case (FuncOf(Function(name, idx, Unit, Real, _), _), Number(value)) if name.endsWith("post") =>
          Variable(name.substring(0, name.length-"post".length), idx) -> value
        case (v, Number(value)) => v -> value
        })
      Number(pre.map({
        case (v, Number(value)) if postByPre.contains(v) => (value - postByPre(v))*(value - postByPre(v))
        case _ => BigDecimal(0)
      }).sum)
    }

    val Imply(True, cond) = monitorCond.subgoals.head.toFormula

    val assumptionsCond = assumptions.reduceOption(And).getOrElse(True)
    val testSpecs: List[(String, Formula)] = testKinds.map({
      case ("compliant", true) => Some("compliant" -> cond)
      case ("incompliant", true) => Some("incompliant" -> Not(cond))
      case _ => None
    }).filter(_.isDefined).map(c => c.get._1 -> And(assumptionsCond, c.get._2)).toList

    val metric = ModelPlex.toMetric(cond)
    ToolProvider.cexTool() match {
      case Some(tool: Mathematica) =>
        val synth = new TestSynthesis(tool)
        //val testCases = synth.synthesizeTestConfig(testCondition, amount, timeout)
        val testCases = testSpecs.map(ts => ts._1 -> synth.synthesizeTestConfig(ts._2, amount, timeout))
        val tcSmVar = testCases.map(tc => tc._1 -> tc._2.map(tcconfig =>
          (tcconfig,
           //@note tcconfig (through findInstance) may contain values that later lead to problems (e.g., division by 0)
           try { Some(synth.synthesizeSafetyMarginCheck(metric, tcconfig)) } catch { case _: ToolException => None },
           variance(tcconfig))
        ))
        new TestSynthesisResponse(model, metric, tcSmVar) :: Nil
      case None => new ErrorResponse("Test case synthesis failed, missing Mathematica") :: Nil
    }
  }
}


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proofs of models
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateProofRequest(db : DBAbstraction, userId : String, modelId : String, name : String, description : String)
  extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val proofId = db.createProofForModel(modelId, name, description, currentDate(), None)
    new CreatedIdResponse(proofId) :: Nil
  }
}

class CreateModelTacticProofRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val model = db.getModel(modelId)
    model.tactic match {
      case Some(tacticText) =>
        val proofId = db.createProofForModel(Integer.parseInt(modelId), model.name + " from tactic",
          "Proof from tactic", currentDate(), Some(tacticText))
        new CreatedIdResponse(proofId.toString) :: Nil
      case None => new ErrorResponse("Model " + modelId + " does not have a tactic associated")::Nil
    }
  }
}

class ProofsForModelRequest(db : DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = {
    val proofs = db.getProofsForModel(modelId).map(proof =>
      (proof, "loaded"/*KeYmaeraInterface.getTaskLoadStatus(proof.proofId.toString).toString.toLowerCase*/))
    new ProofListResponse(proofs) :: Nil
  }
}

class OpenProofRequest(db: DBAbstraction, userId: String, proofId: String, wait: Boolean = false) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val modelId = db.getProofInfo(proofId).modelId
    if (modelId.isEmpty) throw new Exception("Database consistency error: unable to open proof " + proofId + ", because it does not refer to a model")
    else if (db.getModel(modelId.get).userId != userId) new PossibleAttackResponse("Permission denied")::Nil
    else {
      insist(db.getModel(db.getProofInfo(proofId).modelId.getOrElse(throw new CoreException(s"Cannot open a proof without model, proofId=$proofId"))).userId == userId, s"User $userId does not own the model associated with proof $proofId")

      val proofInfo = db.getProofInfo(proofId)
      proofInfo.modelId match {
        case None => new ErrorResponse("Unable to open proof " + proofId + ", because it does not refer to a model")::Nil // duplicate check to above
        case Some(mId) =>
          val generator = new ConfigurableGenerator[Formula]()
          KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p -> inv))
          val defsGenerator = new ConfigurableGenerator[Expression]()
          val (d, _) = KeYmaeraXProblemParser.parseProblem(db.getModel(mId).keyFile)
          d.substs.foreach(sp => defsGenerator.products += (sp.what -> sp.repl))
          session += proofId -> ProofSession(proofId, generator, d)
          TactixLibrary.invGenerator = generator //@todo should not store invariant generator globally for all users
          new OpenProofResponse(proofInfo, "loaded" /*TaskManagement.TaskLoadStatus.Loaded.toString.toLowerCase()*/) :: Nil
      }
    }
  }
}

/**
  * Gets all tasks of the specified proof. A task is some work the user has to do. It is not a KeYmaera task!
  *
  * @param db Access to the database.
  * @param userId Identifies the user.
  * @param proofId Identifies the proof.
  */
class GetAgendaAwesomeRequest(db : DBAbstraction, userId : String, proofId : String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree: ProofTree = DbProofTree(db, proofId)
    val leaves = tree.openGoals
    val closed = tree.openGoals.isEmpty && tree.verifyClosed
    //@todo goal names
    val agendaItems: List[AgendaItem] = leaves.map(n => AgendaItem(n.id.toString, "Unnamed Goal", proofId))
    new AgendaAwesomeResponse(proofId, tree.root, leaves, agendaItems, closed) :: Nil
  }
}

case class GetAgendaItemRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    //@todo seems unused
    ???
//    val closed = db.getProofInfo(proofId).closed
//    val tree = ProofTree.ofTrace(db.getExecutionTrace(proofId.toInt), proofFinished = closed)
//    val possibleItems = db.agendaItemsForProof(proofId.toInt)
//    tree.agendaItemForNode(NodeId.fromString(nodeId), possibleItems) match {
//      case Some(item) => new GetAgendaItemResponse (item) :: Nil
//      case None => new ErrorResponse("No information stored for agenda item " + nodeId) :: Nil
//    }
  }
}

case class SetAgendaItemNameRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String,
                                    displayName: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.nodeIdFromString(nodeId) match {
      case Some(nId) =>
        db.getAgendaItem(proofId.toInt, nId) match {
          case Some(item) =>
            val newItem = AgendaItemPOJO(item.itemId, item.proofId, item.initialProofNode, displayName)
            db.updateAgendaItem(newItem)
            new SetAgendaItemNameResponse(newItem) :: Nil
          case None =>
            val id = db.addAgendaItem(proofId.toInt, nId, displayName)
            new SetAgendaItemNameResponse(AgendaItemPOJO(id, proofId.toInt, nId, displayName)) :: Nil
        }
      case None => new ErrorResponse("Unknown node " + nodeId)::Nil
    }
  }
}

class ProofTaskParentRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId).flatMap(_.parent) match {
      case Some(parent) => new ProofTaskParentResponse(parent)::Nil
      case None => new ErrorResponse("Cannot get parent of node " + nodeId + ", node might be unknown or root")::Nil
    }
  }
}

case class GetPathAllRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    var node: Option[ProofTreeNode] = tree.locate(nodeId)
    var path: List[ProofTreeNode] = Nil
    while (node.nonEmpty) {
      path = node.get::path
      node = node.get.parent
    }
    val parentsRemaining = 0
    new GetPathAllResponse(path.reverse, parentsRemaining)::Nil
  }
}

case class GetBranchRootRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    var currNode = tree.locate(nodeId)
    var done = false
    while (currNode.flatMap(_.parent).nonEmpty && !done) {
      currNode = currNode.flatMap(_.parent)
      /* Don't stop at the first node just because it branches (it may be the end of one branch and the start of the
      * next), but if we see branching anywhere else we've found the end of our branch. */
      done = currNode.get.children.size > 1
    }
    currNode match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(n) => new GetBranchRootResponse(n) :: Nil
    }

  }
}

class ProofTaskExpandRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => throw new Exception("Unknown node " + nodeId)
      case Some(node) if node.children.isEmpty || node.children.head.maker.isEmpty =>
        new ErrorResponse("Unable to expand node " + nodeId + " of proof " + proofId + ", because it did not record a tactic")::Nil
      case Some(node) if node.children.nonEmpty && node.children.head.maker.isDefined =>
        assert(node.children.nonEmpty && node.children.head.maker.isDefined, "Unable to expand node without tactics")
        //@note all children share the same maker
        val (localProvable, parentStep, parentRule) = (node.localProvable, node.children.head.maker.get, node.children.head.makerShortName.get)
        val localProofId = db.createProof(localProvable)
        val innerInterpreter = SpoonFeedingInterpreter(localProofId, db.createProof,
          RequestHelper.listenerFactory(db), SequentialInterpreter, 1, strict=false)
        val parentTactic = BelleParser(parentStep)
        innerInterpreter(parentTactic, BelleProvable(localProvable))

        val trace = db.getExecutionTrace(localProofId)
        if (trace.steps.size == 1 && trace.steps.head.rule == parentRule) {
          DerivationInfo.locate(parentTactic) match {
            case Some(ptInfo) => ExpandTacticResponse(localProofId, ptInfo.codeName, "", Nil, Nil) :: Nil
            case None => new ErrorResponse("No further details available") :: Nil
          }
        } else {
          val innerTree = DbProofTree(db, localProofId.toString).load()
          val stepDetails = innerTree.tacticString
          val innerSteps = innerTree.nodes
          val agendaItems: List[AgendaItem] = innerTree.openGoals.map(n =>
            AgendaItem(n.id.toString, "Unnamed Goal", proofId))

          ExpandTacticResponse(localProofId, parentStep, stepDetails, innerSteps, agendaItems) :: Nil
        }
    }
  }
}

class StepwiseTraceRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val innerSteps = tree.nodes
    val agendaItems: List[AgendaItem] = tree.openGoals.map(n =>
      AgendaItem(n.id.toString, "Unnamed Goal", proofId.toString))
    //@todo fill in parent step for empty ""
    new ExpandTacticResponse(proofId.toInt, "", tree.tacticString, innerSteps, agendaItems) :: Nil
  }
}

class GetSequentStepSuggestionRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => ApplicableAxiomsResponse(Nil, Map.empty) :: Nil
      case Some(node) => node.goal match {
        case None => ApplicableAxiomsResponse(Nil, Map.empty) :: Nil //@note node closed
        case Some(seq) =>
          if (seq.isFOL) {
            val folSuggestions = "QE"::"abbrv"::"hideL"::Nil
            // todo: counterexample, find assumptions + general help
            val tactics = folSuggestions.map(s => (DerivationInfo(s), None))
            ApplicableAxiomsResponse(tactics, Map.empty) :: Nil
          } else {
            // find "largest" succedent formula with programs and suggest top-level popup content
            val pos = SuccPosition(1)
            ApplicableAxiomsResponse(node.applicableTacticsAt(pos), node.tacticInputSuggestions(pos)) :: Nil
          }
      }
    }
  }
}

class GetApplicableAxiomsRequest(db:DBAbstraction, userId: String, proofId: String, nodeId: String, pos:Position)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    if (tree.isClosed) return new ApplicableAxiomsResponse(Nil, Map.empty) :: Nil

    tree.locate(nodeId).map(n => (n.applicableTacticsAt(pos), n.tacticInputSuggestions(pos))) match {
      case Some((tactics, inputs)) => new ApplicableAxiomsResponse(tactics, inputs) :: Nil
      case None => new ApplicableAxiomsResponse(Nil, Map.empty) :: Nil
    }
  }
}

class GetApplicableTwoPosTacticsRequest(db:DBAbstraction, userId: String, proofId: String, nodeId: String,
                                        pos1: Position, pos2: Position) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    if (tree.isClosed) return new ApplicableAxiomsResponse(Nil, Map.empty) :: Nil
    tree.locate(nodeId).map(n => n.applicableTacticsAt(pos1, Some(pos2))) match {
      case None => new ApplicableAxiomsResponse(Nil, Map.empty) :: Nil
      case Some(tactics) => new ApplicableAxiomsResponse(tactics, Map.empty) :: Nil
    }
  }
}

class GetDerivationInfoRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, axiomId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val info = (DerivationInfo.ofCodeName(axiomId), UIIndex.comfortOf(axiomId).map(DerivationInfo.ofCodeName)) :: Nil
    new ApplicableAxiomsResponse(info, Map.empty) :: Nil
  }
}

class ExportCurrentSubgoal(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    DbProofTree(db, proofId).locate(nodeId).flatMap(_.goal) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(goal) =>
        val provable = ProvableSig.startProof(goal)
        val lemma = Lemma.apply(provable, List(ToolEvidence(List("tool" -> "mock"))), None)
        new KvpResponse("sequent", "Provable: \n" + provable.prettyString + "\n\nLemma:\n" + lemma.toString) :: Nil
    }
  }
}

class ExportFormula(db: DBAbstraction, userId: String, proofId: String, nodeId: String, formulaId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    if(!db.getProofsForUser(userId).exists(p => p._1.proofId == proofId.toInt)) {
      new PossibleAttackResponse("Permission denied") :: Nil
    } else {
      DbProofTree(db, proofId).locate(nodeId).flatMap(_.goal) match {
        case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
        case Some(goal) =>
          val formula = goal(SeqPos(formulaId.toInt))
          new KvpResponse("formula", formula.prettyString) :: Nil
      }
    }
  }
}

case class BelleTermInput(value: String, spec:Option[ArgInfo])

class GetStepRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId).flatMap(_.goal) match {
      case None => new ApplicableAxiomsResponse(Nil, Map.empty) :: Nil
      case Some(goal) =>
        goal.sub(pos) match {
          case Some(fml: Formula) =>
            UIIndex.theStepAt(fml, Some(pos)) match {
              case Some(step) => new ApplicableAxiomsResponse((DerivationInfo(step), None) :: Nil, Map.empty) :: Nil
              case None => new ApplicableAxiomsResponse(Nil, Map.empty) :: Nil
            }
          case _ => new ApplicableAxiomsResponse(Nil, Map.empty) :: Nil
        }
    }
  }
}

class GetFormulaPrettyStringRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    DbProofTree(db, proofId).locate(nodeId).flatMap(_.goal.flatMap(_.sub(pos))) match {
      case None => new ErrorResponse("Unknown position " + pos + " at node " + nodeId)::Nil
      case Some(e: Expression) => new PlainResponse("prettyString" -> JsString(e.prettyString))::Nil
    }
  }
}

class CheckTacticInputRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, tacticId: String,
                              paramName: String, paramType: String, paramValue: String)
  extends UserProofRequest(db, userId, proofId) {

  /** Prints a sort as users might expect from other web UI presentations. */
  private def printSort(s: Sort): String = s match {
    case Unit => ""
    case Real => "R"
    case Bool => "B"
    case Tuple(l, r) => printSort(l) + "," + printSort(r)
  }

  /** Prints a named symbol as users might expect from other web UI presentations. */
  private def printNamedSymbol(n: NamedSymbol): String = n match {
    case _: Variable => "variable " + n.prettyString
    case Function(_, _, domain, _, _) => "function " + n.prettyString + "(" + printSort(domain) + ")"
  }

  /** Basic input sanity checks w.r.t. symbols in `sequent`. */
  private def checkInput(sequent: Sequent, input: BelleTermInput, defs: KeYmaeraXProblemParser.Declaration): Response = {
    try {
      val (arg, exprs) = input match {
        case BelleTermInput(value, Some(arg: TermArg)) => arg -> (KeYmaeraXParser(value) :: Nil)
        case BelleTermInput(value, Some(arg: FormulaArg)) => arg -> (KeYmaeraXParser(value) :: Nil)
        case BelleTermInput(value, Some(arg: VariableArg)) => arg -> (KeYmaeraXParser(value) :: Nil)
        case BelleTermInput(value, Some(arg: ExpressionArg)) => arg -> (KeYmaeraXParser(value) :: Nil)
        case BelleTermInput(value, Some(arg@ListArg(_, "formula", _))) => arg -> value.split(",").map(KeYmaeraXParser).toList
      }

      val sortMismatch = arg match {
        case _: TermArg if exprs.size == 1 && exprs.head.kind == TermKind => None
        case _: FormulaArg if exprs.size == 1 && exprs.head.kind == FormulaKind => None
        case _: VariableArg if exprs.size == 1 && exprs.head.kind == TermKind && exprs.head.isInstanceOf[Variable] => None
        case _: ExpressionArg if exprs.size == 1 => None
        case ListArg(_, "formula", _) if exprs.forall(_.kind == FormulaKind) => None
        case _ => Some("Expected " + arg.sort + ", but got " + exprs.map(_.kind).mkString(",") + " " + exprs.map(_.prettyString).mkString(","))
      }

      sortMismatch match {
        case None =>
          val symbols = StaticSemantics.symbols(sequent)
          val paramFV: Set[NamedSymbol] =
            exprs.flatMap(e => StaticSemantics.freeVars(e).toSet ++ StaticSemantics.signature(e)).toSet -- defs.asFunctions - Function("old", None, Real, Real)

          val (hintFresh, allowedFresh) = arg match {
            case _: VariableArg if arg.allowsFresh.contains(arg.name) => (Nil, Nil)
            case _ => (paramFV -- symbols, arg.allowsFresh) //@todo would need other inputs to check
          }

          if (hintFresh.size > allowedFresh.size) {
            val fnVarMismatch = hintFresh.map(fn => fn -> symbols.find(s => s.name == fn.name && s.index == fn.index)).
              filter(_._2.isDefined)
            val msg =
              if (fnVarMismatch.isEmpty) "Argument " + arg.name + " uses new names that do not occur in the sequent: " + hintFresh.mkString(",") +
                (if (allowedFresh.nonEmpty) ", expected new names only as introduced for " + allowedFresh.mkString(",")
                else ", is it a typo?")
              else "Argument " + arg.name + " function/variable mismatch: " +
                fnVarMismatch.map(m => "have " + printNamedSymbol(m._1) + ", expected " + printNamedSymbol(m._2.get)).mkString(",")
            BooleanResponse(flag=false, Some(msg))
          } else {
            BooleanResponse(flag=true)
          }
        case Some(mismatch) => BooleanResponse(flag=false, Some(mismatch))
      }
    } catch {
      case ex: ParseException => BooleanResponse(flag=false, Some(ex.msg))
    }
  }

  override protected def doResultingResponses(): List[Response] = {
    val info = DerivationInfo(tacticId)
    val expectedInputs = info.inputs
    val paramInfo = expectedInputs.find(_.name == paramName)
    val isIllFormed = paramInfo.isEmpty || paramValue.isEmpty
    if (!isIllFormed) {
      val input = BelleTermInput(paramValue, expectedInputs.find(_.name == paramName))

      val tree: ProofTree = DbProofTree(db, proofId)
      tree.locate(nodeId) match {
        case None => BooleanResponse(flag=false, Some("Unknown node " + nodeId + " in proof " + proofId)) :: Nil
        case Some(node) if node.goal.isEmpty => BooleanResponse(flag=false, Some("Node " + nodeId + " does not have a goal")) :: Nil
        case Some(node) if node.goal.isDefined =>
          val sequent = node.goal.get
          val proofSession = session(proofId).asInstanceOf[ProofSession]
          checkInput(sequent, input, proofSession.defs)::Nil
      }
    } else {
      val msg =
        if (paramValue.isEmpty) "Missing value of parameter " + paramName
        else "Parameter " + paramName + " not a valid argument of tactic " + tacticId + ", expected one of " + expectedInputs.map(_.name).mkString(",")
      BooleanResponse(flag=false, Some(msg))::Nil
    }
  }

}

/* If pos is Some then belleTerm must parse to a PositionTactic, else if pos is None belleTerm must parse
* to a Tactic */
class RunBelleTermRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, belleTerm: String,
                          pos: Option[PositionLocator], pos2: Option[PositionLocator] = None,
                          inputs:List[BelleTermInput] = Nil, consultAxiomInfo: Boolean = true, stepwise: Boolean = false)
  extends UserProofRequest(db, userId, proofId) {
  /** Turns belleTerm into a specific tactic expression, including input arguments */
  private def fullExpr(sequent: Sequent) = {
    val paramStrings: List[String] = inputs.map{
      case BelleTermInput(value, Some(_:TermArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(_:FormulaArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(_:VariableArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(_:ExpressionArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(ListArg(_, "formula", _))) => "[" + value.split(",").map("{`"+_+"`}").mkString(",") + "]"
      case BelleTermInput(value, None) => value
    }
    val specificTerm = if (consultAxiomInfo) RequestHelper.getSpecificName(belleTerm, sequent, pos, pos2, _.codeName) else belleTerm
    if (inputs.isEmpty && pos.isEmpty) { assert(pos2.isEmpty, "Undefined pos1, but defined pos2"); specificTerm }
    else if (inputs.isEmpty && pos.isDefined && pos2.isEmpty) { specificTerm + "(" + pos.get.prettyString + ")" }
    else if (inputs.isEmpty && pos.isDefined && pos2.isDefined) { specificTerm + "(" + pos.get.prettyString + "," + pos2.get.prettyString + ")" }
    else specificTerm + "(" + paramStrings.mkString(",") + ")"
  }

  private class TacticPositionError(val msg:String,val pos: edu.cmu.cs.ls.keymaerax.parser.Location,val inlineMsg: String) extends Exception

  override protected def doResultingResponses(): List[Response] = {
    val proof = db.getProofInfo(proofId)
    if (proof.closed) new ErrorResponse("Can't execute tactics on a closed proof") :: Nil
    else {
      val tree: ProofTree = DbProofTree(db, proofId)
      tree.locate(nodeId) match {
        case None => new ErrorResponse("Unknown node " + nodeId + " in proof " + proofId)::Nil
        case Some(node) if node.goal.isEmpty => new ErrorResponse("Node " + nodeId + " does not have a goal")::Nil
        case Some(node) if node.goal.isDefined =>
          val sequent = node.goal.get

          try {
            val proofSession = session(proofId).asInstanceOf[ProofSession]
            val expr = BelleParser.parseWithInvGen(fullExpr(sequent), Some(proofSession.invGenerator), proofSession.defs)

            val appliedExpr: BelleExpr = (pos, pos2, expr) match {
              case (None, None, _: AtPosition[BelleExpr]) =>
                throw new TacticPositionError("Can't run a positional tactic without specifying a position", expr.getLocation, "Expected position in argument list but found none")
              case (None, None, _) => expr
              case (Some(position), None, expr: AtPosition[BelleExpr]) => expr(position)
              case (Some(_), None, expr: BelleExpr) => expr
              case (Some(Fixed(p1, None, _)), Some(Fixed(p2, None, _)), expr: BuiltInTwoPositionTactic) => expr(p1, p2)
              case (Some(_), Some(_), expr: BelleExpr) => expr
              case _ => println("pos " + pos.getClass.getName + ", expr " + expr.getClass.getName); throw new ProverException("Match error")
            }

            val ruleName =
              if (consultAxiomInfo) RequestHelper.getSpecificName(belleTerm, sequent, pos, pos2, _.display.name)
              else "custom"

            if (stepwise) {
              val localProvable = ProvableSig.startProof(sequent)
              val localProofId = db.createProof(localProvable)

              val interpreter = new Interpreter {
                val inner = SpoonFeedingInterpreter(localProofId, db.createProof, RequestHelper.listenerFactory(db),
                  SequentialInterpreter, 1, strict = false)

                override def apply(expr: BelleExpr, v: BelleValue): BelleValue = try {
                  inner(expr, v)
                } catch {
                  //@note stop and display whatever progress was made
                  case ex: Throwable =>
                    val innerId = inner.innerProofId.getOrElse(localProofId)
                    val innerTrace = db.getExecutionTrace(innerId)
                    if (innerTrace.steps.nonEmpty) BelleSubProof(innerId)
                    else throw BelleTacticFailure("No progress", ex)
                }

                override def kill(): Unit = inner.kill()
              }
              val executor = BellerophonTacticExecutor.defaultExecutor
              val taskId = executor.schedule(userId, appliedExpr, BelleProvable(localProvable), interpreter)
              RunBelleTermResponse(localProofId.toString, "()", taskId) :: Nil
            } else {
              val taskId = node.runTactic(userId, SequentialInterpreter, appliedExpr, ruleName)
              RunBelleTermResponse(proofId, node.id.toString, taskId) :: Nil
            }
          } catch {
            case e: ProverException if e.getMessage == "No step possible" => new ErrorResponse("No step possible") :: Nil
            case e: TacticPositionError => new TacticErrorResponse(e.msg, HackyInlineErrorMsgPrinter(belleTerm, e.pos, e.inlineMsg), e) :: Nil
            case e: BelleThrowable => new TacticErrorResponse(e.getMessage, HackyInlineErrorMsgPrinter(belleTerm, UnknownLocation, e.getMessage), e) :: Nil
          }
      }
    }
  }
}

class InitializeProofFromTacticRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val proofInfo = db.getProofInfo(proofId)
    proofInfo.tactic match {
      case None => new ErrorResponse("Proof " + proofId + " does not have a tactic") :: Nil
      case Some(t) if proofInfo.modelId.isEmpty => throw new Exception("Proof " + proofId + " does not refer to a model")
      case Some(t) if proofInfo.modelId.isDefined =>
        val executor = BellerophonTacticExecutor.defaultExecutor
        val interpreter = DatabasePopulator.prepareInterpreter(db, proofId.toInt)
        val model = KeYmaeraXProblemParser(db.getModel(proofInfo.modelId.get).keyFile)
        val provable = BelleProvable(ProvableSig.startProof(model))
        val tactic = BelleParser(t)
        val taskId = executor.schedule(userId, tactic, provable, interpreter)
        new RunBelleTermResponse(proofId, "()", taskId) :: Nil
    }
  }
}

class TaskStatusRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    val (isDone, lastStep) = executor.synchronized {
      //@todo need intermediate step recording and query to get meaningful progress reports
      //val latestExecutionStep = db.getExecutionSteps(proofId.toInt).sortBy(s => s.stepId).lastOption
      //@note below is the conceptually correct implementation of latestExecutionStep, but getExecutionTrace doesn't work
      //when there's not yet an associated profableId for the step (which is the case here since we are mid-step and the
      //provable isn't computed yet).
//      db.getExecutionTrace(proofId.toInt).lastStepId match {
//        case Some(id) => db.getExecutionSteps(proofId.toInt, None).find(p => p.stepId == id)
//        case None => None
//      }

      (!executor.contains(taskId) || executor.isDone(taskId), None)
    }
    new TaskStatusResponse(proofId, nodeId, taskId, if (isDone) "done" else "running", lastStep) :: Nil
  }
}

class TaskResultRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
  extends UserProofRequest(db, userId, proofId) {
  /* It's very important not to report a branch as closed when it isn't. Other wise the user will carry on in blissful
  * ignorance thinking the hardest part of their proof is over when it's not. This is actually a bit difficult to get
  * right, so check the actual provables to make sure we're closing a branch. */
  private def noBogusClosing(tree: ProofTree, pn: ProofTreeNode): Boolean =
    pn.children.size == pn.localProvable.subgoals.size &&
      pn.children.zip(pn.localProvable.subgoals).forall({case (c, sg) => c.localProvable.conclusion == sg})

  override protected def doResultingResponses(): List[Response] = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    executor.synchronized {
      val response = executor.wait(taskId) match {
        case Some(Left(BelleProvable(_, _))) =>
          val tree = DbProofTree(db, proofId)
          tree.locate(nodeId) match {
            case None => new ErrorResponse("Unknown node " + nodeId)
            case Some(node) =>
              //@todo construct provable (expensive!)
              //assert(noBogusClosing(tree, node), "Server thinks a goal has been closed when it clearly has not")
              new TaskResultResponse(proofId, node, progress=true)
          }
//          val positionLocator = if (parentNode.children.isEmpty) None else RequestHelper.stepPosition(db, parentNode.children.head)
//          assert(noBogusClosing(finalTree, parentNode), "Server thinks a goal has been closed when it clearly has not")
//          new TaskResultResponse(proofId, parentNode, positionLocator, progress = true)
        case Some(Left(BelleSubProof(subId))) =>
          //@todo untested with new tree data structure
          //@HACK for stepping into Let steps
          val tree = DbProofTree(db, subId.toString)
          val node = tree.root//findNode(nodeId).get
          //val positionLocator = if (parentNode.subgoals.isEmpty) None else RequestHelper.stepPosition(db, parentNode.children.head)
          assert(noBogusClosing(tree, node), "Server thinks a goal has been closed when it clearly has not")
          new TaskResultResponse(subId.toString, node, progress = true)
        case Some(Right(error: BelleThrowable)) => new ErrorResponse("Tactic failed with error: " + error.getMessage, error.getCause)
        case None => new ErrorResponse("Could not get tactic result - execution cancelled? ")
      }
      //@note may have been cancelled in the meantime
      executor.tryRemove(taskId)
      response :: Nil
    }
  }
}

class StopTaskRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
  extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    //@note may have completed in the meantime
    executor.tasksForUser(userId).foreach(executor.tryRemove(_, force = true))
    new GenericOKResponse() :: Nil
  }
}

/** Prunes a node and everything below */
class PruneBelowRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    if (proofId == "undefined" || proofId == "null") throw new Exception("The user interface lost track of the proof, please try reloading the page.") //@note Web UI bug
    else if (db.getProofInfo(proofId).closed) new ErrorResponse("Pruning not allowed on closed proofs") :: Nil
    else {
      val tree = DbProofTree(db, proofId)
      tree.locate(nodeId) match {
        case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
        case Some(node) =>
          node.pruneBelow()
          val item = AgendaItem(node.id.toString, "Unnamed Goal", proofId)
          new PruneBelowResponse(item) :: Nil
      }
    }
  }
}

class GetProofProgressStatusRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    // @todo return Loading/NotLoaded when appropriate
    val proof = db.getProofInfo(proofId)
    new ProofProgressResponse(proofId, isClosed = proof.closed) :: Nil
  }
}

class CheckIsProvedRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val model = db.getModel(tree.info.modelId.get)
    val conclusionFormula = KeYmaeraXProblemParser.parseAsProblemOrFormula(model.keyFile)
    val conclusion = Sequent(IndexedSeq(), IndexedSeq(conclusionFormula))
    val provable = tree.root.provable
    if (!provable.isProved) new ErrorResponse("Proof verification failed: proof " + proofId + " is not closed.\n Expected a provable without subgoals, but result provable is\n" + provable.prettyString)::Nil
    else if (provable.conclusion != conclusion) new ErrorResponse("Proof verification failed: proof " + proofId + " does not conclude the associated model.\n Expected " + conclusion.prettyString + "\nBut got\n" + provable.conclusion.prettyString)::Nil
    else {
      assert(provable.isProved, "Provable " + provable + " must be proved")
      assert(provable.conclusion == conclusion, "Conclusion of provable " + provable + " must match problem " + conclusion)
      tree.info.tactic match {
        case None =>
          // remember tactic string
          val newInfo = new ProofPOJO(tree.info.proofId, tree.info.modelId, tree.info.name, tree.info.description,
            tree.info.date, tree.info.stepCount, tree.info.closed, tree.info.provableId, tree.info.temporary,
            Some(tree.tacticString))
          db.updateProofInfo(newInfo)
        case Some(_) => // already have a tactic, so do nothing
      }
      new ProofVerificationResponse(proofId, provable, tree.tacticString) :: Nil
    }
  }
}

class IsLicenseAcceptedRequest(db : DBAbstraction) extends Request {
  def resultingResponses(): List[Response] = {
    new BooleanResponse(
      db.getConfiguration("license").config.contains("accepted") &&
      db.getConfiguration("license").config("accepted") == "true"
    ) :: Nil
  }
}

class AcceptLicenseRequest(db : DBAbstraction) extends Request {
  def resultingResponses(): List[Response] = {
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
    if (HyDRAServerConfig.isHosted) new ErrorResponse("Cannot extract the database on a hosted instance of KeYmaera X") :: Nil
    else {
      val productionDatabase = edu.cmu.cs.ls.keymaerax.hydra.SQLite.ProdDB
      productionDatabase.syncDatabase()

      val today = Calendar.getInstance().getTime
      val fmt = new SimpleDateFormat("MDY")

      val extractionPath = System.getProperty("user.home") + File.separator + s"extracted_${fmt.format(today)}.sqlite"
      val dbPath = productionDatabase.dblocation

      val src = new File(dbPath)
      val dest = new File(extractionPath)
      new FileOutputStream(dest).getChannel.transferFrom(
        new FileInputStream(src).getChannel, 0, Long.MaxValue)


      //@todo Maybe instead do this in the production database and then have a catch all that undoes it.
      //That way we don't have to sync twice. Actually, I'm also not sure if this sync is necessary or not...
      val extractedDatabase = new SQLiteDB(extractionPath)
      extractedDatabase.updateConfiguration(new ConfigurationPOJO("extractedflag", Map("extracted" -> "true")))
      extractedDatabase.syncDatabase()

      new ExtractDatabaseResponse(extractionPath) :: Nil
    }
  }
}

class ShutdownReqeuest() extends LocalhostOnlyRequest {
  override def resultingResponses() : List[Response] = {
    new Thread() {
      override def run(): Unit = {
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
    }.start()

    new BooleanResponse(true) :: Nil
  }
}

class ExtractTacticRequest(db: DBAbstraction, proofIdStr: String) extends Request {
  override def resultingResponses(): List[Response] = {
    new ExtractTacticResponse(DbProofTree(db, proofIdStr).tacticString) :: Nil
  }
}

class TacticDiffRequest(db: DBAbstraction, oldTactic: String, newTactic: String) extends Request {
  override def resultingResponses(): List[Response] = {
    val oldT = BelleParser(oldTactic)
    try {
      val newT = BelleParser(newTactic)
      val diff = TacticDiff.diff(oldT, newT)
      new TacticDiffResponse(diff) :: Nil
    } catch {
      case e: ParseException => new ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
    }
  }
}

class ExtractLemmaRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val model = db.getModel(tree.info.modelId.get)
    val tactic = tree.tacticString
    val provable = tree.root.provable
    val evidence = Lemma.requiredEvidence(provable, ToolEvidence(List(
      "tool" -> "KeYmaera X",
      "model" -> model.keyFile,
      "tactic" -> tactic
    )) :: Nil)
    new ExtractProblemSolutionResponse(new Lemma(provable, evidence, Some(tree.info.name)).toString) :: Nil
  }
}

object ArchiveEntryPrinter {
  def tacticEntry(name: String, tactic: String): String =
    s"""Tactic "$name".
       #  $tactic
       #End.
       """.stripMargin('#')

  def archiveEntry(model: ModelPOJO, tactics:List[(String, String)]): String =
    s"""ArchiveEntry "${model.name}".
       #
         #${model.keyFile}
       #
         #${tactics.map(t => tacticEntry(t._1, t._2)).mkString("\n")}
       #
         #End.
       """.stripMargin('#')
}

class ExtractProblemSolutionRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    val proofName = tree.info.name
    val tactic = tree.tacticString
    val model = db.getModel(tree.info.modelId.get)
    val archiveContent = ArchiveEntryPrinter.archiveEntry(model, (proofName, tactic)::Nil)
    new ExtractProblemSolutionResponse(archiveContent) :: Nil
  }
}

class ExtractModelSolutionsRequest(db: DBAbstraction, userId: String, modelIds: List[Int],
                                   withProofs: Boolean, exportEmptyProof: Boolean) extends UserRequest(userId) {
  override def resultingResponses(): List[Response] = {
    def modelProofs(modelId: Int): List[(String, String)] = {
      if (withProofs) db.getProofsForModel(modelId).map(p =>
        p.name -> DbProofTree(db, p.proofId.toString).tacticString)
      else Nil
    }
    val models = modelIds.map(mid => db.getModel(mid) -> modelProofs(mid)).filter(exportEmptyProof || _._2.nonEmpty)
    val archiveContent = models.map({case (model, proofs) => ArchiveEntryPrinter.archiveEntry(model, proofs)}).mkString("\n\n")
    new ExtractProblemSolutionResponse(archiveContent) :: Nil
  }
}

class MockRequest(resourceName: String) extends Request {
  override def resultingResponses(): List[Response] = new MockResponse(resourceName) :: Nil
}

//region Proof validation requests

/** Global server state for proof validation requests.
  * For now, scheduling immediately dispatches a new thread where the validation occurs. In the future, we may want
  * to rate-limit validation requests. The easiest way to do that is to create a thread pool with a max size. */
object ProofValidationRunner {
  private val results : mutable.Map[String, (Formula, BelleExpr, Option[Boolean])] = mutable.Map()

  case class ValidationRequestDNE(taskId: String) extends Exception(s"The requested taskId $taskId does not exist.")

  /** Returns Option[Proved] which is None iff the task is still running, and True if formula didn't prove. */
  def status(taskId: String) : Option[Boolean] = results.get(taskId) match {
    case Some((_, _, proved)) => proved
    case None => throw ValidationRequestDNE(taskId)
  }

  /** Schedules a proof validation request and returns the UUID. */
  def scheduleValidationRequest(db : DBAbstraction, model : Formula, proof : BelleExpr) : String = {
    val taskId = java.util.UUID.randomUUID().toString
    results update (taskId, (model, proof, None))

    new Thread(new Runnable() {
      override def run(): Unit = {
        println(s"Received request to validate $taskId. Running in separate thread.")
        val provable = NoProofTermProvable( Provable.startProof(model) )

        try {
          SequentialInterpreter()(proof, BelleProvable(provable)) match {
            case BelleProvable(p, _) if p.isProved => results update (taskId, (model, proof, Some(true )))
            case _                                 => results update (taskId, (model, proof, Some(false)))
          }
        } catch {
          //Catch everything and indicate a failed proof attempt.
          case e : Throwable => results update (taskId, (model, proof, Some(false)))
        }

        println(s"Done executing validation check for $taskId")
      }
    }).start()

    taskId
  }
}

/** Returns a UUID whose status can be queried at a later time ({complete: true/false[, proves: true/false]}.
  * @see CheckValidationRequest - calling this with the returned UUID should give the status of proof checking. */
class ValidateProofRequest(db : DBAbstraction, model: Formula, proof: BelleExpr) extends Request {
  override def resultingResponses() : List[Response] =
    //Spawn an async validation request and return the reesulting UUID.
    new ValidateProofResponse(ProofValidationRunner.scheduleValidationRequest(db, model, proof), None) :: Nil
}

/** An idempotent request for the status of a validation request; i.e., validation requests aren't removed until the server is resst. */
class CheckValidationRequest(db: DBAbstraction, taskId: String) extends Request {
  override def resultingResponses(): List[Response] = try {
    new ValidateProofResponse(taskId, ProofValidationRunner.status(taskId)) :: Nil
  } catch {
    case e : ProofValidationRunner.ValidationRequestDNE => new ErrorResponse(e.getMessage, e) :: Nil
  }
}

//endregion

object RequestHelper {
  /* Try to figure out the most intuitive inference rule to display for this tactic. If the user asks us "StepAt" then
   * we should use the StepAt logic to figure out which rule is actually being applied. Otherwise just ask TacticInfo */
  def getSpecificName(tacticId: String, sequent:Sequent, l1: Option[PositionLocator], l2: Option[PositionLocator], what: DerivationInfo => String): String = {
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

  /** A listener that stores proof steps in the database `db` for proof `proofId`. */
  def listenerFactory(db: DBAbstraction)(proofId: Int)(tacticName: String, parentInTrace: Int, branch: Int): Seq[IOListener] = {
    val trace = db.getExecutionSteps(proofId)
    assert(-1 <= parentInTrace && parentInTrace < trace.length, "Invalid trace index " + parentInTrace + ", expected -1<=i<trace.length")
    val parentStep: Option[Int] = if (parentInTrace < 0) None else trace(parentInTrace).stepId
    val globalProvable = parentStep match {
      case None => db.getProvable(db.getProofInfo(proofId).provableId.get).provable
      case Some(sId) => db.getExecutionStep(proofId, sId).map(_.local).get
    }
    val ruleName = try {
      RequestHelper.getSpecificName(tacticName.split("\\(").head, null, None, None, _.display.name)
    } catch {
      case _: Throwable => tacticName
    }
    new TraceRecordingListener(db, proofId, parentStep,
      globalProvable, branch, recursive = false, ruleName) :: Nil
  }

}
