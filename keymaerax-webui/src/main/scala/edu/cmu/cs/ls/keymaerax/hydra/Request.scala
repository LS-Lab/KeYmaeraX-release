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
import java.io._
import java.text.SimpleDateFormat
import java.util.{Calendar, Locale}

import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.pt.{NoProofTermProvable, ProvableSig}

import scala.io.Source
import scala.collection.immutable._
import scala.collection.mutable
import edu.cmu.cs.ls.keymaerax.btactics.cexsearch
import edu.cmu.cs.ls.keymaerax.btactics.cexsearch.{BoundedDFS, BreadthFirstSearch, ProgramSearchNode, SearchNode}
import edu.cmu.cs.ls.keymaerax.codegen.{CControllerGenerator, CGenerator, CMonitorGenerator}
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator.TutorialEntry
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory

import scala.util.Try

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
  /** Checks read/write/registered access. Additional checks by overriding doPermission. */
  final def permission(t: SessionToken): Boolean = (t match {
    case t: ReadonlyToken => this.isInstanceOf[ReadRequest]
    case _ => true
  }) && doPermission(t)

  /** Override to provide additional permission checks. */
  protected def doPermission(t: SessionToken): Boolean = true

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

trait ReadRequest
trait RegisteredOnlyRequest
trait WriteRequest extends RegisteredOnlyRequest

/**
  * @todo we don't always check that the username is in fact associated with the other data that's touched by a request.
  *       For example, openProof might not insist that the proofId actually belongs to the associated userId in the request.
  *       The best solution to this in the long term is a re-design of the API, probably.
  * @param username The username of the current user.
  */
abstract class UserRequest(username: String) extends Request {
  override protected def doPermission(t: SessionToken): Boolean = t belongsTo username
}

/** A proof session storing information between requests. */
case class ProofSession(proofId: String, invGenerator: Generator[Formula], defs: KeYmaeraXDeclarationsParser.Declaration)

abstract class UserModelRequest(db: DBAbstraction, username: String, modelId: String) extends UserRequest(username) {
  override final def resultingResponses(): List[Response] = {
    //@todo faster query for existence
    if (db.getModel(modelId).userId != username) new PossibleAttackResponse("Permission denied") :: Nil
    else doResultingResponses()
  }

  protected def doResultingResponses(): List[Response]
}

abstract class UserProofRequest(db: DBAbstraction, username: String, proofId: String) extends UserRequest(username) {
  override final def resultingResponses(): List[Response] = {
    if (proofId == "undefined" || proofId == "null") throw new Exception("The user interface lost track of the proof, please try reloading the page.") //@note Web UI bug
    //@todo faster query for existence
    else if (!db.userOwnsProof(username, proofId)) {
      new PossibleAttackResponse("Permission denied") :: Nil
    }
    else doResultingResponses()
  }

  protected def doResultingResponses(): List[Response]
}

abstract class LocalhostOnlyRequest() extends Request {
  override protected def doPermission(t: SessionToken): Boolean = !HyDRAServerConfig.isHosted //@todo change this to a literal false prior to deployment.
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Users
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateUserRequest(db: DBAbstraction, username: String, password: String, mode: String) extends Request with WriteRequest {
  override def resultingResponses(): List[Response] = {
    db.getUser(username) match {
      case Some(user) => new LoginResponse(false, user, None) ::  Nil
      case None =>
        db.createUser(username, password, mode)
        db.getUser(username) match {
          case Some(newUser) => new LoginResponse(true, newUser, Some(SessionManager.add(newUser))) ::  Nil
          case None => new ErrorResponse("Failed to create user " + username) :: Nil
        }
    }
  }
}

class LoginRequest(db : DBAbstraction, username : String, password : String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val check = db.checkPassword(username, password)
    db.getUser(username) match {
      case Some(user) =>
        val sessionToken =
          if(check) Some(SessionManager.add(user))
          else None
        new LoginResponse(check, user, sessionToken) ::  Nil
      case None => new ErrorResponse("Unable to login user " + username
        + ". Please double-check user name and password, or register a new user.") :: Nil
    }
  }
}

class ProofsForUserRequest(db : DBAbstraction, userId: String) extends UserRequest(userId) with ReadRequest {
  def resultingResponses(): List[Response] = {
    val proofs = db.getProofsForUser(userId).filterNot(_._1.temporary).map(proof =>
      (proof._1, "loaded"/*KeYmaeraInterface.getTaskLoadStatus(proof._1.proofId.toString).toString.toLowerCase*/))
    new ProofListResponse(proofs) :: Nil
  }
}

class UpdateProofNameRequest(db : DBAbstraction, userId: String, proofId : String, newName : String) extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    db.updateProofName(proofId, newName)
    new UpdateProofNameResponse(proofId, newName) :: Nil
  }
}

class FailedRequest(userId: String, msg: String, cause: Throwable = null) extends UserRequest(userId) {
  def resultingResponses(): List[Response] = { new ErrorResponse(msg, cause) :: Nil }
}

class CounterExampleRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
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

class SetupSimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserProofRequest(db, userId, proofId) with RegisteredOnlyRequest {
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

class SimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, initial: Formula, stateRelation: Formula, steps: Int, n: Int, stepDuration: Term) extends UserProofRequest(db, userId, proofId) with RegisteredOnlyRequest {
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

class KyxConfigRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
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

class KeymaeraXVersionRequest() extends Request with ReadRequest {
  override def resultingResponses() : List[Response] = {
    val keymaeraXVersion = VERSION
    val (upToDate, latestVersion) = UpdateChecker.getVersionStatus() match {
      case Some((upd, lv)) => (Some(upd), Some(lv))
      case _ => (None, None)
    }
    new KeymaeraXVersionResponse(keymaeraXVersion, upToDate, latestVersion) :: Nil
  }
}

class ConfigureMathematicaRequest(db : DBAbstraction, linkName : String, jlinkLibFileName : String) extends LocalhostOnlyRequest with WriteRequest {
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

class GetMathematicaConfigSuggestionRequest(db : DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
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

class SystemInfoRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
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

class LicensesRequest() extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val reader = this.getClass.getResourceAsStream("/license/tools_licenses")
    val lines = Source.fromInputStream(reader).mkString.lines.toList
    val header = lines.head
    val licenseStartPos = header.indexOf("License")
    val licenses = lines.tail.tail.map(l => l.splitAt(licenseStartPos)).map({case (tool, license) =>
        JsObject(
          "tool" -> JsString(tool.trim),
          "license" -> JsString(license.trim)
        )
    })
    new PlainResponse("licenses" -> JsArray(licenses:_*)) :: Nil
  }
}

class GetToolRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    //@todo more/different tools
    new KvpResponse("tool", db.getConfiguration("tool").config("qe")) :: Nil
  }
}

class SetToolRequest(db: DBAbstraction, tool: String) extends LocalhostOnlyRequest with WriteRequest {
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

class GetMathematicaConfigurationRequest(db : DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
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

class GetUserThemeRequest(db: DBAbstraction, userName: String) extends UserRequest(userName) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration(userName).config
    new PlainResponse(
      "themeCss" -> config.getOrElse("themeCss", "\"app\"").parseJson,
      "themeFontSize" -> config.getOrElse("themeFontSize", "14").parseJson) :: Nil
  }
}

/** Sets the UI theme. @note ReadRequest allows changing theme in guest mode for presentation purposes. */
class SetUserThemeRequest(db: DBAbstraction, userName: String, themeCss: String, themeFontSize: String)
    extends UserRequest(userName) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration(userName)
    db.updateConfiguration(new ConfigurationPOJO(userName, config.config.updated("themeCss", themeCss).updated("themeFontSize", themeFontSize)))
    new PlainResponse(
      "themeCss" -> themeCss.parseJson,
      "themeFontSize" -> themeFontSize.parseJson) :: Nil
  }
}


class MathematicaStatusRequest(db : DBAbstraction) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration("mathematica").config
    new ToolStatusResponse("Mathematica", config.contains("linkName") && config.contains("jlinkLibDir")) :: Nil
  }
}

class Z3StatusRequest(db : DBAbstraction) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = new ToolStatusResponse("Z3", true) :: Nil
}

class ListExamplesRequest(db: DBAbstraction, userId: String) extends UserRequest(userId) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    //@todo read from the database/some web page?
    val examples =
      new ExamplePOJO(0, "STTT Tutorial",
        "Automated stop sign braking for cars",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/sttt/sttt.kyx",
        "/examples/tutorials/sttt/sttt.png", 1) ::
      new ExamplePOJO(1, "CPSWeek 2016 Tutorial",
        "Proving ODEs",
        "http://www.ls.cs.cmu.edu/KeYmaeraX/KeYmaeraX-tutorial.pdf",
        "classpath:/examples/tutorials/cpsweek/cpsweek.kyx",
        "/examples/tutorials/cpsweek/cpsweek.png", 1) ::
      new ExamplePOJO(2, "FM 2016 Tutorial",
        "Tactics and Proofs",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/fm/fm.kyx",
        "/examples/tutorials/fm/fm.png", 1) ::
      new ExamplePOJO(3, "Beginner's Tutorial",
        "Feature Tour Tutorial",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/basic/basictutorial.kyx",
        "/examples/tutorials/fm/fm.png", 0) ::
        new ExamplePOJO(3, "DLDS",
          "Dynamic Logic for Dynamical Systems Examples",
          //"/keymaerax-projects/dlds/README.md",
          "",
          "classpath:/keymaerax-projects/dlds/dlds.kya",
          "/examples/tutorials/cpsweek/cpsweek.png", 0) ::
      Nil

    db.getUser(userId) match {
      case Some(user) => new ListExamplesResponse(examples.filter(_.level <= user.level)) :: Nil
      case None => new ErrorResponse("Unable to retrieve examples. Unknown user " + userId) :: Nil
    }

  }
}


////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Models
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/** Creates a model from a formula without variable declarations.
  * Separate from CreateModelRequest so that we don't end up swallowing parse errors or returning the wrong parse error. */
class CreateModelFromFormulaRequest(db: DBAbstraction, userId: String, nameOfModel: String, formula: String) extends UserRequest(userId) with WriteRequest {
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

class CreateModelRequest(db: DBAbstraction, userId: String, nameOfModel: String, modelText: String) extends UserRequest(userId) with WriteRequest {
  def resultingResponses(): List[Response] = {
    if (KeYmaeraXProblemParser.isExercise(modelText)) {
      if (db.getModelList(userId).map(_.name).contains(nameOfModel)) {
        new ModelUploadResponse(None, Some("A model with name " + nameOfModel + " already exists, please choose a different name")) :: Nil
      } else {
        val createdId = db.createModel(userId, nameOfModel, modelText, currentDate()).map(_.toString)
        new ModelUploadResponse(createdId, None) :: Nil
      }
    } else try {
      KeYmaeraXProblemParser.parseAsProblemOrFormula(modelText) match {
        case fml: Formula =>
          if (db.getModelList(userId).map(_.name).contains(nameOfModel)) {
            new ModelUploadResponse(None, Some("A model with name " + nameOfModel + " already exists, please choose a different name")) :: Nil
          } else {
            val createdId = db.createModel(userId, nameOfModel, RequestHelper.augmentDeclarations(modelText, fml), currentDate()).map(_.toString)
            new ModelUploadResponse(createdId, None) :: Nil
          }
        case t => new ErrorResponse("Expected a model formula, but got a file with a " + t.kind) :: Nil
      }
    } catch {
      case e: ParseException => ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
    }
  }
}

class UpdateModelRequest(db: DBAbstraction, userId: String, modelId: String, name: String, title: String,
                         description: String, content: String) extends UserRequest(userId) with WriteRequest {
  private def emptyToOption(s: String): Option[String] = if (s.isEmpty) None else Some(s)

  def resultingResponses(): List[Response] = {
    val modelInfo = db.getModel(modelId)
    if (modelInfo.numProofs <= 0) {
      if (KeYmaeraXProblemParser.isExercise(content)) {
        db.updateModel(modelId.toInt, name, emptyToOption(title), emptyToOption(description), emptyToOption(content))
        BooleanResponse(flag = true) :: Nil
      } else try {
        KeYmaeraXProblemParser.parseAsProblemOrFormula(content) match {
          case fml: Formula =>
            val newContent = RequestHelper.augmentDeclarations(content, fml)
            db.updateModel(modelId.toInt, name, emptyToOption(title), emptyToOption(description), emptyToOption(newContent))
            BooleanResponse(flag = true) :: Nil
          case t => new ErrorResponse("Expected a model formula, but got a file with a " + t.kind) :: Nil
        }
      } catch {
        case e: ParseException => ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
      }
    } else new ErrorResponse("Unable to update model " + modelId + " because it has " + modelInfo.numProofs + " proofs") :: Nil
  }
}

class UploadArchiveRequest(db: DBAbstraction, userId: String, kyaFileContents: String) extends UserRequest(userId) with WriteRequest {
  def resultingResponses(): List[Response] = {
    try {
      val archiveEntries = KeYmaeraXArchiveParser.read(kyaFileContents)
      val (failedModels, succeededModels) = archiveEntries.foldLeft((List[String](), List[String]()))({ case ((failedImports, succeededImports), (name, modelFileContent, _, tactic, info)) =>
        // parse entry's model and tactics
        val (d, _) = KeYmaeraXProblemParser.parseProblem(modelFileContent)
        tactic.foreach({ case (_, ttext) => BelleParser.parseWithInvGen(ttext, None, d) })

        val uniqueModelName = db.getUniqueModelName(userId, name)
        db.createModel(userId, uniqueModelName, modelFileContent, currentDate(), info.get("Description"),
          info.get("Title"), info.get("Link"), tactic.headOption.map(_._2)) match {
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
      if (failedModels.isEmpty) BooleanResponse(flag=true) :: Nil
      else throw new Exception("Failed to import the following models\n" + failedModels.mkString("\n") +
        "\nSucceeded importing:\n" + succeededModels.mkString("\n") +
        "\nModel import may have failed because of model name clashed. Try renaming the failed models in the archive to names that do not yet exist in your model list.")
    } catch {
      //@todo adapt parse error positions (are relative to problem inside entry)
      case e: ParseException => ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
    }
  }
}

class ImportExampleRepoRequest(db: DBAbstraction, userId: String, repoUrl: String) extends UserRequest(userId) with WriteRequest {
  override def resultingResponses(): List[Response] = {
    if (repoUrl.endsWith(".json")) {
      DatabasePopulator.importJson(db, userId, repoUrl, prove=false)
      BooleanResponse(flag=true) :: Nil
    } else if (repoUrl.endsWith(".kya") || repoUrl.endsWith(".kyx")) {
      DatabasePopulator.importKya(db, userId, repoUrl, prove=false, Nil)
      BooleanResponse(flag=true) :: Nil
    } else {
      new ErrorResponse("Unknown repository type " + repoUrl + ". Expected .json or .kya") :: Nil
    }
  }
}

class DeleteModelRequest(db: DBAbstraction, userId: String, modelId: String) extends UserModelRequest(db, userId, modelId) with WriteRequest {
  override def doResultingResponses(): List[Response] = {
    val id = Integer.parseInt(modelId)
    //db.getProofsForModel(id).foreach(proof => TaskManagement.forceDeleteTask(proof.proofId.toString))
    val success = db.deleteModel(id)
    BooleanResponse(success) :: Nil
  }
}

class DeleteModelProofsRequest(db: DBAbstraction, userId: String, modelId: String) extends UserModelRequest(db, userId, modelId) with WriteRequest {
  override def doResultingResponses(): List[Response] = {
    val success = db.getProofsForModel(modelId).map(p => db.deleteProof(p.proofId)).reduce(_&&_)
    BooleanResponse(success) :: Nil
  }
}

class DeleteProofRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    //TaskManagement.forceDeleteTask(proofId)
    val success = db.deleteProof(Integer.parseInt(proofId))
    new BooleanResponse(success) :: Nil
  }
}

class GetModelListRequest(db : DBAbstraction, userId : String) extends UserRequest(userId) with ReadRequest {
  def resultingResponses(): List[Response] = {
    new ModelListResponse(db.getModelList(userId).filterNot(_.temporary)) :: Nil
  }
}

class GetModelRequest(db : DBAbstraction, userId : String, modelId : String) extends UserRequest(userId) with ReadRequest {
  private val model: ModelPOJO = db.getModel(modelId)
  insist(model.userId == userId, s"model $modelId does not belong to $userId")
  def resultingResponses(): List[Response] = {
    new GetModelResponse(model) :: Nil
  }
}

class GetModelTacticRequest(db : DBAbstraction, userId : String, modelId : String) extends UserRequest(userId) with ReadRequest {
  def resultingResponses(): List[Response] = {
    val model = db.getModel(modelId)
    new GetModelTacticResponse(model) :: Nil
  }
}

class AddModelTacticRequest(db : DBAbstraction, userId : String, modelId : String, tactic: String) extends UserRequest(userId) with WriteRequest {
  def resultingResponses(): List[Response] = {
    val tacticId = db.addModelTactic(modelId, tactic)
    new BooleanResponse(tacticId.isDefined) :: Nil
  }
}

class ModelPlexMandatoryVarsRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) with RegisteredOnlyRequest {
  def resultingResponses(): List[Response] = {
    val model = db.getModel(modelId)
    val modelFml = KeYmaeraXProblemParser.parseAsProblemOrFormula(model.keyFile)
    new ModelPlexMandatoryVarsResponse(model, StaticSemantics.boundVars(modelFml).symbols.filter(_.isInstanceOf[BaseVariable])) :: Nil
  }
}

class ModelPlexRequest(db: DBAbstraction, userId: String, modelId: String, artifact: String, monitorKind: String,
                       monitorShape: String, conditionKind: String,
                       additionalVars: List[String]) extends UserRequest(userId) with RegisteredOnlyRequest {
  def resultingResponses(): List[Response]  = {
    val model = db.getModel(modelId)
    val modelFml = KeYmaeraXProblemParser.parseAsProblemOrFormula(model.keyFile)
    val vars: Set[BaseVariable] = (StaticSemantics.boundVars(modelFml).symbols ++ additionalVars.map(_.asVariable)).
      filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])

    artifact match {
      case "controller" => createController(model, modelFml, vars)
      case "monitor" => createMonitor(model, modelFml, vars)
      case "sandbox" => createSandbox(model, modelFml, vars)
    }
  }

  private def createController(model: ModelPOJO, modelFml: Formula, vars: Set[BaseVariable]): List[Response] = modelFml match {
    case Imply(_, Box(prg, _)) => conditionKind match {
      case "kym" =>
        val ctrlPrg = ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = prg match {
            case _: ODESystem => Right(Test("true".asFormula))
            case _ => Left(None)
          }
        }, prg).get
        new ModelPlexArtifactResponse(model, ctrlPrg) :: Nil
      case "c" =>
        val controller = (new CGenerator(new CControllerGenerator()))(prg, vars, CGenerator.getInputs(prg))

        val code = s"""
           |${CGenerator.printHeader(model.name)}
           |$controller
           |
           |int main() {
           |  /* control loop stub */
           |  parameters params = { .A=1.0 };
           |  while (true) {
           |    state current; /* read sensor values, e.g., = { .x=0.0 }; */
           |    state input;   /* resolve non-deterministic assignments, e.g., = { .x=0.5 }; */
           |    state post = ctrlStep(current, params, input);
           |    /* hand post actuator set values to actuators */
           |  }
           |  return 0;
           |}
           |""".stripMargin

        new ModelPlexArtifactCodeResponse(model, code) :: Nil
    }
    case _ => new ErrorResponse("Unsupported shape, expected assumptions -> [{ctrl;ode}*]safe, but got " + modelFml.prettyString) :: Nil
  }

  private def createSandbox(model: ModelPOJO, modelFml: Formula, stateVars: Set[BaseVariable]): List[Response] = modelFml match {
    case Imply(_, Box(prg, _)) =>
      conditionKind match {
        case "kym" =>
          //@todo specific formula
          new ModelPlexArtifactResponse(model, "pre := curr; ctrl; if (monitorSatisfied()) { skip; } else { fallback; } actuate;".asProgram) :: Nil
        case "c" =>
          val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(modelFml, stateVars.toList.sorted[NamedSymbol]:_*)
          val monitorCond = (monitorKind, ToolProvider.simplifierTool()) match {
            case ("controller", tool) =>
              val foResult = TactixLibrary.proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
              try {
                TactixLibrary.proveBy(foResult.subgoals.head,
                  SaturateTactic(ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)))
              } catch {
                case _: Throwable => foResult
              }
            case ("model", tool) => ??? //@todo sandbox for model monitors
//              TactixLibrary.proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) &
//              ModelPlex.optimizationOneWithSearch(tool, assumptions)(1) /*& SimplifierV2.simpTac(1)*/)
          }

          if (monitorCond.subgoals.size == 1 && monitorCond.subgoals.head.ante.isEmpty && monitorCond.subgoals.head.succ.size == 1) {
            val monitorFml =  monitorShape match {
              case "boolean" => monitorCond.subgoals.head.succ.head
              case "metric" => ModelPlex.toMetric(monitorCond.subgoals.head.succ.head)
            }

            val params = CGenerator.getParameters(monitorFml, stateVars)
            val inputs = CGenerator.getInputs(prg)
            val declarations = CGenerator.printParameterDeclaration(params) + "\n" +
              CGenerator.printStateDeclaration(stateVars) + "\n" +
              CGenerator.printInputDeclaration(inputs)
            val fallbackCode = new CControllerGenerator()(prg, stateVars, inputs)
            val monitorCode = new CMonitorGenerator(monitorShape)(monitorFml, stateVars, inputs)

            val sandbox =
              s"""
                |${CGenerator.printHeader(model.name)}
                |${CGenerator.INCLUDE_STATEMENTS}
                |$declarations
                |$fallbackCode
                |$monitorCode
                |
                |state ctrl(state curr, const parameters* const params, const input* const in) {
                |  /* controller implementation stub: modify curr to return actuator set values */
                |  return curr;
                |}
                |
                |int main() {
                |  /* control loop stub */
                |  parameters params; /* set system parameters, e.g., = { .A=1.0 }; */
                |  while (true) {
                |    state current; /* read sensor values, e.g., = { .x=0.2 }; */
                |    input in;   /* resolve non-deterministic assignments in the model */
                |    state post = monitoredCtrl(current, &params, &in, &ctrl, &ctrlStep);
                |    /* hand post actuator set values to actuators */
                |  }
                |  return 0;
                |}
                |""".stripMargin

            new ModelPlexArtifactCodeResponse(model, sandbox) :: Nil
          } else new ErrorResponse("ModelPlex failed: expected exactly 1 subgoal, but got " + monitorCond.prettyString) :: Nil
      }
    case _ => new ErrorResponse("Unsupported shape, expected assumptions -> [{ctrl;ode}*]safe, but got " + modelFml.prettyString) :: Nil
  }

  private def createMonitor(model: ModelPOJO, modelFml: Formula, vars: Set[BaseVariable]): List[Response] = {
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(modelFml, vars.toList.sorted[NamedSymbol]:_*)
    val Imply(_, Box(prg, _)) = modelFml
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

    if (monitorCond.subgoals.size == 1 && monitorCond.subgoals.head.ante.isEmpty && monitorCond.subgoals.head.succ.size == 1) {
      val monitorFml =  monitorShape match {
        case "boolean" => monitorCond.subgoals.head.succ.head
        case "metric" => ModelPlex.toMetric(monitorCond.subgoals.head.succ.head)
      }
      conditionKind match {
        case "kym" => new ModelPlexArtifactResponse(model, monitorFml) :: Nil
        case "c" =>
          val inputs = CGenerator.getInputs(prg)
          val monitor = (new CGenerator(new CMonitorGenerator(monitorShape)))(monitorFml, vars, inputs, model.name)
          val code =
            s"""
              |${CGenerator.printHeader(model.name)}
              |$monitor
              |
              |int main() {
              |  /* sandbox stub, select 'sandbox' to auto-generate */
              |  parameters params = { .A=1.0 };
              |  while (true) {
              |    state pre; /* read sensor values, e.g., = { .x=0.0 }; */
              |    state post; /* run controller */
              |    if (!monitorSatisfied(pre,post,params)) post = post; /* replace with fallback control output */
              |    /* hand post actuator set values to actuators */
              |  }
              |  return 0;
              |}
              |""".stripMargin

          new ModelPlexArtifactCodeResponse(model, code) :: Nil
      }
    } else new ErrorResponse("ModelPlex failed: expected exactly 1 subgoal, but got " + monitorCond.prettyString) :: Nil
  }
}

class TestSynthesisRequest(db: DBAbstraction, userId: String, modelId: String, monitorKind: String, testKinds: Map[String, Boolean],
                           amount: Int, timeout: Option[Int]) extends UserRequest(userId) with RegisteredOnlyRequest {
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
  extends UserRequest(userId) with WriteRequest {
  def resultingResponses(): List[Response] = {
    val proofId = db.createProofForModel(modelId, name, description, currentDate(), None)
    new CreatedIdResponse(proofId) :: Nil
  }
}

class CreateModelTacticProofRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) with WriteRequest {
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

class ProofsForModelRequest(db : DBAbstraction, userId: String, modelId: String) extends UserRequest(userId) with ReadRequest {
  def resultingResponses(): List[Response] = {
    val proofs = db.getProofsForModel(modelId).map(proof =>
      (proof, "loaded"/*KeYmaeraInterface.getTaskLoadStatus(proof.proofId.toString).toString.toLowerCase*/))
    new ProofListResponse(proofs) :: Nil
  }
}

class OpenProofRequest(db: DBAbstraction, userId: String, proofId: String, wait: Boolean = false) extends UserProofRequest(db, userId, proofId) with ReadRequest {
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

class OpenGuestArchiveRequest(db: DBAbstraction, uri: String, archiveName: String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    try {
      val userId = uri
      val sanitizedUserId = uri.replaceAllLiterally("/", "%2F").replaceAllLiterally(":", "%3A")
      val pwd = "guest"
      val userExists = db.userExists(userId)
      if (!userExists) db.createUser(userId, pwd, "3")

      val models = db.getModelList(userId)
      DatabasePopulator.importKya(db, userId, uri, prove=false, models)

      //@todo template engine, e.g., twirl, or at least figure out how to parse from a string
      val html =
        <html lang="en" ng-app="loginApp" ng-controller="ServerInfoCtrl">
          <head>
            <meta charset="utf-8"/>
            <meta http-equiv="X-UA-Compatible" content="IE=edge"/>
            <meta name="viewport" content="width=device-width, initial-scale=1"/>
            <meta name="description" content=""/>
            <meta name="author" content="Logical Systems Lab, Carnegie Mellon University"/>
            <link rel="icon" href="../../favicon.ico"/>
            <title>KeYmaera X</title>
            <link href="/css/bootstrap.css" rel="stylesheet" type="text/css"/>
            <link href="/css/font-awesome.min.css" rel="stylesheet" type="text/css"/>
            <link href="/css/sticky-footer-navbar.css" rel="stylesheet"/>
          </head>
          <body>
            <script src="/js/jquery.min.js"></script>
            <script src="/js/jquery-ui.min.js"></script>
            <script src="/js/bootstrap/bootstrap.min.js"></script>
            <script src="/js/angular/angular.min.js"></script>
            <script src="/js/angular/angular-sanitize.min.js"></script>
            <script src="/js/angular/angular-cookies.min.js"></script>
            <script src="/js/angular/angular-route.min.js"></script>
            <script src="/js/angular/angular-animate.min.js"></script>
            <script src="/js/angular/bootstrap/ui-bootstrap-tpls-2.5.0.min.js"></script>
            <script src="/js/loginApp.js"></script>
            <script src="/js/services/services.js"></script>
            <script src="/js/services/session.js"></script>
            <script src="/js/controllers/interceptors.js"></script>
            <script src="/js/controllers/auth.js"></script>
            <script src="/js/controllers.js"></script>
            <script src="/js/controllers/factories.js"></script>
            <script src="/js/controllers/errorReport.js"></script>
            <script src="/js/controllers/login.js"></script>
            <script src="/js/controllers/serverinfo.js"></script>

            <div ng-controller="LoginCtrl" ng-init={"login('" + sanitizedUserId + "','" + pwd + "',true);"}></div>
          </body>
        </html>

      HtmlResponse(html) :: Nil
    } catch {
      // Return a user-friendly message, since there's no user interface running yet to render a JSON error response
      case ex: Throwable =>
        val stacktrace = {
          val sw = new StringWriter
          ex.printStackTrace(new PrintWriter(sw))
          sw.toString
        }
        val html =
          <html lang="en" ng-app="loginApp" ng-controller="ServerInfoCtrl">
            <head>
              <meta charset="utf-8"/>
              <meta http-equiv="X-UA-Compatible" content="IE=edge"/>
              <meta name="viewport" content="width=device-width, initial-scale=1"/>
              <meta name="description" content=""/>
              <meta name="author" content="Logical Systems Lab, Carnegie Mellon University"/>
              <link rel="icon" href="../../favicon.ico"/>
              <title>KeYmaera X</title>
              <link href="/css/bootstrap.css" rel="stylesheet" type="text/css"/>
              <link href="/css/font-awesome.min.css" rel="stylesheet" type="text/css"/>
              <link href="/css/sticky-footer-navbar.css" rel="stylesheet"/>
            </head>
            <body>
              <h1>Error browsing archive</h1>
              <p>Please double-check the archive path/name</p>
              <p>Archive location: {archiveName}</p>
              <p>Archive remote location: {uri}</p>
              <h3>Error details</h3>
              <p>{stacktrace}</p>
            </body>
          </html>

        HtmlResponse(html) :: Nil
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
class GetAgendaAwesomeRequest(db : DBAbstraction, userId : String, proofId : String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree: ProofTree = DbProofTree(db, proofId)
    val leaves = tree.openGoals
    val closed = tree.openGoals.isEmpty && tree.verifyClosed

    //@todo fetch goal names from DB
    def agendaItemName(codeName: String): String = {
      Try(DerivationInfo.ofCodeName(codeName)).toOption match {
        case Some(di) => di.display.name
        case None => codeName
      }
    }

    val agendaItems: List[AgendaItem] = leaves.map(n =>
      AgendaItem(n.id.toString, "Goal: " + agendaItemName(n.makerShortName.getOrElse("").split("\\(").head), proofId))
    AgendaAwesomeResponse(proofId, tree.root, leaves, agendaItems, closed) :: Nil
  }
}

/**
  * Gets the proof root as agenda item (browse a proof from root to leaves).
  * @param db Access to the database.
  * @param userId Identifies the user.
  * @param proofId Identifies the proof.
  */
class GetProofRootAgendaRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree: ProofTree = DbProofTree(db, proofId)
    val agendaItems: List[AgendaItem] = AgendaItem(tree.root.id.toString, "Unnamed Goal", proofId) :: Nil
    AgendaAwesomeResponse(proofId, tree.root, tree.root::Nil, agendaItems, closed=false) :: Nil
  }
}

/**
  * Gets the children of a proof node (browse a proof from root to leaves).
  * @param db Access to the database.
  * @param userId Identifies the user.
  * @param proofId Identifies the proof.
  * @param nodeId Identifies the proof node.
  */
class GetProofNodeChildrenRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {

  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(node) => NodeChildrenResponse(proofId, node) :: Nil
    }
  }
}

case class GetAgendaItemRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
                                    displayName: String) extends UserProofRequest(db, userId, proofId) with WriteRequest {
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
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId).flatMap(_.parent) match {
      case Some(parent) => new ProofTaskParentResponse(parent)::Nil
      case None => new ErrorResponse("Cannot get parent of node " + nodeId + ", node might be unknown or root")::Nil
    }
  }
}

case class GetPathAllRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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

class ProofNodeSequentRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => throw new Exception("Unknown node " + nodeId)
      case Some(node) => ProofNodeSequentResponse(proofId, node) :: Nil
    }
  }
}

class ProofTaskExpandRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
        val innerInterpreter = SpoonFeedingInterpreter(localProofId, -1, db.createProof,
          RequestHelper.listenerFactory(db), SequentialInterpreter, 1, strict=false)
        val parentTactic = BelleParser(parentStep)
        innerInterpreter(parentTactic, BelleProvable(localProvable))
        innerInterpreter.kill()

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

class StepwiseTraceRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
            ApplicableAxiomsResponse(node.applicableTacticsAt(pos), node.tacticInputSuggestions(pos), Some(Fixed(1))) :: Nil
          }
      }
    }
  }
}

class GetApplicableAxiomsRequest(db:DBAbstraction, userId: String, proofId: String, nodeId: String, pos:Position)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
                                        pos1: Position, pos2: Position) extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val info = (DerivationInfo.ofCodeName(axiomId), UIIndex.comfortOf(axiomId).map(DerivationInfo.ofCodeName)) :: Nil
    new ApplicableAxiomsResponse(info, Map.empty) :: Nil
  }
}

class ExportCurrentSubgoal(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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

case class BelleTermInput(value: String, spec:Option[ArgInfo])

class GetStepRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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

class GetLemmasRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position,
                        partialLemmaName: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val infos = ProvableInfo.allInfo.filter(i =>
      (i.isInstanceOf[CoreAxiomInfo] || i.isInstanceOf[DerivedAxiomInfo]) && i.canonicalName.contains(partialLemmaName))
    LemmasResponse(infos)::Nil
  }
}

class GetFormulaPrettyStringRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    DbProofTree(db, proofId).locate(nodeId).flatMap(_.goal.flatMap(_.sub(pos))) match {
      case None => new ErrorResponse("Unknown position " + pos + " at node " + nodeId)::Nil
      case Some(e: Expression) => new PlainResponse("prettyString" -> JsString(e.prettyString))::Nil
    }
  }
}

class CheckTacticInputRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, tacticId: String,
                              paramName: String, paramType: String, paramValue: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {

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
  extends UserProofRequest(db, userId, proofId) with WriteRequest {
  /** Turns belleTerm into a specific tactic expression, including input arguments */
  private def fullExpr(sequent: Sequent): String = {
    val paramStrings: List[String] = inputs.map{
      case BelleTermInput(value, Some(_:TermArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(_:FormulaArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(_:VariableArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(_:ExpressionArg)) => "{`"+value+"`}"
      case BelleTermInput(value, Some(ListArg(_, "formula", _))) => "[" + value.split(",").map("{`"+_+"`}").mkString(",") + "]"
      case BelleTermInput(value, Some(_:StringArg)) => "{`"+value+"`}"
      case BelleTermInput(value, None) => value
    }
    //@note stepAt(pos) may refer to a search tactic without position (e.g, closeTrue, closeFalse)
    val (specificTerm: String, adaptedPos: Option[PositionLocator], adaptedPos2: Option[PositionLocator]) =
      if (consultAxiomInfo) RequestHelper.getSpecificName(belleTerm, sequent, pos, pos2) match {
        case Left(s) => (s, pos, pos2)
        //@note improve tactic maintainability by position search with formula shape on universally applicable tactics
        case Right(t: PositionTacticInfo) if t.codeName == "hideL" || t.codeName == "hideR" => pos match {
          case Some(Fixed(pp, None, _)) if pp.isTopLevel => (t.codeName, Some(Fixed(pp, Some(sequent(pp.top)))), None)
          case _ => (t.codeName, pos, None)
        }
        case Right(t: PositionTacticInfo) => (t.codeName, pos, None)
        case Right(t: InputPositionTacticInfo) => (t.codeName, pos, None)
        case Right(t: TwoPositionTacticInfo) => (t.codeName, pos, pos2)
        case Right(t: InputTwoPositionTacticInfo) => (t.codeName, pos, pos2)
        case Right(t) => (t.codeName, None, None)
      }
      else (belleTerm, pos, pos2)

    if (inputs.isEmpty && adaptedPos.isEmpty) { assert(adaptedPos2.isEmpty, "Undefined pos1, but defined pos2"); specificTerm }
    else if (inputs.isEmpty && adaptedPos.isDefined && adaptedPos2.isEmpty) { specificTerm + "(" + adaptedPos.get.prettyString + ")" }
    else if (inputs.isEmpty && adaptedPos.isDefined && adaptedPos2.isDefined) { specificTerm + "(" + adaptedPos.get.prettyString + "," + adaptedPos2.get.prettyString + ")" }
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
              if (consultAxiomInfo) RequestHelper.getSpecificName(belleTerm, sequent, pos, pos2, _ => appliedExpr.prettyString)
              else "custom"

            def interpreter(proofId: Int, startNodeId: Int) = new Interpreter {
              val inner = SpoonFeedingInterpreter(proofId, startNodeId, db.createProof, RequestHelper.listenerFactory(db),
                SequentialInterpreter, 0, strict = false)

              override def apply(expr: BelleExpr, v: BelleValue): BelleValue = try {
                inner(expr, v)
              } catch {
                case ex: Throwable => inner.innerProofId match {
                  case Some(innerId) =>
                    //@note display progress of inner (Let) proof, works only in stepwise execution (step details dialog)
                    val innerTrace = db.getExecutionTrace(innerId)
                    if (innerTrace.steps.nonEmpty) BelleSubProof(innerId)
                    else throw BelleTacticFailure("No progress", ex)
                  case None => throw ex
                }
              }

              override def kill(): Unit = inner.kill()
            }

            if (stepwise) {
              if (ruleName == "custom") {
                //@note execute tactic scripts step-by-step for better browsing
                val startStepIndex = node.id match {
                  case DbStepPathNodeId(id, _) => db.getExecutionSteps(proofId.toInt).indexWhere(_.stepId == id)
                  case _ => throw new Exception("Unexpected node ID shape " + node.id.toString
                    + ". Expected step path ID of the form (node ID,branch index)")
                }
                val taskId = node.stepTactic(userId, interpreter(proofId.toInt, startStepIndex), appliedExpr)
                RunBelleTermResponse(proofId, node.id.toString, taskId) :: Nil
              } else {
                val localProvable = ProvableSig.startProof(sequent)
                val localProofId = db.createProof(localProvable)
                val executor = BellerophonTacticExecutor.defaultExecutor
                val taskId = executor.schedule(userId, appliedExpr, BelleProvable(localProvable), interpreter(localProofId, -1))
                RunBelleTermResponse(localProofId.toString, "()", taskId) :: Nil
              }
            } else {
              //@note execute clicked single-step tactics on sequential interpreter right away
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

/** Create a proof if it does not exist yet. Read request, so that guest users can check proofs. */
class InitializeProofFromTacticRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val proofInfo = db.getProofInfo(proofId)
    proofInfo.tactic match {
      case None => new ErrorResponse("Proof " + proofId + " does not have a tactic") :: Nil
      case Some(t) if proofInfo.modelId.isEmpty => throw new Exception("Proof " + proofId + " does not refer to a model")
      case Some(t) if proofInfo.modelId.isDefined =>
        val tactic = BelleParser(t)
        try {
          //@note replace listener created by proof tree (we want a different tactic name for each component of the executed tactic)
          val interpreter = (_: List[IOListener]) => DatabasePopulator.prepareInterpreter(db, proofId.toInt)
          val tree: ProofTree = DbProofTree(db, proofId)
          val taskId = tree.root.runTactic(userId, interpreter, tactic, "")
          RunBelleTermResponse(proofId, "()", taskId) :: Nil
        } catch {
          case _: Throwable =>
            //@note if spoonfeeding interpreter fails, try sequential interpreter so that tactics at least proofcheck
            //      even if browsing then shows a single step only
            val tree: ProofTree = DbProofTree(db, proofId)
            val taskId = tree.root.runTactic(userId, SequentialInterpreter, tactic, "custom")
            RunBelleTermResponse(proofId, "()", taskId) :: Nil
        }
    }
  }
}

class TaskStatusRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
              TaskResultResponse(proofId, node, progress=true)
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
          TaskResultResponse(subId.toString, node, progress = true)
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
  extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    //@note may have completed in the meantime
    executor.tasksForUser(userId).foreach(executor.tryRemove(_, force = true))
    new GenericOKResponse() :: Nil
  }
}

/** Prunes a node and everything below */
class PruneBelowRequest(db : DBAbstraction, userId : String, proofId : String, nodeId : String) extends UserProofRequest(db, userId, proofId) with WriteRequest {
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

class GetProofProgressStatusRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    // @todo return Loading/NotLoaded when appropriate
    val proof = db.getProofInfo(proofId)
    new ProofProgressResponse(proofId, isClosed = proof.closed) :: Nil
  }
}

class CheckIsProvedRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
      val tactic = tree.tacticString
      tree.info.tactic match {
        case None =>
          // remember tactic string
          val newInfo = new ProofPOJO(tree.info.proofId, tree.info.modelId, tree.info.name, tree.info.description,
            tree.info.date, tree.info.stepCount, tree.info.closed, tree.info.provableId, tree.info.temporary,
            Some(tactic))
          db.updateProofInfo(newInfo)
        case Some(_) => // already have a tactic, so do nothing
      }
      // remember lemma
      val lemmaName = "user" + File.separator + model.name
      if (!LemmaDBFactory.lemmaDB.contains(lemmaName)) {
        val evidence = Lemma.requiredEvidence(provable, ToolEvidence(List(
          "tool" -> "KeYmaera X",
          "model" -> model.keyFile,
          "tactic" -> tactic
        )) :: Nil)
        LemmaDBFactory.lemmaDB.add(new Lemma(provable, evidence, Some(lemmaName)))
      }
      new ProofVerificationResponse(proofId, provable, tree.tacticString) :: Nil
    }
  }
}

class IsLicenseAcceptedRequest(db : DBAbstraction) extends Request with ReadRequest {
  def resultingResponses(): List[Response] = {
    new BooleanResponse(
      db.getConfiguration("license").config.contains("accepted") &&
      db.getConfiguration("license").config("accepted") == "true"
    ) :: Nil
  }
}

class AcceptLicenseRequest(db : DBAbstraction) extends Request with WriteRequest {
  def resultingResponses(): List[Response] = {
    val newConfiguration = new ConfigurationPOJO("license", Map("accepted" -> "true"))
    db.updateConfiguration(newConfiguration)
    new BooleanResponse(true) :: Nil
  }
}

class RunScalaFileRequest(db: DBAbstraction, proofId: String, proof: File) extends LocalhostOnlyRequest with WriteRequest {
  override def resultingResponses(): List[Response] = ???
}

/////
// Requests for shutting down KeYmaera if KeYmaera is hosted locally.
/////

class IsLocalInstanceRequest() extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = new BooleanResponse(!HyDRAServerConfig.isHosted) :: Nil
}

class ExtractDatabaseRequest() extends LocalhostOnlyRequest with RegisteredOnlyRequest {
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

class ShutdownReqeuest() extends LocalhostOnlyRequest with RegisteredOnlyRequest {
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

class ExtractTacticRequest(db: DBAbstraction, proofIdStr: String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    ExtractTacticResponse(DbProofTree(db, proofIdStr).tacticString) :: Nil
  }
}

class TacticDiffRequest(db: DBAbstraction, oldTactic: String, newTactic: String) extends Request with ReadRequest {
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

class ExtractLemmaRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
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

class ExtractProblemSolutionRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
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
                                   withProofs: Boolean, exportEmptyProof: Boolean) extends UserRequest(userId) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    def modelProofs(modelId: Int): List[(String, String)] = {
      if (withProofs) db.getProofsForModel(modelId).map(p =>
        p.name -> DbProofTree(db, p.proofId.toString).tacticString)
      else Nil
    }
    val models = modelIds.map(mid => db.getModel(mid) -> modelProofs(mid)).filter(exportEmptyProof || _._2.nonEmpty)
    val archiveContent = models.map({case (model, proofs) => ArchiveEntryPrinter.archiveEntry(model, proofs)}).mkString("\n\n")
    new ExtractProblemSolutionResponse(archiveContent + "\n") :: Nil
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
          BelleInterpreter(proof, BelleProvable(provable)) match {
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
class ValidateProofRequest(db : DBAbstraction, model: Formula, proof: BelleExpr) extends Request with ReadRequest {
  override def resultingResponses() : List[Response] =
    //Spawn an async validation request and return the reesulting UUID.
    new ValidateProofResponse(ProofValidationRunner.scheduleValidationRequest(db, model, proof), None) :: Nil
}

/** An idempotent request for the status of a validation request; i.e., validation requests aren't removed until the server is resst. */
class CheckValidationRequest(db: DBAbstraction, taskId: String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = try {
    new ValidateProofResponse(taskId, ProofValidationRunner.status(taskId)) :: Nil
  } catch {
    case e : ProofValidationRunner.ValidationRequestDNE => new ErrorResponse(e.getMessage, e) :: Nil
  }
}

//endregion

object RequestHelper {

  def printDomain(d: Sort): String = d match {
    case Real => "R"
    case Bool => "B"
    case Unit => ""
    case Tuple(l, r) => printDomain(l) + "," + printDomain(r)
  }

  def augmentDeclarations(content: String, parsedContent: Formula): String =
    if (content.contains("Problem.")) content //@note determine by mandatory "Problem." block of KeYmaeraXProblemParser
    else {
      val symbols = StaticSemantics.symbols(parsedContent)
      val fnDecls = symbols.filter(_.isInstanceOf[Function]).map(_.asInstanceOf[Function]).map(fn =>
        if (fn.sort == Real) s"R ${fn.asString}(${printDomain(fn.domain)})."
        else if (fn.sort == Bool) s"B ${fn.asString}(${printDomain(fn.domain)})."
        else ???
      ).mkString("\n  ")
      val varDecls = symbols.filter(_.isInstanceOf[BaseVariable]).map(v => s"R ${v.prettyString}.").mkString("\n  ")
      s"""Functions.
         |  $fnDecls
         |End.
         |ProgramVariables.
         |  $varDecls
         |End.
         |Problem.
         |  $content
         |End.""".stripMargin
    }

  /* String representation of the actual step (if tacticId refers to stepAt, otherwise tacticId).
     For display purposes only. */
  def getSpecificName(tacticId: String, sequent:Sequent, l1: Option[PositionLocator], l2: Option[PositionLocator],
                      what: DerivationInfo => String): String =  getSpecificName(tacticId, sequent, l1, l2) match {
    case Left(s) => s
    case Right(t) => what(t)
  }

  /* Try to figure out the most intuitive inference rule to display for this tactic. If the user asks us "StepAt" then
   * we should use the StepAt logic to figure out which rule is actually being applied. Otherwise just ask TacticInfo */
  def getSpecificName(tacticId: String, sequent:Sequent, l1: Option[PositionLocator], l2: Option[PositionLocator]): Either[String,DerivationInfo] = {
    val pos = l1 match {case Some(Fixed(p, _, _)) => Some(p) case _ => None}
    val pos2 = l2 match {case Some(Fixed(p, _, _)) => Some(p) case _ => None}
    tacticId.toLowerCase match {
      case ("step" | "stepat") if pos.isDefined && pos2.isEmpty =>
        sequent.sub(pos.get) match {
          case Some(fml: Formula) =>
            UIIndex.theStepAt(fml, pos) match {
              case Some(step) => Right(DerivationInfo(step))
              case None => Left(tacticId)
            }
          case _ => Right(DerivationInfo.ofCodeName(tacticId))
        }
      case ("step" | "stepat") if pos.isDefined && pos2.isDefined =>
        sequent.sub(pos.get) match {
          case Some(fml: Formula) =>
            UIIndex.theStepAt(pos.get, pos2.get, sequent) match {
              case Some(step) => Right(DerivationInfo(step))
              case None => Left(tacticId)
            }
        }
      case _ => Right(DerivationInfo.ofCodeName(tacticId))
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
    val codeName = tacticName.split("\\(").head
    val ruleName = try {
      RequestHelper.getSpecificName(codeName, null, None, None, _ => tacticName)
    } catch {
      case _: Throwable => tacticName
    }
    new TraceRecordingListener(db, proofId, parentStep,
      globalProvable, branch, recursive = false, ruleName) :: Nil
  }

}
