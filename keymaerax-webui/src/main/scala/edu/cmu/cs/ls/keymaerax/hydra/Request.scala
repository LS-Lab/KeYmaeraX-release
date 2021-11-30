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
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfoRegistry
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter, HackyInlineErrorMsgPrinter}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.tools.ext._
import spray.json._
import spray.json.DefaultJsonProtocol.{listFormat, _}

import java.io._
import java.net.URLEncoder
import java.nio.file.{Files, Paths}
import java.text.SimpleDateFormat
import java.util.concurrent.{FutureTask, TimeUnit, TimeoutException}
import java.util.{Calendar, Locale}
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging, UpdateChecker}
import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.CollectProgressListener
import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}

import scala.io.Source
import scala.collection.immutable._
import scala.collection.mutable
import edu.cmu.cs.ls.keymaerax.btactics.cexsearch.{BoundedDFS, ProgramSearchNode}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.codegen.{CControllerGenerator, CGenerator, CMonitorGenerator, CodeGenerator, PythonGenerator, PythonMonitorGenerator}
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.btactics.SwitchedSystems.{Controlled, Guarded, StateDependent, SwitchedSystem, Timed}
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator.TutorialEntry
import edu.cmu.cs.ls.keymaerax.parser.{Name, ParsedArchiveEntry, Signature}
import edu.cmu.cs.ls.keymaerax.tools.ext.{Mathematica, TestSynthesis, WolframScript, Z3}
import edu.cmu.cs.ls.keymaerax.tools.install.{ToolConfiguration, Z3Installer}
import edu.cmu.cs.ls.keymaerax.tools.qe.{DefaultSMTConverter, KeYmaeraToMathematica}
import spray.json.JsonParser.ParsingException

import scala.annotation.tailrec
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
sealed trait Request extends Logging {
  /** Checks read/write/registered access. Additional checks by overriding doPermission. */
  final def permission(t: SessionToken): Boolean = (t match {
    case _: ReadonlyToken => this.isInstanceOf[ReadRequest]
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
        case e: ParseException => new ErrorResponse(e.getMessage, e) :: Nil
        case e: Throwable =>
          new ErrorResponse("We're sorry, an internal safety check was violated, which may point to a bug. The safety check reports " +
            e.getMessage, e, severity = "uncaught") :: Nil
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

/** A request that requires an authenticated user who also passes the `dataPermission` check. */
abstract class UserRequest(userId: String, dataPermission: String => Boolean) extends Request {
  override protected def doPermission(t: SessionToken): Boolean = t.belongsTo(userId) && dataPermission(userId)
}

/** A proof session storing information between requests. */
case class ProofSession(proofId: String, invGenerator: Generator[GenProduct], var invSupplier: Generator[GenProduct],
                        defs: Declaration)

abstract class UserModelRequest(db: DBAbstraction, userId: String, modelId: String)
  //@todo faster query for model user
  extends UserRequest(userId, (id: String) => db.getModel(modelId).userId == id) {
  override final def resultingResponses(): List[Response] = doResultingResponses()
  protected def doResultingResponses(): List[Response]
}

abstract class UserProofRequest(db: DBAbstraction, userId: String, proofId: String)
  //@todo faster query for existence
  extends UserRequest(userId, (id: String) => db.getProofInfo(proofId).modelId.isEmpty || db.userOwnsProof(id, proofId)) {
  override final def resultingResponses(): List[Response] = {
    Try(proofId.toInt).toOption match {
      case Some(_) => doResultingResponses()
      case None => new ErrorResponse("The user interface lost track of the proof, please try reloading the page.") :: Nil //@note Web UI bug)
    }
  }

  protected def doResultingResponses(): List[Response]
}

abstract class LocalhostOnlyRequest() extends Request {
  override protected def doPermission(t: SessionToken): Boolean = !HyDRAServerConfig.isHosted //@todo change this to a literal false prior to deployment.
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Users
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class CreateUserRequest(db: DBAbstraction, userId: String, password: String, mode: String) extends Request with WriteRequest {
  override def resultingResponses(): List[Response] = {
    db.getUser(userId) match {
      case Some(user) => new LoginResponse(false, user, None) ::  Nil
      case None =>
        db.createUser(userId, password, mode)
        db.getUser(userId) match {
          case Some(newUser) => new LoginResponse(true, newUser, Some(SessionManager.add(newUser))) ::  Nil
          case None => new ErrorResponse("Failed to create user " + userId) :: Nil
        }
    }
  }
}

class SetDefaultUserRequest(db: DBAbstraction, userId: String, password: String, useDefault: Boolean) extends LocalhostOnlyRequest with WriteRequest {
  override def resultingResponses(): List[Response] = {
    if (useDefault) {
      if (db.checkPassword(userId, password)) {
        Configuration.set(Configuration.Keys.DEFAULT_USER, userId, saveToFile = true)
        Configuration.set(Configuration.Keys.USE_DEFAULT_USER, "true", saveToFile = true)
        BooleanResponse(flag = true) :: Nil
      } else new ErrorResponse("Failed to set default user") :: Nil
    } else {
      Configuration.remove(Configuration.Keys.DEFAULT_USER, saveToFile = true)
      Configuration.set(Configuration.Keys.USE_DEFAULT_USER, "false", saveToFile = true)
      BooleanResponse(flag = true) :: Nil
    }
  }
}

class LocalLoginRequest(db: DBAbstraction, userId: String, password: String) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true") && userId == "local") {
      Configuration.getString(Configuration.Keys.DEFAULT_USER) match {
        case Some(userId) => db.getUser(userId) match {
          case Some(user) =>
            val sessionToken = Some(SessionManager.add(user))
            new LoginResponse(true, user, sessionToken) :: Nil
          case None => DefaultLoginResponse(triggerRegistration = true) :: Nil
        }
        case None => DefaultLoginResponse(triggerRegistration = true) :: Nil
      }
    } else {
      val check = db.checkPassword(userId, password)
      db.getUser(userId) match {
        case Some(user) =>
          val sessionToken =
            if (check) Some(SessionManager.add(user))
            else None
          new LoginResponse(check, user, sessionToken) :: Nil
        case None => new ErrorResponse("Unable to login user " + userId
          + ". Please double-check user name and password, or register a new user.") :: Nil
      }
    }
  }
}

class LoginRequest(db: DBAbstraction, userId: String, password: String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val check = db.checkPassword(userId, password)
    db.getUser(userId) match {
      case Some(user) =>
        val sessionToken =
          if (check) Some(SessionManager.add(user))
          else None
        new LoginResponse(check, user, sessionToken) :: Nil
      case None => new ErrorResponse("Unable to login user " + userId
        + ". Please double-check user name and password, or register a new user.") :: Nil
    }
  }
}

class ProofsForUserRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponses(): List[Response] = {
    val proofs = db.getProofsForUser(userId).filterNot(_._1.temporary).map(proof =>
      (proof._1, "loaded"/*KeYmaeraInterface.getTaskLoadStatus(proof._1.proofId.toString).toString.toLowerCase*/))
    new ProofListResponse(proofs) :: Nil
  }
}

class UserLemmasRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponses(): List[Response] = {
    def getLemma(model: Option[ModelPOJO]): Option[(String, Lemma)] =
      model.flatMap(m => LemmaDBFactory.lemmaDB.get("user" + File.separator + m.name).map(m.name -> _))
    val proofs = db.getProofsForUser(userId).filterNot(_._1.temporary).filter(_._1.closed).
      groupBy(_._1.modelId).map(_._2.head).map(proof => (proof._1, getLemma(proof._1.modelId.map(db.getModel)))).toList
    new UserLemmasResponse(proofs) :: Nil
  }
}

class UpdateProofNameRequest(db: DBAbstraction, userId: String, proofId: String, newName: String)
  extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    db.updateProofName(proofId, newName)
    new UpdateProofNameResponse(proofId, newName) :: Nil
  }
}

class FailedRequest(userId: String, msg: String, cause: Throwable = null) extends UserRequest(userId, _ => true) {
  def resultingResponses(): List[Response] = { new ErrorResponse(msg, cause) :: Nil }
}

class CounterExampleRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String,
                            assumptions: String, fmlIndices: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  def allFnToVar(fml: Formula, fn: Function): Formula = {
    fml.find(t => t match {
        case FuncOf(func, _) if fn.sort == Real => func == fn
        case PredOf(func, arg) if fn.sort == Bool && arg != Nothing => func == fn
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
    val assumptionsJson = assumptions.parseJson.asJsObject.fields.get("additional")
    val additionalAssumptions: Option[Formula] = try {
      assumptionsJson.map(_.convertTo[String].asFormula)
    } catch {
      case ex: ParseException => return ParseErrorResponse("Expected assumptions as a formula, but got " + assumptionsJson.getOrElse("<empty>"),
        ex.expect, ex.found, ex.getDetails, ex.loc, ex) :: Nil
    }

    val useFmlIndices = fmlIndices.parseJson.convertTo[List[String]].map(_.toInt)

    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId)::Nil
      case Some(node) =>
        //@note not a tactic because we don't want to change the proof tree just by looking for counterexamples
        def nonfoError(sequent: Sequent) = {
          val nonFOAnte = sequent.ante.filterNot(_.isFOL)
          val nonFOSucc = sequent.succ.filterNot(_.isFOL)
          new CounterExampleResponse("cex.nonfo", (nonFOSucc ++ nonFOAnte).head) :: Nil
        }

        def filterSequent(s: Sequent): Sequent = s.copy(
          ante = s.ante.zipWithIndex.filter({ case (_, i) => useFmlIndices.contains(-(i+1)) }).map(_._1),
          succ = s.succ.zipWithIndex.filter({ case (_, i) => useFmlIndices.contains(  i+1 ) }).map(_._1)
        )

        @tailrec
        def getCex(node: ProofTreeNode, cexTool: CounterExampleTool): List[Response] = {
          val nodeGoal = node.goal.get
          val sequent = filterSequent(nodeGoal)
          if (sequent.isFOL) {
            if (StaticSemantics.symbols(sequent).isEmpty) {
              //@note counterexample on false (e.g., after QE on invalid formula)
              node.parent match {
                case Some(parent) => getCex(parent, cexTool)
                case None => new CounterExampleResponse("cex.none") :: Nil
              }
            } else {
              val skolemized = TactixLibrary.proveBy(sequent,
                SaturateTactic(TactixLibrary.alphaRule | TactixLibrary.allR('R) | TactixLibrary.existsL('L)))
              val fml = skolemized.subgoals.map(_.toFormula).reduceRight(And)
              val withAssumptions = additionalAssumptions match {
                case Some(a) => Imply(a, fml)
                case None => fml
              }
              try {
                findCounterExample(withAssumptions, cexTool) match {
                  //@todo return actual sequent, use collapsiblesequentview to display counterexample
                  case Some(cex) => new CounterExampleResponse("cex.found", fml, cex) :: Nil
                  case None => new CounterExampleResponse("cex.none") :: Nil
                }
              } catch {
                case _: MathematicaComputationAbortedException => new CounterExampleResponse("cex.timeout") :: Nil
                case ex: ToolException => new ErrorResponse("Error executing counterexample tool", ex) :: Nil
              }
            }
          } else {
            ToolProvider.qeTool() match {
              case Some(qeTool) =>
                val fml = sequent.toFormula
                Try(ProgramSearchNode(fml)(qeTool)).toOption match {
                  case Some(snode) =>
                    if (FormulaTools.dualFree(snode.prog)) {
                      try {
                        val search = new BoundedDFS(10)
                        search(snode) match {
                          case None => nonfoError(sequent)
                          case Some(cex) => new CounterExampleResponse("cex.found", fml, cex.map) :: Nil
                        }
                      } catch {
                        // Counterexample generation is quite hard for, e.g. ODEs, so expect some cases to be unimplemented.
                        // When that happens, just tell the user they need to simplify the formula more.
                        case _: NotImplementedError => nonfoError(sequent)
                      }
                    } else {
                      // no automated counterexamples for games yet
                      nonfoError(sequent)
                    }
                  case None => new CounterExampleResponse("cex.wrongshape") :: Nil
                }
              case None => new CounterExampleResponse("cex.notool") :: Nil
            }
          }
        }

        if (useFmlIndices.nonEmpty) try {
          node.goal match {
            case Some(unfiltered) if filterSequent(unfiltered).isFOL => ToolProvider.cexTool() match {
                case Some(cexTool) => getCex(node, cexTool)
                case None => new CounterExampleResponse("cex.notool") :: Nil
              }
            case Some(unfiltered) =>
              val sequent = filterSequent(unfiltered)
              sequent.succ.find({ case Box(_: ODESystem, _) => true case _ => false }) match {
                case Some(Box(ode: ODESystem, post)) => ToolProvider.invGenTool() match {
                  case Some(tool) => tool.refuteODE(ode, sequent.ante, post) match {
                    case None => new CounterExampleResponse("cex.none") :: Nil
                    case Some(cex) => new CounterExampleResponse("cex.found", sequent.toFormula, cex) :: Nil
                  }
                  case None => new CounterExampleResponse("cex.notool") :: Nil
                }
                case None => nonfoError(sequent)
              }
            case None => new CounterExampleResponse("cex.none") :: Nil
          }
        } catch {
          case _: MathematicaComputationAbortedException => new CounterExampleResponse("cex.timeout") :: Nil
        } else new CounterExampleResponse("cex.emptysequent") :: Nil
    }
  }
}

class ODEConditionsRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(node) =>
        try {
          node.goal match {
            case Some(sequent) => sequent.succ.find({ case Box(_: ODESystem, _) => true case _ => false }) match {
              case Some(Box(ode: ODESystem, post)) => ToolProvider.invGenTool() match {
                case Some(tool) =>
                  val (sufficient, necessary) = tool.genODECond(ode, sequent.ante, post)
                  new ODEConditionsResponse(sufficient, necessary) :: Nil
                case None => new ODEConditionsResponse(Nil, Nil) :: Nil
              }
              case None => new ErrorResponse("ODE system needed to search for ODE conditions, but succedent does not contain an ODE system or ODE system may not be at top level. Please perform additional proof steps until ODE system is at top level.") :: Nil
            }
            case None => new ErrorResponse("ODE system needed to search for ODE conditions, but goal is empty.") :: Nil
          }
        } catch {
          case _: MathematicaComputationAbortedException => new ErrorResponse("ODE conditions search timeout.") :: Nil
        }
    }
  }
}

class PegasusCandidatesRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(node) =>
        try {
          node.goal match {
            case Some(sequent) => sequent.succ.find({ case Box(_: ODESystem, _) => true case _ => false }) match {
              case Some(Box(ode: ODESystem, post)) if post.isFOL => ToolProvider.invGenTool() match {
                case Some(tool) =>
                  val invs = tool.invgen(ode, sequent.ante, post)
                  new PegasusCandidatesResponse(invs) :: Nil
                case None => new PegasusCandidatesResponse(Nil) :: Nil
              }
              case Some(Box(_, post)) if !post.isFOL => new ErrorResponse("Post-condition in FOL is needed to search for invariants; please perform further proof steps until the post-condition of the ODE is a formula in first-order logic.") :: Nil
              case None => new ErrorResponse("ODE system needed to search for invariant candidates, but succedent does not contain an ODE system or ODE system may not be at top level. Please perform additional proof steps until ODE system is at top level.") :: Nil
            }
            case None => new ErrorResponse("ODE system needed to search for invariant candidates, but goal is empty.") :: Nil
          }
        } catch {
          case _: MathematicaComputationAbortedException => new ErrorResponse("ODE invariant search timeout.") :: Nil
        }
    }
  }
}

class SetupSimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with RegisteredOnlyRequest {
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
            val vars = (StaticSemantics.symbols(prg) ++ StaticSemantics.symbols(initial)).filter(_.isInstanceOf[BaseVariable])
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
      case Box(Assign(_,_),_) => Ax.assignbAxiom :: Ax.assignbup :: Nil
      case Diamond(Assign(_,_),_) => Ax.assigndAxiom :: Ax.assigndup :: Nil
      // remove loops
      case Diamond(Loop(_), _) => Ax.loopApproxd :: Nil
      //@note: do nothing, should be gone already
      case Diamond(ODESystem(_, _), _) => Nil
      case _ => AxIndex.axiomsFor(e)
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
      DifferentialHelper.getPrimedVariables(ode).map(v => v -> Variable(v.name + "0", v.index, v.sort)).toMap
    val time: Variable = Variable("t_", None, Real)
    //@note replace initial values with original variable, since we turn them into assignments
    val solution = replaceFree(ToolProvider.odeTool().get.odeSolve(ode, time, iv).get, iv.map(_.swap))
    val flatSolution = FormulaTools.conjuncts(solution).
      sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size)
    Compose(
      flatSolution.map({ case Equal(v: Variable, r) => Assign(v, r) }).reduceRightOption(Compose).getOrElse(Test(True)),
      Test(evoldomain))
  }

  private def replaceFree(f: Formula, vars: Map[Variable, Variable]) = {
    vars.keySet.foldLeft[Formula](f)((b, v) => b.replaceFree(v, vars(v)))
  }
}

class SimulationRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, initial: Formula,
                        stateRelation: Formula, steps: Int, n: Int, stepDuration: Term)
  extends UserProofRequest(db, userId, proofId) with RegisteredOnlyRequest {
  override protected def doResultingResponses(): List[Response] = {
    def replaceFuncs(fml: Formula) = ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case FuncOf(Function(name, idx, Unit, Real, false), _) => Right(BaseVariable(name, idx))
        case _ => Left(None)
      }
    }, fml)

    ToolProvider.simulationTool() match {
      case Some(s) =>
        val varsStateRelation = replaceFuncs(stateRelation).get
        val varsInitial = replaceFuncs(initial).get
        val timedStateRelation = varsStateRelation.replaceFree(Variable("t_"), stepDuration)
        val simulation = s.simulate(varsInitial, timedStateRelation, steps, n)
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
    // keymaera X version
    val kyxConfig = "KeYmaera X version: " + VERSION + newline +
      "Java version: " + System.getProperty("java.runtime.version") + " with " + System.getProperty("sun.arch.data.model") + " bits" + newline +
      "OS: " + System.getProperty("os.name") + " " + System.getProperty("os.version") + newline +
      "LinkName: " + Configuration.getString(Configuration.Keys.MATHEMATICA_LINK_NAME) + newline +
      "jlinkLibDir: " + Configuration.getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
    new KyxConfigResponse(kyxConfig) :: Nil
  }
}

class KeymaeraXVersionRequest() extends Request with ReadRequest {
  override def resultingResponses() : List[Response] = {
    val keymaeraXVersion = VERSION
    val (upToDate, latestVersion) = UpdateChecker.getVersionStatus match {
      case Some((upd, lv)) => (Some(upd), Some(lv))
      case _ => (None, None)
    }
    new KeymaeraXVersionResponse(keymaeraXVersion, upToDate, latestVersion) :: Nil
  }
}

class ConfigureMathematicaRequest(db: DBAbstraction, toolName: String,
                                  linkName: String, jlinkLibFileName: String, jlinkTcpip: String)
    extends LocalhostOnlyRequest with WriteRequest {
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
    } else {
      ToolProvider.shutdown()
      Configuration.set(Configuration.Keys.QE_TOOL, toolName)
      // prefer TCPIP=false if no specific port/machine is configured
      val tcpip = jlinkTcpip match {
        case "true" | "false" => "false" // not user-configurable with this request (but configurable with Advanced options, which then takes precedence)
        case x => x
      }
      val provider = toolName match {
        case "wolframengine" =>
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_TCPIP, tcpip)
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_LINK_NAME, linkNameFile.getAbsolutePath)
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR, jlinkLibDir.getAbsolutePath)
          ToolProvider.initFallbackZ3(WolframEngineToolProvider(ToolConfiguration.config(toolName)), "Wolfram Engine")
        case "mathematica" =>
          Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, tcpip)
          Configuration.set(Configuration.Keys.MATHEMATICA_LINK_NAME, linkNameFile.getAbsolutePath)
          Configuration.set(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR, jlinkLibDir.getAbsolutePath)
          ToolProvider.initFallbackZ3(MathematicaToolProvider(ToolConfiguration.config(toolName)), "Mathematica")
      }
      ToolProvider.setProvider(provider)
      new ConfigureMathematicaResponse(linkNameFile.getAbsolutePath, jlinkLibDir.getAbsolutePath, true) :: Nil
    }
  }
}

class ConfigureZ3Request(z3Path: String) extends LocalhostOnlyRequest with WriteRequest {
  private def isZ3PathCorrect(z3Path: java.io.File): Boolean = z3Path.getName == "z3" || z3Path.getName == "z3.exe"

  override def resultingResponses(): List[Response] = {
    //check to make sure the indicated files exist and point to the correct files.
    val z3File = new java.io.File(z3Path)
    val z3Exists = isZ3PathCorrect(z3File)

    if (!z3Exists) {
      new ConfigureZ3Response("", false) :: Nil
    } else {
      ToolProvider.shutdown()
      Configuration.set(Configuration.Keys.QE_TOOL, "z3")
      Configuration.set(Configuration.Keys.Z3_PATH, z3Path)
      ToolProvider.setProvider(Z3ToolProvider(Map("z3Path" -> z3Path)))
      new ConfigureZ3Response(z3File.getAbsolutePath, true) :: Nil
    }
  }
}

class GetMathematicaConfigSuggestionRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val allSuggestions = ToolConfiguration.mathematicaSuggestion()
    val (suggestionFound, suggestion) = allSuggestions.find(s => new java.io.File(s.kernelPath + s.kernelName).exists &&
        new java.io.File(s.jlinkPath + s.jlinkName).exists) match {
      case Some(s) => (true, s)
      case None => (false, allSuggestions.head) // use the first configuration as suggestion when nothing else matches
    }

    val os = System.getProperty("os.name")
    val jvmBits = System.getProperty("sun.arch.data.model")
    new MathematicaConfigSuggestionResponse(os, jvmBits, suggestionFound, suggestion, allSuggestions) :: Nil
  }
}

class GetWolframEngineConfigSuggestionRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val allSuggestions = ToolConfiguration.wolframEngineSuggestion()
    val (suggestionFound, suggestion) = allSuggestions.find(s => new java.io.File(s.kernelPath + s.kernelName).exists &&
      new java.io.File(s.jlinkPath + s.jlinkName).exists) match {
      case Some(s) => (true, s)
      case None => (false, allSuggestions.head) // use the first configuration as suggestion when nothing else matches
    }

    val os = System.getProperty("os.name")
    val jvmBits = System.getProperty("sun.arch.data.model")
    new MathematicaConfigSuggestionResponse(os, jvmBits, suggestionFound, suggestion, allSuggestions) :: Nil
  }
}

class GetWolframScriptConfigSuggestionRequest(db: DBAbstraction) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val os = System.getProperty("os.name")
    val jvmBits = System.getProperty("sun.arch.data.model")
    try {
      val we = new WolframScript()
      val version = we.getVersion
      we.shutdown()
      new MathematicaConfigSuggestionResponse(os, jvmBits, true,
        ToolConfiguration.ConfigSuggestion(version.major + "." + version.minor + "." + version.revision, "", "", "",
        ""), Nil) :: Nil
    } catch {
      case _: Throwable =>
        new MathematicaConfigSuggestionResponse(os, jvmBits, false,
          ToolConfiguration.ConfigSuggestion("", "", "", "", ""), Nil) :: Nil
    }
  }
}

class GetZ3ConfigSuggestionRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    new Z3ConfigSuggestionResponse(Z3Installer.defaultZ3Path) :: Nil
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
    // StringOps for JDK 11 compatibility
    val lines = (Source.fromInputStream(reader).mkString: StringOps).lines.toList
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
    val toolName = Configuration(Configuration.Keys.QE_TOOL)
    ToolProvider.tool(toolName) match {
      case Some(tool) =>
        val initialized = tool.isInitialized
        if (initialized) new KvpResponse("tool", toolName) :: Nil
        else new ErrorResponse(toolName + " is not initialized. Please double-check the configuration paths.") :: Nil
      case _ => new ErrorResponse(toolName + " failed to initialize. Please reselect the desired tool and double-check the configuration paths. Temporarily switched to fallback tools " + ToolProvider.tools().map(_.name).mkString(",")) :: Nil
    }
  }
}

class SetToolRequest(db: DBAbstraction, tool: String) extends LocalhostOnlyRequest with WriteRequest {
  override def resultingResponses(): List[Response] = {
    //@todo more/different tools
    if (tool != "mathematica" && tool != "z3" && tool != "wolframengine" && tool != "wolframscript") new ErrorResponse("Unknown tool " + tool + ", expected either 'mathematica' or 'z3' or 'wolframengine'")::Nil
    else {
      assert(tool == "mathematica" || tool == "z3" || tool == "wolframengine" || tool == "wolframscript", "Expected either Mathematica or Z3 or Wolfram Engine tool")
      ToolProvider.shutdown()
      val config = ToolConfiguration.config(tool)
      try {
        val (provider: Option[ToolProvider], saveToConfig: Boolean) = tool match {
          case "mathematica" =>
            if (new java.io.File(config.getOrElse("linkName", "")).exists &&
                new java.io.File(config.getOrElse("libDir", "")).exists) {
              if (Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) &&
                Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)) {
                (Some(MultiToolProvider(MathematicaToolProvider(config) :: Z3ToolProvider() :: Nil)), true)
              } else (None, false)
            } else {
              (Some(Z3ToolProvider()), false)
            }
          case "wolframengine" =>
            if (new java.io.File(config.getOrElse("linkName", "")).exists &&
                new java.io.File(config.getOrElse("libDir", "")).exists) {
              if (Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) &&
                Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) &&
                Configuration.contains(Configuration.Keys.WOLFRAMENGINE_TCPIP)) {
                (Some(MultiToolProvider(WolframEngineToolProvider(config) :: Z3ToolProvider() :: Nil)), true)
              } else (None, false)
            } else {
              (Some(Z3ToolProvider()), false)
            }
          case "wolframscript" => (Some(MultiToolProvider(WolframScriptToolProvider(Map.empty) :: Z3ToolProvider() :: Nil)), true)
          case "z3" => (Some(Z3ToolProvider()), true)
          case _ => (Some(new NoneToolProvider), false)
        }
        provider match {
          case Some(p) =>
            if (saveToConfig) Configuration.set(Configuration.Keys.QE_TOOL, tool)
            ToolProvider.setProvider(p)
          case _ => // nothing to do
        }
        new ToolConfigStatusResponse(tool, provider.isDefined) :: Nil
      } catch {
        case ex: Throwable if tool == "mathematica" => new ErrorResponse("Error initializing " + tool + ". Please double-check the configuration paths, that the license is valid (e.g., start Mathematica and type $LicenseExpirationDate, check that license server is reachable, if used), and that the Java JVM 32/64bit fits your operating system.", ex) :: Nil
        case ex: Throwable if tool == "wolframengine" => new ErrorResponse("Error initializing " + tool + ". Please double-check the configuration paths, that the license is valid and the computer is online for license checking. If Wolfram Engine remains unavailable and/or keeps crashing KeYmaera X, please run Wolfram Engine to update the license information (check by running $LicenseExpirationDate in Wolfram Engine) prior to starting KeYmaera X. Also make sure that the Java JVM 32/64bit fits your operating system.", ex) :: Nil
        case ex: Throwable => new ErrorResponse("Error initializing " + tool + ". Please double-check the configuration paths and that the Java JVM 32/64bit fits your operating system.", ex) :: Nil
      }
    }
  }
}

class GetMathematicaConfigurationRequest(db: DBAbstraction, toolName: String) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    val jlinkLibFile = {
      if (osName.contains("win")) "JLinkNativeLibrary.dll"
      else if (osName.contains("mac")) "libJLinkNativeLibrary.jnilib"
      else if (osName.contains("nix") || osName.contains("nux") || osName.contains("aix")) "libJLinkNativeLibrary.so"
      else "Unknown"
    }
    toolName match {
      case "mathematica" if Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) && Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) =>
          new MathematicaConfigurationResponse(
            Configuration(Configuration.Keys.MATHEMATICA_LINK_NAME),
            Configuration(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) + File.separator + jlinkLibFile,
            Configuration.getString(Configuration.Keys.MATH_LINK_TCPIP).getOrElse("")
          ) :: Nil
      case "wolframengine" if Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) && Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) =>
        new MathematicaConfigurationResponse(
          Configuration(Configuration.Keys.WOLFRAMENGINE_LINK_NAME),
          Configuration(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) + File.separator + jlinkLibFile,
          Configuration.getString(Configuration.Keys.WOLFRAMENGINE_TCPIP).getOrElse("")
        ) :: Nil
      case _ => new MathematicaConfigurationResponse("", "", "") :: Nil
    }
  }
}

class GetZ3ConfigurationRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    new Z3ConfigurationResponse(Z3Installer.z3Path) :: Nil
  }
}

class GetFullConfigRequest extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val w = new StringWriter()
    Configuration.printConfig(new PrintWriter(w))
    new FullConfigurationResponse(w.toString) :: Nil
  }
}

class SaveFullConfigRequest(content: String) extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    Configuration.overwrite(content)
    BooleanResponse(flag = true) :: Nil
  }
}

class GetUserThemeRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration(userId).config
    new PlainResponse(
      "themeCss" -> config.getOrElse("themeCss", "\"app\"").parseJson,
      "themeFontSize" -> config.getOrElse("themeFontSize", "14").parseJson,
      "renderMargins" -> config.getOrElse("renderMargins", "[40,80]").parseJson
    ) :: Nil
  }
}

/** Sets the UI theme. @note ReadRequest allows changing theme in guest mode for presentation purposes. */
class SetUserThemeRequest(db: DBAbstraction, userId: String, themeCss: String, themeFontSize: String, renderMargins: String)
    extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val config = db.getConfiguration(userId)
    db.updateConfiguration(new ConfigurationPOJO(userId,
      config.config.updated("themeCss", themeCss).
        updated("themeFontSize", themeFontSize).
        updated("renderMargins", renderMargins)))
    new PlainResponse(
      "themeCss" -> themeCss.parseJson,
      "themeFontSize" -> themeFontSize.parseJson,
      "renderMargins" -> renderMargins.parseJson
    ) :: Nil
  }
}


class MathematicaConfigStatusRequest(db: DBAbstraction) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    ToolProvider.tool("mathematica") match {
      case Some(_) =>
        new ToolConfigStatusResponse("mathematica",
          Configuration.contains(Configuration.Keys.MATHEMATICA_LINK_NAME) &&
          Configuration.contains(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) &&
          ToolProvider.tool("mathematica").isDefined) :: Nil
      case None => new ToolConfigErrorResponse("mathematica", "Mathematica could not be started; please double-check the configured paths and make sure you have a valid license (if you use a license server, make sure it is reachable). Temporarily using " + ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.") :: Nil
    }
  }
}

class WolframEngineConfigStatusRequest(db: DBAbstraction) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    ToolProvider.tool("wolframEngine") match {
      case Some(_) =>
        new ToolConfigStatusResponse("wolframengine",
          Configuration.contains(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) &&
          Configuration.contains(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) &&
          Configuration.contains(Configuration.Keys.WOLFRAMENGINE_TCPIP)) :: Nil
      case None => new ToolConfigErrorResponse("wolframengine", "Wolfram Engine could not be started; please double-check the configured paths and make sure you are online for license checking. Temporarily using " + ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.") :: Nil
    }

  }
}

class WolframScriptConfigStatusRequest(db: DBAbstraction) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = new ToolConfigStatusResponse("wolframscript", true) :: Nil
}

class ToolStatusRequest(db: DBAbstraction, toolId: String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    //@todo switchSolver tactic switches tool without telling UI
    ToolProvider.tool(toolId) match {
      case Some(t: ToolOperationManagement) => new ToolStatusResponse(toolId, t.getAvailableWorkers) :: Nil
      case Some(_) => new ToolStatusResponse(toolId, -1) :: Nil
      case None => new ToolConfigErrorResponse(toolId, "Tool could not be started; please check KeYmaera X -> Preferences. Temporarily using " + ToolProvider.tools().map(_.name).mkString(",") + " with potentially limited functionality.") :: Nil
    }
  }
}

//@todo Detect closed connections and request timeouts server-side
class CancelToolRequest() extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val allCancelled = ToolProvider.tools().map(_.cancel()).reduce(_ && _)
    BooleanResponse(flag = allCancelled) :: Nil
  }
}

class Z3ConfigStatusRequest(db: DBAbstraction) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = new ToolConfigStatusResponse("z3", true) :: Nil
}

class RestartToolRequest(db: DBAbstraction, toolId: String) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    ToolProvider.tool(toolId) match {
      case Some(t: Tool) =>
        t.restart()
        new GenericOKResponse :: Nil
      case _ => new ErrorResponse(s"Restarting failed: unknown tool '$toolId'. Please check the tool configuration.") :: Nil
    }

  }
}

class TestToolConnectionRequest(db: DBAbstraction, toolId: String) extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    ToolProvider.tool(toolId) match {
      case Some(t: QETool) =>
        val simpleQeTask = new FutureTask[Either[Formula, Throwable]](() =>
          try {
            Left(t.quantifierElimination("1+2=3".asFormula))
          } catch {
            case e: Throwable => Right(e)
          })
        new Thread(simpleQeTask).start()
        try {
          val result = simpleQeTask.get(1, TimeUnit.SECONDS)
          if (result.isLeft && result.left.get == "true".asFormula) new GenericOKResponse :: Nil
          else if (result.isLeft && result.left.get != "true".asFormula) new ErrorResponse("Testing connection failed: unexpected result " + result.left.get + " for test 2+3=5") :: Nil
          else /* result.isRight */ new ErrorResponse("Testing connection failed", result.right.get) :: Nil
        } catch {
          case _: TimeoutException =>
            new ErrorResponse("Testing connection failed: tool is not responding. Please restart KeYmaera X.") :: Nil
        }
      case Some(t: Tool) => new ErrorResponse(s"Testing connection failed: do not know how to test '${t.getClass}' tool") :: Nil
      case _ => new ErrorResponse(s"Testing connection failed: unknown tool '$toolId'. Please check the tool configuration.") :: Nil
    }

  }
}

/** List of all predefined tutorials that can directly be imported from the KeYmaera X web UI, in order of display. */
class ListExamplesRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    //@todo read from the database/some web page?
    //@note Learner's mode Level=0, Industry mode Level=1
    val examples = List(
      ExamplePOJO(6, "Textbook",
        "LFCPS 2018 Textbook Examples",
        "",
        "classpath:/keymaerax-projects/lfcps/lfcps.kyx",
        "/examples/tutorials/lfcps-examples.png", 0),
      ExamplePOJO(6, "MOD19",
        "Marktoberdorf 2019 Tutorial Examples",
        //"/keymaerax-projects/lfcps-turorial/README.md",
        "",
        "classpath:/keymaerax-projects/lfcps-tutorial/lfcps-tutorial.kyx",
        "/examples/tutorials/cpsweek/cpsweek.png", 1),
      ExamplePOJO(5, "POPL 2019 Tutorial",
        "Programming CPS With Proofs",
        //"/keymaerax-projects/popltutorial/README.md",
        "",
        "classpath:/keymaerax-projects/popltutorial/popltutorial.kyx",
        "/examples/tutorials/cpsweek/cpsweek.png", 1),
      ExamplePOJO(4, "DLDS",
        "Dynamic Logic for Dynamical Systems Marktoberdorf 2017",
        //"/keymaerax-projects/dlds/README.md",
        "",
        "classpath:/keymaerax-projects/dlds/dlds.kya",
        "/examples/tutorials/cpsweek/cpsweek.png", 1),
      ExamplePOJO(0, "STTT Tutorial",
        "Collection of tutorial examples",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/sttt/sttt.kyx",
        "/examples/tutorials/sttt/sttt.png", 1),
      ExamplePOJO(1, "CPSWeek 2016 Tutorial",
        "Modeling and Proving ODEs",
        "http://www.ls.cs.cmu.edu/KeYmaeraX/KeYmaeraX-tutorial.pdf",
        "classpath:/examples/tutorials/cpsweek/cpsweek.kyx",
        "/examples/tutorials/cpsweek/cpsweek.png", 1),
      ExamplePOJO(2, "FM 2016 Tutorial",
        "Tactics and Proofs",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/fm/fm.kyx",
        "/examples/tutorials/fm/fm.png", 1),
      ExamplePOJO(3, "Beginner's Tutorial",
        "Feature Tour Tutorial",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/basic/basictutorial.kyx",
        "/examples/tutorials/fm/fm.png", 0),
//        new ExamplePOJO(3, "POPL 2019 Tutorial",
//          "Programming CPS With Proofs",
//          //"/keymaerax-projects/popltutorial/README.md",
//          "",
//          "classpath:/keymaerax-projects/popltutorial/popltutorial.kyx",
//          "/examples/tutorials/cpsweek/cpsweek.png", 1)
    )

    db.getUser(userId) match {
      case Some(user) => new ListExamplesResponse(examples.filter(_.level <= user.level)) :: Nil
      case None => new ErrorResponse("Unable to retrieve examples. Unknown user " + userId) :: Nil
    }

  }
}

class GetTemplatesRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val templates = List(
      TemplatePOJO("Plain", "A plain dL formula",
        """ArchiveEntry "New Entry"
          |
          |Problem
          |  /* fill in dL formula here */
          |End.
          |End.""".stripMargin,
        Some(new Region(3, 2, 3, 31)),
        None
      ),
      TemplatePOJO(
        "Structured", "Archive with definitions",
        """ArchiveEntry "New Entry"
          |
          |Definitions
          |  /* A constant with arbitrary value, constrained in predicate p */
          |  /* Real any; */
          |
          |  /* The constant 2 */
          |  /* Real two = 2; */
          |
          |  /* An uninterpreted function */
          |  /* Real f(Real x, Real y); */
          |
          |  /* Function x^2 */
          |  /* Real sq(Real x) = x^two; */
          |
          |  /* Predicate x<=y */
          |  /* Bool leq(Real x, Real y) <-> x<=y; */
          |
          |  /* Predicate p uses other definitions */
          |  /* Bool p(Real x) <-> any>=two & leq(x,two); */
          |
          |  /* Hybrid programs */
          |  /* HP increment ::= { x:=x+1; }; */
          |  /* HP ode ::= { {x'=sq(x) & leq(x,two) } }; */
          |  /* HP system ::= { { increment; ode; }* }; */
          |End.
          |
          |ProgramVariables
          |  /* Real x; */
          |End.
          |
          |Problem
          |  /* fill in dL formula here */
          |  /* p(x) -> [system;]leq(x,any) */
          |End.
          |
          |/* Optional tactic to prove the problem */
          |/*
          |Tactic "Proof"
          |implyR('R=="p(x)->[system{|^@|};]leq(x,any())");
          |expand "system";
          |loop("leq(x,two())", 'R=="[{increment{|^@|};ode{|^@|};}*]leq(x,any())"); <(
          |  "Init":
          |    propClose,
          |  "Post":
          |    QE,
          |  "Step":
          |    composeb('R=="[increment{|^@|};ode{|^@|};]x<=2");
          |    expandAllDefs;
          |    unfold;
          |    ODE('R=="[{x'=x^2&x<=2}]x<=2")
          |)
          |End.
          |*/
          |End.""".stripMargin,
        Some(new Region(33, 2, 33, 35)),
        None
      )
    )

    db.getUser(userId) match {
      case Some(_) => new GetTemplatesResponse(templates) :: Nil
      case None => new ErrorResponse("Unable to retrieve templates. Unknown user " + userId) :: Nil
    }

  }
}

class CreateControlledStabilityTemplateRequest(userId: String, code: String, switchingKind: String, specKind: List[String],
                                               vertices: JsArray, subGraphs: JsArray, transitions: JsArray) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val mode = "mode".asVariable
    def modeOf(s: String): Term = FuncOf(Function(s, None, Unit, Real), Nothing)

    val transitionsByVertex = transitions.elements.toList.map(_.asJsObject).map(t => {
      val ttext = t.fields("text").convertTo[String]
      (t.fields("start").convertTo[String],
        (t.fields("end").convertTo[String], if (ttext.isEmpty) Test(True) else Parser.parser.programParser(ttext)))
    }).groupBy(_._1).map({ case (k, v) => k -> v.map(_._2) })

    val subgraphIds = subGraphs.elements.map(_.asJsObject).map(s => s.fields("id").convertTo[String])
    val modes = vertices.elements.map(_.asJsObject).filter(v => !subgraphIds.contains(v.fields("id").convertTo[String]))

    val (odes, init) = modes.map(m => {
      val mid = m.fields("id").convertTo[String]
      val prg = m.fields("text").convertTo[String].trim match {
        case "" => Test(True)
        case s => Parser.parser.programParser("{" + s + "}")
      }
      (mid, prg, transitionsByVertex.getOrElse(mid, List.empty))
    }).toList.
      //@note ignore subgraphs and other nodes without ODEs
      filter({ case (_, prg, _) => !StaticSemantics.freeVars(prg).isInfinite }).
      partition(_._2.isInstanceOf[ODESystem])

    if (init.length <= 1) {
      val initPrg = init.headOption.flatMap({ case (n, prg, _) =>
        val initTransitions = transitionsByVertex(n).flatMap({
          case (d, Test(True)) =>
            if (odes.exists(_._1 == d)) Some(Test(Equal(mode, modeOf(d))))
            else None
          case (d, tp) =>
            if (odes.exists(_._1 == d)) Some(Compose(Test(Equal(mode, modeOf(d))), tp))
            else Some(tp)
        }).reduceRightOption(Choice)
        prg match {
          case Test(True) => initTransitions
          case _ => Some(initTransitions.map(Compose(prg, _)).getOrElse(prg))
        }
      })
      val c: SwitchedSystem = switchingKind match {
        case "autonomous" => StateDependent(odes.map({ case (_, o: ODESystem, _) => o }))
        case "timed" =>
          if (init.nonEmpty) {
            throw new IllegalArgumentException("Initialization not supported in timed switching template")
          } else {
            val time = subgraphIds.find(_.startsWith("Timed")).flatMap(_.split(":").toList match {
              case _ :: t :: Nil => Some(t)
              case _ => None
            }).getOrElse("t_").asVariable

            val modes = odes.map({ case (n, ODESystem(ode, q), transitions) =>
              val tBound = q match {
                case True => None
                case LessEqual(l, r) if l == time => Some(r)
                case _ => throw new IllegalArgumentException("Only time guards of the shape " + time + "<=T allowed as evolution domain constraints in timed switching template")
              }
              val boundedTransitions = transitions.map({
                case (d, Test(True)) => (d, None)
                case (d, Test(GreaterEqual(l, r))) if l == time => (d, Some(r))
                case (_, _) => throw new IllegalArgumentException("Only time guards of the shape " + time + ">=T allowed on transitions in timed switching template")
              })
              (n, ode, tBound, boundedTransitions)
            })

            Timed(modes, "mode".asVariable, time)
          }
        case "guarded" =>
          if (init.nonEmpty) {
            throw new IllegalArgumentException("Initialization not supported in guarded switching template")
          } else {
            val modes = odes.map({ case (n, o: ODESystem, transitions) =>
              val guardedTransitions = transitions.map({
                case (d, Test(p)) => (d, p)
                case (_, _) => throw new IllegalArgumentException("Only tests allowed on transitions in guarded mode")
              })
              (n, o, guardedTransitions)
            })
            Guarded(modes, "mode".asVariable)
          }
        case "controlled" => Controlled(initPrg, odes.map({ case (n, o: ODESystem, t) => (n, o, t) }), mode)
      }
      List(new GetControlledStabilityTemplateResponse(code, c, specKind))
    } else {
      List(new ErrorResponse("At most 1 initialization node expected, but got nodes " + init.map(_._1).mkString(",")))
    }
  }

  private def flattenAssignments(prg: Program): List[Assign] = prg match {
    case a: Assign => List(a)
    case Compose(a, b) => flattenAssignments(a) ++ flattenAssignments(b)
    case _ => throw new IllegalArgumentException("Unsupported program in hybrid automaton guard; expected guard of the shape ?Q;x_0:=e_0;x_1:=e_1;...;x_n:=e_n;, but got " + prg.prettyString)
  }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Models
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

class UpdateModelRequest(db: DBAbstraction, userId: String, modelId: String, name: String, title: String,
                         description: String, content: String)
  extends UserRequest(userId, _ => true) with WriteRequest {
  private def emptyToOption(s: String): Option[String] = if (s.isEmpty) None else Some(s)

  def resultingResponses(): List[Response] = {
    val modelInfo = db.getModel(modelId)
    if (db.getProofsForModel(modelId).forall(_.stepCount == 0)) {
      if (ArchiveParser.isExercise(content)) {
        db.updateModel(modelId.toInt, name, emptyToOption(title), emptyToOption(description), emptyToOption(content), None)
        ModelUpdateResponse(modelId, name, content, emptyToOption(title), emptyToOption(description), None) :: Nil
      } else try {
        ArchiveParser.parse(content) match {
          case e :: Nil =>
            db.updateModel(modelId.toInt, e.name, e.info.get("Title"), e.info.get("Description"),
              emptyToOption(e.fileContent), e.tactics.headOption.map(_._2))
            ModelUpdateResponse(modelId, e.name, e.problemContent, e.info.get("Title"), e.info.get("Description"), None) :: Nil
          case e => new ErrorResponse("Expected a single entry, but got " + e.size) :: Nil
        }
      } catch {
        case e: ParseException =>
          val nameFinder = """(?:Theorem|Lemma|ArchiveEntry|Exercise)\s*"([^"]*)"""".r("name")
          val entryName = nameFinder.findFirstMatchIn(content).map(_.group("name")).getOrElse("<anonymous>")
          db.updateModel(modelId.toInt, entryName, emptyToOption(modelInfo.title), emptyToOption(modelInfo.description),
            emptyToOption(content), modelInfo.tactic)
          ModelUpdateResponse(modelId, entryName, content, emptyToOption(modelInfo.title),
            emptyToOption(modelInfo.description), Some(e.msg)) :: Nil
      }
    } else new ErrorResponse("Unable to update model " + modelId + " because it has " + modelInfo.numAllProofSteps + " proof steps") :: Nil
  }
}

class UploadArchiveRequest(db: DBAbstraction, userId: String, archiveText: String, modelName: Option[String])
  extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponses(): List[Response] = {
    try {
      val parsedArchiveEntries = ArchiveParser.parse(archiveText)

      //@note archive parser augments a plain formula with definitions and flags it with name '<undefined>'
      val archiveEntries =
        if (parsedArchiveEntries.size == 1 && parsedArchiveEntries.head.name == "<undefined>") {
          parsedArchiveEntries.head.copy(name = modelName.getOrElse("undefined")) :: Nil
        } else parsedArchiveEntries

      val (failedModels, succeededModels) = archiveEntries.foldLeft((List[String](), List[(String, Int)]()))({ case ((failedImports, succeededImports), entry) =>
        val result = DatabasePopulator.importModel(db, userId, prove=false)(DatabasePopulator.toTutorialEntry(entry))
        (failedImports ++ result.right.toSeq, succeededImports ++ result.left.toSeq)
      })
      if (failedModels.isEmpty) {
        if (archiveEntries.size == 1) {
          ModelUploadResponse(Some(succeededModels.head._2.toString), None) :: Nil
        } else BooleanResponse(flag = true) :: Nil
      } else throw new Exception("Failed to import the following models\n" + failedModels.mkString("\n") +
        "\nSucceeded importing:\n" + succeededModels.mkString("\n") +
        "\nModel import may have failed because of model name clashed. Try renaming the failed models in the archive to names that do not yet exist in your model list.")
    } catch {
      //@todo adapt parse error positions (are relative to problem inside entry)
      case e: ParseException =>
        val nameFinder = """(?:Theorem|Lemma|ArchiveEntry|Exercise)\s*"([^"]*)"""".r("name")
        val entryName = nameFinder.findFirstMatchIn(archiveText).map(_.group("name")).getOrElse("<anonymous>")
        val entry = TutorialEntry(entryName, archiveText, None, None, None, List.empty)
        DatabasePopulator.importModel(db, userId, prove=false)(entry) match {
          case Left((_, id)) => ModelUploadResponse(Some(id.toString), Some(e.getMessage)) :: Nil
          case _ => ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
        }
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

class DeleteAllModelsRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with WriteRequest {
  override def resultingResponses(): List[Response] = {
    val allModels = db.getModelList(userId).map(_.modelId)
    allModels.foreach(db.deleteModel)
    BooleanResponse(flag = true) :: Nil
  }
}

class DeleteModelProofStepsRequest(db: DBAbstraction, userId: String, modelId: String) extends UserModelRequest(db, userId, modelId) with WriteRequest {
  override def doResultingResponses(): List[Response] = {
    val modelProofs = db.getProofsForModel(modelId)
    val deleted = modelProofs.map(p => (p.stepCount, db.deleteProofSteps(p.proofId)))
    BooleanResponse(deleted.forall({ case (hadSteps, deletedSteps) => hadSteps == deletedSteps })) :: Nil
  }
}

class DeleteProofRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    //TaskManagement.forceDeleteTask(proofId)
    val success = db.deleteProof(Integer.parseInt(proofId))
    BooleanResponse(success) :: Nil
  }
}

class GetModelListRequest(db: DBAbstraction, userId: String, folder: Option[String]) extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponses(): List[Response] = {
    //@todo folders in DB
    val allModels = db.getModelList(userId).filterNot(_.temporary)
    val models = folder match {
      case None => allModels
      case Some(f) => allModels.filter(_.name.startsWith(f + "/")).map(m => m.copy(name = m.name.stripPrefix(f + "/")))
    }
    new ModelListResponse(models) :: Nil
  }
}

class GetModelRequest(db: DBAbstraction, userId: String, modelId: String)
  extends UserRequest(userId, (id: String) => db.getModel(modelId).userId == id) with ReadRequest {
  def resultingResponses(): List[Response] = new GetModelResponse(db.getModel(modelId)) :: Nil
}

class GetModelTacticRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponses(): List[Response] = new GetModelTacticResponse(db.getModel(modelId)) :: Nil
}

class AddModelTacticRequest(db: DBAbstraction, userId: String, modelId: String, tactic: String) extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponses(): List[Response] = {
    val tacticId = db.addModelTactic(modelId, tactic)
    BooleanResponse(tacticId.isDefined) :: Nil
  }
}

class ModelPlexRequest(db: DBAbstraction, userId: String, modelId: String, artifact: String, monitorKind: String,
                       monitorShape: String, conditionKind: String,
                       additionalVars: List[String]) extends UserRequest(userId, _ => true) with RegisteredOnlyRequest {
  def resultingResponses(): List[Response]  = {
    val model = db.getModel(modelId)
    val modelFml = ModelPlex.normalizeInputFormula(ArchiveParser.parseAsExpandedFormula(model.keyFile))
    val vars: Set[BaseVariable] = (StaticSemantics.boundVars(modelFml).symbols ++ additionalVars.map(_.asVariable)).
      filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])

    artifact match {
      case "controller" => createController(model, modelFml, vars)
      case "monitor" => createMonitor(model, modelFml, vars)
      case "sandbox" => createSandbox(model, modelFml, vars)
    }
  }

  private def extractController(prg: Program): Program = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = prg match {
        case ODESystem(_, q) => Right(Test(q))
        case _ => Left(None)
      }
    }, prg).get
  }

  private def createController(model: ModelPOJO, modelFml: Formula, vars: Set[BaseVariable]): List[Response] = modelFml match {
    case Imply(init, Box(prg, _)) => conditionKind match {
      case "dL" => new ModelPlexArtifactResponse(model, extractController(prg)) :: Nil
      case "C" =>
        val controller = (new CGenerator(new CControllerGenerator(model.defs), init, model.defs))(prg, vars, CodeGenerator.getInputs(prg))
        val code =
          s"""${controller._1}
           |${controller._2}
           |
           |int main() {
           |  /* control loop stub */
           |  parameters params; /* set system parameters, e.g., = { .A=1.0 }; */
           |  while (true) {
           |    state current; /* read sensor values, e.g., = { .x=0.0 }; */
           |    state input;   /* resolve non-deterministic assignments, e.g., = { .x=0.5 }; */
           |    state post = ctrlStep(current, params, input);
           |    /* hand post actuator set values to actuators */
           |  }
           |  return 0;
           |}
           |""".stripMargin

        new ModelPlexCCodeResponse(model, code) :: Nil
      case c => new ErrorResponse("Unknown output format '" + c + "'; please use one of ['dL'|'C']") :: Nil
    }
    case _ => new ErrorResponse("Unsupported shape, expected assumptions -> [{ctrl;ode}*]safe, but got " + modelFml.prettyString) :: Nil
  }

  private def createSandbox(model: ModelPOJO, modelFml: Formula, stateVars: Set[BaseVariable]): List[Response] = modelFml match {
    case Imply(init, Box(prg, _)) =>
      createMonitorCondition(modelFml, stateVars, ListMap.empty) match {
        case Left((monitorConjecture, monitorCond, _)) =>
          def fresh(v: Variable, postfix: String): Variable = BaseVariable(v.name + postfix, v.index, v.sort)

          val fallback = extractController(prg)
          conditionKind match {
            case "dL" =>
              val ctrlVars = StaticSemantics.boundVars(fallback).toSet
              val ctrl = ctrlVars.map(v => AssignAny(fresh(v, "post"))).reduceRightOption(Compose).getOrElse(Test(True))
              val sandbox = Compose(ctrl, Choice(Test(monitorCond), Compose(Test(Not(monitorCond)), fallback)))
              new ModelPlexSandboxResponse(model, monitorConjecture, sandbox) :: Nil
            case "C" =>
              val ctrlInputs = CodeGenerator.getInputs(monitorCond)
              val ctrlMonitorCode = (new CGenerator(new CMonitorGenerator('resist, model.defs), init, model.defs))(monitorCond, stateVars, ctrlInputs, "Monitor")
              val inputs = CodeGenerator.getInputs(prg)
              val fallbackCode = new CControllerGenerator(model.defs)(prg, stateVars, inputs)
              val declarations = ctrlMonitorCode._1.trim
              val monitorCode = ctrlMonitorCode._2.trim

              val sandbox =
                s"""$declarations
                   |${fallbackCode._1}
                   |${fallbackCode._2}
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

              new ModelPlexCCodeResponse(model, sandbox) :: Nil
            case c => new ErrorResponse("Unknown output format '" + c + "'; please use one of ['dL'|'C']") :: Nil
          }
        case Right(e) => e :: Nil
      }
    case _ => new ErrorResponse("Unsupported shape, expected assumptions -> [{ctrl;ode}*]safe, but got " + modelFml.prettyString) :: Nil
  }

  /** Synthesizes a ModelPlex monitor formula over variables `vars` from the model `modelFml`.
    * Returns the monitor conjecture together with the synthesized monitor, or an error. */
  private def createMonitorCondition(modelFml: Formula, vars: Set[BaseVariable],
                                     unobservable: ListMap[NamedSymbol, Option[Formula]]): Either[(Formula, Formula, BelleExpr), ErrorResponse] = {
    val ModelPlexConjecture(_, modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(modelFml, vars.toList.sorted[NamedSymbol], unobservable)

    val mx = ModelPlex.mxSynthesize(monitorKind) &
      //@todo unobservable symbols tactic argument not yet serializable
      //ModelPlex.mxAutoInstantiate(assumptions, unobservable.keySet.toList, Some(ModelPlex.mxSimplify)) &
      ModelPlex.mxAutoInstantiate(assumptions) &
      ModelPlex.mxFormatShape(monitorShape)

    val monitorCond = try {
      TactixLibrary.proveBy(modelplexInput, mx)
    } catch {
      case ex: TacticInapplicableFailure =>
        return Right(new ErrorResponse("Unable to synthesize monitor (missing feature), because \n" + ex.getMessage))
      case ex: TacticAssertionError =>
        return Right(new ErrorResponse("ModelPlex failed: expected unique result, but \n" + ex.getMessage))
    }

    Left(modelplexInput, monitorCond.subgoals.head.succ.head, mx)
  }

  private def createMonitor(model: ModelPOJO, modelFml: Formula, vars: Set[BaseVariable]): List[Response] = {
    val Imply(init, Box(prg, _)) = modelFml
    createMonitorCondition(modelFml, vars, ListMap.empty) match {
      case Left((modelplexConjecture, monitorFml, synthesizeTactic)) =>
        conditionKind match {
          case "dL" =>
            val monitorProof = TactixLibrary.implyR(1) & synthesizeTactic &
              TactixLibrary.prop & DebuggingTactics.done("Monitor proof")
            val mxProof = TactixLibrary.proveBy(Imply(monitorFml, modelplexConjecture), monitorProof)
            val entry = ParsedArchiveEntry(model.name + " ModelPlex Monitor", "theorem",
              "",
              mxProof.conclusion.succ.head.prettyString, Declaration(Map.empty),
              mxProof.conclusion.succ.head,
              ("ModelPlex Monitor Proof", BellePrettyPrinter(monitorProof), monitorProof) :: Nil,
              Nil, Map.empty)
            new ModelPlexMonitorResponse(model, monitorFml, new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))(entry)) :: Nil
          case "C" =>
            val inputs = CodeGenerator.getInputs(prg)
            val monitor = (new CGenerator(new CMonitorGenerator('resist, model.defs), init, model.defs))(monitorFml, vars, inputs, model.name)
            val code =
              s"""${monitor._1}
                 |${monitor._2}
                 |
                 |int main() {
                 |  /* sandbox stub, select 'sandbox' to auto-generate */
                 |  parameters params; /* set parameter values, e.g., = { .A=1.0 }; */
                 |  while (true) {
                 |    state pre; /* read sensor values, e.g., = { .x=0.0 }; */
                 |    state post; /* run controller */
                 |    if (!monitorSatisfied(pre,post,params)) post = post; /* replace with fallback control output */
                 |    /* hand post actuator set values to actuators */
                 |  }
                 |  return 0;
                 |}
                 |""".stripMargin

            new ModelPlexCCodeResponse(model, code) :: Nil
          case "Python" =>
            val inputs = CodeGenerator.getInputs(prg)
            val monitor = (new PythonGenerator(new PythonMonitorGenerator('min, model.defs), init, model.defs))(monitorFml, vars, inputs, model.name)
            val code =
              s"""${monitor._1}
                 |${monitor._2}""".stripMargin

            new ModelPlexCCodeResponse(model, code) :: Nil
        }
      case Right(e) => e :: Nil
    }
  }
}

class TestSynthesisRequest(db: DBAbstraction, userId: String, modelId: String, monitorKind: String,
                           testKinds: Map[String, Boolean], amount: Int, timeout: Option[Int])
  extends UserRequest(userId, _ => true) with RegisteredOnlyRequest {
  def resultingResponses(): List[Response]  = {
    logger.debug("Got Test Synthesis Request")
    val model = db.getModel(modelId)
    val modelFml = ArchiveParser.parseAsFormula(model.keyFile)
    val vars = StaticSemantics.boundVars(modelFml).symbols.filter(_.isInstanceOf[BaseVariable]).toList
    val unobservable = ListMap.empty[NamedSymbol, Option[Formula]]
    val ModelPlexConjecture(_, modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(modelFml, vars, unobservable)
    val monitorCond = (monitorKind, ToolProvider.simplifierTool()) match {
      case ("controller", tool) =>
        val foResult = TactixLibrary.proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
        try {
          TactixLibrary.proveBy(foResult.subgoals.head,
            ModelPlex.optimizationOneWithSearch(tool, assumptions, unobservable.keySet.toList, Some(ModelPlex.mxSimplify))(1))
        } catch {
          case _: Throwable => foResult
        }
      case ("model", tool) => TactixLibrary.proveBy(modelplexInput,
        ModelPlex.modelMonitorByChase(1) &
        SimplifierV3.simpTac(Nil, SimplifierV3.defaultFaxs, SimplifierV3.arithBaseIndex)(1) &
        ModelPlex.optimizationOneWithSearch(tool, assumptions, unobservable.keySet.toList, Some(ModelPlex.mxSimplify))(1)
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

class CreateProofRequest(db: DBAbstraction, userId: String, modelId: String, name: String, description: String)
  extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponses(): List[Response] = {
    if (modelId != "undefined") {
      val proofName = if (name.isEmpty) db.getModel(modelId).name + ": Proof" else name
      val proofId = db.createProofForModel(modelId, proofName, description, currentDate(), None)
      CreatedIdResponse(proofId) :: Nil
    } else {
      new ErrorResponse("Unable to create proof for unknown model") :: Nil
    }
  }
}

class OpenOrCreateLemmaProofRequest(db: DBAbstraction, userId: String, lemmaName: String,
                                    parentProofId: String, parentTaskId: String)
  extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponses(): List[Response] = {
    val modelId: Int = db.getModelList(userId).find(_.name == lemmaName) match {
      case Some(model) => model.modelId
      case None =>
        val tree: ProofTree = DbProofTree(db, parentProofId)
        tree.locate(parentTaskId) match {
          case None => return new ErrorResponse("Unknown node " + parentTaskId + " in proof " + parentProofId) :: Nil
          case Some(node) if node.goal.isEmpty => return new ErrorResponse("Node " + parentTaskId + " does not have a goal") :: Nil
          case Some(node) if node.goal.isDefined =>
            val goal = node.goal.get.toFormula
            val proofSession = session(parentProofId).asInstanceOf[ProofSession]
            val symbols = StaticSemantics.symbols(goal)
            val defs = proofSession.defs.decls.filter({
              case (Name(n, i), _) => symbols.exists(s => s.name == n && s.index == i)
            })
            val lemma = ParsedArchiveEntry(lemmaName, "lemma", "", "", Declaration(defs), goal, Nil, Nil, Map.empty)
            val fileContents = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))(lemma)

            db.createModel(userId, lemmaName, fileContents, currentDate(), None, None, None).get
        }
    }
    val modelProofs = db.getProofsForModel(modelId)
    val proofId = modelProofs.find(_.closed) match {
      case Some(proof) => proof.proofId
      case None => modelProofs match {
        case head :: _ => head.proofId
        case Nil => db.createProofForModel(modelId, "Proof of " + lemmaName, "", currentDate(), None)
      }
    }
    CreatedIdResponse(proofId.toString) :: Nil
  }
}

class CreateModelTacticProofRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponses(): List[Response] = {
    val model = db.getModel(modelId)
    model.tactic match {
      case Some(tacticText) =>
        val proofId = db.createProofForModel(Integer.parseInt(modelId), model.name + " from tactic",
          "Proof from tactic", currentDate(), Some(tacticText))
        CreatedIdResponse(proofId.toString) :: Nil
      case None => new ErrorResponse("Model " + modelId + " does not have a tactic associated")::Nil
    }
  }
}

class ProofsForModelRequest(db: DBAbstraction, userId: String, modelId: String)
  extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponses(): List[Response] = {
    val proofs = db.getProofsForModel(modelId).map(proof =>
      (proof, "loaded"/*KeYmaeraInterface.getTaskLoadStatus(proof.proofId.toString).toString.toLowerCase*/))
    new ProofListResponse(proofs) :: Nil
  }
}

class GetProofLemmasRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    def collectLemmaNames(tactic: String): List[String] = {
      """useLemma(?:At)?\("([^"]+)"""".r("lemmaName").findAllMatchIn(tactic).toList.map(m => m.group("lemmaName"))
    }

    /** Recursively required lemmas in the order they ought to be proved. */
    def recCollectRequiredLemmaNames(proofId: Int, collectedLemmas: List[(String, Int)]): List[(String, Int)] = {
      val proofInfo = db.getProofInfo(proofId)
      val lemmaNames = (proofInfo.tactic.map(collectLemmaNames).getOrElse(Nil).toSet -- collectedLemmas.map(_._1).toSet).toList
      val models = db.getModelList(userId).filter(m => lemmaNames.contains(m.name))
      val lemmaProofs: List[(ModelPOJO, ProofPOJO)] = models.flatMap(m => {
        val proofs = db.getProofsForModel(m.modelId)
        proofs.find(_.tactic.isDefined) match {
          case None => proofs.headOption.map(m -> _)
          case p => p.map(m -> _)
        }
      })
      //@note check non-existent or outdated lemmas
      val unprovedLemmas = lemmaProofs.filter(e => LemmaDBFactory.lemmaDB.get("user" + File.separator + e._1.name) match {
        case Some(l) => l.fact.conclusion == Sequent(IndexedSeq(), IndexedSeq(ArchiveParser.parser(e._1.keyFile).head.model.asInstanceOf[Formula]))
        case None => true
      })
      (unprovedLemmas.foldRight(collectedLemmas)({ case ((m, p), cl) => recCollectRequiredLemmaNames(p.proofId, cl) ++ cl }) ++
        unprovedLemmas.map({ case (m, p) => (m.name, p.proofId) })).distinct
    }

    val lemmaNames = recCollectRequiredLemmaNames(proofId.toInt, Nil)
    ProofLemmasResponse(lemmaNames) :: Nil
  }
}

class OpenProofRequest(db: DBAbstraction, userId: String, proofId: String, wait: Boolean = false) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val proofInfo = db.getProofInfo(proofId)
    val modelId = proofInfo.modelId
    if (modelId.isEmpty) throw new Exception("Database consistency error: unable to open proof " + proofId + ", because it does not refer to a model")
    else if (db.getModel(modelId.get).userId != userId) new PossibleAttackResponse("Permission denied")::Nil
    else {
      insist(db.getModel(proofInfo.modelId.getOrElse(throw new CoreException(s"Cannot open a proof without model, proofId=$proofId"))).userId == userId, s"User $userId does not own the model associated with proof $proofId")

      proofInfo.modelId match {
        case None => new ErrorResponse("Unable to open proof " + proofId + ", because it does not refer to a model")::Nil // duplicate check to above
        case Some(mId) =>
          var products: Map[Expression, Seq[GenProduct]] = Map[Expression, Seq[GenProduct]]()
          Parser.parser.setAnnotationListener((p: Program, inv: Formula) =>
            products += (p -> (products.getOrElse(p, Nil) :+ (inv, None))))
          val problem = ArchiveParser.parseProblem(db.getModel(mId).keyFile)
          //@note add unexpanded (but elaborated) form, and fully expanded form to generator; generator itself also uses unification
          val generator = ConfigurableGenerator.create(products, problem.defs)
          session += proofId -> ProofSession(proofId, TactixLibrary.invGenerator, generator, problem.defs)
          TactixInit.invSupplier = generator
          OpenProofResponse(proofInfo, "loaded" /*TaskManagement.TaskLoadStatus.Loaded.toString.toLowerCase()*/) :: Nil
      }
    }
  }
}

class OpenGuestArchiveRequest(db: DBAbstraction, uri: String, archiveName: String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    try {
      val userId = uri
      val sanitizedUserId = URLEncoder.encode(uri, "UTF-8")
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

/** Gets all tasks of the specified proof. A task is some work the user has to do. It is not a KeYmaera task! */
class GetAgendaAwesomeRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    // reapply lemmas (may have proved in the mean time)
    DbProofTree(db, proofId).openGoals.
      filter(n => n.maker.exists(_.startsWith("useLemma")) && !n.isProved).
      foreach(n => n.parent.map(p => {
        p.pruneBelow()
        p.runTactic(userId, ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), BelleParser(n.maker.get), n.maker.get, wait = true)
      }))

    val tree: ProofTree = DbProofTree(db, proofId)
    val leaves = tree.openGoals
    val closed = tree.openGoals.isEmpty && tree.isProved

    val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList

    // Goals in web UI
    val agendaItems: List[AgendaItem] = leaves.map(n =>
      AgendaItem(n.id.toString, AgendaItem.nameOf(n), proofId))
    // add unexpanded functions, predicates, programs of the open goals of all leaves to the proof session
    val proofSession = session(proofId).asInstanceOf[ProofSession]
    session(proofId) = leaves.flatMap(_.parent).foldLeft(proofSession)(RequestHelper.updateProofSessionDefinitions)
    AgendaAwesomeResponse(tree.info.modelId.get.toString, proofId, tree.root, leaves, agendaItems, closed, marginLeft, marginRight) :: Nil
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
    val agendaItems: List[AgendaItem] = AgendaItem(tree.root.id.toString, AgendaItem.nameOf(tree.root), proofId) :: Nil
    val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
    AgendaAwesomeResponse(tree.info.modelId.get.toString, proofId, tree.root, tree.root::Nil, agendaItems, closed=false, marginLeft, marginRight) :: Nil
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
      case Some(node) =>
        val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
        NodeChildrenResponse(proofId, node, marginLeft, marginRight) :: Nil
    }
  }
}

class ProofTaskNodeRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case Some(node) =>
        val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
        new ProofTaskNodeResponse(node, marginLeft, marginRight)::Nil
      case None => new ErrorResponse("Cannot get parent of node " + nodeId + ", node might be unknown or root")::Nil
    }
  }
}

class ProofTaskParentRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId).flatMap(_.parent) match {
      case Some(parent) =>
        val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
        new ProofTaskNodeResponse(parent, marginLeft, marginRight)::Nil
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
    val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
    new GetPathAllResponse(path.reverse, parentsRemaining, marginLeft, marginRight)::Nil
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
      case Some(n) =>
        val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
        new GetBranchRootResponse(n, marginLeft, marginRight) :: Nil
    }

  }
}

class ProofNodeSequentRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => throw new Exception("Unknown node " + nodeId)
      case Some(node) =>
        val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
        ProofNodeSequentResponse(proofId, node, marginLeft, marginRight) :: Nil
    }
  }
}

class ProofTaskExpandRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, strict: Boolean)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => throw new Exception("Unknown node " + nodeId)
      case Some(node) if node.maker.isEmpty =>
        new ErrorResponse("Unable to expand node " + nodeId + " of proof " + proofId + ", because it did not record a tactic")::Nil
      case Some(node) if node.maker.isDefined =>
        assert(node.maker.isDefined, "Unable to expand node without tactics")
        val (conjecture, parentStep, parentRule) = (ProvableSig.startProof(node.conclusion), node.maker.get, node.makerShortName.get)
        val localProofId = db.createProof(conjecture)
        val proofSession = session(proofId).asInstanceOf[ProofSession]
        //@note add a copy of parent proof session under local proof ID to allow stepping deeper into tactics
        session += localProofId.toString -> proofSession.copy(proofId = localProofId.toString)
        val innerInterpreter = SpoonFeedingInterpreter(localProofId, -1, db.createProof, proofSession.defs,
          RequestHelper.listenerFactory(db, proofSession),
          ExhaustiveSequentialInterpreter(_, throwWithDebugInfo=false), 1, strict=strict, convertPending=false)
        val parentTactic = BelleParser(parentStep)
        innerInterpreter(parentTactic, BelleProvable(conjecture, None, tree.info.defs(db)))
        innerInterpreter.kill()

        val trace = db.getExecutionTrace(localProofId)
        val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
        if (trace.steps.size == 1 && trace.steps.head.rule == parentRule) {
          DerivationInfoRegistry.locate(parentTactic) match {
            case Some(ptInfo) => ExpandTacticResponse(localProofId, Nil, Nil,
              ptInfo.codeName, "", Nil, Nil, marginLeft, marginRight) :: Nil
            case None => new ErrorResponse("No further details available") :: Nil
          }
        } else {
          val innerTree = DbProofTree(db, localProofId.toString).load()
          val (stepDetails, _) = innerTree.tacticString(new VerboseTraceToTacticConverter(innerTree.info.defs(db)))
          val innerSteps = innerTree.nodes
          val agendaItems: List[AgendaItem] = innerTree.openGoals.map(n =>
            AgendaItem(n.id.toString, AgendaItem.nameOf(n), proofId))
          val goals = innerTree.openGoals.map(_.conclusion)
          val backendGoals = innerTree.openGoals.map(n =>
            if (n.conclusion.isFOL) Some(
              (KeYmaeraToMathematica(n.conclusion.toFormula).toString,
               DefaultSMTConverter(n.conclusion.toFormula)))
            else None
          )

          ExpandTacticResponse(localProofId, goals, backendGoals, parentStep, stepDetails, innerSteps,
            agendaItems, marginLeft, marginRight) :: Nil
        }
    }
  }
}

class StepwiseTraceRequest(db: DBAbstraction, userId: String, proofId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val innerSteps = tree.nodes
    val agendaItems: List[AgendaItem] = tree.openGoals.map(n =>
      AgendaItem(n.id.toString, AgendaItem.nameOf(n), proofId))
    //@todo fill in parent step for empty ""
    val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
    ExpandTacticResponse(proofId.toInt, Nil, Nil, "", tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db)))._1, innerSteps, agendaItems, marginLeft, marginRight) :: Nil
  }
}

class GetSequentStepSuggestionRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => ApplicableAxiomsResponse(Nil, Map.empty, topLevel=true) :: Nil
      case Some(node) => node.goal match {
        case None => ApplicableAxiomsResponse(Nil, Map.empty, topLevel=true) :: Nil //@note node closed
        case Some(seq) =>
          if (seq.isFOL) {
            val folSuggestions = "QE"::"abbrv"::"hideL"::Nil
            // todo: counterexample, find assumptions + general help
            val tactics = folSuggestions.map(s => (DerivationInfo(s), None))
            ApplicableAxiomsResponse(tactics, Map.empty, topLevel=true) :: Nil
          } else {
            // find "largest" succedent formula with programs and suggest top-level popup content
            val pos = SuccPosition(1)
            ApplicableAxiomsResponse(node.applicableTacticsAt(pos), node.tacticInputSuggestions(pos), topLevel=true, Some(Fixed(1))) :: Nil
          }
      }
    }
  }
}

class GetApplicableAxiomsRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    if (tree.done) return ApplicableAxiomsResponse(Nil, Map.empty, pos.isTopLevel) :: Nil
    tree.locate(nodeId).map(n => (n.applicableTacticsAt(pos), n.tacticInputSuggestions(pos))) match {
      case Some((tactics, inputs)) => ApplicableAxiomsResponse(tactics, inputs, pos.isTopLevel) :: Nil
      case None => ApplicableAxiomsResponse(Nil, Map.empty, pos.isTopLevel) :: Nil
    }
  }
}

class GetApplicableTwoPosTacticsRequest(db:DBAbstraction, userId: String, proofId: String, nodeId: String,
                                        pos1: Position, pos2: Position)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    if (tree.done) return ApplicableAxiomsResponse(Nil, Map.empty, topLevel=true) :: Nil
    tree.locate(nodeId).map(n => n.applicableTacticsAt(pos1, Some(pos2))) match {
      case None => ApplicableAxiomsResponse(Nil, Map.empty, topLevel=true) :: Nil
      case Some(tactics) => ApplicableAxiomsResponse(tactics, Map.empty, pos1.isTopLevel) :: Nil
    }
  }
}

class GetDerivationInfoRequest(db: DBAbstraction, userId: String, proofId: String, axiomId: Option[String])
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val infos = axiomId match {
      case Some(aid) =>
        val di = Try(DerivationInfo.ofCodeName(aid)).toOption
        di.map(info => (info, UIIndex.comfortOf(aid))).toList
      case None => DerivationInfo.allInfo.
        map({case (_, di) => (di, UIIndex.comfortOf(di.codeName))}).toList
    }
    ApplicableAxiomsResponse(infos, Map.empty, topLevel=true) :: Nil
  }
}

/** Gets the definitions that can be expanded at node `nodeId`. */
class GetApplicableDefinitionsRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    if (tree.done) return ApplicableDefinitionsResponse(Nil) :: Nil
    val proofSession = session(proofId).asInstanceOf[ProofSession]
    tree.locate(nodeId).map(n => n.goal.map(StaticSemantics.symbols).getOrElse(Set.empty)) match {
      case Some(symbols) =>
        val applicable: Map[NamedSymbol, Signature] = symbols.
          filter({ case _: Function => true case _: ProgramConst => true case _: SystemConst => true case _ => false }).
          flatMap(s => proofSession.defs.find(s.name, s.index).map(s -> _)).toMap
        /** Translates the list of parsed argument names `args` into a function argument (Pair). */
        def asPairs(args: Option[List[(Name, Sort)]]): Term = args.map({
          case Nil => Nothing
          case (Name(n, i), _) :: Nil =>
            if (n == Nothing.name) Nothing
            else Variable(n, i)
          case (n, _) :: ns => Pair(Variable(n.name, n.index), asPairs(Some(ns)))
        }).getOrElse(Nothing)
        /** Replaces `.` in expression `repl` with the corresponding argument name from `args`. */
        def withArgs(repl: Option[Expression], args: Option[List[(Name, Sort)]]): Option[Expression] = args match {
          case None => repl
          case Some(a) =>
            //@note can be optimized to just a single traversal if we are sure that . and ._0 do not co-occur and ._i is
            //      a contiguous range
            def argsMap(dots: List[NamedSymbol], i: Int): Map[NamedSymbol, Name] = dots match {
              case Nil => Map.empty
              case dot :: Nil => Map(dot -> a(i)._1)
              case dot :: dots => Map(dot -> a(i)._1) ++ argsMap(dots, i+1)
            }
            val dots = argsMap(repl.map(StaticSemantics.symbols).getOrElse(Set.empty).
              filter({ case _: DotTerm => true case _ => false }).toList.
              sortBy({ case DotTerm(_, None) => -1 case DotTerm(_, Some(i)) => i }), 0)
            repl.flatMap(ExpressionTraversal.traverseExpr(new ExpressionTraversalFunction() {
              override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
                case s: DotTerm =>
                  val n = dots(s)
                  Right(Variable(n.name, n.index))
                case _ => Left(None)
              }
            }, _))
        }
        val expansions: List[(NamedSymbol, Expression, Option[Expression], Boolean)] = applicable.toList.map({
          case (s: Function, Signature(_, sort, args, repl, loc)) => sort match {
            case Real => (s, FuncOf(s, asPairs(args)), withArgs(repl, args), loc == UnknownLocation)
            case Bool => (s, PredOf(s, asPairs(args)), withArgs(repl, args), loc == UnknownLocation)
          }
          case (s: ProgramConst, Signature(_, _, _, repl, loc)) => (s, s, repl, loc == UnknownLocation)
          case (s: SystemConst, Signature(_, _, _, repl, loc)) => (s, s, repl, loc == UnknownLocation)
        }).filter(e => e._4 || e._3.isDefined)
        ApplicableDefinitionsResponse(expansions.sortBy(_._1)) :: Nil
      case None => ApplicableDefinitionsResponse(Nil) :: Nil
    }
  }
}

class SetDefinitionsRequest(db: DBAbstraction, userId: String, proofId: String, what: String, repl: String)
  extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    val proofSession = session(proofId).asInstanceOf[ProofSession]
    Try(what.asExpr).toEither match {
      case Left(ex) => BooleanResponse(flag = false, Some("Unable to parse 'what': " + ex.getMessage)) :: Nil
      case Right(e) =>
        val ewhat = elaborate(e, proofSession.defs.asNamedSymbols)

        Try(repl.asExpr).toEither match {
          case Left(ex) => BooleanResponse(flag = false, Some("Unable to parse 'repl': " + ex.getMessage)) :: Nil
          case Right(r) =>
            val erepl = elaborate(r, proofSession.defs.asNamedSymbols)
            if (erepl.sort == ewhat.sort) {
              val fnwhat: Function = ewhat match {
                case FuncOf(fn: Function, _) => fn
                case PredOf(fn: Function, _) => fn
                case c: ProgramConst => Function(c.name, c.index, Unit, Trafo)
                case c: SystemConst => Function(c.name, c.index, Unit, Trafo)
              }
              val name = Name(fnwhat.name, fnwhat.index)
              proofSession.defs.decls.get(name) match {
                case None =>
                  session(proofId) = proofSession.copy(defs = proofSession.defs.copy(decls = proofSession.defs.decls +
                    (Name(fnwhat.name, fnwhat.index) -> Signature(Some(fnwhat.domain), fnwhat.sort, None, Some(erepl), UnknownLocation))))
                  BooleanResponse(flag = true) :: Nil
                case Some(Signature(_, _, args, None, _)) =>
                  session(proofId) = proofSession.copy(defs = proofSession.defs.copy(decls = proofSession.defs.decls +
                    (Name(fnwhat.name, fnwhat.index) -> Signature(Some(fnwhat.domain), fnwhat.sort, args, Some(erepl), UnknownLocation))))
                  BooleanResponse(flag = true) :: Nil
                case Some(Signature(_, _, _, Some(i), _)) =>
                  new ErrorResponse("Cannot change " + fnwhat.prettyString + ", it is already defined as " + i.prettyString) :: Nil
              }

            } else BooleanResponse(flag = false, Some("Expected a replacement of sort " + ewhat.sort + ", but got " + erepl.sort)) :: Nil
        }
    }
  }

  private def elaborate(e: Expression, elaboratables: List[NamedSymbol]): Expression = {
    def elaborateTo(fn: Function, c: Term, to: (Function, Term) => Expression): Expression = {
      elaboratables.find(ns => ns.name == fn.name && ns.index == fn.index) match {
        case Some(ns: Function) =>
          if (ns.domain == fn.domain && ns.sort != fn.sort) to(ns, c)
          else e
        case None => e
      }
    }
    e match {
      case FuncOf(fn: Function, c) => elaborateTo(fn, c, PredOf)
      case PredOf(fn: Function, c) => elaborateTo(fn, c, FuncOf)
      case _ => e
    }
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
        new KvpResponse("sequent", "Sequent: \n" + goal.toString + "\n\nFormula: \n" + goal.toFormula.prettyString + "\n\nProvable: \n" + provable.prettyString + "\n\nLemma:\n" + lemma.toString) :: Nil
    }
  }
}

case class BelleTermInput(value: String, spec:Option[ArgInfo])

class GetStepRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId).flatMap(_.goal) match {
      case None => ApplicableAxiomsResponse(Nil, Map.empty, pos.isTopLevel) :: Nil
      case Some(goal) =>
        goal.sub(pos) match {
          case Some(fml: Formula) =>
            val substs = session(proofId) match {
              case ps: ProofSession => ps.defs.substs
              case _ => Nil
            }
            UIIndex.theStepAt(fml, Some(pos), None, substs) match {
              case Some(step) => ApplicableAxiomsResponse((step, None) :: Nil, Map.empty, pos.isTopLevel) :: Nil
              case None => ApplicableAxiomsResponse(Nil, Map.empty, pos.isTopLevel) :: Nil
            }
          case _ => ApplicableAxiomsResponse(Nil, Map.empty, pos.isTopLevel) :: Nil
        }
    }
  }
}

class GetLemmasRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position,
                        partialLemmaName: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val infos = ProvableInfo.allInfo.filter({case (name, i) =>
      (i.isInstanceOf[CoreAxiomInfo] || i.isInstanceOf[DerivedAxiomInfo]) && i.canonicalName.contains(partialLemmaName)})
        .toList.map(_._2)
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

  /** Basic input sanity checks w.r.t. symbols in `sequent`. */
  private def checkInput(sequent: Sequent, input: BelleTermInput, defs: Declaration): Response = {
    try {
      input match {
        case BelleTermInput(value, Some(arg: FormulaArg)) =>
          checkExpressionInput(arg, value.asExpr :: Nil, sequent, defs)
        case BelleTermInput(value, Some(arg: ExpressionArgBase)) =>
          checkExpressionInput(arg, value.asExpr :: Nil, sequent, defs)
        case BelleTermInput(value, Some(arg: SubstitutionArg)) =>
          checkSubstitutionInput(arg, value.asSubstitutionPair :: Nil, sequent, defs)
        case BelleTermInput(value, Some(OptionArg(arg))) if !arg.isInstanceOf[SubstitutionArg] =>
          checkExpressionInput(arg, value.asExpr :: Nil, sequent, defs)
        case BelleTermInput(value, Some(OptionArg(arg))) if  arg.isInstanceOf[SubstitutionArg] =>
          checkSubstitutionInput(arg, value.asSubstitutionPair :: Nil, sequent, defs)
        case BelleTermInput(value, Some(arg@ListArg(ai: FormulaArg))) =>
          checkExpressionInput(arg, Parser.parseExpressionList(value), sequent, defs)
      }
    } catch {
      case ex: ParseException => BooleanResponse(flag=false, Some(ex.toString))
    }
  }

  /** Checks expression inputs. */
  private def checkExpressionInput[E <: Expression](arg: ArgInfo, exprs: List[E], sequent: Sequent,
                                                    defs: Declaration) = {

    //@note function/predicate/program symbols are proof parameters if not in input, otherwise look up in definitions
    val elaborated = exprs.map({
      case e@FuncOf(n, a) if !defs.asNamedSymbols.contains(n) => arg match {
        case _: FormulaArg => PredOf(n.copy(sort = Bool), a)
        case _ => e
      }
      case e@PredOf(n, a) if !defs.asNamedSymbols.contains(n) => arg match {
        case _: TermArg => FuncOf(n.copy(sort = Real), a)
        case _ => e
      }
      case a: ProgramConst if FormulaTools.dualFree(sequent) => SystemConst(a.name, a.space)
      case e => defs.elaborateToSystemConsts(defs.elaborateToFunctions(e))
    })

    val sortMismatch: Option[String] = (arg, elaborated) match {
      case (_: FormulaArg, (f: Formula) :: Nil) => DerivationInfoRegistry.convert(arg, List(f)).right.toOption
      case (_: ExpressionArgBase, (e: Expression) :: Nil) => DerivationInfoRegistry.convert(arg, List(e)).right.toOption
      case (ListArg(_: FormulaArg), fmls) if fmls.forall(_.kind == FormulaKind) => None
      case _ => Some("Expected: " + arg.sort + ", found: " + elaborated.map(_.kind).mkString(",") + " " +   elaborated.map(_.prettyString).mkString(","))
    }

    sortMismatch match {
      case None =>
        val symbols = StaticSemantics.symbols(sequent) ++ defs.asNamedSymbols + Function("old", None, Real, Real)
        val paramFV: Set[NamedSymbol] = {
          //@note function/predicate/system/game symbols are proof parameters if they are not declared in the input
          elaborated.flatMap({
            case FuncOf(n, a) if !defs.asNamedSymbols.contains(n) => StaticSemantics.symbols(a)
            case PredOf(n, a) if !defs.asNamedSymbols.contains(n) => StaticSemantics.symbols(a)
            case n: SystemConst if !defs.asNamedSymbols.contains(n) => Set.empty[NamedSymbol]
            case n: ProgramConst if !defs.asNamedSymbols.contains(n) => Set.empty[NamedSymbol]
            case e => StaticSemantics.symbols(e)
          }).toSet
        }

        val (hintFresh, allowedFresh) = arg match {
          case _: VariableArg if arg.allowsFresh.contains(arg.name) => (Nil, Nil)
          case _ => (paramFV -- symbols, arg.allowsFresh) //@todo would need other inputs to check
        }

        if (hintFresh.size > allowedFresh.size) {
          val fnVarMismatch = hintFresh.map(fn => fn -> symbols.find(s => s.name == fn.name && s.index == fn.index)).
            filter(_._2.isDefined)
          if (fnVarMismatch.isEmpty) {
            BooleanResponse(flag = false, Some("argument " + arg.name + " uses new names that do not occur in the sequent: " + hintFresh.mkString(",") +
              (if (allowedFresh.nonEmpty) ", expected new names only as introduced for " + allowedFresh.mkString(",")
              else ", is it a typo?")))
          } else BooleanResponse(flag=true)
        } else {
          BooleanResponse(flag=true)
        }
      case Some(mismatch) => BooleanResponse(flag=false, Some(mismatch))
    }
  }

  /** Checks substitution inputs. */
  private def checkSubstitutionInput(arg: ArgInfo, exprs: List[SubstitutionPair], sequent: Sequent,
                                     defs: Declaration) = {
    //@note parsed as substitution pair is all we check for now
    BooleanResponse(flag=true)
  }

  override protected def doResultingResponses(): List[Response] = {
    val info = DerivationInfo(tacticId)
    val expectedInputs = info.inputs
    val paramInfo = expectedInputs.find(_.name == paramName)
    val isIllFormed = paramInfo.isEmpty || paramValue.isEmpty
    if (!isIllFormed) {
      val input = BelleTermInput(paramValue, paramInfo)

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
      case BelleTermInput(value, Some(_:FormulaArg)) => "\""+value+"\""
      case BelleTermInput(value, Some(_:ExpressionArgBase)) => "\""+value+"\""
      case BelleTermInput(value, Some(_:SubstitutionArg)) => "\""+value+"\""
      /* Tactic parser uses same syntax for formula argument as for singleton formula list argument.
       * if we encounter a singleton list (for example in dC), then present it as a single argument. */
      case BelleTermInput(value, Some(ListArg(_: FormulaArg))) =>
        val values = Parser.parseExpressionList(value).map(_.prettyString)
        if (values.isEmpty) "\"nil\""
        else "\"" + values.mkString("::") + "::nil\""
      case BelleTermInput(value, Some(ListArg(_: VariableArg))) =>
        val values = Parser.parseExpressionList(value).map(_.prettyString)
        if (values.isEmpty) value
        else "\"" + values.mkString("::") + "::nil\""
      case BelleTermInput(value, Some(ListArg(_: TermArg))) =>
        val values = Parser.parseExpressionList(value).map(_.prettyString)
        if (values.isEmpty) value
        else "\"" + values.mkString("::") + "::nil\""
      case BelleTermInput(value, Some(_:StringArg)) => "\""+value.replaceAllLiterally("\"", "\\\"")+"\""
      case BelleTermInput(value, Some(OptionArg(_: ListArg))) =>
        "\"" + Parser.parseExpressionList(value).map(_.prettyString).mkString("::") + "::nil\""
      case BelleTermInput(value, Some(OptionArg(_))) => "\""+value.replaceAllLiterally("\"", "\\\"")+"\""
      case BelleTermInput(value, None) => value
    }
    //@note stepAt(pos) may refer to a search tactic without position (e.g, closeTrue, closeFalse)
    val (specificTerm: String, adaptedPos: Option[PositionLocator], adaptedPos2: Option[PositionLocator]) =
      if (consultAxiomInfo) RequestHelper.getSpecificName(belleTerm, sequent, pos, pos2, session(proofId).asInstanceOf[ProofSession]) match {
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
        case Right(t: BuiltinInfo) => (t.codeName, None, None)
        case Right(t) => (t.codeName, None, None)
      }
      else (belleTerm, pos, pos2)

    if (inputs.isEmpty && adaptedPos.isEmpty) { assert(adaptedPos2.isEmpty, "Undefined pos1, but defined pos2"); specificTerm }
    else if (inputs.isEmpty && adaptedPos.isDefined && adaptedPos2.isEmpty) { specificTerm + "(" + adaptedPos.get.prettyString + ")" }
    else if (inputs.isEmpty && adaptedPos.isDefined && adaptedPos2.isDefined) { specificTerm + "(" + adaptedPos.get.prettyString + "," + adaptedPos2.get.prettyString + ")" }
    else specificTerm + "(" + paramStrings.mkString(",") + ")"
  }

  private class TacticPositionError(val msg:String,val pos: edu.cmu.cs.ls.keymaerax.parser.Location,val inlineMsg: String) extends Exception

  private def backendAvailable: Boolean = Configuration(Configuration.Keys.QE_TOOL) match {
    case "mathematica" => ToolProvider.tool("Mathematica") match {
      case Some(mathematica: Mathematica) => mathematica.getAvailableWorkers > 0
      case None => ToolProvider.qeTool() match {
        case Some(t: ToolOperationManagement) => t.getAvailableWorkers > 0
        case _ => false
      }
      case _ => false
    }
    case "wolframengine" => ToolProvider.tool("WolframEngine") match {
      case Some(mathematica: Mathematica) => mathematica.getAvailableWorkers > 0
      case None => ToolProvider.qeTool() match {
        case Some(t: ToolOperationManagement) => t.getAvailableWorkers > 0
        case _ => false
      }
      case _ => false
    }
    case "wolframscript" => ToolProvider.tool("WolframScript") match {
      case Some(mathematica: Mathematica) => mathematica.getAvailableWorkers > 0
      case None => ToolProvider.qeTool() match {
        case Some(t: ToolOperationManagement) => t.getAvailableWorkers > 0
        case _ => false
      }
      case _ => false
    }
    case "z3" => ToolProvider.tool("Z3") match {
      case Some(z3: Z3) => z3.getAvailableWorkers > 0
      case _ => false
    }
  }

  private def executionInfo(ruleName: String): String = ruleName + ": " + (ruleName match {
    case "solve" | "ODE" =>
      """
        |If it takes too long: provide invariants of the ODE using dC, and prove the invariants with ODE or
        |if necessary one of the specialized ODE proof tactics, such as dI.
      """.stripMargin
    case "QE" =>
      """
        |If it takes too long, try to simplify arithmetic:
        |(1) hide irrelevant assumptions
        |(2) split into multiple goals
        |(3) expand and simplify special functions
        |(4) abbreviate or simplify complicated terms
      """.stripMargin
    case _ => ""
  })

  override protected def doResultingResponses(): List[Response] = {
    if (backendAvailable) {
      val proof = db.getProofInfo(proofId)
      if (proof.closed) new ErrorResponse("Can't execute tactics on a closed proof") :: Nil
      else {
        val tree: ProofTree = DbProofTree(db, proofId)
        tree.locate(nodeId) match {
          case None => new ErrorResponse("Unknown node " + nodeId + " in proof " + proofId) :: Nil
          case Some(node) if node.goal.isEmpty => new ErrorResponse("Node " + nodeId + " does not have a goal") :: Nil
          case Some(node) if node.goal.isDefined =>
            val sequent = node.goal.get

            try {
              val proofSession = session(proofId).asInstanceOf[ProofSession]
              val tacticString = fullExpr(sequent)
              //@note sequential interpreter may change TactixInit.invSupplier:
              // see [[updateProofSessionDefinitions]] for proofSession.invSupplier update when tactic is finished
              TactixInit.invSupplier = proofSession.invSupplier
              // elaborate all variables to function/predicate symbols, but never auto-expand
              val expr = BelleParser.parseWithInvGen(tacticString, Some(proofSession.invGenerator), proofSession.defs, expandAll=false)

              val appliedExpr: BelleExpr = (pos, pos2, expr) match {
                case (None, None, _: AtPosition[BelleExpr]) =>
                  throw new TacticPositionError("Can't run a positional tactic without specifying a position", expr.getLocation, "Expected position in argument list but found none")
                case (None, None, _) => expr
                case (Some(position), None, expr: AtPosition[BelleExpr]) => expr(position)
                case (Some(_), None, expr: BelleExpr) => expr
                case (Some(Fixed(p1, None, _)), Some(Fixed(p2, None, _)), expr: BuiltInTwoPositionTactic) => expr(p1, p2)
                case (Some(_), Some(_), expr: BelleExpr) => expr
                case _ => logger.error("Position error running tactic at pos " + pos.getClass.getName + ", expr " + expr.getClass.getName); throw new ProverException("Match error")
              }

              val ruleName =
                if (consultAxiomInfo) RequestHelper.getSpecificName(belleTerm, sequent, pos, pos2, _ => appliedExpr.prettyString,
                  session(proofId).asInstanceOf[ProofSession])
                else "custom"

              def interpreter(proofId: Int, startNodeId: Int) = new Interpreter {
                private val proofSession = session(proofId.toString).asInstanceOf[ProofSession]
                private val inner = SpoonFeedingInterpreter(proofId, startNodeId, db.createProof, proofSession.defs,
                  RequestHelper.listenerFactory(db, proofSession),
                  ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 0, strict=false, convertPending=true)

                override def apply(expr: BelleExpr, v: BelleValue): BelleValue = try {
                  inner(expr, v)
                } catch {
                  case ex: Throwable => inner.innerProofId match {
                    case Some(innerId) =>
                      //@note display progress of inner (Let) proof, works only in stepwise execution (step details dialog)
                      val innerTrace = db.getExecutionTrace(innerId)
                      if (innerTrace.steps.nonEmpty) BelleSubProof(innerId)
                      else throw new BelleNoProgress("No progress", ex)
                    case None => throw ex
                  }
                }

                override def start(): Unit = inner.start()

                override def kill(): Unit = inner.kill()

                override def isDead: Boolean = inner.isDead

                override def listeners: Seq[IOListener] = inner.listeners
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
                  RunBelleTermResponse(proofId, node.id.toString, taskId, "Executing custom tactic") :: Nil
                } else {
                  val localProvable = ProvableSig.startProof(sequent)
                  val localProofId = db.createProof(localProvable)
                  val executor = BellerophonTacticExecutor.defaultExecutor
                  val taskId = executor.schedule(userId, appliedExpr, BelleProvable(localProvable, node.label.map(_ :: Nil), tree.info.defs(db)), interpreter(localProofId, -1))
                  RunBelleTermResponse(localProofId.toString, "()", taskId, "Executing internal steps of " + executionInfo(belleTerm)) :: Nil
                }
              } else {
                //@note execute clicked single-step tactics on sequential interpreter right away
                val taskId = node.runTactic(userId, ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), appliedExpr, ruleName)
                val info = "Executing " + executionInfo(belleTerm)
                RunBelleTermResponse(proofId, node.id.toString, taskId, info) :: Nil
              }
            } catch {
              case e: ProverException if e.getMessage == "No step possible" => new ErrorResponse("No step possible") :: Nil
              case e: TacticPositionError => new TacticErrorResponse(e.msg, HackyInlineErrorMsgPrinter(belleTerm, e.pos, e.inlineMsg), e) :: Nil
              case e: BelleThrowable => new TacticErrorResponse(e.getMessage, HackyInlineErrorMsgPrinter(belleTerm, UnknownLocation, e.getMessage), e) :: Nil
              case e: ParseException => new TacticErrorResponse(e.getMessage, HackyInlineErrorMsgPrinter(belleTerm, e.loc, e.getMessage), e) :: Nil
            }
        }
      }
    } else {
      new ErrorResponse("Backend tool unavailable or busy. If the tool remains unavailable, please restart KeYmaera X and/or configure a different tool") :: Nil
    }
  }
}

/** Create a proof if it does not exist yet. Read request, so that guest users can check proofs. */
class InitializeProofFromTacticRequest(db: DBAbstraction, userId: String, proofId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val proofInfo = db.getProofInfo(proofId)
    proofInfo.tactic match {
      case None => new ErrorResponse("Proof " + proofId + " does not have a tactic") :: Nil
      case Some(_) if proofInfo.modelId.isEmpty => throw new Exception("Proof " + proofId + " does not refer to a model")
      case Some(t) if proofInfo.modelId.isDefined =>
        val proofSession = session(proofId).asInstanceOf[ProofSession]

        import TacticInfoJsonProtocol._
        val tacticText = try {
          t.parseJson.convertTo[TacticInfo].tacticText
        } catch {
          case _: ParsingException => t //@note backwards compatibility with database tactics not in JSON
        }

        //@note do not auto-expand if tactic contains verbatim expands or "pretty-printed" expands (US)
        val tactic = BelleParser.parseBackwardsCompatible(tacticText, proofSession.defs)

        def atomic(name: String): String = {
          val tree: ProofTree = DbProofTree(db, proofId)
          tree.root.runTactic(userId, ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), tactic, name)
        }

        tactic match {
          case n: NamedBelleExpr => RunBelleTermResponse(proofId, "()", atomic(n.name), "") :: Nil
          case _ =>
            try {
              //@note replace listener created by proof tree (we want a different tactic name for each component of the
              // executed tactic and we want to see progress)
              val interpreter = (_: List[IOListener]) => DatabasePopulator.prepareInterpreter(db, proofId.toInt,
                proofSession.defs, CollectProgressListener() :: Nil)
              val tree: ProofTree = DbProofTree(db, proofId)
              val executor = BellerophonTacticExecutor.defaultExecutor
              val taskId = tree.root.runTactic(userId, interpreter, tactic, "", executor)
              RunBelleTermResponse(proofId, "()", taskId, "") :: Nil
            } catch {
              case _: Throwable =>
                //@note if spoonfeeding interpreter fails, try sequential interpreter so that tactics at least proofcheck
                //      even if browsing then shows a single step only
                RunBelleTermResponse(proofId, "()", atomic("custom"), "") :: Nil
            }
        }
    }
  }
}

class TaskStatusRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    type Progress = (Option[(BelleExpr, Long)], Seq[(BelleExpr, Either[BelleValue, BelleThrowable])])
    val (isDone, progress: Option[Progress]) = executor.synchronized {
      executor.getTask(taskId) match {
        case Some(task) =>
          val progressList = task.interpreter match {
            case SpoonFeedingInterpreter(_, _, _, _, _, interpreterFactory, _, _, _) =>
              //@note the inner interpreters have CollectProgressListeners attached
              interpreterFactory(Nil).listeners.flatMap({
                case l@CollectProgressListener(p) => Some(
                  l.getCurrentTactic.map(f => (f._1, System.currentTimeMillis() - f._2)),
                  scala.collection.immutable.Seq(p:_*))
                case _ => None
              }).headOption
            case _ => None
          }
          (executor.isDone(taskId), progressList)
        case _ => (!executor.contains(taskId) || executor.isDone(taskId), None)
      }
    }
    TaskStatusResponse(proofId, nodeId, taskId, if (isDone) "done" else "running", progress) :: Nil
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
    val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList
    executor.synchronized {
      val response = executor.wait(taskId) match {
        case Some(Left(_: BelleProvable)) =>
          val tree = DbProofTree(db, proofId)
          tree.locate(nodeId) match {
            case None => new ErrorResponse("Unknown node " + nodeId)
            case Some(node) =>
              //@todo construct provable (expensive!)
              //assert(noBogusClosing(tree, node), "Server thinks a goal has been closed when it clearly has not")
              val proofSession = session(proofId).asInstanceOf[ProofSession]
              session(proofId) = RequestHelper.updateProofSessionDefinitions(proofSession, node)
              TaskResultResponse(proofId, node, marginLeft, marginRight, progress=true)
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
          TaskResultResponse(subId.toString, node, marginLeft, marginRight, progress = true)
        case Some(Right(error: BelleThrowable)) => new TacticErrorResponse(error.getMessage, "", error)
        case None => new ErrorResponse("Tactic cancelled, proof state may not reflect result of full tactic")
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
class PruneBelowRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
  extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    if (db.getProofInfo(proofId).closed) new ErrorResponse("Pruning not allowed on closed proofs") :: Nil
    else {
      val tree = DbProofTree(db, proofId)
      tree.locate(nodeId) match {
        case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
        case Some(node) =>
          node.pruneBelow()
          val item = AgendaItem(node.id.toString, AgendaItem.nameOf(node), proofId)
          new PruneBelowResponse(item) :: Nil
      }
    }
  }
}

/** Undoes the last proof step. */
class UndoLastProofStepRequest(db: DBAbstraction, userId: String, proofId: String)
  extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    //@todo do not load all steps
    tree.nodes.lastOption.flatMap(_.parent) match {
      case None => new ErrorResponse("Proof does not have any steps yet") :: Nil
      case Some(node) =>
        node.pruneBelow()
        val info = db.getProofInfo(proofId)
        db.updateProofInfo(info.copy(closed = false))
        val item = AgendaItem(node.id.toString,
          AgendaItem.nameOf(node)
          ,
          proofId, node.allAncestors.map(_.id.toString))
        new PruneBelowResponse(item) :: Nil
    }
  }
}

class GetProofProgressStatusRequest(db: DBAbstraction, userId: String, proofId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    // @todo return Loading/NotLoaded when appropriate
    val proof = db.getProofInfo(proofId)
    new ProofProgressResponse(proofId, isClosed = proof.closed) :: Nil
  }
}

class CheckIsProvedRequest(db: DBAbstraction, userId: String, proofId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  private def exportLemma(lemmaName: String, model: ModelPOJO, provable: ProvableSig, tactic: String) = {
    val evidence = Lemma.requiredEvidence(provable, ToolEvidence(List(
      "tool" -> "KeYmaera X",
      "model" -> model.keyFile,
      "tactic" -> tactic
    )) :: Nil)
    val lemma = new Lemma(provable, evidence, Some(lemmaName))
    if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
    LemmaDBFactory.lemmaDB.add(lemma)
  }
  private def backupProof(model: ModelPOJO, tactic: String) = {
    val proofbackupPath = Paths.get(Configuration.KEYMAERAX_HOME_PATH + File.separator + "proofbackup")
    if (!Files.exists(proofbackupPath)) Files.createDirectories(proofbackupPath)

    val sanitizedModelName = model.name.replaceAll("\\W", "_")
    val proofName = sanitizedModelName + "_" + new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss").format(Calendar.getInstance().getTime)
    var i = 0
    var uniqueProofName = proofName
    while (Files.exists(proofbackupPath.resolve(uniqueProofName))) {
      i = i+1
      uniqueProofName = proofName + "_" + i
    }

    val archiveContent = ArchiveEntryPrinter.archiveEntry(model, (proofName, tactic)::Nil, withComments=false)
    Files.write(proofbackupPath.resolve(uniqueProofName), archiveContent.getBytes())
  }

  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val model = db.getModel(tree.info.modelId.get)
    val entry = ArchiveParser.parse(model.keyFile, parseTactics=false).head

    // proof may have expanded some definitions itself and used lemmas that expanded some definitions
    val provable = tree.root.provable
    val conclusionSignature = StaticSemantics.signature(provable.conclusion)

    val proofSession = session(proofId).asInstanceOf[ProofSession]
    // find expanded definitions (including delayed model assumptions)
    val substs = (entry.defs.substs ++ proofSession.defs.substs ++ tree.proofSubsts).distinct.filter(_.what match {
      case FuncOf(n, _) => !conclusionSignature.contains(n)
      case PredOf(n, _) => !conclusionSignature.contains(n)
      case n: NamedSymbol => !conclusionSignature.contains(n)
      case _ => false
    })

    val conclusionFormula = entry.model.exhaustiveSubst(USubst(substs)).asInstanceOf[Formula]
    val conclusion = Sequent(IndexedSeq(), IndexedSeq(conclusionFormula))

    if (!provable.isProved) new ErrorResponse("Proof verification failed: proof " + proofId + " is not closed.\n Expected a provable without subgoals, but result provable is\n" + provable.prettyString)::Nil
    else if (provable.conclusion != conclusion) new ErrorResponse("Proof verification failed: proof " + proofId + " does not conclude the associated model.\n Expected " + conclusion.prettyString + "\nBut got\n" + provable.conclusion.prettyString)::Nil
    else {
      assert(provable.isProved, "Provable " + provable + " must be proved")
      assert(provable.conclusion == conclusion, "Conclusion of provable " + provable + " must match problem " + conclusion)
      val (tactic, proofStateInfo) = tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db)))
      // remember tactic string and mapping to proof tree
      val newInfo = ProofPOJO(tree.info.proofId, tree.info.modelId, tree.info.name, tree.info.description,
        tree.info.date, tree.info.stepCount, tree.info.closed, tree.info.provableId, tree.info.temporary,
        Some(GetTacticResponse(tactic, proofStateInfo.map({ case (k,v) => (k,v.id.toString) })).getJson.compactPrint))
      db.updateProofInfo(newInfo)
      // remember lemma
      exportLemma("user" + File.separator + model.name, model, provable, tactic)
      // backup proof to prevent data loss
      backupProof(model, tactic)
      new ProofVerificationResponse(proofId, provable, tactic) :: Nil
    }
  }
}

class IsLicenseAcceptedRequest(db: DBAbstraction) extends Request with ReadRequest {
  def resultingResponses(): List[Response] = {
    BooleanResponse(
      db.getConfiguration("license").config.contains("accepted") &&
      db.getConfiguration("license").config("accepted") == "true"
    ) :: Nil
  }
}

class AcceptLicenseRequest(db: DBAbstraction) extends Request with WriteRequest {
  def resultingResponses(): List[Response] = {
    val newConfiguration = new ConfigurationPOJO("license", Map("accepted" -> "true"))
    db.updateConfiguration(newConfiguration)
    BooleanResponse(flag=true) :: Nil
  }
}

/////
// Requests for shutting down KeYmaera if KeYmaera is hosted locally.
/////

class IsLocalInstanceRequest() extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = BooleanResponse(!HyDRAServerConfig.isHosted) :: Nil
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
          HyDRAServerConfig.system.terminate()
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

    BooleanResponse(flag = true) :: Nil
  }
}

class ExtractTacticRequest(db: DBAbstraction, userId: String, proofIdStr: String, verbose: Boolean) extends UserProofRequest(db, userId, proofIdStr) with WriteRequest {
  override def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofIdStr)
    val (tactic, locInfoSrc) = tree.tacticString(
      if (verbose) new VerboseTraceToTacticConverter(tree.info.defs(db))
      else new VerbatimTraceToTacticConverter()
    )
    // remember tactic string
    val locInfo = locInfoSrc.map({ case (k,v) => (k,v.id.toString) })
    val newInfo = ProofPOJO(tree.info.proofId, tree.info.modelId, tree.info.name, tree.info.description,
      tree.info.date, tree.info.stepCount, tree.info.closed, tree.info.provableId, tree.info.temporary,
      Some(GetTacticResponse(tactic, locInfo).getJson.compactPrint))
    db.updateProofInfo(newInfo)
    GetTacticResponse(tactic, locInfo) :: Nil
  }
}

case class ProofStateInfo(loc: Region, node: String)
case class TacticInfo(tacticText: String, nodesByLocation: List[ProofStateInfo])

object TacticInfoJsonProtocol extends DefaultJsonProtocol {
  implicit val regionFormat: RootJsonFormat[Region] = jsonFormat4(Region.apply)
  implicit val proofStateInfoFormat: RootJsonFormat[ProofStateInfo] = jsonFormat2(ProofStateInfo)
  implicit val tacticInfoFormat: RootJsonFormat[TacticInfo] = jsonFormat2(TacticInfo)
}

class GetTacticRequest(db: DBAbstraction, userId: String, proofIdStr: String) extends UserProofRequest(db, userId, proofIdStr) with ReadRequest {
  override def doResultingResponses(): List[Response] = {
    val proofInfo = db.getProofInfo(proofIdStr)
    val (tactic: String, proofStateInfo: Map[Location, String]) = proofInfo.tactic match {
      case Some(t) =>
        import TacticInfoJsonProtocol._
        try {
          val ti = t.parseJson.convertTo[TacticInfo]
          (ti.tacticText, ti.nodesByLocation.map(i => (i.loc, i.node)).toMap.asInstanceOf[Map[Location, String]])
        } catch {
          case _: ParsingException => (t, Map.empty) //@note backwards compatibility with database tactics not in JSON
        }
      case None => (BellePrettyPrinter(Idioms.nil), Map.empty)
    }
    GetTacticResponse(tactic, proofStateInfo) :: Nil
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
      case e: ParseException => ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
    }
  }
}

class ExtractLemmaRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val model = db.getModel(tree.info.modelId.get)
    val (tactic, _) = tree.tacticString(new VerboseTraceToTacticConverter(model.defs))
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
  def archiveEntry(modelInfo: ModelPOJO, tactics: List[(String, String)], withComments: Boolean): String = try {
    ArchiveParser.parser(modelInfo.keyFile) match {
      case (entry@ParsedArchiveEntry(name, _, _, _, _, _, _, _, _)) :: Nil if name == "<undefined>" =>
        new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments)(replaceInfo(entry, modelInfo.name, tactics))
      case (entry@ParsedArchiveEntry(name, _, _, _, _, _, _, _, _)) :: Nil if name != "<undefined>" =>
        new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments)(replaceInfo(entry, entry.name, tactics))
    }
  } catch {
    case _: ParseException =>
      val printedTactics = tactics.map({
        case (name, steps) =>
        s"""Tactic "$name"
          |$steps
          |End.""".stripMargin
      }).mkString("\n")
      s"""/* Model or tactics did not reparse, printed verbatim, needs manual editing */
        |
        |/* Input content */
        |${modelInfo.keyFile}
        |/* End input content */
        |
        |/* Printed tactics */
        |$printedTactics
        |/* End printed tactics */
        |""".stripMargin
  }

  private def replaceInfo(entry: ParsedArchiveEntry, entryName: String, tactics: List[(String, String)]): ParsedArchiveEntry = {
    entry.copy(name = entryName, tactics = tactics.map(e => (e._1, e._2, TactixLibrary.skip)))
  }
}

class ExtractProblemSolutionRequest(db: DBAbstraction, userId: String, proofId: String)
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    val proofName = tree.info.name
    val tactic = try {
      tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db)))._1
    } catch {
      case _: ParseException =>
        // fallback if for whatever reason model or tactic is not parseable: print verbatim without beautification
        RequestHelper.tacticString(tree.info)
    }
    val model = db.getModel(tree.info.modelId.get)

    def getLemmas(tactic: String): List[(String, (Option[ModelPOJO], Option[ProofPOJO]))] = {
      val lemmaFinder = """useLemma\(\"([^\"]*)\"""".r
      val lemmaNames = lemmaFinder.findAllMatchIn(tactic).map(m => m.group(1))
      val lemmaModels = lemmaNames.map(n => n -> db.getModelList(userId).find(n == _.name))
      val lemmas = lemmaModels.map(m => m._1 -> (m._2 match {
        case Some(mp) => db.getProofsForModel(mp.modelId).filter(_.closed) match {
          case Nil => m._2 -> None
          case proofs => m._2 -> Some(proofs.maxBy(_.date))
        }
        case _ => m._2 -> None
      })).toList
      val parentLemmas: List[(String, (Option[ModelPOJO], Option[ProofPOJO]))] = lemmas.flatMap({ case (_, (mp, pp)) => (mp, pp) match {
        case (Some(m), Some(p)) => p.tactic match {
          case Some(t) => getLemmas(t)
          case _ => Nil
        }
        case _ => Nil
      }})

      parentLemmas ++ lemmas
    }

    val lemmas = getLemmas(tactic)
    val printedLemmas = lemmas.map({
      case (_, (Some(modelPOJO), proofPOJO)) =>
        ArchiveEntryPrinter.archiveEntry(modelPOJO,
          proofPOJO match {
            case Some(p) => (p.name -> p.tactic.getOrElse("/* todo */ nil")) :: Nil
            case None => ("Todo" -> "/* todo */ nil") :: Nil
          },
          withComments = true)
      case (lemmaName, (None, _)) => s"""Lemma "$lemmaName" /* todo */ End."""
    })
    val modelContent = ArchiveEntryPrinter.archiveEntry(model, (proofName, tactic) :: Nil, withComments = true)
    val archiveContent = printedLemmas.mkString("\n\n") ++ modelContent
    new ExtractProblemSolutionResponse(archiveContent) :: Nil
  }
}

class ExtractModelSolutionsRequest(db: DBAbstraction, userId: String, modelIds: List[Int],
                                   withProofs: Boolean, exportEmptyProof: Boolean)
  extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    def printProof(tree: ProofTree, model: ModelPOJO): String = try {
      tree.tacticString(new VerboseTraceToTacticConverter(model.defs))._1
    } catch {
      case _: ParseException => RequestHelper.tacticString(tree.info)
    }

    def modelProofs(model: ModelPOJO): List[(String, String)] = {
      if (withProofs) db.getProofsForModel(model.modelId).map(p => p.name -> printProof(DbProofTree(db, p.proofId.toString), model))
      else Nil
    }
    val models = modelIds.map(mid => {
      val model = db.getModel(mid)
      model -> modelProofs(model)
    }).filter(exportEmptyProof || _._2.nonEmpty)
    val archiveContent = models.map({case (model, proofs) => ArchiveEntryPrinter.archiveEntry(model, proofs, withComments=true)}).mkString("\n\n")
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
object ProofValidationRunner extends Logging {
  private val results : mutable.Map[String, (Formula, BelleExpr, Option[Boolean])] = mutable.Map()

  case class ValidationRequestDNE(taskId: String) extends Exception(s"The requested taskId $taskId does not exist.")

  /** Returns Option[Proved] which is None iff the task is still running, and True if formula didn't prove. */
  def status(taskId: String): Option[Boolean] = results.get(taskId) match {
    case Some((_, _, proved)) => proved
    case None => throw ValidationRequestDNE(taskId)
  }

  /** Schedules a proof validation request and returns the UUID. */
  def scheduleValidationRequest(db: DBAbstraction, model: Formula, proof: BelleExpr, defs: Declaration): String = {
    val taskId = java.util.UUID.randomUUID().toString
    results update (taskId, (model, proof, None))

    new Thread(new Runnable() {
      override def run(): Unit = {
        logger.trace(s"Received request to validate $taskId. Running in separate thread.")
        val provable = ElidingProvable( Provable.startProof(model) )

        try {
          BelleInterpreter(proof, BelleProvable(provable, None, defs)) match {
            case BelleProvable(p, _, _) if p.isProved => results update (taskId, (model, proof, Some(true )))
            case _                                    => results update (taskId, (model, proof, Some(false)))
          }
        } catch {
          //Catch everything and indicate a failed proof attempt.
          case e : Throwable => results update (taskId, (model, proof, Some(false)))
        }

        logger.trace(s"Done executing validation check for $taskId")
      }
    }).start()

    taskId
  }
}

/** Returns a UUID whose status can be queried at a later time ({complete: true/false[, proves: true/false]}.
  * @see CheckValidationRequest - calling this with the returned UUID should give the status of proof checking. */
class ValidateProofRequest(db: DBAbstraction, model: Formula, proof: BelleExpr, defs: Declaration) extends Request with ReadRequest {
  override def resultingResponses() : List[Response] =
    //Spawn an async validation request and return the resulting UUID.
    new ValidateProofResponse(ProofValidationRunner.scheduleValidationRequest(db, model, proof, defs), None) :: Nil
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

  def jsonDisplayInfoComponents(di: ProvableInfo): JsValue = {
    val keyPos = AxIndex.axiomIndex(di)._1

    //@todo need more verbose axiom info
    ProvableInfo.locate(di.canonicalName) match {
      case Some(i) =>
        val (cond, op, key, keyPosString, conclusion, conclusionPos) = i.provable.conclusion.succ.head match {
          case Imply(c, eq@Equiv(l, r)) if keyPos == PosInExpr(1::0::Nil) => (Some(c), OpSpec.op(eq).opcode, l, "1.0", r, "1.1")
          case Imply(c, eq@Equiv(l, r)) if keyPos == PosInExpr(1::1::Nil) => (Some(c), OpSpec.op(eq).opcode, r, "1.1", l, "1.0")
          case bcf: BinaryCompositeFormula if keyPos == PosInExpr(0::Nil) => (None, OpSpec.op(bcf).opcode, bcf.left, "0", bcf.right, "1")
          case bcf: BinaryCompositeFormula if keyPos == PosInExpr(1::Nil) => (None, OpSpec.op(bcf).opcode, bcf.right, "1", bcf.left, "0")
          case f => (None, OpSpec.op(Equiv(f, True)).opcode, f, "0", True, "1")
        }
        JsObject(
          "cond" -> (if (cond.isDefined) JsString(UIKeYmaeraXAxiomPrettyPrinter.pp(cond.get)) else JsNull),
          "op" -> (if (op.nonEmpty) JsString(UIKeYmaeraXAxiomPrettyPrinter.pp.htmlEncode(op)) else JsNull),
          "key" -> JsString(UIKeYmaeraXAxiomPrettyPrinter.pp(key)),
          "keyPos" -> JsString(keyPosString),
          "conclusion" -> JsString(UIKeYmaeraXAxiomPrettyPrinter.pp(conclusion)),
          "conclusionPos" -> JsString(conclusionPos)
        )
      case None => JsNull
    }
  }

  /* String representation of the actual step (if tacticId refers to stepAt, otherwise tacticId).
     For display purposes only. */
  def getSpecificName(tacticId: String, sequent:Sequent, l1: Option[PositionLocator], l2: Option[PositionLocator],
                      what: DerivationInfo => String, session: ProofSession): String =
    getSpecificName(tacticId, sequent, l1, l2, session) match {
      case Left(s) => s
      case Right(t) => what(t)
    }

  /* Try to figure out the most intuitive inference rule to display for this tactic. If the user asks us "StepAt" then
   * we should use the StepAt logic to figure out which rule is actually being applied. Otherwise just ask TacticInfo */
  def getSpecificName(tacticId: String, sequent:Sequent, l1: Option[PositionLocator], l2: Option[PositionLocator],
                      session: ProofSession): Either[String,DerivationInfo] = {
    val pos = l1 match {case Some(Fixed(p, _, _)) => Some(p) case _ => None}
    val pos2 = l2 match {case Some(Fixed(p, _, _)) => Some(p) case _ => None}
    tacticId.toLowerCase match {
      case "step" | "stepat" if pos.isDefined && pos2.isEmpty =>
        sequent.sub(pos.get) match {
          case Some(fml: Formula) =>
            UIIndex.theStepAt(fml, pos, Some(sequent), session.defs.substs) match {
              case Some(step) => Right(step)
              case None => Left(tacticId)
            }
          case _ => Right(DerivationInfo.ofCodeName(tacticId))
        }
      case "step" | "stepat" if pos.isDefined && pos2.isDefined =>
        sequent.sub(pos.get) match {
          case Some(fml: Formula) =>
            UIIndex.theStepAt(pos.get, pos2.get, sequent) match {
              case Some(step) => Right(step)
              case None => Left(tacticId)
            }
        }
      case _ => Right(DerivationInfo.ofCodeName(tacticId))
    }
  }

  /** A listener that stores proof steps in the database `db` for proof `proofId`. */
  def listenerFactory(db: DBAbstraction, session: ProofSession)(proofId: Int)(tacticName: String, parentInTrace: Int,
                                                                              branch: Int): Seq[IOListener] = {
    DBTools.listener(db, constructGlobalProvable = false, (tn: String) => {
      val codeName = tn.split("\\(").head
      Try(RequestHelper.getSpecificName(codeName, null, None, None, _ => tacticName, session)).getOrElse(tn)
    })(proofId)(tacticName, parentInTrace, branch)
  }

  /** Updates the definitions in `proofSession` to include the unexpanded symbols of the open goals in `node`. */
  def updateProofSessionDefinitions(proofSession: ProofSession, node: ProofTreeNode): ProofSession = {
    val symbols = node.children.flatMap(_.localProvable.subgoals.flatMap(StaticSemantics.symbols)).toSet[NamedSymbol].filter({
      case _: DifferentialSymbol => false
      case _ => true
    })
    val elaboratedToFns = symbols.filter({
      case Function(n, i, Unit, s, _) => proofSession.defs.decls.exists({
        case (Name(vn, vi), Signature(None, vs, _, _, _)) => vn == n && vi == i && vs == s
        case _ => false
      })
      case _ => false
    })
    val undefinedSymbols = symbols.filter(s => !proofSession.defs.asNamedSymbols.contains(s)) -- elaboratedToFns -- InterpretedSymbols.symbols
    val nodeFml = node.children.flatMap(_.localProvable.subgoals.map(_.toFormula)).reduceRightOption(And).getOrElse(True)
    val collectedArgs = ArchiveParser.declarationsOf(nodeFml, Some(undefinedSymbols))

    val newDefs: Map[Name, Signature] = undefinedSymbols.map({
      case fn@Function(name, index, domain, sort, _) => Name(name, index) -> Signature(Some(domain), sort,
        collectedArgs.decls.get(Name(fn.name, fn.index)).flatMap(_.arguments), None, UnknownLocation)
      case ProgramConst(name, _) => Name(name, None) -> Signature(None, Trafo, None, None, UnknownLocation)
      case SystemConst(name, _) => Name(name, None) -> Signature(None, Trafo, None, None, UnknownLocation)
      case u => Name(u.name, u.index) -> Signature(None, u.sort, None, None, UnknownLocation) // cuts may introduce variables
    }).toMap
    //@note TactixInit.invSupplier, once non-empty, is proofSession.invSupplier + invariants discovered when executing tactics
    val mergedInvSupplier = TactixInit.invSupplier match {
      case ts: ConfigurableGenerator[GenProduct] => if (ts.products.nonEmpty) ts else proofSession.invSupplier
      case ts => ts
    }
    proofSession.copy(defs = proofSession.defs.copy(proofSession.defs.decls ++ newDefs),
      invSupplier = mergedInvSupplier)
  }

  def tacticString(proofInfo: ProofPOJO): String = {
    val text = proofInfo.tactic.getOrElse("/* no tactic recorded */")
    try {
      text.parseJson match {
        case JsObject(fields) if fields.contains("tacticText") => fields("tacticText").asInstanceOf[JsString].value
        case JsString(s) => s
        case _ => "/* no tactic recorded */"
      }
    } catch {
      case _: ParsingException => text //@note backwards-compatibility with database content that's not JSON
    }
  }

}
