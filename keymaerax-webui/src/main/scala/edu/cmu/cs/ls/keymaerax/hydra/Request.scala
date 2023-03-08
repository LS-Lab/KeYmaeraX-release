/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.parser.{Name, Signature}

import spray.json._
import spray.json.JsonParser.ParsingException

import java.text.SimpleDateFormat
import java.util.Calendar

import scala.collection.immutable._
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
trait Request extends Logging {
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
  extends UserRequest(userId, (id: String) =>
    Try(proofId.toInt).toOption.isDefined && (db.getProofInfo(proofId).modelId.isEmpty || db.userOwnsProof(id, proofId))
  ) {
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

class FailedRequest(userId: String, msg: String, cause: Throwable = null) extends UserRequest(userId, _ => true) {
  def resultingResponses(): List[Response] = { new ErrorResponse(msg, cause) :: Nil }
}

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
    val undefinedSymbols = symbols.filter({
      case Function(_, _, _, _, Some(_)) => false
      case _ => true
    }).filter(s => !proofSession.defs.asNamedSymbols.exists({
      // do not update interpreted functions, interpretation may not be recorded in proof nodes
      case ds@Function(n, i, dom, srt, Some(_)) => s match {
        case Function(sn, si, sd, ss, None) => n == sn && i == si && dom == sd && srt == ss
        case _ => ds == s
      }
      case ds => ds == s
    })) -- elaboratedToFns
    val nodeFml = node.children.flatMap(_.localProvable.subgoals.map(_.toFormula)).reduceRightOption(And).getOrElse(True)
    val collectedArgs = ArchiveParser.declarationsOf(nodeFml, Some(undefinedSymbols))

    val newDefs: Map[Name, Signature] = undefinedSymbols.map({
      case fn@Function(name, index, domain, sort, _) => Name(name, index) -> Signature(Some(domain), sort,
        collectedArgs.decls.get(Name(fn.name, fn.index)).flatMap(_.arguments), Right(None), UnknownLocation)
      case ProgramConst(name, _) => Name(name, None) -> Signature(None, Trafo, None, Right(None), UnknownLocation)
      case SystemConst(name, _) => Name(name, None) -> Signature(None, Trafo, None, Right(None), UnknownLocation)
      case u => Name(u.name, u.index) -> Signature(None, u.sort, None, Right(None), UnknownLocation) // cuts may introduce variables
    }).toMap
    //@note TactixInit.invSupplier, once non-empty, is proofSession.invSupplier + invariants discovered when executing tactics
    val mergedInvSupplier = TactixInit.invSupplier match {
      case ts: ConfigurableGenerator[GenProduct] => if (ts.products.nonEmpty) ts else proofSession.invSupplier
      case ts => ts
    }
    proofSession.copy(defs = proofSession.defs.copy(proofSession.defs.decls ++ newDefs),
      invSupplier = mergedInvSupplier)
  }

  def tacticString(proofInfo: ProofPOJO): String = tacticString(proofInfo.tactic.getOrElse("/* no tactic recorded */"))

  def tacticString(s: String): String = {
    try {
      s.parseJson match {
        case JsObject(fields) if fields.contains("tacticText") => fields("tacticText").asInstanceOf[JsString].value
        case JsString(s) => s
        case _ => "/* no tactic recorded */"
      }
    } catch {
      case _: ParsingException => s //@note backwards-compatibility with database content that's not JSON
    }
  }

}
