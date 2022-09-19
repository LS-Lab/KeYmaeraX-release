/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.HackyInlineErrorMsgPrinter
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.btactics.{TactixInit, ToolProvider}
import edu.cmu.cs.ls.keymaerax.core.{ProverException, Sequent}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.{RunBelleTermResponse, TacticErrorResponse}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, ParseException, Parser, UnknownLocation}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement
import edu.cmu.cs.ls.keymaerax.tools.ext.{Mathematica, Z3}

import scala.collection.immutable.{::, List, Nil, Seq}

/* If pos is Some then belleTerm must parse to a PositionTactic, else if pos is None belleTerm must parse
* to a Tactic */
class RunBelleTermRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, belleTerm: String,
                          pos: Option[PositionLocator], pos2: Option[PositionLocator] = None,
                          inputs: List[BelleTermInput] = Nil, consultAxiomInfo: Boolean = true, stepwise: Boolean = false)
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
    val (specificTerm: String, adaptedPos: Option[PositionLocator], adaptedPos2: Option[PositionLocator], args) =
      if (consultAxiomInfo) RequestHelper.getSpecificName(belleTerm, sequent, pos, pos2, session(proofId).asInstanceOf[ProofSession]) match {
        case Left(s) => (s, pos, pos2, Nil)
        //@note improve tactic maintainability by position search with formula shape on universally applicable tactics
        case Right(t: PositionTacticInfo) if t.codeName == "hideL" || t.codeName == "hideR" => pos match {
          case Some(Fixed(pp, None, _)) if pp.isTopLevel => (t.codeName, Some(Fixed(pp, Some(sequent(pp.top)))), None, Nil)
          case _ => (t.codeName, pos, None, Nil)
        }
        case Right(t: PositionTacticInfo) => (t.codeName, pos, None, Nil)
        case Right(t: InputPositionTacticInfo) => (t.codeName, pos, None, t.persistentInputs)
        case Right(t: TwoPositionTacticInfo) => (t.codeName, pos, pos2, Nil)
        case Right(t: InputTwoPositionTacticInfo) => (t.codeName, pos, pos2, t.persistentInputs)
        case Right(t: BuiltinInfo) => (t.codeName, None, None, Nil)
        case Right(t: CoreAxiomInfo) => (t.codeName, pos, None, Nil)
        case Right(t: DerivedAxiomInfo) => (t.codeName, pos, None, Nil)
        case Right(t) => (t.codeName, None, None, t.persistentInputs)
      }
      else (belleTerm, pos, pos2, Nil)

    if ((args match { case (_: ListArg) :: Nil => true case _ => false }) && inputs.isEmpty && adaptedPos.isEmpty) {
      assert(adaptedPos2.isEmpty, "Undefined pos1, but defined pos2")
      specificTerm + "()"
    } else if (inputs.isEmpty && adaptedPos.isEmpty) {
      assert(adaptedPos2.isEmpty, "Undefined pos1, but defined pos2")
      specificTerm
    } else if (inputs.isEmpty) {
      specificTerm + "(" + adaptedPos.get.prettyString + adaptedPos2.map("," + _.prettyString).getOrElse("") + ")"
    } else {
      specificTerm + "(" + paramStrings.mkString(",") + adaptedPos.map("," + _.prettyString).getOrElse("") + adaptedPos2.map("," + _.prettyString).getOrElse("") + ")"
    }
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
              val expr = ArchiveParser.tacticParser(tacticString, proofSession.defs)

              val ruleName =
                if (consultAxiomInfo) RequestHelper.getSpecificName(belleTerm, sequent, pos, pos2, _ => expr.prettyString,
                  session(proofId).asInstanceOf[ProofSession])
                else "custom"

              def interpreter(proofId: Int, startNodeId: Int) = new Interpreter {
                private val proofSession = session(proofId.toString).asInstanceOf[ProofSession]
                private val inner = SpoonFeedingInterpreter(proofId, startNodeId, db.createProof, proofSession.defs,
                  RequestHelper.listenerFactory(db, proofSession),
                  ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), 0, strict=false, convertPending=true, recordInternal=false)

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
                  val taskId = node.stepTactic(userId, interpreter(proofId.toInt, startStepIndex), expr)
                  RunBelleTermResponse(proofId, node.id.toString, taskId, "Executing custom tactic") :: Nil
                } else {
                  val localProvable = ProvableSig.startProof(sequent, tree.info.defs(db))
                  val localProofId = db.createProof(localProvable)
                  val executor = BellerophonTacticExecutor.defaultExecutor
                  val taskId = executor.schedule(userId, expr, BelleProvable.labeled(localProvable, node.label.map(_ :: Nil)), interpreter(localProofId, -1))
                  RunBelleTermResponse(localProofId.toString, "()", taskId, "Executing internal steps of " + executionInfo(belleTerm)) :: Nil
                }
              } else {
                //@note execute clicked single-step tactics on sequential interpreter right away
                val taskId = node.runTactic(userId, ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), expr, ruleName)
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