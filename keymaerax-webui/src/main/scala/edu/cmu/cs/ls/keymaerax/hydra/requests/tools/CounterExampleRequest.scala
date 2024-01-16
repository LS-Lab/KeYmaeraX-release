/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.tools

import edu.cmu.cs.ls.keymaerax.bellerophon.SaturateTactic
import edu.cmu.cs.ls.keymaerax.btactics.cexsearch.{BoundedDFS, ProgramSearchNode}
import edu.cmu.cs.ls.keymaerax.btactics.{TactixLibrary, ToolProvider}
import edu.cmu.cs.ls.keymaerax.core.{And, Bool, Box, Expression, Formula, FuncOf, Function, Imply, NamedSymbol, Nothing, ODESystem, PredOf, Real, Sequent, StaticSemantics, Term, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.hydra.responses.models.ParseErrorResponse
import edu.cmu.cs.ls.keymaerax.hydra.responses.tools.CounterExampleResponse
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.{ExpressionAugmentor, FormulaAugmentor, SequentAugmentor}
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.parser.ParseException
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.tools.ext.CounterExampleTool
import edu.cmu.cs.ls.keymaerax.tools.{MathematicaComputationAbortedException, MathematicaComputationTimedOutException, ToolException}
import spray.json.DefaultJsonProtocol._
import spray.json._

import scala.annotation.tailrec
import scala.collection.immutable.{List, Map, Nil}
import scala.util.Try

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
      //TODO: check if should be changed
      case Function(_, _, _, _, None) => true case _ => false }).map(_.asInstanceOf[Function])
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
          new CounterExampleResponse("cex.nonfo", additionalAssumptions, (nonFOSucc ++ nonFOAnte).head) :: Nil
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
                case None => new CounterExampleResponse("cex.none", additionalAssumptions) :: Nil
              }
            } else {
              val skolemized = TactixLibrary.proveBy(sequent,
                SaturateTactic(TactixLibrary.alphaRule | TactixLibrary.allR(Symbol("R")) | TactixLibrary.existsL(Symbol("L"))))
              val fml = skolemized.subgoals.map(_.toFormula).reduceRight(And)
              val withAssumptions = additionalAssumptions match {
                case Some(a) => Imply(a, fml)
                case None => fml
              }
              try {
                findCounterExample(withAssumptions, cexTool) match {
                  //@todo return actual sequent, use collapsiblesequentview to display counterexample
                  case Some(cex) => new CounterExampleResponse("cex.found", additionalAssumptions, fml, cex) :: Nil
                  case None => new CounterExampleResponse("cex.none", additionalAssumptions) :: Nil
                }
              } catch {
                case _: MathematicaComputationAbortedException => new CounterExampleResponse("cex.timeout", additionalAssumptions) :: Nil
                case _: MathematicaComputationTimedOutException => new CounterExampleResponse("cex.timeout", additionalAssumptions) :: Nil
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
                          case Some(cex) => new CounterExampleResponse("cex.found", additionalAssumptions, fml, cex.map) :: Nil
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
                  case None => new CounterExampleResponse("cex.wrongshape", additionalAssumptions) :: Nil
                }
              case None => new CounterExampleResponse("cex.notool", additionalAssumptions) :: Nil
            }
          }
        }

        if (useFmlIndices.nonEmpty) try {
          node.goal match {
            case Some(unfiltered) if filterSequent(unfiltered).isFOL => ToolProvider.cexTool() match {
              case Some(cexTool) => getCex(node, cexTool)
              case None => new CounterExampleResponse("cex.notool", additionalAssumptions) :: Nil
            }
            case Some(unfiltered) =>
              val sequent = filterSequent(unfiltered)
              sequent.succ.find({ case Box(_: ODESystem, _) => true case _ => false }) match {
                case Some(Box(ode: ODESystem, post)) => ToolProvider.invGenTool() match {
                  case Some(tool) => tool.refuteODE(ode, sequent.ante, post) match {
                    case None => new CounterExampleResponse("cex.none", additionalAssumptions) :: Nil
                    case Some(cex) => new CounterExampleResponse("cex.found", additionalAssumptions, sequent.toFormula, cex) :: Nil
                  }
                  case None => new CounterExampleResponse("cex.notool", additionalAssumptions) :: Nil
                }
                case None => nonfoError(sequent)
              }
            case None => new CounterExampleResponse("cex.none", additionalAssumptions) :: Nil
          }
        } catch {
          case _: MathematicaComputationAbortedException => new CounterExampleResponse("cex.timeout", additionalAssumptions) :: Nil
          case _: MathematicaComputationTimedOutException => new CounterExampleResponse("cex.timeout", additionalAssumptions) :: Nil
        } else new CounterExampleResponse("cex.emptysequent", additionalAssumptions) :: Nil
    }
  }
}
