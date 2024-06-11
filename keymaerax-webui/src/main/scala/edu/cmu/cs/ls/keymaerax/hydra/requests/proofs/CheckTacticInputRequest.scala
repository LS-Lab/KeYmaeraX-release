/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfoRegistry
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.core.{
  Bool,
  Expression,
  Formula,
  FormulaKind,
  FuncOf,
  NamedSymbol,
  PredOf,
  ProgramConst,
  Real,
  Sequent,
  StaticSemantics,
  SubstitutionPair,
  SystemConst,
}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.parser._

import scala.collection.immutable.{::, List, Nil, Set}

class CheckTacticInputRequest(
    db: DBAbstraction,
    userId: String,
    proofId: String,
    nodeId: String,
    tacticId: String,
    paramName: String,
    paramType: String,
    paramValue: String,
) extends UserProofRequest(db, userId, proofId) with ReadRequest {

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
        case BelleTermInput(value, Some(OptionArg(arg))) if arg.isInstanceOf[SubstitutionArg] =>
          checkSubstitutionInput(arg, value.asSubstitutionPair :: Nil, sequent, defs)
        case BelleTermInput(value, Some(arg @ ListArg(ai: FormulaArg))) =>
          checkExpressionInput(arg, Parser.parseExpressionList(value), sequent, defs)
      }
    } catch { case ex: ParseException => BooleanResponse(flag = false, Some(ex.toString)) }
  }

  /** Checks expression inputs. */
  private def checkExpressionInput[E <: Expression](
      arg: ArgInfo,
      exprs: List[E],
      sequent: Sequent,
      defs: Declaration,
  ) = {

    // @note function/predicate/program symbols are proof parameters if not in input, otherwise look up in definitions
    val elaborated = exprs.map({
      case e @ FuncOf(n, a) if !defs.asNamedSymbols.contains(n) =>
        arg match {
          case _: FormulaArg => PredOf(n.copy(sort = Bool), a)
          case _ => e
        }
      case e @ PredOf(n, a) if !defs.asNamedSymbols.contains(n) =>
        arg match {
          case _: TermArg => FuncOf(n.copy(sort = Real), a)
          case _ => e
        }
      case a: ProgramConst if FormulaTools.dualFree(sequent) => SystemConst(a.name, a.space)
      case e => defs.elaborateToSystemConsts(defs.elaborateToFunctions(e))
    })

    val sortMismatch: Option[String] = (arg, elaborated) match {
      case (_: FormulaArg, (f: Formula) :: Nil) => DerivationInfoRegistry.convert(arg, List(f)).toOption
      case (_: ExpressionArgBase, (e: Expression) :: Nil) => DerivationInfoRegistry.convert(arg, List(e)).toOption
      case (ListArg(_: FormulaArg), fmls) if fmls.forall(_.kind == FormulaKind) => None
      case _ => Some(
          "Expected: " + arg.sort + ", found: " + elaborated.map(_.kind).mkString(",") + " " +
            elaborated.map(_.prettyString).mkString(",")
        )
    }

    sortMismatch match {
      case None =>
        val allowedSymbols = StaticSemantics.symbols(sequent) ++ defs.asNamedSymbols ++ TacticReservedSymbols.symbols
        val paramFV: Set[NamedSymbol] = {
          // @note function/predicate/system/game symbols are proof parameters if they are not declared in the input
          elaborated
            .flatMap({
              case FuncOf(n, a) if !defs.asNamedSymbols.contains(n) => StaticSemantics.symbols(a)
              case PredOf(n, a) if !defs.asNamedSymbols.contains(n) => StaticSemantics.symbols(a)
              case n: SystemConst if !defs.asNamedSymbols.contains(n) => Set.empty[NamedSymbol]
              case n: ProgramConst if !defs.asNamedSymbols.contains(n) => Set.empty[NamedSymbol]
              case e => StaticSemantics.symbols(e)
            })
            .toSet
        }

        val (hintFresh, allowedFresh) = arg match {
          case _: VariableArg if arg.allowsFresh.contains(arg.name) => (Nil, Nil)
          case _ => (paramFV -- allowedSymbols, arg.allowsFresh) // @todo would need other inputs to check
        }

        if (hintFresh.size > allowedFresh.size) {
          val fnVarMismatch = hintFresh
            .map(fn => fn -> allowedSymbols.find(s => s.name == fn.name && s.index == fn.index))
            .filter(_._2.isDefined)
          if (fnVarMismatch.isEmpty) {
            BooleanResponse(
              flag = false,
              Some(
                "argument " + arg.name + " uses new names that do not occur in the sequent: " +
                  hintFresh.mkString(",") +
                  (if (allowedFresh.nonEmpty) ", expected new names only as introduced for " +
                     allowedFresh.mkString(",")
                   else ", is it a typo?")
              ),
            )
          } else BooleanResponse(
            flag = false,
            Some(
              "function/variable mismatch between goal and argument " + arg.name + ": " +
                fnVarMismatch
                  .map({ case (have, Some(expect)) =>
                    have.prettyString + "(" + have.getClass.getSimpleName + ") vs. " + expect.prettyString + "(" +
                      expect.getClass.getSimpleName + " in sequent)"
                  })
                  .mkString(", ")
            ),
          )
        } else { BooleanResponse(flag = true) }
      case Some(mismatch) => BooleanResponse(flag = false, Some(mismatch))
    }
  }

  /** Checks substitution inputs. */
  private def checkSubstitutionInput(
      arg: ArgInfo,
      exprs: List[SubstitutionPair],
      sequent: Sequent,
      defs: Declaration,
  ) = {
    // @note parsed as substitution pair is all we check for now
    BooleanResponse(flag = true)
  }

  override protected def doResultingResponse(): Response = {
    val info = DerivationInfo(tacticId)
    val expectedInputs = info.inputs
    val paramInfo = expectedInputs.find(_.name == paramName)
    val isIllFormed = paramInfo.isEmpty || paramValue.isEmpty
    if (!isIllFormed) {
      val input = BelleTermInput(paramValue, paramInfo)

      val tree: ProofTree = DbProofTree(db, proofId)
      tree.locate(nodeId) match {
        case None => BooleanResponse(flag = false, Some("Unknown node " + nodeId + " in proof " + proofId))
        case Some(node) if node.goal.isEmpty =>
          BooleanResponse(flag = false, Some("Node " + nodeId + " does not have a goal"))
        case Some(node) if node.goal.isDefined =>
          val sequent = node.goal.get
          val proofSession = session(proofId).asInstanceOf[ProofSession]
          checkInput(sequent, input, proofSession.defs)
      }
    } else {
      val msg =
        if (paramValue.isEmpty) "Missing value of parameter " + paramName
        else "Parameter " + paramName + " not a valid argument of tactic " + tacticId + ", expected one of " +
          expectedInputs.map(_.name).mkString(",")
      BooleanResponse(flag = false, Some(msg))
    }
  }

}
