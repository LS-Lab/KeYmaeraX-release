/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.core.{
  Bool,
  DotTerm,
  Expression,
  FuncOf,
  Function,
  NamedSymbol,
  Nothing,
  Pair,
  PredOf,
  ProgramConst,
  Real,
  Sort,
  StaticSemantics,
  SystemConst,
  Term,
  Variable,
}
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ApplicableDefinitionsResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, DbProofTree, ProofSession, ReadRequest, Response, UserProofRequest}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.parser.{Name, Signature, UnknownLocation}

import scala.collection.immutable.{::, List, Map, Nil, Set}

/** Gets the definitions that can be expanded at node `nodeId`. */
class GetApplicableDefinitionsRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    if (tree.done) return ApplicableDefinitionsResponse(Nil)
    val proofSession = session(proofId).asInstanceOf[ProofSession]
    tree.locate(nodeId).map(n => n.goal.map(StaticSemantics.symbols).getOrElse(Set.empty)) match {
      case Some(symbols) =>
        val applicable: Map[NamedSymbol, Signature] = symbols
          .filter({
            case _: Function => true
            case _: ProgramConst => true
            case _: SystemConst => true
            case _ => false
          })
          .flatMap(s => proofSession.defs.find(s.name, s.index).map(s -> _))
          .toMap

        /** Translates the list of parsed argument names `args` into a function argument (Pair). */
        def asPairs(args: Option[List[(Name, Sort)]]): Term = args
          .map({
            case Nil => Nothing
            case (Name(n, i), _) :: Nil => if (n == Nothing.name) Nothing else Variable(n, i)
            case (n, _) :: ns => Pair(Variable(n.name, n.index), asPairs(Some(ns)))
          })
          .getOrElse(Nothing)

        /** Replaces `.` in expression `repl` with the corresponding argument name from `args`. */
        def withArgs(repl: Option[Expression], args: Option[List[(Name, Sort)]]): Option[Expression] = args match {
          case None => repl
          case Some(a) =>
            // @note can be optimized to just a single traversal if we are sure that . and ._0 do not co-occur and ._i is
            //      a contiguous range
            def argsMap(dots: List[NamedSymbol], i: Int): Map[NamedSymbol, Name] = dots match {
              case Nil => Map.empty
              case dot :: Nil => Map(dot -> a(i)._1)
              case dot :: dots => Map(dot -> a(i)._1) ++ argsMap(dots, i + 1)
            }
            val dots = argsMap(
              repl
                .map(StaticSemantics.symbols)
                .getOrElse(Set.empty)
                .filter({
                  case _: DotTerm => true
                  case _ => false
                })
                .toList
                .sortBy({
                  case DotTerm(_, None) => -1
                  case DotTerm(_, Some(i)) => i
                }),
              0,
            )
            repl.flatMap(
              ExpressionTraversal.traverseExpr(
                new ExpressionTraversalFunction() {
                  override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
                    case s: DotTerm =>
                      val n = dots(s)
                      Right(Variable(n.name, n.index))
                    case _ => Left(None)
                  }
                },
                _,
              )
            )
        }
        val expansions: List[(NamedSymbol, Expression, Option[Expression], Boolean)] = applicable
          .toList
          .map({
            case (s: Function, Signature(_, sort, args, Right(repl), loc)) => sort match {
                case Real => (s, FuncOf(s, asPairs(args)), withArgs(repl, args), loc == UnknownLocation)
                case Bool => (s, PredOf(s, asPairs(args)), withArgs(repl, args), loc == UnknownLocation)
              }
            case (s: Function, Signature(_, sort, args, Left(repl), loc)) => sort match {
                case Real => (s, FuncOf(s, asPairs(args)), withArgs(Some(repl), args), loc == UnknownLocation)
                case Bool => (s, PredOf(s, asPairs(args)), withArgs(Some(repl), args), loc == UnknownLocation)
              }
            case (s: ProgramConst, Signature(_, _, _, Right(repl), loc)) => (s, s, repl, loc == UnknownLocation)
            case (s: SystemConst, Signature(_, _, _, Right(repl), loc)) => (s, s, repl, loc == UnknownLocation)
          })
          .filter(e => e._4 || e._3.isDefined)
        ApplicableDefinitionsResponse(expansions.sortBy(_._1))
      case None => ApplicableDefinitionsResponse(Nil)
    }
  }
}
