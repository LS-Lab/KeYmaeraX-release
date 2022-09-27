/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.core.{Expression, FuncOf, Function, NamedSymbol, PredOf, ProgramConst, SystemConst, Term, Trafo, Unit}
import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, DBAbstraction, ErrorResponse, ProofSession, Response, UserProofRequest, WriteRequest}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter
import edu.cmu.cs.ls.keymaerax.parser.{Name, Signature, UnknownLocation}

import scala.collection.immutable.{List, Nil}
import scala.util.Try

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
            val erepl = proofSession.defs.elaborateToSystemConsts(proofSession.defs.elaborateToFunctions(r))
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