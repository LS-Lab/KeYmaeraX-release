/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Check full Kaisar file which can contain, e.g., multiple models / proofs / declarations
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{Ident, ProofCheckException}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.StandardLibrary._
import edu.cmu.cs.ls.keymaerax.core._

object FileChecker {

  /** Context is list of declarations already checked */
  type FileContext = List[KaisarDecl]

  /** Look up result of previous proof */
  private def getTheorem(kc: FileContext, name: Ident): Option[TheoremDecl] = {
    kc.flatMap({
        case td: TheoremDecl => if (td.name == name) List(td) else Nil
        case _ => Nil
      })
      .headOption
    // map(td => (td.in, td.conclusion)).headOption
  }

  /** Convert file-level context to proof-level context for individual proof checking */
  private def toProofContext(kc: FileContext): Context = {
    val ss: List[Statement] = kc.flatMap({
      case ld: LetDecl => List(ld.ls)
      case _ => Nil
    })
    ss.foldLeft(Context.empty)(_.:+(_))
  }

  /** Check declarations in context */
  def apply(kc: FileContext, file: List[KaisarDecl]): Unit = {
    file match {
      case Nil =>
      case Decls(dcls) :: decls => apply(kc, dcls ++ decls)
      case decl :: decls =>
        val newDecls: List[KaisarDecl] = decl match {
          case PragmaDecl(pd) => Pragma.apply(pd); Nil
          case ld: LetDecl => // @TODO: check admissibility
            List(ld)
          case TheoremDecl(name, pf, outPf, _conclusion) =>
            val proofCon = toProofContext(kc)
            val (outCon, cncl) = Kaisar.result(proofCon, pf)
            List(TheoremDecl(name, pf, outCon, cncl))
          case ProvesDecl(thmName, conclusion) =>
            // @TODO: Elaborate conclusion formula
            // @TODO: Decide whether need to use conclusion proof and SSA-ify both or whether source proof suffices
            // partial answer: Will need SSA-ify pass if we want to refine proofs that contain @, which we probably do
            getTheorem(kc, thmName) match {
              case None => throw ProofCheckException("Couldn't find theorem named " + thmName)
              case Some(td) =>
                val Box(a, True) = asBox(conclusion)
                val proofCon = toProofContext(kc)
                val elabA = proofCon.elaborateFunctions(a, node = Triv())
                val ssaA = SSAPass(elabA)
                RefinementChecker(td.outPf, ssaA);
                Nil
            }
          case ConclusionDecl(thmName) => getTheorem(kc, thmName) match {
              case None => throw ProofCheckException("Couldn't find theorem named " + thmName)
              case Some(td) =>
                println(s"Printing conclusion of theorem $thmName:\n" + td.conclusion.prettyString)
                Nil
            }
          case SynthesizeDecl(thmName) => getTheorem(kc, thmName) match {
              case None => throw ProofCheckException("Couldn't find theorem named " + thmName)
              case Some(td) =>
                // @TODO: Pretty-printer for strategies, or add command that executes them.
                val strat = SimpleStrategy(AngelStrategy(td.outPf))
                println(s"Printing strategy synthesized from theorem $thmName:\n" + strat)
                Nil
            }
          case _: Decls => throw new Exception("Unreachable code by pattern match")
        }
        apply(kc ++ newDecls, decls)
    }
  }

  /** Entry point */
  def apply(decl: Decls): Unit = { apply(Nil, decl.dcls) }
}
