/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Parse full Kaisar file which can contain, e.g., multiple models / proofs / declarations
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse._
// allow Scala-style comments and ignore newlines
import ScalaWhitespace._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ParserCommon._

object KaisarFileParser {
  def letDecl[$: P]: P[LetDecl] = ProofParser.let.map({ case ls: LetSym => LetDecl(ls) })
  def pragmaDecl[$: P]: P[PragmaDecl] = ProofParser.pragma.map((pr: Pragma) => PragmaDecl(pr.ps))
  def synthesizeDecl[$: P]: P[SynthesizeDecl] = ("synthesize" ~ ident ~ ";").map(SynthesizeDecl)
  def conclusionDecl[$: P]: P[ConclusionDecl] = ("conclusion" ~ ident ~ ";").map(ConclusionDecl)
  def theoremDecl[$: P]: P[TheoremDecl] = (("proof" ~ ident ~ "begin" ~ ProofParser.proof ~ "end")).map({
    case (name, ss) => TheoremDecl(name, KaisarProof.block(ss))
  })
  def provesDecl[$: P]: P[ProvesDecl] = ("proves" ~ ident ~ ExpressionParser.formula ~ ";").map({ case (id, fml) =>
    ProvesDecl(id, fml)
  })
  def decl[$: P]: P[KaisarDecl] = letDecl | pragmaDecl | synthesizeDecl | conclusionDecl | theoremDecl | provesDecl
  def file[$: P]: P[Decls] = decl.rep(1).map(dcls => Decls(dcls.toList)) ~ ws
}
