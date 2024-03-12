/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Data types for top-level declarations of Kaisar files.
 * @see
 *   [[KaisarProof]] for proof statement constructors
 * @see
 *   [[KaisarFileParser]] for concrete file syntax parsing
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.core._

sealed trait KaisarDecl

/** Apply a pragma directive to the entire remainder of the file */
case class PragmaDecl(ls: PragmaSpec) extends KaisarDecl

/** Define a function, predicate, or program which can be reused across proofs */
case class LetDecl(ls: LetSym) extends KaisarDecl

/** Check a proof of a strategy and give it a name */
case class TheoremDecl(name: Ident, inPf: Statement, outPf: Statement = Triv(), conclusion: Formula = True)
    extends KaisarDecl

/** Check whether given conclusion follows from given proof */
case class ProvesDecl(thmName: Ident, conclusion: Formula) extends KaisarDecl

/** Display the already-proved conclusion of a proof */
case class ConclusionDecl(thmName: Ident) extends KaisarDecl

/** Display the synthesized strategy resulting from an already-proved proof. */
case class SynthesizeDecl(thmName: Ident) extends KaisarDecl

/** List of declarations evaluated sequentially */
case class Decls(dcls: List[KaisarDecl]) extends KaisarDecl
