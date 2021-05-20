/*
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * Source AST equality for proofs which ignores metadata and line numbers
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import org.scalactic._

object ProofEquality extends Equality[Statement] {
  override def areEqual(a: Statement, b: Any): Boolean = {
    if(!b.isInstanceOf[Statement]) return false
    (a, b) match {
      case (Triv(), Triv()) => true
      case (Assume(pat, f), Assume(patR, fR)) => pat == patR && f == fR
      case (Assert(pat, f, m), Assert(patR, fR, mR)) => pat == patR && f == fR && m == mR
      case (Modify(ids, mods), Modify(idsR, modsR)) => ids == idsR && mods == modsR
      case (Label(st, snapshot), Label(stR, snapshotR))  => st == stR
      case (Note(x, proof, annotation), Note(xR, proofR, annotationR)) => x == xR && proof == proofR
      case (LetSym(f, args, e), LetSym(fR, argsR, eR)) => f == fR && args == argsR && e == eR
      case (Match(pat, e), Match(patR, eR)) => pat == patR && e == eR
      case (Block(ss), Block(ssR)) if ss.length == ssR.length =>
        ss.zip(ssR).forall({case (l, r) => areEqual(l, r)})
      case (Switch(scrutinee, pats), Switch(scrutineeR, patsR)) if scrutinee == scrutineeR && pats.length == patsR.length =>
        pats.zip(patsR).forall({case ((x, f, b), (xr, fr, br)) => x == xr && f == fr && areEqual(b, br)})
      case (BoxChoice(ll, lr), BoxChoice(rl, rr)) => areEqual(ll, rl) && areEqual(lr, rr)
      case (For(metX, met0, metIncr, conv, guard, body, ge), For(metXR, met0R, metIncrR, convR, guardR, bodyR, geR)) =>
        metX == metXR && met0 == met0R && metIncr == metIncrR && conv == convR && guard == guardR && areEqual(body, bodyR) && ge == geR
      case (While(x, j, s), While(xr, jr, sr)) => x == xr && j == jr && areEqual(s, sr)
      case (BoxLoop(s, ih), BoxLoop(sr, ihr)) => areEqual(s, sr)
      case (Ghost(s), Ghost(sr)) => areEqual(s, sr)
      case (InverseGhost(s), InverseGhost(sr)) => areEqual(s, sr)
      case (ProveODE(ds, dc), ProveODE(dsR, dcR)) => ds == dsR && dc == dcR
      case (Was(now, was), r) => areEqual(now, r)
      case (l, Was(now, was)) => areEqual(l, now)
      case (m: MetaNode, mr: MetaNode) => m == mr
      case _ => a == b
    }
  }
}
