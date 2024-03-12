/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Ad-hoc library of CdGL tactics.
 * @TODO:
 *   Revisit design when library gets bigger
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.cdgl.Proof._
import edu.cmu.cs.ls.keymaerax.core._
import scala.collection.immutable

object TermTactics {
  def compareConstant(f: Term, g: Term, k: Number): Proof = {
    if (k.value <= 0) throw ProofException(s"ConstSplit expects positive k, got ${k.value}")
    Compare(f, g, QE(Greater(k, Number(0)), Triv()))
  }

  def and(args: Proof*): Proof = { args.reduce(AndI) }

  def and(i: Int): Proof = { List.tabulate(i)(i => Hyp(i)).reduce(AndI) }

  def and(G: Context): Proof = { and(G.asIndexedSeq.length) }
}
