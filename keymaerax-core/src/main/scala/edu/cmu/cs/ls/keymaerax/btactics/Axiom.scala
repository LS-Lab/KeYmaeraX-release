/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable

/** Finite list of axioms retrieved from the prover core. */
@deprecated("Use Provable.axioms etc directly instead")
object Axiom {
  /** immutable list of sound axioms, i.e., valid formulas of differential dynamic logic. */
  @deprecated("Use Provable.axiom instead")
  val axioms: immutable.Map[String, Formula] = Provable.axiom

  /** A Provable proving the axiom named `id` */
  @deprecated("Use Provable.axioms instead")
  def apply(id: String): Provable = Provable.axioms(id)
   //throw new CoreException("Axiom " + id + " does not exist in:\n" + Axiom.axioms.mkString("\n"))

  @deprecated("Use Provable.axioms instead")
  def axiom(id: String): Provable = apply(id)
}

/** Finite list of axiomatic rules. */
@deprecated("Use Provable.rules instead")
object AxiomaticRule {
  /** immutable list of locally sound axiomatic proof rules (premises, conclusion) */
  @deprecated("Use Provable.rules instead")
  val rules: immutable.Map[String, Provable] = Provable.rules
  /**
    * Obtain the axiomatic proof rule called `id`.
    * That is, the locally sound Provable representing the axiomatic rule of name `id`.
    * All available axiomatic rules are listed in [[edu.cmu.cs.ls.keymaerax.core.AxiomaticRule.rules]]
    *
    * @author Andre Platzer
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    */
  @deprecated("May want to use Provable.rules instead?")
  def apply(id: String): Provable = Provable.rules(id)
  //  case _ => throw new CoreException("Axiomatic Rule " + id + " does not exist in:\n" + AxiomaticRule.rules.mkString("\n"))

  /**
    * A uniform substitution instance of an axiomatic proof rule,
    * i.e. locally sound proof rules that are represented by a pair of concrete formulas, one for the premise and one for the conclusion.
    * Axiomatic proof rules are employed after forming their uniform substitution instances.
    * All available axiomatic rules are listed in [[edu.cmu.cs.ls.keymaerax.core.AxiomaticRule.rules]]
    * Returns the instantied axiomatic rule as a Provable:
    * {{{
    *    s(G1) |- s(D1) ... s(Gn) |- s(Dn)
    *   ----------------------------------
    *               s(G) |- s(D)
    * }}}
    *
    * @param id the name of the axiomatic rule to use, which identifies some rule
    * {{{
    *    G1 |- D1 ... Gn |- Dn
    *   ----------------------------------
    *            G |- D
    * }}}
    * @param subst the substitution `s` to use to instantiate axiomatic rule called `id`.
    * @author Andre Platzer
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    */
  @deprecated("Use Provable.rules(id)(subst) instead.")
  def apply(id: String, subst: USubst): Provable = apply(id)(subst)
}
