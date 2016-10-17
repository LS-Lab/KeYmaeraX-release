/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
  * Axioms of KeYmaera X and axiomatic proof rules of KeYmaera X.
  * resulting from differential dynamic logic.
  * @note Soundness-critical: Only adopt sound axioms and sound axiomatic rules.
  * @author Andre Platzer
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
  * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
  * @note Code Review: 2016-08-17
  */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXAxiomParser

/**
  * The data base of axioms and axiomatic rules of KeYmaera X as resulting from differential dynamic logic axiomatizations.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
  * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
  * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.AxiomIndex]]]]
  */
private[core] object AxiomBase {
  /**
    * KeYmaera X Axiomatic Proof Rules.
    * @note Soundness-critical: Only return locally sound proof rules.
    * @return immutable list of locally sound axiomatic proof rules (premise, conclusion)
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
    * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
    * @author Andre Platzer
    */
  private[core] def loadAxiomaticRules : immutable.Map[String, (immutable.IndexedSeq[Sequent], Sequent)] = {
    val pany = UnitPredicational("p_", AnyArg)
    val qany = UnitPredicational("q_", AnyArg)
    val fany = UnitFunctional("f_", AnyArg, Real)
    val gany = UnitFunctional("g_", AnyArg, Real)
    val ctxf = Function("ctx_", None, Real, Bool) // predicate symbol
    // Sort of predicational is really (Real->Bool)->Bool except sort system doesn't know that type.
    val context = Function("ctx_", None, Bool, Bool) // predicational symbol
    val a = ProgramConst("a_")

    Map()
  }

  /**
    * Look up an axiom of KeYmaera X,
    * i.e. sound axioms are valid formulas of differential dynamic logic.
    * parse the axiom file and add all loaded knowledge to the axioms map.
    * @note Result of axiom parse is asserted for a decent set of axioms to remove from soundness-critical core.
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    */
  private[core] def loadAxioms: immutable.Map[String, Formula] = {
    try {
      val res = KeYmaeraXAxiomParser(loadAxiomString())
      assert(res.length == res.map(k => k._1).distinct.length, "No duplicate axiom names during parse")
      res.map(k => (k._1 -> k._2)).toMap
    } catch { case e: Exception => e.printStackTrace(); println("Problem while reading axioms " + e); sys.exit(10) }
  } ensuring(assertCheckAxiomFile _, "checking parse of axioms against expected outcomes")

  /** Redundant code checking expected form of axioms */
  private def assertCheckAxiomFile(axs : Map[String, Formula]): Boolean = {
    val x = Variable("x_", None, Real)
    val y = Variable("y_", None, Real)
    val p0 = PredOf(Function("p", None, Unit, Bool), Nothing)
    val p = Function("p", None, Real, Bool)
    val pany = UnitPredicational("p", AnyArg)
    val q0 = PredOf(Function("q", None, Unit, Bool), Nothing)
    val qany = UnitPredicational("q", AnyArg)
    val c = FuncOf(Function("c", None, Unit, Real), Nothing)
    val f0 = FuncOf(Function("f", None, Unit, Real), Nothing)
    val fany = UnitFunctional("f", AnyArg, Real)
    val gany = UnitFunctional("g", AnyArg, Real)
    val a = ProgramConst("a")
    val b = ProgramConst("b")
    val ode = DifferentialProgramConst("c", AnyArg)

    val H0 = PredOf(Function("H", None, Unit, Bool), Nothing)

    assert(axs("all instantiate") == Imply(Forall(Seq(x), PredOf(p,x)), PredOf(p,f0)), "all instantiate")
    // soundness-critical that these are for p() not for p(x) or p(||)
    assert(axs("vacuous all quantifier") == Equiv(Forall(immutable.IndexedSeq(x), p0), p0), "vacuous all quantifier")

    true
  }

  /**
    * KeYmaera X axioms,
    * i.e. sound axioms are valid formulas of differential dynamic logic.
    *
    * @note Soundness-critical: Only adopt valid formulas as axioms.
    *
    * @author Nathan Fulton
    * @author Stefan Mitsch
    * @author Jan-David Quesel
    * @author Andre Platzer
    *
    * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
    * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012."
    * @see "Andre Platzer. Dynamic logics of dynamical systems. arXiv 1205.4788, May 2012."
    * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
    * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
    */
  private[core] def loadAxiomString() : String =
"""
/**
 * FIRST-ORDER QUANTIFIER AXIOMS
 */

Axiom "all dual".
  (!\exists x_ !p(||)) <-> \forall x_ p(||)
End.

Axiom "all dual time".
  (!\exists t_ !p(||)) <-> \forall t_ p(||)
End.

Axiom /*\\foralli */ "all instantiate".
  (\forall x_ p(x_)) -> p(f())
End.

Axiom /*\\existsi */ "exists generalize".
  p(f()) -> \exists x_ p(x_)
End.

/* consequence of "all instantiate" @note generalized "all instantiate" */
Axiom "all eliminate".
  (\forall x_ p(||)) -> p(||)
End.

Axiom "exists eliminate".
  p(||) -> \exists x_ p(||)
End.

Axiom "exists dual".
  (!\forall x (!p(||))) <-> (\exists x p(||))
End.

Axiom "vacuous all quantifier".
  (\forall x_ p()) <-> p()
End.

/**
 * CONGRUENCE AXIOMS (for constant terms)
 */

Axiom "const congruence".
  s() = t() -> ctxT_(s()) = ctxT_(t())
End.

Axiom "const formula congruence".
  s() = t() -> (ctxF_(s()) <-> ctxF_(t()))
End.
"""
}
