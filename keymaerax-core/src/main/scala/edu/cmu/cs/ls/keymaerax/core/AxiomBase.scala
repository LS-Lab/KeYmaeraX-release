/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
  * Axioms of KeYmaera X and axiomatic proof rules of KeYmaera X.
  * resulting from differential dynamic logic.
  * @note Soundness-critical: Only adopt sound axioms and sound axiomatic rules.
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3380825 Differential equation invariance axiomatization]]. J. ACM. 67(1), 6:1-6:66, 2020.
  * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-94205-6_15 Uniform substitution for differential game logic]]. In Didier Galmiche, Stephan Schulz and Roberto Sebastiani, editors, Automated Reasoning, 9th International Joint Conference, IJCAR 2018, volume 10900 of LNCS, pp. 211-227. Springer 2018.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015.
  * @see Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @note Code Review: 2020-02-17
  */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import edu.cmu.cs.ls.keymaerax.Logging

import scala.collection.immutable
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.DLAxiomParser

/**
  * The data base of axioms and axiomatic rules of KeYmaera X as resulting from differential dynamic logic axiomatizations.
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3380825 Differential equation invariance axiomatization]]. J. ACM. 67(1), 6:1-6:66, 2020.
  * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3209108.3209147 Differential equation axiomatization: The impressive power of differential ghosts]]. In Anuj Dawar and Erich Grädel, editors, Proceedings of the 33rd Annual ACM/IEEE Symposium on Logic in Computer Science, LICS'18, ACM 2018.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-94205-6_15 Uniform substitution for differential game logic]]. In Didier Galmiche, Stephan Schulz and Roberto Sebastiani, editors, Automated Reasoning, 9th International Joint Conference, IJCAR 2018, volume 10900 of LNCS, pp. 211-227. Springer 2018.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015.
  * @see Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @author Andre Platzer
  * @author Yong Kiam Tan
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.Ax]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.AxIndex]]
  */
private[core] object AxiomBase extends Logging {
  /**
    * KeYmaera X Axiomatic Proof Rules.
    * @note Soundness-critical: Only return locally sound proof rules.
    * @return immutable list of locally sound axiomatic proof rules (premise, conclusion)
    * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
    * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-94205-6_15 Uniform substitution for differential game logic]]. In Didier Galmiche, Stephan Schulz and Roberto Sebastiani, editors, Automated Reasoning, 9th International Joint Conference, IJCAR 2018, volume 10900 of LNCS, pp. 211-227. Springer 2018.
    * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015.
    * @see Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
    * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
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
    val x = Variable("x_", None, Real)
    val Jany = UnitPredicational("J", AnyArg)
    Map(
      /**
        * Rule "CQ equation congruence".
        * Premise f_(||) = g_(||)
        * Conclusion ctxP_(f_(||)) <-> ctxP_(g_(||))
        * End.
        * {{{
        *      f(x)   =  g(x)
        *   --------------------- CQ
        *    c(f(x)) <-> c(g(x))
        * }}}
        * @see Figure 2 of Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
        */
      ("CQ equation congruence",
        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Equal(fany, gany)))),
          Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredOf(ctxf, fany), PredOf(ctxf, gany)))))),
      /**
        * Rule "CE congruence".
        * Premise p_(||) <-> q_(||)
        * Conclusion ctxF_(p_(||)) <-> ctxF_(q_(||))
        * End.
        * {{{
        *       p(x) <-> q(x)
        *   --------------------- CE
        *    C{p(x)} <-> C{q(x)}
        * }}}
        * @see Figure 2 of Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
        */
      ("CE congruence",
        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(pany, qany)))),
          Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredicationalOf(context, pany), PredicationalOf(context, qany)))))),
      /**
        * Rule "<> monotone".
        * Premise p(||) ==> q(||)
        * Conclusion <a;>p(||) ==> <a;>q(||)
        * End.
        * @see Figure 5 of Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
        */
      ("<> monotone",
        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(pany), immutable.IndexedSeq(qany))),
          Sequent(immutable.IndexedSeq(Diamond(a, pany)), immutable.IndexedSeq(Diamond(a, qany))))),
//      /**
//        * Rule "ind induction".
//        * Premise p(||) ==> [a;]p(||)
//        * Conclusion p(||) ==> [a*]p(||)
//        * {{{
//        *     p(x) |- [a]p(x)
//        *   --------------------- ind
//        *     p(x) |- [{a}*]p(x)
//        * }}}
//        * Interderives with FP fixpoint rule.
//        * FP is used as basis, because deriving FP from ind leads to a duplicate premise, needing list to set contraction.
//        * @see Lemma 4.1 of Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
//        * @see Lemma 7.2 and Corollary 16.1 of Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
//        */
//      ("ind induction",
//        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(a, pany)))),
//          Sequent(immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(Loop(a), pany))))),
      /**
        * Rule "FP fixpoint".
        * Premise p(||) | <a>q(||) ==> q(||)
        * Conclusion <a*>p(||) ==> q(||)
        * {{{
        *     p(x) | <a>q(x) |- q(x)
        *   ------------------------- FP
        *     <a*>p(x) |- q(x)
        * }}}
        * Justification: loops have a least-fixpoint semantics, so imply any other fixpoint q(x).
        * Interderives with ind induction rule.
        * FP is used as basis, because deriving FP from ind leads to a duplicate premise, needing list to set contraction.
        * @see Lemma 4.1 of Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
        * @see Lemma 16.11 and Corollary 16.1 of Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
        */
      ("FP fixpoint",
        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(Or(pany, Diamond(a, qany))), immutable.IndexedSeq(qany))),
          Sequent(immutable.IndexedSeq(Diamond(Loop(a), pany)), immutable.IndexedSeq(qany)))),
      /**
        * Rule "con convergence".
        * Premise: x > 0, J(||) |- <a{|x|}><x:=x-1;> J(||)
        * Conclusion:  \exists x J(||) |- <a{|x|}*>\exists x (x<=0 & J(||))
        * {{{
        *        x > 0, J(x) |- <a{|x|}>J(x-1)
        *    ---------------------------------------------------- con
        *     \exists x J(x) |- <a{|x|}*>\exists x (x<=0 & J(x))
        * }}}
        * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
        * @see Section 17.4 of Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
        */
      ("con convergence",
        (immutable.IndexedSeq(
            Sequent(immutable.IndexedSeq(Greater(x,Number(0)),Jany), immutable.IndexedSeq(Diamond(ProgramConst("a_", Except(x::Nil)), Diamond(Assign(x,Minus(x,Number(1))),Jany))))),
          Sequent(immutable.IndexedSeq(Exists(immutable.IndexedSeq(x), Jany)), immutable.IndexedSeq(Diamond(Loop(ProgramConst("a_", Except(x::Nil))), Exists(immutable.Seq(x), And(LessEqual(x, Number(0)), Jany)))))))
    )
  }

  /**
    * Look up the axioms of KeYmaera X,
    * i.e. sound axioms are valid formulas of differential dynamic logic / differential game logic.
    * Parse the axiom file and add all loaded knowledge to the axioms map.
    * @note Result of axiom parse is asserted for a decent set of axioms to remove from soundness-critical core.
    * @see [[loadAxiomString()]]
    */
  private[core] def loadAxioms: immutable.Map[String, Formula] = {
    try {
      val res = DLAxiomParser(loadAxiomString())
      insist(res.length == res.map(k => k._1).distinct.length, "No duplicate axiom names during parse of AxiomBase")
      res.map(k => (k._1 -> k._2)).toMap
    } catch { case e: Exception => logger.error("Cannot read axioms", e); println("Cannot read axioms " + e); sys.exit(10) }
  } ensuring(assertCheckAxiomFile _, "checking parse of axioms against expected outcomes")

  /** Redundant code checking expected form of axioms after parsing */
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
    val sys = SystemConst("a")
    val ode = DifferentialProgramConst("c", AnyArg)

    val H0 = PredOf(Function("H", None, Unit, Bool), Nothing)

    /**
      * HYBRID PROGRAM MODALITY AXIOMS
      */
    // @see Figure 2 of Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
    insist(axs("<> diamond") == Equiv(Not(Box(a, Not(pany))), Diamond(a, pany)), "<> diamond")
    insist(axs("[:=] assign") == Equiv(Box(Assign(x,f0), PredOf(p,x)), PredOf(p, f0)), "[:=] assign")
    insist(axs("[:=] assign equality") == Equiv(Box(Assign(x,f0), pany), Forall(Seq(x), Imply(Equal(x,f0), pany))), "[:=] assign equality")
    insist(axs("[?] test") == Equiv(Box(Test(q0), p0), Imply(q0, p0)), "[?] test")
    insist(axs("[++] choice") == Equiv(Box(Choice(a,b), pany), And(Box(a, pany), Box(b, pany))), "[++] choice")
    insist(axs("[;] compose") == Equiv(Box(Compose(a,b), pany), Box(a, Box(b, pany))), "[;] compose")
    insist(axs("[*] iterate") == Equiv(Box(Loop(a), pany), And(pany, Box(a, Box(Loop(a), pany)))), "[*] iterate")
    //@note only sound for hybrid systems not for hybrid games
    insist(axs("K modal modus ponens") == Imply(Box(sys, Imply(pany,qany)), Imply(Box(sys, pany), Box(sys, qany))), "K modal modus ponens")
    //@note could also have accepted axiom I for hybrid systems but not for hybrid games
    insist(axs("VK vacuous") == Imply(Box(a, True), Imply(p0, Box(a, p0))), "VK vacuous")

    /**
      * DIFFERENTIAL EQUATION AXIOMS
      */
    // @see Figure 3 of Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
    insist(axs("DW base") == Box(ODESystem(ode, qany), qany), "DW base")
    insist(axs("DMP differential modus ponens") == Imply(Box(ODESystem(ode, qany), Imply(qany,UnitPredicational("r",AnyArg))),
      Imply(
        Box(ODESystem(ode, UnitPredicational("r",AnyArg)), pany),
        Box(ODESystem(ode, qany), pany))), "DMP differential modus ponens")
    /* @note Generalized postcondition compared to theory as in DE differential effect (system) */
    insist(axs("DE differential effect") == Equiv(
      Box(ODESystem(AtomicODE(DifferentialSymbol(x),FuncOf(Function("f",None,Real,Real),x)), PredOf(Function("q",None,Real,Bool),x)), pany),
      Box(ODESystem(AtomicODE(DifferentialSymbol(x),FuncOf(Function("f",None,Real,Real),x)), PredOf(Function("q",None,Real,Bool),x)), Box(Assign(DifferentialSymbol(x), FuncOf(Function("f",None,Real,Real),x)), pany))), "DE differential effect")
    //@note in analogy to DE
    /* @note Completeness: reassociate needed in DifferentialProduct data structures */
    insist(axs("DE differential effect (system)") == Equiv(
      Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x),fany),ode), qany), pany),
      Box(ODESystem(DifferentialProduct(ode,AtomicODE(DifferentialSymbol(x),fany)), qany), Box(Assign(DifferentialSymbol(x), fany), pany))), "DE differential effect (system)")
    insist(axs("DI differential invariance") == Imply(Imply(qany, Box(ODESystem(ode,qany), DifferentialFormula(pany))),
      Equiv(Box(ODESystem(ode,qany),pany), Box(Test(qany),pany))), "DI differential invariance")
    insist(axs("DG differential ghost") == Equiv(
      Box(ODESystem(DifferentialProgramConst("c",Except(y::Nil)), UnitPredicational("q",Except(y::Nil))), UnitPredicational("p",Except(y::Nil))),
      Exists(Seq(y), Box(ODESystem(DifferentialProduct(DifferentialProgramConst("c",Except(y::Nil)),
        AtomicODE(DifferentialSymbol(y), Plus(Times(UnitFunctional("a",Except(y::Nil),Real), y), UnitFunctional("b",Except(y::Nil),Real)))
      ), UnitPredicational("q",Except(y::Nil))), UnitPredicational("p",Except(y::Nil))))), "DG differential ghost")
    //@note in analogy to DG
    insist(axs("DG differential ghost constant") == Equiv(
      Box(ODESystem(DifferentialProgramConst("c",Except(y::Nil)), UnitPredicational("q",Except(y::Nil))), UnitPredicational("p",Except(y::Nil))),
      Exists(Seq(y), Box(ODESystem(DifferentialProduct(DifferentialProgramConst("c",Except(y::Nil)),
        AtomicODE(DifferentialSymbol(y), UnitFunctional("b",Except(y::Nil),Real))
      ), UnitPredicational("q",Except(y::Nil))), UnitPredicational("p",Except(y::Nil))))), "DG differential ghost constant")
    //@note in analogy to remark in proof of soundness of DG
    insist(axs("DG inverse differential ghost") == Equiv(
      Box(ODESystem(DifferentialProgramConst("c",Except(y::Nil)), UnitPredicational("q",Except(y::Nil))), UnitPredicational("p",Except(y::Nil))),
      Forall(Seq(y), Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(y), Plus(Times(UnitFunctional("a",Except(y::Nil),Real), y), UnitFunctional("b",Except(y::Nil),Real))),
        DifferentialProgramConst("c",Except(y::Nil))),
        UnitPredicational("q",Except(y::Nil))), UnitPredicational("p",Except(y::Nil))))), "DG inverse differential ghost")

    /* DIFFERENTIAL AXIOMS FOR TERMS */

    insist(axs("c()' derive constant fn") == Equal(Differential(c), Number(0)), "c()' derive constant fn")
    insist(axs("+' derive sum") == Equal(Differential(Plus(fany, gany)), Plus(Differential(fany), Differential(gany))), "+' derive sum")
    insist(axs("*' derive product") == Equal(Differential(Times(fany, gany)), Plus(Times(Differential(fany), gany), Times(fany, Differential(gany)))), "*' derive product")
    /** DIFFERENTIAL FOR FORMULAS */
    insist(axs(">=' derive >=") == Equiv(DifferentialFormula(GreaterEqual(fany, gany)), GreaterEqual(Differential(fany), Differential(gany))), ">=' derive >=")
    insist(axs(">' derive >") == Equiv(DifferentialFormula(Greater(fany, gany)), GreaterEqual(Differential(fany), Differential(gany))), ">' derive >")
    insist(axs("&' derive and") == Equiv(DifferentialFormula(And(pany, qany)), And(DifferentialFormula(pany), DifferentialFormula(qany))), "&' derive and")
    insist(axs("|' derive or") == Equiv(DifferentialFormula(Or(pany, qany)), And(DifferentialFormula(pany), DifferentialFormula(qany))) || axs("|' derive or") == Imply(And(DifferentialFormula(pany), DifferentialFormula(qany)), DifferentialFormula(Or(pany, qany))), "|' derive or")
    insist(axs("x' derive var") == Equal(Differential(x), DifferentialSymbol(x)), "x' derive var")

    //insist(axs("all instantiate") == Imply(Forall(Seq(x), PredOf(p,x)), PredOf(p,f0)), "all instantiate")
    // soundness-critical that these are for p() not for p(x) or p(||)
    //insist(axs("vacuous all quantifier") == Equiv(Forall(immutable.IndexedSeq(x), p0), p0), "vacuous all quantifier")

    true
  }

  /**
    * KeYmaera X axioms,
    * i.e. sound axioms are valid formulas of differential dynamic logic / differential game logic.
    *
    * @note Soundness-critical: Only adopt valid formulas as axioms.
    *
    * @author Nathan Fulton
    * @author Stefan Mitsch
    * @author Jan-David Quesel
    * @author Andre Platzer
    * @author Yong Kiam Tan
    * @author Fabian Immler
    * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
    * @see Andre Platzer and Yong Kiam Tan. [[https://doi.org/10.1145/3380825 Differential equation invariance axiomatization]]. J. ACM. 67(1), 6:1-6:66, 2020.
    * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-94205-6_15 Uniform substitution for differential game logic]]. In Didier Galmiche, Stephan Schulz and Roberto Sebastiani, editors, Automated Reasoning, 9th International Joint Conference, IJCAR 2018, volume 10900 of LNCS, pp. 211-227. Springer 2018.
    * @see Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
    */
  private[this] def loadAxiomString() : String =
"""
Axiom "<> diamond"
  ![a;]!p(||) <-> <a;>p(||)
End.

Axiom "[:=] assign"
  [x_:=f();]p(x_) <-> p(f())
End.

Axiom "[:=] assign equality"
  [x_:=f();]p(||) <-> \forall x_ (x_=f() -> p(||))
End.

Axiom "[:=] self assign"
  [x_:=x_;]p(||) <-> p(||)
End.

Axiom "[':=] differential assign"
  [x_':=f();]p(x_') <-> p(f())
End.

Axiom "[':=] assign equality"
  [x_':=f();]p(||) <-> \forall x_' (x_'=f() -> p(||))
End.

Axiom "[':=] self assign"
  [x_':=x_';]p(||) <-> p(||)
End.

Axiom "[:*] assign nondet"
  [x_:=*;]p(||) <-> \forall x_ p(||)
End.

Axiom "[?] test"
  [?q();]p() <-> (q() -> p())
End.

Axiom "[++] choice"
  [a;++b;]p(||) <-> ([a;]p(||) & [b;]p(||))
End.

Axiom "[;] compose"
  [a;b;]p(||) <-> [a;][b;]p(||)
End.

Axiom "[*] iterate"
  [{a;}*]p(||) <-> (p(||) & [a;][{a;}*]p(||))
End.


Axiom "DW base"
  [{c&q(||)}]q(||)
/* [x'=f(x)&q(x);]q(x) THEORY */
End.

Axiom "DE differential effect"
  [{x_'=f(x_)&q(x_)}]p(||) <-> [{x_'=f(x_)&q(x_)}][x_':=f(x_);]p(||)
  /* [x'=f(x)&q(x);]p(x,x') <-> [x'=f(x)&q(x);][x':=f(x);]p(x,x')  THEORY */
End.

Axiom "DE differential effect (system)"
  /* @note Soundness: f(||) cannot have ' by data structure invariant. AtomicODE requires explicit-form so f(||) cannot have differentials/differential symbols */
  [{x_'=f(||),c&q(||)}]p(||) <-> [{c,x_'=f(||)&q(||)}][x_':=f(||);]p(||)
End.

/* @todo soundness requires only vectorial x in p(||). Already no primes in q(||). */
Axiom "DI differential invariance"
  ([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}]((p(||))'))
/* ([x'=f(x)&q(x);]p(x) <-> [?q(x);]p(x)) <- (q(x) -> [x'=f(x)&q(x);]((p(x))') THEORY */
End.

/* Differential Auxiliary / Differential Ghost */
Axiom "DG differential ghost"
  [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}]p(|y_|)
  /* [x'=f(x)&q(x);]p(x) <-> \exists y [{x'=f(x),y'=(a(x)*y)+b(x))&q(x)}]p(x) THEORY */
End.
Axiom "DG inverse differential ghost"
  [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \forall y_ [{y_'=(a(|y_|)*y_)+b(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)
  /* [{x_'=f(x_)&q(x_)}]p(x_) <-> \forall y_ [{y_'=a(x_)*y+b(x_),x_'=f(x_)&q(x_)}]p(x_) THEORY */
End.

Axiom "DG inverse differential ghost implicational"
  [{c{|y_|}&q(|y_|)}]p(|y_|) -> \forall y_ [{y_'=a(||),c{|y_|}&q(|y_|)}]p(|y_|)
End.

/* Special case of DG differential ghost that ghosts in constants which DS can remove without additional rewriting. */
Axiom "DG differential ghost constant"
  [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{c{|y_|},y_'=b(|y_|)&q(|y_|)}]p(|y_|)
End.
Axiom "DG differential ghost constant all"
  [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \forall y_ [{c{|y_|},y_'=b(|y_|)&q(|y_|)}]p(|y_|)
End.

Axiom "DS& differential equation solution"
  [{x_'=c()&q(x_)}]p(|x_'|) <-> \forall t_ (t_>=0 -> ((\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) -> [x_:=x_+(c()*t_);]p(|x_'|)))
End.

/* @todo: , commute should be derivable from this + ghost */
Axiom ", sort"
  [{c,d,e&q(||)}]p(||) <-> [{c,e,d&q(||)}]p(||)
End.

Axiom ", commute"
  [{c,d&q(||)}]p(||) <-> [{d,c&q(||)}]p(||)
End.

/* @todo soundness requires no primes in p(||) */
Axiom "DX differential skip"
  [{c&q(||)}]p(||) -> (q(||)->p(||))
End.

Axiom "D[;] differential self compose"
  [{c&q(||)}]p(||) <-> [{c&q(||)}][{c&q(||)}]p(||)
End.

Axiom "DIo open differential invariance >"
  ([{c&q(||)}]f(||)>g(||) <-> [?q(||);]f(||)>g(||)) <- (q(||) -> [{c&q(||)}](f(||)>g(||) -> (f(||)>g(||))'))
End.

Axiom "DMP differential modus ponens"
  ([{c&q(||)}]p(||) <- [{c&r(||)}]p(||)) <- [{c&q(||)}](q(||) -> r(||))
End.

Axiom "Uniq uniqueness"
  <{c&q(||)}>p(||) & <{c&r(||)}>p(||) -> <{c & q(||)&r(||)}>p(||)
End.

/* @note soundness requires no primes in f(||) (guaranteed by data structure invariant) */
Axiom "Cont continuous existence"
  h()!=0 & f(||) > 0 -> <{t_'=h(),c&f(||)>0}>t_!=g()
End.

/* @note compared to J. ACM, the following axiom
  1) is specialized to closed postconditions with f(|t_|) >= 0
  2) uses a time variable t_ instead of vectorial quantification
  @todo soundness requires no primes in f(|t_|) */
Axiom "RI& closed real induction >="
  [{c{|t_|}&q(|t_|)}]f(|t_|)>=0 <->
  (q(|t_|) ->f(|t_|)>=0) &
  [{{c{|t_|}&q(|t_|) & f(|t_|)>=0};t_:=0;}] (<{t_'=1,c{|t_|}&q(|t_|)}>t_!=0 -> <{t_'=1,c{|t_|}&f(|t_|)>=0}>t_!=0)
End.

/* @note compared to J. ACM, the following axiom uses a time variable t_ instead of vectorial quantification */
Axiom "RI& real induction"
  [{c{|s_,t_|}&q(|s_,t_|)}]p(|s_,t_|) <->
  \forall s_ [{t_'=1,c{|s_,t_|}&q(|s_,t_|)&(p(|s_,t_|)|t_=s_)}] (t_ = s_ ->
    p(|s_,t_|) &
    (<{t_'=1,c{|s_,t_|}&q(|s_,t_|)|t_=s_}>t_!=s_ -> <{t_'=1,c{|s_,t_|}&p(|s_,t_|)|t_=s_}>t_!=s_)
  )
End.

Axiom "IVT"
  <{c&q(||)}>(f(||)>=0&p(||)) -> f(||)<=0 -> <{c&q(||)}> (f(||)=0 & <{c&q(||)}>(f(||)>=0&p(||)))
  /* @note formal proof IVTaxiom in https://github.com/LS-Lab/Isabelle-dL/blob/d6ca357/Differential_Axioms2.thy
   * soundness requires f(||) to be continuous
   */
End.

Axiom "DCC"
  [{c&r(||)}](p(||)->q(||)) <- (([{c&r(||)&p(||)}]q(||)) & ([{c&r(||)}](!p(||)->[{c&r(||)}]!p(||))))
  /* @note formal proof DCCaxiom in https://github.com/LS-Lab/Isabelle-dL/blob/d6ca357/Differential_Axioms2.thy
   * differential conditional cut (e.g., (40) in https://arxiv.org/abs/1903.00153v1) */
End.

/** DIFFERENTIAL AXIOMS */

Axiom "c()' derive constant fn"
  (c())' = 0
End.

Axiom "x' derive var"
  (x_)' = x_'
End.

Axiom "-' derive neg"
  (-f(||))' = -((f(||))')
End.

Axiom "+' derive sum"
  (f(||) + g(||))' = (f(||))' + (g(||))'
End.

Axiom "-' derive minus"
  (f(||) - g(||))' = (f(||))' - (g(||))'
End.

Axiom "*' derive product"
  (f(||) * g(||))' = (f(||))'*g(||) + f(||)*(g(||))'
End.

Axiom "/' derive quotient"
  (f(||) / g(||))' = ((f(||))'*g(||) - f(||)*(g(||))') / (g(||)^2)
End.

Axiom "chain rule"
	[y_:=g(|y_|);][y_':=1;]( (f(g(|y_|)))' = (f(y_))' * (g(|y_|))' )
End.

Axiom "^' derive power"
	((f(||)^(c()))' = (c()*(f(||)^(c()-1)))*((f(||))')) <- c()!=0
End.

Axiom ">=' derive >="
  (f(||) >= g(||))' <-> ((f(||))' >= (g(||))')
End.

Axiom ">' derive >"
  (f(||) > g(||))' <-> ((f(||))' >= (g(||))')
  /* sic! easier */
End.

Axiom "&' derive and"
  (p(||) & q(||))' <-> ((p(||))' & (q(||))')
End.

Axiom "|' derive or"
  (p(||) | q(||))' <-> ((p(||))' & (q(||))')
  /* sic! yet <- */
End.

Axiom "forall' derive forall"
  (\forall x_ p(||))' <-> \forall x_ ((p(||))')
End.

Axiom "exists' derive exists"
  (\exists x_ p(||))' <-> \forall x_ ((p(||))')
  /* sic! yet <- */
End.

/** HYBRID PROGRAMS / GAMES */

Axiom "<d> dual"
  <{a;}^@>p(||) <-> !<a;>!p(||)
End.

Axiom "VK vacuous"
  (p() -> [a;]p()) <- [a;]true
End.

Axiom "[]T system"
  [a{|^@|};]true
End.

Axiom "K modal modus ponens"
  [a{|^@|};](p(||)->q(||)) -> ([a{|^@|};]p(||) -> [a{|^@|};]q(||))
End.

Axiom "I induction"
  (p(||) & [{a{|^@|};}*](p(||) -> [a{|^@|};] p(||))) -> [{a{|^@|};}*]p(||)
End.

Axiom "B Barcan"
  [a{|^@x_|};]\forall x_ p(||) <-> \forall x_ [a{|^@x_|};]p(||)
End.

/** FIRST-ORDER QUANTIFIER AXIOMS */

Axiom "all dual"
  (!\exists x_ !p(||)) <-> \forall x_ p(||)
End.

Axiom "all prime dual"
  (!\exists x_' !p(||)) <-> \forall x_' p(||)
End.

/* generalized "all instantiate" */
Axiom "all eliminate"
  (\forall x_ p(||)) -> p(||)
End.
Axiom "all eliminate prime"
  (\forall x_' p(||)) -> p(||)
End.
"""
}
