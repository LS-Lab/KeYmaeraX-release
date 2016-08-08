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
 * @note Code Review: 2016-03-09
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
       */
      ("CE congruence",
        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(pany, qany)))),
          Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredicationalOf(context, pany), PredicationalOf(context, qany)))))),
      /**
       * Rule "<> monotone".
       * Premise p(||) ==> q(||)
       * Conclusion <a;>p(||) ==> <a;>q(||)
       * End.
       * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
       */
      ("<> monotone",
        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(pany), immutable.IndexedSeq(qany))),
          Sequent(immutable.IndexedSeq(Diamond(a, pany)), immutable.IndexedSeq(Diamond(a, qany))))),
      /**
       * Rule "ind induction".
       * Premise p(||) ==> [a;]p(||)
       * Conclusion p(||) ==> [a*]p(||)
       * {{{
       *     p(x) |- [a]p(x)
       *   --------------------- ind
       *     p(x) |- [{a}*]p(x)
       * }}}
       * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 17(1), 2015.  Lemma 4.1"
       */
      ("ind induction",
        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(a, pany)))),
          Sequent(immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(Loop(a), pany))))),
      /* UNSOUND FOR HYBRID GAMES */
      /**
       * Rule "Goedel".
       * Premise p(||)
       * Conclusion [a;]p(||)
       * End.
       * {{{
       *       p(||)
       *   ----------- G
       *    [a;]p(||)
       * }}}
       * @NOTE Unsound for hybrid games
       * @TODO Add [a;]true -> to conclusion to make it sound for hybrid games (and then equivalent to [] monotone)
       */
      ("Goedel",
        (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(pany))),
          Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(Box(a, pany)))))
    )
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
  private def assertCheckAxiomFile(axs : Map[String, Formula]) = {
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

    /**
     * HYBRID PROGRAM MODALITY AXIOMS
     */
    // Figure 2
    assert(axs("<> diamond") == Equiv(Not(Box(a, Not(pany))), Diamond(a, pany)), "<> diamond")
    assert(axs("[:=] assign") == Equiv(Box(Assign(x,f0), PredOf(p,x)), PredOf(p, f0)), "[:=] assign")
    assert(axs("[:=] assign equality") == Equiv(Box(Assign(x,f0), pany), Forall(Seq(x), Imply(Equal(x,f0), pany))), "[:=] assign equality")
    assert(axs("[?] test") == Equiv(Box(Test(q0), p0), Imply(q0, p0)), "[?] test")
    assert(axs("[++] choice") == Equiv(Box(Choice(a,b), pany), And(Box(a, pany), Box(b, pany))), "[++] choice")
    assert(axs("[;] compose") == Equiv(Box(Compose(a,b), pany), Box(a, Box(b, pany))), "[;] compose")
    assert(axs("[*] iterate") == Equiv(Box(Loop(a), pany), And(pany, Box(a, Box(Loop(a), pany)))), "[*] iterate")
    //@note only sound for hybrid systems not for hybrid games
    assert(axs("K modal modus ponens") == Imply(Box(a, Imply(pany,qany)), Imply(Box(a, pany), Box(a, qany))), "K modal modus ponens")
    //@note could also have accepted axiom I for hybrid systems but not for hybrid games
    assert(axs("V vacuous") == Imply(p0, Box(a, p0)), "V vacuous")

    /**
     * DIFFERENTIAL EQUATION AXIOMS
     */
    // Figure 3
    assert(axs("DW") == Box(ODESystem(ode, qany), qany), "DW")
    assert(axs("DC differential cut") == Imply(Box(ODESystem(ode, qany), UnitPredicational("r",AnyArg)),
      Equiv(Box(ODESystem(ode, qany), pany),
        Box(ODESystem(ode, And(qany,UnitPredicational("r",AnyArg))), pany))), "DC differential cut")
    /* @note Generalized postcondition compared to theory as in DE differential effect (system) */
    assert(axs("DE differential effect") == Equiv(
      Box(ODESystem(AtomicODE(DifferentialSymbol(x),FuncOf(Function("f",None,Real,Real),x)), PredOf(Function("q",None,Real,Bool),x)), pany),
      Box(ODESystem(AtomicODE(DifferentialSymbol(x),FuncOf(Function("f",None,Real,Real),x)), PredOf(Function("q",None,Real,Bool),x)), Box(DiffAssign(DifferentialSymbol(x), FuncOf(Function("f",None,Real,Real),x)), pany))
    ), "DE differential effect")
    //@note in analogy to DE
    /* @note Completeness: reassociate needed in DifferentialProduct data structures */
    assert(axs("DE differential effect (system)") == Equiv(
      Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x),fany),ode), qany), pany),
      Box(ODESystem(DifferentialProduct(ode,AtomicODE(DifferentialSymbol(x),fany)), qany), Box(DiffAssign(DifferentialSymbol(x), fany), pany))
    ), "DE differential effect (system)")
    assert(axs("DI differential invariance") == Imply(Imply(qany, Box(ODESystem(ode,qany), DifferentialFormula(pany))),
      Equiv(Box(ODESystem(ode,qany),pany), Box(Test(qany),pany))), "DI differential invariance")
    assert(axs("DG differential ghost") == Equiv(
      Box(ODESystem(DifferentialProgramConst("c",Except(y)), UnitPredicational("q",Except(y))), UnitPredicational("p",Except(y))),
      Exists(Seq(y), Box(ODESystem(DifferentialProduct(DifferentialProgramConst("c",Except(y)),
        AtomicODE(DifferentialSymbol(y), Plus(Times(UnitFunctional("a",Except(y),Real), y), UnitFunctional("b",Except(y),Real)))
      ), UnitPredicational("q",Except(y))), UnitPredicational("p",Except(y))))
    ), "DG differential ghost")
    //@note in analogy to DG
    assert(axs("DG differential ghost constant") == Equiv(
      Box(ODESystem(DifferentialProgramConst("c",Except(y)), UnitPredicational("q",Except(y))), UnitPredicational("p",Except(y))),
      Exists(Seq(y), Box(ODESystem(DifferentialProduct(DifferentialProgramConst("c",Except(y)),
        AtomicODE(DifferentialSymbol(y), UnitFunctional("g",Except(y),Real))
      ), UnitPredicational("q",Except(y))), UnitPredicational("p",Except(y))))
    ), "DG differential ghost constant")
    //@note in analogy to remark in proof of soundness of DG
    assert(axs("DG inverse differential ghost system") == Imply(
      Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(x),UnitFunctional("f",Except(y),Real)),DifferentialProgramConst("c",Except(y))), UnitPredicational("q",Except(y))), UnitPredicational("p",Except(y))),
      Forall(Seq(y), Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(y), gany),
        DifferentialProduct(AtomicODE(DifferentialSymbol(x),UnitFunctional("f",Except(y),Real)),DifferentialProgramConst("c",Except(y))
        )), UnitPredicational("q",Except(y))), UnitPredicational("p",Except(y))))
    ), "DG inverse differential ghost system")
    //@note in analogy to remark in proof of soundness of DG
    assert(axs("DG inverse differential ghost") == Imply(
      Box(ODESystem(AtomicODE(DifferentialSymbol(x),UnitFunctional("f",Except(y),Real)), UnitPredicational("q",Except(y))), UnitPredicational("p",Except(y))),
      Forall(Seq(y), Box(ODESystem(DifferentialProduct(AtomicODE(DifferentialSymbol(y), gany),
        AtomicODE(DifferentialSymbol(x),UnitFunctional("f",Except(y),Real))
      ), UnitPredicational("q",Except(y))), UnitPredicational("p",Except(y))))
    ), "DG inverse differential ghost")

    /* DIFFERENTIAL AXIOMS FOR TERMS */

    assert(axs("c()' derive constant fn") == Equal(Differential(c), Number(0)), "c()' derive constant fn")
    assert(axs("+' derive sum") == Equal(Differential(Plus(fany, gany)), Plus(Differential(fany), Differential(gany))), "+' derive sum")
    assert(axs("-' derive minus") == Equal(Differential(Minus(fany, gany)), Minus(Differential(fany), Differential(gany))), "-' derive minus")
    assert(axs("*' derive product") == Equal(Differential(Times(fany, gany)), Plus(Times(Differential(fany), gany), Times(fany, Differential(gany)))), "*' derive product")
    /** DIFFERENTIAL FOR FORMULAS */
    assert(axs("!=' derive !=") == Equiv(DifferentialFormula(NotEqual(fany, gany)), Equal(Differential(fany), Differential(gany))), "!=' derive !=")
    assert(axs("&' derive and") == Equiv(DifferentialFormula(And(pany, qany)), And(DifferentialFormula(pany), DifferentialFormula(qany))), "&' derive and")
    assert(axs("|' derive or") == Equiv(DifferentialFormula(Or(pany, qany)), And(DifferentialFormula(pany), DifferentialFormula(qany))) || axs("|' derive or") == Imply(And(DifferentialFormula(pany), DifferentialFormula(qany)), DifferentialFormula(Or(pany, qany))), "|' derive or")
    assert(axs("x' derive var") == Equal(Differential(x), DifferentialSymbol(x)), "x' derive var")

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
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
   * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012."
   * @see "Andre Platzer. Dynamic logics of dynamical systems. arXiv 1205.4788, May 2012."
   * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
   */
  private[core] def loadAxiomString() : String =
"""
Axiom "<> diamond".
  ![a;]!p(||) <-> <a;>p(||)
End.

Axiom "[:=] assign".
  [x_:=f();]p(x_) <-> p(f())
End.

Axiom "[:=] assign equality".
  [x_:=f();]p(||) <-> \forall x_ (x_=f() -> p(||))
End.

Axiom "[:=] assign equality exists".
  [x_:=f();]p(||) <-> \exists x_ (x_=f() & p(||))
End.

Axiom "[:=] self assign".
  [x_:=x_;]p(||) <-> p(||)
End.

Axiom "[':=] differential assign".
  [x_':=f();]p(x_') <-> p(f())
End.

Axiom "[:*] assign nondet".
  [x_:=*;]p(||) <-> \forall x_ p(||)
End.

Axiom "[?] test".
  [?q();]p() <-> (q() -> p())
End.

Axiom "[++] choice".
  [a;++b;]p(||) <-> ([a;]p(||) & [b;]p(||))
End.

Axiom "[;] compose".
  [a;b;]p(||) <-> [a;][b;]p(||)
End.

Axiom "[*] iterate".
  [{a;}*]p(||) <-> (p(||) & [a;][{a;}*]p(||))
End.


Axiom "DW".
  [{c&q(||)}]q(||)
/* [x'=f(x)&q(x);]q(x) THEORY */
End.

Axiom "DC differential cut".
  ([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)
/* ([x'=f(x)&q(x);]p(x) <-> [x'=f(x)&(q(x)&r(x));]p(x)) <- [x'=f(x)&q(x);]r(x) THEORY */
End.

Axiom "DE differential effect".
  /* [x'=f(x)&q(x);]p(x,x') <-> [x'=f(x)&q(x);][x':=f(x);]p(x,x')  THEORY */
  [{x_'=f(x_)&q(x_)}]p(||) <-> [{x_'=f(x_)&q(x_)}][x_':=f(x_);]p(||)
End.

Axiom "DE differential effect (system)".
  /* @note Soundness: f(||) cannot have ' by data structure invariant. AtomicODE requires explicit-form so f(||) cannot have differentials/differential symbols */
  [{x_'=f(||),c&q(||)}]p(||) <-> [{c,x_'=f(||)&q(||)}][x_':=f(||);]p(||)
End.

Axiom "DI differential invariance".
  ([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}](p(||)'))
/* ([x'=f(x)&q(x);]p(x) <-> [?q(x);]p(x)) <- (q(x) -> [x'=f(x)&q(x);]((p(x))') THEORY */
End.

/* Differential Auxiliary / Differential Ghost */
Axiom "DG differential ghost".
  [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}]p(|y_|)
  /* [x'=f(x)&q(x);]p(x) <-> \exists y [{x'=f(x),y'=(a(x)*y)+b(x))&q(x)}]p(x) THEORY */
End.

/* Special case of DG differential ghost that ghosts in constants which DS can remove without additional rewriting. */
Axiom "DG differential ghost constant".
  [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{c{|y_|},y_'=g(|y_|)&q(|y_|)}]p(|y_|)
End.

Axiom "DG inverse differential ghost system".
  [{x_'=f(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)  ->  \forall y_ [{y_'=g(||),x_'=f(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)
End.

Axiom "DG inverse differential ghost".
  /* [{x_'=f(x_)&q(x_)}]p(x_)  ->  \forall y_ [{y_'=g(||),x_'=f(x_)&q(x_)}]p(x_) */
  [{x_'=f(|y_|)&q(|y_|)}]p(|y_|)  ->  \forall y_ [{y_'=g(||),x_'=f(|y_|)&q(|y_|)}]p(|y_|)
End.

/* Formatter axioms for diff eqs. */
Axiom ", commute".
  [{c,d&q(||)}]p(||) <-> [{d,c&q(||)}]p(||)
End.

Axiom "DS& differential equation solution".
  [{x_'=c()&q(x_)}]p(||) <-> \forall t_ (t_>=0 -> ((\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) -> [x_:=x_+(c()*t_);]p(||)))
End.

/** @Derived from DW (not implementable for technical reasons - abstraction of c, ??) */
Axiom "DX differential skip".
  [{c&q(||)}]p(||) -> (q(||)->p(||))
End.


Axiom "c()' derive constant fn".
  c()' = 0
End.

Axiom "x' derive var".
  (x_)' = x_'
End.

Axiom "-' derive neg".
  (-f(||))' = -((f(||))')
End.

Axiom "+' derive sum".
  (f(||) + g(||))' = ((f(||))') + ((g(||))')
End.

Axiom "-' derive minus".
  (f(||) - g(||))' = ((f(||))') - ((g(||))')
End.

Axiom "*' derive product".
  (f(||) * g(||))' = (((f(||))')*g(||)) + (f(||)*((g(||))'))
End.

Axiom "/' derive quotient".
  (f(||) / g(||))' = ((((f(||))')*g(||)) - (f(||)*((g(||))'))) / (g(||)^2)
End.

Axiom "chain rule".
	[y_:=g(x_);][y_':=1;]( (f(g(x_)))' = ((f(y_))') * ((g(x_))') )
End.

Axiom "^' derive power".
	((f(||)^(c()))' = (c()*(f(||)^(c()-1)))*((f(||))')) <- (c() != 0)
End.

Axiom "=' derive =".
  (f(||) = g(||))' <-> ((f(||)') = (g(||)'))
End.

Axiom ">=' derive >=".
  (f(||) >= g(||))' <-> ((f(||)') >= (g(||)'))
End.

Axiom ">' derive >".
  (f(||) > g(||))' <-> ((f(||)') >= (g(||)'))
  /* sic! easier */
End.

Axiom "<=' derive <=".
  (f(||) <= g(||))' <-> ((f(||)') <= (g(||)'))
End.

Axiom "<' derive <".
  (f(||) < g(||))' <-> ((f(||)') <= (g(||)'))
  /* sic! easier */
End.

Axiom "!=' derive !=".
  (f(||) != g(||))' <-> ((f(||)') = (g(||)'))
  /* sic! */
End.

Axiom "&' derive and".
  (p(||) & q(||))' <-> ((p(||)') & (q(||)'))
End.

Axiom "|' derive or".
  (p(||) | q(||))' <-> ((p(||)') & (q(||)'))
  /* sic! yet <- */
End.

Axiom "forall' derive forall".
  (\forall x_ p(||))' <-> (\forall x_ (p(||)'))
End.

Axiom "exists' derive exists".
  (\exists x_ p(||))' <-> (\forall x_ (p(||)'))
  /* sic! yet <- */
End.

/** EXCLUSIVELY FOR HYBRID PROGRAMS. UNSOUND FOR HYBRID GAMES. */

/* @NOTE requires removing axioms unsound for hybrid games */
/*Axiom "<d> dual".
  <{a;}^d>p(||) <-> !<a;>!p(||)
  <{a;}^@>p(||) <-> !<a;>!p(||)
End.*/

/* @NOTE Unsound for hybrid games */
Axiom "V vacuous".
  p() -> [a;]p()
  /* @TODO (p() -> [a;]p()) <- [a;]true sound for hybrid games */
End.

/* @NOTE Unsound for hybrid games */
Axiom "K modal modus ponens".
  [a;](p(||)->q(||)) -> (([a;]p(||)) -> ([a;]q(||)))
End.

/* @NOTE Unsound for hybrid games, use ind induction rule instead */
Axiom "I induction".
  /*@TODO Drop or Use this form instead? which is possibly more helpful: ([{a;}*](p(||) -> [a;] p(||))) -> (p(||) -> [{a;}*]p(||)) THEORY */
  (p(||) & [{a;}*](p(||) -> [a;] p(||))) -> [{a;}*]p(||)
End.

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

/* consequence of "all instantiate" @note generalized "all instantiate" */
Axiom "all eliminate".
  (\forall x_ p(||)) -> p(||)
End.

Axiom "exists eliminate".
  p(||) -> \exists x_ p(||)
End.

Axiom "vacuous all quantifier".
  (\forall x_ p()) <-> p()
End.

/**
 * CONGRUENCE AXIOMS (for constant terms)
 */

Axiom "const congruence".
  (s() = t()) -> (ctxT_(s()) = ctxT_(t()))
End.

Axiom "const formula congruence".
  (s() = t()) -> (ctxF_(s()) <-> ctxF_(t()))
End.
"""
}
