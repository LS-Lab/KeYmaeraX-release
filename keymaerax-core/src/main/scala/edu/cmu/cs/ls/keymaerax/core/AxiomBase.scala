/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Axioms of KeYmaera X and axiomatic proof rules of KeYmaera X.
 * resulting from differential dynamic logic.
 * @note Soundness-critical: Only adopt sound axioms and sound axiomatic rules.
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
 * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @note Code Review: 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXAxiomParser

/**
 * The data base of axioms and axiomatic rules of KeYmaera X as resulting from differential dynamic logic axiomatizations.
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.DerivedAxioms]]
 */
private[core] object AxiomBase {
  /**
   * KeYmaera X Axiomatic Proof Rules.
   * @note Soundness-critical: Only return locally sound proof rules.
   * @return immutable list of locally sound axiomatic proof rules (premise, conclusion)
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
   * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @author Andre Platzer
   */
  private[core] def loadAxiomaticRules() : immutable.Map[String, (Sequent, Sequent)] = {
    val x = Variable("x_", None, Real)
    val pany = PredOf(Function("p_", None, Real, Bool), Anything)
    val qany = PredOf(Function("q_", None, Real, Bool), Anything)
    val fany = FuncOf(Function("f_", None, Real, Real), Anything)
    val gany = FuncOf(Function("g_", None, Real, Real), Anything)
    val ctxt = Function("ctx_", None, Real, Real) // function symbol
    val ctxf = Function("ctx_", None, Real, Bool) // predicate symbol
    // Sort of predicational is really (Real->Bool)->Bool except sort system doesn't know that type.
    val context = Function("ctx_", None, Bool, Bool) // predicational symbol
    val a = ProgramConst("a_")

    Map(
      /**
       * Rule "all generalization".
       * Premise p(x)
       * Conclusion \forall x p(x)
       * End.
       */
      /*("all generalization",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(px)),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Forall(Seq(x), px))))),*/
      /**
       * Rule "all generalization".
       * Premise p(??)
       * Conclusion \forall x p(??)
       * End.
       * @Note generalization of p(x) to p(??) as in Theorem 14
       */
      ("all generalization",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(pany)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Forall(immutable.Seq(x), pany))))),
      /**
       * Rule "CT term congruence".
       * Premise f_(??) = g_(??)
       * Conclusion ctxT_(f_(??)) = ctxT_(g_(??))
       * End.
       * @derived ("Could also use CQ equation congruence with p(.)=(ctx_(.)=ctx_(g_(x))) and reflexivity of = instead.")
       */
      ("CT term congruence",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(fany, gany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(FuncOf(ctxt, fany), FuncOf(ctxt, gany)))))),
      /**
       * Rule "CQ equation congruence".
       * Premise f_(??) = g_(??)
       * Conclusion ctxP_(f_(??)) <-> ctxP_(g_(??))
       * End.
       */
      ("CQ equation congruence",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(fany, gany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredOf(ctxf, fany), PredOf(ctxf, gany)))))),
      /**
       * Rule "CE congruence".
       * Premise p_(??) <-> q_(??)
       * Conclusion ctxF_(p_(??)) <-> ctxF_(q_(??))
       * End.
       */
      ("CE congruence",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(pany, qany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredicationalOf(context, pany), PredicationalOf(context, qany)))))),
      /**
       * Rule "CE congruence".
       * Premise p_(??) <-> q_(??)
       * Conclusion ctxF_(p_(??)) |- ctxF_(q_(??))
       * End.
       * @derived EquivifyRight, cut, prop
       */
      ("CO one-sided congruence",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(pany, qany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(PredicationalOf(context, pany)), immutable.IndexedSeq(PredicationalOf(context, qany))))),
      /**
       * Rule "[] monotone".
       * Premise p(??) ==> q(??)
       * Conclusion [a;]p(??) ==> [a;]q(??)
       * End.
       * @derived useAt("<> dual") & by("<> monotone")
       * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
       */
      ("[] monotone",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(qany)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(Box(a, pany)), immutable.IndexedSeq(Box(a, qany))))),
      /**
       * Rule "<> monotone".
       * Premise p(??) ==> q(??)
       * Conclusion <a;>p(??) ==> <a;>q(??)
       * End.
       * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
       */
      ("<> monotone",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(qany)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(Diamond(a, pany)), immutable.IndexedSeq(Diamond(a, qany))))),
      /**
       * Rule "ind induction".
       * Premise p(??) ==> [a;]p(??)
       * Conclusion p(??) ==> [a*]p(??)
       * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
       */
      ("ind induction",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(a, pany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(Loop(a), pany))))),
      /* UNSOUND FOR HYBRID GAMES */
      /**
       * Rule "Goedel".
       * Premise p(??)
       * Conclusion [a;]p(??)
       * End.
       * @NOTE Unsound for hybrid games
       * @TODO Add [a;]true -> to conclusion to make it sound for hybrid games (and then equivalent to [] monotone)
       */
      ("Goedel",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(pany)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Box(a, pany)))))
    )
  }

  /**
   * Look up an axiom of KeYmaera X,
   * i.e. sound axioms are valid formulas of differential dynamic logic.
   * parse the axiom file and add all loaded knowledge to the axioms map.
   * @note Result of axiom parse is asserted for a decent set of axioms to remove from soundness-critical core.
   */
  private[core] def loadAxioms: immutable.Map[String, Formula] = {
    try {
      //Code for old parser:
//      val parser = new KeYmaeraParser(enabledLogging = false)
//      val alp = parser.ProofFileParser
//      val res = alp.runParser(loadAxiomString())
      val res = KeYmaeraXAxiomParser(loadAxiomString())

      assert(res.length == res.map(k => k._1).distinct.length, "No duplicate axiom names during parse")

      res.map(k => (k._1 -> k._2)).toMap
    } catch { case e: Exception => e.printStackTrace(); println("Problem while reading axioms " + e); sys.exit(10) }
  } ensuring(assertCheckAxiomFile _, "checking parse of axioms against expected outcomes")

  /** Redundant code checking expected form of axioms */
  private def assertCheckAxiomFile(axs : Map[String, Formula]) = {
    val x = Variable("x", None, Real)
    val x_ = Variable("x_", None, Real)
    val xp = DifferentialSymbol(x)
    val p0 = PredOf(Function("p", None, Unit, Bool), Nothing)
    val p = Function("p", None, Real, Bool)
    val pany = PredOf(p, Anything)
    val q = Function("q", None, Real, Bool)
    val q0 = PredOf(Function("q", None, Unit, Bool), Nothing)
    val qany = PredOf(Function("q", None, Real, Bool), Anything)
    val r = Function("r", None, Real, Bool)
    val c = FuncOf(Function("c", None, Unit, Real), Nothing)
    val f = Function("f", None, Real, Real)
    val f0 = FuncOf(Function("f", None, Unit, Real), Nothing)
    val fany = FuncOf(Function("f", None, Real, Real), Anything)
    val g0 = FuncOf(Function("g", None, Unit, Real), Nothing)
    val gany = FuncOf(Function("g", None, Real, Real), Anything)
    val h0 = FuncOf(Function("h", None, Unit, Real), Nothing)
    val t0 = FuncOf(Function("t", None, Unit, Real), Nothing)
    val a = ProgramConst("a")
    val b = ProgramConst("b")

    val v = Variable("v", None, Real)
    val H0 = PredOf(Function("H", None, Unit, Bool), Nothing)

    // Figure 2
    assert(axs("<> dual") == Equiv(Not(Box(a, Not(pany))), Diamond(a, pany)), "<> dual")
    assert(axs("[:=] assign") == Equiv(Box(Assign(x,f0), PredOf(p,x)), PredOf(p, f0))
      || axs("[:=] assign") == Equiv(Box(Assign(v,t0), PredOf(p,v)), PredOf(p, t0)), "[:=] assign")
    assert(axs("[?] test") == Equiv(Box(Test(q0), p0), Imply(q0, p0))
      || axs("[?] test") == Equiv(Box(Test(H0), p0), Imply(H0, p0)), "[?] test")
    assert(axs("[++] choice") == Equiv(Box(Choice(a,b), pany), And(Box(a, pany), Box(b, pany))), "[++] choice")
    assert(axs("[;] compose") == Equiv(Box(Compose(a,b), pany), Box(a, Box(b, pany))), "[;] compose")
    assert(axs("[*] iterate") == Equiv(Box(Loop(a), pany), And(pany, Box(a, Box(Loop(a), pany)))), "[*] iterate")
    //@note only sound for hybrid systems not for hybrid games
    assert(axs("K modal modus ponens") == Imply(Box(a, Imply(pany,qany)), Imply(Box(a, pany), Box(a, qany))), "K modal modus ponens")
    //@note could also have accepted axiom I for hybrid systems but not for hybrid games
    assert(axs("V vacuous") == Imply(p0, Box(a, p0)), "V vacuous")

    // Figure 3
   /* assert(axs("DC differential cut") == Imply(Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), PredOf(q,x)), PredOf(r,x)),
      Equiv(Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), PredOf(q,x)), PredOf(p,x)),
        Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), And(PredOf(q,x), PredOf(r,x))), PredOf(p,x)))), "DC differential cut") */

    assert(axs("c()' derive constant fn") == Equal(Differential(c), Number(0)), "c()' derive constant fn")
    assert(axs("+' derive sum") == Equal(Differential(Plus(fany, gany)), Plus(Differential(fany), Differential(gany))), "+' derive sum")
    assert(axs("-' derive minus") == Equal(Differential(Minus(fany, gany)), Minus(Differential(fany), Differential(gany))), "-' derive minus")
    assert(axs("*' derive product") == Equal(Differential(Times(fany, gany)), Plus(Times(Differential(fany), gany), Times(fany, Differential(gany)))), "*' derive product")
    assert(axs("!=' derive !=") == Equiv(DifferentialFormula(NotEqual(fany, gany)), Equal(Differential(fany), Differential(gany))), "!=' derive !=")
    assert(axs("&' derive and") == Equiv(DifferentialFormula(And(pany, qany)), And(DifferentialFormula(pany), DifferentialFormula(qany))), "&' derive and")
    assert(axs("|' derive or") == Equiv(DifferentialFormula(Or(pany, qany)), And(DifferentialFormula(pany), DifferentialFormula(qany))) || axs("|' derive or") == Imply(And(DifferentialFormula(pany), DifferentialFormula(qany)), DifferentialFormula(Or(pany, qany))), "|' derive or")
    assert(axs("x' derive var") == Equal(Differential(x_), DifferentialSymbol(x_)), "x' derive var")
    //assert(axs("x' derive variable") == Forall(immutable.Seq(x_), Equal(Differential(x_), DifferentialSymbol(x_))), "x' derive variable")

    assert(axs("all instantiate") == Imply(Forall(Seq(x), PredOf(p,x)), PredOf(p,t0)), "all instantiate")
    // soundness-critical that these are for p() not for p(x) or p(??)
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
   * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
   */
  private[core] def loadAxiomString() : String =
"""
Variables.
End.

/**
 * FIRST-ORDER QUANTIFIER AXIOMS
 */
Axiom /*\\foralli */ "all instantiate".
  (\forall x p(x)) -> p(t())
End.

/* consequence of "all instantiate" @note generalized "all instantiate" */
Axiom "all eliminate".
  (\forall x p(??)) -> p(??)
End.

Axiom "vacuous all quantifier".
  (\forall x p()) <-> p()
End.

Axiom "all dual".
  (!\exists x (!p(x))) <-> (\forall x p(x))
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


/**
 * HYBRID PROGRAM MODALITIES
 */

Axiom "<> dual".
  (![a;](!p(??))) <-> <a;>p(??)
End.

Axiom "[:=] assign".
  [v:=t();]p(v) <-> p(t())
End.

Axiom "[':=] differential assign".
  [v':=t();]p(v') <-> p(t())
End.

Axiom "[:*] assign nondet".
  [x:=*;]p(x) <-> (\forall x p(x))
End.

Axiom "[?] test".
  [?H();]p() <-> (H() -> p())
End.

Axiom "[++] choice".
  [a;++b;]p(??) <-> ([a;]p(??) & [b;]p(??))
End.

Axiom "[;] compose".
  [a;b;]p(??) <-> [a;][b;]p(??)
End.

Axiom "[*] iterate".
  [{a;}*]p(??) <-> (p(??) & [a;][{a;}*] p(??))
End.

/**
 * DIFFERENTIAL EQUATION AXIOMS
 */

Axiom "DW".
  [{c&H(??)}]H(??)
/* [x'=f(x)&q(x);]q(x) THEORY */
End.

Axiom "DC differential cut".
  ([{c&H(??)}]p(??) <-> [{c&(H(??)&r(??))}]p(??)) <- [{c&H(??)}]r(??)
/* ([x'=f(x)&q(x);]p(x) <-> [x'=f(x)&(q(x)&r(x));]p(x)) <- [x'=f(x)&q(x);]r(x) THEORY */
End.

Axiom "DE differential effect".
  /* [x'=f(x)&q(x);]p(x,x') <-> [x'=f(x)&q(x);][x':=f(x);]p(x,x')  THEORY */
  /* @NOTE Generalized argument compared to theory as in DE differential effect (system) */
  /* @NOTE In systems, f(x) cannot have ' by data structure invariant */
  [{x'=f(x)&q(x)}]p(??) <-> [{x'=f(x)&q(x)}][x':=f(x);]p(??)
End.

Axiom "DI differential invariant".
  [{c&H(??)}]p(??) <- (H(??)-> (p(??) & [{c&H(??)}]((p(??))')))
/* [x'=f(x)&q(x);]p(x) <- (q(x) -> (p(x) & [x'=f(x)&q(x);]((p(x))'))) THEORY */
End.

/* Differential Auxiliary / Differential Ghost */
Axiom "DG differential ghost".
  [{c&H(??)}]p(??) <-> \exists y [{c,y'=(t()*y)+s()&H(??)}]p(??)
  /* [x'=f(x)&q(x);]p(x) <-> \exists y [{x'=f(x),y'=(a(x)*y)+b(x))&q(x)}]p(x) THEORY */
End.

/* DG differential ghost, general Lipschitz case */
/*Axiom "DG differential Lipschitz ghost".
  ([x'=f(x)&q(x);]p(x) <-> \exists y [{x'=f(x),y'=g(x,y)&q(x)}]p(x))
  <- (\exists L \forall x \forall y \forall z (abs(g(x,y)-g(x,z)) <= L*abs(y-z)))
End.*/

/* DG differential ghost, general Lipschitz case, system case */
Axiom "DG differential Lipschitz ghost system".
  /* @see "DG differential Lipschitz ghost" THEORY */
  ([{c&H(??)}]p(??) <-> (\exists y [{y'=g(??),c&H(??)}]p(??)))
  <- (\exists L [{c&H(??)}] (\forall a \forall b \forall u \forall v (a>=b -> [y:=a;u:=g(??);y:=b;v:=g(??);] (-L*(a-b) <= u-v & u-v <= L*(a-b)))))
  /* <- (\exists L [{c&H(??)}] (\forall a \forall b \forall u \forall v ([y:=a;u:=g(??);y:=b;v:=g(??);] (abs(u-v) <= L*abs(a-b))))) */
End.

Axiom "DG++ System".
  ([{x'=f(x), c & H(??)}]p(??))  ->  (\forall y [{y'=g(??), x'=f(x), c & H(??)}]p(??))
End.

Axiom "DG++".
  ([{x'=f(x) & H(??)}]p(??))  ->  (\forall y [{y'=g(??),x'=f(x) & H(??)}]p(??))
End.

/* Formatter axioms for diff eqs. */
Axiom ", commute".
  [{c,d & H(??)}]p(??) <-> [{d,c & H(??)}]p(??)
End.

Axiom "DS& differential equation solution".
  [{x'=c()&q(x)}]p(x) <-> \forall t (t>=0 -> ((\forall s ((0<=s&s<=t) -> q(x+(c()*s)))) -> [x:=x+(c()*t);]p(x)))
End.

/** @Derived from DW (not implementable for technical reasons - abstraction of c, ??) */
Axiom "DX differential skip".
  [{c&H(??)}]p(??) -> (H(??)->p(??))
End.

/**
 * DIFFERENTIAL INVARIANTS for SYSTEMS
 */

Axiom "DE differential effect (system)".
  /* @NOTE Soundness: AtomicODE requires explicit-form so f(??) cannot verbatim mention differentials/differential symbols */
  /* @NOTE Completeness: reassociate needed in DifferentialProduct data structures */
  [{x'=f(??),c&H(??)}]p(??) <-> [{c,x'=f(??)&H(??)}][x':=f(??);]p(??)
End.

/**
 * DERIVATION FOR FORMULAS
 */

Axiom "&' derive and".
  (p(??) & q(??))' <-> ((p(??)') & (q(??)'))
End.

Axiom "|' derive or".
  (p(??) | q(??))' <-> ((p(??)') & (q(??)'))
  /* sic! */
End.

Axiom "c()' derive constant fn".
  c()' = 0
End.

Axiom "=' derive =".
  (f(??) = g(??))' <-> ((f(??)') = (g(??)'))
End.

Axiom ">=' derive >=".
  (f(??) >= g(??))' <-> ((f(??)') >= (g(??)'))
End.

Axiom ">' derive >".
  (f(??) > g(??))' <-> ((f(??)') >= (g(??)'))
  /* sic! easier */
End.

Axiom "<=' derive <=".
  (f(??) <= g(??))' <-> ((f(??)') <= (g(??)'))
End.

Axiom "<' derive <".
  (f(??) < g(??))' <-> ((f(??)') <= (g(??)'))
  /* sic! easier */
End.

Axiom "!=' derive !=".
  (f(??) != g(??))' <-> ((f(??)') = (g(??)'))
  /* sic! */
End.

/* DERIVATION FOR TERMS */

Axiom "-' derive neg".
  (-f(??))' = -(f(??)')
End.

Axiom "+' derive sum".
  (f(??) + g(??))' = (f(??)') + (g(??)')
End.

Axiom "-' derive minus".
  (f(??) - g(??))' = (f(??)') - (g(??)')
End.

Axiom "*' derive product".
  (f(??) * g(??))' = ((f(??)')*g(??)) + (f(??)*(g(??)'))
End.

Axiom "/' derive quotient".
  (f(??) / g(??))' = (((f(??)')*g(??)) - (f(??)*(g(??)'))) / (g(??)^2)
End.

Axiom "chain rule".
	[y:=g(x);][y':=1;]( (f(g(x)))' = (f(y)') * (g(x)') )
End.

Axiom "^' derive power".
	((f(??)^(c()))' = (c()*(f(??)^(c()-1)))*(f(??)')) <- (c() != 0)
End.

Axiom "x' derive var".
   ((x_)' = x_')
End.

/** EXCLUSIVELY FOR HYBRID PROGRAMS. UNSOUND FOR HYBRID GAMES. */

/* @NOTE requires removing axioms unsound for hybrid games */
/*Axiom "<d> dual".
  <{a;}^d>p(??) <-> !<a;>!p(??)
  <{a;}^@>p(??) <-> !<a;>!p(??)
End.*/

/* @NOTE Unsound for hybrid games */
Axiom "V vacuous".
  p() -> [a;]p()
  /* @TODO (p() -> [a;]p()) <- [a;]true sound for hybrid games */
End.

/* @NOTE Unsound for hybrid games */
Axiom "K modal modus ponens".
  [a;](p(??)->q(??)) -> (([a;]p(??)) -> ([a;]q(??)))
End.

/* @NOTE Unsound for hybrid games, use ind induction rule instead */
Axiom "I induction".
  /*@TODO Drop or Use this form instead? which is possibly more helpful: ([{a;}*](p(??) -> [a;] p(??))) -> (p(??) -> [{a;}*]p(??)) THEORY */
  (p(??) & [{a;}*](p(??) -> [a;] p(??))) -> [{a;}*]p(??)
End.
"""
  /*
  Axiom "forall' derive forall".
  (\forall x p(??))' <-> (\forall x (p(??)'))
End.

Axiom "exists' derive exists".
  (\exists x p(??))' <-> (\forall x (p(??)'))
  /* sic! */
End.
   */
}
