/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Axioms of KeYmaera X and axiomatic proof rules of KeYmaera X.
 * resulting from differential dynamic logic
 * @note Soundness-critical: Only adopt sound axioms and sound axiomatic rules.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraParser


/**
 * The data base of axioms and axiomatic rules of KeYmaera X as resulting from differential dynamic logic axiomatizations.
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @author aplatzer
 */
private[core] object AxiomBase {
  /**
   * KeYmaera X Axiomatic Proof Rules.
   * @note Soundness-critical: Only return locally sound proof rules.
   * @return immutable list of locally sound axiomatic proof rules (premise, conclusion)
   * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
   * @author aplatzer
   */
  private[core] def loadAxiomaticRules() : immutable.Map[String, (Sequent, Sequent)] = {
    val x = Variable("x_", None, Real)
    val px = PredOf(Function("p_", None, Real, Bool), x)
    val pany = PredOf(Function("p_", None, Real, Bool), Anything)
    val qx = PredOf(Function("q_", None, Real, Bool), x)
    val qany = PredOf(Function("q_", None, Real, Bool), Anything)
    val fany = FuncOf(Function("f_", None, Real, Real), Anything)
    val gany = FuncOf(Function("g_", None, Real, Real), Anything)
    val ctxt = Function("ctx_", None, Real, Real) // function symbol
    val ctxf = Function("ctx_", None, Real, Bool) // predicate symbol
    // Sort of predicational is really (Real->Bool)->Bool except sort system doesn't know that type.
    val context = Function("ctx_", None, Bool, Bool) // predicational symbol
    val a = ProgramConst("a_")
    val fmlany = PredOf(Function("F_", None, Real, Bool), Anything)

    Map(
      /**
       * Rule "all generalization".
       * Premise p(x)
       * Conclusion \forall x . p(x)
       * End.
       */
      /*("all generalization",
        (Sequent(Seq(), IndexedSeq(), IndexedSeq(px)),
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Forall(Seq(x), px))))),*/
      /**
       * Rule "all generalization".
       * Premise p(?)
       * Conclusion \forall x . p(?)
       * End.
       */
      ("all generalization",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(pany)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Forall(immutable.Seq(x), pany))))),
      /**
       * Rule "CT term congruence".
       * Premise f_(?) = g_(?)
       * Conclusion ctxT_(f_(?)) = ctxT_(g_(?))
       * End.
       * @derived("Could also use CQ equation congruence with p(.)=(ctx_(.)=ctx_(g_(x))) and reflexivity of = instead.")
       */
      ("CT term congruence",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(fany, gany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(FuncOf(ctxt, fany), FuncOf(ctxt, gany)))))),
      /**
       * Rule "CQ equation congruence".
       * Premise f_(?) = g_(?)
       * Conclusion ctxP_(f_(?)) <-> ctxP_(g_(?))
       * End.
       */
      ("CQ equation congruence",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equal(fany, gany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredOf(ctxf, fany), PredOf(ctxf, gany)))))),
      /**
       * Rule "CE congruence".
       * Premise p_(?) <-> q_(?)
       * Conclusion ctxF_(p_(?)) <-> ctxF_(q_(?))
       * End.
       */
      ("CE congruence",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(pany, qany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(PredicationalOf(context, pany), PredicationalOf(context, qany)))))),
      ("CO one-sided congruence",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(Equiv(pany, qany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(PredicationalOf(context, pany)), immutable.IndexedSeq(PredicationalOf(context, qany))))),
      /**
       * Rule "all monotone".
       * Premise p(x) ==> q(x)
       * Conclusion \forall x. p(x) ==> \forall x. q(x)
       * End.
       */
      ("all monotone",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(px), immutable.IndexedSeq(qx)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(Forall(immutable.Seq(x), px)), immutable.IndexedSeq(Forall(immutable.Seq(x), qx))))),
      /**
       * Rule "exists monotone".
       * Premise p(x) ==> q(x)
       * Conclusion \exists x. p(x) ==> \exists x. q(x)
       * End.
       */
      ("exists monotone",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(px), immutable.IndexedSeq(qx)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(Exists(immutable.Seq(x), px)), immutable.IndexedSeq(Exists(immutable.Seq(x), qx))))),
      /**
       * Rule "[] monotone".
       * Premise p(x) ==> q(x)
       * Conclusion [a;]p(x) ==> [a;]q(x)
       * End.
       */
      ("[] monotone",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(qany)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(Box(a, pany)), immutable.IndexedSeq(Box(a, qany))))),
      /**
       * Rule "<> monotone".
       * Premise p(x) ==> q(x)
       * Conclusion <a;>p(x) ==> <a;>q(x)
       * End.
       */
      ("<> monotone",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(qany)),
          Sequent(immutable.Seq(), immutable.IndexedSeq(Diamond(a, pany)), immutable.IndexedSeq(Diamond(a, qany))))),
      /**
       * Rule "ind induction".
       * Premise p(?) ==> [a;]p(?)
       * Conclusion p(?) ==> [a*]p(?)
       */
      ("ind induction",
        (Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(a, pany))),
          Sequent(immutable.Seq(), immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(Loop(a), pany))))),
      /* UNSOUND FOR HYBRID GAMES */
      /**
       * Rule "Goedel".
       * Premise p(x)
       * Conclusion [a;]p(x)
       * End.
       * @NOTE Unsound for hybrid games
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
   * @todo In the long run, could benefit from asserting expected parse of axioms to remove parser from soundness-critical core. This, obviously, introduces redundancy.
   */
  private[core] def loadAxioms: immutable.Map[String, Formula] = {
    val parser = new KeYmaeraParser(enabledLogging = false)
    val alp = parser.ProofFileParser
    val res = alp.runParser(loadAxiomString())

    assert(res.length == res.map(k => k.name).distinct.length, "No duplicate axiom names during parse")

    res.map(k => (k.name -> k.formula)).toMap
  } ensuring(assertCheckAxiomFile _, "checking parse of axioms against expected outcomes")

  private def assertCheckAxiomFile(axs : Map[String, Formula]) = {
    val x = Variable("x", None, Real)
    val x_ = Variable("x_", None, Real)
    val aP0 = PredOf(Function("p", None, Unit, Bool), Nothing)
    val aPn = PredOf(Function("p", None, Real, Bool), Anything)
    val aQn = PredOf(Function("q", None, Real, Bool), Anything)
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val aF = FuncOf(Function("f", None, Real, Real), Anything)
    val aG = FuncOf(Function("g", None, Real, Real), Anything)
    val a = ProgramConst("a")
    val b = ProgramConst("b")
    // soundness-critical that these are for p() not for p(x) or p(?)
    assert(axs("vacuous all quantifier") == Equiv(aP0, Forall(immutable.IndexedSeq(x), aP0)), "vacuous all quantifier")
    assert(axs("vacuous exists quantifier") == Equiv(aP0, Exists(immutable.IndexedSeq(x), aP0)), "vacuous exists quantifier")
    assert(axs("V vacuous") == Imply(aP0, Box(a, aP0)), "V vacuous")

    assert(axs("[++] choice") == Equiv(Box(Choice(a,b), aPn), And(Box(a, aPn), Box(b, aPn))), "[++] choice")
    assert(axs("[;] compose") == Equiv(Box(Compose(a,b), aPn), Box(a, Box(b, aPn))), "[;] compose")

    assert(axs("c()' derive constant fn") == Equal(Differential(aC), Number(0)), "c()' derive constant fn")
    assert(axs("-' derive minus") == Equal(Differential(Minus(aF, aG)), Minus(Differential(aF), Differential(aG))), "-' derive minus")
    assert(axs("*' derive product") == Equal(Differential(Times(aF, aG)), Plus(Times(Differential(aF), aG), Times(aF, Differential(aG)))), "*' derive product")
    assert(axs("!=' derive !=") == Equiv(DifferentialFormula(NotEqual(aF, aG)), Equal(Differential(aF), Differential(aG))), "!=' derive !=")
    assert(axs("|' derive or") == Equiv(DifferentialFormula(Or(aPn, aQn)), And(DifferentialFormula(aPn), DifferentialFormula(aQn))), "|' derive or")
    assert(axs("x' derive variable") == Forall(immutable.Seq(x_), Equal(Differential(x_), DifferentialSymbol(x_))), "x' derive variable")
    true
  }

  /**
   * Look up an axiom of KeYmaera X,
   * i.e. sound axioms are valid formulas of differential dynamic logic.
   */
  private[core] def loadAxiomString() : String =
"""
/**
 * KeYmaera Axioms.
 *
 * @note Soundness-critical: Only adopt valid formulas as axioms.
 *
 * @author Nathan Fulton
 * @author Stefan Mitsch
 * @author Jan-David Quesel
 * @author Andre Platzer
 * 
 * Basic dL Axioms of Differential Dynamic Logic.
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012."
 * @see "Andre Platzer. Dynamic logics of dynamical systems. arXiv 1205.4788, May 2012."
 * @see "Andre Platzer. Differential game logic. arXiv 1408.1980, August 2014."
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @todo simplify/unify the number of declarations.
 */
Variables.
  T c().
  T s.
  T s().
  T t.
  T t().
  T x.
  T v. /* TODO-nrf this needs to be a V */
  T f(T).
  T g(T).
  T ctxT_(T).
  P a.
  P b.
  CP c.
  F p.
  F p(T).
  F p(?).
  F q.
  F q(T).
  F r(?).
  F ctxF_(T).
  F H.
  F H(T).
  /* for arithmetic axioms */
  /* T r.
   * T Abs(T).
   * T Max(T, T).
   * T Min(T, T).*/
End.

/**
 * FIRST-ORDER QUANTIFIER AXIOMS
 */
Axiom /*\\foralli */ "all instantiate".
  (\forall x. p(x)) -> p(t())
End.

/* consequence of "all instantiate" */
Axiom "all eliminate".
  (\forall x. p(?)) -> p(?)
End.

/* @Derived */
Axiom "exists generalize".
  p(t()) -> \exists x. p(x)
End.

Axiom "vacuous all quantifier".
  p <-> \forall x. p
End.

/* @Derived */
Axiom "vacuous exists quantifier".
  p <-> \exists x. p
End.

Axiom "all dual".
  (\forall x . p(x)) <-> !(\exists x . (!p(x)))
End.

/* @Derived */
Axiom "exists dual".
  (\exists x . p(x)) <-> !(\forall x . (!p(x)))
End.

/*
Axiom "all quantifier scope".
  (\forall x. (p(x) & q)) <-> ((\forall x. p(x)) & q)
End.
*/

/**
 * CONGRUENCE AXIOMS (for constant terms)
 */

Axiom "const congruence".
  s() = t() -> ctxT_(s()) = ctxT_(t())
End.

Axiom "const formula congruence".
  s() = t() -> (ctxF_(s()) <-> ctxF_(t()))
End.


/**
 * HYBRID PROGRAM MODALITIES
 */

Axiom "<> dual".
  <a;>p(?) <-> ![a;](!p(?))
End.

/* @Derived */
Axiom "[] dual".
  [a;]p(?) <-> !<a;>(!p(?))
End.

Axiom "[:=] assign".
  [v:=t();]p(v) <-> p(t())
End.

/* @derived */
Axiom "<:=> assign".
  <v:=t();>p(v) <-> p(t())
End.

/* @derived */
Axiom "[:=] assign equational".
  [v:=t();]p(v) <-> \forall v . (v=t() -> p(v))
End.

Axiom "[:=] vacuous assign".
  [v:=t();]p <-> p
End.

/* @derived */
Axiom "<:=> vacuous assign".
  <v:=t();>p <-> p
End.

Axiom "[':=] differential assign".
  [v':=t();]p(v') <-> p(t())
End.

/* @derived */
Axiom "<':=> differential assign".
  <v':=t();>p(v') <-> p(t())
End.

Axiom "[:*] assign nondet".
  [v:=*;]p(v) <-> \forall v. p(v)
End.

/* @derived */
Axiom "<:*> assign nondet".
  <v:=*;>p(v) <-> \exists v. p(v)
End.

Axiom "[?] test".
  [?H;]p <-> (H -> p).
End.

/* @Derived */
Axiom "<?> test".
  <?H;>p <-> (H & p).
End.

Axiom "[++] choice".
  [a ++ b]p(?) <-> ([a;]p(?) & [b;]p(?)).
End.

/* @Derived */
Axiom "<++> choice".
   <a ++ b;>p(?) <-> (<a;>p(?) | <b;>p(?)).
End.

Axiom "[;] compose".
  [ a; b; ]p(?) <-> [a;][b;]p(?).
End.

/* @Derived */
Axiom "<;> compose".
  < a; b; >p(?) <-> <a;><b;>p(?).
End.

Axiom "[*] iterate".
  [a*]p(?) <-> (p(?) & [a;][a*] p(?)).
End.

/* @Derived */
Axiom "<*> iterate".
  <a*>p(?) <-> (p(?) | <a;><a*> p(?)).
End.

/* @Derived */
Axiom "Domain Constraint Conjunction Reordering".
  [c & (H(?) & q(?));]p(?) <-> [c & (q(?) & H(?));]p(?)
End.

/**
 * DIFFERENTIAL EQUATION AXIOMS
 */

Axiom "DW differential weakening".
  [c&H(?);]p(?) <-> ([c&H(?);](H(?)->p(?)))
/* [x'=f(x)&q(x);]p(x) <-> ([x'=f(x)&q(x);](q(x)->p(x))) THEORY */
End.

Axiom "DC differential cut".
  ([c&H(?);]p(?) <-> [c&(H(?)&r(?));]p(?)) <- [c&H(?);]r(?)
/* ([x'=f(x)&q(x);]p(x) <-> [x'=f(x)&(q(x)&r(x));]p(x)) <- [x'=f(x)&q(x);]r(x) THEORY */
End.

Axiom "DE differential effect".
  /* [x'=f(x)&q(x);]p(x) <-> [x'=f(x)&q(x);][x':=f(x);]p(x)  @TODO sound but incomplete */
  /* @TODO [x'=f(x)&q(x);]p(x,x') <-> [x'=f(x)&q(x);][x':=f(x);]p(x,x')  THEORY */
  /*@NOTE Generalized compared to theory as in DE differential effect (system) */
  [x'=f(x)&q(x);]p(?) <-> [x'=f(x)&q(x);][x':=f(x);]p(?)
End.

Axiom "DI differential invariant".
  [c&H(?);]p(?) <- (H(?)-> (p(?) & [c&H(?);]((p(?))')))
/* [x'=f(x)&q(x);]p(x) <- (q(x) -> (p(x) & [x'=f(x)&q(x);]((p(x))'))) THEORY */
End.

/* Differential Auxiliary / Differential Ghost */
Axiom "DA differential ghost".
  /*@TODO Code Review discrepancy: change to TODO form from theory, not old calculus */
  /* [c&H(?);]p(?) <- ((p(?) <-> \exists x. q(?)) &
   * [c,x'=t()*x+s()&H(?);]q(?)) */
  [c&H(?);]p(?) <-> \exists y. [c,y'=t()*y+s()&H(?);]p(?)
  /* [x'=f(x)&q(x);]p(x) <-> \exists y. [(x'=f(x),y'=a(x)*y+b(x))&q(x);]p(x) THEORY */
End.

/* @Derived */
Axiom "DS differential equation solution".
  [x'=c();]p(x) <-> \forall t. (t>=0 -> [x:=x+c()*t;]p(x))
End.

Axiom "DS& differential equation solution".
  [x'=c()&q(x);]p(x) <-> \forall t. (t>=0 -> ((\forall s. ((0<=s&s<=t) -> q(x+c()*s))) -> [x:=x+c()*t;]p(x)))
End.

/* @derived(DS differential equation solution + duality) */
Axiom "Dsol differential equation solution".
 <x'=c();>p(x) <-> \exists t. (t>=0 & <x:=x+c()*t;>p(x))
End.

/* @Derived */
Axiom "Dsol& differential equation solution".
  <x'=c()&q(x);>p(x) <-> \exists t. (t>=0 & ((\forall s. ((0<=s&s<=t) -> q(x+c()*s))) & <x:=x+c()*t;>p(x)))
End.

/**
 * DIFFERENTIAL INVARIANTS for SYSTEMS
 */

Axiom "DE differential effect (system)".
    /* @NOTE Soundness: AtomicODE requires explicit-form so f(?) cannot verbatim mention differentials/differential symbols */
    /* @NOTE Completeness: reassociate needed in DifferentialProduct data structures */
    [x'=f(?),c&H(?);]p(?) <-> [c,x'=f(?)&H(?);][x':=f(?);]p(?)
End.

/**
 * DERIVATION FOR FORMULAS
 */

/* @todo added and probably not nec. */
/* @derived by CE */
Axiom "->' derive imply".
  (p(?) -> q(?))' <-> (!p(?) | q(?))'
End.

Axiom "&' derive and".
  (p(?) & q(?))' <-> ((p(?)') & (q(?)'))
End.

Axiom "|' derive or".
  (p(?) | q(?))' <-> ((p(?)') & (q(?)'))
  /* sic! */
End.

Axiom "forall' derive forall".
  (\forall x. p(?))' <-> (\forall x. (p(?)'))
End.

Axiom "exists' derive exists".
  (\exists x. p(?))' <-> (\forall x. (p(?)'))
  /* sic! */
End.

Axiom "c()' derive constant fn".
  c()' = 0
End.

Axiom "=' derive =".
  (f(?) = g(?))' <-> ((f(?)') = (g(?)'))
End.

Axiom ">=' derive >=".
  (f(?) >= g(?))' <-> ((f(?)') >= (g(?)'))
End.

Axiom ">' derive >".
  (f(?) > g(?))' <-> ((f(?)') >= (g(?)'))
  /* sic! easier */
End.

Axiom "<=' derive <=".
  (f(?) <= g(?))' <-> ((f(?)') <= (g(?)'))
End.

Axiom "<' derive <".
  (f(?) < g(?))' <-> ((f(?)') <= (g(?)'))
  /* sic! easier */
End.

Axiom "!=' derive !=".
  (f(?) != g(?))' <-> ((f(?)') = (g(?)'))
  /* sic! */
End.

/* DERIVATION FOR TERMS */

Axiom "-' derive neg".
  (-f(?))' = -(f(?)')
End.

Axiom "+' derive sum".
  (f(?) + g(?))' = (f(?)') + (g(?)')
End.

Axiom "-' derive minus".
  (f(?) - g(?))' = (f(?)') - (g(?)')
End.

Axiom "*' derive product".
  (f(?) * g(?))' = ((f(?)')*g(?)) + (f(?)*(g(?)'))
End.

Axiom "/' derive quotient".
  (f(?) / g(?))' = (((f(?)')*g(?)) - (f(?)*(g(?)'))) / (g(?)^2)
End.

Axiom "chain rule".
	[y:=g(x);][y':=1;]( (f(g(x)))' = (f(y)') * (g(x)') )
End.

Axiom "^' derive power".
	(f(?)^c())' = (c()*(f(?)^(c()-1)))*(f(?)') <- c() != 0
End.

Axiom "x' derive variable".
  \forall x_ . ((x_)' = x_')
End.

/**
 * EXCLUSIVELY FOR HYBRID PROGRAMS.
 * UNSOUND FOR HYBRID GAMES.
 */

/* @NOTE Unsound for hybrid games */
Axiom "V vacuous".
  p -> [a;]p
End.

/* @NOTE Unsound for hybrid games */
Axiom "K modal modus ponens".
  [a;](p(?)->q(?)) -> (([a;]p(?)) -> ([a;]q(?)))
End.

/* @NOTE Unsound for hybrid games, use ind induction rule instead */
Axiom "I induction".
  /*@TODO Use this form instead? which is possibly more helpful: ([a*](p(?) -> [a;] p(?))) -> (p(?) -> [a*]p(?)) THEORY */
  (p(?) & [a*](p(?) -> [a;] p(?))) -> [a*]p(?)
End.


/**
 * Boolean algebra
 */
 Axiom "& associative".
  p(?) & q(?) & r(?) <-> p(?) & (q(?) & r(?))
 End.
 /* ... */

/**
 * Real arithmetic
 */

/* Unused so far
Axiom "+ associative".
  (r + s) + t = r + (s + t)
End.

Axiom "* associative".
  (r * s) * t = r * (s * t)
End.

Axiom "+ commutative".
  s+t = t+s
End.

Axiom "* commutative".
  s*t = t*s
End.

Axiom "distributive".
  r*(s+t) = (r*s) + (r*t)
End.

Axiom "+ identity".
  s + 0 = s
End.

Axiom "* identity".
  s * 1 = s
End.

Axiom "+ inverse".
  s + (-s) = 0
End.

Axiom "* inverse".
  s != 0 -> s * (s^-1) = 1
End.

Axiom "positivity".
  0 < s | 0 = s | 0 < -s
End.

Axiom "+ closed".
  (0 < s & 0 < t) -> 0 < s+t
End.

Axiom "* closed".
  (0 < s & 0 < t) -> 0 < s*t
End.

Axiom "<".
  s<t <-> 0 < t-s
End.

Axiom ">".
  s>t <-> t<s
End.
*/

Axiom "<=".
  f(?)<=g(?) <-> (f(?)<g(?) | f(?)=g(?))
End.

Axiom "= negate".
  f(?) = g(?) <-> !(f(?) != g(?))
End.

Axiom "< negate".
  f(?) < g(?) <-> !(f(?) >= g(?))
End.

Axiom ">= flip".
  f(?) >= g(?) <-> (g(?) <= f(?))
End.

Axiom "> flip".
  f(?) > g(?) <-> (g(?) < f(?))
End.

/* Unused so far
Axiom "abs expand".
  Abs(s) = if (s < 0) then -s else s fi
End.
*/
/* @todo Multi-argument don't parse
Axiom "max expand".
  Max(s, t) = if (s > t) then s else t fi
End.

Axiom "min expand".
  Min(s, t) = if (s < t) then s else t fi
End.
*/
"""
}
