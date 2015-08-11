/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Axioms of KeYmaera X and axiomatic proof rules of KeYmaera X.
 * resulting from differential dynamic logic
 * @note Soundness-critical: Only adopt sound axioms and sound axiomatic rules.
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.parser.{LoadedAxiom, KeYmaeraParser}


/**
 * The data base of axioms and axiomatic rules of KeYmaera X as resulting from differential dynamic logic axiomatizations.
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
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
   * @author Andre Platzer
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
      val parser = new KeYmaeraParser(enabledLogging = false)
      val alp = parser.ProofFileParser
      val res = alp.runParser(loadAxiomString())

      assert(res.length == res.map(k => k.name).distinct.length, "No duplicate axiom names during parse")

      //@todo move as assertions to assertCheckAxiomFile once we can parse multi-argument functions
      val f = FuncOf(Function("f", None, Unit, Real), Nothing)
      val g = FuncOf(Function("g", None, Unit, Real), Nothing)
      val h = FuncOf(Function("h", None, Unit, Real), Nothing)
      val min = Equal(FuncOf(Function("min", None, Tuple(Real, Real), Real), Pair(f, g)), h)
      val minAxiom = Equiv(min, Or(And(LessEqual(f, g), Equal(h, f)), And(GreaterEqual(f, g), Equal(h, g))))
      val max = Equal(FuncOf(Function("max", None, Tuple(Real, Real), Real), Pair(f, g)), h)
      val maxAxiom = Equiv(max, Or(And(GreaterEqual(f, g), Equal(h, f)), And(LessEqual(f, g), Equal(h, g))))

      (res ++ (LoadedAxiom("min", minAxiom) :: LoadedAxiom("max", maxAxiom) :: Nil)).map(k => (k.name -> k.formula)).toMap
    } catch {
      case e: Exception => e.printStackTrace(); println("Problem while reading axioms " + e); sys.exit(10)
    }
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
    val qny = PredOf(Function("q", None, Real, Bool), Anything)
    val r = Function("r", None, Real, Bool)
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val f = Function("f", None, Real, Real)
    val f0 = FuncOf(Function("f", None, Unit, Real), Nothing)
    val fany = FuncOf(Function("f", None, Real, Real), Anything)
    val gany = FuncOf(Function("g", None, Real, Real), Anything)
    val t0 = FuncOf(Function("t", None, Unit, Real), Nothing)
    val a = ProgramConst("a")
    val b = ProgramConst("b")

    //@todo should not use strange names, better x and q
    val v = Variable("v", None, Real)
    val h0 = PredOf(Function("H", None, Unit, Bool), Nothing)

    // Figure 2
    assert(axs("<> dual") == Equiv(Diamond(a, pany), Not(Box(a, Not(pany)))), "<> dual")
    assert(axs("[:=] assign") == Equiv(Box(Assign(x,f0), PredOf(p,x)), PredOf(p, f0))
      || axs("[:=] assign") == Equiv(Box(Assign(v,t0), PredOf(p,v)), PredOf(p, t0)), "[:=] assign")
    assert(axs("[?] test") == Equiv(Box(Test(q0), p0), Imply(q0, p0))
      || axs("[?] test") == Equiv(Box(Test(h0), p0), Imply(h0, p0)), "[?] test")
    assert(axs("[++] choice") == Equiv(Box(Choice(a,b), pany), And(Box(a, pany), Box(b, pany))), "[++] choice")
    assert(axs("[;] compose") == Equiv(Box(Compose(a,b), pany), Box(a, Box(b, pany))), "[;] compose")
    assert(axs("[*] iterate") == Equiv(Box(Loop(a), pany), And(pany, Box(a, Box(Loop(a), pany)))), "[*] iterate")
    //@note only sound for hybrid systems not for hybrid games
    assert(axs("K modal modus ponens") == Imply(Box(a, Imply(pany,qny)), Imply(Box(a, pany), Box(a, qny))), "K modal modus ponens")
    //@note could also have accepted axiom I for hybrid systems but not for hybrid games
    assert(axs("V vacuous") == Imply(p0, Box(a, p0)), "V vacuous")

    // Figure 3
   /* assert(axs("DC differential cut") == Imply(Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), PredOf(q,x)), PredOf(r,x)),
      Equiv(Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), PredOf(q,x)), PredOf(p,x)),
        Box(ODESystem(AtomicODE(xp, FuncOf(f,x)), And(PredOf(q,x), PredOf(r,x))), PredOf(p,x)))), "DC differential cut") */

    assert(axs("c()' derive constant fn") == Equal(Differential(aC), Number(0)), "c()' derive constant fn")
    assert(axs("+' derive sum") == Equal(Differential(Plus(fany, gany)), Plus(Differential(fany), Differential(gany))), "+' derive sum")
    assert(axs("-' derive minus") == Equal(Differential(Minus(fany, gany)), Minus(Differential(fany), Differential(gany))), "-' derive minus")
    assert(axs("*' derive product") == Equal(Differential(Times(fany, gany)), Plus(Times(Differential(fany), gany), Times(fany, Differential(gany)))), "*' derive product")
    assert(axs("!=' derive !=") == Equiv(DifferentialFormula(NotEqual(fany, gany)), Equal(Differential(fany), Differential(gany))), "!=' derive !=")
    assert(axs("&' derive and") == Equiv(DifferentialFormula(And(pany, qny)), And(DifferentialFormula(pany), DifferentialFormula(qny))), "&' derive and")
    assert(axs("|' derive or") == Equiv(DifferentialFormula(Or(pany, qny)), And(DifferentialFormula(pany), DifferentialFormula(qny))) || axs("|' derive or") == Imply(And(DifferentialFormula(pany), DifferentialFormula(qny)), DifferentialFormula(Or(pany, qny))), "|' derive or")
    assert(axs("x' derive variable") == Forall(immutable.Seq(x_), Equal(Differential(x_), DifferentialSymbol(x_))), "x' derive variable")

    assert(axs("all instantiate") == Imply(Forall(Seq(x), PredOf(p,x)), PredOf(p,t0)), "all instantiate")
    assert(axs("all distribute") == Imply(Forall(Seq(x), Imply(PredOf(p,x),PredOf(q,x))), Imply(Forall(Seq(x),PredOf(p,x)), Forall(Seq(x),PredOf(q,x)))), "all distribute")
    // soundness-critical that these are for p() not for p(x) or p(?)
    assert(axs("vacuous all quantifier") == Equiv(p0, Forall(immutable.IndexedSeq(x), p0)), "vacuous all quantifier")
    assert(axs("vacuous exists quantifier") == Equiv(p0, Exists(immutable.IndexedSeq(x), p0)), "vacuous exists quantifier")
    true
  }

  /**
   * Look up an axiom of KeYmaera X,
   * i.e. sound axioms are valid formulas of differential dynamic logic.
   */
  private[core] def loadAxiomString() : String =
"""
/**
 * KeYmaera X Axioms.
 *
 * @note Soundness-critical: Only adopt valid formulas as axioms.
 *
 * @author Nathan Fulton
 * @author Stefan Mitsch
 * @author Jan-David Quesel
 * @author Andre Platzer
 * 
 * Basic dL Axioms of Differential Dynamic Logic.
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. arXiv 1503.01981, 2015."
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
  CP d.
  F pf.
  F p(T).
  F p(??).
  F q.
  F q(T).
  F r(??).
  F ctxF_(T).
  F H.
  F H(T).
  /* for arithmetic axioms */
  /* T r. */
  T abs(T).
  T f().
  T g().
  /*T max(T, T).
  T min(T, T).*/
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

Axiom "all distribute".
  (\forall x. (p(x)->q(x))) -> ((\forall x. p(x)) -> (\forall x. q(x)))
End.

/* @Derived */
Axiom "exists generalize".
  p(t()) -> \exists x. p(x)
End.

Axiom "vacuous all quantifier".
  p <-> \forall x. p
  /*  pf <-> \forall x pf*/
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
  <a;>p(??) <-> ![a;](!p(??))
End.

/* @Derived */
Axiom "[] dual".
  [a;]p(??) <-> !<a;>(!p(??))
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
  [a ++ b]p(??) <-> ([a;]p(??) & [b;]p(??)).
End.

/* @Derived */
Axiom "<++> choice".
   <a ++ b;>p(??) <-> (<a;>p(??) | <b;>p(??)).
End.

Axiom "[;] compose".
  [ a; b; ]p(??) <-> [a;][b;]p(??).
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
  [c&H(?);]p(?) <-> \exists y. [c,y'=t()*y+s()&H(?);]p(?)
  /* [x'=f(x)&q(x);]p(x) <-> \exists y. [(x'=f(x),y'=a(x)*y+b(x))&q(x);]p(x) THEORY */
End.

/* Inverse Differential Auxiliary / Differential Ghost -- not strictly necessary but saves a lot of reordering work. */
Axiom "DA inverse differential ghost".
  [c&H(?);]p(?) <-> \exists y. [y'=t()*y+s(),c&H(?);]p(?)
End.

/*Axiom "DA inverse differential ghost theory version".
  [x'=f(x)&q(x);]p(x) <-> \exists y. [(y'=a(x)*y+b(x), x'=f(x))&q(x);]p(x)
End.*/

/* DG differential ghost, general Lipschitz case */
/*Axiom "DG differential Lipschitz ghost".
  ([x'=f(x)&q(x);]p(x) <-> \exists y. [x'=f(x),y'=g(x,y)&q(x);]p(x))
  <- (\exists L \forall x \forall y \forall z (y>=z -> (-L*(y-x) <= g(x,y)-g(x,z) & g(x,y)-g(x,z) <= L*(y-z))))
End.*/

/* DG differential ghost, general Lipschitz case, system case */
Axiom "DG differential Lipschitz ghost system".
  /* @see "DG differential Lipschitz ghost" THEORY */
  ([c&H(?);]p(?) <-> \exists y. [y'=g(?),c&H(?);]p(?))
  <- (\exists L . [c&H(?);] (\forall a . \forall b . \forall u . \forall v . (a>=b -> [y:=a;u:=g(?);y:=b;v:=g(?)] (-L*(a-b) <= u-v & u-v <= L*(a-b)))))
End.

/* Formatter axioms for diff eqs. @todo unused except in tactics implementation of itself */
Axiom ", commute".
  [c,d & H(?);]p(?) <-> [d,c & H(?);]p(?)
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

/* @NOTE requires removing axioms unsound for hybrid games */
/*Axiom "<d> dual".
  <{a;}^d>p(?) <-> !<a;>!p(?)
  <{a;}^@>p(?) <-> !<a;>!p(?)
End.*/

/* @NOTE Unsound for hybrid games */
Axiom "V vacuous".
  p -> [a;]p
  /* @TODO (p -> [a;]p) <- [a;]true sound for hybrid games */
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

Axiom "= reflexive".
  s() = s()
End.

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

/* @todo change second case to a strict inequality */
Axiom "abs".
  (abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<=0 & t()=-s()))
End.

/* @todo Multi-argument don't parse in KeYmaeraParser:1203
Axiom "max expand".
  (max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<=g() & h()=g()))
End.

Axiom "min expand".
  (min(f(), g()) = h()) <-> ((f()<=g() & h()=f()) | (f()>=g() & h()=g()))
End. */
"""
}
