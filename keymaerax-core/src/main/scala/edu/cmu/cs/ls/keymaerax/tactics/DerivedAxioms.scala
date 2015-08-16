/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{PositionTactic, Tactic, ApplyRule}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._

import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{ToolEvidence, Evidence}

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Derived Axioms.
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 */
object DerivedAxioms {
  import TactixLibrary._

  /** Database for derived axioms */
  //@todo which lemma db to use?
  val derivedAxiomDB = new FileLemmaDB
  type LemmaID = String

  private val AUTO_INSERT = true

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  private[tactics] def derivedAxiom(name: String, fact: Provable): Lemma = {
    require(fact.isProved, "only proved Provables would be accepted as derived axioms: " + name + " got\n" + fact)
    // create evidence (traces input into tool and output from tool)
    val evidence = new ToolEvidence(immutable.Map("input" -> fact.toString, "output" -> "true")) :: Nil
    val lemma = Lemma(fact, evidence, Some(name))
    if (!AUTO_INSERT) {
      lemma
    } else {
      // first check whether the lemma DB already contains identical lemma name
      val lemmaID = if (derivedAxiomDB.contains(name)) {
        // identical lemma contents with identical name, so reuse ID
        if (derivedAxiomDB.get(name) == Some(lemma)) lemma.name.get
        else throw new IllegalStateException("Prover already has a different lemma filed under the same name " + derivedAxiomDB.get(name))
      } else {
        LookupLemma.addLemma(derivedAxiomDB, lemma)
      }
      derivedAxiomDB.get(lemmaID).get
    }
  }

  /** Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available */
  private[tactics] def derivedAxiom(name: String, derived: Sequent, tactic: Tactic): Lemma = {
    //@todo optimize: no need to prove if already filed in derivedAxiomDB anyhow
    val witness = TactixLibrary.proveBy(derived, tactic)
    assert(witness.isProved, "tactics proving derived axioms should produce proved Provables: " + name + " got\n" + witness)
    derivedAxiom(name, witness)
  }

  /** Package a Lemma for a derived axiom up as a tactic */
  private[tactics] def derivedAxiomT(lemma: Lemma): ApplyRule[LookupLemma] = {
    require(derivedAxiomDB.contains(lemma.name.get), "Lemma has already been added")
    val lemmaRule = LookupLemma(derivedAxiomDB, lemma.name.get)
    new ApplyRule(lemmaRule) {
      override def applicable(node: ProofNode): Boolean = node.sequent.sameSequentAs(lemma.fact.conclusion)
    }
  }

  private val x = Variable("x_", None, Real)
  private val px = PredOf(Function("p_", None, Real, Bool), x)
  private val pany = PredOf(Function("p_", None, Real, Bool), Anything)
  private val qx = PredOf(Function("q_", None, Real, Bool), x)
  private val qany = PredOf(Function("q_", None, Real, Bool), Anything)
  private val fany = FuncOf(Function("f_", None, Real, Real), Anything)
  private val gany = FuncOf(Function("g_", None, Real, Real), Anything)
  private val ctxt = Function("ctx_", None, Real, Real) // function symbol
  private val ctxf = Function("ctx_", None, Real, Bool) // predicate symbol
  private val context = Function("ctx_", None, Bool, Bool) // predicational symbol

  /**
   * {{{Axiom "<-> reflexive".
   *  p() <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val equivReflexiveAxiom = derivedAxiom("<-> reflexive",
    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq("p() <-> p()".asFormula)))
      (EquivRight(SuccPos(0)), 0)
      // right branch
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (Close(AntePos(0),SuccPos(0)), 0)
  )

  lazy val equivReflexiveT = derivedAxiomT(equivReflexiveAxiom)

  /**
   * {{{Axiom "!! double negation".
   *  (!(!p())) <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val doubleNegationAxiom = derivedAxiom("!! double negation",
    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq("(!(!p())) <-> p()".asFormula)))
      (EquivRight(SuccPos(0)), 0)
      // right branch
      (NotRight(SuccPos(0)), 1)
      (NotLeft(AntePos(1)), 1)
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (NotLeft(AntePos(0)), 0)
      (NotRight(SuccPos(1)), 0)
      (Close(AntePos(0),SuccPos(0)), 0)
  )

  lazy val doubleNegationT = derivedAxiomT(doubleNegationAxiom)

  /**
   * {{{Axiom "exists dual".
   *   (!\forall x (!p(x))) <-> (\exists x p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val existsDualAxiom = derivedAxiom("exists dual",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!\\forall x (!p(x))) <-> \\exists x p(x)".asFormula)),
    useAt("all dual", PosInExpr(1::Nil))(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val existsDualT = derivedAxiomT(existsDualAxiom)

  /**
   * {{{Axiom "[] dual".
   *    (!<a;>(!p(??))) <-> [a;]p(??)
   * End.
   * }}}
   * @note almost same proof as "exists dual"
   * @Derived
   */
  lazy val boxDualAxiom = derivedAxiom("[] dual",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!<a;>(!p(??))) <-> [a;]p(??)".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val boxDualT = derivedAxiomT(boxDualAxiom)

  /**
   * {{{Axiom "<:=> assign".
   *    <v:=t();>p(v) <-> p(t())
   * End.
   * }}}
   * @Derived
   */
  lazy val assigndAxiom = derivedAxiom("<:=> assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<v:=t();>p(v) <-> p(t())".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[:=] assign")(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val assigndT = derivedAxiomT(assigndAxiom)

  /**
   * {{{Axiom "[:=] assign equational".
   *    [v:=t();]p(v) <-> \forall v (v=t() -> p(v))
   * End.
   * }}}
   * @Derived
   */
  lazy val assignbEquationalAxiom = derivedAxiom("[:=] assign equational",
    Sequent(Nil, IndexedSeq(), IndexedSeq("[v:=t();]p(v) <-> \\forall v (v=t() -> p(v))".asFormula)),
    useAt("[:=] assign")(SuccPosition(0, 0::Nil)) &
      commuteEquivRightT(SuccPos(0)) &
      byUS(allSubstitute)
  )

  lazy val assignbEquationalT = derivedAxiomT(assignbEquationalAxiom)

  /**
   * {{{Axiom "[:=] vacuous assign".
   *    [v:=t();]p() <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val vacuousAssignbAxiom = derivedAxiom("[:=] vacuous assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq("[v:=t();]p() <-> p()".asFormula)),
    useAt("[:=] assign")(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val vacuousAssignbT = derivedAxiomT(vacuousAssignbAxiom)

  /**
   * {{{Axiom "<:=> vacuous assign".
   *    <v:=t();>p() <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val vacuousAssigndAxiom = derivedAxiom("<:=> vacuous assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<v:=t();>p() <-> p()".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[:=] vacuous assign")(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val vacuousAssigndT = derivedAxiomT(vacuousAssigndAxiom)

  /**
   * {{{Axiom "<':=> differential assign".
   *    <v':=t();>p(v') <-> p(t())
   * End.
   * }}}
   * @Derived
   */
  lazy val assignDAxiom = derivedAxiom("<':=> differential assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<v':=t();>p(v') <-> p(t())".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[':=] differential assign")(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val assignDT = derivedAxiomT(assignDAxiom)

  /**
   * {{{Axiom "<:*> assign nondet".
   *    <x:=*;>p(x) <-> (\exists x p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val nondetassigndAxiom = derivedAxiom("<*:> assign nondet",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<x:=*;>p(x) <-> (\\exists x p(x))".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[:*] assign nondet")(SuccPosition(0, 0::0::Nil)) &
      useAt("all dual", PosInExpr(1::Nil))(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val nondetassigndT = derivedAxiomT(nondetassigndAxiom)

  /**
   * {{{Axiom "<?> test".
   *    <?H();>p() <-> (H() & p())
   * End.
   * }}}
   * @Derived
   */
  lazy val testdAxiom = derivedAxiom("<?> test",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<?H();>p() <-> (H() & p())".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[?] test")(SuccPosition(0, 0::0::Nil)) &
      prop
  )

  lazy val testdT = derivedAxiomT(testdAxiom)

  /**
   * {{{Axiom "<++> choice".
   *    <a;++b;>p(??) <-> (<a;>p(??) | <b;>p(??))
   * End.
   * }}}
   * @todo first show de Morgan
   */
  lazy val choicedAxiom = derivedAxiom("<++> choice",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<a;++b;>p(??) <-> (<a;>p(??) | <b;>p(??))".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[++] choice")(SuccPosition(0, 0::0::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::0::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
      prop
  )

  /**
   * {{{Axiom "<;> compose".
   *    <a;b;>p(??) <-> <a;><b;>p(??)
   * End.
   * }}}
   * @Derived
   */
  lazy val composedAxiom = derivedAxiom("<;> compose",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<a;b;>p(??) <-> <a;><b;>p(??)".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[;] compose")(SuccPosition(0, 0::0::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 1::0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  /**
   * {{{Axiom "<*> iterate".
   *    <{a;}*>p(??) <-> (p(??) | <a;><{a;}*> p(??))
   * End.
   * }}}
   * @Derived
   */
  lazy val iteratedAxiom = derivedAxiom("<*> iterate",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<{a;}*>p(??) <-> (p(??) | <a;><{a;}*> p(??))".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[*] iterate")(SuccPosition(0, 0::0::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::1::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
      HilbertCalculus.stepAt(SuccPosition(0, 0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 1::1::0::1::Nil)) &
      prop
      //useAt(doubleNegationAxiom)(SuccPosition(0, 1::1::0::1::Nil)) &
      //byUS(equivReflexiveAxiom)
  )

  //@todo this is somewhat indirect. Maybe it'd be better to represent derived axioms merely as Lemma and auto-wrap them within their ApplyRule[LookupLemma] tactics on demand.
  //private def useAt(lem: ApplyRule[LookupLemma]): PositionTactic = TactixLibrary.useAt(lem.rule.lemma.fact)

  /**
   * {{{Axiom "exists generalize".
   *    p(t()) -> (\exists x p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val existsGeneralize = derivedAxiom("exists generalize",
    Sequent(Nil, IndexedSeq(), IndexedSeq("p(t()) -> (\\exists x p(x))".asFormula)),
//    useAt("exists dual", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
//      useAt("all instantiate", PosInExpr(0::Nil))(SuccPosition(0, 1::0::Nil)) &
//      prop
      useAt("exists dual", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
        implyR(SuccPos(0)) &
        notR(SuccPos(0)) &
        useAt("all instantiate", PosInExpr(0::Nil))(AntePosition(1, Nil)) &
        prop
  )

  /**
   * {{{Axiom "all substitute".
   *    (\forall x (x=t() -> p(x))) <-> p(t())
   * End.
   * }}}
   * @Derived
   */
  lazy val allSubstitute = derivedAxiom("all substitute",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(\\forall x (x=t() -> p(x))) <-> p(t())".asFormula)),
    equivR(SuccPos(0)) & onBranch(
      //@todo unifications fail here and may have to be constructed manually. Or proved from sequent calculus
      (equivLeftLbl, useAt("all instantiate")(AntePos(0)) & prop),
      (equivRightLbl, allR(SuccPos(0)) &
        useAt("const formula congruence", PosInExpr(1::0::Nil))(SuccPos(0)) & close)
    )
  )


  /**
   * {{{Axiom "vacuous exists quantifier".
   *    (\exists x p()) <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val vacuousExistsAxiom = derivedAxiom("vacuous exists quantifier",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(\\exists x p()) <-> p()".asFormula)),
    useAt(existsDualAxiom, PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("vacuous all quantifier")(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val vacuousExistsT = derivedAxiomT(vacuousExistsAxiom)

  /**
   * {{{Axiom "V[:*] vacuous assign nondet".
   *    [x:=*;]p() <-> p()
   * End.
   * @todo reorient
   * @Derived
   */
  lazy val vacuousBoxAssignNondetAxiom = derivedAxiom("V[:*] vacuous assign nondet",
    Sequent(Nil, IndexedSeq(), IndexedSeq("([x:=*;]p()) <-> p()".asFormula)),
    useAt("[:*] assign nondet")(SuccPosition(0, 0::Nil)) &
      useAt("vacuous all quantifier")(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val vacuousBoxAssignNondetT = derivedAxiomT(vacuousBoxAssignNondetAxiom)

  /**
   * {{{Axiom "V<:*> vacuous assign nondet".
   *    <x:=*;>p() <-> p()
   * End.
   * }}}
   * @todo reorient
   * @Derived
   */
  lazy val vacuousDiamondAssignNondetAxiom = derivedAxiom("V<:*> vacuous assign nondet",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(<x:=*;>p()) <-> p()".asFormula)),
    useAt("<:*> assign nondet")(SuccPosition(0, 0::Nil)) &
      useAt(vacuousExistsAxiom)(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val vacuousDiamondAssignNondetT = derivedAxiomT(vacuousDiamondAssignNondetAxiom)


  /**
   * {{{Axiom "Domain Constraint Conjunction Reordering".
   *    [{c & (H(??) & q(??))}]p(??) <-> [{c & (q(??) & H(??))}]p(??)
   * End.
   * }}}
   * @Derived
   */
  lazy val domainCommute = derivedAxiom("Domain Constraint Conjunction Reordering",
    Sequent(Nil, IndexedSeq(), IndexedSeq("[{c & (H(??) & q(??))}]p(??) <-> [{c & (q(??) & H(??))}]p(??)".asFormula)),
    useAt(andCommute)(SuccPosition(0, 0::0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val domainCommuteT = derivedAxiomT(domainCommute)

  /**
   * {{{Axiom "& commute".
   *    (p() & q()) <-> (q() & p())
   * End.
   * }}}
   * @Derived
   */
  lazy val andCommute = derivedAxiom("& commute",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(p() & q()) <-> (q() & p())".asFormula)),
    prop
  )

  lazy val andCommuteT = derivedAxiomT(andCommute)

  /**
   * {{{Axiom "& associative".
   *    ((p() & q()) & r()) <-> (p() & (q() & r()))
   * End.
   * }}}
   * @Derived
   */
  lazy val andAssoc = derivedAxiom("& associative",
    Sequent(Nil, IndexedSeq(), IndexedSeq("((p() & q()) & r()) <-> (p() & (q() & r()))".asFormula)),
    prop
  )

  lazy val andAssocT = derivedAxiomT(andAssoc)

  /**
   * {{{Axiom "!& deMorgan".
   *    (!(p() & q())) <-> ((!p()) | (!q()))
   * End.
   * }}}
   * @Derived
   */
  lazy val notAnd = derivedAxiom("!& deMorgan",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!(p() & q())) <-> ((!p()) | (!q()))".asFormula)),
    prop
  )

  lazy val notAndT = derivedAxiomT(notAnd)

  /**
   * {{{Axiom "!| deMorgan".
   *    (!(p() | q())) <-> ((!p()) & (!q()))
   * End.
   * }}}
   * @Derived
   */
  lazy val notOr = derivedAxiom("!| deMorgan",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!(p() | q())) <-> ((!p()) & (!q()))".asFormula)),
    prop
  )

  lazy val notOrT = derivedAxiomT(notOr)

  /**
   * {{{Axiom "!-> deMorgan".
   *    (!(p() -> q())) <-> ((p()) & (!q()))
   * End.
   * }}}
   * @Derived
   */
  lazy val notImply = derivedAxiom("!-> deMorgan",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!(p() -> q())) <-> ((p()) & (!q()))".asFormula)),
    prop
  )

  lazy val notImplyT = derivedAxiomT(notImply)

  /**
   * {{{Axiom "!<-> deMorgan".
   *    (!(p() <-> q())) <-> (((p()) & (!q())) | ((!p()) & (q())))
   * End.
   * }}}
   * @Derived
   */
  lazy val notEquiv = derivedAxiom("!<-> deMorgan",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(!(p() <-> q())) <-> (((p()) & (!q())) | ((!p()) & (q())))".asFormula)),
    prop
  )

  lazy val notEquivT = derivedAxiomT(notEquiv)

  /**
   * {{{Axiom "-> expand".
   *    (p() -> q()) <-> ((!p()) | q())
   * End.
   * }}}
   * @Derived
   */
  lazy val implyExpand = derivedAxiom("-> expand",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(p() -> q()) <-> ((!p()) | q())".asFormula)),
    prop
  )

  lazy val implyExpandT = derivedAxiomT(implyExpand)

  /**
   * {{{Axiom "->' derive imply".
   *    (p(??) -> q(??))' <-> (!p(??) | q(??))'
   * End.
   * }}}
   * @Derived by CE
   */
  lazy val Dimply = derivedAxiom("->' derive imply",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(p(??) -> q(??))' <-> (!p(??) | q(??))'".asFormula)),
    useAt(implyExpand)(SuccPosition(0, 0::0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val DimplyT = derivedAxiomT(Dimply)

  /**
   * {{{Axiom "\forall->\exists".
   *    (\forall x p(x)) -> (\exists x p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val forallThenExistsAxiom = derivedAxiom("\\forall->\\exists",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(\\forall x p(x)) -> (\\exists x p(x))".asFormula)),
    //      useAt("all instantiate")(SuccPosition(0, 0::Nil)) &
    //      useAt("exists generalize")(SuccPosition(0, 1::Nil)) &
    //      byUS(equivReflexiveAxiom)
    implyR(SuccPosition(0)) &
      useAt("exists generalize", PosInExpr(1::Nil))(SuccPosition(0)) &
      useAt("all instantiate")(AntePosition(0)) &
      closeId
  )

  /**
   * {{{Axiom "->true".
   *    (p()->true) <-> true
   * End.
   * }}}
   * @Derived
   */
  lazy val impliesTrue = derivedAxiom("->true",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(p()->true) <-> true".asFormula)),
    prop
  )

  lazy val impliesTrueT = derivedAxiomT(impliesTrue)

  /**
   * {{{Axiom "true->".
   *    (true->p()) <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val trueImplies = derivedAxiom("true->",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(true->p()) <-> p()".asFormula)),
    prop
  )

  lazy val trueImpliesT = derivedAxiomT(trueImplies)

  /**
   * {{{Axiom "&true".
   *    (p()&true) <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val andTrue = derivedAxiom("&true",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(p()&true) <-> p()".asFormula)),
    prop
  )

  lazy val andTrueT = derivedAxiomT(andTrue)

  /**
   * {{{Axiom "true&".
   *    (true&p()) <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val trueAnd = derivedAxiom("true&",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(true&p()) <-> p()".asFormula)),
    prop
  )

  lazy val trueAndT = derivedAxiomT(trueAnd)

  /**
   * {{{Axiom "DS differential equation solution".
   *    [{x'=c()}]p(x) <-> \forall t (t>=0 -> [x:=x+(c()*t);]p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val DSnodomain = derivedAxiom("DS differential equation solution",
    Sequent(Nil, IndexedSeq(), IndexedSeq("[{x'=c()}]p(x) <-> \\forall t (t>=0 -> [x:=x+(c()*t);]p(x))".asFormula)),
    useAt("DS& differential equation solution")(SuccPosition(0, 0::Nil)) &
      useAt(impliesTrue)(SuccPosition(0, 0::0::1::0::0::Nil)) &
      useAt("vacuous all quantifier")(SuccPosition(0, 0::0::1::0::Nil)) &
      useAt(trueImplies)(SuccPosition(0, 0::0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  /**
   * {{{Axiom "Dsol differential equation solution".
   *    <{x'=c()}>p(x) <-> \exists t (t>=0 & <x:=x+(c()*t);>p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val DSdnodomain = derivedAxiom("Dsol differential equation solution",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<{x'=c()}>p(x) <-> \\exists t (t>=0 & <x:=x+(c()*t);>p(x))".asFormula)),
    useAt("Dsol& differential equation solution")(SuccPosition(0, 0::Nil)) &
      useAt(impliesTrue)(SuccPosition(0, 0::0::1::0::0::Nil)) &
      useAt("vacuous all quantifier")(SuccPosition(0, 0::0::1::0::Nil)) &
      useAt(trueAnd)(SuccPosition(0, 0::0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  /**
   * {{{Axiom "Dsol& differential equation solution".
   *    <{x'=c()&q(x)}>p(x) <-> \exists t (t>=0 & ((\forall s ((0<=s&s<=t) -> q(x+(c()*s)))) & <x:=x+(c()*t);>p(x)))
   * End.
   * }}}
   * @todo duality from DS&
   */
  lazy val DSd = derivedAxiom("Dsol& differential equation solution",
    Sequent(Nil, IndexedSeq(), IndexedSeq("<{x'=c()&q(x)}>p(x) <-> \\exists t (t>=0 & ((\\forall s ((0<=s&s<=t) -> q(x+(c()*s)))) & <x:=x+(c()*t);>p(x)))".asFormula)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      step(SuccPosition(0, 0::Nil))
  )

  //  lazy val existsDualAxiom: LookupLemma = derivedAxiom("exists dual",
//    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq("\\exists x q(x) <-> !(\\forall x (!q(x)))".asFormula)))
//      (CutRight("\\exists x q(x) <-> !!(\\exists x (!!q(x)))".asFormula, SuccPos(0)), 0)
//      // right branch
//      (EquivifyRight(SuccPos(0)), 1)
//      (AxiomaticRule("CE congruence", USubst(
//        SubstitutionPair(PredicationalOf(context, DotFormula), "\\exists x q(x) <-> !⎵".asFormula) ::
//          SubstitutionPair(pany, "!\\exists x !!q(x)".asFormula) ::
//          SubstitutionPair(qany, "\\forall x !q(x)".asFormula) :: Nil
//      )), 1)
//      (CommuteEquivRight(SuccPos(0)), 1)
//      (Axiom("all dual"), 1)
//      (Close(AntePos(0),SuccPos(0)), 1)
//  )

  /**
   * {{{Axiom "abs".
   *   (abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))
   * End.
   * }}}
   * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]
   */
  lazy val absDef = derivedAxiom("abs",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))".asFormula)),
    TactixLibrary.QE //TactixLibrary.master
  )

  lazy val absT = derivedAxiomT(absDef)

  /**
   * {{{Axiom "min".
   *    (min(f(), g()) = h()) <-> ((f()<=g() & h()=f()) | (f()>g() & h()=g()))
   * End.
   * }}}
   * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]
   */
  lazy val minDef = derivedAxiom("min",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(min(f(), g()) = h()) <-> ((f()<=g() & h()=f()) | (f()>g() & h()=g()))".asFormula)),
    TactixLibrary.QE //TactixLibrary.master
  )

  lazy val minT = derivedAxiomT(minDef)

  /**
   * {{{Axiom "max".
   *    (max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<g() & h()=g()))
   * End.
   * }}}
   * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]
   */
  lazy val maxDef = derivedAxiom("max",
    Sequent(Nil, IndexedSeq(), IndexedSeq("(max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<g() & h()=g()))".asFormula)),
    TactixLibrary.QE //TactixLibrary.master
  )

  lazy val maxT = derivedAxiomT(maxDef)

}
