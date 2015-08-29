/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics.{boxMonotoneT, diamondMonotoneT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{Tactic, ApplyRule}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import scala.annotation.switch
import scala.collection.immutable
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._

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

  /** A Provable proving the derived axiom named id (convenience) */
  def derivedAxiom(name: String): Provable =
    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(derivedAxiomFormula(name).get)))(derivedAxiomR(name), 0)

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
        derivedAxiomDB.add(lemma)
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

  /** Package a Lemma for a derived axiom up as a rule */
  private[tactics] def derivedAxiomR(lemma: String): LookupLemma = {
    require(derivedAxiomDB.contains(lemma), "Lemma has already been added")
    LookupLemma(derivedAxiomDB, lemma)
  }

  /** Package a Lemma for a derived axiom up as a tactic */
  private[tactics] def derivedAxiomT(lemma: Lemma): ApplyRule[LookupLemma] = {
    require(derivedAxiomDB.contains(lemma.name.get), "Lemma has already been added")
    new ApplyRule(derivedAxiomR(lemma.name.get)) {
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
   * Looks up a tactic by name to derive an axiom.
   * @note For interface stability reasons (see [[AxiomTactic.axiomLookupBaseT()]])
   * @param name The name of the derived axiom.
   * @return The tactic to apply the derived axiom, if found. None otherwise.
   */
  def derivedAxiomTactic(name: String): Option[Tactic] = derivedAxiomInfo(name) match {
    case Some((_, t)) => Some(t)
    case None => None
  }

  /**
   * Looks up a derived axiom formula by name.
   * @note For interface stability reasons (see [[AxiomTactic.axiomLookupBaseT()]])
   * @param name The name of the derived axiom.
   * @return The axiom formula, if found. None otherwise.
   */
  def derivedAxiomFormula(name: String): Option[Formula] = derivedAxiomInfo(name) match {
    case Some((fml, _)) => Some(fml)
    case None => None
  }

  /**
   * Looks up infomration about a derived axiom by name.
   * @note For interface stability reasons (see [[AxiomTactic.axiomLookupBaseT()]])
   * @param name The name of the derived axiom.
   * @return The axiom formula and tactic, if found. None otherwise.
   * @note Central index for looking up derived axioms by names.
   */
  private def derivedAxiomInfo(name: String): Option[(Formula, ApplyRule[LookupLemma])] = {(name: @switch) match {
    //@note implemented as match rather than lookup in a map to retain lazy evaluation
    case "<-> reflexive" => Some(equivReflexiveF, equivReflexiveT)
    case "!! double negation" => Some(doubleNegationF, doubleNegationT)
    case "exists dual" => Some(existsDualF, existsDualT)
    case "!exists" => Some(notExistsF, notExistsT)
    case "!all" => Some(notAllF, notAllT)
    case "[] dual" => Some(boxDualF, boxDualT)
    case "<:=> assign" => Some(assigndF, assigndT)
    case ":= assign dual" => Some(assignDualF, assignDualT)
    case "[:=] assign equational" => Some(assignbEquationalF, assignbEquationalT)
    case "[:=] vacuous assign" => Some(vacuousAssignbF, vacuousAssignbT)
    case "<:=> vacuous assign" => Some(vacuousAssigndF, vacuousAssigndT)
    case "<':=> differential assign" => Some(assignDF, assignDT)
    case "<:*> assign nondet" => Some(nondetassigndF, nondetassigndT)
    case "<?> test" => Some(testdF, testdT)
    case "<++> choice" => Some(choicedF, choicedT)
    case "<;> compose" => Some(composedF, composedT)
    case "<*> iterate" => Some(iteratedF, iteratedT)
    case "<*> approx" => Some(loopApproxdF, loopApproxdT)
    case "exists generalize" => Some(existsGeneralizeF, existsGeneralizeT)
    case "all substitute" => Some(allSubstituteF, allSubstituteT)
    case "vacuous exists quantifier" => Some(vacuousExistsF, vacuousExistsT)
    case "V[:*] vacuous assign nondet" => Some(vacuousBoxAssignNondetF, vacuousBoxAssignNondetT)
    case "V<:*> vacuous assign nondet" => Some(vacuousDiamondAssignNondetF, vacuousDiamondAssignNondetT)
    case "DW differential weakening" => Some(DWeakeningF, DWeakeningT)
    case "DS differential equation solution" => Some(DSnodomainF, DSnodomainT)
    case "Dsol& differential equation solution" => Some(DSddomainF, DSddomainT)
    case "Dsol differential equation solution" => Some(DSdnodomainF, DSdnodomainT)
    case "Domain Constraint Conjunction Reordering" => Some(domainCommuteF, domainCommuteT)
    case "& commute" => Some(andCommuteF, andCommuteT)
    case "& associative" => Some(andAssocF, andAssocT)
    case "!& deMorgan" => Some(notAndF, notAndT)
    case "!| deMorgan" => Some(notOrF, notOrT)
    case "!-> deMorgan" => Some(notImplyF, notImplyT)
    case "!<-> deMorgan" => Some(notEquivF, notEquivT)
    case "-> expand" => Some(implyExpandF, implyExpandT)
    case "-> tautology" => Some(implyTautologyF, implyTautologyT)
    case "->' derive imply" => Some(DimplyF, DimplyT)
    case "\\forall->\\exists" => Some(forallThenExistsF, forallThenExistsT)
    case "->true" => Some(impliesTrueF, impliesTrueT)
    case "true->" => Some(trueImpliesF, trueImpliesT)
    case "&true" => Some(andTrueF, andTrueT)
    case "true&" => Some(trueAndF, trueAndT)
    case "0*" => Some(zeroTimesF, zeroTimesT)
    case "0+" => Some(zeroPlusF, zeroPlusT)
    case "x' derive var" => Some(DvarF, DvarT)
    case "' linear" => Some(DlinearF, DlinearT)
    case "' linear right" => Some(DlinearRightF, DlinearRightT)
    case "DG differential pre-ghost" => Some(DGpreghostF, DGpreghostT)
    case "= reflexive" => Some(equalReflexiveF, equalReflexiveT)
    case "* commute" => Some(timesCommuteF, timesCommuteT)
    case "= commute" => Some(equalCommuteF, equalCommuteT)
    case "<=" => Some(lessEqualF, lessEqualT)
    case "= negate" => Some(notNotEqualF, notNotEqualT)
    case "! !=" => derivedAxiomInfo("= negate")
    case "! =" => Some(notEqualF, notEqualT)
    case "! <" => Some(notLessF, notLessT)
    case "! <=" => Some(notLessEqualF, notLessEqualT)
    case "! >" => Some(notGreaterF, notGreaterT)
    case "! >=" => derivedAxiomInfo("< negate")
    case "< negate" => Some(notGreaterEqualF, notGreaterEqualT)
    case ">= flip" => Some(flipGreaterEqualF, flipGreaterEqualT)
    case "> flip" => Some(flipGreaterF, flipGreaterT)
    case "abs" => Some(absF, absT)
    case "min" => Some(minF, minT)
    case "max" => Some(maxF, maxT)
    case _ => None
  } } ensuring(r => r.isEmpty || r.get._2.rule.lemma.name.get == name, "Lookup of DerivedAxiom found correct lemma " + name)

  /**
   * {{{Axiom "<-> reflexive".
   *  p() <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val equivReflexiveF = "p() <-> p()".asFormula
  lazy val equivReflexiveAxiom = derivedAxiom("<-> reflexive",
    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(equivReflexiveF)))
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
  lazy val doubleNegationF = "(!(!p())) <-> p()".asFormula
  lazy val doubleNegationAxiom = derivedAxiom("!! double negation",
    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(doubleNegationF)))
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
  lazy val existsDualF = "(!\\forall x (!p(x))) <-> \\exists x p(x)".asFormula
  lazy val existsDualAxiom = derivedAxiom("exists dual",
    Sequent(Nil, IndexedSeq(), IndexedSeq(existsDualF)),
    useAt("all dual", PosInExpr(1::Nil))(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val existsDualT = derivedAxiomT(existsDualAxiom)

  /**
   * {{{Axiom "!exists".
   *   (!\exists x (p(x))) <-> \forall x (!p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val notExistsF = "(!\\exists x (p(x))) <-> \\forall x (!p(x))".asFormula
  lazy val notExists = derivedAxiom("!exists",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notAllF)),
    useAt("!! double negation", PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt("exists dual")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  lazy val notExistsT = derivedAxiomT(notExists)

  /**
   * {{{Axiom "!all".
   *   (!\forall x (p(x))) <-> \exists x (!p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val notAllF = "(!\\forall x (p(x))) <-> \\exists x (!p(x))".asFormula
  lazy val notAll = derivedAxiom("!all",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notAllF)),
    useAt("!! double negation", PosInExpr(1::Nil))(1, 0::0::0::Nil) &
    useAt("exists dual")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  lazy val notAllT = derivedAxiomT(notAll)

  /**
   * {{{Axiom "![]".
   *   ![a;]p(x) <-> <a;>!p(x)
   * End.
   * }}}
   * @Derived
   */
  lazy val notBoxF = "(![a;]p(x)) <-> (<a;>!p(x))".asFormula
  lazy val notBox = derivedAxiom("![]",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notBoxF)),
    useAt("!! double negation", PosInExpr(1::Nil))(1, 0::0::1::Nil) &
      useAt("<> dual")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  lazy val notBoxT = derivedAxiomT(notBox)

  /**
   * {{{Axiom "!<>".
   *   !<a;>p(x) <-> [a;]!p(x)
   * End.
   * }}}
   * @Derived
   */
  lazy val notDiamondF = "(!<a;>p(x)) <-> ([a;]!p(x))".asFormula
  lazy val notDiamond = derivedAxiom("!<>",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notDiamondF)),
    useAt("!! double negation", PosInExpr(1::Nil))(1, 0::0::1::Nil) &
      useAt("[] dual")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  lazy val notDiamondT = derivedAxiomT(notDiamond)

  /**
   * {{{Axiom "all eliminate".
   *    (\forall x p(??)) -> p(??)
   * End.
   * }}}
   * @todo will clash unlike the converse proof.
   */
  lazy val allEliminateF = "(\\forall x p(??)) -> p(??)".asFormula
  lazy val allEliminateAxiom = derivedAxiom("all eliminate",
    Sequent(Nil, IndexedSeq(), IndexedSeq(allEliminateF)),
    US(SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm), PredOf(Function("p",None,Real,Bool),Anything))::Nil)
  )
  lazy val allEliminateT = derivedAxiomT(allEliminateAxiom)

  /**
   * {{{Axiom "all distribute".
   *   (\forall x (p(x)->q(x))) -> ((\forall x p(x))->(\forall x q(x)))
   * }}}
   */
  // Imply(Forall(Seq(x), Imply(PredOf(p,x),PredOf(q,x))), Imply(Forall(Seq(x),PredOf(p,x)), Forall(Seq(x),PredOf(q,x))))
  lazy val allDistributeF = "(\\forall x (p(x)->q(x))) -> ((\\forall x p(x))->(\\forall x q(x)))".asFormula
  lazy val allDistributeAxiom = derivedAxiom("all distribute",
    Sequent(Nil, IndexedSeq(), IndexedSeq(allDistributeF)),
    implyR(1) & implyR(1) &
      allR(1) &
      allL(Variable("x",None,Real), Variable("x",Some(0),Real))(-2) &
      allL(Variable("x",None,Real), Variable("x",Some(0),Real))(-1) &
      prop
  )
  lazy val allDistributeT = derivedAxiomT(allDistributeAxiom)

  /**
   * {{{Axiom "all quantifier scope".
   *    (\forall x (p(x) & q())) <-> ((\forall x p(x)) & q())
   * End.
   * }}}
   * @todo follows from "all distribute" and "all vacuous"
   */


  /**
   * {{{Axiom "[] dual".
   *    (!<a;>(!p(??))) <-> [a;]p(??)
   * End.
   * }}}
   * @note almost same proof as "exists dual"
   * @Derived
   */
  lazy val boxDualF = "(!<a;>(!p(??))) <-> [a;]p(??)".asFormula
  lazy val boxDualAxiom = derivedAxiom("[] dual",
    Sequent(Nil, IndexedSeq(), IndexedSeq(boxDualF)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val boxDualT = derivedAxiomT(boxDualAxiom)

  /**
   * {{{Axiom "".
   *    [a;]p(??) & <a;>q(??) -> <a;>(p(??) & q(??))
   * End.
   * }}}
   * @Derived
   */
  lazy val boxDiamondPropagationF = "([a;]p(??) & <a;>q(??)) -> <a;>(p(??) & q(??))".asFormula
  lazy val boxDiamondPropagation = derivedAxiom("[]~><> propagation",
    Sequent(Nil, IndexedSeq(), IndexedSeq(boxDiamondPropagationF)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, PosInExpr(0::1::Nil))) &
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, PosInExpr(1::Nil))) &
    cut("[a;]p(??) & [a;]!(p(??)&q(??)) -> [a;]!q(??)".asFormula) & onBranch(
      (cutShowLbl, hide(SuccPosition(0)) &
        cut("[a;](p(??) & !(p(??)&q(??)))".asFormula) & onBranch(
          (cutShowLbl, implyR(SuccPosition(0)) & splitb(SuccPosition(0)) & prop),
          (cutUseLbl, implyR(SuccPosition(0)) & hide(AntePosition(1)) & boxMonotoneT & prop)
        )),
      (cutUseLbl, prop)
    )
  )

  lazy val boxDiamondPropagationT = derivedAxiomT(boxDiamondPropagation)

  /**
   * {{{Axiom "<:=> assign".
   *    <v:=t();>p(v) <-> p(t())
   * End.
   * }}}
   * @Derived
   */
  lazy val assigndF = "<v:=t();>p(v) <-> p(t())".asFormula
  lazy val assigndAxiom = derivedAxiom("<:=> assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq(assigndF)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[:=] assign")(SuccPosition(0, 0::0::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 0::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val assigndT = derivedAxiomT(assigndAxiom)

  /**
   * {{{Axiom ":= assign dual".
   *    <v:=t();>p(v) <-> [v:=t();]p(v)
   * End.
   * }}}
   * @Derived
   */
  lazy val assignDualF = "<v:=t();>p(v) <-> [v:=t();]p(v)".asFormula
  lazy val assignDualAxiom = derivedAxiom(":= assign dual",
    Sequent(Nil, IndexedSeq(), IndexedSeq(assignDualF)),
      useAt("<:=> assign")(SuccPosition(0, PosInExpr(0::Nil))) &
      useAt("[:=] assign")(SuccPosition(0, PosInExpr(1::Nil))) &
      byUS(equivReflexiveAxiom)
  )

  lazy val assignDualT = derivedAxiomT(assignDualAxiom)

  /**
   * {{{Axiom "[:=] assign equational".
   *    [v:=t();]p(v) <-> \forall v (v=t() -> p(v))
   * End.
   * }}}
   * @Derived
   */
  lazy val assignbEquationalF = "[v:=t();]p(v) <-> \\forall v (v=t() -> p(v))".asFormula
  lazy val assignbEquationalAxiom = derivedAxiom("[:=] assign equational",
    Sequent(Nil, IndexedSeq(), IndexedSeq(assignbEquationalF)),
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
  lazy val vacuousAssignbF = "[v:=t();]p() <-> p()".asFormula
  lazy val vacuousAssignbAxiom = derivedAxiom("[:=] vacuous assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq(vacuousAssignbF)),
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
  lazy val vacuousAssigndF = "<v:=t();>p() <-> p()".asFormula
  lazy val vacuousAssigndAxiom = derivedAxiom("<:=> vacuous assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq(vacuousAssigndF)),
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
  lazy val assignDF = "<v':=t();>p(v') <-> p(t())".asFormula
  lazy val assignDAxiom = derivedAxiom("<':=> differential assign",
    Sequent(Nil, IndexedSeq(), IndexedSeq(assignDF)),
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
  lazy val nondetassigndF = "<x:=*;>p(x) <-> (\\exists x p(x))".asFormula
  lazy val nondetassigndAxiom = derivedAxiom("<:*> assign nondet",
    Sequent(Nil, IndexedSeq(), IndexedSeq(nondetassigndF)),
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
  lazy val testdF = "<?H();>p() <-> (H() & p())".asFormula
  lazy val testdAxiom = derivedAxiom("<?> test",
    Sequent(Nil, IndexedSeq(), IndexedSeq(testdF)),
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
  lazy val choicedF = "<a;++b;>p(??) <-> (<a;>p(??) | <b;>p(??))".asFormula
  lazy val choicedAxiom = derivedAxiom("<++> choice",
    Sequent(Nil, IndexedSeq(), IndexedSeq(choicedF)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[++] choice")(SuccPosition(0, 0::0::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::0::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
      prop
  )

  lazy val choicedT = derivedAxiomT(choicedAxiom)

  /**
   * {{{Axiom "<;> compose".
   *    <a;b;>p(??) <-> <a;><b;>p(??)
   * End.
   * }}}
   * @Derived
   */
  lazy val composedF = "<a;b;>p(??) <-> <a;><b;>p(??)".asFormula
  lazy val composedAxiom = derivedAxiom("<;> compose",
    Sequent(Nil, IndexedSeq(), IndexedSeq(composedF)),
    useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 0::Nil)) &
      useAt("[;] compose")(SuccPosition(0, 0::0::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::1::Nil)) &
      useAt("<> dual", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
      useAt(doubleNegationAxiom)(SuccPosition(0, 1::0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val composedT = derivedAxiomT(composedAxiom)

  /**
   * {{{Axiom "<*> iterate".
   *    <{a;}*>p(??) <-> (p(??) | <a;><{a;}*> p(??))
   * End.
   * }}}
   * @Derived
   */
  lazy val iteratedF = "<{a;}*>p(??) <-> (p(??) | <a;><{a;}*> p(??))".asFormula
  lazy val iteratedAxiom = derivedAxiom("<*> iterate",
    Sequent(Nil, IndexedSeq(), IndexedSeq(iteratedF)),
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

  lazy val iteratedT = derivedAxiomT(iteratedAxiom)

  /**
   * {{{Axiom "<*> approx".
   *    <a;>p(??) -> <{a;}*>p(??)
   * End.
   * }}}
   * @Derived
   */
  lazy val loopApproxdF = "<a;>p(??) -> <{a;}*>p(??)".asFormula
  lazy val loopApproxd = derivedAxiom("<*> approx",
    Sequent(Nil, IndexedSeq(), IndexedSeq(loopApproxdF)),
    useAt("<*> iterate")(SuccPosition(0, PosInExpr(1::Nil))) &
    useAt("<*> iterate")(SuccPosition(0, PosInExpr(1::1::1::Nil))) &
    cut("<a;>p(??) -> <a;>(p(??) | <a;><{a;}*>p(??))".asFormula) & onBranch(
      (cutShowLbl, hideT(SuccPosition(0)) & ls(implyR) & diamondMonotoneT & prop),
      (cutUseLbl, prop)
    )
  )

  lazy val loopApproxdT = derivedAxiomT(loopApproxd)


  //@todo this is somewhat indirect. Maybe it'd be better to represent derived axioms merely as Lemma and auto-wrap them within their ApplyRule[LookupLemma] tactics on demand.
  //private def useAt(lem: ApplyRule[LookupLemma]): PositionTactic = TactixLibrary.useAt(lem.rule.lemma.fact)

  /**
   * {{{Axiom "exists generalize".
   *    p(t()) -> (\exists x p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val existsGeneralizeF = "p(t()) -> (\\exists x p(x))".asFormula
  lazy val existsGeneralize = derivedAxiom("exists generalize",
    Sequent(Nil, IndexedSeq(), IndexedSeq(existsGeneralizeF)),
//    useAt("exists dual", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
//      useAt("all instantiate", PosInExpr(0::Nil))(SuccPosition(0, 1::0::Nil)) &
//      prop
      useAt("exists dual", PosInExpr(1::Nil))(SuccPosition(0, 1::Nil)) &
        implyR(SuccPos(0)) &
        notR(SuccPos(0)) &
        useAt("all instantiate", PosInExpr(0::Nil))(AntePosition(1, Nil)) &
        prop
  )

  lazy val existsGeneralizeT = derivedAxiomT(existsGeneralize)

  /**
   * {{{Axiom "all substitute".
   *    (\forall x (x=t() -> p(x))) <-> p(t())
   * End.
   * }}}
   * @Derived
   */
  lazy val allSubstituteF = "(\\forall x (x=t() -> p(x))) <-> p(t())".asFormula
  lazy val allSubstitute = derivedAxiom("all substitute",
    Sequent(Nil, IndexedSeq(), IndexedSeq(allSubstituteF)),
    equivR(SuccPos(0)) & onBranch(
      //@note unifications fail here -> proved from sequent calculus
      (equivLeftLbl, allL(Variable("x"), "t()".asTerm)(AntePos(0)) & implyL(AntePos(0)) && (equalReflexive(SuccPos(1)), close)),
      (equivRightLbl, allR(SuccPos(0)) & implyR(SuccPos(0)) & EqualityRewritingImpl.constFormulaCongruenceT(AntePos(1), left=true)(SuccPos(0)) & close)
    )
  )

  lazy val allSubstituteT = derivedAxiomT(allSubstitute)


  /**
   * {{{Axiom "vacuous exists quantifier".
   *    (\exists x p()) <-> p()
   * End.
   * }}}
   * @Derived
   */
  lazy val vacuousExistsF = "(\\exists x p()) <-> p()".asFormula
  lazy val vacuousExistsAxiom = derivedAxiom("vacuous exists quantifier",
    Sequent(Nil, IndexedSeq(), IndexedSeq(vacuousExistsF)),
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
  lazy val vacuousBoxAssignNondetF = "([x:=*;]p()) <-> p()".asFormula
  lazy val vacuousBoxAssignNondetAxiom = derivedAxiom("V[:*] vacuous assign nondet",
    Sequent(Nil, IndexedSeq(), IndexedSeq(vacuousBoxAssignNondetF)),
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
  lazy val vacuousDiamondAssignNondetF = "(<x:=*;>p()) <-> p()".asFormula
  lazy val vacuousDiamondAssignNondetAxiom = derivedAxiom("V<:*> vacuous assign nondet",
    Sequent(Nil, IndexedSeq(), IndexedSeq(vacuousDiamondAssignNondetF)),
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
  lazy val domainCommuteF = "[{c & (H(??) & q(??))}]p(??) <-> [{c & (q(??) & H(??))}]p(??)".asFormula
  lazy val domainCommute = derivedAxiom("Domain Constraint Conjunction Reordering",
    Sequent(Nil, IndexedSeq(), IndexedSeq(domainCommuteF)),
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
  lazy val andCommuteF = "(p() & q()) <-> (q() & p())".asFormula
  lazy val andCommute = derivedAxiom("& commute",
    Sequent(Nil, IndexedSeq(), IndexedSeq(andCommuteF)),
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
  lazy val andAssocF = "((p() & q()) & r()) <-> (p() & (q() & r()))".asFormula
  lazy val andAssoc = derivedAxiom("& associative",
    Sequent(Nil, IndexedSeq(), IndexedSeq(andAssocF)),
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
  lazy val notAndF = "(!(p() & q())) <-> ((!p()) | (!q()))".asFormula
  lazy val notAnd = derivedAxiom("!& deMorgan",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notAndF)),
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
  lazy val notOrF = "(!(p() | q())) <-> ((!p()) & (!q()))".asFormula
  lazy val notOr = derivedAxiom("!| deMorgan",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notOrF)),
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
  lazy val notImplyF = "(!(p() -> q())) <-> ((p()) & (!q()))".asFormula
  lazy val notImply = derivedAxiom("!-> deMorgan",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notImplyF)),
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
  lazy val notEquivF = "(!(p() <-> q())) <-> (((p()) & (!q())) | ((!p()) & (q())))".asFormula
  lazy val notEquiv = derivedAxiom("!<-> deMorgan",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notEquivF)),
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
  lazy val implyExpandF = "(p() -> q()) <-> ((!p()) | q())".asFormula
  lazy val implyExpand = derivedAxiom("-> expand",
    Sequent(Nil, IndexedSeq(), IndexedSeq(implyExpandF)),
    prop
  )

  lazy val implyExpandT = derivedAxiomT(implyExpand)

  /**
   * {{{Axiom "-> tautology".
   *    (p() -> (q() -> p()&q())) <-> true
   * End.
   * }}}
   * @Derived
   */
  lazy val implyTautologyF = "(p() -> (q() -> p()&q())) <-> true".asFormula
  lazy val implyTautology = derivedAxiom("-> tautology",
    Sequent(Nil, IndexedSeq(), IndexedSeq(implyTautologyF)),
    prop
  )

  lazy val implyTautologyT = derivedAxiomT(implyTautology)

  /**
   * {{{Axiom "->' derive imply".
   *    (p(??) -> q(??))' <-> (!p(??) | q(??))'
   * End.
   * }}}
   * @Derived by CE
   */
  lazy val DimplyF = "(p(??) -> q(??))' <-> (!p(??) | q(??))'".asFormula
  lazy val Dimply = derivedAxiom("->' derive imply",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DimplyF)),
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
  lazy val forallThenExistsF = "(\\forall x p(x)) -> (\\exists x p(x))".asFormula
  lazy val forallThenExistsAxiom = derivedAxiom("\\forall->\\exists",
    Sequent(Nil, IndexedSeq(), IndexedSeq(forallThenExistsF)),
    //      useAt("all instantiate")(SuccPosition(0, 0::Nil)) &
    //      useAt("exists generalize")(SuccPosition(0, 1::Nil)) &
    //      byUS(equivReflexiveAxiom)
    implyR(SuccPosition(0)) &
      useAt("exists generalize", PosInExpr(1::Nil))(SuccPosition(0)) &
      useAt("all instantiate")(AntePosition(0)) &
      closeId
  )

  lazy val forallThenExistsT = derivedAxiomT(forallThenExistsAxiom)

  /**
   * {{{Axiom "->true".
   *    (p()->true) <-> true
   * End.
   * }}}
   * @Derived
   */
  lazy val impliesTrueF = "(p()->true) <-> true".asFormula
  lazy val impliesTrue = derivedAxiom("->true",
    Sequent(Nil, IndexedSeq(), IndexedSeq(impliesTrueF)),
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
  lazy val trueImpliesF = "(true->p()) <-> p()".asFormula
  lazy val trueImplies = derivedAxiom("true->",
    Sequent(Nil, IndexedSeq(), IndexedSeq(trueImpliesF)),
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
  lazy val andTrueF = "(p()&true) <-> p()".asFormula
  lazy val andTrue = derivedAxiom("&true",
    Sequent(Nil, IndexedSeq(), IndexedSeq(andTrueF)),
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
  lazy val trueAndF = "(true&p()) <-> p()".asFormula
  lazy val trueAnd = derivedAxiom("true&",
    Sequent(Nil, IndexedSeq(), IndexedSeq(trueAndF)),
    prop
  )

  lazy val trueAndT = derivedAxiomT(trueAnd)

  /**
   * {{{Axiom "0*".
   *    (0*f()) = 0
   * End.
   * }}}
   * @Derived
   */
  lazy val zeroTimesF = "(0*f()) = 0".asFormula
  lazy val zeroTimes = derivedAxiom("0*",
    Sequent(Nil, IndexedSeq(), IndexedSeq(zeroTimesF)),
    QE
  )

  lazy val zeroTimesT = derivedAxiomT(zeroTimes)

  /**
   * {{{Axiom "0+".
   *    (0+f()) = f()
   * End.
   * }}}
   * @Derived
   */
  lazy val zeroPlusF = "(0+f()) = f()".asFormula
  lazy val zeroPlus = derivedAxiom("0+",
    Sequent(Nil, IndexedSeq(), IndexedSeq(zeroPlusF)),
    QE
  )

  lazy val zeroPlusT = derivedAxiomT(zeroPlus)


  // differential equations

  /**
   * {{{Axiom "DW differential weakening".
   *    [{c&H(??)}]p(??) <-> ([{c&H(??)}](H(??)->p(??)))
   *    /* [x'=f(x)&q(x);]p(x) <-> ([x'=f(x)&q(x);](q(x)->p(x))) THEORY */
   * End.
   * }}}
   * @see footnote 3 in "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, volume 9195 of LNCS, pages 467-481. Springer, 2015. arXiv 1503.01981, 2015."
   */
  lazy val DWeakeningF = "[{c&H(??)}]p(??) <-> ([{c&H(??)}](H(??)->p(??)))".asFormula
  lazy val DWeakening = derivedAxiom("DW differential weakening",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DWeakeningF)),
    equivR(1) & onBranch(
      (BranchLabels.equivLeftLbl,
        cut("[{c&H(??)}](p(??)->(H(??)->p(??)))".asFormula) & onBranch(
          (BranchLabels.cutShowLbl, cohide(2) & G & prop),
          (BranchLabels.cutUseLbl,
            useAt("K modal modus ponens")(-2) & implyL(-2) & (close, close) )
        )
        ),
      (BranchLabels.equivRightLbl,
        useAt("K modal modus ponens")(-1) &
          implyL(-1) & (cohide(2) & byUS("DW"), close)
        )
    )
  )
  lazy val DWeakeningT = derivedAxiomT(DWeakening)

  /**
   * {{{Axiom "DS diamond differential skip".
   *    <{c&H(??)}>p(??) <- H(??)&p(??)
   * End.
   * }}}
   * @Derived
   */
  lazy val DskipdF = "<{c&H(??)}>p(??) <- H(??)&p(??)".asFormula
  lazy val Dskipd = derivedAxiom("DX diamond differential skip",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DskipdF)),
    useAt("!! double negation", PosInExpr(1::Nil))(SuccPosition(0, PosInExpr(0::Nil))) &
    useAt("!& deMorgan")(SuccPosition(0, PosInExpr(0::0::Nil))) &
    useAt("-> expand", PosInExpr(1::Nil))(SuccPosition(0, PosInExpr(0::0::Nil))) &
    ODETactics.diffSkipT(DifferentialProgramConst("c"))(SuccPosition(0, PosInExpr(0::0::Nil))) &
    useAt("<> dual")(SuccPosition(0, PosInExpr(0::Nil))) & implyR(SuccPosition(0)) & close
  )

  /**
   * {{{Axiom "DS differential equation solution".
   *    [{x'=c()}]p(x) <-> \forall t (t>=0 -> [x:=x+(c()*t);]p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val DSnodomainF = "[{x'=c()}]p(x) <-> \\forall t (t>=0 -> [x:=x+(c()*t);]p(x))".asFormula
  lazy val DSnodomain = derivedAxiom("DS differential equation solution",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DSnodomainF)),
    useAt("DS& differential equation solution")(SuccPosition(0, 0::Nil)) &
      useAt(impliesTrue)(SuccPosition(0, 0::0::1::0::0::Nil)) &
      useAt("vacuous all quantifier")(SuccPosition(0, 0::0::1::0::Nil)) &
      useAt(trueImplies)(SuccPosition(0, 0::0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val DSnodomainT = derivedAxiomT(DSnodomain)

  /**
   * {{{Axiom "Dsol differential equation solution".
   *    <{x'=c()}>p(x) <-> \exists t (t>=0 & <x:=x+(c()*t);>p(x))
   * End.
   * }}}
   * @Derived
   */
  lazy val DSdnodomainF = "<{x'=c()}>p(x) <-> \\exists t (t>=0 & <x:=x+(c()*t);>p(x))".asFormula
  lazy val DSdnodomain = derivedAxiom("Dsol differential equation solution",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DSdnodomainF)),
    useAt("Dsol& differential equation solution")(SuccPosition(0, 0::Nil)) &
      useAt(impliesTrue)(SuccPosition(0, 0::0::1::0::0::Nil)) &
      useAt("vacuous all quantifier")(SuccPosition(0, 0::0::1::0::Nil)) &
      useAt(trueAnd)(SuccPosition(0, 0::0::1::Nil)) &
      byUS(equivReflexiveAxiom)
  )

  lazy val DSdnodomainT = derivedAxiomT(DSdnodomain)

  /**
   * {{{Axiom "Dsol& differential equation solution".
   *    <{x'=c()&q(x)}>p(x) <-> \exists t (t>=0 & ((\forall s ((0<=s&s<=t) -> q(x+(c()*s)))) & <x:=x+(c()*t);>p(x)))
   * End.
   * }}}
   */
  lazy val DSddomainF = "<{x'=c()&q(x)}>p(x) <-> \\exists t (t>=0 & ((\\forall s ((0<=s&s<=t) -> q(x+(c()*s)))) & <x:=x+(c()*t);>p(x)))".asFormula
  lazy val DSddomain = derivedAxiom("Dsol& differential equation solution",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DSddomainF)),
    useAt("<> dual", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("DS& differential equation solution")(1, 0::0::Nil) &
      useAt("!all")(1, 0::Nil) & //step(1, 0::Nil) &
      useAt("!-> deMorgan")(1, 0::0::Nil) &
      useAt("!-> deMorgan")(1, 0::0::1::Nil) &
      useAt("<> dual")(1, 0::0::1::1::Nil) &
      //useAt("& associative", PosInExpr(1::Nil))(1, 0::0::Nil) &
      byUS("<-> reflexive")
  )

  lazy val DSddomainT = derivedAxiomT(DSddomain)

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
   * {{{Axiom "DG differential pre-ghost".
   *    [{c&H(??)}]p(??) <-> \exists y [{y'=(t()*y)+s(),c&H(??)}]p(??)
   *    // [x'=f(x)&q(x);]p(x) <-> \exists y [{y'=(a(x)*y)+b(x), x'=f(x))&q(x)}]p(x) THEORY
   * End.
   * }}}
   * Pre Differential Auxiliary / Differential Ghost -- not strictly necessary but saves a lot of reordering work.
   */
  lazy val DGpreghostF = "[{c&H(??)}]p(??) <-> \\exists y [{y'=(t()*y)+s(),c&H(??)}]p(??)".asFormula
  lazy val DGpreghost = derivedAxiom("DG differential pre-ghost",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DGpreghostF)),
    useAt("DG differential ghost")(SuccPosition(0, 0::Nil)) &
      useAt(", commute")(SuccPosition(0, 0::0::Nil)) &
      byUS(equivReflexiveAxiom)
  )
  lazy val DGpreghostT = derivedAxiomT(DGpreghost)

  /**
   * {{{Axiom "x' derive var".
   *    (x_)' = x_'
   * End.
   * }}}
   * @todo derive
   */
  lazy val DvarF = "((x_)' = x_')".asFormula
  lazy val Dvar = derivedAxiom("'x derive var",
    Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(DvarF)))
      (CutRight("\\forall x_ ((x_)' = x_')".asFormula, SuccPos(0)), 0)
      // right branch
      (UniformSubstitutionRule.UniformSubstitutionRuleForward(Axiom.axiom("all eliminate"),
        USubst(SubstitutionPair(PredOf(Function("p_",None,Real,Bool),Anything), DvarF)::Nil)), 0)
      // left branch
      (Axiom.axiom("x' derive variable"), 0)
    /*TacticLibrary.instantiateQuanT(Variable("x_",None,Real), Variable("x",None,Real))(1) &
      byUS("= reflexive")*/
  )
  lazy val DvarT = derivedAxiomT(Dvar)
  /**
   * {{{Axiom "' linear".
   *    (c()*f(??))' = c()*(f(??))'
   * End.
   * }}}
   */
  lazy val DlinearF = "(c()*f(??))' = c()*(f(??))'".asFormula
  lazy val Dlinear = derivedAxiom("' linear",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DlinearF)),
    useAt("*' derive product")(SuccPosition(0, 0::Nil)) &
      useAt("c()' derive constant fn")(SuccPosition(0, 0::0::0::Nil)) &
      useAt(zeroTimes)(SuccPosition(0, 0::0::Nil)) &
      useAt(zeroPlus)(SuccPosition(0, 0::Nil)) &
      byUS("= reflexive")
  )
  lazy val DlinearT = derivedAxiomT(Dlinear)
  /**
   * {{{Axiom "' linear right".
   *    (f(??)*c())' = f(??)'*c()
   * End.
   * }}}
   */
  lazy val DlinearRightF = "(f(??)*c())' = (f(??))'*c()".asFormula
  lazy val DlinearRight = derivedAxiom("' linear right",
    Sequent(Nil, IndexedSeq(), IndexedSeq(DlinearRightF)),
    useAt("* commute")(SuccPosition(0, 0::0::Nil)) &
      useAt("* commute")(SuccPosition(0, 1::Nil)) &
      by(Dlinear)
  )
  lazy val DlinearRightT = derivedAxiomT(DlinearRight)

  // real arithmetic

  /**
   * {{{Axiom "= reflexive".
   *    s() = s()
   * End.
   * }}}
   */
  lazy val equalReflexiveF = "s() = s()".asFormula
  lazy val equalReflex = derivedAxiom("= reflexive",
    Sequent(Nil, IndexedSeq(), IndexedSeq(equalReflexiveF)),
    QE
  )
  lazy val equalReflexiveT = derivedAxiomT(equalReflex)

  /**
   * {{{Axiom "= commute".
   *   (f()=g()) <-> (g()=f())
   * End.
   * }}}
   */
  lazy val equalCommuteF = "(f()=g()) <-> (g()=f())".asFormula
  lazy val equalCommute = derivedAxiom("= commute",
    Sequent(Nil, IndexedSeq(), IndexedSeq(equalCommuteF)),
    QE
  )
  lazy val equalCommuteT = derivedAxiomT(equalCommute)
  /**
   * {{{Axiom "* commute".
   *   (f()*g()) = (g()*f())
   * End.
   * }}}
   */
  lazy val timesCommuteF = "(f()*g()) = (g()*f())".asFormula
  lazy val timesCommute = derivedAxiom("* commute",
    Sequent(Nil, IndexedSeq(), IndexedSeq(timesCommuteF)),
    QE
  )
  lazy val timesCommuteT = derivedAxiomT(timesCommute)

  /**
   * {{{Axiom "<=".
   *   (f()<=g()) <-> ((f()<g()) | (f()=g()))
   * End.
   * }}}
   */
  lazy val lessEqualF = "(f()<=g()) <-> ((f()<g()) | (f()=g()))".asFormula
  lazy val lessEqual = derivedAxiom("<=",
    Sequent(Nil, IndexedSeq(), IndexedSeq(lessEqualF)),
    QE
  )
  lazy val lessEqualT = derivedAxiomT(lessEqual)
  /**
   * {{{Axiom "= negate".
   *   (!(f() != g())) <-> (f() = g())
   * End.
   * }}}
   */
  lazy val notNotEqualF = "(!(f() != g())) <-> (f() = g())".asFormula
  lazy val notNotEqual = derivedAxiom("= negate",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notNotEqualF)),
    QE
  )
  lazy val notNotEqualT = derivedAxiomT(notNotEqual)
  /**
   * {{{Axiom "! =".
   *   !(f() = g()) <-> f() != g()
   * End.
   * }}}
   */
  lazy val notEqualF = "((!(f() = g())) <-> (f() != g())".asFormula
  lazy val notEqual = derivedAxiom("= negate",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notEqualF)),
    QE
  )
  lazy val notEqualT = derivedAxiomT(notEqual)
  /**
   * {{{Axiom "! >".
   *   (!(f() > g())) <-> (f() <= g())
   * End.
   * }}}
   */
  lazy val notGreaterF = "(!(f() > g())) <-> (f() <= g())".asFormula
  lazy val notGreater = derivedAxiom("! >",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notGreaterF)),
    QE
  )
  lazy val notGreaterT = derivedAxiomT(notGreater)
  /**
   * {{{Axiom "! <".
   *   (!(f() < g())) <-> (f() >= g())
   * End.
   * }}}
   * @todo derive more efficiently via flip
   */
  lazy val notLessF = "(!(f() < g())) <-> (f() >= g())".asFormula
  lazy val notLess = derivedAxiom("! <",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notLessF)),
    QE
  )
  lazy val notLessT = derivedAxiomT(notLess)
  /**
   * {{{Axiom "! <=".
   *   (!(f() <= g())) <-> (f() > g())
   * End.
   * }}}
   * @todo derive more efficiently via flip
   */
  lazy val notLessEqualF = "(!(f() <= g())) <-> (f() > g())".asFormula
  lazy val notLessEqual = derivedAxiom("! <",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notLessEqualF)),
    QE
  )
  lazy val notLessEqualT = derivedAxiomT(notLessEqual)
  /**
   * {{{Axiom "< negate".
   *   (!(f() >= g())) <-> (f() < g())
   * End.
   * }}}
   */
  lazy val notGreaterEqualF = "(!(f() >= g())) <-> (f() < g())".asFormula
  lazy val notGreaterEqual = derivedAxiom("< negate",
    Sequent(Nil, IndexedSeq(), IndexedSeq(notGreaterEqualF)),
    QE
  )
  lazy val notGreaterEqualT = derivedAxiomT(notGreaterEqual)
  /**
   * {{{Axiom ">= flip".
   *   (f() >= g()) <-> (g() <= f())
   * End.
   * }}}
   */
  lazy val flipGreaterEqualF = "(f() >= g()) <-> (g() <= f())".asFormula
  lazy val flipGreaterEqual = derivedAxiom(">= flip",
    Sequent(Nil, IndexedSeq(), IndexedSeq(flipGreaterEqualF)),
    QE
  )
  lazy val flipGreaterEqualT = derivedAxiomT(flipGreaterEqual)
  /**
   * {{{Axiom "> flip".
   *   (f() > g()) <-> (g() < f())
   * End.
  */
  lazy val flipGreaterF = "(f() > g()) <-> (g() < f())".asFormula
  lazy val flipGreater = derivedAxiom("> flip",
    Sequent(Nil, IndexedSeq(), IndexedSeq(flipGreaterF)),
    QE
  )
  lazy val flipGreaterT = derivedAxiomT(flipGreater)

  /* Unused so far @todo use f(), g() etc instead of r,s
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
  (s<t) <-> (0 < t-s)
End.

Axiom ">".
  (s>t) <-> (t<s)
End.
*/


  /**
   * {{{Axiom "abs".
   *   (abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))
   * End.
   * }}}
   * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]
   */
  lazy val absF = "(abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))".asFormula
  lazy val absDef = derivedAxiom("abs",
    Sequent(Nil, IndexedSeq(), IndexedSeq(absF)),
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
  lazy val minF = "(min(f(), g()) = h()) <-> ((f()<=g() & h()=f()) | (f()>g() & h()=g()))".asFormula
  lazy val minDef = derivedAxiom("min",
    Sequent(Nil, IndexedSeq(), IndexedSeq(minF)),
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
  lazy val maxF = "(max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<g() & h()=g()))".asFormula
  lazy val maxDef = derivedAxiom("max",
    Sequent(Nil, IndexedSeq(), IndexedSeq(maxF)),
    TactixLibrary.QE //TactixLibrary.master
  )

  lazy val maxT = derivedAxiomT(maxDef)

}
