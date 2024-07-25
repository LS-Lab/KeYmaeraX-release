/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.Logging
import org.keymaerax.bellerophon._
import org.keymaerax.btactics.FOQuantifierTactics.allInstantiateInverse
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.btactics.macros.DerivationInfoAugmentors._
import org.keymaerax.btactics.macros._
import org.keymaerax.core._
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.{PosInExpr, RenUSubst}
import org.keymaerax.lemma.{Lemma, LemmaDB, LemmaDBFactory}
import org.keymaerax.parser.Declaration
import org.keymaerax.parser.StringConverter._
import org.keymaerax.pt._
import org.keymaerax.tools.ToolEvidence

import scala.annotation.nowarn
import scala.collection.immutable._
import scala.collection.{immutable, mutable}
import scala.reflect.runtime.universe.{Assign => _, _}
import scala.reflect.runtime.{universe => ru}

/**
 * Central Database of Derived Axioms and Derived Axiomatic Rules, including information about core axioms and axiomatic
 * rules from [[[org.keymaerax.core.AxiomBase]]. This registry of [[[org.keymaerax.btactics.macros.AxiomInfo]] also
 * provides meta information for matching keys and recursors for unificiation and chasing using the
 * [[[org.keymaerax.btactics.macros.Axiom @Axiom]] annotation.
 *
 * =Using Axioms and Axiomatic Rules=
 *
 * Using a (derived) axiom merely requires indicating the position where to use it:
 * {{{
 *   UnifyUSCalculus.useAt(Ax.choiceb)(1)
 * }}}
 * Closing a proof or using an axiomatic rule after unification works as follows:
 * {{{
 *   UnifyUSCalculus.byUS(Ax.choiceb)
 * }}}
 * Closing a proof or using an axiomatic rule verbatim without unification works as follows:
 * {{{
 *   UnifyUSCalculus.by(Ax.choiceb)
 * }}}
 * Equivalently one can also write `TactixLibrary.useAt` or `TactixLibrary.byUS` because [[TactixLibrary]] extends
 * [[UnifyUSCalculus]].
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.core.AxiomBase]]
 * @see
 *   [[org.keymaerax.btactics.macros.AxiomInfo]]
 * @see
 *   [[UnifyUSCalculus.matcherFor()]]
 * @note
 *   To simplify bootstrap and avoid dependency management, the proofs of the derived axioms are written with explicit
 *   reference to other scala-objects representing provables (which will be proved on demand) as opposed to by referring
 *   to the names, which needs a map canonicalName->tacticOnDemand.
 * @note
 *   Lemmas are lazy vals, since their proofs may need a fully setup prover with QE
 * @note
 *   Derived axioms use the Provable facts of other derived axioms in order to avoid initialization cycles with
 *   AxiomInfo's contract checking.
 */
@nowarn("cat=deprecation&origin=org.keymaerax.btactics.UnifyUSCalculus.by")
object Ax extends Logging {

  private val DerivedAxiomProvableSig = ProvableSig // NoProofTermProvable
  /** Database for derived axioms */
  private val derivedAxiomDB: LemmaDB = LemmaDBFactory.lemmaDB

  type LemmaID = String

  private val AUTO_INSERT: Boolean = true

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  def derivedFact(info: DerivedAxiomInfo, fact: ProvableSig): DerivedAxiomInfo = {
    val lemmaName = info.storedName
    require(
      fact.isProved,
      "only proved Provables would be accepted as derived axioms: " + info.canonicalName + " got\n" + fact,
    )
    val npt = ElidingProvable(fact.underlyingProvable, fact.defs)
    val alternativeFact =
      if (ProvableSig.PROOF_TERMS_ENABLED) { TermProvable(npt, AxiomTerm(lemmaName), fact.defs) }
      else { npt }
    // create evidence (traces input into tool and output from tool)
    val evidence = ToolEvidence(immutable.List("input" -> npt.toString, "output" -> "true")) :: Nil
    // Makes it so we have the same provablesig when loading vs. storing
    val lemma = Lemma(alternativeFact, Lemma.requiredEvidence(alternativeFact, evidence), Some(lemmaName))
    val insertedLemma =
      if (!AUTO_INSERT) { lemma }
      else {
        /* @todo BUG does not work at the moment because lemmaDB adds some evidence to the lemmas and thus equality
         * (and thus contains) no longer means what this code thinks it means. */
        // first check whether the lemma DB already contains identical lemma name
        val lemmaID =
          if (derivedAxiomDB.contains(lemmaName)) {
            // identical lemma contents with identical name, so reuse ID
            derivedAxiomDB.get(lemmaName) match {
              case Some(storedLemma) =>
                if (storedLemma != lemma) {
                  throw new IllegalStateException(
                    "Prover already has a different lemma filed under the same name " + derivedAxiomDB
                      .get(lemmaName) + " (lemma " + info
                      .canonicalName + " stored in file name " + lemmaName + ") instead of " + lemma
                  )
                } else { lemma.name.get }
              case None => lemma.name.get
            }
          } else { derivedAxiomDB.add(lemma) }
        derivedAxiomDB.get(lemmaID).get
      }
    info.setLemma(insertedLemma)
    info
  }

  def derivedRule(info: DerivedRuleInfo, fact: ProvableSig): DerivedRuleInfo = {
    // create evidence (traces input into tool and output from tool)
    val evidence = ToolEvidence(immutable.List("input" -> fact.toString, "output" -> "true")) :: Nil
    val lemmaName = info.storedName
    val lemma = Lemma(fact, Lemma.requiredEvidence(fact, evidence), Some(lemmaName))
    val insertedLemma =
      if (!AUTO_INSERT) { lemma }
      else {
        // first check whether the lemma DB already contains identical lemma name
        val lemmaID =
          if (derivedAxiomDB.contains(lemmaName)) {
            // identical lemma contents with identical name, so reuse ID
            if (derivedAxiomDB.get(lemmaName).contains(lemma)) lemma.name.get
            else {
              throw new IllegalStateException(
                s"Prover already has a different lemma filed under the same name: ${derivedAxiomDB
                    .get(lemmaName)} (lemma ${info.codeName} stored in file $lemmaName) instead of $lemma"
              )
            }
          } else { derivedAxiomDB.add(lemma) }
        derivedAxiomDB.get(lemmaID).get
      }
    info.setLemma(insertedLemma)
    info
  }

  private[this] def derivedRuleSequent(
      info: DerivedRuleInfo,
      derived: => Sequent,
      tactic: => BelleExpr,
  ): DerivedRuleInfo = {
    val storageName = info.storedName
    val lemma = derivedAxiomDB.get(storageName) match {
      case Some(lemma) => lemma
      case None =>
        val witness = TactixLibrary.proveBy(derived, tactic)
        derivedRule(info, witness).lemma
    }
    info.setLemma(lemma)
    info
  }

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  def derivedAxiomFromFact(info: DerivedAxiomInfo, derived: Formula, fact: ProvableSig): DerivedAxiomInfo = derivedFact(
    info,
    fact,
  ) ensuring (
    info =>
      DerivationInfoAugmentors.ProvableInfoAugmentor(info).provable.conclusion == Sequent(
        immutable.IndexedSeq(),
        immutable.IndexedSeq(derived),
      ),
    "derivedAxioms's fact indeed proved the expected formula.\n" + derived + "\nproved by\n" + fact
  )

  /**
   * Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available
   */
  def derivedAxiom(info: DerivedAxiomInfo, derived: => Sequent, tactic: => BelleExpr): DerivedAxiomInfo = {
    val lemma = derivedAxiomDB.get(info.storedName) match {
      case Some(lemma) => lemma
      case None =>
        val witness = TactixLibrary.proveBy(derived, tactic)
        assert(
          witness.isProved,
          "tactics proving derived axioms should produce proved Provables: " + info.canonicalName + " got\n" + witness,
        )
        derivedFact(info, witness).lemma
    }
    info.setLemma(lemma)
    info
  }

  /**
   * Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available
   */
  def derivedFormula(info: DerivedAxiomInfo, derived: Formula, tactic: => BelleExpr): DerivedAxiomInfo =
    derivedAxiom(info, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(derived)), tactic)

  private val v = Variable("x_", None, Real)
  private val anonv = ProgramConst("a_", Except(v :: Nil))
  private val Jany = UnitPredicational("J", AnyArg)

  /** populates the derived lemma database with all of the lemmas in the case statement above. */
  private[keymaerax] def prepopulateDerivedLemmaDatabase(): Unit = {
    require(AUTO_INSERT, "AUTO_INSERT should be on if lemma database is being pre-populated.")

    val lemmas = getClass.getDeclaredFields.filter(f => classOf[StorableInfo].isAssignableFrom(f.getType))
    val fns = lemmas.map(_.getName)

    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(ru.typeOf[Ax.type].termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    // @note lazy vals have a "hidden" getter method that does the initialization
    val fields = fns.map(fn => ru.typeOf[Ax.type].member(ru.TermName(fn)).asMethod.getter.asMethod)
    val fieldMirrors = fields.map(im.reflectMethod)

    val failures = mutable.Buffer.empty[(String, Throwable)]
    fieldMirrors
      .indices
      .foreach(idx => {
        try {
          val fm = fieldMirrors(idx)
          logger.info("Deriving: " + fm.symbol.fullName + "...")
          fm()
          logger.info("done")
          DerivationInfo.seeName(fm.symbol.name.toString)
        } catch {
          case e: Throwable =>
            failures += (fns(idx) -> e)
            logger.warn("WARNING: Failed to add derived lemma.", e)
        }
      })
    if (failures.nonEmpty) throw new Exception(
      s"WARNING: Encountered ${failures.size} errors when trying to populate DerivedAxioms database. Unable to derive:\n" + failures
        .map(_._1)
        .mkString("\n"),
      failures.head._2,
    )
  }

  // ***************
  // Core Axiomatic Rules   see [[AxiomBase]]
  // ***************

  @Derivation
  val CQrule: AxiomaticRuleInfo = AxiomaticRuleInfo.create(name = "CQrule", canonicalName = "CQ equation congruence")

  @Derivation
  val CErule: AxiomaticRuleInfo = AxiomaticRuleInfo.create(name = "CErule", canonicalName = "CE congruence")

  @Derivation
  val mondrule: AxiomaticRuleInfo = AxiomaticRuleInfo.create(name = "mondrule", canonicalName = "<> monotone")

  @Derivation
  val FPrule: AxiomaticRuleInfo = AxiomaticRuleInfo.create(
    name = "FPrule",
    canonicalName = "FP fixpoint",
    displayLevel = DisplayLevel.Browse,
    displayPremises = "P | <a>Q |- Q",
    displayConclusion = "<a*>P |- Q",
  )

  @Derivation
  val conrule: AxiomaticRuleInfo = AxiomaticRuleInfo.create(name = "conrule", canonicalName = "con convergence")

  // ***************
  // Core Axioms   see [[AxiomBase]]
  // ***************

  // Hybrid Programs / Hybrid Games

  // @note default key = 0::Nil, recursor = (Nil)::Nil for direct reduction of LHS to RHS without substructure.
  @Derivation
  val diamond: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "diamond",
    canonicalName = "<> diamond",
    displayName = Some("<·>"),
    displayNameAscii = Some("<.>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__&not;[a]&not;P__↔&langle;a&rangle;P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val assignbAxiom: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "assignbAxiom",
    canonicalName = "[:=] assign",
    displayName = Some("[:=]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[x:=e]p(x)__↔p(e)",
    key = "0",
    recursor = "*",
    unifier = Unifier.Full,
  )

  @Derivation
  val assignbeq: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "assignbeq",
    canonicalName = "[:=] assign equality",
    displayName = Some("[:=]="),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[x:=e]P__↔∀x(x=e→P)",
    key = "0",
    recursor = "0.1;*",
    unifier = Unifier.SurjectiveLinearPretend,
  )

  @Derivation
  val selfassignb: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "selfassignb",
    canonicalName = "[:=] self assign",
    displayName = Some("[:=]"),
    displayConclusion = "__[x:=x]P__↔P",
  )

  @Derivation
  val Dassignb: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dassignb",
    canonicalName = "[':=] differential assign",
    displayName = Some("[:=]"),
    displayConclusion = "__[x':=c]p(x')__↔p(c)",
    key = "0",
    recursor = "*",
    unifier = Unifier.Full,
  )

  @Derivation
  val Dassignbeq: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dassignbeq",
    canonicalName = "[':=] assign equality",
    displayName = Some("[:=]="),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[x':=e]P__↔∀x'(x'=e→P)",
    key = "0",
    recursor = "0.1;*",
    unifier = Unifier.SurjectiveLinearPretend,
  )

  @Derivation
  val Dselfassignb: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dselfassignb",
    canonicalName = "[':=] self assign",
    displayName = Some("[':=]"),
    displayConclusion = "__[x':=x']P__↔P",
  )

  @Derivation
  val randomb: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "randomb",
    canonicalName = "[:*] assign nondet",
    displayName = Some("[:*]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[x:=*]P__↔∀x P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val testb: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "testb",
    canonicalName = "[?] test",
    displayName = Some("[?]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[?Q]P__↔(Q→P)",
    key = "0",
    recursor = "1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val choiceb: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "choiceb",
    canonicalName = "[++] choice",
    displayName = Some("[∪]"),
    displayNameAscii = Some("[++]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a∪b]P__↔[a]P∧[b]P",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val composeb: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "composeb",
    canonicalName = "[;] compose",
    displayName = Some("[;]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a;b]P__↔[a][b]P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val iterateb: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "iterateb",
    canonicalName = "[*] iterate",
    displayName = Some("[*]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a*]P__↔P∧[a][a*]P",
    key = "0",
    recursor = "1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val barcan: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "barcan",
    canonicalName = "B Barcan",
    displayName = Some("B Barcan"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a]∀x p(x)__ ↔∀x[a]p(x)  (x∉a)",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )

  // Differential Equations

  // @TODO: Old AxiomInfo calls DWeakening
  @Derivation
  val DWbase: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DWbase",
    canonicalName = "DW base",
    displayName = Some("DW base"),
    displayLevel = DisplayLevel.Internal,
    displayConclusion = "__[{x'=f(x)&Q}]Q__",
    key = "",
    recursor = "",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val DE: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DE",
    canonicalName = "DE differential effect",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=f(x)&Q}]P__↔[x'=f(x)&Q][x':=f(x)]P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val DEs: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DEs",
    canonicalName = "DE differential effect (system)",
    displayName = Some("DE"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=F,c&Q}]P__↔[{c,x'=F&Q}][x':=f(x)]P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )

  /* @todo soundness requires only vectorial x in p(||) */
  @Derivation
  val DIequiv: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DIequiv",
    canonicalName = "DI differential invariance",
    displayName = Some("DI"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "(__[{x'=f(x)&Q}]P__↔[?Q]P)←(Q→[{x'=f(x)&Q}](P)')",
    key = "1.0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val DGa: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DGa",
    canonicalName = "DG differential ghost",
    displayName = Some("DG"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=f(x)&Q}]P__↔∃y [{x'=f(x),y'=a*y+b&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )

  // @todo name: why inverse instead of universal?
  @Derivation
  val DGpp: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DGpp",
    canonicalName = "DG inverse differential ghost",
    displayName = Some("DG inverse differential ghost"),
    displayConclusion = "__[{x'=f(x)&Q}]P__↔∀y [{y'=a*y+b,x'=f(x)&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val DGi: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DGi",
    canonicalName = "DG inverse differential ghost implicational",
    displayName = Some("DG inverse differential ghost implicational"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=f(x)&Q}]P__→∀y [{y'=g(x,y),x'=f(x)&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val DGC: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DGC",
    canonicalName = "DG differential ghost constant",
    displayName = Some("DG"),
    displayConclusion = "__[{x'=f(x)&Q}]P__↔∃y [{x'=f(x),y'=g()&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val DGCa: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DGCa",
    canonicalName = "DG differential ghost constant all",
    displayName = Some("DGa"),
    displayConclusion = "__[{x'=f(x)&Q}]P__↔∀y [{x'=f(x),y'=g()&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val DS: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DS",
    canonicalName = "DS& differential equation solution",
    displayName = Some("DS&"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=c()&q(x)}]P__ ↔ ∀t≥0 (∀0≤s≤t q(x+c()*s)) → [x:=x+c()*t;]P)",
    key = "0",
    recursor = "0.1.1;0.1;*",
    unifier = Unifier.SurjectiveLinearPretend,
  )

  /* @todo: , commute should be derivable from this + ghost */
  @Derivation
  val commaSort: CoreAxiomInfo = CoreAxiomInfo
    .create(name = "commaSort", canonicalName = ", sort", displayName = Some(","), unifier = Unifier.Linear)

  @Derivation
  val commaCommute: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "commaCommute",
    canonicalName = ", commute",
    displayName = Some(","),
    unifier = Unifier.Linear,
    key = "0",
    recursor = "",
  )

  @Derivation
  val DX: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DX",
    canonicalName = "DX differential skip",
    key = "0",
    recursor = "1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dcomp: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dcomp",
    canonicalName = "D[;] differential self compose",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "[x'=f(x)&Q]P ↔ [x'=f(x)&Q][x'=f(x)&Q]P",
    unifier = Unifier.Linear,
  )

  @Derivation
  val DIogreater: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DIogreater",
    canonicalName = "DIo open differential invariance >",
    displayName = Some("DIo >"),
    displayConclusion = "(__[{x'=f(x)&Q}]g(x)>h(x)__↔[?Q]g(x)>h(x))←(Q→[{x'=f(x)&Q}](g(x)>h(x)→(g(x)>h(x))'))",
    key = "1.0",
    recursor = "*",
    unifier = Unifier.Linear,
  )

  @Derivation
  val DMP: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DMP",
    canonicalName = "DMP differential modus ponens",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "(__[{x'=f(x)&Q}]P__←[{x'=f(x)&R}]P)←[{x'=f(x)&Q}](Q→R)",
    inputs = "R:formula",
    key = "1.1",
    // TODO recursor = (0::Nil)::(Nil)::Nil
  )

  @Derivation
  val Uniq: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Uniq",
    canonicalName = "Uniq uniqueness",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "<x'=f(x)&Q}>P ∧ <x'=f(x)&R>P → __<x'=f(x)&Q∧R>P__",
    key = "1",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )

  /* @note soundness requires no primes in f(||) (guaranteed by data structure invariant) */
  @Derivation
  val Cont: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Cont",
    canonicalName = "Cont continuous existence",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "e>0 → __<x'=f(x),t'=1&e>0>t≠0__",
    key = "1",
    recursor = "*",
  )

  @Derivation
  val RIclosedgeq: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "RIclosedgeq",
    canonicalName = "RI& closed real induction >=",
    displayName = Some("RI& >="),
    displayLevel = DisplayLevel.Browse,
    displayConclusion =
      "__[x'=f(x)&Q]e≥0__ ↔ (Q→e≥0) ∧ [x'=f(x)&Q∧e≥0};t:=0;](<{t'=1,x'=f(x)&Q>t≠0→<t'=1,x'=f(x)&e≥0}>t≠0)",
    key = "0",
    recursor = "1.1.1;1.1.0;1;0",
  )

  @Derivation
  val RI: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "RI",
    canonicalName = "RI& real induction",
    displayName = Some("RI&"),
    displayConclusion =
      "__[x'=f(x)&Q]P__ ↔ ∀s [t'=1,x'=f(x)&Q&(P|t=s)](t=s -> P & (<t'=1,x'=f(x)&(Q|t=s)>t!=s -> <t'=1,x'=f(x)&(P|t=s)>t!=s))",
    key = "0",
    recursor = "*",
  )

  @Derivation
  val IVT: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "IVT",
    canonicalName = "IVT",
    displayConclusion =
      "<{t'=f(t,x),x'=g(t,x)&q(t,x)}>(t>=z&p(t,x))→t<=z→<{t'=f(t,x),x'=g(t,x)&q(t,x)}>(t=z∧<{t'=f(t,x),x'=g(t,x)&q(t,x)}>(t>=z∧p(t,x))",
    unifier = Unifier.Full,
  )

  @Derivation
  val DCC: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DCC",
    canonicalName = "DCC",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=f(x)&R}](P→Q)__←([{x'=f(x)&R&P}]Q∧[{x'=f(x)&R}](¬P→[{x'=f(x)&R}]¬P)",
    key = "1",
    recursor = "0",
    unifier = Unifier.Linear,
  )

  /* DIFFERENTIAL AXIOMS */

  @Derivation
  val Dconst: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dconst",
    canonicalName = "c()' derive constant fn",
    displayName = Some("c()'"),
    displayConclusion = "__(c)'__=0",
    unifier = Unifier.Linear,
    key = "0",
    recursor = "",
  )

  @Derivation
  val DvarAxiom: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "DvarAxiom",
    canonicalName = "x' derive var",
    displayName = Some("x'"),
    displayConclusion = "__(x)'__=x'",
    unifier = Unifier.Linear,
    key = "0",
    recursor = "",
  )

  // @todo derivable by CET
  @Derivation
  val Dneg: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dneg",
    canonicalName = "-' derive neg",
    displayName = Some("-'"),
    displayConclusion = "__(-f(x))'__=-(f(x))'",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dplus: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dplus",
    canonicalName = "+' derive sum",
    displayName = Some("+'"),
    displayConclusion = "__(f(x)+g(x))'__=f(x)'+g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )

  // @todo derivable by CET
  @Derivation
  val Dminus: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dminus",
    canonicalName = "-' derive minus",
    displayName = Some("-'"),
    displayConclusion = "__(f(x)-g(x))'__=f(x)'-g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dtimes: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dtimes",
    canonicalName = "*' derive product",
    displayName = Some("·'"),
    displayNameAscii = Some("*'"),
    displayConclusion = "__(f(x)·g(x))'__=(f(x))'·g(x)+f(x)·(g(x))'",
    key = "0",
    recursor = "0.0;1.1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dquotient: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dquotient",
    canonicalName = "/' derive quotient",
    displayName = Some("/'"),
    displayConclusion = "__(f(g)/g(x))'__=(g(x)·(f(x))-f(x)·(g(x))')/g(x)<sup>2</sup>",
    key = "0",
    recursor = "0.0.0;0.1.1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dcompose: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dcompose",
    canonicalName = "chain rule",
    displayName = Some("∘'"),
    displayNameAscii = Some("o'"),
    displayConclusion = "[y:=g(x)][y':=1](__(f(g(x)))'__=(f(y))'·(g(x))'",
    key = "1.1.0",
    recursor = "1.1;1;*",
  )

  @Derivation
  val Dpower: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dpower",
    canonicalName = "^' derive power",
    displayName = Some("^'"),
    displayConclusion = "__(f(g)^n)'__=n·f(g)^(n-1)·(f(g))'←n≠0",
    unifier = Unifier.Linear,
    key = "1.0",
    recursor = "1",
  )

  @Derivation
  val Dgreaterequal: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dgreaterequal",
    canonicalName = ">=' derive >=",
    displayNameAscii = Some(">='"),
    displayName = Some("≥'"),
    displayConclusion = "__(f(x)≥g(x))'__↔f(x)'≥g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dgreater: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dgreater",
    canonicalName = ">' derive >",
    displayName = Some(">'"),
    displayConclusion = "__(f(x)>g(x))'__↔f(x)'≥g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dand: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dand",
    canonicalName = "&' derive and",
    displayName = Some("∧'"),
    displayNameAscii = Some("&'"),
    displayConclusion = "__(P&Q)'__↔P'∧Q'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dor: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dor",
    canonicalName = "|' derive or",
    displayName = Some("∨'"),
    displayNameAscii = Some("|'"),
    displayConclusion = "__(P|Q)'__↔P'∧Q'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dforall: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dforall",
    canonicalName = "forall' derive forall",
    displayName = Some("∀'"),
    displayNameAscii = Some("all'"),
    displayConclusion = "__(∀x p(x))'__↔∀x (p(x))'",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val Dexists: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Dexists",
    canonicalName = "exists' derive exists",
    displayName = Some("∃'"),
    displayNameAscii = Some("exists'"),
    displayConclusion = "__(∃x p(x))'__↔∀x (p(x))'",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )

  /* HYBRID PROGRAMS / GAMES */

  @Derivation
  val duald: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "duald",
    canonicalName = "<d> dual",
    displayName = Some("&langle;<sup>d</sup>&rangle;"),
    displayNameAscii = Some("<d>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__&langle;a<sup>d</sup>&rangle;P__↔¬&langle;a&rangle;¬P",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val VK: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "VK",
    canonicalName = "VK vacuous",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "(p→__[a]p__)←[a]⊤",
    key = "1.1",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val boxTrueAxiom: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "boxTrueAxiom",
    canonicalName = "[]T system",
    displayName = Some("[]T axiom"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a]⊤__",
    key = "",
    recursor = "",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val K: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "K",
    canonicalName = "K modal modus ponens",
    displayLevel = DisplayLevel.All,
    displayConclusion = "[a](P→Q) → (__[a]P → [a]Q__)",
    key = "1",
    recursor = "*",
  )

  // @note the tactic I has a name and belleExpr, but there's no tactic that simply applies the I-> axiom,
  // because its sole purpose is to derive the stronger equivalence form
  @Derivation
  val Iind: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "Iind",
    canonicalName = "I induction",
    displayName = Some("I<sub>→</sub>"),
    displayNameAscii = Some("Iind"),
    displayLevel = DisplayLevel.Internal,
    displayConclusion = "P∧[a<sup>*</sup>](P→[a]P)→__[a<sup>*</sup>]P__",
    key = "1",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )

  /* FIRST-ORDER QUANTIFIER AXIOMS */

  /** all dual */
  @Derivation
  val alld: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "alld",
    canonicalName = "all dual",
    displayName = Some("∀d"),
    displayNameAscii = Some("alld"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__¬∃x ¬P__ ↔ ∀x P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val allPd: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "allPd",
    canonicalName = "all prime dual",
    displayName = Some("∀'d"),
    displayNameAscii = Some("allPd"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__¬∃x' ¬P__ ↔ ∀x' P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )

  /** all eliminate */
  @Derivation
  val alle: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "alle",
    canonicalName = "all eliminate",
    displayName = Some("∀e"),
    displayNameAscii = Some("alle"),
    displayConclusion = "__∀x P__ → P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val alleprime: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "alleprime",
    canonicalName = "all eliminate prime",
    displayName = Some("∀e'"),
    displayNameAscii = Some("allep"),
    displayConclusion = "__∀x' P__ → P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )

  // ***************
  // Derived Axioms
  // ***************

  // semantic renaming cases

  /**
   * Semantically renamed
   * {{{
   * Axiom "[:=] assign equality y"
   *    [y_:=f();]p(||) <-> \forall y_ (y_=f() -> p(||))
   * End.
   * }}}
   * @note
   *   needs semantic renaming
   */
  @Derivation
  lazy val assignbeqy: DerivedAxiomInfo = derivedAxiomFromFact(
    DerivedAxiomInfo.create(
      name = "assignbeqy",
      canonicalName = "[:=] assign equality y",
      displayName = Some("[:=]=y"),
      displayLevel = DisplayLevel.Internal,
    ),
    "[y_:=f();]p(||) <-> \\forall y_ (y_=f() -> p(||))".asFormula,
    ProvableSig.axioms("[:=] assign equality")(URename("x_".asVariable, "y_".asVariable, semantic = true)),
  )

  /**
   * Semantically renamed
   * {{{
   * Axiom "[:=] self assign y"
   *   [y_:=y_;]p(||) <-> p(||)
   * End.
   * }}}
   * @note
   *   needs semantic renaming
   */
  @Derivation
  lazy val selfassignby: DerivedAxiomInfo = derivedAxiomFromFact(
    DerivedAxiomInfo.create(
      name = "selfassignby",
      canonicalName = "[:=] self assign y",
      displayName = Some("[:=]y"),
      displayLevel = DisplayLevel.Internal,
    ),
    "[y_:=y_;]p(||) <-> p(||)".asFormula,
    ProvableSig.axioms("[:=] self assign")(URename("x_".asVariable, "y_".asVariable, semantic = true)),
  )

  /**
   * Semantically renamed
   * {{{
   * Axiom "DE differential effect (system) y"
   *    // @note Soundness: f(||) cannot have ' by data structure invariant. AtomicODE requires explicit-form so f(||) cannot have differentials/differential symbols
   *    [{y_'=f(||),c&q(||)}]p(||) <-> [{c,y_'=f(||)&q(||)}][y_':=f(||);]p(||)
   * End.
   * }}}
   * @note
   *   needs semantic renaming
   */
  @Derivation
  lazy val DEsysy: DerivedAxiomInfo = derivedAxiomFromFact(
    DerivedAxiomInfo.create(
      name = "DEsysy",
      canonicalName = "DE differential effect (system) y",
      displayLevel = DisplayLevel.Internal,
      displayConclusion = "__[{y'=F,c&Q}]P__↔[{c,y'=F&Q}][y':=f(x)]P",
      key = "0",
      recursor = "1;*",
    ),
    "[{y_'=f(||),c&q(||)}]p(||) <-> [{c,y_'=f(||)&q(||)}][y_':=f(||);]p(||)".asFormula,
    ProvableSig.axioms("DE differential effect (system)")(URename("x_".asVariable, "y_".asVariable, semantic = true)),
  )

  /**
   * Semantically renamed
   * {{{
   * Axiom "all dual y"
   *    (!\exists y_ !p(||)) <-> \forall y_ p(||)
   * End.
   * }}}
   * @note
   *   needs semantic renaming
   */
  @Derivation
  lazy val alldy: DerivedAxiomInfo = derivedAxiomFromFact(
    DerivedAxiomInfo.create(
      name = "alldy",
      canonicalName = "all dual y",
      displayName = Some("∀d"),
      displayNameAscii = Some("alldy"),
      displayLevel = DisplayLevel.Internal,
    ),
    "(!\\exists y_ !p(||)) <-> \\forall y_ p(||)".asFormula,
    ProvableSig.axioms("all dual")(URename("x_".asVariable, "y_".asVariable, semantic = true)),
  )

  /**
   * Semantically renamed
   * {{{
   * Axiom "all dual time"
   *    (!\exists t_ !p(||)) <-> \forall t_ p(||)
   * End.
   * }}}
   * @note
   *   needs semantic renaming
   */
  @Derivation
  lazy val alldt: DerivedAxiomInfo = derivedAxiomFromFact(
    DerivedAxiomInfo.create(
      name = "alldt",
      canonicalName = "all dual time",
      displayName = Some("∀d"),
      displayNameAscii = Some("alldt"),
      displayLevel = DisplayLevel.Internal,
    ),
    "(!\\exists t_ !p(||)) <-> \\forall t_ p(||)".asFormula,
    ProvableSig.axioms("all dual")(URename("x_".asVariable, "t_".asVariable, semantic = true)),
  )

  /**
   * Semantically renamed
   * {{{
   * Axiom "all eliminate y"
   *   (\forall y_ p(||)) -> p(||)
   * End.
   * }}}
   * @note
   *   needs semantic renaming
   */
  @Derivation
  lazy val ally: DerivedAxiomInfo = derivedAxiomFromFact(
    DerivedAxiomInfo.create(
      name = "ally",
      canonicalName = "all eliminate y",
      displayName = Some("∀y"),
      displayNameAscii = Some("ally"),
      displayLevel = DisplayLevel.Internal,
    ),
    "(\\forall y_ p(||)) -> p(||)".asFormula,
    ProvableSig.axioms("all eliminate")(URename("x_".asVariable, "y_".asVariable, semantic = true)),
  )

  // derived axioms used in useAt itself, thus given as Provables not lemmas, just in case to avoid dependencies

  lazy val boxTrueTrue: ProvableSig = TactixLibrary
    .proveBy("[a{|^@|};]true <-> true".asFormula, equivR(1) < (closeT, cohideR(1) & byUS(boxTrueAxiom)))

  lazy val impliesRightAnd: ProvableSig = TactixLibrary
    .proveBy("(p_()->q_()) & (p_()->r_()) <-> (p_() -> q_()&r_())".asFormula, TactixLibrary.prop)

  lazy val sameImpliesImplies: ProvableSig = TactixLibrary
    .proveBy("(p_()->q_()) -> (p_()->r_()) <-> (p_() -> (q_()->r_()))".asFormula, TactixLibrary.prop)

  lazy val factorAndRight: ProvableSig = TactixLibrary
    .proveBy("(q_()&p_()) & (r_()&p_()) <-> ((q_()&r_()) & p_())".asFormula, TactixLibrary.prop)

  lazy val factorAndLeft: ProvableSig = TactixLibrary
    .proveBy("(p_()&q_()) & (p_()&r_()) <-> (p_() & (q_()&r_()))".asFormula, TactixLibrary.prop)

  lazy val factorOrRight: ProvableSig = TactixLibrary
    .proveBy("(q_()|p_()) & (r_()|p_()) <-> ((q_()&r_()) | p_())".asFormula, TactixLibrary.prop)

  lazy val factorOrLeft: ProvableSig = TactixLibrary
    .proveBy("(p_()|q_()) & (p_()|r_()) <-> (p_() | (q_()&r_()))".asFormula, TactixLibrary.prop)

  lazy val factorImpliesOrRight: ProvableSig = TactixLibrary
    .proveBy("(q_()|p_()) -> (r_()|p_()) <-> ((q_()->r_()) | p_())".asFormula, TactixLibrary.prop)

  lazy val factorImpliesOrLeft: ProvableSig = TactixLibrary
    .proveBy("(p_()|q_()) -> (p_()|r_()) <-> (p_() | (q_()->r_()))".asFormula, TactixLibrary.prop)

  lazy val impliesMonAndLeft: ProvableSig = TactixLibrary
    .proveBy("(q_()->r_()) -> (q_()&p_() -> r_()&p_())".asFormula, TactixLibrary.prop)

  lazy val impliesMonAndRight: ProvableSig = TactixLibrary
    .proveBy("(q_()->r_()) -> (p_()&q_() -> p_()&r_())".asFormula, TactixLibrary.prop)

  lazy val trueOr: ProvableSig = TactixLibrary.proveBy("true | p_() <-> true".asFormula, TactixLibrary.prop)

  lazy val orTrue: ProvableSig = TactixLibrary.proveBy("p_() | true <-> true".asFormula, TactixLibrary.prop)

  lazy val ponensAndPassthrough_Imply: ProvableSig = TactixLibrary
    .proveBy("((p_() ->q_())&p_() -> q_()) <-> true".asFormula, TactixLibrary.prop)

  lazy val ponensAndPassthrough_Equiv: ProvableSig = TactixLibrary
    .proveBy("((p_()<->q_())&p_() -> q_()) <-> true".asFormula, TactixLibrary.prop)

  lazy val ponensAndPassthrough_coImply: ProvableSig = TactixLibrary
    .proveBy("((q_() ->p_())&q_() -> p_()) <-> true".asFormula, TactixLibrary.prop)

  lazy val ponensAndPassthrough_coEquiv: ProvableSig = TactixLibrary
    .proveBy("((p_()<->q_())&q_() -> p_()) <-> true".asFormula, TactixLibrary.prop)

  // derived rules

  /**
   * {{{
   * Rule "contra2".
   * Premise !q(||) ==> !p(||)
   * Conclusion p(||) ==> q(||)
   * End.
   * }}}
   *
   * @derived
   */
  @Derivation
  lazy val contraposition2Rule: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "contraposition2Rule",
      canonicalName = "contra2",
      displayName = Some("contra2"),
      displayPremises = "!Q |- !P",
      displayConclusion = "P |- Q",
    ),
    Sequent(immutable.IndexedSeq("p_(||)".asFormula), immutable.IndexedSeq("q_(||)".asFormula)),
    useAt(doubleNegation, PosInExpr(1 :: Nil))(1) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(-1) &
      notR(1) &
      notL(-1),
  )

  /**
   * {{{
   * Rule "ind induction".
   * Premise p(||) ==> [a;]p(||)
   * Conclusion p(||) ==> [a*]p(||)
   * }}}
   * {{{
   *  p(x) |- [a]p(x)
   * -------------------- ind
   *  p(x) |- [{a}*]p(x)
   * }}}
   *
   * Interderives with FP fixpoint rule.
   *
   * @see
   *   Lemma 4.1 of Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log.
   *   17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @see
   *   Lemma 7.2 and Corollary 16.1 of Andre Platzer.
   *   [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
   */
  @Derivation
  lazy val indrule: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "indrule",
      canonicalName = "ind induction",
      displayPremises = "P |- [a]P",
      displayConclusion = "P |- [a*]P",
    ),
    Sequent(immutable.IndexedSeq("p_(||)".asFormula), immutable.IndexedSeq("[{a_;}*]p_(||)".asFormula)),
    useAt(box, PosInExpr(1 :: Nil))(1) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(-1) & notR(1) & notL(-1) &
      byUS(FPrule) &
      orL(-1) < (
        closeId(-1, 1),
        useAt(doubleNegation, PosInExpr(1 :: Nil))(-1) & notR(1) & notL(-1) &
          useAt(box)(1)
      ),
  )

  /**
   * DUPLICATE: Rule "FP fixpoint duplicate" only for documentation purposes to show that FP rule derives from ind
   * induction rule, except with a duplicate premise.
   *
   * {{{
   * Premise p(||) | <a>q(||) ==> q(||)
   * Conclusion <a*>p(||) ==> q(||)
   * }}}
   * {{{
   *  p(x) | <a>q(x) |- q(x)    p(x) | <a>q(x) |- q(x)
   * -------------------------------------------------- FP
   *  <a*>p(x) |- q(x)
   * }}}
   *
   * Interderives with ind induction rule. FP is used as basis, because deriving FP from ind leads to a duplicate
   * premise, needing list to set contraction.
   *
   * @see
   *   Lemma 4.1 of Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log.
   *   17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @see
   *   Lemma 16.11 and Corollary 16.1 of Andre Platzer.
   *   [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
   * @see
   *   [[FPrule]]
   */
  @Derivation
  private[btactics] lazy val FPruleduplicate: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "FPruleduplicate",
      canonicalName = "FP rule duplicate",
      displayLevel = DisplayLevel.Internal,
      displayPremises = "P | <a>Q |- Q ;; P | <a>Q |- Q",
      displayConclusion = "<a*>P |- Q",
    ),
    Sequent(immutable.IndexedSeq("<{a_;}*>p_(||)".asFormula), immutable.IndexedSeq("q_(||)".asFormula)),
    cut("<{a_;}*>q_(||)".asFormula) < (
      /* use: */
      hide(-1) &
        useAt(diamond, PosInExpr(1 :: Nil))(-1) &
        useAt(doubleNegation, PosInExpr(1 :: Nil))(1) & notL(-1) & notR(1) &
        byUS(indrule) &
        useAt(box, PosInExpr(1 :: Nil))(1) &
        useAt(doubleNegation)(1, 0 :: 1 :: Nil) &
        notL(-1) & notR(1) &
        cut("p_(||) | <a_;>q_(||)".asFormula) < (
          /* use: */
          hide(-1),
          /* show: */
          orR(2) & closeId(-1, 3)
        ),
      /* show: */
      hide(1) &
        byUS(mondrule) &
        cut("p_(||) | <a_;>q_(||)".asFormula) < (
          /* use: */
          hide(-1),
          /* show: */
          orR(2) & closeId(-1, 2)
        )
    ),
  )

  /**
   * {{{
   * Rule "all generalization".
   * Premise p(||)
   * Conclusion \forall x p(||)
   * End.
   * }}}
   *
   * @derived
   *   from G or from [] monotone with program x:=*
   * @derived
   *   from Skolemize
   * @note
   *   generalization of p(x) to p(||) as in Theorem 14
   */
  @Derivation
  lazy val allGeneralize: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "allGeneralize",
      canonicalName = "all generalization",
      displayName = Some("all gen"),
      displayNameAscii = Some("allgen"),
      displayNameLong = Some("allgen"),
      displayPremises = "|- P",
      displayConclusion = "|- \\forall x P",
    ),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("\\forall x_ p_(||)".asFormula)),
    useAt(randomb, PosInExpr(1 :: Nil))(1) &
      cut(Box(AssignAny(Variable("x_", None, Real)), True)) < (
        byUS(monbaxiom) & hide(-1),
        hide(1) & useAt(boxTrueAxiom)(1)
      ),
  )

  /**
   * {{{
   * Rule "all generalization".
   * Premise p(||) |- q(||)
   * Conclusion \forall x p(||) |- \forall x q(||)
   * End.
   * }}}
   */
  @Derivation
  lazy val monallrule: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "monallrule",
      canonicalName = "all monotone",
      displayName = Some("M∀"),
      displayNameAscii = Some("Mall"),
      displayPremises = "P |- Q",
      displayConclusion = "∀x P |- ∀ x Q",
    ),
    Sequent(immutable.IndexedSeq("\\forall x_ p_(||)".asFormula), immutable.IndexedSeq("\\forall x_ q_(||)".asFormula)),
    implyRi()(-1, 1) &
      useAt(allDistElim)(1) &
      byUS(allGeneralize),
  )

  /**
   * {{{
   * Rule "Goedel".
   * Premise p(||)
   * Conclusion [a;]p(||)
   * End.
   * }}}
   * {{{
   *     p(||)
   * ----------- G
   *  [a{|^@|};]p(||)
   * }}}
   *
   * @note
   *   Unsound for hybrid games
   * @derived
   *   from M and [a]true
   */
  @Derivation
  lazy val Goedel: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "Goedel",
      canonicalName = "Goedel",
      displayName = Some("G"),
      displayPremises = "|- P",
      displayConclusion = "|- [a;]P",
    ),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("[a_{|^@|};]p_(||)".asFormula)),
    cut("[a_{|^@|};]true".asFormula) < (
      // use
      byUS(monbaxiom) & hide(-1),
      // show
      hide(1) & useAt(boxTrueAxiom)(1)
    ),
  )

  /**
   * {{{
   * Axiom "V vacuous".
   *   p() -> [a{|^@|};]p()
   * End.
   * }}}
   * @note
   *   unsound for hybrid games
   */
  @Derivation
  lazy val V: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "V",
      canonicalName = "V vacuous",
      displayConclusion = "p→__[a]p__",
      key = "1",
      recursor = "*",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(IndexedSeq(), IndexedSeq("p() -> [a{|^@|};]p()".asFormula)),
    useAt(VK, PosInExpr(1 :: Nil))(1) &
      useAt(boxTrueAxiom)(1),
  )

  /**
   * {{{
   * Axiom /*\\foralli */ "all instantiate"
   *   (\forall x_ p(x_)) -> p(f())
   * End.
   * }}}
   * @note
   *   Core axiom derivable thanks to [:=]= and [:=]
   */
  @Derivation
  lazy val allInst: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "allInst",
      canonicalName = "all instantiate",
      displayName = Some("∀inst"),
      displayNameAscii = Some("allInst"),
      displayConclusion = "__∀x p(x)__ → p(f())",
      key = "0",
      recursor = "*",
    ),
    "(\\forall x_ p(x_)) -> p(f())".asFormula,
    cutR("(\\forall x_ (x_=f()->p(x_))) -> p(f())".asFormula)(1) < (
      useAt(assignbeq, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
        useAt(assignbAxiom)(1, 0 :: Nil) &
        implyR(1) & close(-1, 1),
      CMon(PosInExpr(0 :: 0 :: Nil)) &
        implyR(1) & implyR(1) & close(-1, 1)
    ),
    //      ------------refl
    //      p(f) -> p(f)
    //      ------------------ [:=]
    //    [x:=f]p(x) -> p(f)
    //   --------------------------------[:=]=
    //    \forall x (x=f -> p(x)) -> p(f)
    //   -------------------------------- CMon(p(x) -> (x=f->p(x)))
    //   \forall x p(x) -> p(f)
  )

  @Derivation
  lazy val allInstPrime: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "allInstPrime",
      canonicalName = "all instantiate prime",
      displayName = Some("∀inst'"),
      displayNameAscii = Some("allInstPrime"),
      displayConclusion = "__∀x' p(x')__ → p(f())",
      key = "0",
      recursor = "*",
    ),
    "(\\forall x_' p(x_')) -> p(f())".asFormula,
    cutR("(\\forall x_' (x_'=f()->p(x_'))) -> p(f())".asFormula)(1) < (
      useAt(Dassignbeq, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
        useAt(Dassignb)(1, 0 :: Nil) &
        implyR(1) & close(-1, 1),
      CMon(PosInExpr(0 :: 0 :: Nil)) &
        implyR(1) & implyR(1) & close(-1, 1)
    ),
    //      ------------refl
    //      p(f) -> p(f)
    //      ------------------ [':=]
    //    [x':=f]p(x') -> p(f)
    //   --------------------------------[':=]=
    //    \forall x' (x'=f -> p(x')) -> p(f)
    //   -------------------------------- CMon(p(x') -> (x'=f->p(x')))
    //   \forall x' p(x') -> p(f)
  )

  /**
   * {{{
   *   Axiom "vacuous all quantifier"
   *     (\forall x_ p()) <-> p()
   *   End.
   * }}}
   * @note
   *   Half of this is a base axiom officially but already derives from [:*] and V
   */
  @Derivation
  lazy val allV: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "allV",
      canonicalName = "vacuous all quantifier",
      displayName = Some("V∀"),
      displayNameAscii = Some("allV"),
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ p()) <-> p()".asFormula)),
    useAt(equivExpand)(1) & andR(1) < (
      byUS(alle),
      useAt(randomb, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
        byUS(V)
    ),
  )

  /**
   * {{{
   * Rule "CT term congruence".
   * Premise f_(||) = g_(||)
   * Conclusion ctxT_(f_(||)) = ctxT_(g_(||))
   * End.
   * }}}
   *
   * @derived
   *   ("Could also use CQ equation congruence with p(.)=(ctx_(.)=ctx_(g_(x))) and reflexivity of = instead.")
   */
  @Derivation
  lazy val CTtermCongruence: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "CTtermCongruence",
      canonicalName = "CT term congruence",
      displayName = Some("CT term congruence"),
      displayNameAscii = Some("CTtermCongruence"),
      displayNameLong = Some("CTtermCongruence"),
      displayPremises = "|- f_(||) = g_(||)",
      displayConclusion = "|- ctx_(f_(||)) = ctx_(g_(||))",
    ),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("ctx_(f_(||)) = ctx_(g_(||))".asFormula)),
    cutR("ctx_(g_(||)) = ctx_(g_(||))".asFormula)(SuccPos(0)) < (
      byUS(equalReflexive),
      equivifyR(1) &
        HilbertCalculus.CQ(PosInExpr(0 :: 0 :: Nil)) &
        useAt(equalCommute)(1)
    ),
  )

  /**
   * {{{
   * Rule "CQimply equation congruence".
   * Premise f_(||) = g_(||)
   * Conclusion ctx_(f_(||)) -> ctx_(g_(||))
   * End.
   * }}}
   */
  @Derivation
  lazy val CQimplyCongruence: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "CQimplyCongruence",
      canonicalName = "CQimply equation congruence",
      displayName = Some("CQimply"),
      displayNameAscii = Some("CQimplyCongruence"),
      displayNameLong = Some("CQimplyCongruence"),
      displayPremises = "|- f_(||) = g_(||)",
      displayConclusion = "|- ctx_(f_(||)) -> ctx_(g_(||))",
    ),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("ctx_(f_(||)) -> ctx_(g_(||))".asFormula)),
    TactixLibrary.equivifyR(1) & by(CQrule),
  )

  /**
   * {{{
   * Rule "CQrevimply equation congruence".
   * Premise g_(||) = f_(||)
   * Conclusion ctx_(f_(||)) -> ctx_(g_(||))
   * End.
   * }}}
   */
  @Derivation
  lazy val CQrevimplyCongruence: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "CQrevimplyCongruence",
      canonicalName = "CQrevimply equation congruence",
      displayName = Some("CQrevimply"),
      displayNameAscii = Some("CQrevimplyCongruence"),
      displayNameLong = Some("CQrevimplyCongruence"),
      displayPremises = "|- g_(||) = f_(||)",
      displayConclusion = "|- ctx_(f_(||)) -> ctx_(g_(||))",
    ),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("ctx_(f_(||)) -> ctx_(g_(||))".asFormula)),
    TactixLibrary.equivifyR(1) & by(CQrule) & TactixLibrary.commuteEqual(1),
  )

  /**
   * {{{
   * Rule "CEimply congruence".
   * Premise p_(||) <-> q_(||)
   * Conclusion ctx_{p_(||)} -> ctx_{q_(||)}
   * End.
   * }}}
   */
  @Derivation
  lazy val CEimplyCongruence: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "CEimplyCongruence",
      canonicalName = "CEimply congruence",
      displayName = Some("CEimply"),
      displayNameAscii = Some("CEimplyCongruence"),
      displayNameLong = Some("CEimplyCongruence"),
      displayPremises = "|- p_(||) <-> q_(||)",
      displayConclusion = "|- ctx_{p_(||)} -> ctx_{(q_(||)}",
    ),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("ctx_{p_(||)} -> ctx_{q_(||)}".asFormula)),
    TactixLibrary.equivifyR(1) & by(CErule),
  )

  /**
   * {{{
   * Rule "CErevimply congruence".
   * Premise q_(||) <-> p_(||)
   * Conclusion ctx_{p_(||)} -> ctx_{q_(||)}
   * End.
   * }}}
   */
  @Derivation
  lazy val CErevimplyCongruence: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "CErevimplyCongruence",
      canonicalName = "CErevimply congruence",
      displayName = Some("CErevimply"),
      displayNameAscii = Some("CErevimplyCongruence"),
      displayNameLong = Some("CErevimplyCongruence"),
      displayPremises = "|- q_(||) <-> p_(||)",
      displayConclusion = "|- ctx_{p_(||)} -> ctx_{(q_(||)}",
    ),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("ctx_{p_(||)} -> ctx_{q_(||)}".asFormula)),
    TactixLibrary.equivifyR(1) & by(CErule) & TactixLibrary.commuteEquivR(1),
  )

  /**
   * {{{
   * Rule "[] monotone".
   * Premise p(||) ==> q(||)
   * Conclusion [a;]p(||) ==> [a;]q(||)
   * End.
   * }}}
   *
   * @derived
   *   useAt(diamond) & by("<> monotone")
   * @see
   *   "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
   * @see
   *   "André Platzer. Differential Hybrid Games."
   * @note
   *   Notation changed to p instead of p_ just for the sake of the derivation.
   */
  @Derivation
  lazy val monbaxiom: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "monbaxiom",
      canonicalName = "[] monotone",
      displayName = Some("[] monotone"),
      displayNameAscii = Some("[]monotone"),
      displayNameLong = Some("[]monotone"),
      displayPremises = "P |- Q",
      displayConclusion = "[a;]P |- [a;]Q",
    ),
    Sequent(immutable.IndexedSeq("[a_;]p_(||)".asFormula), immutable.IndexedSeq("[a_;]q_(||)".asFormula)),
    useAt(box, PosInExpr(1 :: Nil))(-1) & useAt(box, PosInExpr(1 :: Nil))(1) &
      notL(-1) & notR(1) &
      by(
        Ax.mondrule,
        USubst(
          SubstitutionPair(UnitPredicational("p_", AnyArg), Not(UnitPredicational("q_", AnyArg))) ::
            SubstitutionPair(UnitPredicational("q_", AnyArg), Not(UnitPredicational("p_", AnyArg))) :: Nil
        ),
      ) &
      notL(-1) & notR(1),
  )

  /**
   * {{{
   * Rule "[] monotone 2".
   * Premise q(||) ==> p(||)
   * Conclusion [a;]q(||) ==> [a;]p(||)
   * End.
   * }}}
   *
   * @derived
   *   useAt(boxMonotone) with p and q swapped
   * @see
   *   "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
   * @see
   *   "André Platzer. Differential Hybrid Games."
   * @note
   *   Renamed form of boxMonotone.
   */
  @Derivation
  lazy val monb2: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "monb2",
      canonicalName = "[] monotone 2",
      displayName = Some("[] monotone 2"),
      displayNameAscii = Some("[]monotone 2"),
      displayNameLong = Some("[]monotone 2"),
      displayPremises = "Q |- P",
      displayConclusion = "[a;]Q |- [a;]P",
    ),
    Sequent(immutable.IndexedSeq("[a_;]q_(||)".asFormula), immutable.IndexedSeq("[a_;]p_(||)".asFormula)),
    useAt(box, PosInExpr(1 :: Nil))(-1) & useAt(box, PosInExpr(1 :: Nil))(1) &
      notL(-1) & notR(1) &
      byUS(mondrule) &
      //      ProofRuleTactics.axiomatic("<> monotone", USubst(
      //        SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Not(PredOf(Function("q_", None, Real, Bool), Anything))) ::
      //          SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Not(PredOf(Function("p_", None, Real, Bool), Anything))) :: Nil)) &
      notL(-1) & notR(1),
  )

  /**
   * {{{
   * Rule "con convergence flat".
   * Premisses: \exists x_ (x <= 0 & J(||)) |- P
   *            x_ > 0, J(||) |- <a{|x_|}><x_:=x_-1;> J(||)
   * Conclusion  \exists x_ J(||) |- <a{|x_|}*>P(||)
   * }}}
   * {{{
   *  \exists x_ (x_ <= 0 & J(x_)) |- P   x_ > 0, J(x_) |- <a{|x_|}>J(x_-1)
   * ----------------------------------------------------------------------- con
   *  \exists x_ J(x_) |- <a{|x_|}*>P
   * }}}
   */
  @Derivation
  lazy val conflat: DerivedRuleInfo = derivedRuleSequent(
    DerivedRuleInfo.create(
      name = "conflat",
      canonicalName = "con convergence flat",
      displayName = Some("con flat"),
      displayNameAscii = Some("conflat"),
      displayNameLong = Some("conflat"),
      displayPremises = "\\exists v (v<=0&J) |- P;; v > 0, J |- <a>J(v-1)",
      displayConclusion = "J |- <a*>P",
    ),
    Sequent(
      immutable.IndexedSeq(Exists(immutable.Seq(v), Jany)),
      immutable.IndexedSeq(Diamond(Loop(anonv), "p_(||)".asFormula)),
    ),
    cut(Diamond(Loop(anonv), Exists(immutable.Seq(v), And(LessEqual(v, Number(0)), Jany)))) < (
      hideL(-1) & mond
      // existsL(-1)
      // useAt("exists eliminate", PosInExpr(1::Nil))(-1) & andL(-1)
      ,
      hideR(1) & by(Ax.conrule)
    ),
  )

  // derived axioms and their proofs

  /**
   * {{{
   * Axiom "<-> reflexive".
   *   p() <-> p()
   * End.
   * }}}
   *
   * @see
   *   [[equalReflexive]]
   */
  @Derivation
  lazy val equivReflexive: DerivedAxiomInfo = derivedFact(
    DerivedAxiomInfo.create(
      name = "equivReflexive",
      canonicalName = "<-> reflexive",
      displayName = Some("↔R"),
      displayNameAscii = Some("<->R"),
      displayConclusion = "__p↔p__",
      key = "",
      recursor = "",
      unifier = Unifier.Full,
    ),
    DerivedAxiomProvableSig.startProof(
      Sequent(IndexedSeq(), IndexedSeq("p_() <-> p_()".asFormula)),
      Declaration(Map.empty),
    )(EquivRight(SuccPos(0)), 0)
    // right branch
    (Close(AntePos(0), SuccPos(0)), 1)
    // left branch
    (Close(AntePos(0), SuccPos(0)), 0),
  )

  /** Convert <-> to two implications: `(p_() <-> q_()) <-> (p_()->q_())&(q_()->p_())` */
  @Derivation
  lazy val equivExpand: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "equivExpand",
      canonicalName = "<-> expand",
      displayName = Some("↔2→←"),
      displayNameAscii = Some("<->2-><-"),
      unifier = Unifier.Full,
    ),
    "(p_() <-> q_()) <-> (p_()->q_())&(q_()->p_())".asFormula,
    prop,
  )

  /** Convert <-> to two conjunctions: `(p_() <-> q_()) <-> (p_()&q_())|(!p_()&!q_())` */
  @Derivation
  lazy val equivExpandAnd: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "equivExpandAnd",
      canonicalName = "<-> expand and",
      displayName = Some("↔2∧"),
      displayNameAscii = Some("<->2&"),
      unifier = Unifier.Full,
    ),
    "(p_() <-> q_()) <-> (p_()&q_())|(!p_()&!q_())".asFormula,
    prop,
  )

  /**
   * {{{
   * Axiom "-> distributes over &".
   *   (p() -> (q()&r())) <-> ((p()->q()) & (p()->r()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val implyDistAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "implyDistAnd",
      canonicalName = "-> distributes over &",
      displayName = Some("→∧"),
      displayNameAscii = Some("->&"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_()&r_())) <-> ((p_()->q_()) & (p_()->r_()))".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "-> weaken".
   *   (p() -> q()) -> (p()&c() -> q())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val implyWeaken: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "implyWeaken",
      canonicalName = "-> weaken",
      displayName = Some("→W"),
      displayNameAscii = Some("->W"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) -> ((p_()&c_()) -> q_())".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "-> distributes over <->".
   *   (p() -> (q()<->r())) <-> ((p()->q()) <-> (p()->r()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val implyDistEquiv: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "implyDistEquiv",
      canonicalName = "-> distributes over <->",
      displayName = Some("→↔"),
      displayNameAscii = Some("-><->"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_()<->r_())) <-> ((p_()->q_()) <-> (p_()->r_()))".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "| distributes over &".
   *   (p() & (q() | r())) <-> ((p() & q()) | (p() & r()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val orDistAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "orDistAnd",
      canonicalName = "| distributes over &",
      displayName = Some("∨∧"),
      displayNameAscii = Some("|&"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() & (q_()|r_())) <-> ((p_()&q_()) | (p_()&r_()))".asFormula)),
    prop,
  )

  /** CONGRUENCE AXIOMS (for constant terms) */

  /**
   * {{{
   * Axiom "const congruence"
   *   s() = t() -> ctxT_(s()) = ctxT_(t())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val constCongruence: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "constCongruence",
      canonicalName = "const congruence",
      displayName = Some("CCE"),
      key = "1",
      recursor = "*",
      unifier = Unifier.Full,
    ),
    "s() = t() -> ctxT_(s()) = ctxT_(t())".asFormula,
    allInstantiateInverse(("s()".asTerm, "x_".asVariable))(1) &
      by(proveBy(
        "\\forall x_ (x_ = t() -> ctxT_(x_) = ctxT_(t()))".asFormula,
        useAt(assignbeq, PosInExpr(1 :: Nil))(1) &
          useAt(assignbAxiom)(1) &
          byUS(equalReflexive),
      )),
  )

  /**
   * {{{
   * Axiom "const formula congruence"
   *   s() = t() -> (ctxF_(s()) <-> ctxF_(t()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val constFormulaCongruence: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "constFormulaCongruence",
      canonicalName = "const formula congruence",
      displayName = Some("CCQ"),
      key = "1",
      recursor = "*",
      unifier = Unifier.Full,
    ),
    "s() = t() -> (ctxF_(s()) <-> ctxF_(t()))".asFormula,
    allInstantiateInverse(("s()".asTerm, "x_".asVariable))(1) &
      by(proveBy(
        "\\forall x_ (x_ = t() -> (ctxF_(x_) <-> ctxF_(t())))".asFormula,
        useAt(assignbeq, PosInExpr(1 :: Nil))(1) &
          useAt(assignbAxiom)(1) &
          byUS(equivReflexive),
      )),
  )

  /**
   * {{{
   * Axiom "!! double negation".
   *   (!(!p())) <-> p()
   * End.
   * }}}
   */
  @Derivation
  lazy val doubleNegation: DerivedAxiomInfo = derivedFact(
    DerivedAxiomInfo.create(
      name = "doubleNegation",
      canonicalName = "!! double negation",
      displayName = Some("¬¬"),
      displayNameAscii = Some("!!"),
      displayConclusion = "__¬¬p__↔p",
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    DerivedAxiomProvableSig.startProof(
      Sequent(IndexedSeq(), IndexedSeq("(!(!p_())) <-> p_()".asFormula)),
      Declaration(Map.empty),
    )(EquivRight(SuccPos(0)), 0)
    // right branch
    (NotRight(SuccPos(0)), 1)(NotLeft(AntePos(1)), 1)(Close(AntePos(0), SuccPos(0)), 1)
    // left branch
    (NotLeft(AntePos(0)), 0)(NotRight(SuccPos(1)), 0)(Close(AntePos(0), SuccPos(0)), 0),
  )

  /**
   * {{{
   * Axiom "vacuous all quantifier".
   *   (\forall x_ p()) <-> p()
   * End.
   * }}}
   *
   * @Derived
   *   from new axiom "p() -> (\forall x_ p())" and ""all instantiate" or "all eliminate".
   * @todo
   *   replace by weaker axiom in AxiomBase and prove it.
   */

  /**
   * {{{
   * Axiom "exists dual".
   *   (!\forall x (!p(||))) <-> (\exists x p(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val existsDual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsDual",
      canonicalName = "exists dual",
      displayName = Some("∃d"),
      displayNameAscii = Some("existsd"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__¬∀x ¬P__ ↔ ∃x P",
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_ (!p_(||))) <-> \\exists x_ p_(||)".asFormula)),
    useAt(alld, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  @Derivation
  lazy val existsPDual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsPDual",
      canonicalName = "exists prime dual",
      displayName = Some("∃'d"),
      displayNameAscii = Some("existsprimed"),
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_' (!p_(||))) <-> \\exists x_' p_(||)".asFormula)),
    useAt(allPd, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  @Derivation
  lazy val existsDualy: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsDualy",
      canonicalName = "exists dual y",
      displayName = Some("∃d"),
      displayNameAscii = Some("existsdy"),
      displayLevel = DisplayLevel.Internal,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall y_ (!p_(||))) <-> \\exists y_ p_(||)".asFormula)),
    useAt(alldy, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "!exists".
   *   (!\exists x (p(||))) <-> \forall x (!p(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val notExists: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notExists",
      canonicalName = "!exists",
      displayName = Some("¬∃"),
      displayNameAscii = Some("!exists"),
      displayConclusion = "__(¬∃x (p(x)))__↔∀x (¬p(x))",
      key = "0",
      recursor = "0;*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!\\exists x_ (p_(||))) <-> \\forall x_ (!p_(||))".asFormula)),
    useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: 0 :: Nil) &
      useAt(alld)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "!all".
   *   (!\forall x (p(||))) <-> \exists x (!p(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val notAll: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notAll",
      canonicalName = "!all",
      displayName = Some("¬∀"),
      displayNameAscii = Some("!all"),
      displayConclusion = "__¬∀x (p(x)))__↔∃x (¬p(x))",
      key = "0",
      recursor = "0;*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_ (p_(||))) <-> \\exists x_ (!p_(||))".asFormula)),
    useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: 0 :: Nil) &
      useAt(existsDual)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "![]".
   *   ![a;]P <-> <a;>!P
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val notBox: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notBox",
      canonicalName = "![]",
      displayName = Some("¬[]"),
      displayNameAscii = Some("![]"),
      displayConclusion = "__¬[a]P__↔<a>¬P",
      key = "0",
      recursor = "1;*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(![a_;]p_(||)) <-> (<a_;>!p_(||))".asFormula)),
    useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: 1 :: Nil) &
      useAt(diamond)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "!<>".
   *   !<a;>p(x) <-> [a;]!p(x)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val notDiamond: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notDiamond",
      canonicalName = "!<>",
      displayName = Some("¬<>"),
      displayNameAscii = Some("!<>"),
      displayConclusion = "__¬<a>P__↔[a]¬P",
      key = "0",
      recursor = "1;*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!<a_;>p_(||)) <-> ([a_;]!p_(||))".asFormula)),
    useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: 1 :: Nil) &
      useAt(box)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  // ***************
  // Derived Axioms
  // ***************

  /**
   * {{{
   * Axiom "all distribute".
   *   (\forall x (p(x)->q(x))) -> ((\forall x p(x))->(\forall x q(x)))
   * }}}
   */
  @Derivation
  lazy val allDist: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "allDist",
      canonicalName = "all distribute",
      displayName = Some("∀→"),
      displayNameAscii = Some("all->"),
      displayConclusion = "(∀x (p(x)→q(x))) → (__∀x p(x) → ∀x q(x)__)",
      key = "1",
      recursor = "*",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("(\\forall x_ (p(x_)->q(x_))) -> ((\\forall x_ p(x_))->(\\forall x_ q(x_)))".asFormula),
    ),
    implyR(1) & implyR(1) & allR(1) & allL(-2) & allL(-1) & prop,
  )

  /**
   * {{{
   * Axiom "all distribute elim".
   *   (\forall x (P->Q)) -> ((\forall x P)->(\forall x Q))
   * }}}
   */
  @Derivation
  lazy val allDistElim: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "allDistElim",
      canonicalName = "all distribute elim",
      displayName = Some("∀→"),
      displayNameAscii = Some("all->"),
      displayConclusion = "(∀x (P→Q)) → (__∀x P → ∀x Q__)",
      key = "1",
      recursor = "*",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("(\\forall x_ (p_(||)->q_(||))) -> ((\\forall x_ p_(||))->(\\forall x_ q_(||)))".asFormula),
    ),
    implyR(1) & implyR(1) & ProofRuleTactics.skolemizeR(1) & useAt(alle)(-1) & useAt(alle)(-2) & prop,
  )

  /**
   * {{{
   * Axiom "all quantifier scope".
   *    (\forall x (p(x) & q())) <-> ((\forall x p(x)) & q())
   * End.
   * }}}
   *
   * @todo
   *   follows from "all distribute" and "all vacuous"
   */

  /**
   * {{{
   * Axiom "exists distribute elim".
   *   (\forall x (P->Q)) -> ((\exists x P)->(\exists x Q))
   * }}}
   */
  @Derivation
  lazy val existsDistElim: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsDistElim",
      canonicalName = "exists distribute elim",
      displayName = Some("∃→"),
      displayNameAscii = Some("exists->"),
      displayConclusion = "(∀x (P→Q)) → (__∃x P → ∃x Q__)",
      key = "1",
      recursor = "*",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("(\\forall x_ (p_(||)->q_(||))) -> ((\\exists x_ p_(||))->(\\exists x_ q_(||)))".asFormula),
    ),
    useExpansionAt(existsDual)(1, 1 :: 0 :: Nil) &
      useExpansionAt(existsDual)(1, 1 :: 1 :: Nil) &
      useAt(converseImply, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(converseImply, PosInExpr(0 :: Nil))(1, 0 :: 0 :: Nil) &
      byUS(allDistElim),
  )

  /**
   * {{{
   * Axiom "[] box".
   *    (!<a;>(!p(||))) <-> [a;]p(||)
   * End.
   * }}}
   *
   * @note
   *   almost same proof as "exists dual"
   * @Derived
   */
  @Derivation
  lazy val box: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "box",
      canonicalName = "[] box",
      displayName = Some("[·]"),
      displayNameAscii = Some("[.]"),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "__&not;&langle;a&rangle;&not;P__ ↔ [a]P",
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!<a_;>(!p_(||))) <-> [a_;]p_(||)".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: 1 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   *   Axiom "Kd diamond modus ponens".
   *     [a{|^@|};](p(||)->q(||)) -> (<a{|^@|};>p(||) -> <a{|^@|};>q(||))
   *   End.
   * }}}
   */
  @Derivation
  lazy val Kd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Kd",
      canonicalName = "Kd diamond modus ponens",
      displayConclusion = "[a](P→Q) → (<a>P → __<a>Q__)",
      key = "1.1",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};](p(||)->q(||)) -> (<a{|^@|};>p(||) -> <a{|^@|};>q(||))".asFormula)),
    useExpansionAt(diamond)(1, 1 :: 0 :: Nil) &
      useExpansionAt(diamond)(1, 1 :: 1 :: Nil) &
      useAt(converseImply, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(converseImply, PosInExpr(0 :: Nil))(1, 0 :: 1 :: Nil) &
      byUS(K),
  )

  /**
   * {{{
   *   Axiom "Kd2 diamond modus ponens".
   *     [a{|^@|};]p(||) -> (<a{|^@|};>q(||) -> <a{|^@|};>(p(||)&q(||)))
   *   End.
   * }}}
   */
  @Derivation
  lazy val Kd2: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Kd2",
      canonicalName = "Kd2 diamond modus ponens",
      displayConclusion = "[a]P → (<a>Q → __<a>(P∧Q)__)",
      key = "1.1",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};]p(||) -> (<a{|^@|};>q(||) -> <a{|^@|};>(p(||)&q(||)))".asFormula)),
    useExpansionAt(diamond)(1, 1 :: 0 :: Nil) &
      useExpansionAt(diamond)(1, 1 :: 1 :: Nil) &
      useAt(Ax.converseImply, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(K, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(K, PosInExpr(1 :: Nil))(1) &
      useAt(proveBy("(p_() -> !(p_()&q_()) -> !q_()) <-> true".asFormula, prop))(1, 1 :: Nil) &
      byUS(boxTrueAxiom) & TactixLibrary.done,
  )

  /**
   * {{{
   * Axiom "[]~><> propagation".
   *    [a;]p(||) & <a;>q(||) -> <a;>(p(||) & q(||))
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   unsound for hybrid games
   */
  @Derivation
  lazy val boxDiamondPropagation: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "boxDiamondPropagation", canonicalName = "[]~><> propagation", displayName = Some("[]~><>")),
    Sequent(
      IndexedSeq(),
      IndexedSeq("([a_{|^@|};]p_(||) & <a_{|^@|};>q_(||)) -> <a_{|^@|};>(p_(||) & q_(||))".asFormula),
    ),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: 1 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      cut("[a_{|^@|};]p_(||) & [a_{|^@|};]!(p_(||)&q_(||)) -> [a_{|^@|};]!q_(||)".asFormula) < (
        /* use */ SaturateTactic(alphaRule) & andLi(keepLeft = false)(AntePos(1), AntePos(2)) & modusPonens(
          AntePos(1),
          AntePos(0),
        ) & id,
        /* show */ hideR(1) &
          cut("[a_{|^@|};](p_(||) & !(p_(||)&q_(||)))".asFormula) < (
            /* use */ implyR(1) & hideL(-2) & /* monb fails renaming substitution */ implyRi & CMon(
              PosInExpr(1 :: Nil)
            ) & propClose,
            /* show */ implyR(1) & TactixLibrary.boxAnd(1) & propClose
          )
      ),
  )

  /**
   * {{{
   * Axiom "[]~><> subst propagation".
   *    <a;>true -> ([a;]p(||) -> <a;>p(||))
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   unsound for hybrid games
   */
  @Derivation
  lazy val boxDiamondSubstPropagation: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "boxDiamondSubstPropagation",
      canonicalName = "[]~><> subst propagation",
      displayName = Some("[]~><> subst"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("<a_{|^@|};>true -> ([a_{|^@|};]p(||) -> <a_{|^@|};>p(||))".asFormula)),
    cut("[a_{|^@|};]p(||) & <a_{|^@|};>true -> <a_{|^@|};>p(||)".asFormula) < (
      prop & done,
      hideR(1) & useAt(boxDiamondPropagation, PosInExpr(0 :: Nil))(1, 0 :: Nil) & useAt(andTrue)(1, 0 :: 1 :: Nil) &
        prop & done
    ),
  )

  /**
   * {{{
   * Axiom "K1".
   *   [a;](p(||)&q(||)) -> [a;]p(||) & [a;]q(||)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   implements Cresswell, Hughes. A New Introduction to Modal Logic, K1 p. 26
   * @internal
   */
  private lazy val K1: ProvableSig = TactixLibrary.proveBy( // derivedAxiom("K1",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)".asFormula)),
    implyR(1) & andR(1) < (
      useAt(boxSplitLeft, PosInExpr(0 :: Nil))(-1) & close,
      useAt(boxSplitRight, PosInExpr(0 :: Nil))(-1) & close
    ),
  )

  /**
   * {{{
   * Axiom "K2".
   *   [a;]p(||) & [a;]q(||) -> [a;](p(||)&q(||))
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   unsound for hybrid games
   * @note
   *   implements Cresswell, Hughes. A New Introduction to Modal Logic, K2 p. 27
   * @internal
   */
  private lazy val K2: ProvableSig = TactixLibrary.proveBy( // derivedAxiom("K2",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};]p_(||) & [a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))".asFormula)),
    cut(
      /*(9)*/ "([a_{|^@|};](q_(||)->p_(||)&q_(||)) -> ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))))  ->  (([a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)) -> [a_{|^@|};](p_(||)&q_(||)))"
        .asFormula
    ) < (
      /* use */ cut(
        /*(6)*/ "[a_{|^@|};](q_(||) -> (p_(||)&q_(||)))  ->  ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||)))"
          .asFormula
      ) < (
        /* use */ modusPonens(AntePos(1), AntePos(0)) & close,
        /* show */ cohide(2) & byUS(K)
      ),
      /* show */ cut(
        /*(8)*/ "([a_{|^@|};]p_(||) -> [a_{|^@|};](q_(||) -> p_(||)&q_(||)))  ->  (([a_{|^@|};](q_(||)->p_(||)&q_(||)) -> ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))))  ->  (([a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)) -> [a_{|^@|};](p_(||)&q_(||))))"
          .asFormula
      ) < (
        /* use */ cut( /*(5)*/ "[a_{|^@|};]p_(||) -> [a_{|^@|};](q_(||) -> p_(||)&q_(||))".asFormula) < (
          /* use */ modusPonens(AntePos(1), AntePos(0)) & close,
          /* show */ cohide(3) & useAt(K, PosInExpr(1 :: Nil))(1) & useAt(implyTautology)(1, 1 :: Nil) & HilbertCalculus
            .V(1) & close
        ),
        /* show */ cohide(3) & prop
      )
    ),
  )

  /**
   * {{{
   * Axiom "K modal modus ponens &".
   *    [a;](p_(||)->q_(||)) & [a;]p_(||) -> [a;]q_(||)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   unsound for hybrid games
   */
  @Derivation
  lazy val Kand: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Kand",
      canonicalName = "K modal modus ponens &",
      displayName = Some("K&"),
      displayConclusion = "[a](P→Q) ∧ [a]P → __[a]Q__)",
      key = "1",
      recursor = "0;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};](p_(||)->q_(||)) & [a{|^@|};]p_(||) -> [a{|^@|};]q_(||)".asFormula)),
    useAt(andImplies, PosInExpr(0 :: Nil))(1) &
      byUS(K),
  )

  /**
   * {{{
   * Axiom "&->".
   *    (A() & B() -> C()) <-> (A() -> B() -> C())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val andImplies: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "andImplies", canonicalName = "&->", displayName = Some("&->")),
    Sequent(IndexedSeq(), IndexedSeq("(A_() & B_() -> C_()) <-> (A_() -> B_() -> C_())".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "[] split".
   *    [a;](p(||)&q(||)) <-> [a;]p(||)&[a;]q(||)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   unsound for hybrid games
   * @note
   *   implements Cresswell, Hughes. A New Introduction to Modal Logic, K3 p. 28
   */
  @Derivation
  lazy val boxAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "boxAnd",
      canonicalName = "[] split",
      displayName = Some("[]∧"),
      displayNameAscii = Some("[]^"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__[a](P∧Q)__↔[a]P ∧ [a]Q",
      key = "0",
      recursor = "0;1",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) <-> [a_{|^@|};]p_(||)&[a_{|^@|};]q_(||)".asFormula)),
    equivR(1) < (
      useAt(K1, PosInExpr(1 :: Nil))(1) & close,
      useAt(K2, PosInExpr(1 :: Nil))(1) & close
    ),
  )

  /**
   * {{{
   * Axiom "[] or left".
   *    [a;](p(||)) -> [a;](p(||)|[a;]q(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val boxOrLeft: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "boxOrLeft",
      canonicalName = "[] or left",
      displayName = Some("[]∨L"),
      displayNameAscii = Some("[]orL"),
      displayLevel = DisplayLevel.Browse,
      displayConclusion = "[a]P->__[a](P∨Q)__",
      key = "1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("[a;]p(||) -> [a;](p(||) | q(||))".asFormula)),
    implyR(1) & monb & prop,
  )

  /**
   * {{{
   * Axiom "[] or right".
   *    [a;](p(||)) -> [a;](p(||)|[a;]q(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val boxOrRight: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "boxOrRight",
      canonicalName = "[] or right",
      displayName = Some("[]∨R"),
      displayNameAscii = Some("[]orR"),
      displayLevel = DisplayLevel.Browse,
      displayConclusion = "[a]Q->__[a](P∨Q)__",
      key = "1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("[a;]q(||) -> [a;](p(||) | q(||))".asFormula)),
    implyR(1) & monb & prop,
  )

  /**
   * {{{
   * Axiom "[] conditional split".
   *    [a;](p(||)->q(||)&r(||)) <-> [a;](p(||)->q(||)) & [a;](p(||)->r(||))
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   unsound for hybrid games
   */
  @Derivation
  lazy val boxImpliesAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "boxImpliesAnd",
      canonicalName = "[] conditional split",
      displayName = Some("[]→∧"),
      displayNameAscii = Some("[]->^"),
      displayConclusion = "__[a](P→Q∧R)__ ↔ [a](P→Q) ∧ [a](P→R)",
      unifier = Unifier.Linear,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "[a_{|^@|};](P_(||)->Q_(||)&R_(||)) <-> [a_{|^@|};](P_(||)->Q_(||)) & [a_{|^@|};](P_(||)->R_(||))".asFormula
      ),
    ),
    useAt(implyDistAnd, PosInExpr(0 :: Nil))(1, 0 :: 1 :: Nil) &
      useAt(boxAnd, PosInExpr(0 :: Nil))(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "boxSplitLeft".
   *    [a;](p(||)&q(||)) -> [a;]p(||)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   implements (1)-(5) of Cresswell, Hughes. A New Introduction to Modal Logic, K1
   * @internal
   */
  private lazy val boxSplitLeft: ProvableSig = {
    TactixLibrary.proveBy( // derivedAxiom("[] split left",
      Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||)".asFormula)),
      cut( /*(2)*/ "[a_{|^@|};](p_(||)&q_(||) -> p_(||))".asFormula) < (
        /* use */ cut(
          /*(4)*/ "[a_{|^@|};](p_(||)&q_(||)->p_(||)) -> ([a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||))".asFormula
        ) < (
          /* use */ modusPonens(AntePos(0), AntePos(1)) & close,
          /* show */ cohide(2) & byUS(K)
        ),
        /* show */ cohide(2) & useAt(PC1)(1, 1 :: 0 :: Nil) & useAt(implySelf)(1, 1 :: Nil) & HilbertCalculus
          .V(1) & close
      ),
    )
  }

  /**
   * {{{
   * Axiom "<> split".
   *    <a;>(p(||)|q(||)) <-> <a;>p(||)|<a;>q(||)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   unsound for hybrid games
   */
  @Derivation
  lazy val diamondOr: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "diamondOr",
      canonicalName = "<> split",
      displayName = Some("<>∨"),
      displayNameAscii = Some("<>|"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__&langle;a&rangle;(P∨Q)__↔&langle;a&rangle;P ∨ &langle;a&rangle;Q",
      key = "0",
      recursor = "0;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<a_{|^@|};>(p_(||)|q_(||)) <-> <a_{|^@|};>p_(||)|<a_{|^@|};>q_(||)".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 1 :: Nil) &
      useAt(notOr)(1, 0 :: 0 :: 1 :: Nil) &
      useAt(boxAnd)(1, 0 :: 0 :: Nil) &
      useAt(notAnd)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<> partial vacuous".
   *    <a;>p(||) & q() <-> <a;>(p(||)&q())
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   unsound for hybrid games
   */
  @Derivation
  lazy val pVd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "pVd", canonicalName = "<> partial vacuous", key = "1", recursor = "0;1"),
    Sequent(IndexedSeq(), IndexedSeq("(<a_{|^@|};>p_(||) & q_()) <-> <a_{|^@|};>(p_(||)&q_())".asFormula)),
    equivR(1) < (
      andL(-1) & useAt(diamond, PosInExpr(1 :: Nil))(1) & notR(1) &
        useAt(diamond, PosInExpr(1 :: Nil))(-1) & notL(-1) &
        useAt(notAnd)(-2, 1 :: Nil) & useAt(implyExpand, PosInExpr(1 :: Nil))(-2, 1 :: Nil) &
        useAt(converseImply)(-2, 1 :: Nil) & useAt(doubleNegation)(-2, 1 :: 0 :: Nil) &
        useAt(K, PosInExpr(0 :: Nil))(-2) & implyL(-2) < (HilbertCalculus.V(Symbol("Rlast")) & id, id),
      useAt(diamond, PosInExpr(1 :: Nil))(-1) & useAt(notAnd)(-1, 0 :: 1 :: Nil) &
        useAt(implyExpand, PosInExpr(1 :: Nil))(-1, 0 :: 1 :: Nil) & notL(-1) &
        andR(1) < (
          useAt(diamond, PosInExpr(1 :: Nil))(1) & notR(1) & implyRi &
            useAt(K, PosInExpr(1 :: Nil))(1) &
            useAt(proveBy("(!p() -> p() -> q()) <-> true".asFormula, prop))(1, 1 :: Nil) & byUS(boxTrueAxiom),
          useAt(proveBy("!q_() -> (p_() -> !q_())".asFormula, prop), PosInExpr(1 :: Nil))(2, 1 :: Nil) &
            HilbertCalculus.V(2) & notR(2) & id
        )
    ),
  )

  /**
   * {{{
   * Axiom "<> split left".
   *   <a;>(p(||)&q(||)) -> <a;>p(||)
   * End.
   * }}}
   *
   * @Derived
   * @internal
   */
  private lazy val diamondSplitLeft: ProvableSig = TactixLibrary.proveBy( // derivedAxiom("<> split left",
    Sequent(IndexedSeq(), IndexedSeq("<a_;>(p_(||)&q_(||)) -> <a_;>p_(||)".asFormula)),
    useAt(PC1)(1, 0 :: 1 :: Nil) & useAt(implySelf)(1) & close,
  )

  /**
   * {{{
   * Axiom "boxSplitRight".
   *   [a;](p(||)&q(||)) -> [a;]q(||)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   implements (6)-(9) of Cresswell, Hughes. A New Introduction to Modal Logic, K1
   * @internal
   */
  private lazy val boxSplitRight: ProvableSig = TactixLibrary.proveBy( // derivedAxiom("[] split right",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]q_(||)".asFormula)),
    cut( /*7*/ "[a_{|^@|};](p_(||)&q_(||) -> q_(||))".asFormula) < (
      /* use */ cut(
        /*(8)*/ "[a_{|^@|};](p_(||)&q_(||)->q_(||)) -> ([a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]q_(||))".asFormula
      ) < (
        /* use */ modusPonens(AntePos(0), AntePos(1)) & close,
        /* show */ cohide(2) & byUS(K)
      ),
      /* show */ cohide(2) & useAt(PC2)(1, 1 :: 0 :: Nil) & useAt(implySelf)(1, 1 :: Nil) & HilbertCalculus.V(1) & close
    ),
  )

  /**
   * {{{
   * Axiom ":= assign dual 2".
   *   <x:=f();>p(||) <-> [x:=f();]p(||)
   * End.
   * }}}
   *
   * @see
   *   [[assignDual]]
   */
  @Derivation
  lazy val assignDual2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "assignDual2",
      canonicalName = ":= assign dual 2",
      displayName = Some("⟨:=⟩D"),
      displayNameAscii = Some("<:=>D"),
      displayConclusion = "__&langle;x:=f();&rangle;P__ ↔ [x:=f();]P",
      key = "0",
      recursor = "*",
    ),
    "<x_:=f();>p(||) <-> [x_:=f();]p(||)".asFormula,
    useAt(selfassignb, PosInExpr(1 :: Nil))(1, 0 :: 1 :: Nil) &
      useAt(assigndAxiom)(1, 0 :: Nil) &
      byUS(equivReflexive),
    // NOTE alternative proof:
    //    useAt("[:=] assign equality exists")(1, 1::Nil) &
    //      useAt("<:=> assign equality")(1, 0::Nil) &
    //      byUS(equivReflexiveAxiom)
  )

  @Derivation
  lazy val DassignDual2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "DassignDual2", canonicalName = "':= assign dual 2", displayName = Some("':=D")),
    "<x_':=f();>p(||) <-> [x_':=f();]p(||)".asFormula,
    useAt(Dselfassignb, PosInExpr(1 :: Nil))(1, 0 :: 1 :: Nil) &
      useAt(DassigndAxiom)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<:=> assign equality".
   *   <x:=f();>p(||) <-> \exists x (x=f() & p(||))
   * End.
   * }}}
   *
   * @Derived
   *   from [:=] assign equality, quantifier dualities
   * @Derived
   *   by ":= assign dual" from "[:=] assign equality exists".
   */
  @Derivation
  lazy val assigndEqualityAxiom: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "assigndEqualityAxiom",
      canonicalName = "<:=> assign equality",
      displayName = Some("<:=>"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__<x:=e>P__↔∃x(x=e∧P)",
      key = "0",
      recursor = "0.1;*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f_();>p_(||) <-> \\exists x_ (x_=f_() & p_(||))".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(existsDual, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(notAnd)(1, 1 :: 0 :: 0 :: Nil) &
      useAt(implyExpand, PosInExpr(1 :: Nil))(1, 1 :: 0 :: 0 :: Nil) &
      CE(PosInExpr(0 :: Nil)) &
      byUS(assignbeq),
  )

  @Derivation
  lazy val DassigndEqualityAxiom: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DassigndEqualityAxiom",
      canonicalName = "<':=> assign equality",
      displayName = Some("<':=>"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__<x':=e>P__↔∃x'(x'=e∧P)",
      key = "0",
      recursor = "0.1;*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("<x_':=f_();>p_(||) <-> \\exists x_' (x_'=f_() & p_(||))".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(existsPDual, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(notAnd)(1, 1 :: 0 :: 0 :: Nil) &
      useAt(implyExpand, PosInExpr(1 :: Nil))(1, 1 :: 0 :: 0 :: Nil) &
      CE(PosInExpr(0 :: Nil)) &
      byUS(Dassignbeq),
  )

  /**
   * {{{
   * Axiom "[:=] assign equality exists".
   *   [x:=f();]p(||) <-> \exists x (x=f() & p(||))
   * End.
   * }}}
   *
   * @Derived
   *   by ":= assign dual" from "<:=> assign equality".
   * @todo
   *   does not derive yet
   */
  @Derivation
  lazy val assignbequalityexists: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "assignbequalityexists",
      canonicalName = "[:=] assign equality exists",
      displayName = Some("[:=]"),
      displayNameAscii = Some("[:=] assign exists"),
    ),
    "[x_:=f();]p(||) <-> \\exists x_ (x_=f() & p(||))".asFormula,
    useAt(assignDual2, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      byUS(assigndEqualityAxiom),
    //      useAt(assigndEqualityAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
    //        //@note := assign dual is not applicable since [v:=t()]p(v) <-> <v:=t()>p(t),
    //        //      and [v:=t()]p(||) <-> <v:=t()>p(||) not derivable since clash in allL
    //        useAt(":= assign dual")(1, 1::Nil) & byUS(equivReflexiveAxiom)
  )

  @Derivation
  lazy val Dassignbequalityexists: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "Dassignbequalityexists",
      canonicalName = "[':=] assign equality exists",
      displayName = Some("[':=]"),
      displayNameAscii = Some("[':=] assign exists"),
    ),
    "[x_':=f();]p(||) <-> \\exists x_' (x_'=f() & p(||))".asFormula,
    useAt(DassignDual2, PosInExpr(1 :: Nil))(1, 0 :: Nil) & byUS(DassigndEqualityAxiom),
  )

  /**
   * {{{
   * Axiom "[:=] assign exists".
   *   [x_:=f_();]p_(||) -> \exists x_ p_(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val assignbexists: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "assignbexists",
      canonicalName = "[:=] assign exists",
      displayName = Some("[:=]∃"),
      displayNameAscii = Some("[:=]exists"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("[x_:=f_();]p_(||) -> \\exists x_ p_(||)".asFormula)),
//    useAt(existsAndAxiom, PosInExpr(1::Nil))(1, 1::Nil)
//      & byUS("[:=] assign equality exists")
    useAt(assignbequalityexists, PosInExpr(0 :: Nil))(1, 0 :: Nil) &
      byUS(existsAnd),
  )

  /**
   * {{{
   * Axiom "[:=] assign all".
   *   \forall x_ p_(||) -> [x_:=f_();]p_(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val assignball: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "assignball",
      canonicalName = "[:=] assign all",
      displayName = Some("[:=]∀"),
      displayNameAscii = Some("[:=]all"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(||) -> [x_:=f_();]p_(||)".asFormula)),
    //    useAt(existsAndAxiom, PosInExpr(1::Nil))(1, 1::Nil)
    //      & byUS("[:=] assign equality exists")
    useAt(assignbeq, PosInExpr(0 :: Nil))(1, 1 :: Nil) &
      byUS(forallImplies),
  )

  /**
   * {{{
   * Axiom "\\exists& exists and".
   *   \exists x_ (q_(||) & p_(||)) -> \exists x_ (p_(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val existsAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsAnd",
      canonicalName = "\\exists& exists and",
      displayName = Some("∃∧"),
      displayNameAscii = Some("existsand"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ (q_(||) & p_(||)) -> \\exists x_ (p_(||))".asFormula)),
    /*implyR(1) &*/ CMon(PosInExpr(0 :: Nil)) & prop, // & andL(-1) & closeId//(-2,1)
  )

  /**
   * {{{
   * Axiom "\\exists& exists or"
   *   (\exists x_ (p_(x_) |  q_(x_))) <-> (\exists x_ p_(x_) | \exists x_ q_(x_))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val existsOr: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsOr",
      canonicalName = "\\exists| exists or",
      displayName = Some("∃∨"),
      displayNameAscii = Some("existsor"),
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("(\\exists x_ (p_(x_) |  q_(x_))) <-> (\\exists x_ p_(x_) | \\exists x_ q_(x_))".asFormula),
    ),
    equivR(1) < (
      existsL(-1) & orR(1) & existsR(1) & existsR(2) & prop,
      orL(-1) < (
        existsL(-1) & existsR(1) & prop,
        existsL(-1) & existsR(1) & prop
      )
    ),
  )

  /**
   * {{{
   * Axiom "\\forall-> forall implies".
   *   \forall x_ p_(||) -> \forall x_ (q_(||) -> p_(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val forallImplies: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "forallImplies",
      canonicalName = "\\forall-> forall implies",
      displayName = Some("∀→"),
      displayNameAscii = Some("forallimplies"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(||) -> \\forall x_ (q_(||) -> p_(||))".asFormula)),
    /*implyR(1) &*/ CMon(PosInExpr(0 :: Nil)) & prop, // & andL(-1) & closeId//(-2,1)
  )

  /**
   * {{{
   * Axiom "<:=> assign equality all".
   *   <x:=f();>p(||) <-> \forall x (x=f() -> p(||))
   * End.
   * }}}
   */
  @Derivation
  lazy val assigndEqualityAll: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "assigndEqualityAll",
      canonicalName = "<:=> assign equality all",
      displayName = Some("<:=>"),
      key = "0",
      recursor = "*;0.1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f_();>p_(||) <-> \\forall x_ (x_=f_() -> p_(||))".asFormula)),
    useAt(assignDual2, PosInExpr(0 :: Nil))(1, 0 :: Nil) &
      byUS(assignbeq),
  )

  /**
   * {{{
   * Axiom "<:=> assign".
   *   <v:=t();>p(v) <-> p(t())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val assigndAxiom: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "assigndAxiom",
      canonicalName = "<:=> assign",
      displayName = Some("<:=>"),
      displayConclusion = "__&langle;x:=e&rangle;p(x)__↔p(e)",
      key = "0",
      recursor = "*",
      unifier = Unifier.Full,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f();>p(x_) <-> p(f())".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(assignbAxiom)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  @Derivation
  lazy val DassigndAxiom: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DassigndAxiom",
      canonicalName = "<':=> assign",
      displayName = Some("<':=>"),
      displayConclusion = "__&langle;x':=e&rangle;p(x')__↔p(e)",
      key = "0",
      recursor = "*",
      unifier = Unifier.Full,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<x_':=f();>p(x_') <-> p(f())".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(Dassignb)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<:=> self assign".
   *   <x_:=x_;>p(||) <-> p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val selfassignd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "selfassignd", canonicalName = "<:=> self assign", displayName = Some("<:=>")),
    Sequent(IndexedSeq(), IndexedSeq("<x_:=x_;>p(||) <-> p(||)".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(selfassignb)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom ":= assign dual".
   *   <v:=t();>p(v) <-> [v:=t();]p(v)
   * End.
   * }}}
   *
   * @see
   *   [[assignDual2]]
   */
  @Derivation
  lazy val assignDual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "assignDual", canonicalName = ":= assign dual", displayName = Some(":=D")),
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f();>p(x_) <-> [x_:=f();]p(x_)".asFormula)),
    useAt(assigndAxiom)(1, 0 :: Nil) &
      useAt(assignbAxiom)(1, 1 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "[:=] assign equational".
   *   [v:=t();]p(v) <-> \forall v (v=t() -> p(v))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val assignbequational: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "assignbequational",
      canonicalName = "[:=] assign equational",
      displayName = Some("[:=]=="),
      key = "0",
      recursor = "*;0.1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("[x_:=f();]p(x_) <-> \\forall x_ (x_=f() -> p(x_))".asFormula)),
    useAt(assignbAxiom)(1, 0 :: Nil) &
      commuteEquivR(1) &
      byUS(allSubstitute),
  )

  /**
   * {{{
   * Axiom "[:=] assign update".
   *   [x:=t();]P <-> [x:=t();]P
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val assignbup: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "assignbup",
      canonicalName = "[:=] assign update",
      displayName = Some("[:=]"),
      key = "0",
      recursor = "1;*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("[x_:=t_();]p_(||) <-> [x_:=t_();]p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<:=> assign update".
   *   <x:=t();>P <-> <x:=t();>P
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val assigndup: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "assigndup",
      canonicalName = "<:=> assign update",
      displayName = Some("<:=>"),
      key = "0",
      recursor = "1;*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("<x_:=t_();>p_(||) <-> <x_:=t_();>p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "[:=] vacuous assign".
   *   [v:=t();]p() <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val vacuousAssignb: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "vacuousAssignb", canonicalName = "[:=] vacuous assign", displayName = Some("V[:=]")),
    Sequent(IndexedSeq(), IndexedSeq("[v_:=t_();]p_() <-> p_()".asFormula)),
    useAt(assignbAxiom)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<:=> vacuous assign".
   *   <v:=t();>p() <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val vacuousAssignd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "vacuousAssignd", canonicalName = "<:=> vacuous assign", displayName = Some("V<:=>")),
    Sequent(IndexedSeq(), IndexedSeq("<v_:=t_();>p_() <-> p_()".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(vacuousAssignb)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "[':=] differential assign".
   *   [x_':=f();]p(x_') <-> p(f())
   * End.
   * }}}
   *
   * @Derived
   */
  lazy val assignDAxiomb: ProvableSig = DerivedAxiomProvableSig.axioms("[':=] differential assign")
  // @note the following derivation works if uniform renaming can mix BaseVariable with DifferentialSymbols.
  /*derivedAxiom("[':=] differential assign",
    Sequent(IndexedSeq(), IndexedSeq("[x_':=f();]p(x_') <-> p(f())".asFormula)),
    ProofRuleTactics.uniformRenaming(DifferentialSymbol(Variable("x_")), Variable("x_")) &
    byUS("[:=] assign")
//      useAt(assignbAxiom)(1, 0::0::Nil) &
//      byUS(equivReflexiveAxiom)
  )*/

  /**
   * {{{
   * Axiom "[':=] differential assign y".
   *   [y_':=f();]p(y_') <-> p(f())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val Dassignby: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Dassignby",
      canonicalName = "[':=] differential assign y",
      displayName = Some("[y':=]"),
      displayLevel = DisplayLevel.Internal,
      displayConclusion = "__[y':=c]p(y')__↔p(c)",
      unifier = Unifier.Full,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[y_':=f();]p(y_') <-> p(f())".asFormula)),
    byUS(assignDAxiomb),
  )

  /**
   * {{{
   * Axiom "<':=> differential assign".
   *   <v':=t();>p(v') <-> p(t())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val Dassignd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Dassignd",
      canonicalName = "<':=> differential assign",
      displayName = Some("<':=>"),
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("<x_':=f();>p(x_') <-> p(f())".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(Dassignb, PosInExpr(0 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<:*> assign nondet".
   *   <x:=*;>p(x) <-> (\exists x p(x))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val randomd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "randomd",
      canonicalName = "<:*> assign nondet",
      displayName = Some("<:*>"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__<x:=*>P__↔∃x P",
      key = "0",
      recursor = "0;*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<x_:=*;>p_(||) <-> (\\exists x_ p_(||))".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(randomb)(1, 0 :: 0 :: Nil) &
      useAt(alld, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<?> test".
   *   <?q();>p() <-> (q() & p())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val testd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "testd",
      canonicalName = "<?> test",
      displayName = Some("<?>"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__<?Q>P__↔Q∧P",
      key = "0",
      recursor = "1;0",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<?q_();>p_() <-> (q_() & p_())".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(testb)(1, 0 :: 0 :: Nil) &
      prop,
  )

  /* inverse testd axiom for chase */
  @Derivation
  lazy val invtestd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "invtestd",
      canonicalName = "<?> invtest",
      displayName = Some("<?>i"),
      key = "0",
      recursor = "1",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(q_() & p_()) <-> <?q_();>p_()".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(testb)(1, 1 :: 0 :: Nil) &
      prop,
  )

  /* inverse testd axiom for chase */
  @Derivation
  lazy val testdcombine: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "testdcombine",
      canonicalName = "<?> combine",
      displayName = Some("<?> combine"),
      key = "0",
      recursor = "*",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<?q_();><?p_();>r_() <-> <?q_()&p_();>r_()".asFormula)),
    useAt(testd)(1, 1 :: Nil) &
      useAt(testd)(1, 0 :: Nil) &
      useAt(testd)(1, 0 :: 1 :: Nil) &
      prop,
  )

  /**
   * {{{
   * Axiom "<++> choice".
   *   <a;++b;>p(||) <-> (<a;>p(||) | <b;>p(||))
   * End.
   * }}}
   *
   * @todo
   *   first show de Morgan
   */
  @Derivation
  lazy val choiced: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "choiced",
      canonicalName = "<++> choice",
      displayName = Some("<∪>"),
      displayNameAscii = Some("<++>"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__<a∪b>P__↔<a>P∨<b>P",
      key = "0",
      recursor = "0;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<a_;++b_;>p_(||) <-> (<a_;>p_(||) | <b_;>p_(||))".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(choiceb)(1, 0 :: 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 1 :: Nil) &
      equivR(1) & OnAll(SaturateTactic(alphaRule)) < (andLi & id, orL(-1) & OnAll(notL(-1) & id)),
  )

  /**
   * {{{
   * Axiom "<;> compose".
   *   <a;b;>p(||) <-> <a;><b;>p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val composed: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "composed",
      canonicalName = "<;> compose",
      displayName = Some("<;>"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__<a;b>P__↔<a><b>P",
      key = "0",
      recursor = "1;*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<a_;b_;>p_(||) <-> <a_;><b_;>p_(||)".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(composeb)(1, 0 :: 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 1 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(doubleNegation)(1, 1 :: 0 :: 1 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<*> iterate".
   *   <{a;}*>p(||) <-> (p(||) | <a;><{a;}*> p(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val iterated: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "iterated",
      canonicalName = "<*> iterate",
      displayName = Some("<*>"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__<a*>P__↔P∨<a><a*>P",
      key = "0",
      recursor = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<{a_;}*>p_(||) <-> (p_(||) | <a_;><{a_;}*> p_(||))".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(iterateb)(1, 0 :: 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 1 :: 1 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 1 :: Nil) &
      useAt(notAnd)(1, 0 :: Nil) & // HilbertCalculus.stepAt(1, 0::Nil) &
      useAt(doubleNegation)(1, 1 :: 1 :: 0 :: 1 :: Nil) &
      prop,
  )

  /**
   * {{{
   * Axiom "<*> approx".
   *   <a;>p(||) -> <{a;}*>p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val loopApproxd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "loopApproxd",
      canonicalName = "<*> approx",
      displayName = Some("<*> approx"),
      displayConclusion = "<a>P → __<a*>P__",
      key = "1",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<a_;>p_(||) -> <{a_;}*>p_(||)".asFormula)),
    useAt(iterated)(1, 1 :: Nil) &
      useAt(iterated)(1, 1 :: 1 :: 1 :: Nil) &
      cut("<a_;>p_(||) -> <a_;>(p_(||) | <a_;><{a_;}*>p_(||))".asFormula) < (
        /* use */ prop,
        /* show */ hideR(1) & implyR(Symbol("_")) & mond & prop
      ),
  )

  /**
   * {{{
   * Axiom "[*] approx".
   *   [{a;}*]p(||) -> [a;]p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val loopApproxb: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "loopApproxb",
      canonicalName = "[*] approx",
      displayName = Some("[*] approx"),
      displayConclusion = "__[a*]P__ → [a]P",
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[{a_;}*]p_(||) -> [a_;]p_(||)".asFormula)),
    useAt(iterateb)(1, 0 :: Nil) &
      useAt(iterateb)(1, 0 :: 1 :: 1 :: Nil) &
      cut("[a_;](p_(||) & [a_;][{a_;}*]p_(||)) -> [a_;]p_(||)".asFormula) < (
        /* use */ prop,
        /* show */ hideR(1) & implyR(Symbol("_")) & HilbertCalculus.monb & prop
      ),
  )

  /**
   * {{{
   * Axiom "II induction".
   *   [{a;}*](p(||)->[a;]p(||)) -> (p(||)->[{a;}*]p(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val IIinduction: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "IIinduction",
      canonicalName = "II induction",
      displayName = Some("II induction"),
      displayLevel = DisplayLevel.Internal,
    ),
    "==> [{a_{|^@|};}*](p_(||)->[a_{|^@|};]p_(||)) -> (p_(||)->[{a_{|^@|};}*]p_(||))".asSequent,
    useAt(Iind)(1, 1 :: 1 :: Nil) & prop & done,
  )

  /**
   * {{{
   * Axiom "[*] merge".
   *   [{a;}*][{a;}*]p(||) <-> [{a;}*]p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val loopMergeb: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "loopMergeb",
      canonicalName = "[*] merge",
      displayName = Some("[*] merge"),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "__[a*][a*]P__ ↔ [a*]P",
      key = "0",
      recursor = "*",
    ),
    "==> [{a_{|^@|};}*][{a_{|^@|};}*]p_(||) <-> [{a_{|^@|};}*]p_(||)".asSequent,
    equivR(1) < (
      useAt(iterateb)(-1) & prop & done,
      implyRi & useAt(IIinduction, PosInExpr(1 :: Nil))(1) & G(1) & useAt(iterateb)(1, 0 :: Nil) & prop & done
    ),
  )

  /**
   * {{{
   * Axiom "<*> merge".
   *   <{a;}*><{a;}*>p(||) <-> <{a;}*>p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val loopMerged: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "loopMerged",
      canonicalName = "<*> merge",
      displayName = Some("<*> merge"),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "__<a*><a*>P__ ↔ <a*>P",
      key = "0",
      recursor = "*",
    ),
    "==> <{a_{|^@|};}*><{a_{|^@|};}*>p_(||) <-> <{a_{|^@|};}*>p_(||)".asSequent,
    equivR(1) < (
      useAt(diamond, PosInExpr(1 :: Nil))(1) & useAt(loopMergeb, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
        useAt(box, PosInExpr(1 :: Nil))(1, 0 :: 1 :: Nil) & useAt(diamond)(1) &
        useAt(doubleNegation)(1, 1 :: 1 :: Nil) & id & done,
      useAt(iterated)(1) & prop & done
    ),
  )

  /**
   * {{{
   * Axiom "[**] iterate iterate".
   *   [{a;}*;{a;}*]p(||) <-> [{a;}*]p(||)
   * End.
   * }}}
   * @see
   *   Lemma 7.6 of textbook
   * @Derived
   */
  @Derivation
  lazy val iterateiterateb: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "iterateiterateb",
      canonicalName = "[**] iterate iterate",
      displayName = Some("[**]"),
      displayConclusion = "__[a*;a*]P__ ↔ [a*]P",
      key = "",
      recursor = "*",
      unifier = Unifier.Full,
    ),
    "==> [{a_{|^@|};}*;{a_{|^@|};}*]p_(||) <-> [{a_{|^@|};}*]p_(||)".asSequent,
    useAt(composeb)(1, 0 :: Nil) & by(loopMergeb),
  )

  /**
   * {{{
   * Axiom "<**> iterate iterate".
   *   <{a;}*;{a;}*>p(||) <-> <{a;}*>p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val iterateiterated: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "iterateiterated",
      canonicalName = "<**> iterate iterate",
      displayName = Some("<**>"),
      displayConclusion = "__<a*;a*>P__ ↔ <a*>P",
      key = "",
      recursor = "*",
      unifier = Unifier.Full,
    ),
    "==> <{a_{|^@|};}*;{a_{|^@|};}*>p_(||) <-> <{a_{|^@|};}*>p_(||)".asSequent,
    useAt(composed)(1, 0 :: Nil) & by(loopMerged),
  )

  /**
   * {{{
   * Axiom "[*-] backiterate".
   *   [{a;}*]p(||) <-> p(||) & [{a;}*][{a;}]p(||)
   * End.
   * }}}
   * @see
   *   Lemma 7.5 in textbook
   * @Derived
   *   for programs
   */
  @Derivation
  lazy val backiterateb: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "backiterateb",
      canonicalName = "[*-] backiterate",
      displayName = Some("[*-]"),
      key = "0",
      recursor = "1.1;1;0",
      unifier = Unifier.Full,
    ),
    "==> [{a_{|^@|};}*]p_(||) <-> p_(||) & [{a_{|^@|};}*][a_{|^@|};]p_(||)".asSequent,
    equivR(1) < (
      byUS(backiteratebnecc),
      by(backiteratebsuff)
    ),
  )

  /**
   * {{{
   * Axiom "[*-] backiterate sufficiency".
   *   [{a;}*]p(||) <- p(||) & [{a;}*][{a;}]p(||)
   * End.
   * }}}
   * @see
   *   Lemma 7.5 in textbook
   * @Derived
   *   for programs
   */
  @Derivation
  lazy val backiteratebsuff: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "backiteratebsuff",
      canonicalName = "[*-] backiterate sufficiency",
      displayName = Some("[*-] backiterate sufficiency"),
      displayLevel = DisplayLevel.Internal,
    ),
    "p_(||) & [{a_{|^@|};}*][a_{|^@|};]p_(||) ==> [{a_{|^@|};}*]p_(||)".asSequent,
    andL(-1) & useAt(IIinduction, PosInExpr(1 :: 1 :: Nil))(1) < (
      close(-1, 1),
      hideL(-1) & byUS(monbaxiom) & implyR(1) & close(-1, 1)
    ),
  )

  /**
   * {{{
   * Axiom "[*-] backiterate necessity".
   *   [{a;}*]p(||) -> p(||) & [{a;}*][{a;}]p(||)
   * End.
   * }}}
   * @see
   *   Figure 7.8 in textbook
   * @Derived
   *   for programs
   */
  @Derivation
  lazy val backiteratebnecc: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "backiteratebnecc",
      canonicalName = "[*-] backiterate necessity",
      displayName = Some("[*-] backiterate necessity"),
      displayLevel = DisplayLevel.Internal,
    ),
    "[{b_{|^@|};}*]q_(||) ==> q_(||) & [{b_{|^@|};}*][b_{|^@|};]q_(||)".asSequent,
    andR(1) < (
      useAt(iterateb)(-1) & andL(-1) & close(-1, 1),
      generalize("[{b_{|^@|};}*]q_(||)".asFormula)(1) < (
        useAt(IIinduction, PosInExpr(1 :: 1 :: Nil))(1) < (
          close(-1, 1),
          G(1) & useAt(iterateb)(1, 0 :: Nil) & prop
        ),
        implyRi()(-1, 1) & byUS(loopApproxb)
      )
    ),
  )

  /**
   * {{{
   * Axiom "Ieq induction".
   *   [{a;}*]p(||) <-> p(||) & [{a;}*](p(||)->[{a;}]p(||))
   * End.
   * }}}
   * @see
   *   Section 7.7.4 in textbook
   * @Derived
   *   for programs
   */
  @Derivation
  lazy val I: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "I",
      canonicalName = "I",
      displayLevel = DisplayLevel.All,
      displayConclusion = "__[a*]P__↔P∧[a*](P→[a]P)",
      key = "0",
      recursor = "1.1.1;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "==> [{a_{|^@|};}*]p_(||) <-> p_(||) & [{a_{|^@|};}*](p_(||)->[a_{|^@|};]p_(||))".asSequent,
    equivR(1) < (
      andR(1) < (
        HilbertCalculus.iterateb(-1) & andL(-1) & close(-1, 1),
        useAt(backiterateb)(-1) & andL(-1) & hideL(-1) & byUS(monbaxiom) & implyR(1) & close(-1, 1)
      ),
      useAt(IIinduction, PosInExpr(1 :: 1 :: Nil))(1) & OnAll(prop & done)
    ),
  )

  // @todo this is somewhat indirect. Maybe it'd be better to represent derived axioms merely as Lemma and auto-wrap them within their ApplyRule[LookupLemma] tactics on demand.
  // private def useAt(lem: ApplyRule[LookupLemma]): PositionTactic = TactixLibrary.useAt(lem.rule.lemma.fact)

  /**
   * {{{
   * Axiom "exists generalize".
   *   p(t()) -> (\exists x p(x))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val existsGeneralize: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsGeneralize",
      canonicalName = "exists generalize",
      displayName = Some("∃G"),
      displayNameAscii = Some("existsG"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("p_(f()) -> (\\exists x_ p_(x_))".asFormula)),
    useAt(existsDual, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      implyR(SuccPos(0)) &
      notR(SuccPos(0)) &
      useAt(allInst, PosInExpr(0 :: Nil))(-2) &
      prop,
  )

  @Derivation
  lazy val existsGeneralizey: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsGeneralizey",
      canonicalName = "exists generalize y",
      displayName = Some("∃Gy"),
      displayNameAscii = Some("existsGy"),
      displayLevel = DisplayLevel.Internal,
    ),
    Sequent(IndexedSeq(), IndexedSeq("p_(f()) -> (\\exists y_ p_(y_))".asFormula)),
    useAt(existsDual, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      implyR(SuccPos(0)) &
      notR(SuccPos(0)) &
      useAt(allInst, PosInExpr(0 :: Nil))(-2) &
      prop,
  )

  /**
   * {{{
   * Axiom "exists eliminate".
   *   p(||) -> (\exists x p(||))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val existse: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existse",
      canonicalName = "exists eliminate",
      displayName = Some("∃e"),
      displayNameAscii = Some("existse"),
      displayConclusion = "P→__∃x P__",
      key = "1",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("p_(||) -> (\\exists x_ p_(||))".asFormula)),
    useAt(existsDual, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      implyR(1) &
      notR(1) &
      useAt(alle, PosInExpr(0 :: Nil))(-2) &
      prop,
    // also derives from existsDualAxiom & converseImply & doubleNegation & useAt("all eliminate")
  )

  /**
   * {{{
   * Axiom "exists eliminate y"
   *   p(||) -> \exists y_ p(||)
   * End.
   * }}}
   */
  @Derivation
  lazy val existsey: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsey",
      canonicalName = "exists eliminate y",
      displayName = Some("∃ey"),
      displayNameAscii = Some("existsey"),
      displayLevel = DisplayLevel.Internal,
    ),
    Sequent(IndexedSeq(), IndexedSeq("p_(||) -> (\\exists y_ p_(||))".asFormula)),
    useAt(existsDualy, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      implyR(1) &
      notR(1) &
      useAt(ally, PosInExpr(0 :: Nil))(-2) &
      prop,
    // also derives from existsDualAxiom & converseImply & doubleNegation & useAt(allEliminate_y)
  )

  /**
   * {{{
   * Axiom "all then exists".
   *   (\forall x p(||)) -> (\exists x p(||))
   * End.
   * }}}
   *
   * @see
   *   [[forallThenExists]]
   */
  @Derivation
  lazy val allThenExists: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "allThenExists",
      canonicalName = "all then exists",
      displayName = Some("∀→∃"),
      displayNameAscii = Some("allThenExists"),
      displayConclusion = "∀x P → ∃x P",
    ),
    "(\\forall x_ p_(||)) -> (\\exists x_ p_(||))".asFormula,
    useAt(existse, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(alle, PosInExpr(0 :: Nil))(1, 0 :: Nil) &
      implyR(1) & close(-1, 1),
  )

  /**
   * {{{
   * Axiom "all substitute".
   *   (\forall x (x=t() -> p(x))) <-> p(t())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val allSubstitute: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "allSubstitute",
      canonicalName = "all substitute",
      displayName = Some("∀S"),
      displayNameAscii = Some("allS"),
      displayConclusion = "__∀x(x=e→p(x))__ ↔ p(e)",
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ (x_=t_() -> p_(x_))) <-> p_(t_())".asFormula)),
    equivR(SuccPos(0)) < (
      /* equiv left */ allL(Variable("x_"), "t_()".asTerm)(-1) & implyL(-1) < (cohide(2) & byUS(equalReflexive), close),
      /* equiv right */ allR(1) & implyR(1) & eqL2R(-2)(1) & close
    ),
  )

  /**
   * {{{
   * Axiom "vacuous exists quantifier".
   *   (\exists x p()) <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val existsV: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsV",
      canonicalName = "vacuous exists quantifier",
      displayName = Some("V∃"),
      displayNameAscii = Some("existsV"),
      displayConclusion = "__∃x p__ ↔ p",
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(\\exists x_ p_()) <-> p_()".asFormula)),
    useAt(existsDual, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(allV)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "partial vacuous exists quantifier".
   *   (\exists x p(x) & q()) <-> (\exists x p(x)) & q()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val pexistsV: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "pexistsV",
      canonicalName = "partial vacuous exists quantifier",
      displayName = Some("pV∃"),
      displayNameAscii = Some("pexistsV"),
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ (p_(x_) & q_()) <-> \\exists x_ p_(x_) & q_()".asFormula)),
    equivR(1) < (
      existsL(-1) & andR(1) < (existsR("x_".asVariable)(1) & prop & done, prop & done),
      andL(Symbol("L")) & existsL(-1) & existsR("x_".asVariable)(1) & prop & done
    ),
  )

  /**
   * {{{ Axiom "V[:*] vacuous assign nondet". [x:=*;]p() <-> p() End.
   * @todo
   *   reorient
   * @Derived
   */
  @Derivation
  lazy val vacuousBoxAssignNondet: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "vacuousBoxAssignNondet",
      canonicalName = "V[:*] vacuous assign nondet",
      displayName = Some("V[:*]"),
      displayConclusion = "__[x:=*;]p__ ↔ p",
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("([x_:=*;]p_()) <-> p_()".asFormula)),
    useAt(randomb)(1, 0 :: Nil) &
      useAt(allV)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "V<:*> vacuous assign nondet".
   *   <x:=*;>p() <-> p()
   * End.
   * }}}
   *
   * @todo
   *   reorient
   * @Derived
   */
  @Derivation
  lazy val vacuousDiamondAssignNondet: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "vacuousDiamondAssignNondet",
      canonicalName = "V<:*> vacuous assign nondet",
      displayName = Some("V<:*>"),
      displayConclusion = "__<x:=*;>p__ ↔ p",
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(<x_:=*;>p_()) <-> p_()".asFormula)),
    useAt(randomd)(1, 0 :: Nil) &
      useAt(existsV)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "Domain Constraint Conjunction Reordering".
   *   [{c & (H(||) & q(||))}]p(||) <-> [{c & (q(||) & H(||))}]p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val domainCommute: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "domainCommute",
      canonicalName = "Domain Constraint Conjunction Reordering",
      displayName = Some("{∧}C"),
      displayNameAscii = Some("{&}C"),
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("[{c_ & (H_(||) & q_(||))}]p_(||) <-> [{c_ & (q_(||) & H_(||))}]p_(||)".asFormula),
    ),
    useAt(andCommute)(1, 0 :: 0 :: 1 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "[] post weaken".
   *   [a;]p(||)  ->  [a;](q(||)->p(||))
   * End.
   * }}}
   *
   * @Derived
   *   from M (or also from K)
   */
  @Derivation
  lazy val postWeaken: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "postWeaken",
      canonicalName = "[] post weaken",
      displayName = Some("[]PW"),
      key = "1",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("([a_;]p_(||))  ->  [a_;](q_(||)->p_(||))".asFormula)),
    implyR(1) & HilbertCalculus.monb & prop,
  )

  /**
   * {{{
   * Axiom "& commute".
   *   (p() & q()) <-> (q() & p())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val andCommute: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "andCommute",
      canonicalName = "& commute",
      displayName = Some("∧C"),
      displayNameAscii = Some("&C"),
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() & q_()) <-> (q_() & p_())".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "| commute".
   *   (p() | q()) <-> (q() | p())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val orCommute: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "orCommute",
      canonicalName = "| commute",
      displayName = Some("∨C"),
      displayNameAscii = Some("|C"),
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() | q_()) <-> (q_() | p_())".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "& associative".
   *   ((p() & q()) & r()) <-> (p() & (q() & r()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val andAssoc: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "andAssoc",
      canonicalName = "& associative",
      displayName = Some("∧A"),
      displayNameAscii = Some("&A"),
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("((p_() & q_()) & r_()) <-> (p_() & (q_() & r_()))".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "| associative".
   *   ((p() | q()) | r()) <-> (p() | (q() | r()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val orAssoc: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "orAssoc",
      canonicalName = "| associative",
      displayName = Some("∨A"),
      displayNameAscii = Some("|A"),
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("((p_() | q_()) | r_()) <-> (p_() | (q_() | r_()))".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "& reflexive".
   *   p() & p() <-> p()
   * End.
   * }}}
   */
  @Derivation
  lazy val andReflexive: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "andReflexive",
      canonicalName = "& reflexive",
      displayName = Some("∧R"),
      displayNameAscii = Some("&R"),
      key = "0",
      recursor = "*",
      unifier = Unifier.Full,
    ),
    Sequent(IndexedSeq(), IndexedSeq("p_() & p_() <-> p_()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "<-> true".
   *   (p() <-> true) <-> p()
   * End.
   * }}}
   */
  @Derivation
  lazy val equivTrue: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "equivTrue",
      canonicalName = "<-> true",
      displayName = Some("↔true"),
      displayNameAscii = Some("<-> true"),
      key = "0",
      recursor = "*",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p() <-> true) <-> p()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "-> self".
   *   (p() -> p()) <-> true
   * End.
   * }}}
   */
  @Derivation
  lazy val implySelf: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "implySelf",
      canonicalName = "-> self",
      displayName = Some("→self"),
      displayNameAscii = Some("-> self"),
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> p_()) <-> true".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "-> converse".
   *   (p() -> q()) <-> (!q() -> !p())
   * End.
   * }}}
   * Contraposition
   */
  @Derivation
  lazy val converseImply: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "converseImply",
      canonicalName = "-> converse",
      displayName = Some("→conv"),
      displayNameAscii = Some("-> conv"),
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) <-> (!q_() -> !p_())".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "!& deMorgan".
   *   (!(p() & q())) <-> ((!p()) | (!q()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val notAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notAnd",
      canonicalName = "!& deMorgan",
      displayName = Some("¬∧"),
      displayNameAscii = Some("!&"),
      displayConclusion = "__¬(p∧q)__↔(¬p|¬q)",
      unifier = Unifier.SurjectiveLinear,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(p_() & q_())) <-> ((!p_()) | (!q_()))".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "!| deMorgan".
   *   (!(p() | q())) <-> ((!p()) & (!q()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val notOr: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notOr",
      canonicalName = "!| deMorgan",
      displayName = Some("¬∨"),
      displayNameAscii = Some("!|"),
      displayConclusion = "__(¬(p|q))__↔(¬p∧¬q)",
      unifier = Unifier.SurjectiveLinear,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(p_() | q_())) <-> ((!p_()) & (!q_()))".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "!-> deMorgan".
   *   (!(p() -> q())) <-> ((p()) & (!q()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val notImply: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notImply",
      canonicalName = "!-> deMorgan",
      displayName = Some("¬→"),
      displayNameAscii = Some("!->"),
      displayConclusion = "__¬(p->q)__↔(p∧¬q)",
      unifier = Unifier.SurjectiveLinear,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(p_() -> q_())) <-> ((p_()) & (!q_()))".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "!<-> deMorgan".
   *   (!(p() <-> q())) <-> (((p()) & (!q())) | ((!p()) & (q())))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val notEquiv: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notEquiv",
      canonicalName = "!<-> deMorgan",
      displayName = Some("¬↔"),
      displayNameAscii = Some("!<->"),
      displayConclusion = "__¬(p↔q)__↔(p∧¬q)| (¬p∧q)",
      unifier = Unifier.SurjectiveLinear,
      key = "0",
      recursor = "0.0;0.1;1.0;1.1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(p_() <-> q_())) <-> (((p_()) & (!q_())) | ((!p_()) & (q_())))".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "-> expand".
   *   (p() -> q()) <-> ((!p()) | q())
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val implyExpand: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "implyExpand",
      canonicalName = "-> expand",
      displayName = Some("→E"),
      displayNameAscii = Some("->E"),
      unifier = Unifier.Linear,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) <-> ((!p_()) | q_())".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "PC1".
   *   p()&q() -> p()
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   implements Cresswell, Hughes. A New Introduction to Modal Logic, PC1
   */
  @Derivation
  lazy val PC1: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "PC1", canonicalName = "PC1", unifier = Unifier.Full),
    Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> p_()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "PC2".
   *   p()&q() -> q()
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   implements Cresswell, Hughes. A New Introduction to Modal Logic, PC2
   */
  @Derivation
  lazy val PC2: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "PC2", canonicalName = "PC2", unifier = Unifier.Full),
    Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> q_()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "PC3".
   *   p()&q() -> ((p()->r())->(p()->q()&r())) <-> true
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   implements Cresswell, Hughes. A New Introduction to Modal Logic, PC3
   */
  @Derivation
  lazy val PC3: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "PC3", canonicalName = "PC3", unifier = Unifier.Full),
    Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> ((p_()->r_())->(p_()->q_()&r_())) <-> true".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "PC9".
   *   p() -> p() | q()
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   implements Cresswell, Hughes. A New Introduction to Modal Logic, PC9
   */
  @Derivation
  lazy val PC9: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "PC9", canonicalName = "PC9", unifier = Unifier.Full),
    Sequent(IndexedSeq(), IndexedSeq("p_() -> p_() | q_()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "PC10".
   *   q() -> p() | q()
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   implements Cresswell, Hughes. A New Introduction to Modal Logic, PC10
   */
  @Derivation
  lazy val PC10: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "PC10", canonicalName = "PC10", unifier = Unifier.Full),
    Sequent(IndexedSeq(), IndexedSeq("q_() -> p_() | q_()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "-> tautology".
   *   (p() -> (q() -> p()&q())) <-> true
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val implyTautology: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "implyTautology",
      canonicalName = "-> tautology",
      displayName = Some("→taut"),
      displayNameAscii = Some("->taut"),
      unifier = Unifier.Full,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_() -> p_()&q_())) <-> true".asFormula)),
    prop,
  )

//  /**
//    * {{{Axiom "-' derive minus"
//    *    (f(||) - g(||))' = (f(||))' - (g(||))'
//    * End.
//    * }}}
//    * @todo needs CET so CE for terms
//    */
//  @Axiom("-'", conclusion = "__(f(x)-g(x))'__=f(x)'-g(x)'",
//    key = "0", recursor = "0;1", unifier = "surjlinear")
//  val Dminus: DerivedAxiomInfo = derivedAxiom("-' derive minus",
//    Sequent(IndexedSeq(), IndexedSeq("(f(||) - g(||))' = (f(||))' - (g(||))'".asFormula)),
//    useAt(minus2Plus)(1, 1::Nil) &
//      useAt(minus2Plus)(1, 0::0::Nil) &
//      useAt(Dlinear)(1, 0::Nil) &
//      byUS(equivReflexive)
//  )
//
//  /**
//    * {{{Axiom "-' derive neg"
//    *    (-f(||))' = -((f(||))')
//    * End.
//    * }}}
//    * @todo needs CET so CE for terms
//    */
//  @Axiom("-'", conclusion = "__(-f(x))'__=-(f(x))'",
//    key = "0", recursor = "0", unifier = "surjlinear")
//  val Dneg: DerivedAxiomInfo = derivedAxiom("-' derive neg",
//    Sequent(IndexedSeq(), IndexedSeq("(-f(||))' = -((f(||))')".asFormula)),
//    useAt(neg2Minus)(1, 0::0::Nil) &
//      useAt(neg2Minus)(1, 1::Nil) &
//      useAt(Dminus)(1, 0::Nil) &
//      useAt(Dconst)(1, 0::0::Nil) &
//      byUS(equivReflexive)
//  )
//
  /**
   * {{{
   * Axiom "<=' derive <=".
   *   (f(||) <= g(||))' <-> ((f(||))' <= (g(||))')
   * End.
   * }}}
   *
   * @Derivable
   *   by CE
   */
  @Derivation
  val Dlessequal: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Dlessequal",
      canonicalName = "<=' derive <=",
      displayName = Some("≤'"),
      displayNameAscii = Some("<='"),
      displayConclusion = "__(f(x)≤g(x))'__↔f(x)'≤g(x)'",
      key = "0",
      recursor = "0;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f(||) <= g(||))' <-> ((f(||))' <= (g(||))')".asFormula)),
    useAt(flipLessEqual)(1, 1 :: Nil) &
      useAt(flipLessEqual)(1, 0 :: 0 :: Nil) &
      byUS(Dgreaterequal),
  )

  /**
   * {{{
   * Axiom "<' derive <"
   *   (f(||) < g(||))' <-> ((f(||))' <= (g(||))')
   *   // sic(!) easier
   * End.
   * }}}
   *
   * @Derived
   *   by CE
   */
  @Derivation
  val Dless: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Dless",
      canonicalName = "<' derive <",
      displayName = Some("<'"),
      displayConclusion = "__(f(x)<g(m))'__↔f(x)'≤g(x)'",
      key = "0",
      recursor = "0;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f(||) < g(||))' <-> ((f(||))' <= (g(||))')".asFormula)),
    useAt(flipLessEqual)(1, 1 :: Nil) &
      useAt(flipLess)(1, 0 :: 0 :: Nil) &
      byUS(Dgreater),
  )

  @Derivation
  val Dequal: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Dequal",
      canonicalName = "=' derive =",
      displayName = Some("='"),
      displayConclusion = "__(f(x)=g(x))'__↔f(x)'=g(x)'",
      key = "0",
      recursor = "0;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f(||) = g(||))' <-> ((f(||))' = (g(||))')".asFormula)),
    useAt(equal2And)(1, 0 :: 0 :: Nil) &
      useAt(Dand)(1, 0 :: Nil) &
      useAt(Dlessequal)(1, 0 :: 0 :: Nil) &
      useAt(Dgreaterequal)(1, 0 :: 1 :: Nil) &
      useAt(equal2And, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "!=' derive !="
   *   (f(||) != g(||))' <-> ((f(||))' = (g(||))')
   *   // sic!
   * End.
   * }}}
   *
   * @Derived
   *   by CE
   */
  @Derivation
  val Dnotequal: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Dnotequal",
      canonicalName = "!=' derive !=",
      displayName = Some("≠'"),
      displayNameAscii = Some("!='"),
      displayConclusion = "__(f(x)≠g(x))'__↔f(x)'=g(x)'",
      key = "0",
      recursor = "0;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f(||) != g(||))' <-> ((f(||))' = (g(||))')".asFormula)),
    useAt(notEqual2Or)(1, 0 :: 0 :: Nil) &
      useAt(Dor)(1, 0 :: Nil) &
      useAt(Dless)(1, 0 :: 0 :: Nil) &
      useAt(Dgreater)(1, 0 :: 1 :: Nil) &
      useAt(equal2And, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "->' derive imply".
   *   (p(||) -> q(||))' <-> (!p(||) | q(||))'
   * End.
   * }}}
   *
   * @Derived
   *   by CE
   */
  @Derivation
  lazy val Dimply: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Dimply",
      canonicalName = "->' derive imply",
      displayName = Some("→'"),
      displayNameAscii = Some("->'"),
      displayConclusion = "__(P→Q)'__↔(¬P∨Q)'",
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_(||) -> q_(||))' <-> (!p_(||) | q_(||))'".asFormula)),
    useAt(implyExpand)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "\forall->\exists".
   *   (\forall x p(x)) -> (\exists x p(x))
   * End.
   * }}}
   *
   * @see
   *   [[allThenExists]]
   */
  @Derivation
  lazy val forallThenExists: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "forallThenExists",
      canonicalName = "\\forall->\\exists",
      displayName = Some("∀→∃"),
      displayNameAscii = Some("all->exists"),
      displayLevel = DisplayLevel.Internal,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ p_(x_)) -> (\\exists x_ p_(x_))".asFormula)),
    implyR(1) &
      useAt(existsGeneralize, PosInExpr(1 :: Nil))(1) &
      useAt(allInst)(-1) &
      id,
  )

  /**
   * {{{
   * Axiom "->true".
   *   (p()->true) <-> true
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val implyTrue: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "implyTrue",
      canonicalName = "->true",
      displayName = Some("→⊤"),
      displayNameAscii = Some("->T"),
      displayConclusion = "__(p→⊤)__↔⊤",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_()->true) <-> true".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "true->".
   *   (true->p()) <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val trueImply: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "trueImply",
      canonicalName = "true->",
      displayName = Some("⊤→"),
      displayNameAscii = Some("T->"),
      displayConclusion = "__(⊤→p)__↔p",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(true->p_()) <-> p_()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "&true".
   *   (p()&true) <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val andTrue: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "andTrue",
      canonicalName = "&true",
      displayName = Some("∧⊤"),
      displayNameAscii = Some("&T"),
      displayConclusion = "__(p∧⊤)__↔p",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_()&true) <-> p_()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "&false".
   *   (p()&false) <-> false
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val andFalse: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "andFalse",
      canonicalName = "&false",
      displayName = Some("∧⊥"),
      displayNameAscii = Some("&false"),
      displayConclusion = "__(p∧⊥)__↔⊥",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_()&false) <-> false".asFormula)),
    prop,
  )

  /* inverse andtrue axiom for chase */
  @Derivation
  lazy val andTrueInv: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "andTrueInv",
      canonicalName = "&true inv",
      displayName = Some("&true inv"),
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("p_() <-> (p_()&true)".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "true&".
   *   (true&p()) <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val trueAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "trueAnd",
      canonicalName = "true&",
      displayName = Some("⊤∧"),
      displayNameAscii = Some("T&"),
      displayConclusion = "__(⊤∧p)__↔p",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(true&p_()) <-> p_()".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "false&".
   *   (false&p()) <-> false
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val falseAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "falseAnd",
      canonicalName = "false&",
      displayName = Some("⊥∧"),
      displayNameAscii = Some("false&"),
      displayConclusion = "__(⊥∧p)__↔⊥",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(false&p_()) <-> false".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "0*".
   *   (0*f()) = 0
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val zeroTimes: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "zeroTimes", canonicalName = "0*", displayName = Some("0*"), unifier = Unifier.SurjectiveLinear),
    Sequent(IndexedSeq(), IndexedSeq("(0*f_()) = 0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(
      proveBy("\\forall x (0*x = 0)".asFormula, TactixLibrary.RCF)
    ),
  )

  /**
   * {{{
   * Axiom "*0".
   *   (f()*0) = 0
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val timesZero: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "timesZero", canonicalName = "*0", displayName = Some("*0"), unifier = Unifier.SurjectiveLinear),
    Sequent(IndexedSeq(), IndexedSeq("(f_()*0) = 0".asFormula)),
    if (false) useAt(timesCommute)(1, 0 :: Nil) & byUS(zeroTimes)
    else allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(
      proveBy("\\forall x (x*0 = 0)".asFormula, TactixLibrary.RCF)
    ),
  )

  /**
   * {{{
   * Axiom "-1*".
   *   (-1*f()) = -f()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val negOneTimes: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "negOneTimes",
      canonicalName = "-1*",
      displayName = Some("-1*"),
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("((-1)*f_()) = -f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(
      proveBy("\\forall x ((-1)*x = -x)".asFormula, TactixLibrary.RCF)
    ),
  )

  /**
   * {{{
   * Axiom "0+".
   *   (0+f()) = f()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val zeroPlus: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "zeroPlus", canonicalName = "0+", displayName = Some("0+"), unifier = Unifier.SurjectiveLinear),
    Sequent(IndexedSeq(), IndexedSeq("(0+f_()) = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(
      proveBy("\\forall x (0+x = x)".asFormula, TactixLibrary.RCF)
    ),
  )

  /**
   * {{{
   * Axiom "+0".
   *   (f()+0) = f()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val plusZero: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "plusZero", canonicalName = "+0", displayName = Some("+0"), unifier = Unifier.SurjectiveLinear),
    Sequent(IndexedSeq(), IndexedSeq("(f_()+0) = f_()".asFormula)),
    if (false) useAt(plusCommute)(1, 0 :: Nil) & byUS(zeroPlus)
    else allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(
      proveBy("\\forall x (x+0 = x)".asFormula, TactixLibrary.RCF)
    ),
  )

  // differential equations

  /**
   * {{{
   * Axiom "DW differential weakening".
   *   [{c&q(||)}]p(||) <-> ([{c&q(||)}](q(||)->p(||)))
   *   /* [x'=f(x)&q(x);]p(x) <-> ([x'=f(x)&q(x);](q(x)->p(x))) THEORY */
   * End.
   * }}}
   *
   * @see
   *   footnote 3 in "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and
   *   Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings,
   *   volume 9195 of LNCS, pages 467-481. Springer, 2015. arXiv 1503.01981, 2015."
   */
  @Derivation
  lazy val DW: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DW",
      canonicalName = "DW differential weakening",
      displayConclusion = "__[x'=f(x)&Q]P__↔[x'=f(x)&Q](Q→P)",
      key = "0",
      recursor = "",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[{c_&q_(||)}]p_(||) <-> ([{c_&q_(||)}](q_(||)->p_(||)))".asFormula)),
    equivR(1) < (
      /* equiv left */
      cut("[{c_&q_(||)}](p_(||)->(q_(||)->p_(||)))".asFormula) < (
        /* use */ useAt(K, PosInExpr(0 :: Nil))(-2) & implyL(-2) < (close, close),
        /* show */ G(2) & prop
      ),
      /* equiv right */
      useAt(K, PosInExpr(0 :: Nil))(-1) & implyL(-1) < (cohide(2) & byUS(DWbase), close)
    ),
  )

  /**
   * {{{
   * Axiom "DW differential weakening and".
   *   [{c&q(||)}]p(||) -> ([{c&q(||)}](q(||)&p(||)))
   * End.
   * }}}
   */
  @Derivation
  lazy val DWeakenAnd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DWeakenAnd",
      canonicalName = "DW differential weakening and",
      displayName = Some("DW∧"),
      displayNameAscii = Some("DWand"),
      displayConclusion = "[x'=f(x)&Q]P→[x'=f(x)&Q](Q∧P)",
    ),
    Sequent(IndexedSeq(), IndexedSeq("[{c_&q_(||)}]p_(||) -> ([{c_&q_(||)}](q_(||)&p_(||)))".asFormula)),
    implyR(1) & cut("[{c_&q_(||)}](q_(||)->(p_(||)->(q_(||)&p_(||))))".asFormula) < (
      /* use */ useAt(K, PosInExpr(0 :: Nil))(Symbol("Llast")) & implyL(Symbol("Llast")) < (
        cohide(Symbol("Rlast")) & byUS(DWbase) & done,
        useAt(K, PosInExpr(0 :: Nil))(Symbol("Llast")) & implyL(Symbol("Llast")) < (close, close)
      ),
      /* show */ G(Symbol("Rlast")) & prop
    ),
  )

  /**
   * {{{
   * Axiom "DW Q initial".
   *   (q(||) -> [{c&q(||)}]p(||)) <-> [{c&q(||)}]p(||)
   * End.
   * }}}
   */
  @Derivation
  lazy val DWQinitial: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DWQinitial",
      canonicalName = "DW Q initial",
      displayName = Some("DW Q initial"),
      displayConclusion = "(Q→[x'=f(x)&Q]P) ↔ [x'=f(x)&Q]P",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(q_(||) -> [{c_&q_(||)}]p_(||)) <-> [{c_&q_(||)}]p_(||)".asFormula)),
    equivR(1) < (
      implyL(-1) < (useAt(DI)(1) & implyR(1) & closeId(-1, 1), closeId(-1, 1)),
      implyR(1) & closeId(-1, 1)
    ),
  )

  /**
   * {{{
   * Axiom "DR differential refine".
   *   ([{c&q(||)}]p(||) <- [{c&r(||)}]p(||)) <- [{c&q(||)}]r(||)
   * End.
   *
   * @Derived
   * }}}
   */
  @Derivation
  lazy val DR: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DR",
      canonicalName = "DR differential refine",
      displayConclusion = "(__[{x'=f(x)&Q}]P__←[{x'=f(x)&R}]P)←[{x'=f(x)&Q}]R",
      key = "1.1",
      unifier = Unifier.SurjectiveLinear,
      inputs = "R:formula",
    ),
    Sequent(IndexedSeq(), IndexedSeq("([{c&q(||)}]p(||) <- [{c&r(||)}]p(||)) <- [{c&q(||)}]r(||)".asFormula)),
    implyR(1) &
      useAt(DMP, PosInExpr(1 :: Nil))(1) &
      useAt(DW, PosInExpr(1 :: Nil))(1) & id,
  )

  /**
   * {{{
   * Axiom "DR<> diamond differential refine".
   *   (<{c&q(||)}>p(||) <- <{c&r(||)}>p(||)) <- [{c&r(||)}]q(||)
   * End.
   *
   * @Derived
   * }}}
   */
  @Derivation
  lazy val DRd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DRd",
      canonicalName = "DR<> differential refine",
      displayConclusion = "(__<{x'=f(x)&Q}>P__←<{x'=f(x)&R}>P)←[{x'=f(x)&R}]Q",
      key = "1.1",
      unifier = Unifier.SurjectiveLinear,
      inputs = "R:formula",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(<{c&q(||)}>p(||) <- <{c&r(||)}>p(||)) <- [{c&r(||)}]q(||)".asFormula)),
    implyR(1) & implyR(1) &
      useAt(diamond, PosInExpr(1 :: Nil))(1) &
      useAt(diamond, PosInExpr(1 :: Nil))(-2) & notL(-2) & notR(1) &
      implyRi()(AntePos(1), SuccPos(0)) & implyRi &
      byUS(DR),
  )

  /**
   * {{{
   * Axiom "DC differential cut".
   *   ([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)
   * End.
   *
   * @Derived
   * }}}
   */
  // @todo: Reconsider names for all the variants of DC
  @Derivation
  lazy val DC: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DCaxiom",
      canonicalName = "DC differential cut",
      displayName = Some("DC"),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "(__[x'=f(x)&Q]P__↔[x'=f(x)&Q∧R]P)←[x'=f(x)&Q]R",
      key = "1.0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
      inputs = "R:formula",
    ),
    Sequent(IndexedSeq(), IndexedSeq("([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)".asFormula)),
    implyR(1) & equivR(1) < (
      implyRi()(AntePos(1), SuccPos(0)) &
        useAt(DR, PosInExpr(1 :: Nil))(1) &
        useAt(DW, PosInExpr(0 :: Nil))(1) & G(1) & prop,
      useAt(DWeakenAnd, PosInExpr(0 :: Nil))(-1) &
        implyRi()(AntePos(1), SuccPos(0)) & implyRi & byUS(DR)
    ),
  )

//  /**
//    * {{{Axiom "DI differential invariance".
//    *  ([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}]((p(||))'))
//    *  //([x'=f(x)&q(x);]p(x) <-> [?q(x);]p(x)) <- (q(x) -> [x'=f(x)&q(x);]((p(x))')) THEORY
//    * End.
//    * }}}
//    *
//    * @Derived
//    */
//  lazy val DIinvariance = DIequiv
//    /*DerivedAxiomProvableSig.axioms("DI differential invariance")*/ /*derivedAxiom("DI differential invariance",
//    Sequent(IndexedSeq(), IndexedSeq(DIinvarianceF)),
//    implyR(1) & equivR(1) <(
//      testb(1) &
//        useAt("DX differential skip")(-2) &
//        close
//      ,
//      testb(-2) &
//        useAt("DI differential invariant")(1) &
//        prop & onAll(close)
//    )
//  )*/

  /**
   * {{{
   * Axiom "DI differential invariant".
   *   [{c&q(||)}]p(||) <- (q(||)-> (p(||) & [{c&q(||)}]((p(||))')))
   *   // [x'=f(x)&q(x);]p(x) <- (q(x) -> (p(x) & [x'=f(x)&q(x);]((p(x))'))) THEORY
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val DI: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DI",
      canonicalName = "DI differential invariant",
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "__[{x'=f(x)&Q}]P__←(Q→P∧[{x'=f(x)&Q}](P)')",
      unifier = Unifier.SurjectiveLinear,
      key = "1",
      recursor = "1.1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("[{c&q(||)}]p(||) <- (q(||)-> (p(||) & [{c&q(||)}]((p(||))')))".asFormula)),
    implyR(1) & useAt(implyDistAnd, PosInExpr(0 :: Nil))(-1) & andL(-1) &
      useAt(testb, PosInExpr(1 :: Nil))(-1) &
      cut(DIinvarianceF) < (
        prop & onAll(close),
        cohide(2) & by(DIequiv)
      ),
  )
  private lazy val DIinvarianceF = "([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}]((p(||))'))".asFormula

  /**
   * {{{
   * Axiom "DIo open differential invariance <".
   *   ([{c&q(||)}]f(||)<g(||) <-> [?q(||);]f(||)<g(||)) <- (q(||) -> [{c&q(||)}](f(||)<g(||) -> (f(||)<g(||))'))
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val DIoless: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DIoless",
      canonicalName = "DIo open differential invariance <",
      displayName = Some("DIo <"),
      displayConclusion = "(__[{x'=f(x)&Q}]g(x)<h(x)__↔[?Q]g(x)<h(x))←(Q→[{x'=f(x)&Q}](g(x)<h(x)→(g(x)<h(x))'))",
      unifier = Unifier.SurjectiveLinear,
      key = "1.0",
      recursor = "*",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "([{c&q(||)}]f(||)<g(||) <-> [?q(||);]f(||)<g(||)) <- (q(||) -> [{c&q(||)}](f(||)<g(||) -> (f(||)<g(||))'))"
          .asFormula
      ),
    ),
    useAt(flipLess)(1, 1 :: 0 :: 1 :: Nil) &
      useAt(flipLess)(1, 1 :: 1 :: 1 :: Nil) &
      useAt(flipLess)(1, 0 :: 1 :: 1 :: 0 :: Nil) &
      Derive.Dless(1, 0 :: 1 :: 1 :: 1 :: Nil) &
      useAt(flipLessEqual)(1, 0 :: 1 :: 1 :: 1 :: Nil) &
      useExpansionAt(Dgreater)(1, 0 :: 1 :: 1 :: 1 :: Nil) &
      byUS(DIogreater),
  )

//  /**
//    * {{{Axiom "DV differential variant <=".
//    *    <{c&true}>f(||)<=g(||) <- \exists e_ (e_>0 & [{c&true}](f(||)>=g(||) -> f(||)'<=g(||)'-e_))
//    * End.
//    * }}}
//    *
//    * @Derived
//    */
//  lazy val DVLessEqual = derivedAxiom("DV differential variant <=",
//    Sequent(IndexedSeq(), IndexedSeq("<{c&true}>f(||)<=g(||) <- \\exists e_ (e_>0 & [{c&true}](f(||)>=g(||) -> f(||)'<=g(||)'-e_))".asFormula)),
//    useAt(flipLessEqual.fact)(1, 1::1::Nil) &
//      useAt(flipGreaterEqual.fact)(1, 0::0::1::1:: 0::Nil) &
//      useAt(flipLessEqual.fact)(1, 0::0::1::1:: 1::Nil) &
//      // transform g(||)'+e_<=f(||)' to g(||)'<=f(||)'-e_
//      useAt(TactixLibrary.proveBy("s()-r()>=t() <-> s()>=t()+r()".asFormula, QE & done), PosInExpr(0::Nil))(1, 0::0::1::1:: 1::Nil) &
//      byUS("DV differential variant >=")
//  )

  /**
   * {{{
   * Axiom "DX diamond differential skip".
   *   <{c&q(||)}>p(||) <- q(||)&p(||)
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val dDX: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "dDX",
      canonicalName = "DX diamond differential skip",
      displayConclusion = "Q∧P → <x'=f(x)&Q>P",
      key = "1",
      recursor = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<{c&q(||)}>p(||) <- q(||)&p(||)".asFormula)),
    useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(notAnd)(1, 0 :: 0 :: Nil) &
      useAt(implyExpand, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(DX, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(diamond)(1, 0 :: Nil) & implyR(1) & close,
  )

  /**
   * {{{
   * Axiom "DS differential equation solution".
   *   [{x'=c()}]p(x) <-> \forall t (t>=0 -> [x:=x+(c()*t);]p(x))
   * End.
   * }}}
   *
   * @Derived
   * @todo
   *   postcondition formulation is weaker than that of DS&
   */
  @Derivation
  lazy val DSnodomain: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DSnodomain",
      canonicalName = "DS differential equation solution",
      displayName = Some("DS"),
      displayConclusion = "__[{x'=c()}]P__ ↔ ∀t≥0 [x:=x+c()*t;]P",
      key = "0",
      recursor = "0.1.1;*",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("[{x_'=c_()}]p_(x_) <-> \\forall t_ (t_>=0 -> [x_:=x_+(c_()*t_);]p_(x_))".asFormula),
    ),
    useAt(DS)(1, 0 :: Nil) &
      useAt(implyTrue)(1, 0 :: 0 :: 1 :: 0 :: 0 :: Nil) &
      useAt(allV)(1, 0 :: 0 :: 1 :: 0 :: Nil) &
      useAt(trueImply)(1, 0 :: 0 :: 1 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "Dsol differential equation solution".
   *   <{x'=c()}>p(x) <-> \exists t (t>=0 & <x:=x+(c()*t);>p(x))
   * End.
   * }}}
   *
   * @Derived
   * @todo
   *   postcondition formulation is weaker than that of DS&
   */
  @Derivation
  lazy val DSdnodomain: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DSdnodomain",
      canonicalName = "Dsol differential equation solution",
      displayName = Some("DS"),
      displayConclusion = "__<{x'=c()}>P__ ↔ ∃t≥0 <x:=x+c()*t;>P",
      key = "0",
      recursor = "0.1.1;*",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("<{x_'=c_()}>p_(x_) <-> \\exists t_ (t_>=0 & <x_:=x_+(c_()*t_);>p_(x_))".asFormula),
    ),
    useAt(DSddomain)(1, 0 :: Nil) &
      useAt(implyTrue)(1, 0 :: 0 :: 1 :: 0 :: 0 :: Nil) &
      useAt(allV)(1, 0 :: 0 :: 1 :: 0 :: Nil) &
      useAt(trueAnd)(1, 0 :: 0 :: 1 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "Dsol& differential equation solution".
   *   <{x'=c()&q(x)}>p(||) <-> \exists t (t>=0 & ((\forall s ((0<=s&s<=t) -> q(x+(c()*s)))) & <x:=x+(c()*t);>p(||)))
   * End.
   * }}}
   */
  @Derivation
  lazy val DSddomain: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DSddomain",
      canonicalName = "Dsol& differential equation solution",
      displayName = Some("DS&"),
      unifier = Unifier.Linear,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "<{x_'=c()&q(x_)}>p(|x_',t_|) <-> \\exists t_ (t_>=0 & ((\\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) & <x_:=x_+(c()*t_);>p(|x_',t_|)))"
          .asFormula
      ),
    ),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(DS)(1, 0 :: 0 :: Nil) &
      useAt(alldt, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      useAt(notImply)(1, 0 :: 0 :: Nil) &
      useAt(notImply)(1, 0 :: 0 :: 1 :: Nil) &
      useAt(diamond)(1, 0 :: 0 :: 1 :: 1 :: Nil) &
      // useAt("& associative", PosInExpr(1::Nil))(1, 0::0::Nil) &
      byUS(equivReflexive),
  )

  //  lazy val existsDualAxiom: LookupLemma = derivedAxiom("exists dual",
  //    Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("\\exists x q(x) <-> !(\\forall x (!q(x)))".asFormula)))
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
   * {{{
   * Axiom "DG differential pre-ghost".
   *   [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{y_'=(a(|y_|)*y_)+b(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)
   *   // [x'=f(x)&q(x);]p(x) <-> \exists y [{y'=(a(x)*y)+b(x), x'=f(x))&q(x)}]p(x) THEORY
   * End.
   * }}}
   * Pre Differential Auxiliary / Differential Ghost -- not strictly necessary but saves a lot of reordering work.
   */
  @Derivation
  lazy val DGpreghost: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "DGpreghost", canonicalName = "DG differential pre-ghost", displayName = Some("DG")),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "[{c{|y_|}&q(|y_|)}]p(|y_|) <-> \\exists y_ [{y_'=(a(|y_|)*y_)+b(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)".asFormula
      ),
    ),
    useAt(DGa)(1, 0 :: Nil) &
      useAt(commaCommute)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  // diamond differential axioms

  /**
   * {{{
   * Axiom "DGd diamond differential ghost".
   *   <{c{|y_|}&q(|y_|)}>p(|y_|) <-> \forall y_ <{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}>p(|y_|)
   *   // <x'=f(x)&q(x);>p(x) <-> \forall y <{x'=f(x),y'=(a(x)*y)+b(x))&q(x)}>p(x) THEORY
   * End.
   * }}}
   */
  @Derivation
  lazy val DGd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "DGd", canonicalName = "DGd diamond differential ghost"),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}>p(|y_|)".asFormula
      ),
    ),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(DGa)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: 0 :: Nil) &
      useAt(alldy, PosInExpr(0 :: Nil))(1, 0 :: Nil) &
      useAt(diamond, PosInExpr(0 :: Nil))(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "DGd diamond inverse differential ghost implicational".
   *   <{c{|y_|}&q(|y_|)}>p(|y_|)  ->  \exists y_ <{y_'=a(||),c{|y_|}&q(|y_|)}>p(|y_|)
   * End.
   * }}}
   */
  @Derivation
  lazy val DGdi: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "DGdi", canonicalName = "DGd diamond inverse differential ghost implicational"),
    Sequent(
      IndexedSeq(),
      IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|)  <-  \\exists y_ <{y_'=a(||),c{|y_|}&q(|y_|)}>p(|y_|)".asFormula),
    ),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: 1 :: Nil) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(alldy)(1, 0 :: 0 :: Nil) &
      useAt(box)(1, 0 :: 0 :: 0 :: Nil) &
      useAt(converseImply, PosInExpr(1 :: Nil))(1) &
      byUS(DGi),
  )

  /**
   * {{{
   * Axiom "DGCd diamond differential ghost const".
   *   <{c{|y_|}&q(|y_|)}>p(|y_|) <-> \forall y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)
   * End.
   * }}}
   */
  @Derivation
  lazy val DGCd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DGCd",
      canonicalName = "DGd diamond differential ghost constant",
      displayName = Some("DG"),
      displayConclusion = "__[{x'=f(x)&Q}]P__↔∃y [{x'=f(x),y'=g()&Q}]P",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)".asFormula),
    ),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(DGC)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: 0 :: Nil) &
      useAt(alldy, PosInExpr(0 :: Nil))(1, 0 :: Nil) &
      useAt(diamond, PosInExpr(0 :: Nil))(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  @Derivation
  lazy val DGCdc: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "DGCdc", canonicalName = "DGd diamond differential ghost constant converse"),
    Sequent(
      IndexedSeq(),
      IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{y_'=b(|y_|),c{|y_|}&q(|y_|)}>p(|y_|)".asFormula),
    ),
    useAt(proveBy(
      "<{c,d&q(||)}>p(||) <-> <{d,c&q(||)}>p(||)".asFormula,
      useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
        useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
        useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1) &
        byUS(commaCommute),
    ))(1, PosInExpr(1 :: 0 :: Nil)) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(DGC)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 0 :: 0 :: 0 :: Nil) &
      useAt(alldy, PosInExpr(0 :: Nil))(1, 0 :: Nil) &
      useAt(diamond, PosInExpr(0 :: Nil))(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  @Derivation
  lazy val DGCde: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "DGCde", canonicalName = "DGd diamond differential ghost constant exists"),
    Sequent(
      IndexedSeq(),
      IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\exists y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)".asFormula),
    ),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 0 :: Nil) &
      useAt(DGCa)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(alldy, PosInExpr(0 :: Nil))(1, 1 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "DWd diamond differential weakening".
   *   <{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)&p_(||))
   * End.
   * }}}
   */
  @Derivation
  lazy val DWd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "DWd", canonicalName = "DWd diamond differential weakening"),
    Sequent(IndexedSeq(), IndexedSeq("<{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)&p_(||))".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(proveBy("!(p_() & q_()) <-> (p_() -> !q_())".asFormula, TactixLibrary.prop))(1, 1 :: 0 :: 1 :: Nil) &
      useAt(DW, PosInExpr(1 :: Nil))(1, 1 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "DWd Q initial".
   *   q_(||)&<{c&q_(||)}>p_(||) <-> <{c&q_(||)}>p_(||)
   * End.
   * }}}
   */
  @Derivation
  lazy val DWdQinitial: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "DWdQinitial", canonicalName = "DWd Q initial", displayName = Some("DWd Q initial")),
    Sequent(IndexedSeq(), IndexedSeq("q_(||)&<{c&q_(||)}>p_(||) <-> <{c&q_(||)}>p_(||)".asFormula)),
    equivR(1) < (
      andL(-1) & closeId(-2, 1),
      andR(1) < (
        useAt(diamond, PosInExpr(1 :: Nil))(-1) & notL(-1) & useAt(DWQinitial, PosInExpr(1 :: Nil))(2) & implyR(
          2
        ) & closeId(-1, 1),
        closeId(-1, 1)
      )
    ),
  )

  /**
   * {{{
   * Axiom "DWd2 diamond differential weakening".
   *   <{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)->p_(||))
   * End.
   * }}}
   */
  @Derivation
  lazy val DWd2: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "DWd2", canonicalName = "DWd2 diamond differential weakening"),
    Sequent(IndexedSeq(), IndexedSeq("<{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)->p_(||))".asFormula)),
    equivR(1) < (
      implyRi & CMon(PosInExpr(1 :: Nil)) & prop & done,
      cutAt("q_(||) & (q_(||)->p_(||))".asFormula)(1, 1 :: Nil) < (
        implyRi & useAt(Kd2, PosInExpr(1 :: Nil))(1) & byUS(DWbase),
        cohideR(1) & CMon(PosInExpr(1 :: Nil)) & prop & done
      )
    ),
  )

  /**
   * {{{
   * Axiom "DCd diamond differential cut".
   *   (<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)
   *   // (<x'=f(x)&q(x); >p(x) <-> <x'=f(x)&(q(x)&r(x));>p(x)) <- [x'=f(x)&q(x);]r(x) THEORY
   * End.
   * }}}
   */
  @Derivation
  lazy val DCdaxiom: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DCdaxiom",
      canonicalName = "DCd diamond differential cut",
      displayName = Some("DCd"),
      displayConclusion = "(__<x'=f(x)&Q>P__↔<x'=f(x)&Q∧R>P)←[x'=f(x)&Q]R",
      key = "1.0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: 1 :: Nil) &
      useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1, 1 :: Nil) &
      byUS(DC),
  )

  /**
   * {{{
   * Axiom "leave within closed <=".
   *   (<{c&q}>p<=0 <-> <{c&q&p>=0}>p=0) <- p>=0
   * End.
   * }}}
   */
  @Derivation
  lazy val leaveWithinClosed: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "leaveWithinClosed", canonicalName = "leave within closed <=", key = "1.0", recursor = "*"),
    "==>(<{c_{|t_|}&q_(|t_|)}>p_(|t_|)<=0 <-> <{c_{|t_|}&q_(|t_|)&p_(|t_|)>=0}>p_(|t_|)=0) <- p_(|t_|)>=0".asSequent,
    prop & Idioms.<(
      cut("[{c_{|t_|}&q_(|t_|)}]p_(|t_|)>=0".asFormula) & Idioms.<(
        dC("p_(|t_|)>=0".asFormula)(-2) & Idioms.<(
          useAt(DWd)(-2) & useAt(diamond, PosInExpr(1 :: Nil))(1) & useAt(diamond, PosInExpr(1 :: Nil))(-2) & notR(
            1
          ) & notL(-2) &
            generalize("(!p_(|t_|)=0)".asFormula)(1) & Idioms
              .<(id, useAt(equalExpand)(-1, 0 :: Nil) & useAt(flipGreaterEqual)(1, 0 :: 0 :: 1 :: Nil) & prop & done),
          id,
        ),
        useAt(diamond, PosInExpr(1 :: Nil))(1) & notR(1) &
          useAt(RIclosedgeq, PosInExpr(0 :: Nil))(1) & prop & HilbertCalculus.composeb(1) &
          dC("!p_(|t_|)=0".asFormula)(1) & Idioms.<(
            useAt(DW)(1) &
              TactixLibrary.generalize("true".asFormula)(1) & Idioms
                .<(cohideR(1) & useAt(boxTrueAxiom)(1), nil) /* TODO: Goedel? */ &
              implyR(1) &
              TactixLibrary.generalize("t_=0".asFormula)(1) & Idioms
                .<(cohideR(1) & assignb(1) & byUS(equalReflexive), nil) /* TODO: assignb? */ &
              implyR(1) &
              dR("p_(|t_|)>0".asFormula)(1) & Idioms.<(
                useAt(Cont, PosInExpr(1 :: Nil))(1) &
                  andR(1) < (
                    cohideR(1) & QE,
                    useAt(greaterEqual)(-1, 1 :: 1 :: 0 :: Nil) &
                      prop &
                      done
                  ),
                useAt(DW)(1) &
                  TactixLibrary.generalize("true".asFormula)(1) & Idioms
                    .<(cohideR(1) & useAt(boxTrueAxiom)(1), nil) /* TODO: Goedel? */ &
                  useAt(greaterEqual)(1, 1 :: Nil) &
                  prop &
                  done,
              ),
            id,
          ),
      ),
      dR("q_(|t_|)".asFormula)(-2) & Idioms.<(
        useAt(diamond, PosInExpr(1 :: Nil))(1) & notR(1) &
          useAt(diamond, PosInExpr(1 :: Nil))(-2) & notL(-2) &
          TactixLibrary.generalize("!p_(|t_|)<=0".asFormula)(1) & Idioms
            .<(id, useAt(lessEqual)(-1, 0 :: Nil) & prop & done),
        useAt(DW)(1) &
          TactixLibrary.generalize("true".asFormula)(1) & Idioms
            .<(cohideR(1) & useAt(boxTrueAxiom)(1), prop & done), /* TODO: Goedel? */
      ),
    ),
  )

  /**
   * {{{
   * Axiom "open invariant closure >".
   *   ([{c&q}]p>0 <-> [{c&q&p>=0}]p>0) <- p>=0
   * End.
   * }}}
   */
  @Derivation
  lazy val openInvariantClosure: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "openInvariantClosure", canonicalName = "open invariant closure >", key = "1.0", recursor = "*"),
    "==>([{c_{|t_|}&q_(|t_|)}]p_(|t_|)>0 <-> [{c_{|t_|}&q_(|t_|)&p_(|t_|)>=0}]p_(|t_|)>0) <- p_(|t_|)>=0".asSequent,
    implyR(1) &
      useAt(box, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(box, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(notGreater)(1, 0 :: 0 :: 1 :: Nil) &
      equivR(1) & OnAll(SaturateTactic(alphaRule)) < (
        useAt(leaveWithinClosed, PosInExpr(1 :: 0 :: Nil))(1) < (
          useAt(diamond, PosInExpr(1 :: Nil))(1) & useAt(diamond, PosInExpr(1 :: Nil))(-2) & SaturateTactic(alphaRule) &
            HilbertCalculus
              .DW(1) & generalize("!p_(|t_|)=0".asFormula)(1) < (id, useAt(greaterEqual)(1, 0 :: 1 :: Nil) & propClose),
          id
        ),
        useAt(leaveWithinClosed, PosInExpr(1 :: 0 :: Nil))(-2) < (
          useAt(diamond, PosInExpr(1 :: Nil))(1) & useAt(diamond, PosInExpr(1 :: Nil))(-2) & SaturateTactic(alphaRule) &
            generalize("!!p_(|t_|)>0".asFormula)(1) < (
              id, useAt(gtzImpNez)(-1, 0 :: 0 :: Nil) & useAt(notNotEqual)(-1, 0 :: Nil) & id
            ),
          id
        )
      ),
  )

  /**
   * {{{
   * Axiom "DCd diamond differential cut".
   *   (<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)
   *   // (<x'=f(x)&q(x); >p(x) <-> <x'=f(x)&(q(x)&r(x));>p(x)) <- [x'=f(x)&q(x);]r(x) THEORY
   * End.
   * }}}
   */
  @Derivation
  lazy val commaCommuted: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "commaCommuted", canonicalName = ",d commute"),
    Sequent(IndexedSeq(), IndexedSeq("<{c,d&q(||)}>p(||) <-> <{d,c&q(||)}>p(||)".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1) &
      byUS(commaCommute),
  )

  private val dbx_internal = Variable("y_", None, Real)

  /**
   * {{{
   * Axiom "DBX>".
   *   (e>0 -> [c&q(||)]e>0) <- [c&q(||)](e)'>=g*e
   * End.
   * }}}
   * Strict Darboux inequality / Grönwall inequality.
   *
   * @note
   *   More precisely: this derivation assumes that y_ does not occur, hence the more fancy space dependents.
   * @note
   *   For soundness, the cofactor g must not mention divisions that are not guarded by the ODE domain constraint (see
   *   DG).
   * @see
   *   André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
   * @see
   *   [[DBXgtOpen]]
   */
  @Derivation
  lazy val DBXgt: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DBXgt",
      canonicalName = "DBX>",
      displayName = Some("DBX>"),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "(e>0 → __[x'=f(x)&Q]e>0__) ← [x'=f(x)&Q](e)'≥ge",
      key = "1.1",
      recursor = "1.0",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "(e_(|y_|)>0 -> [{c{|y_|}&q(|y_|)}]e_(|y_|)>0) <- [{c{|y_|}&q(|y_|)}](e_(|y_|))'>=g(|y_|)*e_(|y_|)".asFormula
      ),
    ),
    implyR(1) & implyR(1) &
      dG(
        AtomicODE(
          DifferentialSymbol(dbx_internal),
          Times(Neg(Divide("g(|y_|)".asTerm, Number(BigDecimal(2)))), dbx_internal),
        ),
        None, /*Some("e_(|y_|)*y_^2>0".asFormula)*/
      )(1) &
      useAt(
        Ax.DGpp,
        (us: Option[Subst]) =>
          us.get ++ RenUSubst(
            // (Variable("y_",None,Real), dbx_internal) ::
            (
              UnitFunctional("a", Except(Variable("y_", None, Real) :: Nil), Real),
              Neg(Divide("g(|y_|)".asTerm, Number(BigDecimal(2)))),
            ) ::
              (UnitFunctional("b", Except(Variable("y_", None, Real) :: Nil), Real), Number(BigDecimal(0))) :: Nil
          ),
      )(-1) &
      // The following replicates functionality of existsR(Number(1))(1)
      // 1) Stutter
      cutLR("\\exists y_ [y_:=y_;][{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e_(|y_|)>0".asFormula)(1, 0 :: Nil) < (
        cutLR("[y_:=1;][{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e_(|y_|)>0".asFormula)(1) < (
          // 2) assignb
          useAt(assignbeqy)(1) &
            ProofRuleTactics.skolemizeR(1) & implyR(1),
          // 3) finish up
          cohide(1) & CMon(PosInExpr(Nil)) &
            byUS(
              existsGeneralizey,
              (_: Subst) =>
                RenUSubst(
                  ("f()".asTerm, Number(1)) :: (
                    "p_(.)".asFormula,
                    Box(
                      Assign("y_".asVariable, DotTerm()),
                      "[{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e_(|y_|)>0".asFormula,
                    ),
                  ) :: Nil
                ),
            )
        ),
        cohide(1) & equivifyR(1) & CE(PosInExpr(0 :: Nil)) & byUS(selfassignby) & done
      ) &
      useAt(ally, PosInExpr(0 :: Nil))(-1) & // allL/*(dbx_internal)*/(-1) &
      useAt(commaCommute)(-1) & // @note since DG inverse differential ghost has flipped order
      cutR("[{c{|y_|},y_'=(-(g(|y_|)/2))*y_+0&q(|y_|)}]e_(|y_|)*y_^2>0".asFormula)(1) < (
        useAt(DI)(1) & implyR(1) & andR(1) < (
          hideL(-4) & hideL(-1) & byUS(TactixLibrary.proveBy(
            Sequent(IndexedSeq("e_()>0".asFormula, "y()=1".asFormula), IndexedSeq("e_()*y()^2>0".asFormula)),
            QE & done,
          )),
          derive(1, PosInExpr(1 :: Nil)) &
            useAt(commaCommute)(1) & useAt(DEsysy)(1) &
            useAt(Dassignby, PosInExpr(0 :: Nil))(1, PosInExpr(1 :: Nil)) &
            cohide2(-1, 1) & HilbertCalculus.monb &
            // DebuggingTactics.print("DI finished") &
            byUS(TactixLibrary.proveBy(
              Sequent(
                IndexedSeq("ep()>=g()*e_()".asFormula),
                IndexedSeq("ep()*y()^2 + e_()*(2*y()^(2-1)*((-g()/2)*y()+0))>=0".asFormula),
              ),
              QE & done,
            ))
        ),
        implyR(1) &
          // DebuggingTactics.print("new post") &
          cohide2(-4, 1) & HilbertCalculus.monb & byUS(
            TactixLibrary
              .proveBy(Sequent(IndexedSeq("e_()*y()^2>0".asFormula), IndexedSeq("e_()>0".asFormula)), QE & done)
          )
      ),
  )

  /**
   * {{{
   * Axiom "DBX> open".
   *   (e>0 -> [c&q(||)]e>0) <- [c&q(||)](e>0 -> (e)'>=g*e)
   * End.
   * }}}
   * Strict Darboux inequality / Grönwall inequality benefiting from open inequality in postcondition.
   *
   * @note
   *   More precisely: this derivation assumes that y_ does not occur, hence the more fancy space dependents.
   * @note
   *   For soundness, the cofactor g must not mention divisions that are not guarded by the ODE domain constraint (see
   *   DG)
   * @see
   *   André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
   * @see
   *   [[DBXgt]]
   */
  @Derivation
  lazy val DBXgtOpen: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DBXgtOpen",
      canonicalName = "DBX> open",
      displayName = Some("DBX> open"),
      displayConclusion = "(e_>0 → __[x'=f(x)&Q]e_>0__) ← [x'=f(x)&Q](e_>0→(e_)'≥ge)",
      key = "1.1",
      recursor = "1.1.0",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "(e_(|y_|)>0 -> [{c{|y_|}&q(|y_|)}]e_(|y_|)>0) <- [{c{|y_|}&q(|y_|)}](e_(|y_|) > 0 -> (e_(|y_|)'>=g(|y_|)*e_(|y_|)))"
          .asFormula
      ),
    ),
    implyR(1) & implyR(1) &
      dG(
        AtomicODE(
          DifferentialSymbol(dbx_internal),
          Times(Neg(Divide("g(|y_|)".asTerm, Number(BigDecimal(2)))), dbx_internal),
        ),
        None, /*Some("e_(|y_|)*y_^2>0".asFormula)*/
      )(1) &
      useAt(
        Ax.DGpp,
        (us: Option[Subst]) =>
          us.get ++ RenUSubst(
            // (Variable("y_",None,Real), dbx_internal) ::
            (
              UnitFunctional("a", Except(Variable("y_", None, Real) :: Nil), Real),
              Neg(Divide("g(|y_|)".asTerm, Number(BigDecimal(2)))),
            ) ::
              (UnitFunctional("b", Except(Variable("y_", None, Real) :: Nil), Real), Number(BigDecimal(0))) :: Nil
          ),
      )(-1) &
      // The following replicates functionality of existsR(Number(1))(1)
      // 1) Stutter
      cutLR("\\exists y_ [y_:=y_;][{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e_(|y_|)>0".asFormula)(1, 0 :: Nil) < (
        cutLR("[y_:=1;][{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e_(|y_|)>0".asFormula)(1) < (
          // 2) assignb
          useAt(assignbeqy)(1) &
            ProofRuleTactics.skolemizeR(1) & implyR(1),
          // 3) finish up
          cohide(1) & CMon(PosInExpr(Nil)) &
            byUS(
              existsGeneralizey,
              (_: Subst) =>
                RenUSubst(
                  ("f()".asTerm, Number(1)) :: (
                    "p_(.)".asFormula,
                    Box(
                      Assign("y_".asVariable, DotTerm()),
                      "[{c{|y_|},y_'=(-g(|y_|)/2)*y_+0&q(|y_|)}]e_(|y_|)>0".asFormula,
                    ),
                  ) :: Nil
                ),
            )
        ),
        cohide(1) & equivifyR(1) & CE(PosInExpr(0 :: Nil)) & byUS(selfassignby) & done
      ) &
      useAt(ally, PosInExpr(0 :: Nil))(-1) & // allL/*(dbx_internal)*/(-1) &
      useAt(commaCommute)(-1) & // @note since DG inverse differential ghost has flipped order
      cutR("[{c{|y_|},y_'=(-(g(|y_|)/2))*y_+0&q(|y_|)}]e_(|y_|)*y_^2>0".asFormula)(1) < (
        useAt(DIogreater)(1) < (
          HilbertCalculus.testb(1) & implyR(1) & hideL(-4) & hideL(-1) & byUS(TactixLibrary.proveBy(
            Sequent(IndexedSeq("e_()>0".asFormula, "y()=1".asFormula), IndexedSeq("e_()*y()^2>0".asFormula)),
            QE & done,
          )),
          implyR(1) & hideL(-4) &
            derive(1, PosInExpr(1 :: 1 :: Nil)) &
            useAt(commaCommute)(1) & useAt(DEsysy)(1) &
            useAt(Dassignby, PosInExpr(0 :: Nil))(1, PosInExpr(1 :: Nil)) &
            cohide2(-1, 1) & HilbertCalculus.monb &
            // DebuggingTactics.print("DI finished") &
            byUS(TactixLibrary.proveBy(
              Sequent(
                IndexedSeq("e_() > 0 -> ep()>=g()*e_()".asFormula),
                IndexedSeq("e_()*y()^2 >0 -> ep()*y()^2 + e_()*(2*y()^(2-1)*((-g()/2)*y()+0))>=0".asFormula),
              ),
              QE & done,
            ))
        ),
        implyR(1) &
          // DebuggingTactics.print("new post") &
          cohide2(-4, 1) & HilbertCalculus.monb & byUS(
            TactixLibrary
              .proveBy(Sequent(IndexedSeq("e_()*y()^2>0".asFormula), IndexedSeq("e_()>0".asFormula)), QE & done)
          )
      ),
  )

  private val assignbexistsy = Ax.assignbexists.provable(URename("x_".asVariable, dbx_internal, semantic = true))
  private val DBXgtz = Ax.DBXgt.provable(URename(dbx_internal, "z_".asVariable, semantic = true))

  /**
   * {{{
   * Axiom "DBX>=".
   *   (e>=0 -> [c&q(||)]e>=0) <- [c&q(||)](e)'>=g*e
   * End.
   * }}}
   * Non-strict Darboux inequality / Grönwall inequality.
   *
   * @note
   *   More precisely: this derivation assumes that y_,z_ do not occur, hence the more fancy space dependents.
   * @note
   *   For soundness, the cofactor g must not mention divisions that are not guarded by the ODE domain constraint (see
   *   DG)
   * @see
   *   André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
   * @see
   *   [[DBXgt]]
   */
  @Derivation
  lazy val DBXge: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DBXge",
      canonicalName = "DBX>=",
      displayName = Some("DBX>="),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "(e>=0 → __[x'=f(x)&Q]e>=0__) ← [x'=f(x)&Q](e)'≥ge",
      key = "1.1",
      recursor = "1.0",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "(e_(|y_,z_|)>=0 -> [{c{|y_,z_|}&q(|y_,z_|)}]e_(|y_,z_|)>=0) <- [{c{|y_,z_|}&q(|y_,z_|)}](e_(|y_,z_|))'>=g(|y_,z_|)*e_(|y_,z_|)"
          .asFormula
      ),
    ),
    implyR(1) & implyR(1) &
      dG(
        AtomicODE(
          DifferentialSymbol(dbx_internal),
          Times(Neg(Divide("g(|y_,z_|)".asTerm, Number(BigDecimal(2)))), dbx_internal),
        ),
        None,
      )(1) &
      useAt(
        Ax.DGpp,
        (us: Option[Subst]) =>
          us.get ++ RenUSubst(
            (
              UnitFunctional("a", Except(Variable("y_", None, Real) :: Nil), Real),
              Neg(Divide("g(|y_,z_|)".asTerm, Number(BigDecimal(2)))),
            ) ::
              (UnitFunctional("b", Except(Variable("y_", None, Real) :: Nil), Real), Number(BigDecimal(0))) :: Nil
          ),
      )(-1) &
      cutR("\\exists y_ y_>0".asFormula)(1) < (cohideR(1) & QE, implyR(1) & existsL(Symbol("Llast"))) &
      useAt(
        assignbexistsy,
        PosInExpr(1 :: Nil),
        (us: Option[Subst]) => us.get ++ RenUSubst(("f_()".asTerm, dbx_internal) :: Nil),
      )(1) &
      useAt(selfassignby)(1) &
      useAt(ally, PosInExpr(0 :: Nil))(-1) & // allL/*(dbx_internal)*/(-1) &
      useAt(commaCommute)(-1) &
      cutR("[{c{|y_,z_|},y_'=(-(g(|y_,z_|)/2))*y_+0&q(|y_,z_|)}](e_(|y_,z_|)*y_^2>=0 & y_ > 0)".asFormula)(1) < (
        TactixLibrary.boxAnd(1) & andR(1) < (
          useAt(DI)(1) & implyR(1) & andR(1) < (
            hideL(-4) & hideL(-1) &
              byUS(TactixLibrary.proveBy(
                Sequent(IndexedSeq("e_()>=0".asFormula, "y()>0".asFormula), IndexedSeq("e_()*y()^2>=0".asFormula)),
                QE & done,
              )),
            derive(1, PosInExpr(1 :: Nil)) &
              useAt(commaCommute)(1) & useAt(DEsysy)(1) &
              useAt(Dassignby, PosInExpr(0 :: Nil))(1, PosInExpr(1 :: Nil)) &
              cohide2(-1, 1) & HilbertCalculus.monb &
              byUS(TactixLibrary.proveBy(
                Sequent(
                  IndexedSeq("ep()>=g()*e_()".asFormula),
                  IndexedSeq("ep()*y()^2 + e_()*(2*y()^(2-1)*((-g()/2)*y()+0))>=0".asFormula),
                ),
                QE & done,
              ))
          ),
          cohideOnlyL(Symbol("Llast")) &
            implyRi &
            useAt(
              DBXgtz,
              PosInExpr(1 :: Nil),
              (us: Option[Subst]) => us.get ++ RenUSubst(("g(|z_|)".asTerm, "(-g(|y_,z_|)/2)".asTerm) :: Nil),
            )(1) &
            derive(1, PosInExpr(1 :: 0 :: Nil)) &
            useAt(commaCommute)(1) & useAt(DEsysy)(1) &
            G(1) & useAt(Dassignby, PosInExpr(0 :: Nil))(1) &
            byUS(TactixLibrary.proveBy("f()+0>=f()".asFormula, QE & done))
        ),
        cohideR(1) & implyR(1) &
          HilbertCalculus.monb &
          byUS(TactixLibrary.proveBy(
            Sequent(IndexedSeq("e_()*y()^2>=0 & y() > 0".asFormula), IndexedSeq("e_()>=0".asFormula)),
            QE & done,
          ))
      ),
  )

  // Some extra versions of the dbx axioms for use in implementations

  private lazy val dbxEqArith = proveBy("f_() = 0 <-> f_()>=0 & -f_()>=0".asFormula, QE)

  /**
   * {{{
   * Axiom "DBX=".
   *   (e=0 -> [c&q(||)]e=0) <- [c&q(||)](e)'=g*e
   * End.
   * }}}
   * Darboux equality
   *
   * @note
   *   More precisely: this derivation assumes that y_,z_ do not occur, hence the more fancy space dependents.
   * @note
   *   For soundness, the cofactor g must not mention divisions that are not guarded by the ODE domain constraint (see
   *   DG)
   * @see
   *   André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
   * @see
   *   [[DBXge]]
   */
  @Derivation
  lazy val DBXeq: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DBXeq",
      canonicalName = "DBX=",
      displayName = Some("DBX="),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "(e=0 → __[x'=f(x)&Q]e=0__) ← [x'=f(x)&Q](e)'=ge",
      key = "1.1",
      recursor = "1.0",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "(e_(|y_,z_|)=0 -> [{c{|y_,z_|}&q(|y_,z_|)}]e_(|y_,z_|)=0) <- [{c{|y_,z_|}&q(|y_,z_|)}](e_(|y_,z_|))'=g(|y_,z_|)*e_(|y_,z_|)"
          .asFormula
      ),
    ),
    implyR(1) & implyR(1) &
      useAt(dbxEqArith)(Symbol("Llast")) & andL(Symbol("Llast")) &
      useAt(dbxEqArith)(1, PosInExpr(1 :: Nil)) &
      TactixLibrary.boxAnd(1) & andR(1) < (
        hideL(-3) & exchangeL(-1, -2) & implyRi &
          useAt(Ax.DBXge, PosInExpr(1 :: Nil))(1) & monb &
          byUS(TactixLibrary.proveBy("f()=g() ==> f()>=g()".asSequent, QE & done)),
        hideL(-2) & exchangeL(-1, -2) & implyRi &
          useAt(Ax.DBXge, PosInExpr(1 :: Nil))(1) & monb &
          derive(1, 0 :: Nil) &
          byUS(TactixLibrary.proveBy("f()=g()*h() ==> -f()>=g()*(-h())".asSequent, QE & done))
      ),
  )

  private lazy val dbxLtArith = proveBy("f_() < 0 <-> -f_()>0".asFormula, QE)

  /**
   * {{{
   * Axiom "DBX> open".
   *   (e>0 -> [c&q(||)]e>0) <- [c&q(||)](e>0 -> (e)'>=g*e)
   * End.
   * }}}
   * Strict Darboux inequality / Grönwall inequality benefiting from open inequality in postcondition.
   *
   * @note
   *   More precisely: this derivation assumes that y_ does not occur, hence the more fancy space dependents.
   * @note
   *   For soundness, the cofactor g must not mention divisions that are not guarded by the ODE domain constraint (see
   *   DG)
   * @see
   *   André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
   * @see
   *   [[DBXgt]]
   */
  @Derivation
  lazy val DBXltOpen: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DBXltOpen",
      canonicalName = "DBX< open",
      displayName = Some("DBX< open"),
      displayConclusion = "(e<0 → __[x'=f(x)&Q]e<0__) ← [x'=f(x)&Q](e<0→(e)'<=ge)",
      key = "1.1",
      recursor = "1.1.0",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "(e_(|y_|)<0 -> [{c{|y_|}&q(|y_|)}]e_(|y_|)<0) <- [{c{|y_|}&q(|y_|)}](e_(|y_|) < 0 -> (e_(|y_|)'<=g(|y_|)*e_(|y_|)))"
          .asFormula
      ),
    ),
    implyR(1) &
      useAt(dbxLtArith)(1, 0 :: Nil) &
      useAt(dbxLtArith)(1, 1 :: 1 :: Nil) &
      useAt(Ax.DBXgtOpen, PosInExpr(1 :: Nil))(1) &
      monb &
      derive(1, 1 :: 0 :: Nil) &
      byUS(TactixLibrary.proveBy("e_() < 0->f()<=g()*h() ==> -e_()>0 -> -f()>=g()*(-h())".asSequent, QE & done)),
  )

  private lazy val dbxLeArith = proveBy("f_() <= 0 <-> -f_()>=0".asFormula, QE)

  /**
   * {{{
   * Axiom "DBX<=".
   *   (e<=0 -> [c&q(||)]e<=0) <- [c&q(||)](e)'<=g*e
   * End.
   * }}}
   * Non-strict Darboux inequality / Grönwall inequality.
   *
   * @note
   *   More precisely: this derivation assumes that y_,z_ do not occur, hence the more fancy space dependents.
   * @note
   *   For soundness, the cofactor g must not mention divisions that are not guarded by the ODE domain constraint (see
   *   DG)
   * @see
   *   André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
   * @see
   *   [[DBXgt]]
   */
  @Derivation
  lazy val DBXle: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DBXle",
      canonicalName = "DBX<=",
      displayName = Some("DBX<="),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "(e<=0 → __[x'=f(x)&Q]e<=0__) ← [x'=f(x)&Q](e)'<=ge",
      key = "1.1",
      recursor = "1.0",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "(e_(|y_,z_|)<=0 -> [{c{|y_,z_|}&q(|y_,z_|)}]e_(|y_,z_|)<=0) <- [{c{|y_,z_|}&q(|y_,z_|)}](e_(|y_,z_|))'<=g(|y_,z_|)*e_(|y_,z_|)"
          .asFormula
      ),
    ),
    implyR(1) &
      useAt(dbxLeArith)(1, 0 :: Nil) &
      useAt(dbxLeArith)(1, 1 :: 1 :: Nil) &
      useAt(DBXge, PosInExpr(1 :: Nil))(1) &
      monb &
      derive(1, 0 :: Nil) &
      byUS(TactixLibrary.proveBy("f()<=g()*h() ==> -f()>=g()*(-h())".asSequent, QE & done)),
  )

  private lazy val dbxNeArith = proveBy("f_() != 0 <-> f_()>0 | -f_()>0".asFormula, QE)

  /**
   * {{{
   * Axiom "DBX!= open".
   *   (e!=0 -> [c&q(||)]e!=0) <- [c&q(||)](e!=0 -> (e)'=g*e)
   * End.
   * }}}
   * Strict Darboux != benefiting from open inequality in postcondition.
   *
   * @note
   *   More precisely: this derivation assumes that y_ does not occur, hence the more fancy space dependents.
   * @note
   *   For soundness, the cofactor g must not mention divisions that are not guarded by the ODE domain constraint (see
   *   DG)
   * @see
   *   André Platzer and Yong Kiam Tan. Differential Equation Invariance Axiomatization. arXiv:1905.13429, May 2019.
   * @see
   *   [[DBXgt]]
   */
  @Derivation
  lazy val DBXneOpen: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DBXneOpen",
      canonicalName = "DBX!= open",
      displayName = Some("DBX!= open"),
      displayConclusion = "(e!=0 → __[x'=f(x)&Q]e!=0__) ← [x'=f(x)&Q](e!=0→(e)'=ge)",
      key = "1.1",
      recursor = "1.1.0",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "(e_(|y_|)!=0 -> [{c{|y_|}&q(|y_|)}]e_(|y_|)!=0) <- [{c{|y_|}&q(|y_|)}](e_(|y_|) != 0 -> (e_(|y_|)'=g(|y_|)*e_(|y_|)))"
          .asFormula
      ),
    ),
    implyR(1) &
      useAt(dbxNeArith)(1, 0 :: Nil) &
      useAt(dbxNeArith)(1, 1 :: 1 :: Nil) &
      implyR(1) & orL(Symbol("Llast")) < (
        useAt(Ax.boxOrLeft)(1) & exchangeL(-1, -2) & implyRi &
          useAt(Ax.DBXgtOpen, PosInExpr(1 :: Nil))(1) & monb &
          byUS(TactixLibrary.proveBy("e_() != 0->f()=g() ==> e_()>0 -> f()>=g()".asSequent, QE & done)),
        useAt(Ax.boxOrRight)(1) & exchangeL(-1, -2) & implyRi &
          useAt(Ax.DBXgtOpen, PosInExpr(1 :: Nil))(1) & monb &
          derive(1, 1 :: 0 :: Nil) &
          byUS(TactixLibrary.proveBy("e_() != 0->f()=g()*h() ==> -e_()>0 -> -f()>=g()*(-h())".asSequent, QE & done))
      ),
  )

  /** Dual version of initial-value theorem. */
  @Derivation
  lazy val dualIVT: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "dualIVT", canonicalName = "dualIVT", key = "1", unifier = Unifier.Linear),
    "[{c&q(||)}](f(||)>=z()->p(||)) <- (f(||)<=z() & [{c&q(||)}](f(||)=z()->[{c&q(||)}](f(||)>=z()->p(||))))".asFormula,
    implyR(1) & andL(-1) & useAt(box, PosInExpr(1 :: Nil))(-2) & useAt(box, PosInExpr(1 :: Nil))(1) &
      notL(-2) & notR(1) & useAt(notImply, PosInExpr(0 :: Nil))(-2, 1 :: Nil) &
      useAt(notImply, PosInExpr(0 :: Nil))(1, 1 :: Nil) &
      useAt(geNormalize)(-2, 1 :: 0 :: Nil) &
      useAt(IVT, PosInExpr(0 :: Nil))(-2) & implyL(-2) &
      Idioms.<(
        useAt(metricLe)(-1) & id,
        useAt(box, PosInExpr(1 :: Nil))(1, 1 :: 1 :: 0 :: Nil) &
          useAt(doubleNegation, PosInExpr(0 :: Nil))(1, 1 :: 1 :: Nil) &
          useAt(notImply, PosInExpr(0 :: Nil))(1, 1 :: 1 :: 1 :: Nil) &
          useAt(eqNormalize)(1, 1 :: 0 :: Nil) &
          useAt(geNormalize)(1, 1 :: 1 :: 1 :: 0 :: Nil) &
          id,
      ),
  )

  @Derivation
  lazy val oneGeZero: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "oneGeZero", canonicalName = "oneGeZero"),
    "1>=0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val timeCond: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timeCond", canonicalName = "timeCond"),
    "[{x_'=1, c{|x_|} & q(||)}](!x_ <= h() -> [{x_'=1, c{|x_|} & q(||)}](!x_ <= h()))".asFormula,
    generalize(True)(1) & Idioms.<(
      useAt(boxTrueAxiom)(1),
      implyR(1) & useAt(Ax.notLessEqual, PosInExpr(0 :: Nil))(-2) &
        useAt(Ax.notLessEqual, PosInExpr(0 :: Nil))(1, 1 :: Nil),
    ) &
      useAt(DI)(1) & implyR(1) & andR(1) & Idioms.<(
        id,
        derive(1, 1 :: Nil) &
          cohideR(1) & useAt(Ax.DEs, PosInExpr(0 :: Nil))(1) &
          generalize(True)(1) & Idioms
            .<(cohideR(1) & useAt(boxTrueAxiom)(1), useAt(Dassignb)(1) & cohideR(1) & by(oneGeZero)),
      ),
  )

  @Derivation
  lazy val timeStep: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timeStep", canonicalName = "timeStep", key = "1", unifier = Unifier.Linear),
    "[{x_'=1,c{|x_|}&q(||)}]p(||) <- (x_ <= h() & [{x_'=1,c{|x_|}&q(||)&x_<=h()}](p(||) & (x_=h()->[{x_'=1,c{|x_|}&q(||)&x_>=h()}]p(||))))"
      .asFormula,
    implyR(1) & andL(-1) &
      cutR("[{x_'=1, c{|x_|} & q(||)}]((x_>=h()->p(||))&(x_<=h()->p(||)))".asFormula)(1) &
      Idioms.<(
        useAt(boxAnd)(1) & andR(1) &
          Idioms.<(
            useAt(Ax.dualIVT, PosInExpr(1 :: Nil))(1) & andR(1) &
              Idioms.<(
                id,
                useAt(boxAnd)(-2) & andL(-2) & hideL(-2) &
                  cutR(
                    "[{x_'=1, c{|x_|} & q(||)}](x_ <= h() -> x_ = h() -> [{x_'=1, c{|x_|} & q(||)}](x_ >= h() -> p(||)))"
                      .asFormula
                  )(1) &
                  Idioms.<(
                    useAt(Ax.DCC, PosInExpr(1 :: Nil))(1) & andR(1) & Idioms.<(
                      DLBySubst.boxElim(1) & prop & useAt(Ax.DCC, PosInExpr(1 :: Nil))(1) & andR(1) &
                        Idioms.<(
                          id,
                          hideL(-1) & HilbertCalculus.DC("x_>=h()".asFormula)(1) &
                            Idioms.<(
                              useAt(DW)(1) & generalize(True)(1) & Idioms
                                .<(cohideR(1) & useAt(boxTrueAxiom)(1), prop & done),
                              useAt(DI)(1) & implyR(1) & andR(1) & Idioms.<(
                                hideL(-2) & useAt(Ax.equalExpand, PosInExpr(0 :: Nil))(-1) & andL(-1) &
                                  useAt(Ax.flipLessEqual, PosInExpr(0 :: Nil))(-2) & id & done,
                                useAt(Ax.DEs, PosInExpr(0 :: Nil))(1) &
                                  generalize(True)(1) &
                                  Idioms.<(
                                    cohideR(1) & useAt(boxTrueAxiom)(1),
                                    derive(1, 1 :: Nil) & useAt(Dassignb)(1) & cohideR(1) & by(oneGeZero),
                                  ),
                              ),
                            ),
                        ),
                      prop & cohideR(1) & by(timeCond),
                    ),
                    cohideR(1) & implyR(1) & DLBySubst.boxElim(1) & implyR(1) & implyL(-1) &
                      Idioms.<(hideR(1) & useAt(Ax.equalExpand, PosInExpr(0 :: Nil))(-1) & andL(-1) & id, prop & done),
                  ),
              ),
            useAt(boxAnd)(-2) & andL(-2) &
              useAt(Ax.DCC, PosInExpr(1 :: Nil))(1) & andR(1) & Idioms
                .<(DLBySubst.boxElim(1) & id, cohideR(1) & by(timeCond)),
          ),
        cohideR(1) & implyR(1) & DLBySubst.boxElim(1) & andL(-1) & cutR("x_>=h() | x_<=h()".asFormula)(1) &
          Idioms.<(
            cohideR(1) & useAt(Ax.flipLessEqual, PosInExpr(1 :: Nil))(1, 0 :: Nil) & byUS(Ax.lessEqualTotal),
            prop & done,
          ),
      ),
  )

  /**
   * {{{
   *   Axiom "[d] dual".
   *    [{a;}^@]p(||) <-> ![a;]!p(||)
   *   End.
   * }}}
   * @derived
   */
  @Derivation
  lazy val dualb: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "dualb",
      canonicalName = "[d] dual",
      displayName = Some("[d]"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "__[a<sup>d</sup>]P__↔¬[a]¬P",
      key = "0",
      recursor = "0",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[{a;}^@]p(||) <-> ![a;]!p(||)".asFormula)),
    useExpansionAt(box)(1, 0 :: Nil) &
      useAt(duald)(1, 0 :: 0 :: Nil) &
      useAt(box)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  /**
   * {{{
   *   Axiom "[d] dual direct".
   *    [{a;}^@]p(||) <-> <a;>p(||)
   *   End.
   * }}}
   * @derived
   */
  @Derivation
  lazy val dualDirectb: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "dualDirectb",
      canonicalName = "[d] dual direct",
      displayName = Some("[d]"),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "__[a<sup>d</sup>]P__↔&langle;a&rangle;P",
      key = "0",
      recursor = ".",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("[{a;}^@]p(||) <-> <a;>p(||)".asFormula)),
    useExpansionAt(diamond)(1, 1 :: Nil) &
      byUS(dualb),
  )

  /**
   * {{{
   *   Axiom "<d> dual direct".
   *    <{a;}^@>p(||) <-> [a;]p(||)
   *   End.
   * }}}
   * @derived
   */
  @Derivation
  lazy val dualDirectd: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "dualDirectd",
      canonicalName = "<d> dual direct",
      displayName = Some("<d>"),
      displayConclusion = "__&langle;a<sup>d</sup>&rangle;P__↔[a]P",
      key = "0",
      recursor = ".",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("<{a;}^@>p(||) <-> [a;]p(||)".asFormula)),
    useExpansionAt(box)(1, 1 :: Nil) &
      // useAt(box, AxIndex.axiomIndex(box)._1.sibling)(1, 1::Nil) &
      byUS(duald),
  )

  // differentials

  /**
   * {{{
   * Axiom "x' derive var commuted".
   *   (x_') = (x_)'
   * End.
   * }}}
   */
  @Derivation
  lazy val DvariableCommutedAxiom: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DvariableCommutedAxiom",
      canonicalName = "x' derive var commuted",
      displayName = Some("x',C"),
      displayConclusion = "x'=__(x)'__",
      unifier = Unifier.Linear,
      key = "0",
      recursor = "",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(x_') = (x_)'".asFormula)),
    useAt(equalCommute)(1) &
      byUS(DvarAxiom),
  )

  /**
   * {{{
   * Axiom "x' derive variable".
   *   \forall x_ ((x_)' = x_')
   * End.
   * }}}
   */
  @Derivation
  lazy val DvariableAxiom: DerivedAxiomInfo = derivedFact(
    DerivedAxiomInfo.create(
      name = "DvariableAxiom",
      canonicalName = "x' derive variable",
      displayName = Some("x'"),
      displayConclusion = "__(x)'__=x'",
    ),
    DerivedAxiomProvableSig.startProof(
      Sequent(IndexedSeq(), IndexedSeq("\\forall x_ ((x_)' = x_')".asFormula)),
      Declaration(Map.empty),
    )(Skolemize(SuccPos(0)), 0)(DerivedAxiomProvableSig.axioms("x' derive var"), 0),
  )
  //  /**
  //   * {{{Axiom "x' derive var".
  //   *    (x_)' = x_'
  //   * End.
  //   * }}}
  //   * @todo derive
  //   */
  //  lazy val DvarF = "((x_)' = x_')".asFormula
  //  lazy val Dvar = derivedAxiom("'x derive var",
  //    Provable.startProof(Sequent(IndexedSeq(), IndexedSeq(DvarF)))
  //      (CutRight("\\forall x_ ((x_)' = x_')".asFormula, SuccPos(0)), 0)
  //      // right branch
  //      (UniformSubstitutionRule.UniformSubstitutionRuleForward(Axiom.axiom("all eliminate"),
  //        USubst(SubstitutionPair(PredOf(Function("p_",None,Real,Bool),Anything), DvarF)::Nil)), 0)
  //      // left branch
  //      (Axiom.axiom("x' derive variable"), 0)
  //    /*TacticLibrary.instantiateQuanT(Variable("x_",None,Real), Variable("x",None,Real))(1) &
  //      byUS(Ax.equalReflexive)*/
  //  )
  //  lazy val DvarT = TactixLibrary.byUS(Dvar)
  /**
   * {{{
   * Axiom "' linear".
   *   (c()*f(||))' = c()*(f(||))'
   * End.
   * }}}
   */
  // @todo unifier = "full" for better error handling because of c?
  @Derivation
  lazy val Dlinear: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "Dlinear",
      canonicalName = "' linear",
      displayName = Some("l'"),
      unifier = Unifier.Linear,
      key = "0",
      recursor = "1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(c_()*f_(||))' = c_()*(f_(||))'".asFormula)),
    useAt(Dtimes)(1, 0 :: Nil) &
      useAt(Dconst)(1, 0 :: 0 :: 0 :: Nil) &
      useAt(zeroTimes)(1, 0 :: 0 :: Nil) &
      useAt(zeroPlus)(1, 0 :: Nil) &
      byUS(equalReflexive),
  )

  /**
   * {{{
   * Axiom "' linear right".
   *   (f(||)*c())' = f(||)'*c()
   * End.
   * }}}
   */
  @Derivation
  lazy val DlinearRight: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "DlinearRight",
      canonicalName = "' linear right",
      displayName = Some("l'"),
      key = "0",
      recursor = "0",
      unifier = Unifier.SurjectiveLinearPretend,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f(||)*c())' = (f(||))'*c()".asFormula)),
    useAt(Dtimes)(1, 0 :: Nil) &
      useAt(Dconst)(1, 0 :: 1 :: 1 :: Nil) &
      useAt(timesZero)(1, 0 :: 1 :: Nil) &
      useAt(plusZero)(1, 0 :: Nil) &
      byUS(equalReflexive),
  )
  // @note elegant proof that clashes for some reason
  //  derivedAxiom("' linear right",
  //  Sequent(IndexedSeq(), IndexedSeq(DlinearRightF)),
  //  useAt("* commute")(1, 0::0::Nil) &
  //    useAt("* commute")(1, 1::Nil) &
  //    by(Dlinear)
  // )

  /**
   * {{{
   * Axiom "Uniq uniqueness iff"
   *   <{c&q(||)}>p(||) & <{c&r(||)}>p(||) <-> <{c & q(||)&r(||)}>(p(||))
   * End.
   * }}}
   */
  @Derivation
  lazy val UniqIff: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "UniqIff",
      canonicalName = "Uniq uniqueness iff",
      displayName = Some("Uniq"),
      displayConclusion = "<x'=f(x)&Q}>P ∧ <x'=f(x)&R>P ↔ __<x'=f(x)&Q∧R>P__",
      key = "1",
      recursor = "0;1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "<{c&q(||)}>p(||) & <{c&r(||)}>p(||) <-> <{c&q(||) & r(||)}>p(||)".asFormula,
    equivR(1) < (
      implyRi & byUS(Uniq),
      andR(1) < (
        dR("q(||)&r(||)".asFormula)(1) < (id, HilbertCalculus.DW(1) & G(1) & prop),
        dR("q(||)&r(||)".asFormula)(1) < (id, HilbertCalculus.DW(1) & G(1) & prop)
      )
    ),
  )

  // real arithmetic

  /**
   * {{{
   * Axiom "= reflexive".
   *   s() = s()
   * End.
   * }}}
   *
   * @see
   *   [[equivReflexive]]
   */
  @Derivation
  lazy val equalReflexive: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "equalReflexive",
      canonicalName = "= reflexive",
      displayName = Some("=R"),
      displayConclusion = "s=s",
      unifier = Unifier.Full,
      key = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("s_() = s_()".asFormula)),
    allInstantiateInverse(("s_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x x=x".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "= commute".
   *   (f()=g()) <-> (g()=f())
   * End.
   * }}}
   */
  @Derivation
  lazy val equalCommute: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "equalCommute",
      canonicalName = "= commute",
      displayName = Some("=C"),
      displayConclusion = "__f=g__ ↔ g=f",
      key = "0",
      recursor = "*",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f_()=g_()) <-> (g_()=f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x=y <-> y=x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom ">= reflexive".
   *    s() >= s()
   * End.
   * }}}
   */
  @Derivation
  lazy val greaterEqualReflexive: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "greaterEqualReflexive",
      canonicalName = ">= reflexive",
      displayName = Some(">=R"),
      unifier = Unifier.Full,
      key = "",
      recursor = "",
    ),
    Sequent(IndexedSeq(), IndexedSeq("s_() >= s_()".asFormula)),
    QE & done,
  )

//  /**
//    * {{{Axiom "-2- neg to minus".
//    *   (-f()) = (0 - f())
//    * End.
//    * }}}
//    * @see zeroMinus
//    */
//  @Axiom("-2-", unifier = "linear")
//  lazy val neg2Minus: DerivedAxiomInfo = derivedAxiom("-2- neg to minus", Sequent(IndexedSeq(), IndexedSeq("(-f_()) = (0 - f_())".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
//      byUS(proveBy("\\forall y \\forall x ((-x) = (0-x))".asFormula, TactixLibrary.RCF))
//  )
//
//  /**
//    * {{{Axiom "-2+ minus to plus".
//    *   (f()-g()) = (f() + (-1)*g())
//    * End.
//    * }}}
//    */
//  @Axiom("-2+", unifier = "linear")
//  lazy val minus2Plus: DerivedAxiomInfo = derivedAxiom("-2+ minus to plus", Sequent(IndexedSeq(), IndexedSeq("(f_()-g_()) = (f_() + (-1)*g_())".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//      byUS(proveBy("\\forall y \\forall x ((x-y) = (x+(-1)*y))".asFormula, TactixLibrary.RCF))
//  )
//
  /**
   * {{{
   * Axiom "<=".
   *   (f()<=g()) <-> ((f()<g()) | (f()=g()))
   * End.
   * }}}
   */
  @Derivation
  lazy val lessEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "lessEqual", canonicalName = "<=", displayName = Some("<="), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("(f_()<=g_()) <-> ((f_()<g_()) | (f_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x<=y <-> (x<y | x=y))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom ">=".
   *   (f()>=g()) <-> ((f()>g()) | (f()=g()))
   * End.
   * }}}
   */
  @Derivation
  lazy val greaterEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "greaterEqual", canonicalName = ">=", displayName = Some(">="), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("(f_()>=g_()) <-> ((f_()>g_()) | (f_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x>=y <-> (x>y | x=y))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "! !=".
   *   (!(f() != g())) <-> (f() = g())
   * End.
   * }}}
   */
  @Derivation
  lazy val notNotEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notNotEqual",
      canonicalName = "! !=",
      displayName = Some("¬≠"),
      displayNameAscii = Some("!!="),
      displayConclusion = "__(¬(f≠g)__↔(f=g))",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(f_() != g_())) <-> (f_() = g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x ((!(x != y)) <-> (x = y))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "! =".
   *   !(f() = g()) <-> f() != g()
   * End.
   * }}}
   */
  @Derivation
  lazy val notEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notEqual",
      canonicalName = "! =",
      displayName = Some("¬ ="),
      displayNameAscii = Some("! ="),
      displayConclusion = "__(¬(f=g))__↔(f≠g)",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(f_() = g_())) <-> (f_() != g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x ((!(x = y)) <-> (x != y))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "!= to or".
   *   (f() != g()) <-> f() < g() | f() > g()
   * End.
   * }}}
   */
  @Derivation
  lazy val notEqual2Or: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notEqual2Or",
      canonicalName = "!=2|",
      displayName = Some("≠2∨"),
      displayNameAscii = Some("!=2|"),
      displayLevel = DisplayLevel.Browse,
      displayConclusion = "__(f≠g)__ ↔ f<g ∨ f>g",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f_() != g_()) <-> f_() < g_() | f_() > g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x != y <-> x<y | x>y)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "!= to or".
   *   (f() = g()) <-> f() <= g() & f() >= g()
   * End.
   * }}}
   */
  @Derivation
  lazy val equal2And: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "equal2And",
      canonicalName = "=2&",
      displayName = Some("=2∧"),
      displayNameAscii = Some("=2&"),
      displayLevel = DisplayLevel.Browse,
      displayConclusion = "__(f≠g)__ ↔ f<g ∨ f>g",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f_() = g_()) <-> f_() <= g_() & f_() >= g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x = y <-> x<=y & x>=y)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "! >".
   *   (!(f() > g())) <-> (f() <= g())
   * End.
   * }}}
   */
  @Derivation
  lazy val notGreater: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notGreater",
      canonicalName = "! >",
      displayName = Some("¬>"),
      displayNameAscii = Some("!>"),
      displayConclusion = "__¬(f>g)__↔(f≤g)",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(f_() > g_())) <-> (f_() <= g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x ((!(x > y)) <-> (x <= y))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "> flip".
   *   (f() > g()) <-> (g() < f())
   * End.
   * }}}
   */
  @Derivation
  lazy val flipGreater: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "flipGreater",
      canonicalName = "> flip",
      displayName = Some(">F"),
      unifier = Unifier.Linear,
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f_() > g_()) <-> (g_() < f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x ((x > y) <-> (y < x))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom ">= flip".
   *   (f() >= g()) <-> (g() <= f())
   * End.
   * }}}
   */
  @Derivation
  lazy val flipGreaterEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "flipGreaterEqual",
      canonicalName = ">= flip",
      displayName = Some(">=F"),
      unifier = Unifier.Linear,
      key = "0",
      recursor = "*",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f_() >= g_()) <-> (g_() <= f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x ((x >= y) <-> (y <= x))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "< flip".
   *   (f() < g()) <-> (g() > f())
   * End.
   * }}}
   */
  @Derivation
  lazy val flipLess: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "flipLess", canonicalName = "< flip", displayName = Some("<F"), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("(f_() < g_()) <-> (g_() > f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x ((x < y) <-> (y > x))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "<= flip".
   *   (f() <= g()) <-> (g() >= f())
   * End.
   * }}}
   */
  @Derivation
  lazy val flipLessEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "flipLessEqual", canonicalName = "<= flip", displayName = Some("<=F"), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("(f_() <= g_()) <-> (g_() >= f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x ((x <= y) <-> (y >= x))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "! <".
   *   (!(f() < g())) <-> (f() >= g())
   * End.
   * }}}
   */
  @Derivation
  lazy val notLess: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notLess",
      canonicalName = "! <",
      displayName = Some("¬<"),
      displayNameAscii = Some("!<"),
      displayConclusion = "__¬(f<g)__↔(f≥g)",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(f_() < g_())) <-> (f_() >= g_())".asFormula)),
    useAt(flipGreater, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) & useAt(notGreater)(1, 0 :: Nil) & useAt(
      flipGreaterEqual
    )(1, 1 :: Nil) & byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "! <=".
   *   (!(f() <= g())) <-> (f() > g())
   * End.
   * }}}
   */
  @Derivation
  lazy val notLessEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notLessEqual",
      canonicalName = "! <=",
      displayName = Some("¬≤"),
      displayNameAscii = Some("!<="),
      displayConclusion = "__(¬(f≤g)__↔(f>g)",
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(f_() <= g_())) <-> (f_() > g_())".asFormula)),
    useAt(flipGreaterEqual, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) & useAt(notGreaterEqual)(1, 0 :: Nil) & useAt(
      flipGreater
    )(1, 1 :: Nil) & byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "! >=".
   *   (!(f() >= g())) <-> (f() < g())
   * End.
   * }}}
   */
  @Derivation
  lazy val notGreaterEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notGreaterEqual",
      canonicalName = "! >=",
      displayName = Some("¬≥"),
      displayNameAscii = Some("!>="),
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(!(f_() >= g_())) <-> (f_() < g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x ((!(x >= y)) <-> (x < y))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "+ associative".
   *   (f()+g()) + h() = f() + (g()+h())
   * End.
   * }}}
   */
  @Derivation
  lazy val plusAssociative: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "plusAssociative",
      canonicalName = "+ associative",
      displayName = Some("+A"),
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f_() + g_()) + h_() = f_() + (g_() + h_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
    )(1) &
      byUS(proveBy("\\forall z \\forall y \\forall x ((x + y) + z = x + (y + z))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "* associative".
   *   (f()*g()) * h() = f() * (g()*h())
   * End.
   * }}}
   */
  @Derivation
  lazy val timesAssociative: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "timesAssociative",
      canonicalName = "* associative",
      displayName = Some("*A"),
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("(f_() * g_()) * h_() = f_() * (g_() * h_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
    )(1) &
      byUS(proveBy("\\forall z \\forall y \\forall x ((x * y) * z = x * (y * z))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "+ commute".
   *   f()+g() = g()+f()
   * End.
   * }}}
   */
  @Derivation
  lazy val plusCommute: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "plusCommute", canonicalName = "+ commute", displayName = Some("+C"), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("f_()+g_() = g_()+f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x+y = y+x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "* commute".
   *   f()*g() = g()*f()
   * End.
   * }}}
   */
  @Derivation
  lazy val timesCommute: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "timesCommute", canonicalName = "* commute", displayName = Some("*C"), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("f_()*g_() = g_()*f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x*y = y*x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "distributive".
   *   f()*(g()+h()) = f()*g() + f()*h()
   * End.
   * }}}
   */
  @Derivation
  lazy val distributive: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "distributive", canonicalName = "distributive", displayName = Some("*+")),
    Sequent(IndexedSeq(), IndexedSeq("f_()*(g_()+h_()) = f_()*g_() + f_()*h_()".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
    )(1) &
      byUS(proveBy("\\forall z \\forall y \\forall x (x*(y+z) = x*y + x*z)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "* identity".
   *   f()*1 = f()
   * End.
   * }}}
   */
  @Derivation
  lazy val timesIdentity: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "timesIdentity", canonicalName = "* identity", displayName = Some("*I")),
    Sequent(IndexedSeq(), IndexedSeq("f_()*1 = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x (x*1 = x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "identity *".
   *   1*f() = f()
   * End.
   * }}}
   */
  @Derivation
  lazy val identityTimes: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "identityTimes", canonicalName = "identity *", displayName = Some("I*")),
    Sequent(IndexedSeq(), IndexedSeq("1*f_() = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x (1*x = x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "1/x * y".
   *   1/f() * g() = g()/f()
   * End.
   * }}}
   */
  @Derivation
  lazy val timesDivInverse: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "timesDivInverse", canonicalName = "* div-inverse", displayName = Some("1/x*")),
    Sequent(IndexedSeq(), IndexedSeq("1/f_() * g_() = g_()/f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      allInstantiateInverse(("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (1/x*y = y/x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "+ inverse".
   *   f() + (-f()) = 0
   * End.
   * }}}
   */
  @Derivation
  lazy val plusInverse: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "plusInverse", canonicalName = "+ inverse", displayName = Some("+i"), unifier = Unifier.Full),
    Sequent(IndexedSeq(), IndexedSeq("f_() + (-f_()) = 0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x (x + (-x) = 0)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "* inverse".
   *   f() != 0 -> f()*(f()^-1) = 1
   * End.
   * }}}
   */
  @Derivation
  lazy val timesInverse: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "timesInverse", canonicalName = "* inverse", displayName = Some("*i"), unifier = Unifier.Full),
    Sequent(IndexedSeq(), IndexedSeq("f_() != 0 -> f_()*(f_()^(-1)) = 1".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x (x != 0 -> x*(x^(-1)) = 1)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "positivity".
   *   f() < 0 | f() = 0 | 0 < f()
   * End.
   * }}}
   */
  @Derivation
  lazy val positivity: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "positivity", canonicalName = "positivity", displayName = Some("Pos")),
    Sequent(IndexedSeq(), IndexedSeq("f_() < 0 | f_() = 0 | 0 < f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x (x < 0 | x = 0 | 0 < x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "+ closed".
   *   0 < f() & 0 < g() -> 0 < f()+g()
   * End.
   * }}}
   */
  @Derivation
  lazy val plusClosed: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "plusClosed", canonicalName = "+ closed", displayName = Some("+c")),
    Sequent(IndexedSeq(), IndexedSeq("0 < f_() & 0 < g_() -> 0 < f_()+g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (0 < x & 0 < y -> 0 < x+y)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "* closed".
   *   0 < f() & 0 < g() -> 0 < f()*g()
   * End.
   * }}}
   */
  @Derivation
  lazy val timesClosed: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "timesClosed", canonicalName = "* closed", displayName = Some("*c")),
    Sequent(IndexedSeq(), IndexedSeq("0 < f_() & 0 < g_() -> 0 < f_()*g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (0 < x & 0 < y -> 0 < x*y)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "<".
   *   f() < g() <-> 0 < g()-f()
   * End.
   * }}}
   */
  @Derivation
  lazy val less: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "less", canonicalName = "<", displayName = Some("<"), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("f_() < g_() <-> 0 < g_()-f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x < y <-> 0 < y-x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom ">".
   *   f() > g() <-> g() < f()
   * End.
   * }}}
   */
  @Derivation
  lazy val greater: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "greater", canonicalName = ">", displayName = Some(">"), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("f_() > g_() <-> g_() < f_()".asFormula)),
    byUS(flipGreater),
  )

  // built-in arithmetic

  /**
   * {{{
   * Axiom "!= elimination".
   *   f()!=g() <-> \exists z (f()-g())*z=1
   * End.
   * }}}
   * @see
   *   André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
   */
  // @note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val notEqualElim = derivedAxiom("!= elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()!=g_()) <-> \\exists z_ ((f_()-g_())*z_=1)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x!=y) <-> \\exists z_ ((x-y)*z_=1))".asFormula, TactixLibrary.RCF))
//  )

  /**
   * {{{
   * Axiom ">= elimination".
   *   f()>=g() <-> \exists z f()-g()=z^2
   * End.
   * }}}
   * @see
   *   André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
   */
  // @note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val greaterEqualElim = derivedAxiom(">= elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()>=g_()) <-> \\exists z_ (f_()-g_()=z_^2)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x>=y) <-> \\exists z_ (x-y=z_^2))".asFormula, TactixLibrary.RCF))
//  )

  /**
   * {{{
   * Axiom "> elimination".
   *   f()>g() <-> \exists z (f()-g())*z^2=1
   * End.
   * }}}
   * @see
   *   André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
   */
  // @note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val greaterElim = derivedAxiom("> elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()>g_()) <-> \\exists z_ ((f_()-g_())*z_^2=1)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x>y) <-> \\exists z_ ((x-y)*z_^2=1))".asFormula, TactixLibrary.RCF))
//  )

  /**
   * {{{
   * Axiom "1>0".
   *   1>0
   * End.
   * }}}
   */
  @Derivation
  lazy val oneGreaterZero: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "oneGreaterZero", canonicalName = "1>0", displayName = Some("1>0"), unifier = Unifier.Linear),
    Sequent(IndexedSeq(), IndexedSeq("1>0".asFormula)),
    TactixLibrary.RCF,
  )

  /**
   * {{{
   * Axiom "nonnegative squares".
   *   f()^2>=0
   * End.
   * }}}
   */
  @Derivation
  lazy val nonnegativeSquares: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "nonnegativeSquares",
      canonicalName = "nonnegative squares",
      displayName = Some("^2>=0"),
      unifier = Unifier.Linear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("f_()^2>=0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x (x^2>=0)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom ">2!=".
   *   f()>g() -> f()!=g()
   * End.
   * }}}
   */
  @Derivation
  lazy val greaterImpliesNotEqual: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "greaterImpliesNotEqual", canonicalName = ">2!=", displayName = Some(">2!=")),
    Sequent(IndexedSeq(), IndexedSeq("f_()>g_() -> f_()!=g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x (x>y -> x!=y)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "> monotone".
   *   f()+h()>g() <- f()>g() & h()>=0
   * End.
   * }}}
   */
  @Derivation
  lazy val greaterMonotone: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "greaterMonotone", canonicalName = "> monotone", displayName = Some(">mon")),
    Sequent(IndexedSeq(), IndexedSeq("f_()+h_()>g_() <- f_()>g_() & h_()>=0".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
    )(1) &
      byUS(proveBy("\\forall z \\forall y \\forall x (x+z>y <- x>y & z>=0)".asFormula, TactixLibrary.RCF)),
  )

  // stuff

  /**
   * {{{
   * Axiom "abs".
   *   (abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))
   * End.
   * }}}
   *
   * @Derived
   *   from built-in arithmetic abs in [[org.keymaerax.tools.qe.MathematicaQETool]]
   */
  @Derivation
  lazy val abs: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "abs", canonicalName = "abs"),
    Sequent(
      IndexedSeq(),
      IndexedSeq("(abs(s_()) = t_()) <->  ((s_()>=0 & t_()=s_()) | (s_()<0 & t_()=-s_()))".asFormula),
    ),
    allInstantiateInverse(("s_()".asTerm, "x".asVariable), ("t_()".asTerm, "y".asVariable))(1) &
      byUS(
        proveBy("\\forall y \\forall x ((abs(x) = y) <->  ((x>=0 & y=x) | (x<0 & y=-x)))".asFormula, TactixLibrary.RCF)
      ),
  )

  /**
   * {{{
   * Axiom "min".
   *   (min(f(), g()) = h()) <-> ((f()<=g() & h()=f()) | (f()>g() & h()=g()))
   * End.
   * }}}
   *
   * @Derived
   *   from built-in arithmetic abs in [[org.keymaerax.tools.qe.MathematicaQETool]]
   */
  @Derivation
  lazy val min: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "min", canonicalName = "min"),
    Sequent(
      IndexedSeq(),
      IndexedSeq("(min(f_(), g_()) = h_()) <-> ((f_()<=g_() & h_()=f_()) | (f_()>g_() & h_()=g_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall z \\forall y \\forall x ((min(x, y) = z) <-> ((x<=y & z=x) | (x>y & z=y)))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "max".
   *   (max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<g() & h()=g()))
   * End.
   * }}}
   *
   * @Derived
   *   from built-in arithmetic abs in [[org.keymaerax.tools.qe.MathematicaQETool]]
   */
  @Derivation
  lazy val max: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "max", canonicalName = "max"),
    Sequent(
      IndexedSeq(),
      IndexedSeq("(max(f_(), g_()) = h_()) <-> ((f_()>=g_() & h_()=f_()) | (f_()<g_() & h_()=g_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall z \\forall y \\forall x ((max(x, y) = z) <-> ((x>=y & z=x) | (x<y & z=y)))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "<*> stuck".
   *   <{a;}*>p(||) <-> <{a;}*>p(||)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val loopStuck: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "loopStuck",
      canonicalName = "<*> stuck",
      displayName = Some("<*> stuck"),
      key = "0",
      recursor = "",
    ),
    Sequent(IndexedSeq(), IndexedSeq("<{a_;}*>p_(||) <-> <{a_;}*>p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  @Derivation
  lazy val programStuck: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "programStuck",
      canonicalName = "<a> stuck",
      displayName = Some("<a> stuck"),
      key = "0",
      recursor = "1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("<a_;>p_(||) <-> <a_;>p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "<'> stuck".
   *   <{c&q(||)}>p(||) <-> <{c&q(||)}>p(||)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val odeStuck: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "odeStuck",
      canonicalName = "<'> stuck",
      displayName = Some("<'> stuck"),
      key = "0",
      recursor = "",
    ),
    Sequent(IndexedSeq(), IndexedSeq("<{c_&q_(||)}>p_(||) <-> <{c_&q_(||)}>p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "& recursor".
   *   p() & q() <-> p() & q()
   * End.
   * }}}
   */
  @Derivation
  lazy val andRecursor: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "andRecursor",
      canonicalName = "& recursor",
      displayName = Some("& recursor"),
      unifier = Unifier.Linear,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() & q_()) <-> (p_() & q_())".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "| recursor".
   *   p() | q() <-> p() | q()
   * End.
   * }}}
   */
  @Derivation
  lazy val orRecursor: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "orRecursor",
      canonicalName = "| recursor",
      displayName = Some("| recursor"),
      unifier = Unifier.Linear,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_() | q_()) <-> (p_() | q_())".asFormula)),
    prop,
  )

  /**
   * {{{
   * Axiom "<= both".
   *   f()<=g() <- ((f() <= F() & gg() <= g()) & F() <= gg())
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalLEBoth: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalLEBoth",
      canonicalName = "<= both",
      displayName = Some("<= both"),
      key = "1",
      recursor = "",
    ),
    Sequent(IndexedSeq(), IndexedSeq("f_()<=g_() <- ((f_()<=F_() & gg_()<=g_()) & F_() <= gg_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("gg_()".asTerm, "yy".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall yy \\forall X \\forall y \\forall x (x<=y <- ((x<=X & yy<=y) & X<=yy))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "< both".
   *   f()<g() <- ((f() <= F() & gg() <= g()) & F() < gg())
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalLBoth: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "intervalLBoth", canonicalName = "< both", displayName = Some("< both"), key = "1", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()<g_() <- ((f_()<=F_() & gg_()<=g_()) & F_() < gg_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("gg_()".asTerm, "yy".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall yy \\forall X \\forall y \\forall x (x<y <- ((x<=X & yy<=y) & X<yy))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "neg<= up".
   *   -f()<=h() <- (ff()<=f() & -ff() <= h())
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalUpNeg: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalUpNeg",
      canonicalName = "neg<= up",
      displayName = Some("neg<="),
      key = "1",
      recursor = "0",
    ),
    Sequent(IndexedSeq(), IndexedSeq("-f_()<=h_() <- (ff_() <= f_() & -ff_() <= h_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
    )(1) &
      byUS(proveBy("\\forall xx \\forall z \\forall x (-x<=z <- (xx<=x & -xx <=z))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "abs<= up".
   *   abs(f())<=h() <- ((ff()<=f() & f() <= F()) & (-ff()<=h() & F()<=h()))
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalUpAbs: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalUpAbs",
      canonicalName = "abs<= up",
      displayName = Some("abs<="),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("abs(f_())<=h_() <- ((ff_() <= f_() & f_() <= F_()) & (-ff_() <= h_() & F_()<= h_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
      ("F_()".asTerm, "X".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall X \\forall xx \\forall z \\forall x (abs(x)<=z <- ((xx<=x & x <=X) & (-xx <= z & X <= z)))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "max<= up".
   *   max(f(),g())<=h() <- ((f()<=F() & g()<=G()) & (F() <= h() & G()<=h()))
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalUpMax: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalUpMax",
      canonicalName = "max<= up",
      displayName = Some("max<="),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("max(f_(),g_())<=h_() <- ((f_()<=F_() & g_()<=G_()) & (F_() <= h_() & G_()<=h_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("G_()".asTerm, "Y".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall Y \\forall X \\forall z \\forall y \\forall x (max(x,y)<=z <- ((x<=X & y<=Y) & (X<=z & Y<=z)))"
          .asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "min<= up".
   *   min(f(),g())<=h() <- ((f()<=F() & g()<=G()) & (F()<=h() | G()<=h()))
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalUpMin: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalUpMin",
      canonicalName = "min<= up",
      displayName = Some("min<="),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("min(f_(),g_())<=h_() <- ((f_()<=F_() & g_()<=G_()) & (F_() <= h_() | G_()<=h_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("G_()".asTerm, "Y".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall Y \\forall X \\forall z \\forall y \\forall x (min(x,y)<=z <- ((x<=X & y<=Y) & (X<=z | Y<=z)))"
          .asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "+<= up".
   *   f()+g()<=h() <- ((f()<=F() & g()<=G()) & F()+G()<=h())
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalUpPlus: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalUpPlus",
      canonicalName = "+<= up",
      displayName = Some("+<="),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("f_()+g_()<=h_() <- ((f_()<=F_() & g_()<=G_()) & F_()+G_()<=h_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("G_()".asTerm, "Y".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall Y \\forall X \\forall z \\forall y \\forall x (x+y<=z <- ((x<=X & y<=Y) & X+Y<=z))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "-<= up".
   *   f()-g()<=h() <- ((f()<=F() & gg()<=g()) & F()-gg()<=h())
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalUpMinus: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalUpMinus",
      canonicalName = "-<= up",
      displayName = Some("-<="),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("f_()-g_()<=h_() <- ((f_()<=F_() & gg_()<=g_()) & F_()-gg_()<=h_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("gg_()".asTerm, "yy".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall yy \\forall X \\forall z \\forall y \\forall x (x-y<=z <- ((x<=X & yy<=y) & X-yy<=z))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "*<= up".
   *   f()*g()<=h() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & (ff()*gg()<=h() & ff()*G()<=h() & F()*gg()<=h() & F()*G()<=h()))
   * End.
   * }}}
   */
  // A more efficient check is available if we know that f_() or g_() is strictly positive
  // For example, if 0<= ff_(), then we only need ff_() * G_() <= h_() & F_() * G() <= h_()

  @Derivation
  lazy val intervalUpTimes: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalUpTimes",
      canonicalName = "*<= up",
      displayName = Some("*<="),
      key = "1",
      recursor = "0.0.0;0.0.1;0.1.0;0.1.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "f_()*g_()<=h_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & (ff_()*gg_()<=h_() & ff_()*G_()<=h_() & F_()*gg_()<=h_() & F_()*G_()<=h_()))"
          .asFormula
      ),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("G_()".asTerm, "Y".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
      ("gg_()".asTerm, "yy".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (x*y<=z <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & (xx*yy<=z & xx*Y<=z & X*yy<=z & X*Y<=z)))"
          .asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "1Div<= up".
   *   1/f()<=h() <- ((ff()<=f() & ff()*f()>0) & (1/ff()<=h()))
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalUp1Divide: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "intervalUp1Divide", canonicalName = "1Div<= up", displayName = Some("1/<=")),
    Sequent(IndexedSeq(), IndexedSeq("1/f_()<=h_() <- ((F_()<=f_() & F_()*f_()>0) & (1/F_()<=h_()))".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("h_()".asTerm, "y".asVariable),
      ("F_()".asTerm, "X".asVariable),
    )(1) &
      byUS(
        proveBy("\\forall X \\forall y \\forall x (1/x<=y <- ((X<=x & X*x>0) & (1/X<=y)))".asFormula, TactixLibrary.RCF)
      ),
  )

  /**
   * {{{
   * Axiom "Div<= up".
   *   f()/g()<=h() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & ((G()<0 | 0<gg()) & (ff()/gg()<=h() & ff()/G()<=h() & F()/gg()<=h() & F()/G()<=h())))
   * End.
   * }}}
   */
  // A more efficient check is available

//  lazy val intervalUpDivide = derivedAxiom("Div<= up", Sequent(IndexedSeq(), IndexedSeq(("f_()/g_()<=h_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((G_()<0 | 0<gg_()) & (ff_()/gg_()<=h_() & ff_()/G_()<=h_() & F_()/gg_()<=h_() & F_()/G_()<=h_())))").asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
//      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (x/y<=z <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(xx/yy<=z & xx/Y<=z & X/yy<=z & X/Y<=z))))".asFormula, TactixLibrary.RCF))
//  )

  /**
   * {{{
   * Axiom "pow<= up".
   *   f()^2<=h() <- ((ff()<=f() & f()<=F()) & (ff()^2<=h() & F()^2<=h()))
   * End.
   * }}}
   */

  @Derivation
  lazy val intervalUpPower: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalUpPower",
      canonicalName = "pow<= up",
      displayName = Some("pow<="),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("f_()^2 <=h_() <- ((ff_()<=f_() & f_()<=F_()) & (ff_()^2 <= h_() & F_()^2 <=h_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall xx \\forall X \\forall z \\forall x (x^2<=z <- ((xx<=x & x<=X) & (xx^2<=z & X^2<=z)))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "<=neg down".
   *   h<=-f() <- (f()<=F() & h() <= -F())
   * End.
   * }}}
   */

  @Derivation
  lazy val intervalDownNeg: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalDownNeg",
      canonicalName = "<=neg down",
      displayName = Some("<=neg"),
      key = "1",
      recursor = "0",
    ),
    Sequent(IndexedSeq(), IndexedSeq("h_()<=-f_() <- (f_() <= F_() & h_() <= -F_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
    )(1) &
      byUS(proveBy("\\forall X \\forall z \\forall x (z<=-x <- (x<=X & z<=-X))".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "<=abs down".
   *   h()<=abs(f()) <- ((ff()<=f() & f() <= F()) & (h()<=ff() | h()<=-F()))
   * End.
   * }}}
   */

  @Derivation
  lazy val intervalDownAbs: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalDownAbs",
      canonicalName = "<=abs down",
      displayName = Some("<=abs"),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("h_()<=abs(f_()) <- ((ff_() <= f_() & f_() <= F_()) & (h_() <= ff_() | h_() <= -F_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
      ("F_()".asTerm, "X".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall X \\forall xx \\forall z \\forall x (z<=abs(x) <- ((xx<=x & x <=X) & (z <= xx | z <= -X)))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "<=max down".
   *   h()<=max(f(),g()) <- ((ff()<=f() & gg()<=g()) & (ff()<=h() | gg()<=h()))
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalDownMax: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalDownMax",
      canonicalName = "<=max down",
      displayName = Some("<=max"),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("h_() <= max(f_(),g_()) <- ((ff_()<=f_() & gg_()<=g_()) & (h_() <= ff_() | h_() <= gg_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
      ("gg_()".asTerm, "yy".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall yy \\forall xx \\forall z \\forall y \\forall x (z <= max(x,y) <- ((xx<=x & yy<=y) & (z<=xx | z<=yy)))"
          .asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "<=min down".
   *   h()<=min(f(),g()) <- ((ff()<=f() & gg()<=g()) & (h()<=ff() & h()<=gg()))
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalDownMin: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalDownMin",
      canonicalName = "<=min down",
      displayName = Some("<=min"),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq("h_()<=min(f_(),g_()) <- ((ff_()<=f_() & gg_()<=g_()) & (h_() <= ff_() & h_()<=gg_()))".asFormula),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
      ("gg_()".asTerm, "yy".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall yy \\forall xx \\forall z \\forall y \\forall x (z<=min(x,y) <- ((xx<=x & yy<=y) & (z<=xx & z<=yy)))"
          .asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "<=+ down".
   *   h()<=f()+g() <- ((ff()<=f() & gg()<=g()) & h()<=ff()+gg())
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalDownPlus: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalDownPlus",
      canonicalName = "<=+ down",
      displayName = Some("<=+"),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("h_()<=f_()+g_() <- ((ff_()<=f_() & gg_()<=g_()) & h_()<=ff_()+gg_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
      ("gg_()".asTerm, "yy".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall yy \\forall xx \\forall z \\forall y \\forall x (z<=x+y <- ((xx<=x & yy<=y) & z<=xx+yy))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "<=- down".
   *   h()<=f()-g() <- ((ff()<=f() & g()<=G()) & h()<=ff()-G())
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalDownMinus: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalDownMinus",
      canonicalName = "<=- down",
      displayName = Some("<=-"),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("h_()<=f_()-g_() <- ((ff_()<=f_() & g_()<=G_()) & h_()<=ff_()-G_())".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
      ("G_()".asTerm, "Y".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall Y \\forall xx \\forall z \\forall y \\forall x (z<=x-y <- ((xx<=x & y<=Y) & z<=xx-Y))".asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "<=* down".
   *   h()<=f()*g()<- (((ff()<=f() & f()<=F()) & (gg()<=g() & g()<=G())) & (h()<=ff()*gg() & h()<=ff()*G() & h()<=F()*gg() & h()<=F()*G()))
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalDownTimes: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalDownTimes",
      canonicalName = "<=* down",
      displayName = Some("<=*"),
      key = "1",
      recursor = "0.0.0;0.0.1;0.1.0;0.1.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "h_()<=f_()*g_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & (h_()<=ff_()*gg_() & h_()<=ff_()*G_() & h_()<=F_()*gg_() & h_()<=F_()*G_()))"
          .asFormula
      ),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("g_()".asTerm, "y".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("G_()".asTerm, "Y".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
      ("gg_()".asTerm, "yy".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (z<=x*y <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & (z<=xx*yy & z<=xx*Y & z<=X*yy & z<=X*Y)))"
          .asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "<=1Div down".
   *   h()<=1/f() <- ((f()<=F() & F()*f()>0) & (h()<=1/F()))
   * End.
   * }}}
   */
  @Derivation
  lazy val intervalDown1Divide: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "intervalDown1Divide", canonicalName = "<=1Div down", displayName = Some("<=1/")),
    Sequent(IndexedSeq(), IndexedSeq("h_()<=1/f_() <- ((f_()<=F_() & F_()*f_()>0) & (h_()<=1/F_()))".asFormula)),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("h_()".asTerm, "y".asVariable),
      ("F_()".asTerm, "X".asVariable),
    )(1) &
      byUS(
        proveBy("\\forall X \\forall y \\forall x (y<=1/x <- ((x<=X & X*x>0) & (y<=1/X)))".asFormula, TactixLibrary.RCF)
      ),
  )

  /**
   * {{{
   * Axiom "<=Div down".
   *   h() <= f()/g() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & ((G()<0 | 0 < gg()) & (ff()/gg()<=h() & ff()/G()<=h() & F()/gg()<=h() & F()/G()<=h())))
   * End.
   * }}}
   */

//  lazy val intervalDownDivide = derivedAxiom("<=Div down", Sequent(IndexedSeq(), IndexedSeq(("h_() <= f_()/g_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((G_()<0 | 0 < gg_()) & (h_()<=ff_()/gg_() & h_()<=ff_()/G_() & h_()<=F_()/gg_() & h_()<=F_()/G_())))").asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
//      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (z<=x/y <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(z<=xx/yy & z<=xx/Y & z<=X/yy & z<=X/Y))))".asFormula, TactixLibrary.RCF))
//  )

  /**
   * {{{
   * Axiom "<=pow down".
   *   h()<=f()^2 <- ((ff()<=f() & f()<=F()) & ((0<= ff_() & h()<=ff()^2) | (F_() <0 & h()<=F()^2)))
   * End.
   * }}}
   */

  @Derivation
  lazy val intervalDownPower: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "intervalDownPower",
      canonicalName = "<=pow down",
      displayName = Some("<=pow"),
      key = "1",
      recursor = "0.0;0.1",
    ),
    Sequent(
      IndexedSeq(),
      IndexedSeq(
        "h_() <= f_()^2 <- ((ff_()<=f_() & f_()<=F_()) & ((0<= ff_() & h_() <= ff_()^2) | (F_()<=0 & h_() <= F_()^2)))"
          .asFormula
      ),
    ),
    allInstantiateInverse(
      ("f_()".asTerm, "x".asVariable),
      ("h_()".asTerm, "z".asVariable),
      ("F_()".asTerm, "X".asVariable),
      ("ff_()".asTerm, "xx".asVariable),
    )(1) &
      byUS(proveBy(
        "\\forall xx \\forall X \\forall z \\forall x (z<=x^2 <- ((xx<=x & x<=X) & ((0 <= xx & z<=xx^2) | (X<= 0 & z<=X^2))))"
          .asFormula,
        TactixLibrary.RCF,
      )),
  )

  /**
   * {{{
   * Axiom "dgZeroEquilibrium".
   *   x=0 & n>0 -> [{x'=c*x^n}]x=0
   * End.
   * }}}
   */
  // @note not derivable with Z3; added to AxiomBase and tested to be derivable in DerivedAxiomsTests.
//  lazy val dgZeroEquilibrium = derivedAxiom("dgZeroEquilibrium", Sequent(IndexedSeq(), IndexedSeq("x=0 & n>0 -> [{x'=c*x^n}]x=0".asFormula)),
//    implyR(1) & DA("y' = ( (-c*x^(n-1)) / 2)*y".asDifferentialProgram, "x*y^2=0&y>0".asFormula)(1) <(
//      TactixLibrary.QE,
//      implyR(1) & TactixLibrary.boxAnd(1) & andR(1) <(
//        DifferentialTactics.diffInd()(1) & QE,
//        DA("z' = (c*x^(n-1)/4) * z".asDifferentialProgram, "y*z^2 = 1".asFormula)(1) <(
//          QE,
//          implyR(1) & diffInd()(1) & QE
//        )
//      )
//    )
//  )

  // Metric Normal Form

  /**
   * {{{
   * Axiom "= expand".
   *   f_()=g_() <-> f_()<=g_()&g_()<=f_()
   * End.
   * }}}
   */
  @Derivation
  lazy val equalExpand: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "equalExpand", canonicalName = "= expand"),
    Sequent(IndexedSeq(), IndexedSeq("f_()=g_() <-> f_()<=g_()&g_()<=f_()".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "!= expand".
   *   f_()!=g_() <-> f_()<g_()|g_()<f_()
   * End.
   * }}}
   */
  @Derivation
  lazy val notEqualExpand: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "notEqualExpand", canonicalName = "!= expand"),
    Sequent(IndexedSeq(), IndexedSeq("f_()!=g_() <-> f_()<g_()|g_()<f_()".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom ">= neg".
   *   f_()>=g_() <-> -f_()<=-g_()
   * End.
   * }}}
   */
  @Derivation
  lazy val geNeg: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "geNeg", canonicalName = ">= neg"),
    Sequent(IndexedSeq(), IndexedSeq("f_()>=g_() <-> -f_()<=-g_()".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "> neg".
   *   f_()>g_() <-> -f_() < -g_()
   * End.
   * }}}
   */
  @Derivation
  lazy val gtNeg: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "gtNeg", canonicalName = "> neg"),
    Sequent(IndexedSeq(), IndexedSeq("f_()>g_() <-> -f_() < -g_()".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "<= to <".
   *   f_()<=0 <- f_()<0
   * End.
   * }}}
   */
  @Derivation
  lazy val leApprox: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "leApprox", canonicalName = "<= to <", unifier = Unifier.Linear, key = "1", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()<=0 <- f_()<0".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "metric <".
   *   f_()<g_() <-> f_()-g_()<0
   * End.
   * }}}
   */
  @Derivation
  lazy val metricLt: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "metricLt", canonicalName = "metric <", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()<g_() <-> f_()-g_()<0".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "metric <=".
   *   f_()<=g_() <-> f_()-g_()<=0
   * End.
   * }}}
   */
  @Derivation
  lazy val metricLe: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "metricLe", canonicalName = "metric <=", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()<=g_() <-> f_()-g_()<=0".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "metric <= & <=".
   *   f_()<=0 & g_()<=0 <-> max(f_(), g_())<=0
   * End.
   * }}}
   */
  @Derivation
  lazy val metricAndLe: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "metricAndLe", canonicalName = "metric <= & <=", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()<=0 & g_()<=0 <-> max(f_(), g_())<=0".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "metric < & <".
   *   f_()<0 & g_()<0 <-> max(f_(), g_())<0
   * End.
   * }}}
   */
  @Derivation
  lazy val metricAndLt: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "metricAndLt", canonicalName = "metric < & <", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()<0 & g_()<0 <-> max(f_(), g_())<0".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "metric <= | <=".
   *   f_()<=0 | g_()<=0 <-> min(f_(), g_())<=0
   * End.
   * }}}
   */
  @Derivation
  lazy val metricOrLe: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "metricOrLe", canonicalName = "metric <= | <=", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()<=0 | g_()<=0 <-> min(f_(), g_())<=0".asFormula)),
    QE & done,
  )

  /**
   * {{{
   * Axiom "metric < | <".
   *   f_()<0 | g_()<0 <-> min(f_(), g_())<0
   * End.
   * }}}
   */
  @Derivation
  lazy val metricOrLt: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "metricOrLt", canonicalName = "metric < | <", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()<0 | g_()<0 <-> min(f_(), g_())<0".asFormula)),
    QE & done,
  )

  // Extra arithmetic axioms for SimplifierV3 not already included above

  /**
   * {{{
   * Axiom "* identity neg".
   *   f()*-1 = -f()
   * End.
   * }}}
   */
  @Derivation
  lazy val timesIdentityNeg: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "timesIdentityNeg", canonicalName = "* identity neg", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()*(-1) = -f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x (x*(-1) = -x)".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "minus neg".
   *   -(f()-g()) = g()-f()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val minusNeg: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "minusNeg", canonicalName = "minus neg", unifier = Unifier.Linear, key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("-(f_()-g_()) = g_()-f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x -(x-y)=y-x".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "plus neg".
   *   f()+(-g()) = f()-g()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val plusNeg: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "plusNeg", canonicalName = "plus neg", unifier = Unifier.Linear, key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()+(-g_()) = f_()-g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
      byUS(proveBy("\\forall y \\forall x x+(-y)=x-y".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "plus neg".
   *   f()+(-g()) = f()-g()
   * End.
   * }}}
   *
   * @Derived
   */
  // TODO That displayName looks like a typo
  @Derivation
  lazy val negPlus: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "negPlus",
      canonicalName = "neg plus",
      displayName = Some("plusNeg"),
      unifier = Unifier.Linear,
      key = "0",
      recursor = "",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(-g_()) + f_() = f_()-g_()".asFormula)),
    useAt(plusCommute.provable)(1, PosInExpr(0 :: Nil)) & byUS(plusNeg.provable),
  )

  /**
   * {{{
   * Axiom "neg neg".
   *   -(-f()) = f()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val negNeg: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "negNeg", canonicalName = "neg neg", unifier = Unifier.Linear, key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("-(-f_()) = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x -(-x)=x".asFormula, TactixLibrary.RCF)),
  )

  /**
   * {{{
   * Axiom "-0".
   *   (f()-0) = f()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val minusZero: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "minusZero", canonicalName = "-0", unifier = Unifier.Linear, key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("(f_()-0) = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(
      proveBy("\\forall x (x-0 = x)".asFormula, TactixLibrary.RCF)
    ),
  )

  /**
   * {{{
   * Axiom "0-".
   *   (0-f()) = -f()
   * End.
   * }}}
   *
   * @Derived
   */
  @Derivation
  lazy val zeroMinus: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "zeroMinus", canonicalName = "0-", unifier = Unifier.Linear, key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("(0-f_()) = -f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(
      proveBy("\\forall x (0-x = -x)".asFormula, TactixLibrary.RCF)
    ),
  )

  // TODO: add more text to the following
  @Derivation
  lazy val gtzImpNez: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "gtzImpNez", canonicalName = ">0 -> !=0"),
    Sequent(IndexedSeq(), IndexedSeq("f_() > 0 -> f_()!=0".asFormula)),
    QE,
  )

  @Derivation
  lazy val ltzImpNez: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "ltzImpNez", canonicalName = "<0 -> !=0"),
    Sequent(IndexedSeq(), IndexedSeq("f_() < 0 -> f_()!=0".asFormula)),
    QE,
  )

  @Derivation
  lazy val zeroDivNez: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "zeroDivNez", canonicalName = "!=0 -> 0/F"),
    Sequent(IndexedSeq(), IndexedSeq("f_() != 0 -> 0/f_() = 0".asFormula)),
    QE,
  )

  @Derivation
  lazy val powZero: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "powZero", canonicalName = "F^0", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()^0 = 1".asFormula)),
    QE,
  )

  @Derivation
  lazy val powOne: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "powOne", canonicalName = "F^1", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()^1 = f_()".asFormula)),
    QE,
  )

  @Derivation
  lazy val powNegOne: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "powNegOne", canonicalName = "F^(-1)", key = "0", recursor = ""),
    Sequent(IndexedSeq(), IndexedSeq("f_()^(-1) = 1/f_()".asFormula)),
    RCF,
  )

  /** `t<->tt` equivalence */
  private def equivSequent(t: String, tt: String): Sequent =
    Sequent(IndexedSeq(), IndexedSeq(Equiv(t.asFormula, tt.asFormula)))

  /** `f->(t<->tt)` conditional equivalence */
  private def implySequent(f: String, t: String, tt: String): Sequent =
    Sequent(IndexedSeq(), IndexedSeq(Imply(f.asFormula, Equiv(t.asFormula, tt.asFormula))))

  private def propQE: BelleExpr = prop & QE & done

  // The following may already appear above
  // They are stated here in a shape suitable for the simplifier
  // (Ir)reflexivity axioms for comparison operators
  @Derivation
  lazy val lessNotRefl: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "lessNotRefl", canonicalName = "< irrefl", unifier = Unifier.Full, key = "0", recursor = ""),
    equivSequent("F_()<F_()", "false"),
    propQE,
  )

  @Derivation
  lazy val greaterNotRefl: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "greaterNotRefl", canonicalName = "> irrefl", unifier = Unifier.Full, key = "0", recursor = ""),
    equivSequent("F_()>F_()", "false"),
    propQE,
  )

  @Derivation
  lazy val notEqualNotRefl: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "notEqualNotRefl", canonicalName = "!= irrefl", unifier = Unifier.Full, key = "0", recursor = ""),
    equivSequent("F_()!=F_()", "false"),
    propQE,
  )

  /** @see [[equivReflexive]] */
  @Derivation
  lazy val equalRefl: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "equalRefl", canonicalName = "= refl", unifier = Unifier.Full, key = "0", recursor = ""),
    equivSequent("F_() = F_()", "true"),
    propQE,
  )

  @Derivation
  lazy val lessEqualRefl: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "lessEqualRefl", canonicalName = "<= refl", unifier = Unifier.Full, key = "0", recursor = ""),
    equivSequent("F_() <= F_()", "true"),
    propQE,
  )

  @Derivation
  lazy val greaterEqualRefl: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo
      .create(name = "greaterEqualRefl", canonicalName = ">= refl", unifier = Unifier.Full, key = "0", recursor = ""),
    equivSequent("F_() >= F_()", "true"),
    propQE,
  )

  // (anti) symmetry axioms
  @Derivation
  lazy val equalSym: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "equalSym", canonicalName = "= sym"),
    implySequent("F_() = G_()", "G_() = F_()", "true"),
    propQE,
  )

  @Derivation
  lazy val notEqualSym: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "notEqualSym", canonicalName = "!= sym"),
    implySequent("F_() != G_()", "G_() != F_()", "true"),
    propQE,
  )

  @Derivation
  lazy val greaterNotSym: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "greaterNotSym", canonicalName = "> antisym"),
    implySequent("F_() > G_()", "G_() > F_()", "false"),
    propQE,
  )

  @Derivation
  lazy val lessNotSym: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "lessNotSym", canonicalName = "< antisym"),
    implySequent("F_() < G_()", "G_() < F_()", "false"),
    propQE,
  )

  // totality axioms
  @Derivation
  lazy val lessEqualTotal: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "lessEqualTotal", canonicalName = "<= total"),
    "==> F_() <= G_() | G_() <= F_()".asSequent,
    propQE,
  )

  @Derivation
  lazy val greaterEqualTotal: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(name = "greaterEqualTotal", canonicalName = ">= total"),
    "==> F_() >= G_() | G_() >= F_()".asSequent,
    propQE,
  )

  /**
   * {{{
   * Axiom "all stutter".
   *   \forall x P <-> \forall x P
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val allStutter: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "allStutter",
      canonicalName = "all stutter",
      displayName = Some("all stutter"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "0",
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(||) <-> \\forall x_ p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  @Derivation
  lazy val allStutterPrime: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "allStutterPrime",
      canonicalName = "all stutter prime",
      displayName = Some("all stutter'"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "",
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_' p_(||) <-> \\forall x_' p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "exists stutter".
   *   \exists x P <-> \exists x P
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val existsStutter: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsStutter",
      canonicalName = "exists stutter",
      displayName = Some("exists stutter"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "0",
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ p_(||) <-> \\exists x_ p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  @Derivation
  lazy val existsStutterPrime: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "existsStutterPrime",
      canonicalName = "exists stutter prime",
      displayName = Some("exists stutter'"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "",
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_' p_(||) <-> \\exists x_' p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "and stutter".
   *   P&Q <-> P&Q
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val andStutter: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "andStutter",
      canonicalName = "and stutter",
      displayName = Some("and stutter"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("p_(||) & q_(||) <-> p_(||) & q_(||)".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "or stutter".
   *   P|Q <-> P|Q
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val orStutter: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "orStutter",
      canonicalName = "or stutter",
      displayName = Some("or stutter"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("p_(||) | q_(||) <-> p_(||) | q_(||)".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "imply stutter".
   *   (P->Q) <-> (P->Q)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val implyStutter: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "implyStutter",
      canonicalName = "imply stutter",
      displayName = Some("imply stutter"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_(||) -> q_(||)) <-> (p_(||) -> q_(||))".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "equiv stutter".
   *   (P<->Q) <-> (P<->Q)
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val equivStutter: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "equivStutter",
      canonicalName = "equiv stutter",
      displayName = Some("equiv stutter"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "0;1",
    ),
    Sequent(IndexedSeq(), IndexedSeq("(p_(||) <-> q_(||)) <-> (p_(||) <-> q_(||))".asFormula)),
    byUS(equivReflexive),
  )

  /**
   * {{{
   * Axiom "not stutter".
   *   !P <-> !P
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
   */
  @Derivation
  lazy val notStutter: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "notStutter",
      canonicalName = "not stutter",
      displayName = Some("not stutter"),
      displayLevel = DisplayLevel.Internal,
      key = "0",
      recursor = "0",
    ),
    Sequent(IndexedSeq(), IndexedSeq("!p_(||) <-> !p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  // Liveness additions

  /**
   * {{{
   * Axiom "K<&>".
   *   [{c & q(||) & !p(||)}]!r(||) -> (<{c & q(||)}>r(||) -> <{c & q(||)}>p(||))
   * End.
   * }}}
   *
   * @Derived
   * @note
   *   postcondition refinement
   */
  @Derivation
  lazy val KDomD: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "KDomD",
      canonicalName = "K<&>",
      displayConclusion = "[x'=f(x)&Q∧¬P]¬R → (__<x'=f(x)&Q>R → <x'=f(x)&Q>P__)",
      key = "1",
      recursor = "*",
    ),
    "==> [{c & q(||) & !p(||)}]!r(||) -> (<{c & q(||)}>r(||) -> <{c & q(||)}>p(||))".asSequent,
    implyR(1) & implyR(1) &
      useExpansionAt(diamond)(1) &
      useExpansionAt(diamond)(-2) &
      notL(-2) & notR(1) & implyRi()(-1, 1) &
      useAt(DR, PosInExpr(1 :: Nil))(1) & TactixLibrary.boxAnd(1) & andR(1) < (
        HilbertCalculus.DW(1) & G(1) & implyR(1) & id,
        id
      ),
  )

  /** Polynomial Arithmetic [[org.keymaerax.btactics.PolynomialArithV2]] */

  @Derivation
  lazy val eqNormalize: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "eqNormalize", canonicalName = "eqNormalize", key = "0", recursor = ""),
    "s_() = t_() <-> s_() - t_() = 0".asFormula,
    QE,
  )

  @Derivation
  lazy val neNormalize: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "neNormalize", canonicalName = "neNormalize", key = "0", recursor = ""),
    "s_() != t_() <-> s_() - t_() != 0".asFormula,
    QE,
  )

  @Derivation
  lazy val gtNormalize: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "gtNormalize", canonicalName = "gtNormalize", key = "0", recursor = ""),
    "f_()>g_() <-> f_()-g_()>0".asFormula,
    QE,
  )

  @Derivation
  lazy val geNormalize: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "geNormalize", canonicalName = "geNormalize", key = "0", recursor = ""),
    "f_()>=g_() <-> f_()-g_()>=0".asFormula,
    QE,
  )

  @Derivation
  lazy val divNeEq: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divNeEq", canonicalName = "divNeEq"),
    "G_()!=0 -> F_()/G_() = 0 -> F_() = 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divNeNe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divNeNe", canonicalName = "divNeNe"),
    "G_()!=0 -> F_()/G_() != 0 -> F_() != 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divGtEq: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divGtEq", canonicalName = "divGtEq"),
    "G_()>0 -> F_()/G_() = 0 -> F_() = 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divLtEq: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divLtEq", canonicalName = "divLtEq"),
    "G_()<0 -> F_()/G_() = 0 -> F_() = 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divGtNe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divGtNe", canonicalName = "divGtNe"),
    "G_()>0 -> F_()/G_() != 0 -> F_() != 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divLtNe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divLtNe", canonicalName = "divLtNe"),
    "G_()<0 -> F_()/G_() != 0 -> F_() != 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divGtGt: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divGtGt", canonicalName = "divGtGt"),
    "G_()>0 -> F_()/G_() > 0 -> F_() > 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divLtGt: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divLtGt", canonicalName = "divLtGt"),
    "G_()<0 -> F_()/G_() > 0 -> F_() < 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divGtGe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divGtGe", canonicalName = "divGtGe"),
    "G_()>0 -> F_()/G_() >= 0 -> F_() >= 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divLtGe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divLtGe", canonicalName = "divLtGe"),
    "G_()<0 -> F_()/G_() >= 0 -> F_() <= 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divGtLt: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divGtLt", canonicalName = "divGtLt"),
    "G_()>0 -> F_()/G_() < 0 -> F_() < 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divLtLt: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divLtLt", canonicalName = "divLtLt"),
    "G_()<0 -> F_()/G_() < 0 -> F_() > 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divGtLe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divGtLe", canonicalName = "divGtLe"),
    "G_()>0 -> F_()/G_() <= 0 -> F_() <= 0".asFormula,
    QE,
  )

  @Derivation
  lazy val divLtLe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divLtLe", canonicalName = "divLtLe"),
    "G_()<0 -> F_()/G_() <= 0 -> F_() >= 0".asFormula,
    QE,
  )

  @Derivation
  lazy val coefficientTimesPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "coefficientTimesPrv", canonicalName = "coefficientTimesPrv"),
    ("(l_() = ln_()/ld_() & r_() = rn_()/rd_() & ((ln_()*rn_() = pn_() & ld_()*rd_()=pd_() & ld_() != 0 & rd_() != 0)<-> true)) ->" +
      "l_()*r_() = pn_()/pd_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val coefficientPlusPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "coefficientPlusPrv", canonicalName = "coefficientPlusPrv"),
    ("(l_() = ln_()/ld_() & r_() = rn_()/rd_() & ((ln_()*rd_() + rn_()*ld_() = pn_() & ld_()*rd_()=pd_() & ld_() != 0 & rd_() != 0)<-> true)) ->" +
      "l_()+r_() = pn_()/pd_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val coefficientNegPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "coefficientNegPrv", canonicalName = "coefficientNegPrv"),
    ("(x_() = xn_()/xd_() & ((-xn_()=nxn_() & xd_() != 0)<-> true)) ->" +
      "-x_() = nxn_()/xd_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val coefficientBigDecimalPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "coefficientBigDecimalPrv", canonicalName = "coefficientBigDecimalPrv"),
    ("(x_() = xn_()/xd_() & ((xn_()/xd_()=bd_() & xd_() != 0)<-> true)) ->" +
      "x_() = bd_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val plusTimes: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "plusTimes", canonicalName = "plusTimes"),
    "l_() = a_()*b_() & r_() = c_()*b_() & a_() + c_() = d_() -> l_() + r_() = d_()*b_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val negTimes: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "negTimes", canonicalName = "negTimes"),
    "l_() = a_()*b_() & -a_() = c_() -> -l_() = c_()*b_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val powerLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerLemma", canonicalName = "powerLemma"),
    "(i_() >= 0 & j_() >= 0 & i_() + j_() = k_()) -> x_()^i_() * x_()^j_() = x_() ^ k_()".asFormula,
    prop & eqR2L(-3)(1) & cohideR(1) & QE & done,
  )

  @Derivation
  lazy val monomialTimesLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "monomialTimesLemma", canonicalName = "monomialTimesLemma"),
    ("(l_() = cl_() * xls_() &" +
      " r_() = cr_() * xrs_() &" +
      " cl_() * cr_() = c_() &" +
      " xls_() * xrs_() = xs_()" +
      ") -> l_() * r_() = c_() * xs_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val timesPowersBoth: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesPowersBoth", canonicalName = "timesPowersBoth"),
    ("(((i_() >= 0 & j_() >= 0 & i_() + j_() = k_())<->true) & xs_() * ys_() = xys_())" +
      "->" +
      "(xs_() * x_()^i_()) * (ys_() * x_()^j_()) = xys_() * x_()^k_()").asFormula,
    prop & cutR("x_()^i_()*x_()^j_() = x_()^k_()".asFormula)(1) & Idioms.<(
      useAt(powerLemma, PosInExpr(1 :: Nil))(1) & prop & done,
      implyR(1) & eqR2L(-6)(1) & hideL(-6) & hideL(-3) & eqR2L(-1)(1) & cohideR(1) & QE & done,
    ),
  )

  @Derivation
  lazy val timesPowersLeft: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesPowersLeft", canonicalName = "timesPowersLeft"),
    "(xs_() * ys_() = xys_()) -> xs_() * x_() * (ys_()) = xys_() * x_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val timesPowersRight: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesPowersRight", canonicalName = "timesPowersRight"),
    "(xs_() * ys_() = xys_()) -> xs_() * (ys_()*y_()) = xys_() * y_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val timesPowers1Right: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesPowers1Right", canonicalName = "timesPowers1Right"),
    "xs_() * 1 = xs_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val timesPowers1Left: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesPowers1Left", canonicalName = "timesPowers1Left"),
    "1 * ys_() = ys_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val zez: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "zez", canonicalName = "zez"),
    "0 = 0".asFormula,
    byUS(Ax.equalReflexive),
  )

  @Derivation
  lazy val emptySprout: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "emptySprout", canonicalName = "emptySprout"),
    "s_() = 0 & t_() = u_() -> s_() + t_() = 0 + u_() + 0".asFormula,
    QE & done,
  )

  // @todo: should these be constructed more systematically?! e.g., define common subformulas only once. would make the code more robust...
  @Derivation
  lazy val branch2Left: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch2Left", canonicalName = "branch2Left ", displayName = Some("branch2Left ")),
    "t_() = l_() + v_() + r_() & l_() + x_() = lx_() -> t_() + x_() = lx_() + v_()  + r_() ".asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch2Value: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch2Value", canonicalName = "branch2Value"),
    "t_() = l_() + v_() + r_() & v_() + x_() = vx_() -> t_() + x_() = l_()  + vx_() + r_() ".asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch2Right: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch2Right", canonicalName = "branch2Right"),
    "t_() = l_() + v_() + r_() & r_() + x_() = rx_() -> t_() + x_() = l_()  + v_()  + rx_()".asFormula,
    QE & done,
  )

  /** @note for the Left case, could actually just use [[branch2Left]] */
  @Derivation
  lazy val branch2GrowLeft: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch2GrowLeft", canonicalName = "branch2GrowLeft"),
    "t_() = l_() + v_() + r_() & l_() + x_() = l1_() + lv_() + l2_() -> t_() + x_() = l1_() + lv_() + l2_() + v_() + r_()"
      .asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch2GrowRight: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch2GrowRight", canonicalName = "branch2GrowRight"),
    "t_() = l_() + v_() + r_() & r_() + x_() = r1_() + rv_() + r2_() -> t_() + x_() = l_()                  + v_() + r1_() + rv_() + r2_()"
      .asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch3Left: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch3Left", canonicalName = "branch3Left"),
    "t_() = l_() + v_() + m_() + w_() + r_() & l_() + x_() = lx_() -> t_() + x_() = lx_() + v_()  + m_()  + w_()  + r_() "
      .asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch3Value1: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch3Value1", canonicalName = "branch3Value1"),
    "t_() = l_() + v_() + m_() + w_() + r_() & v_() + x_() = vx_() -> t_() + x_() = l_()  + vx_() + m_()  + w_()  + r_() "
      .asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch3Mid: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch3Mid", canonicalName = "branch3Mid"),
    "t_() = l_() + v_() + m_() + w_() + r_() & m_() + x_() = mx_() -> t_() + x_() = l_()  + v_()  + mx_() + w_()  + r_() "
      .asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch3Value2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch3Value2", canonicalName = "branch3Value2"),
    "t_() = l_() + v_() + m_() + w_() + r_() & w_() + x_() = wx_() -> t_() + x_() = l_()  + v_()  + m_()  + wx_() + r_() "
      .asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch3Right: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch3Right", canonicalName = "branch3Right"),
    "t_() = l_() + v_() + m_() + w_() + r_() & r_() + x_() = rx_() -> t_() + x_() = l_()  + v_()  + m_()  + w_()  + rx_()"
      .asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch3GrowLeft: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch3GrowLeft", canonicalName = "branch3GrowLeft"),
    ("t_() = l_() + v_() + m_() + w_() + r_() & l_() + x_() = l1_() + lv_() + l2_() ->" +
      "t_() + x_() = (l1_() + lv_() + l2_()) + v_()  + (m_()  + w_()  + r_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch3GrowMid: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch3GrowMid", canonicalName = "branch3GrowMid"),
    ("t_() = l_() + v_() + m_() + w_() + r_() & m_() + x_() = m1_() + mv_() + m2_() ->" +
      "t_() + x_() = (l_() + v_() + m1_()) + mv_()  + (m2_()  + w_()  + r_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val branch3GrowRight: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "branch3GrowRight", canonicalName = "branch3GrowRight"),
    ("t_() = l_() + v_() + m_() + w_() + r_() & r_() + x_() = r1_() + rv_() + r2_() ->" +
      "t_() + x_() = (l_() + v_() + m_()) + w_()  + (r1_()  + rv_()  + r2_())").asFormula,
    QE & done,
  )

  // Lemmas for Add

  @Derivation
  lazy val plusEmpty: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "plusEmpty", canonicalName = "plusEmpty"),
    "t_() = s_() & u_() = 0 -> t_() + u_() = s_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val plusBranch2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "plusBranch2", canonicalName = "plusBranch2"),
    ("(s_() = l_() + v_() + r_() & t_() + l_() + v_() + r_() = sum_()) ->" +
      "t_() + s_() = sum_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val plusBranch3: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "plusBranch3", canonicalName = "plusBranch3"),
    ("(s_() = l_() + v1_() + m_() + v2_() + r_() & t_() + l_() + v1_() + m_() + v2_() + r_() = sum_()) ->" +
      "t_() + s_() = sum_()").asFormula,
    QE & done,
  )

  // Lemmas for Minus

  @Derivation
  lazy val minusEmpty: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "minusEmpty", canonicalName = "minusEmpty"),
    "t_() = s_() & u_() = 0 -> t_() - u_() = s_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val minusBranch2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "minusBranch2", canonicalName = "minusBranch2"),
    ("(s_() = l_() + v_() + r_() & t_() - l_() - v_() - r_() = sum_()) ->" +
      "t_() - s_() = sum_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val minusBranch3: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "minusBranch3", canonicalName = "minusBranch3"),
    ("(s_() = l_() + v1_() + m_() + v2_() + r_() & t_() - l_() - v1_() - m_() - v2_() - r_() = sum_()) ->" +
      "t_() - s_() = sum_()").asFormula,
    QE & done,
  )

  // Lemmas for Minus Monomial

  @Derivation
  lazy val plusMinus: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "plusMinus", canonicalName = "plusMinus"),
    "t_() + (-x_()) = s_() -> t_() - x_() = s_()".asFormula,
    QE & done,
  )

  // Lemmas for Times Monomial

  @Derivation
  lazy val monTimesZero: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "monTimesZero", canonicalName = "monTimesZero"),
    "t_() = 0 -> t_() * x_() = 0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val monTimesBranch2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "monTimesBranch2", canonicalName = "monTimesBranch2"),
    ("(t_() = l_() + v_() + r_() &" +
      "l_() * x_() = lx_() &" +
      "v_() * x_() = vx_() &" +
      "r_() * x_() = rx_()) -> t_() * x_() = lx_() + vx_() + rx_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val monTimesBranch3: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "monTimesBranch3", canonicalName = "monTimesBranch3"),
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() &" +
      "l_() * x_() = lx_() &" +
      "v1_() * x_() = v1x_() &" +
      "m_() * x_() = mx_() &" +
      "v2_() * x_() = v2x_() &" +
      "r_() * x_() = rx_()) -> t_() * x_() = lx_() + v1x_() + mx_() + v2x_() + rx_()").asFormula,
    QE & done,
  )

  // Lemmas for Times

  @Derivation
  lazy val timesEmpty: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesEmpty", canonicalName = "timesEmpty"),
    "t_() = 0 -> t_() * u_() = 0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val timesBranch2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesBranch2", canonicalName = "timesBranch2"),
    ("(t_() = l_() + v_() + r_() & l_()*u_() + u_() * v_() + r_()*u_() = sum_()) ->" +
      "t_() * u_() = sum_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val timesBranch3: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesBranch3", canonicalName = "timesBranch3"),
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() & l_()*u_() + u_()*v1_() + m_()*u_() + u_()*v2_() + r_()*u_() = sum_()) ->" +
      "t_() * u_() = sum_()").asFormula,
    QE & done,
  )

  // Lemmas for Power

  @Derivation
  lazy val powerZero: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerZero", canonicalName = "powerZero"),
    "1 = one_() -> t_() ^ 0 = one_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val powerOne: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerOne", canonicalName = "powerOne"),
    "t_() = s_() -> t_() ^ 1 = s_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val powerEven: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerEven", canonicalName = "powerEven"),
    ("((n_() = 2*m_() <-> true) & t_()^m_() = p_() & p_()*p_() = r_()) ->" +
      "t_() ^ n_() = r_()").asFormula,
    implyR(1) & andL(-1) & andL(-2) &
      useAt(Ax.equivTrue, PosInExpr(0 :: Nil))(-1) &
      eqL2R(-1)(1) & hideL(-1) &
      cutR("t_() ^ (2*m_()) = (t_()^m_())^2".asFormula)(1) & Idioms
        .<(QE & done, implyR(1) & eqL2R(-3)(1) & hideL(-3) & eqL2R(-1)(1) & hideL(-1) & QE & done),
  )

  @Derivation
  lazy val powerOdd: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerOdd", canonicalName = "powerOdd"),
    ("((n_() = 2*m_() + 1 <-> true) & t_()^m_() = p_() & p_()*p_()*t_() = r_()) ->" +
      "t_() ^ n_() = r_()").asFormula,
    implyR(1) & andL(-1) & andL(-2) &
      useAt(Ax.equivTrue, PosInExpr(0 :: Nil))(-1) &
      eqL2R(-1)(1) & hideL(-1) &
      cutR("t_() ^ (2*m_() + 1) = (t_()^m_())^2*t_()".asFormula)(1) & Idioms
        .<(QE & done, implyR(1) & eqL2R(-3)(1) & hideL(-3) & eqL2R(-1)(1) & hideL(-1) & QE & done),
  )

  @Derivation
  lazy val powerPoly: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerPoly", canonicalName = "powerPoly"),
    "(q_() = i_() & p_()^i_() = r_()) -> p_()^q_() = r_()".asFormula,
    implyR(1) & andL(-1) &
      eqL2R(-1)(1, 0 :: 1 :: Nil) &
      hideL(-1) &
      id,
  )

  // Lemmas for division

  @Derivation
  lazy val divideNumber: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divideNumber", canonicalName = "divideNumber"),
    "(q_() = i_() & p_()*(1/i_()) = r_()) -> p_()/q_() = r_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val divideRat: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divideRat", canonicalName = "divideRat"),
    "(q_() = n_()/d_() & p_()*(d_()/n_()) = r_()) -> p_()/q_() = r_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val divideNeg: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divideNeg", canonicalName = "divideNeg"),
    "-(p_()/(-q_())) = r_() -> p_()/q_() = r_()".asFormula,
    QE & done,
  )

  // Lemmas for negation

  @Derivation
  lazy val negateEmpty: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "negateEmpty", canonicalName = "negateEmpty"),
    "t_() = 0 -> -t_() = 0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val negateBranch2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "negateBranch2", canonicalName = "negateBranch2"),
    ("(t_() = l_() + v_() + r_() & -l_() = nl_() & -v_() = nv_() & -r_() = nr_()) ->" +
      "-t_() = nl_() + nv_() + nr_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val negateBranch3: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "negateBranch3", canonicalName = "negateBranch3"),
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() & -l_() = nl_() & -v1_() = nv1_() & -m_() = nm_() & -v2_() = nv2_() & -r_() = nr_()) ->" +
      "-t_() = nl_() + nv1_() + nm_() + nv2_() + nr_()").asFormula,
    QE & done,
  )

  // Lemmas for normalization

  @Derivation
  lazy val normalizeCoeff0: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizeCoeff0", canonicalName = "normalizeCoeff0"),
    "(c_() = 0 / d_() ) -> c_() = 0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizeCoeff1: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizeCoeff1", canonicalName = "normalizeCoeff1"),
    "(c_() = n_() / 1 ) -> c_() = n_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizeMonom0: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizeMonom0", canonicalName = "normalizeMonom0"),
    "(x_() = c_() * ps_() & c_() = 0) -> x_() = 0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizeMonomCS: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizeMonomCS", canonicalName = "normalizeMonomCS"),
    ("(x_() = c_() * ps_() & c_() * ps_() = cps_()) ->" +
      "x_() = cps_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizeMonomNCS: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizeMonomNCS", canonicalName = "normalizeMonomNCS"),
    ("(x_() = c_() * ps_() & -c_() = m_() & m_() * ps_() = cps_()) ->" +
      "x_() = -cps_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizePowers1V: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizePowers1V", canonicalName = "normalizePowers1V"),
    "(c_() = 1) -> c_() * (1 * v_()^1) = v_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizePowers1R: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizePowers1R", canonicalName = "normalizePowers1R"),
    "(c_() = 1) -> c_() * (1 * t_()) = t_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizePowersC1: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizePowersC1", canonicalName = "normalizePowersC1"),
    "(c_() = d_()) -> c_() * 1 = d_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizePowersCV: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizePowersCV", canonicalName = "normalizePowersCV"),
    "(c_() = d_()) -> c_() * (1 * v_()^1) = d_()*v_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizePowersCP: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizePowersCP", canonicalName = "normalizePowersCP"),
    "(c_() = d_()) -> c_() * (1 * t_()) = d_()*t_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizePowersRV: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizePowersRV", canonicalName = "normalizePowersRV"),
    "(c_() * ps_() = cps_()) -> c_() * (ps_() * v_()^1) = cps_() * v_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizePowersRP: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizePowersRP", canonicalName = "normalizePowersRP"),
    "(c_() * ps_() = cps_()) -> c_() * (ps_() * t_()) = cps_() * t_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizeBranch2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizeBranch2", canonicalName = "normalizeBranch2"),
    ("(t_() = l_() + v_() + r_() & l_() = ln_() & v_() = vn_() & r_() = rn_()) ->" +
      "t_() = ln_() + vn_() + rn_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val normalizeBranch3: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "normalizeBranch3", canonicalName = "normalizeBranch3"),
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() & l_() = ln_() & v1_() = v1n_() & m_() = mn_() & v2_() = v2n_() & r_() = rn_()) ->" +
      "t_() = ln_() + v1n_() + mn_() + v2n_() + rn_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val reassocRight0: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "reassocRight0", canonicalName = "reassocRight0"),
    ("(" +
      "t_() = l_() + r_() &" +
      "r_() = 0   &" +
      "l_() = ll_()" +
      ") ->" +
      "t_() = ll_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val reassocRightPlus: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "reassocRightPlus", canonicalName = "reassocRightPlus"),
    ("(" +
      "t_() = l_() + r_() &" +
      "r_() = rs_() + rr_() &" +
      "l_() + rs_() = lrs_()" +
      ") ->" +
      "t_() = lrs_() + rr_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val reassocLeft0RightConst: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "reassocLeft0RightConst", canonicalName = "reassocLeft0RightConst"),
    ("(" +
      "t_() = l_() + r_() &" +
      "r_() = c_() &" +
      "l_() = 0" +
      ") ->" +
      "t_() = c_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val reassocRightConst: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "reassocRightConst", canonicalName = "reassocRightConst"),
    ("(" +
      "t_() = l_() + r_() &" +
      "r_() = c_() &" +
      "l_() = ll_()" +
      ") ->" +
      "t_() = ll_() + c_()").asFormula,
    QE & done,
  )

  // lemmas to prove equality

  @Derivation
  lazy val equalityBySubtraction: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "equalityBySubtraction", canonicalName = "equalityBySubtraction"),
    "t_() - s_() = 0 -> t_() = s_()".asFormula,
    QE & done,
  )

  // Lemmas for partition
  @Derivation
  lazy val partition2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "partition2", canonicalName = "partition2"),
    "(t_() = r_() & t1_() = r1_() & t2_() = r2_() & t_() - t1_() - t2_() = 0) -> t_() = t1_() + t2_()".asFormula,
    QE & done,
  )

  // Lemmas for splitting coefficients

  @inline
  private def nz(t: Term): Formula = NotEqual(t, Number(0))

  @inline
  def splitCoefficientNumericCondition(n: Term, d: Term, n1: Term, d1: Term, n2: Term, d2: Term): Formula =
    And(Equal(Times(Times(n, d1), d2), Times(d, Plus(Times(d1, n2), Times(d2, n1)))), And(nz(d), And(nz(d1), nz(d2))))

  @Derivation
  lazy val splitCoefficient: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "splitCoefficient", canonicalName = "splitCoefficient"),
    Imply(
      And(
        "c_() = n_()/d_()".asFormula,
        Equiv(
          splitCoefficientNumericCondition(
            "n_()".asTerm,
            "d_()".asTerm,
            "n1_()".asTerm,
            "d1_()".asTerm,
            "n2_()".asTerm,
            "d2_()".asTerm,
          ),
          True,
        ),
      ),
      "c_() = n1_()/d1_() + n2_()/d2_()".asFormula,
    ),
    QE & done,
  )

  @Derivation
  lazy val splitMonomial: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "splitMonomial", canonicalName = "splitMonomial"),
    "(c_() = c1_() + c2_() & m_() = c_() * x_()) -> m_() = c1_() * x_() + c2_() * x_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val splitEmpty: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "splitEmpty", canonicalName = "splitEmpty ", displayName = Some("splitEmpty ")),
    "t_() = 0 -> t_() = 0 + 0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val splitBranch2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo
      .create(name = "splitBranch2", canonicalName = "splitBranch2 ", displayName = Some("splitBranch2 ")),
    ("(t_() = l_() + v_() + r_() & l_() = l1_() + l2_() & v_() = v1_() + v2_() & r_() = r1_() + r2_())" +
      "->" +
      "t_() = (l1_() + v1_() + r1_()) + (l2_() + v2_() + r2_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val splitBranch3: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo
      .create(name = "splitBranch3", canonicalName = "splitBranch3 ", displayName = Some("splitBranch3 ")),
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() & l_() = l1_() + l2_() & v1_() = v11_() + v12_() & m_() = m1_() + m2_() & v2_() = v21_() + v22_() & r_() = r1_() + r2_())" +
      "->" +
      "t_() = (l1_() + v11_() + m1_() + v21_() + r1_()) + (l2_() + v12_() + m2_() + v22_() + r2_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val varPowerLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "varPowerLemma", canonicalName = "varPowerLemma"),
    "v_()^n_() = 0 + 1 / 1 * (1 * v_()^n_()) + 0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val varLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "varLemma", canonicalName = "varLemma"),
    "v_() = 0 + 1 / 1 * (1 * v_()^1) + 0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val constLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "constLemma", canonicalName = "constLemma"),
    Equal(
      "n_()".asTerm,
      Seq(Number(0), Times(Divide("n_()".asTerm, Number(1)), Number(1)), Number(0)).reduceLeft(Plus),
    ),
    QE & done,
  )

  @Derivation
  lazy val rationalLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "rationalLemma", canonicalName = "rationalLemma"),
    Equal("n_() / d_()".asTerm, Seq(Number(0), Times("n_()/d_()".asTerm, Number(1)), Number(0)).reduceLeft(Plus)),
    QE & done,
  )

  // Power of Divide

  @Derivation
  lazy val powerDivide0: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerDivide0", canonicalName = "powerDivide0"),
    "(x_()/y_()) ^ 0 = x_()^0 / y_()^0".asFormula,
    QE & done,
  )

  @Derivation
  lazy val powerDivideEven: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerDivideEven", canonicalName = "powerDivideEven"),
    ("(" +
      " (n_() = 2*m_() <-> true) &" +
      " (x_()/y_())^m_() = x_() ^ m_() / y_() ^ m_()" +
      ") ->" +
      "(x_()/y_())^n_() = x_()^n_() / y_()^n_()").asFormula,
    prop &
      useAt(
        Ax.powerEven,
        PosInExpr(1 :: Nil),
        (subst: Option[Subst]) =>
          subst.getOrElse(RenUSubst(Seq())) ++ RenUSubst(Seq(("p_()".asTerm, "x_()^m_()/y_()^m_()".asTerm))),
      )(1) &
      andR(1) & Idioms.<(
        useAt(Ax.equivTrue)(1) & id,
        andR(1) & Idioms.<(
          id,
          useAt(
            Ax.ratFormTimes,
            PosInExpr(1 :: Nil),
            (subst: Option[Subst]) =>
              subst.getOrElse(RenUSubst(Seq())) ++ RenUSubst(Seq(
                ("nx_()".asTerm, "x_()^m_()".asTerm),
                ("dx_()".asTerm, "y_()^m_()".asTerm),
                ("ny_()".asTerm, "x_()^m_()".asTerm),
                ("dy_()".asTerm, "y_()^m_()".asTerm),
              )),
          )(1) &
            andR(1) & Idioms.<(
              cohideR(1) & byUS(Ax.equalReflexive),
              andR(1) & Idioms.<(
                cohideR(1) & byUS(Ax.equalReflexive),
                andR(1) & Idioms.<(
                  useAt(Ax.equalSym, PosInExpr(1 :: 0 :: Nil))(1) & Idioms.<(
                    closeT,
                    useAt(
                      Ax.powerEven,
                      PosInExpr(1 :: Nil),
                      (
                        subst: Option[Subst]
                      ) => subst.getOrElse(RenUSubst(Seq())) ++ RenUSubst(Seq(("p_()".asTerm, "x_()^m_()".asTerm))),
                    )(1) &
                      andR(1) & Idioms.<(prop & done, prop & OnAll(cohideR(1) & byUS(Ax.equalReflexive))),
                  ),
                  useAt(Ax.equalSym, PosInExpr(1 :: 0 :: Nil))(1) & Idioms.<(
                    closeT,
                    useAt(
                      Ax.powerEven,
                      PosInExpr(1 :: Nil),
                      (
                        subst: Option[Subst]
                      ) => subst.getOrElse(RenUSubst(Seq())) ++ RenUSubst(Seq(("p_()".asTerm, "y_()^m_()".asTerm))),
                    )(1) &
                      andR(1) & Idioms.<(prop & done, prop & OnAll(cohideR(1) & byUS(Ax.equalReflexive))),
                  ),
                ),
              ),
            ),
        ),
      ),
  )

  @Derivation
  lazy val powerDivideOdd: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "powerDivideOdd", canonicalName = "powerDivideOdd"),
    ("((n_() = 2*m_()+1 <-> true) & (x_()/y_())^m_() = x_() ^ m_() / y_() ^ m_()) ->" +
      "(x_()/y_())^n_() = x_()^n_() / y_()^n_()").asFormula,
    prop &
      useAt(
        Ax.powerOdd,
        PosInExpr(1 :: Nil),
        (subst: Option[Subst]) =>
          subst.getOrElse(RenUSubst(Seq())) ++ RenUSubst(Seq(("p_()".asTerm, "x_()^m_()/y_()^m_()".asTerm))),
      )(1) &
      andR(1) & Idioms.<(
        useAt(Ax.equivTrue)(1) & id,
        andR(1) & Idioms.<(
          id,
          cut(
            ("x_()^m_()/y_()^m_()*(x_()^m_()/y_()^m_())*(x_()/y_()) =" +
              "(x_()^m_()*x_()^m_()*x_())/(y_()^m_()*y_()^m_()*y_())").asFormula
          ) &
            Idioms.<(
              eqL2R(-4)(1) & hideL(-4) &
                cut("x_()^n_() = x_()^m_()*x_()^m_()*x_()".asFormula) & Idioms.<(
                  eqR2L(-4)(1) & hideL(-4) &
                    cut("y_()^n_() = y_()^m_()*y_()^m_()*y_()".asFormula) & Idioms.<(
                      eqR2L(-4)(1) & hideL(-4) & cohideR(1) & byUS(Ax.equalReflexive),
                      hideR(1) & useAt(
                        Ax.powerOdd,
                        PosInExpr(1 :: Nil),
                        (
                          subst: Option[Subst]
                        ) => subst.getOrElse(RenUSubst(Seq())) ++ RenUSubst(Seq(("p_()".asTerm, "y_()^m_()".asTerm))),
                      )(1) &
                        andR(1) & Idioms.<(prop & done, prop & OnAll(cohideR(1) & byUS(Ax.equalReflexive))),
                    ),
                  hideR(1) & useAt(
                    Ax.powerOdd,
                    PosInExpr(1 :: Nil),
                    (
                      subst: Option[Subst]
                    ) => subst.getOrElse(RenUSubst(Seq())) ++ RenUSubst(Seq(("p_()".asTerm, "x_()^m_()".asTerm))),
                  )(1) &
                    andR(1) & Idioms.<(prop & done, prop & OnAll(cohideR(1) & byUS(Ax.equalReflexive))),
                ),
              cohideR(2) & QE & done,
            ),
        ),
      ),
  )

  // Lemmas for rational forms

  @Derivation
  lazy val ratFormAdd: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "ratFormAdd", canonicalName = "ratFormAdd"),
    ("(x_() = nx_() / dx_() &" +
      "y_() = ny_() / dy_() &" +
      "gcd_() * rx_() = dx_() &" +
      "gcd_() * ry_() = dy_() &" +
      "nx_() * ry_() + ny_() * rx_() = nz_() &" +
      "rx_() * gcd_() * ry_() = dz_())" +
      "->" +
      "x_() + y_() = nz_() / dz_()").asFormula,
    implyR(1) & andL(Symbol("Llast")) * 5 &
      (eqL2R(-1)(1) & hideL(-1)) * 2 &
      (eqR2L(-1)(1) & hideL(-1)) * 4 &
      QE & done,
  )

  @Derivation
  lazy val ratFormMinus: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "ratFormMinus", canonicalName = "ratFormMinus"),
    ("(x_() = nx_() / dx_() &" +
      "y_() = ny_() / dy_() &" +
      "gcd_() * rx_() = dx_() &" +
      "gcd_() * ry_() = dy_() &" +
      "nx_() * ry_() - ny_() * rx_() = nz_() &" +
      "rx_() * gcd_() * ry_() = dz_())" +
      "->" +
      "x_() - y_() = nz_() / dz_()").asFormula,
    implyR(1) & andL(Symbol("Llast")) * 5 &
      (eqL2R(-1)(1) & hideL(-1)) * 2 &
      (eqR2L(-1)(1) & hideL(-1)) * 4 &
      QE & done,
  )

  @Derivation
  lazy val ratFormDivide: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "ratFormDivide", canonicalName = "ratFormDivide"),
    ("(x_() = nx_() / dx_() &" +
      "y_() = ny_() / dy_() &" +
      "nx_() * dy_() = nz_() &" +
      "ny_() * dx_() = dz_())" +
      "->" +
      "x_() / y_() = nz_() / dz_()").asFormula,
    implyR(1) & andL(Symbol("Llast")) * 3 &
      (eqL2R(-1)(1) & hideL(-1)) * 2 &
      (eqR2L(-1)(1) & hideL(-1)) * 2 &
      QE & done,
  )

  @Derivation
  lazy val ratFormTimes: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "ratFormTimes", canonicalName = "ratFormTimes"),
    ("(x_() = nx_() / dx_() &" +
      "y_() = ny_() / dy_() &" +
      "nx_() * ny_() = nz_() &" +
      "dx_() * dy_() = dz_())" +
      "->" +
      "x_() * y_() = nz_() / dz_()").asFormula,
    implyR(1) & andL(Symbol("Llast")) * 3 &
      (eqL2R(-1)(1) & hideL(-1)) * 2 &
      (eqR2L(-1)(1) & hideL(-1)) * 2 &
      QE & done,
  )

  @Derivation
  lazy val ratFormPower: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "ratFormPower", canonicalName = "ratFormPower"),
    ("(x_() = nx_() / dx_() &" +
      "y_() = ny_() / dy_() &" +
      "ny_() / dy_() = m_() & " +
      "(nx_() / dx_())^m_() = nx_()^m_() / dx_() ^ m_() &" +
      "nx_()^m_() = nz_() &" +
      "dx_()^m_() = dz_()" +
      ")" +
      "->" +
      "x_() ^ y_() = nz_() / dz_()").asFormula,
    implyR(1) & andL(Symbol("Llast")) * 5 &
      (eqL2R(-1)(1) & hideL(-1)) * 6 &
      cohideR(1) & byUS(Ax.equalReflexive),
  )

  @Derivation
  lazy val ratFormNeg: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "ratFormNeg", canonicalName = "ratFormNeg"),
    ("(x_() = nx_() / dx_() &" +
      "-nx_() = nz_())" +
      "->" +
      "-x_() = nz_() / dx_()").asFormula,
    implyR(1) & andL(Symbol("Llast")) * 1 &
      (eqL2R(-1)(1) & hideL(-1)) * 1 &
      (eqR2L(-1)(1) & hideL(-1)) * 1 &
      QE & done,
  )

  @Derivation
  lazy val divideIdentity: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "divideIdentity", canonicalName = "divideIdentity"),
    "(x_() = y_() & 1 = z_()) -> x_() = y_() / z_()".asFormula,
    QE & done,
  )

  // Taylor Model Arithmetic [[org.keymaerax.btactics.TaylorModelArith]]

  @Derivation
  lazy val taylorModelPlusPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelPlusPrv", canonicalName = "taylorModelPlusPrv"),
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() + poly2_() = poly_() &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ + i2_ & i1_ + i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() + elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelMinusPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelMinusPrv", canonicalName = "taylorModelMinusPrv"),
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() - poly2_() = poly_() &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ - i2_ & i1_ - i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() - elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelCollectPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelCollectPrv", canonicalName = "taylorModelCollectPrv"),
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "poly1_() = polyLow_() + polyHigh_() &" +
      "polyLow_() = poly_() &" +
      "polyHigh_() = rem_() & " +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= rem_() + i1_ & rem_() + i1_  <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelPartitionPrv1: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelPartitionPrv1", canonicalName = "taylorModelPartitionPrv1"),
    ("((\\exists err_ (elem_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "poly_() = polyTrue_() + polyFalse_() & " +
      "newElem_() = elem_() - polyTrue_() & " +
      "newElem_() + polyTrue_() = poly1_() & " +
      "polyFalse_() = poly2_()" +
      ") ->" +
      "\\exists err_ (elem_() = poly1_() + err_ & 0 <= err_ & err_ <= 0)").asFormula,
    QE & done,
  )
  @Derivation
  lazy val taylorModelPartitionPrv2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelPartitionPrv2", canonicalName = "taylorModelPartitionPrv2"),
    ("((\\exists err_ (elem_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "poly_() = polyTrue_() + polyFalse_() & " +
      "newElem_() = elem_() - polyTrue_() & " +
      "newElem_() + polyTrue_() = poly1_() & " +
      "polyFalse_() = poly2_()" +
      ") ->" +
      "\\exists err_ (newElem_() = poly2_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelTransElem: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelTransElem", canonicalName = "taylorModelTransElem"),
    ("((\\exists err_ (elem_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "elem1_() = elem_()) ->" +
      "\\exists err_ (elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelIntervalPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelIntervalPrv", canonicalName = "taylorModelIntervalPrv"),
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "poly1_() = rem_() &" +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= rem_() + i1_ & rem_() + i1_  <= u_())))" +
      ") ->" +
      "l_() <= elem1_() & elem1_() <= u_()").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelEmptyIntervalPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelEmptyIntervalPrv", canonicalName = "taylorModelEmptyIntervalPrv"),
    "(\\exists err_ (elem1_() = poly1_() + err_ & 0 <= err_ & err_ <= 0)) -> elem1_() = poly1_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelTimesPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelTimesPrv", canonicalName = "taylorModelTimesPrv"),
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() * poly2_() = polyLow_() + polyHigh_() &" +
      "polyLow_() = poly_() &" +
      "polyHigh_() = rem_() & " +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= rem_() + i1_ * poly2_() + i2_ * poly1_() + i1_ * i2_ & rem_() + i1_ * poly2_() + i2_ * poly1_() + i1_ * i2_ <= u_())))" + // @todo: horner form for poly1, poly2 ?!
      ") ->" +
      "\\exists err_ (elem1_() * elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & andL(-3) & andL(-4) & andL(-5) & existsL(-1) & existsL(-1) & allL(
      "err__0".asTerm
    )(-4) & allL("err_".asTerm)(-4) &
      existsR("rem_() + err__0 * poly2_() + err_ * poly1_() + err__0 * err_".asTerm)(1) & QE & done,
  )

  @Derivation
  lazy val taylorModelDivideExactPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelDivideExactPrv", canonicalName = "taylorModelDivideExactPrv"),
    ("((\\exists err_ (elem1_() * inv_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "elem1_()/elem2_() = elem1_() * inv_()" +
      ") ->" +
      "\\exists err_ (elem1_() / elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & eqL2R(-2)(1) & id,
  )

  @Derivation
  lazy val taylorModelSquarePrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "taylorModelSquarePrv",
      canonicalName = "taylorModelSquarePrv",
    ), // @todo: is there a better scheme than just multiplication?
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "poly1_()^2 = polyLow_() + polyHigh_() &" +
      "polyLow_() = poly_() &" +
      "polyHigh_() = rem_() & " +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= rem_() + 2 * i1_ * poly1_() + i1_^2 & rem_() + 2 * i1_ * poly1_() + i1_^2 <= u_())))" + // @todo: horner form for poly1 ?!
      ") ->" +
      "\\exists err_ (elem1_()^2 = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & andL(-3) & andL(-4) & existsL(-1) & allL("err_".asTerm)(-4) &
      existsR("rem_() + 2 * err_ * poly1_() + err_^2".asTerm)(1) & QE & done,
  )

  @Derivation
  lazy val taylorModelPowerOne: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelPowerOne", canonicalName = "taylorModelPowerOne"),
    ("(\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_()))" +
      " ->" +
      "\\exists err_ (elem1_()^1 = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelPowerEven: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelPowerEven", canonicalName = "taylorModelPowerEven"),
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ ((elem1_()^m_())^2 = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "(n_() = 2*m_() <-> true)" +
      ")" +
      "->" +
      "\\exists err_ (elem1_()^n_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & cut("(elem1_()^m_())^2 = elem1_()^(2*m_())".asFormula) & Idioms.<(
      eqL2R(-4)(-2) & hideL(-4) & useAt(Ax.equivTrue, PosInExpr(0 :: Nil))(-3) & eqR2L(-3)(-2) & QE & done,
      cohideR(2) & QE & done,
    ),
  )

  @Derivation
  lazy val taylorModelPowerOdd: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelPowerOdd", canonicalName = "taylorModelPowerOdd"),
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ ((elem1_()^m_())^2*elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "(n_() = 2*m_() + 1 <-> true)" +
      ")" +
      "->" +
      "\\exists err_ (elem1_()^n_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & cut("(elem1_()^m_())^2*elem1_() = elem1_()^(2*m_() + 1)".asFormula) & Idioms.<(
      eqL2R(-4)(-2) & hideL(-4) & useAt(Ax.equivTrue, PosInExpr(0 :: Nil))(-3) & eqR2L(-3)(-2) & QE & done,
      cohideR(2) & QE & done,
    ),
  )

  @Derivation
  lazy val taylorModelNegPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelNegPrv", canonicalName = "taylorModelNegPrv"),
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "-poly1_() = poly_() &" +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= -i1_ & -i1_ <= u_())))" +
      ") ->" +
      "\\exists err_ (-elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelExactPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelExactPrv", canonicalName = "taylorModelExactPrv"),
    ("elem_() = poly_() ->" +
      "\\exists err_ (elem_() = poly_() + err_ & 0 <= err_ & err_ <= 0)").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelApproxPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelApproxPrv", canonicalName = "taylorModelApproxPrv"),
    ("(" +
      "\\exists err_ (elem_() = poly_() + err_ & l_() <= err_ & err_ <= u_()) &" +
      "poly_() = poly1_() + poly2_() &" +
      "poly1_() = poly1rep_() &" +
      "poly2_() = poly2rep_() &" +
      "(\\forall i1_ (l_() <= i1_ & i1_ <= u_() ->" +
      "   l2_() <= poly2rep_() + i1_ & poly2rep_() + i1_ <= u2_()))" +
      ") ->" +
      "\\exists err_ (elem_() = poly1rep_() + err_ & l2_() <= err_ & err_ <= u2_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelEvalPrv: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelEvalPrv", canonicalName = "taylorModelEvalPrv"),
    ("(" +
      "\\exists err_ (elem_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_()) &" +
      "poly1_() = polyrep_() &" +
      "\\exists err_ (polyrep_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_()) &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ + i2_ & i1_ + i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem_() = poly2_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Derivation
  lazy val refineTmExists: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "refineTmExists", canonicalName = "refineTmExists"),
    "(\\forall err_ (P(err_) -> Q(err_))) -> ((\\exists x_ P(x_)) -> (\\exists err_ Q(err_)))".asFormula,
    implyR(1) & implyR(1) & existsL(-2) & existsR("x_".asVariable)(1) & allL("x_".asVariable)(-1) & prop & done,
  )

  @Derivation
  lazy val taylorModelIntervalLe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelIntervalLe", canonicalName = "taylorModelIntervalLe"),
    "((l_() <= f_() - g_() & f_() - g_() <= u_()) & (u_() <= 0 <-> true)) -> f_() <= g_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelIntervalLt: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelIntervalLt", canonicalName = "taylorModelIntervalLt"),
    "((l_() <= f_() - g_() & f_() - g_() <= u_()) & (u_() < 0 <-> true)) -> f_() < g_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelIntervalGe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelIntervalGe", canonicalName = "taylorModelIntervalGe"),
    "((l_() <= f_() - g_() & f_() - g_() <= u_()) & (l_() >= 0 <-> true)) -> f_() >= g_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val taylorModelIntervalGt: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "taylorModelIntervalGt", canonicalName = "taylorModelIntervalGt"),
    "((l_() <= f_() - g_() & f_() - g_() <= u_()) & (l_() > 0 <-> true)) -> f_() > g_()".asFormula,
    QE & done,
  )

  // Taylor Model [[org.keymaerax.btactics.TaylorModelTactics]]

  @Derivation
  lazy val unfoldExistsLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "unfoldExistsLemma", canonicalName = "unfoldExistsLemma"),
    "\\exists x_ (r_() = s_() + x_ & P_(x_)) <-> P_(r_()-s_())".asFormula,
    prop & Idioms.<(
      existsL(-1) & andL(-1) & cutR("r_() - s_() = x_".asFormula)(1) & Idioms
        .<(QE & done, implyR(1) & eqL2R(-3)(1) & id),
      existsR("r_() - s_()".asTerm)(1) & prop & QE & done,
    ),
  )

  @Derivation
  lazy val foldAndLessEqExistsLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "foldAndLessEqExistsLemma", canonicalName = "foldAndLessEqExistsLemma"),
    ("(a() <= x_ - b() & x_ - b() <= c()) <->" +
      "(\\exists xr_ (x_ = xr_ + b() & (a() <= xr_ & xr_ <= c())))").asFormula,
    QE & done,
  )

  @Derivation
  lazy val leTimesMonoLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "leTimesMonoLemma", canonicalName = "leTimesMonoLemma"),
    "0 <= t_() & t_() <= h_() -> R_() <= t_() * U_() + cU_() -> R_() <= max((0,h_() * U_())) + cU_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val timesLeMonoLemma: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "timesLeMonoLemma", canonicalName = "timesLeMonoLemma"),
    "0 <= t_() & t_() <= h_() -> t_() * L_() + cL_() <= U_() -> min((0,h_() * L_())) + cL_() <= U_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val minGtNorm: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "minGtNorm", canonicalName = "minGtNorm"),
    "min((f_(),g_()))>h_()<->(f_()>h_()&g_()>h_())".asFormula,
    QE & done,
  )

  @Derivation
  lazy val minLeNorm: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "minLeNorm", canonicalName = "minLeNorm"),
    "min((f_(),g_()))<=h_()<->(f_()<=h_()|g_()<=h_())".asFormula,
    QE & done,
  )

  @Derivation
  lazy val minGeNorm: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "minGeNorm", canonicalName = "minGeNorm"),
    "min((f_(),g_()))>=h_()<->(f_()>=h_()&g_()>=h_())".asFormula,
    QE & done,
  )

  @Derivation
  lazy val leMaxNorm: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "leMaxNorm", canonicalName = "leMaxNorm"),
    "h_()<=max((f_(),g_()))<->(h_()<=f_()|h_()<=g_())".asFormula,
    QE & done,
  )

  @Derivation
  lazy val trivialInequality: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "trivialInequality", canonicalName = "trivialInequality"),
    "(x_() = 0 & y_() = 0) -> x_() <= y_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val refineConjunction: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "refineConjunction", canonicalName = "refineConjunction"),
    "((f_() -> h_()) & (g_() -> i_())) -> ((f_() & g_()) -> (h_() & i_()))".asFormula,
    prop & done,
  )

  @Derivation
  lazy val refineLe1: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "refineLe1", canonicalName = "refineLe1"),
    "g()<=h()->(f()<=g()->f()<=h())".asFormula,
    QE & done,
  )

  @Derivation
  lazy val refineLe2: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "refineLe2", canonicalName = "refineLe2"),
    "h()<=f()->(f()<=g()->h()<=g())".asFormula,
    QE & done,
  )

  @Derivation
  lazy val trivialRefineLtGt: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "trivialRefineLtGt", canonicalName = "trivialRefineLtGt"),
    "(w_() - v_() + y_() - x_() = 0) -> (v_() < w_() -> x_() > y_())".asFormula,
    QE & done,
  )

  @Derivation
  lazy val trivialRefineGeLe: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "trivialRefineGeLe", canonicalName = "trivialRefineGeLe"),
    "(v_() - w_() - y_() + x_() = 0) -> (v_() >= w_() -> x_() <= y_())".asFormula,
    QE & done,
  )

  @Derivation
  lazy val eqAddIff: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "eqAddIff", canonicalName = "eqAddIff"),
    "f_() = g_() + h_() <-> h_() = f_() - g_()".asFormula,
    QE & done,
  )

  @Derivation
  lazy val plusDiffRefl: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "plusDiffRefl", canonicalName = "plusDiffRefl"),
    "f_() = g_() + (f_() - g_())".asFormula,
    QE & done,
  )

  // ODELiveness

  @Derivation
  lazy val TExge: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "TExge", canonicalName = "TExge"),
    "<{gextimevar_'=1}> (gextimevar_ >= p())".asFormula,
    solve(1) & QE & done,
  )

  @Derivation
  lazy val TExgt: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(name = "TExgt", canonicalName = "TExgt"),
    "<{gextimevar_'=1}> (gextimevar_ > p())".asFormula,
    solve(1) & QE & done,
  )

  @Derivation
  lazy val commaCommuteD: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo
      .create(name = "commaCommuteD", canonicalName = "commaCommuteD", displayName = Some(", commute diamond")),
    "<{c,d&q(||)}>p(||) <-> <{d,c&q(||)}>p(||)".asFormula,
    prop < (
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(-1) & useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) &
        notL(-1) & notR(1) & useAt(Ax.commaCommute)(1) & close,
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(-1) & useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) &
        notL(-1) & notR(1) & useAt(Ax.commaCommute)(1) & close
    ),
  )

  /* ODEInvariance */

  @Derivation
  lazy val dBarcan: DerivedAxiomInfo = derivedAxiom(
    DerivedAxiomInfo.create(
      name = "dBarcan",
      canonicalName = "D Barcan",
      displayName = Some("D Barcan"),
      displayLevel = DisplayLevel.All,
      displayConclusion = "∃x<a>p(x)__ ↔ <a>∃x p(x) (x∉a)",
      key = "0",
      recursor = "0",
      unifier = Unifier.SurjectiveLinear,
    ),
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ <a{|^@x_|};>p(||) <-> <a{|^@x_|};>\\exists x_ p(||)".asFormula)),
    diamondd(1, 1 :: Nil) &
      diamondd(1, 0 :: 0 :: Nil) &
      useAt(Ax.existsDual, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(Ax.doubleNegation)(1, 0 :: 0 :: 0 :: Nil) &
      useAt(Ax.notExists)(1, 1 :: 0 :: 1 :: Nil) &
      useAt(Ax.barcan)(1, 1 :: 0 :: Nil) &
      byUS(Ax.equivReflexive),
  )
}
