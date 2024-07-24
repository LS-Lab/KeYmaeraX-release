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
 * =Adding Derived Axioms and Derived Axiomatic Rules=
 *
 * Core Axioms are loaded from the core and their meta information is annotated in this file e.g. as follows:
 * {{{
 *   @Axiom(
 *     name = "choiceb",
 *     displayName = Some("[∪]"),
 *     displayNameAscii = Some("[++]"),
 *     displayConclusion = "__[a∪b]P__↔[a]P∧[b]P",
 *     key = "0",
 *     recursor = "0;1",
 *     unifier = Unifier.SurjectiveLinear,
 *   )
 *   val choiceb = coreAxiom("[++] choice")
 * }}}
 *
 * Derived Axioms are proved with a tactic and their meta information is annotated in this file e.g. as follows:
 * {{{
 *   @Axiom(
 *     name = "V",
 *     displayConclusion = "p→__[a]p__",
 *     key = "1",
 *     recursor = "*",
 *   )
 *   lazy val V = derivedAxiom("V vacuous",
 *     "p() -> [a{|^@|};]p()".asFormula,
 *     useAt(Ax.VK, PosInExpr(1::Nil))(1) &
 *     useAt(Ax.boxTrue)(1)
 *   )
 * }}}
 *
 * Derived Axiomatic Rules are derived with a tactic and their meta information is annotated in this file as follows:
 * {{{
 *   @ProofRule(
 *     name = "monb",
 *     displayName = Some("M[]"),
 *     displayPremises = "P |- Q",
 *     displayConclusion = "[a;]P |- [a;]Q",
 *   )
 *   lazy val monb = derivedRuleSequent("M[]",
 *     Sequent(immutable.IndexedSeq("[a_;]p_(||)".asFormula), immutable.IndexedSeq("[a_;]q_(||)".asFormula)),
 *     someTactic)
 * }}}
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.core.AxiomBase]]
 * @see
 *   [[org.keymaerax.btactics.macros.AxiomInfo]]
 * @see
 *   [[org.keymaerax.btactics.macros.Axiom]]
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

  /** Look up a core axiom from [[Provable.axioms]] and wrap it into a [[CoreAxiomInfo]] */
  private def coreAxiom(name: String): CoreAxiomInfo = { CoreAxiomInfo(name) }

  private val AUTO_INSERT: Boolean = true

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  def derivedFact(name: String, fact: ProvableSig): DerivedAxiomInfo = {
    val dai = DerivedAxiomInfo(name)
    val lemmaName = dai.storedName
    require(fact.isProved, "only proved Provables would be accepted as derived axioms: " + name + " got\n" + fact)
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
                    "Prover already has a different lemma filed under the same name " + derivedAxiomDB.get(
                      lemmaName
                    ) + " (lemma " + name + " stored in file name " + lemmaName + ") instead of " + lemma
                  )
                } else { lemma.name.get }
              case None => lemma.name.get
            }
          } else { derivedAxiomDB.add(lemma) }
        derivedAxiomDB.get(lemmaID).get
      }
    dai.setLemma(insertedLemma)
    dai
  }

  def derivedRule(name: String, fact: ProvableSig): DerivedRuleInfo = {
    // create evidence (traces input into tool and output from tool)
    val dri = DerivedRuleInfo(name)
    val evidence = ToolEvidence(immutable.List("input" -> fact.toString, "output" -> "true")) :: Nil
    val lemmaName = dri.storedName
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
                "Prover already has a different lemma filed under the same name " + derivedAxiomDB
                  .get(lemmaName) + " (lemma " + name + " stored in file name " + lemmaName + ") instnead of " + lemma
              )
            }
          } else { derivedAxiomDB.add(lemma) }
        derivedAxiomDB.get(lemmaID).get
      }
    dri.setLemma(insertedLemma)
    dri
  }

  private[this] def derivedRuleSequent(name: String, derived: => Sequent, tactic: => BelleExpr): DerivedRuleInfo = {
    val dri = DerivedRuleInfo(name)
    val storageName = dri.storedName
    val lemma = derivedAxiomDB.get(storageName) match {
      case Some(lemma) => lemma
      case None =>
        val witness = TactixLibrary.proveBy(derived, tactic)
        derivedRule(name, witness).lemma
    }
    dri.setLemma(lemma)
    dri
  }

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  def derivedAxiomFromFact(canonicalName: String, derived: Formula, fact: ProvableSig): DerivedAxiomInfo = derivedFact(
    canonicalName,
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
  def derivedAxiom(canonicalName: String, derived: => Sequent, tactic: => BelleExpr): DerivedAxiomInfo = {
    val dai: DerivedAxiomInfo = DerivedAxiomInfo(canonicalName)
    val lemma = derivedAxiomDB.get(dai.storedName) match {
      case Some(lemma) => lemma
      case None =>
        val witness = TactixLibrary.proveBy(derived, tactic)
        assert(
          witness.isProved,
          "tactics proving derived axioms should produce proved Provables: " + canonicalName + " got\n" + witness,
        )
        derivedFact(canonicalName, witness).lemma
    }
    dai.setLemma(lemma)
    dai
  }

  /**
   * Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available
   */
  def derivedFormula(name: String, derived: Formula, tactic: => BelleExpr): DerivedAxiomInfo =
    derivedAxiom(name, Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(derived)), tactic)

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
  @Axiom(
    name = "diamond",
    displayName = Some("<·>"),
    displayNameAscii = Some("<.>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__&not;[a]&not;P__↔&langle;a&rangle;P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  val diamond: CoreAxiomInfo = coreAxiom("<> diamond")

  @Axiom(
    name = "assignbAxiom",
    displayName = Some("[:=]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[x:=e]p(x)__↔p(e)",
    key = "0",
    recursor = "*",
    unifier = Unifier.Full,
  )
  val assignbAxiom: CoreAxiomInfo = coreAxiom("[:=] assign")

  @Axiom(
    name = "assignbeq",
    displayName = Some("[:=]="),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[x:=e]P__↔∀x(x=e→P)",
    key = "0",
    recursor = "0.1;*",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  val assignbeq: CoreAxiomInfo = coreAxiom("[:=] assign equality")

  @Axiom(name = "selfassignb", displayName = Some("[:=]"), displayConclusion = "__[x:=x]P__↔P")
  val selfassignb: CoreAxiomInfo = coreAxiom("[:=] self assign")

  @Axiom(
    name = "Dassignb",
    displayName = Some("[:=]"),
    displayConclusion = "__[x':=c]p(x')__↔p(c)",
    key = "0",
    recursor = "*",
    unifier = Unifier.Full,
  )
  val Dassignb: CoreAxiomInfo = coreAxiom("[':=] differential assign")

  @Axiom(
    name = "Dassignbeq",
    displayName = Some("[:=]="),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[x':=e]P__↔∀x'(x'=e→P)",
    key = "0",
    recursor = "0.1;*",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  val Dassignbeq: CoreAxiomInfo = coreAxiom("[':=] assign equality")

  @Axiom(name = "Dselfassignb", displayName = Some("[':=]"), displayConclusion = "__[x':=x']P__↔P")
  val Dselfassignb: CoreAxiomInfo = coreAxiom("[':=] self assign")

  @Axiom(
    name = "randomb",
    displayName = Some("[:*]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[x:=*]P__↔∀x P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val randomb: CoreAxiomInfo = coreAxiom("[:*] assign nondet")

  @Axiom(
    name = "testb",
    displayName = Some("[?]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[?Q]P__↔(Q→P)",
    key = "0",
    recursor = "1",
    unifier = Unifier.SurjectiveLinear,
  )
  val testb: CoreAxiomInfo = coreAxiom("[?] test")

  @Axiom(
    name = "choiceb",
    displayName = Some("[∪]"),
    displayNameAscii = Some("[++]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a∪b]P__↔[a]P∧[b]P",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val choiceb: CoreAxiomInfo = coreAxiom("[++] choice")

  @Axiom(
    name = "composeb",
    displayName = Some("[;]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a;b]P__↔[a][b]P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val composeb: CoreAxiomInfo = coreAxiom("[;] compose")

  @Axiom(
    name = "iterateb",
    displayName = Some("[*]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a*]P__↔P∧[a][a*]P",
    key = "0",
    recursor = "1",
    unifier = Unifier.SurjectiveLinear,
  )
  val iterateb: CoreAxiomInfo = coreAxiom("[*] iterate")

  @Axiom(
    name = "barcan",
    displayName = Some("B Barcan"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a]∀x p(x)__ ↔∀x[a]p(x)  (x∉a)",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  val barcan: CoreAxiomInfo = coreAxiom("B Barcan")

  // Differential Equations

  // @TODO: Old AxiomInfo calls DWeakening
  @Axiom(
    name = "DWbase",
    displayName = Some("DW base"),
    displayLevel = DisplayLevel.Internal,
    displayConclusion = "__[{x'=f(x)&Q}]Q__",
    key = "",
    recursor = "",
    unifier = Unifier.SurjectiveLinear,
  )
  val DWbase: CoreAxiomInfo = coreAxiom("DW base")

  @Axiom(
    name = "DE",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=f(x)&Q}]P__↔[x'=f(x)&Q][x':=f(x)]P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val DE: CoreAxiomInfo = coreAxiom("DE differential effect")

  @Axiom(
    name = "DEs",
    displayName = Some("DE"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=F,c&Q}]P__↔[{c,x'=F&Q}][x':=f(x)]P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val DEs: CoreAxiomInfo = coreAxiom("DE differential effect (system)")

  /* @todo soundness requires only vectorial x in p(||) */
  @Axiom(
    name = "DIequiv",
    displayName = Some("DI"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "(__[{x'=f(x)&Q}]P__↔[?Q]P)←(Q→[{x'=f(x)&Q}](P)')",
    key = "1.0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  val DIequiv: CoreAxiomInfo = coreAxiom("DI differential invariance")

  @Axiom(
    name = "DGa",
    displayName = Some("DG"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=f(x)&Q}]P__↔∃y [{x'=f(x),y'=a*y+b&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val DGa: CoreAxiomInfo = coreAxiom("DG differential ghost")

  // @todo name: why inverse instead of universal?
  @Axiom(
    name = "DGpp",
    displayName = Some("DG inverse differential ghost"),
    displayConclusion = "__[{x'=f(x)&Q}]P__↔∀y [{y'=a*y+b,x'=f(x)&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val DGpp: CoreAxiomInfo = coreAxiom("DG inverse differential ghost")

  @Axiom(
    name = "DGi",
    displayName = Some("DG inverse differential ghost implicational"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=f(x)&Q}]P__→∀y [{y'=g(x,y),x'=f(x)&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val DGi: CoreAxiomInfo = coreAxiom("DG inverse differential ghost implicational")

  @Axiom(
    name = "DGC",
    displayName = Some("DG"),
    displayConclusion = "__[{x'=f(x)&Q}]P__↔∃y [{x'=f(x),y'=g()&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val DGC: CoreAxiomInfo = coreAxiom("DG differential ghost constant")

  @Axiom(
    name = "DGCa",
    displayName = Some("DGa"),
    displayConclusion = "__[{x'=f(x)&Q}]P__↔∀y [{x'=f(x),y'=g()&Q}]P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val DGCa: CoreAxiomInfo = coreAxiom("DG differential ghost constant all")

  @Axiom(
    name = "DS",
    displayName = Some("DS&"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=c()&q(x)}]P__ ↔ ∀t≥0 (∀0≤s≤t q(x+c()*s)) → [x:=x+c()*t;]P)",
    key = "0",
    recursor = "0.1.1;0.1;*",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  val DS: CoreAxiomInfo = coreAxiom("DS& differential equation solution")

  /* @todo: , commute should be derivable from this + ghost */
  @Axiom(name = "commaSort", displayName = Some(","), unifier = Unifier.Linear)
  val commaSort: CoreAxiomInfo = coreAxiom(", sort")

  @Axiom(name = "commaCommute", displayName = Some(","), unifier = Unifier.Linear, key = "0", recursor = "")
  val commaCommute: CoreAxiomInfo = coreAxiom(", commute")

  @Axiom(name = "DX", key = "0", recursor = "1", unifier = Unifier.SurjectiveLinear)
  val DX: CoreAxiomInfo = coreAxiom("DX differential skip")

  @Axiom(
    name = "Dcomp",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "[x'=f(x)&Q]P ↔ [x'=f(x)&Q][x'=f(x)&Q]P",
    unifier = Unifier.Linear,
  )
  val Dcomp: CoreAxiomInfo = coreAxiom("D[;] differential self compose")

  @Axiom(
    name = "DIogreater",
    displayName = Some("DIo >"),
    displayConclusion = "(__[{x'=f(x)&Q}]g(x)>h(x)__↔[?Q]g(x)>h(x))←(Q→[{x'=f(x)&Q}](g(x)>h(x)→(g(x)>h(x))'))",
    key = "1.0",
    recursor = "*",
    unifier = Unifier.Linear,
  )
  val DIogreater: CoreAxiomInfo = coreAxiom("DIo open differential invariance >")

  @Axiom(
    name = "DMP",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "(__[{x'=f(x)&Q}]P__←[{x'=f(x)&R}]P)←[{x'=f(x)&Q}](Q→R)",
    inputs = "R:formula",
    key = "1.1", /*@todo, recursor = (0::Nil)::(Nil)::Nil*/
  )
  val DMP: CoreAxiomInfo = coreAxiom("DMP differential modus ponens")

  @Axiom(
    name = "Uniq",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "<x'=f(x)&Q}>P ∧ <x'=f(x)&R>P → __<x'=f(x)&Q∧R>P__",
    key = "1",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Uniq: CoreAxiomInfo = coreAxiom("Uniq uniqueness")

  /* @note soundness requires no primes in f(||) (guaranteed by data structure invariant) */
  @Axiom(
    name = "Cont",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "e>0 → __<x'=f(x),t'=1&e>0>t≠0__",
    key = "1",
    recursor = "*",
  )
  val Cont: CoreAxiomInfo = coreAxiom("Cont continuous existence")

  @Axiom(
    name = "RIclosedgeq",
    displayName = Some("RI& >="),
    displayLevel = DisplayLevel.Browse,
    displayConclusion =
      "__[x'=f(x)&Q]e≥0__ ↔ (Q→e≥0) ∧ [x'=f(x)&Q∧e≥0};t:=0;](<{t'=1,x'=f(x)&Q>t≠0→<t'=1,x'=f(x)&e≥0}>t≠0)",
    key = "0",
    recursor = "1.1.1;1.1.0;1;0",
  )
  val RIclosedgeq: CoreAxiomInfo = coreAxiom("RI& closed real induction >=")

  @Axiom(
    name = "RI",
    displayName = Some("RI&"),
    displayConclusion =
      "__[x'=f(x)&Q]P__ ↔ ∀s [t'=1,x'=f(x)&Q&(P|t=s)](t=s -> P & (<t'=1,x'=f(x)&(Q|t=s)>t!=s -> <t'=1,x'=f(x)&(P|t=s)>t!=s))",
    key = "0",
    recursor = "*",
  )
  val RI: CoreAxiomInfo = coreAxiom("RI& real induction")

  @Axiom(
    name = "IVT",
    displayConclusion =
      "<{t'=f(t,x),x'=g(t,x)&q(t,x)}>(t>=z&p(t,x))→t<=z→<{t'=f(t,x),x'=g(t,x)&q(t,x)}>(t=z∧<{t'=f(t,x),x'=g(t,x)&q(t,x)}>(t>=z∧p(t,x))",
    unifier = Unifier.Full,
  )
  val IVT: CoreAxiomInfo = coreAxiom("IVT")

  @Axiom(
    name = "DCC",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__[{x'=f(x)&R}](P→Q)__←([{x'=f(x)&R&P}]Q∧[{x'=f(x)&R}](¬P→[{x'=f(x)&R}]¬P)",
    key = "1",
    recursor = "0",
    unifier = Unifier.Linear,
  )
  val DCC: CoreAxiomInfo = coreAxiom("DCC")

  /* DIFFERENTIAL AXIOMS */

  @Axiom(
    name = "Dconst",
    displayName = Some("c()'"),
    displayConclusion = "__(c)'__=0",
    unifier = Unifier.Linear,
    key = "0",
    recursor = "",
  )
  val Dconst: CoreAxiomInfo = coreAxiom("c()' derive constant fn")

  @Axiom(
    name = "DvarAxiom",
    displayName = Some("x'"),
    displayConclusion = "__(x)'__=x'",
    unifier = Unifier.Linear,
    key = "0",
    recursor = "",
  )
  val DvarAxiom: CoreAxiomInfo = coreAxiom("x' derive var")

  // @todo derivable by CET
  @Axiom(
    name = "Dneg",
    displayName = Some("-'"),
    displayConclusion = "__(-f(x))'__=-(f(x))'",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dneg: CoreAxiomInfo = coreAxiom("-' derive neg")

  @Axiom(
    name = "Dplus",
    displayName = Some("+'"),
    displayConclusion = "__(f(x)+g(x))'__=f(x)'+g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dplus: CoreAxiomInfo = coreAxiom("+' derive sum")

  // @todo derivable by CET
  @Axiom(
    name = "Dminus",
    displayName = Some("-'"),
    displayConclusion = "__(f(x)-g(x))'__=f(x)'-g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dminus: CoreAxiomInfo = coreAxiom("-' derive minus")

  @Axiom(
    name = "Dtimes",
    displayName = Some("·'"),
    displayNameAscii = Some("*'"),
    displayConclusion = "__(f(x)·g(x))'__=(f(x))'·g(x)+f(x)·(g(x))'",
    key = "0",
    recursor = "0.0;1.1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dtimes: CoreAxiomInfo = coreAxiom("*' derive product")

  @Axiom(
    name = "Dquotient",
    displayName = Some("/'"),
    displayConclusion = "__(f(g)/g(x))'__=(g(x)·(f(x))-f(x)·(g(x))')/g(x)<sup>2</sup>",
    key = "0",
    recursor = "0.0.0;0.1.1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dquotient: CoreAxiomInfo = coreAxiom("/' derive quotient")

  @Axiom(
    name = "Dcompose",
    displayName = Some("∘'"),
    displayNameAscii = Some("o'"),
    displayConclusion = "[y:=g(x)][y':=1](__(f(g(x)))'__=(f(y))'·(g(x))'",
    key = "1.1.0",
    recursor = "1.1;1;*",
  )
  val Dcompose: CoreAxiomInfo = coreAxiom("chain rule")

  @Axiom(
    name = "Dpower",
    displayName = Some("^'"),
    displayConclusion = "__(f(g)^n)'__=n·f(g)^(n-1)·(f(g))'←n≠0",
    unifier = Unifier.Linear,
    key = "1.0",
    recursor = "1",
  )
  val Dpower: CoreAxiomInfo = coreAxiom("^' derive power")

  @Axiom(
    name = "Dgreaterequal",
    displayNameAscii = Some(">='"),
    displayName = Some("≥'"),
    displayConclusion = "__(f(x)≥g(x))'__↔f(x)'≥g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dgreaterequal: CoreAxiomInfo = coreAxiom(">=' derive >=")

  @Axiom(
    name = "Dgreater",
    displayName = Some(">'"),
    displayConclusion = "__(f(x)>g(x))'__↔f(x)'≥g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dgreater: CoreAxiomInfo = coreAxiom(">' derive >")

  @Axiom(
    name = "Dand",
    displayName = Some("∧'"),
    displayNameAscii = Some("&'"),
    displayConclusion = "__(P&Q)'__↔P'∧Q'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dand: CoreAxiomInfo = coreAxiom("&' derive and")

  @Axiom(
    name = "Dor",
    displayName = Some("∨'"),
    displayNameAscii = Some("|'"),
    displayConclusion = "__(P|Q)'__↔P'∧Q'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dor: CoreAxiomInfo = coreAxiom("|' derive or")

  @Axiom(
    name = "Dforall",
    displayName = Some("∀'"),
    displayNameAscii = Some("all'"),
    displayConclusion = "__(∀x p(x))'__↔∀x (p(x))'",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dforall: CoreAxiomInfo = coreAxiom("forall' derive forall")

  @Axiom(
    name = "Dexists",
    displayName = Some("∃'"),
    displayNameAscii = Some("exists'"),
    displayConclusion = "__(∃x p(x))'__↔∀x (p(x))'",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dexists: CoreAxiomInfo = coreAxiom("exists' derive exists")

  /* HYBRID PROGRAMS / GAMES */

  @Axiom(
    name = "duald",
    displayName = Some("&langle;<sup>d</sup>&rangle;"),
    displayNameAscii = Some("<d>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__&langle;a<sup>d</sup>&rangle;P__↔¬&langle;a&rangle;¬P",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  val duald: CoreAxiomInfo = coreAxiom("<d> dual")

  @Axiom(
    name = "VK",
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "(p→__[a]p__)←[a]⊤",
    key = "1.1",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  val VK: CoreAxiomInfo = coreAxiom("VK vacuous")

  @Axiom(
    name = "boxTrueAxiom",
    displayName = Some("[]T axiom"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a]⊤__",
    key = "",
    recursor = "",
    unifier = Unifier.SurjectiveLinear,
  )
  val boxTrueAxiom: CoreAxiomInfo = coreAxiom("[]T system")

  @Axiom(
    name = "K",
    displayLevel = DisplayLevel.All,
    displayConclusion = "[a](P→Q) → (__[a]P → [a]Q__)",
    key = "1",
    recursor = "*",
  )
  val K: CoreAxiomInfo = coreAxiom("K modal modus ponens")

  // @note the tactic I has a name and belleExpr, but there's no tactic that simply applies the I-> axiom,
  // because its sole purpose is to derive the stronger equivalence form
  @Axiom(
    name = "Iind",
    displayName = Some("I<sub>→</sub>"),
    displayNameAscii = Some("Iind"),
    displayLevel = DisplayLevel.Internal,
    displayConclusion = "P∧[a<sup>*</sup>](P→[a]P)→__[a<sup>*</sup>]P__",
    key = "1",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )
  val Iind: CoreAxiomInfo = coreAxiom("I induction")

  /* FIRST-ORDER QUANTIFIER AXIOMS */

  /** all dual */
  @Axiom(
    name = "alld",
    displayName = Some("∀d"),
    displayNameAscii = Some("alld"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__¬∃x ¬P__ ↔ ∀x P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  val alld: CoreAxiomInfo = coreAxiom("all dual")

  @Axiom(
    name = "allPd",
    displayName = Some("∀'d"),
    displayNameAscii = Some("allPd"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__¬∃x' ¬P__ ↔ ∀x' P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  val allPd: CoreAxiomInfo = coreAxiom("all prime dual")

  /** all eliminate */
  @Axiom(
    name = "alle",
    displayName = Some("∀e"),
    displayNameAscii = Some("alle"),
    displayConclusion = "__∀x P__ → P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  val alle: CoreAxiomInfo = coreAxiom("all eliminate")

  @Axiom(
    name = "alleprime",
    displayName = Some("∀e'"),
    displayNameAscii = Some("allep"),
    displayConclusion = "__∀x' P__ → P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  val alleprime: CoreAxiomInfo = coreAxiom("all eliminate prime")

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
  @Axiom(name = "assignbeqy", displayName = Some("[:=]=y"), displayLevel = DisplayLevel.Internal)
  lazy val assignbeqy: DerivedAxiomInfo = derivedAxiomFromFact(
    "[:=] assign equality y",
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
  @Axiom(name = "selfassignby", displayName = Some("[:=]y"), displayLevel = DisplayLevel.Internal)
  lazy val selfassignby: DerivedAxiomInfo = derivedAxiomFromFact(
    "[:=] self assign y",
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
  @Axiom(
    name = "DEsysy",
    displayLevel = DisplayLevel.Internal,
    displayConclusion = "__[{y'=F,c&Q}]P__↔[{c,y'=F&Q}][y':=f(x)]P",
    key = "0",
    recursor = "1;*",
  )
  lazy val DEsysy: DerivedAxiomInfo = derivedAxiomFromFact(
    "DE differential effect (system) y",
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
  @Axiom(
    name = "alldy",
    displayName = Some("∀d"),
    displayNameAscii = Some("alldy"),
    displayLevel = DisplayLevel.Internal,
  )
  lazy val alldy: DerivedAxiomInfo = derivedAxiomFromFact(
    "all dual y",
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
  @Axiom(
    name = "alldt",
    displayName = Some("∀d"),
    displayNameAscii = Some("alldt"),
    displayLevel = DisplayLevel.Internal,
  )
  lazy val alldt: DerivedAxiomInfo = derivedAxiomFromFact(
    "all dual time",
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
  @Axiom(name = "ally", displayName = Some("∀y"), displayNameAscii = Some("ally"), displayLevel = DisplayLevel.Internal)
  lazy val ally: DerivedAxiomInfo = derivedAxiomFromFact(
    "all eliminate y",
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
  @ProofRule(
    name = "contraposition2Rule",
    displayName = Some("contra2"),
    displayPremises = "!Q |- !P",
    displayConclusion = "P |- Q",
  )
  lazy val contraposition2Rule: DerivedRuleInfo = derivedRuleSequent(
    "contra2",
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
   *     p(x) |- [a]p(x)
   *   --------------------- ind
   *     p(x) |- [{a}*]p(x)
   * }}}
   * Interderives with FP fixpoint rule.
   * @see
   *   Lemma 4.1 of Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log.
   *   17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @see
   *   Lemma 7.2 and Corollary 16.1 of Andre Platzer.
   *   [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
   */
//  ("ind induction",
//    (immutable.IndexedSeq(Sequent(immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(a, pany)))),
//      Sequent(immutable.IndexedSeq(pany), immutable.IndexedSeq(Box(Loop(a), pany))))),
  @ProofRule(name = "indrule", displayPremises = "P |- [a]P", displayConclusion = "P |- [a*]P")
  lazy val indrule: DerivedRuleInfo = derivedRuleSequent(
    "ind induction",
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
   * {{{
   * Premise p(||) | <a>q(||) ==> q(||)
   * Conclusion <a*>p(||) ==> q(||)
   * }}}
   * {{{
   *     p(x) | <a>q(x) |- q(x)    p(x) | <a>q(x) |- q(x)
   *   --------------------------------------------------- FP
   *     <a*>p(x) |- q(x)
   * }}}
   * Interderives with ind induction rule. FP is used as basis, because deriving FP from ind leads to a duplicate
   * premise, needing list to set contraction.
   * @see
   *   Lemma 4.1 of Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log.
   *   17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
   * @see
   *   Lemma 16.11 and Corollary 16.1 of Andre Platzer.
   *   [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
   * @see
   *   [[FPrule]]
   */
  @ProofRule(
    name = "FPruleduplicate",
    displayLevel = DisplayLevel.Internal,
    displayPremises = "P | <a>Q |- Q ;; P | <a>Q |- Q",
    displayConclusion = "<a*>P |- Q",
  )
  private[btactics] lazy val FPruleduplicate: DerivedRuleInfo = derivedRuleSequent(
    "FP rule duplicate",
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
  @ProofRule(
    name = "allGeneralize",
    displayName = Some("all gen"),
    displayNameAscii = Some("allgen"),
    displayNameLong = Some("allgen"),
    displayPremises = "|- P",
    displayConclusion = "|- \\forall x P",
  )
  lazy val allGeneralize: DerivedRuleInfo = derivedRuleSequent(
    "all generalization",
    // (immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(pany))),
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
  @ProofRule(
    name = "monallrule",
    displayName = Some("M∀"),
    displayNameAscii = Some("Mall"),
    displayPremises = "P |- Q",
    displayConclusion = "∀x P |- ∀ x Q",
  )
  lazy val monallrule: DerivedRuleInfo = derivedRuleSequent(
    "all monotone",
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
   *       p(||)
   *   ----------- G
   *    [a{|^@|};]p(||)
   * }}}
   * @note
   *   Unsound for hybrid games
   * @derived
   *   from M and [a]true
   */
  @ProofRule(name = "Goedel", displayName = Some("G"), displayPremises = "|- P", displayConclusion = "|- [a;]P")
  lazy val Goedel: DerivedRuleInfo = derivedRuleSequent(
    "Goedel",
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
  @Axiom(
    name = "V",
    displayConclusion = "p→__[a]p__",
    key = "1",
    recursor = "*",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val V: DerivedAxiomInfo = derivedAxiom(
    "V vacuous",
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
  @Axiom(
    name = "allInst",
    displayName = Some("∀inst"),
    displayNameAscii = Some("allInst"),
    displayConclusion = "__∀x p(x)__ → p(f())",
    key = "0",
    recursor = "*",
  )
  lazy val allInst: DerivedAxiomInfo = derivedFormula(
    "all instantiate",
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

  @Axiom(
    name = "allInstPrime",
    displayName = Some("∀inst'"),
    displayNameAscii = Some("allInstPrime"),
    displayConclusion = "__∀x' p(x')__ → p(f())",
    key = "0",
    recursor = "*",
  )
  lazy val allInstPrime: DerivedAxiomInfo = derivedFormula(
    "all instantiate prime",
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
  @Axiom(name = "allV", displayName = Some("V∀"), displayNameAscii = Some("allV"), key = "0", recursor = "*")
  lazy val allV: DerivedAxiomInfo = derivedAxiom(
    "vacuous all quantifier",
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
  @ProofRule(
    name = "CTtermCongruence",
    displayName = Some("CT term congruence"),
    displayNameAscii = Some("CTtermCongruence"),
    displayNameLong = Some("CTtermCongruence"),
    displayPremises = "|- f_(||) = g_(||)",
    displayConclusion = "|- ctx_(f_(||)) = ctx_(g_(||))",
  )
  lazy val CTtermCongruence: DerivedRuleInfo = derivedRuleSequent(
    "CT term congruence",
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
  @ProofRule(
    name = "CQimplyCongruence",
    displayName = Some("CQimply"),
    displayNameAscii = Some("CQimplyCongruence"),
    displayNameLong = Some("CQimplyCongruence"),
    displayPremises = "|- f_(||) = g_(||)",
    displayConclusion = "|- ctx_(f_(||)) -> ctx_(g_(||))",
  )
  lazy val CQimplyCongruence: DerivedRuleInfo = derivedRuleSequent(
    "CQimply equation congruence",
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
  @ProofRule(
    name = "CQrevimplyCongruence",
    displayName = Some("CQrevimply"),
    displayNameAscii = Some("CQrevimplyCongruence"),
    displayNameLong = Some("CQrevimplyCongruence"),
    displayPremises = "|- g_(||) = f_(||)",
    displayConclusion = "|- ctx_(f_(||)) -> ctx_(g_(||))",
  )
  lazy val CQrevimplyCongruence: DerivedRuleInfo = derivedRuleSequent(
    "CQrevimply equation congruence",
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
  @ProofRule(
    name = "CEimplyCongruence",
    displayName = Some("CEimply"),
    displayNameAscii = Some("CEimplyCongruence"),
    displayNameLong = Some("CEimplyCongruence"),
    displayPremises = "|- p_(||) <-> q_(||)",
    displayConclusion = "|- ctx_{p_(||)} -> ctx_{(q_(||)}",
  )
  lazy val CEimplyCongruence: DerivedRuleInfo = derivedRuleSequent(
    "CEimply congruence",
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
  @ProofRule(
    name = "CErevimplyCongruence",
    displayName = Some("CErevimply"),
    displayNameAscii = Some("CErevimplyCongruence"),
    displayNameLong = Some("CErevimplyCongruence"),
    displayPremises = "|- q_(||) <-> p_(||)",
    displayConclusion = "|- ctx_{p_(||)} -> ctx_{(q_(||)}",
  )
  lazy val CErevimplyCongruence: DerivedRuleInfo = derivedRuleSequent(
    "CErevimply congruence",
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
  @ProofRule(
    name = "monbaxiom",
    displayName = Some("[] monotone"),
    displayNameAscii = Some("[]monotone"),
    displayNameLong = Some("[]monotone"),
    displayPremises = "P |- Q",
    displayConclusion = "[a;]P |- [a;]Q",
  )
  lazy val monbaxiom: DerivedRuleInfo = derivedRuleSequent(
    "[] monotone",
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
  @ProofRule(
    name = "monb2",
    displayName = Some("[] monotone 2"),
    displayNameAscii = Some("[]monotone 2"),
    displayNameLong = Some("[]monotone 2"),
    displayPremises = "Q |- P",
    displayConclusion = "[a;]Q |- [a;]P",
  )
  lazy val monb2: DerivedRuleInfo = derivedRuleSequent(
    "[] monotone 2",
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
   *    \exists x_ (x_ <= 0 & J(x_)) |- P   x_ > 0, J(x_) |- <a{|x_|}>J(x_-1)
   *    ------------------------------------------------- con
   *     \exists x_ J(x_) |- <a{|x_|}*>P
   * }}}
   */
  @ProofRule(
    name = "conflat",
    displayName = Some("con flat"),
    displayNameAscii = Some("conflat"),
    displayNameLong = Some("conflat"),
    displayPremises = "\\exists v (v<=0&J) |- P;; v > 0, J |- <a>J(v-1)",
    displayConclusion = "J |- <a*>P",
  )
  lazy val conflat: DerivedRuleInfo = derivedRuleSequent(
    "con convergence flat",
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
   * @Derived
   * @see
   *   [[equalReflexive]]
   */
  @Axiom(
    name = "equivReflexive",
    displayName = Some("↔R"),
    displayNameAscii = Some("<->R"),
    displayConclusion = "__p↔p__",
    key = "",
    recursor = "",
    unifier = Unifier.Full,
  )
  lazy val equivReflexive: DerivedAxiomInfo = derivedFact(
    "<-> reflexive",
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
  @Axiom(name = "equivExpand", displayName = Some("↔2→←"), displayNameAscii = Some("<->2-><-"), unifier = Unifier.Full)
  lazy val equivExpand: DerivedAxiomInfo =
    derivedFormula("<-> expand", "(p_() <-> q_()) <-> (p_()->q_())&(q_()->p_())".asFormula, prop)

  /** Convert <-> to two conjunctions: `(p_() <-> q_()) <-> (p_()&q_())|(!p_()&!q_())` */
  @Axiom(name = "equivExpandAnd", displayName = Some("↔2∧"), displayNameAscii = Some("<->2&"), unifier = Unifier.Full)
  lazy val equivExpandAnd: DerivedAxiomInfo =
    derivedFormula("<-> expand and", "(p_() <-> q_()) <-> (p_()&q_())|(!p_()&!q_())".asFormula, prop)

  /**
   * {{{
   * Axiom "-> distributes over &".
   *   (p() -> (q()&r())) <-> ((p()->q()) & (p()->r()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(name = "implyDistAnd", displayName = Some("→∧"), displayNameAscii = Some("->&"))
  lazy val implyDistAnd: DerivedAxiomInfo = derivedAxiom(
    "-> distributes over &",
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
  @Axiom(name = "implyWeaken", displayName = Some("→W"), displayNameAscii = Some("->W"))
  lazy val implyWeaken: DerivedAxiomInfo = derivedAxiom(
    "-> weaken",
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
  @Axiom(name = "implyDistEquiv", displayName = Some("→↔"), displayNameAscii = Some("-><->"))
  lazy val implyDistEquiv: DerivedAxiomInfo = derivedAxiom(
    "-> distributes over <->",
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
  @Axiom(name = "orDistAnd", displayName = Some("∨∧"), displayNameAscii = Some("|&"))
  lazy val orDistAnd: DerivedAxiomInfo = derivedAxiom(
    "| distributes over &",
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
  @Axiom(name = "constCongruence", displayName = Some("CCE"), key = "1", recursor = "*", unifier = Unifier.Full)
  lazy val constCongruence: DerivedAxiomInfo = derivedFormula(
    "const congruence",
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
  @Axiom(name = "constFormulaCongruence", displayName = Some("CCQ"), key = "1", recursor = "*", unifier = Unifier.Full)
  lazy val constFormulaCongruence: DerivedAxiomInfo = derivedFormula(
    "const formula congruence",
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
   *
   * @Derived
   */
  @Axiom(
    name = "doubleNegation",
    displayName = Some("¬¬"),
    displayNameAscii = Some("!!"),
    displayConclusion = "__¬¬p__↔p",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val doubleNegation: DerivedAxiomInfo = derivedFact(
    "!! double negation",
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
  @Axiom(
    name = "existsDual",
    displayName = Some("∃d"),
    displayNameAscii = Some("existsd"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__¬∀x ¬P__ ↔ ∃x P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val existsDual: DerivedAxiomInfo = derivedAxiom(
    "exists dual",
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_ (!p_(||))) <-> \\exists x_ p_(||)".asFormula)),
    useAt(alld, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  @Axiom(
    name = "existsPDual",
    displayName = Some("∃'d"),
    displayNameAscii = Some("existsprimed"),
    key = "0",
    recursor = "*",
  )
  lazy val existsPDual: DerivedAxiomInfo = derivedAxiom(
    "exists prime dual",
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_' (!p_(||))) <-> \\exists x_' p_(||)".asFormula)),
    useAt(allPd, PosInExpr(1 :: Nil))(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: 0 :: Nil) &
      byUS(equivReflexive),
  )

  @Axiom(
    name = "existsDualy",
    displayName = Some("∃d"),
    displayNameAscii = Some("existsdy"),
    displayLevel = DisplayLevel.Internal,
  )
  lazy val existsDualy: DerivedAxiomInfo = derivedAxiom(
    "exists dual y",
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
  @Axiom(
    name = "notExists",
    displayName = Some("¬∃"),
    displayNameAscii = Some("!exists"),
    displayConclusion = "__(¬∃x (p(x)))__↔∀x (¬p(x))",
    key = "0",
    recursor = "0;*",
  )
  lazy val notExists: DerivedAxiomInfo = derivedAxiom(
    "!exists",
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
  @Axiom(
    name = "notAll",
    displayName = Some("¬∀"),
    displayNameAscii = Some("!all"),
    displayConclusion = "__¬∀x (p(x)))__↔∃x (¬p(x))",
    key = "0",
    recursor = "0;*",
  )
  lazy val notAll: DerivedAxiomInfo = derivedAxiom(
    "!all",
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
  @Axiom(
    name = "notBox",
    displayName = Some("¬[]"),
    displayNameAscii = Some("![]"),
    displayConclusion = "__¬[a]P__↔<a>¬P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val notBox: DerivedAxiomInfo = derivedAxiom(
    "![]",
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
  @Axiom(
    name = "notDiamond",
    displayName = Some("¬<>"),
    displayNameAscii = Some("!<>"),
    displayConclusion = "__¬<a>P__↔[a]¬P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val notDiamond: DerivedAxiomInfo = derivedAxiom(
    "!<>",
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
  @Axiom(
    name = "allDist",
    displayName = Some("∀→"),
    displayNameAscii = Some("all->"),
    displayConclusion = "(∀x (p(x)→q(x))) → (__∀x p(x) → ∀x q(x)__)",
    key = "1",
    recursor = "*",
  )
  lazy val allDist: DerivedAxiomInfo = derivedAxiom(
    "all distribute",
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
  @Axiom(
    name = "allDistElim",
    displayName = Some("∀→"),
    displayNameAscii = Some("all->"),
    displayConclusion = "(∀x (P→Q)) → (__∀x P → ∀x Q__)",
    key = "1",
    recursor = "*",
  )
  lazy val allDistElim: DerivedAxiomInfo = derivedAxiom(
    "all distribute elim",
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
  @Axiom(
    name = "existsDistElim",
    displayName = Some("∃→"),
    displayNameAscii = Some("exists->"),
    displayConclusion = "(∀x (P→Q)) → (__∃x P → ∃x Q__)",
    key = "1",
    recursor = "*",
  )
  lazy val existsDistElim: DerivedAxiomInfo = derivedAxiom(
    "exists distribute elim",
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
  @Axiom(
    name = "box",
    displayName = Some("[·]"),
    displayNameAscii = Some("[.]"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "__&not;&langle;a&rangle;&not;P__ ↔ [a]P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val box: DerivedAxiomInfo = derivedAxiom(
    "[] box",
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
  @Axiom(
    name = "Kd",
    displayConclusion = "[a](P→Q) → (<a>P → __<a>Q__)",
    key = "1.1",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val Kd: DerivedAxiomInfo = derivedAxiom(
    "Kd diamond modus ponens",
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
  @Axiom(
    name = "Kd2",
    displayConclusion = "[a]P → (<a>Q → __<a>(P∧Q)__)",
    key = "1.1",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val Kd2: DerivedAxiomInfo = derivedAxiom(
    "Kd2 diamond modus ponens",
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
  @Axiom(name = "boxDiamondPropagation", displayName = Some("[]~><>"))
  lazy val boxDiamondPropagation: DerivedAxiomInfo = derivedAxiom(
    "[]~><> propagation",
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
  @Axiom(name = "boxDiamondSubstPropagation", displayName = Some("[]~><> subst"))
  lazy val boxDiamondSubstPropagation: DerivedAxiomInfo = derivedAxiom(
    "[]~><> subst propagation",
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
  @Axiom(
    name = "Kand",
    displayName = Some("K&"),
    displayConclusion = "[a](P→Q) ∧ [a]P → __[a]Q__)",
    key = "1",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val Kand: DerivedAxiomInfo = derivedAxiom(
    "K modal modus ponens &",
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
  @Axiom(name = "andImplies", displayName = Some("&->"))
  lazy val andImplies: DerivedAxiomInfo = derivedAxiom(
    "&->",
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
  @Axiom(
    name = "boxAnd",
    displayName = Some("[]∧"),
    displayNameAscii = Some("[]^"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a](P∧Q)__↔[a]P ∧ [a]Q",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.Linear,
  )
  lazy val boxAnd: DerivedAxiomInfo = derivedAxiom(
    "[] split",
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
  @Axiom(
    name = "boxOrLeft",
    displayName = Some("[]∨L"),
    displayNameAscii = Some("[]orL"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "[a]P->__[a](P∨Q)__",
    key = "1",
  )
  lazy val boxOrLeft: DerivedAxiomInfo = derivedAxiom(
    "[] or left",
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
  @Axiom(
    name = "boxOrRight",
    displayName = Some("[]∨R"),
    displayNameAscii = Some("[]orR"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "[a]Q->__[a](P∨Q)__",
    key = "1",
  )
  lazy val boxOrRight: DerivedAxiomInfo = derivedAxiom(
    "[] or right",
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
  @Axiom(
    name = "boxImpliesAnd",
    displayName = Some("[]→∧"),
    displayNameAscii = Some("[]->^"),
    displayConclusion = "__[a](P→Q∧R)__ ↔ [a](P→Q) ∧ [a](P→R)",
    unifier = Unifier.Linear,
  )
  lazy val boxImpliesAnd: DerivedAxiomInfo = derivedAxiom(
    "[] conditional split",
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
  @Axiom(
    name = "diamondOr",
    displayName = Some("<>∨"),
    displayNameAscii = Some("<>|"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__&langle;a&rangle;(P∨Q)__↔&langle;a&rangle;P ∨ &langle;a&rangle;Q",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val diamondOr: DerivedAxiomInfo = derivedAxiom(
    "<> split",
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
  @Axiom(name = "pVd", key = "1", recursor = "0;1")
  lazy val pVd: DerivedAxiomInfo = derivedAxiom(
    "<> partial vacuous",
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
  @Axiom(
    name = "assignDual2",
    displayName = Some("⟨:=⟩D"),
    displayNameAscii = Some("<:=>D"),
    displayConclusion = "__&langle;x:=f();&rangle;P__ ↔ [x:=f();]P",
    key = "0",
    recursor = "*",
  )
  lazy val assignDual2: DerivedAxiomInfo = derivedFormula(
    ":= assign dual 2",
    "<x_:=f();>p(||) <-> [x_:=f();]p(||)".asFormula,
    useAt(selfassignb, PosInExpr(1 :: Nil))(1, 0 :: 1 :: Nil) &
      useAt(assigndAxiom)(1, 0 :: Nil) &
      byUS(equivReflexive),
    // NOTE alternative proof:
    //    useAt("[:=] assign equality exists")(1, 1::Nil) &
    //      useAt("<:=> assign equality")(1, 0::Nil) &
    //      byUS(equivReflexiveAxiom)
  )

  @Axiom(name = "DassignDual2", displayName = Some("':=D"))
  lazy val DassignDual2: DerivedAxiomInfo = derivedFormula(
    "':= assign dual 2",
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
  @Axiom(
    name = "assigndEqualityAxiom",
    displayName = Some("<:=>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__<x:=e>P__↔∃x(x=e∧P)",
    key = "0",
    recursor = "0.1;*",
  )
  lazy val assigndEqualityAxiom: DerivedAxiomInfo = derivedAxiom(
    "<:=> assign equality",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f_();>p_(||) <-> \\exists x_ (x_=f_() & p_(||))".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(existsDual, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(notAnd)(1, 1 :: 0 :: 0 :: Nil) &
      useAt(implyExpand, PosInExpr(1 :: Nil))(1, 1 :: 0 :: 0 :: Nil) &
      CE(PosInExpr(0 :: Nil)) &
      byUS(assignbeq),
  )

  @Axiom(
    name = "DassigndEqualityAxiom",
    displayName = Some("<':=>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__<x':=e>P__↔∃x'(x'=e∧P)",
    key = "0",
    recursor = "0.1;*",
  )
  lazy val DassigndEqualityAxiom: DerivedAxiomInfo = derivedAxiom(
    "<':=> assign equality",
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
  @Axiom(name = "assignbequalityexists", displayName = Some("[:=]"), displayNameAscii = Some("[:=] assign exists"))
  lazy val assignbequalityexists: DerivedAxiomInfo = derivedFormula(
    "[:=] assign equality exists",
    "[x_:=f();]p(||) <-> \\exists x_ (x_=f() & p(||))".asFormula,
    useAt(assignDual2, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      byUS(assigndEqualityAxiom),
    //      useAt(assigndEqualityAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
    //        //@note := assign dual is not applicable since [v:=t()]p(v) <-> <v:=t()>p(t),
    //        //      and [v:=t()]p(||) <-> <v:=t()>p(||) not derivable since clash in allL
    //        useAt(":= assign dual")(1, 1::Nil) & byUS(equivReflexiveAxiom)
  )

  @Axiom(name = "Dassignbequalityexists", displayName = Some("[':=]"), displayNameAscii = Some("[':=] assign exists"))
  lazy val Dassignbequalityexists: DerivedAxiomInfo = derivedFormula(
    "[':=] assign equality exists",
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
  @Axiom(
    name = "assignbexists",
    displayName = Some("[:=]∃"),
    displayNameAscii = Some("[:=]exists"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "*",
  )
  lazy val assignbexists: DerivedAxiomInfo = derivedAxiom(
    "[:=] assign exists",
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
  @Axiom(name = "assignball", displayName = Some("[:=]∀"), displayNameAscii = Some("[:=]all"))
  lazy val assignball: DerivedAxiomInfo = derivedAxiom(
    "[:=] assign all",
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
  @Axiom(name = "existsAnd", displayName = Some("∃∧"), displayNameAscii = Some("existsand"))
  lazy val existsAnd: DerivedAxiomInfo = derivedAxiom(
    "\\exists& exists and",
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
  @Axiom(name = "existsOr", displayName = Some("∃∨"), displayNameAscii = Some("existsor"))
  lazy val existsOr: DerivedAxiomInfo = derivedAxiom(
    "\\exists| exists or",
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
  @Axiom(name = "forallImplies", displayName = Some("∀→"), displayNameAscii = Some("forallimplies"))
  lazy val forallImplies: DerivedAxiomInfo = derivedAxiom(
    "\\forall-> forall implies",
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
  @Axiom(name = "assigndEqualityAll", displayName = Some("<:=>"), key = "0", recursor = "*;0.1")
  lazy val assigndEqualityAll: DerivedAxiomInfo = derivedAxiom(
    "<:=> assign equality all",
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
  @Axiom(
    name = "assigndAxiom",
    displayName = Some("<:=>"),
    displayConclusion = "__&langle;x:=e&rangle;p(x)__↔p(e)",
    key = "0",
    recursor = "*",
    unifier = Unifier.Full,
  )
  lazy val assigndAxiom: DerivedAxiomInfo = derivedAxiom(
    "<:=> assign",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f();>p(x_) <-> p(f())".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(assignbAxiom)(1, 0 :: 0 :: Nil) &
      useAt(doubleNegation)(1, 0 :: Nil) &
      byUS(equivReflexive),
  )

  @Axiom(
    name = "DassigndAxiom",
    displayName = Some("<':=>"),
    displayConclusion = "__&langle;x':=e&rangle;p(x')__↔p(e)",
    key = "0",
    recursor = "*",
    unifier = Unifier.Full,
  )
  lazy val DassigndAxiom: DerivedAxiomInfo = derivedAxiom(
    "<':=> assign",
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
  @Axiom(name = "selfassignd", displayName = Some("<:=>"))
  lazy val selfassignd: DerivedAxiomInfo = derivedAxiom(
    "<:=> self assign",
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
  @Axiom(name = "assignDual", displayName = Some(":=D"))
  lazy val assignDual: DerivedAxiomInfo = derivedAxiom(
    ":= assign dual",
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
  @Axiom(name = "assignbequational", displayName = Some("[:=]=="), key = "0", recursor = "*;0.1")
  lazy val assignbequational: DerivedAxiomInfo = derivedAxiom(
    "[:=] assign equational",
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
  @Axiom(name = "assignbup", displayName = Some("[:=]"), key = "0", recursor = "1;*")
  lazy val assignbup: DerivedAxiomInfo = derivedAxiom(
    "[:=] assign update",
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
  @Axiom(name = "assigndup", displayName = Some("<:=>"), key = "0", recursor = "1;*")
  lazy val assigndup: DerivedAxiomInfo = derivedAxiom(
    "<:=> assign update",
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
  @Axiom(name = "vacuousAssignb", displayName = Some("V[:=]"))
  lazy val vacuousAssignb: DerivedAxiomInfo = derivedAxiom(
    "[:=] vacuous assign",
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
  @Axiom(name = "vacuousAssignd", displayName = Some("V<:=>"))
  lazy val vacuousAssignd: DerivedAxiomInfo = derivedAxiom(
    "<:=> vacuous assign",
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
  @Axiom(
    name = "Dassignby",
    displayName = Some("[y':=]"),
    displayLevel = DisplayLevel.Internal,
    displayConclusion = "__[y':=c]p(y')__↔p(c)",
    unifier = Unifier.Full,
  )
  lazy val Dassignby: DerivedAxiomInfo = derivedAxiom(
    "[':=] differential assign y",
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
  @Axiom(name = "Dassignd", displayName = Some("<':=>"), key = "0", recursor = "*")
  lazy val Dassignd: DerivedAxiomInfo = derivedAxiom(
    "<':=> differential assign",
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
  @Axiom(
    name = "randomd",
    displayName = Some("<:*>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__<x:=*>P__↔∃x P",
    key = "0",
    recursor = "0;*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val randomd: DerivedAxiomInfo = derivedAxiom(
    "<:*> assign nondet",
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
  @Axiom(
    name = "testd",
    displayName = Some("<?>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__<?Q>P__↔Q∧P",
    key = "0",
    recursor = "1;0",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val testd: DerivedAxiomInfo = derivedAxiom(
    "<?> test",
    Sequent(IndexedSeq(), IndexedSeq("<?q_();>p_() <-> (q_() & p_())".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 0 :: Nil) &
      useAt(testb)(1, 0 :: 0 :: Nil) &
      prop,
  )

  /* inverse testd axiom for chase */
  @Axiom(name = "invtestd", displayName = Some("<?>i"), key = "0", recursor = "1", unifier = Unifier.Linear)
  lazy val invtestd: DerivedAxiomInfo = derivedAxiom(
    "<?> invtest",
    Sequent(IndexedSeq(), IndexedSeq("(q_() & p_()) <-> <?q_();>p_()".asFormula)),
    useAt(diamond, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(testb)(1, 1 :: 0 :: Nil) &
      prop,
  )

  /* inverse testd axiom for chase */
  @Axiom(name = "testdcombine", displayName = Some("<?> combine"), key = "0", recursor = "*", unifier = Unifier.Linear)
  lazy val testdcombine: DerivedAxiomInfo = derivedAxiom(
    "<?> combine",
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
  @Axiom(
    name = "choiced",
    displayName = Some("<∪>"),
    displayNameAscii = Some("<++>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__<a∪b>P__↔<a>P∨<b>P",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val choiced: DerivedAxiomInfo = derivedAxiom(
    "<++> choice",
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
  @Axiom(
    name = "composed",
    displayName = Some("<;>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__<a;b>P__↔<a><b>P",
    key = "0",
    recursor = "1;*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val composed: DerivedAxiomInfo = derivedAxiom(
    "<;> compose",
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
  @Axiom(
    name = "iterated",
    displayName = Some("<*>"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__<a*>P__↔P∨<a><a*>P",
    key = "0",
    recursor = "1",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val iterated: DerivedAxiomInfo = derivedAxiom(
    "<*> iterate",
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
  @Axiom(
    name = "loopApproxd",
    displayName = Some("<*> approx"),
    displayConclusion = "<a>P → __<a*>P__",
    key = "1",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val loopApproxd: DerivedAxiomInfo = derivedAxiom(
    "<*> approx",
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
  @Axiom(
    name = "loopApproxb",
    displayName = Some("[*] approx"),
    displayConclusion = "__[a*]P__ → [a]P",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val loopApproxb: DerivedAxiomInfo = derivedAxiom(
    "[*] approx",
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
  @Axiom(name = "IIinduction", displayName = Some("II induction"), displayLevel = DisplayLevel.Internal)
  lazy val IIinduction: DerivedAxiomInfo = derivedAxiom(
    "II induction",
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
  @Axiom(
    name = "loopMergeb",
    displayName = Some("[*] merge"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "__[a*][a*]P__ ↔ [a*]P",
    key = "0",
    recursor = "*",
  )
  lazy val loopMergeb: DerivedAxiomInfo = derivedAxiom(
    "[*] merge",
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
  @Axiom(
    name = "loopMerged",
    displayName = Some("<*> merge"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "__<a*><a*>P__ ↔ <a*>P",
    key = "0",
    recursor = "*",
  )
  lazy val loopMerged: DerivedAxiomInfo = derivedAxiom(
    "<*> merge",
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
  @Axiom(
    name = "iterateiterateb",
    displayName = Some("[**]"),
    displayConclusion = "__[a*;a*]P__ ↔ [a*]P",
    key = "",
    recursor = "*",
    unifier = Unifier.Full,
  )
  lazy val iterateiterateb: DerivedAxiomInfo = derivedAxiom(
    "[**] iterate iterate",
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
  @Axiom(
    name = "iterateiterated",
    displayName = Some("<**>"),
    displayConclusion = "__<a*;a*>P__ ↔ <a*>P",
    key = "",
    recursor = "*",
    unifier = Unifier.Full,
  )
  lazy val iterateiterated: DerivedAxiomInfo = derivedAxiom(
    "<**> iterate iterate",
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
  @Axiom(name = "backiterateb", displayName = Some("[*-]"), key = "0", recursor = "1.1;1;0", unifier = Unifier.Full)
  lazy val backiterateb: DerivedAxiomInfo = derivedAxiom(
    "[*-] backiterate",
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
  @Axiom(
    name = "backiteratebsuff",
    displayName = Some("[*-] backiterate sufficiency"),
    displayLevel = DisplayLevel.Internal,
  )
  lazy val backiteratebsuff: DerivedAxiomInfo = derivedAxiom(
    "[*-] backiterate sufficiency",
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
  @Axiom(
    name = "backiteratebnecc",
    displayName = Some("[*-] backiterate necessity"),
    displayLevel = DisplayLevel.Internal,
  )
  lazy val backiteratebnecc: DerivedAxiomInfo = derivedAxiom(
    "[*-] backiterate necessity",
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
  @Axiom(
    name = "I",
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a*]P__↔P∧[a*](P→[a]P)",
    key = "0",
    recursor = "1.1.1;1",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val I: DerivedAxiomInfo = derivedAxiom(
    "I",
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
  @Axiom(name = "existsGeneralize", displayName = Some("∃G"), displayNameAscii = Some("existsG"))
  lazy val existsGeneralize: DerivedAxiomInfo = derivedAxiom(
    "exists generalize",
    Sequent(IndexedSeq(), IndexedSeq("p_(f()) -> (\\exists x_ p_(x_))".asFormula)),
    useAt(existsDual, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      implyR(SuccPos(0)) &
      notR(SuccPos(0)) &
      useAt(allInst, PosInExpr(0 :: Nil))(-2) &
      prop,
  )

  @Axiom(
    name = "existsGeneralizey",
    displayName = Some("∃Gy"),
    displayNameAscii = Some("existsGy"),
    displayLevel = DisplayLevel.Internal,
  )
  lazy val existsGeneralizey: DerivedAxiomInfo = derivedAxiom(
    "exists generalize y",
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
  @Axiom(
    name = "existse",
    displayName = Some("∃e"),
    displayNameAscii = Some("existse"),
    displayConclusion = "P→__∃x P__",
    key = "1",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val existse: DerivedAxiomInfo = derivedAxiom(
    "exists eliminate",
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
  @Axiom(
    name = "existsey",
    displayName = Some("∃ey"),
    displayNameAscii = Some("existsey"),
    displayLevel = DisplayLevel.Internal,
  )
  lazy val existsey: DerivedAxiomInfo = derivedAxiom(
    "exists eliminate y",
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
  @Axiom(
    name = "allThenExists",
    displayName = Some("∀→∃"),
    displayNameAscii = Some("allThenExists"),
    displayConclusion = "∀x P → ∃x P",
  )
  lazy val allThenExists: DerivedAxiomInfo = derivedFormula(
    "all then exists",
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
  @Axiom(
    name = "allSubstitute",
    displayName = Some("∀S"),
    displayNameAscii = Some("allS"),
    displayConclusion = "__∀x(x=e→p(x))__ ↔ p(e)",
    key = "0",
    recursor = "*",
  )
  lazy val allSubstitute: DerivedAxiomInfo = derivedAxiom(
    "all substitute",
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
  @Axiom(
    name = "existsV",
    displayName = Some("V∃"),
    displayNameAscii = Some("existsV"),
    displayConclusion = "__∃x p__ ↔ p",
    key = "0",
    recursor = "*",
  )
  lazy val existsV: DerivedAxiomInfo = derivedAxiom(
    "vacuous exists quantifier",
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
  @Axiom(name = "pexistsV", displayName = Some("pV∃"), displayNameAscii = Some("pexistsV"))
  lazy val pexistsV: DerivedAxiomInfo = derivedAxiom(
    "partial vacuous exists quantifier",
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
  @Axiom(
    name = "vacuousBoxAssignNondet",
    displayName = Some("V[:*]"),
    displayConclusion = "__[x:=*;]p__ ↔ p",
    key = "0",
    recursor = "*",
  )
  lazy val vacuousBoxAssignNondet: DerivedAxiomInfo = derivedAxiom(
    "V[:*] vacuous assign nondet",
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
  @Axiom(
    name = "vacuousDiamondAssignNondet",
    displayName = Some("V<:*>"),
    displayConclusion = "__<x:=*;>p__ ↔ p",
    key = "0",
    recursor = "*",
  )
  lazy val vacuousDiamondAssignNondet: DerivedAxiomInfo = derivedAxiom(
    "V<:*> vacuous assign nondet",
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
  @Axiom(name = "domainCommute", displayName = Some("{∧}C"), displayNameAscii = Some("{&}C"))
  lazy val domainCommute: DerivedAxiomInfo = derivedAxiom(
    "Domain Constraint Conjunction Reordering",
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
  @Axiom(name = "postWeaken", displayName = Some("[]PW"), key = "1", recursor = "*")
  lazy val postWeaken: DerivedAxiomInfo = derivedAxiom(
    "[] post weaken",
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
  @Axiom(
    name = "andCommute",
    displayName = Some("∧C"),
    displayNameAscii = Some("&C"),
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val andCommute: DerivedAxiomInfo =
    derivedAxiom("& commute", Sequent(IndexedSeq(), IndexedSeq("(p_() & q_()) <-> (q_() & p_())".asFormula)), prop)

  /**
   * {{{
   * Axiom "| commute".
   *   (p() | q()) <-> (q() | p())
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(
    name = "orCommute",
    displayName = Some("∨C"),
    displayNameAscii = Some("|C"),
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val orCommute: DerivedAxiomInfo =
    derivedAxiom("| commute", Sequent(IndexedSeq(), IndexedSeq("(p_() | q_()) <-> (q_() | p_())".asFormula)), prop)

  /**
   * {{{
   * Axiom "& associative".
   *   ((p() & q()) & r()) <-> (p() & (q() & r()))
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(
    name = "andAssoc",
    displayName = Some("∧A"),
    displayNameAscii = Some("&A"),
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val andAssoc: DerivedAxiomInfo = derivedAxiom(
    "& associative",
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
  @Axiom(
    name = "orAssoc",
    displayName = Some("∨A"),
    displayNameAscii = Some("|A"),
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val orAssoc: DerivedAxiomInfo = derivedAxiom(
    "| associative",
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
  @Axiom(
    name = "andReflexive",
    displayName = Some("∧R"),
    displayNameAscii = Some("&R"),
    key = "0",
    recursor = "*",
    unifier = Unifier.Full,
  )
  lazy val andReflexive: DerivedAxiomInfo =
    derivedAxiom("& reflexive", Sequent(IndexedSeq(), IndexedSeq("p_() & p_() <-> p_()".asFormula)), prop)

  /**
   * {{{
   * Axiom "<-> true".
   *   (p() <-> true) <-> p()
   * End.
   * }}}
   */
  @Axiom(
    name = "equivTrue",
    displayName = Some("↔true"),
    displayNameAscii = Some("<-> true"),
    key = "0",
    recursor = "*",
    unifier = Unifier.Linear,
  )
  lazy val equivTrue: DerivedAxiomInfo =
    derivedAxiom("<-> true", Sequent(IndexedSeq(), IndexedSeq("(p() <-> true) <-> p()".asFormula)), prop)

  /**
   * {{{
   * Axiom "-> self".
   *   (p() -> p()) <-> true
   * End.
   * }}}
   */
  @Axiom(name = "implySelf", displayName = Some("→self"), displayNameAscii = Some("-> self"), key = "0", recursor = "*")
  lazy val implySelf: DerivedAxiomInfo =
    derivedAxiom("-> self", Sequent(IndexedSeq(), IndexedSeq("(p_() -> p_()) <-> true".asFormula)), prop)

  /**
   * {{{
   * Axiom "-> converse".
   *   (p() -> q()) <-> (!q() -> !p())
   * End.
   * }}}
   * Contraposition
   */
  @Axiom(
    name = "converseImply",
    displayName = Some("→conv"),
    displayNameAscii = Some("-> conv"),
    key = "0",
    recursor = "*",
  )
  lazy val converseImply: DerivedAxiomInfo = derivedAxiom(
    "-> converse",
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
  @Axiom(
    name = "notAnd",
    displayName = Some("¬∧"),
    displayNameAscii = Some("!&"),
    displayConclusion = "__¬(p∧q)__↔(¬p|¬q)",
    unifier = Unifier.SurjectiveLinear,
    key = "0",
    recursor = "0;1",
  )
  lazy val notAnd: DerivedAxiomInfo = derivedAxiom(
    "!& deMorgan",
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
  @Axiom(
    name = "notOr",
    displayName = Some("¬∨"),
    displayNameAscii = Some("!|"),
    displayConclusion = "__(¬(p|q))__↔(¬p∧¬q)",
    unifier = Unifier.SurjectiveLinear,
    key = "0",
    recursor = "0;1",
  )
  lazy val notOr: DerivedAxiomInfo = derivedAxiom(
    "!| deMorgan",
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
  @Axiom(
    name = "notImply",
    displayName = Some("¬→"),
    displayNameAscii = Some("!->"),
    displayConclusion = "__¬(p->q)__↔(p∧¬q)",
    unifier = Unifier.SurjectiveLinear,
    key = "0",
    recursor = "0;1",
  )
  lazy val notImply: DerivedAxiomInfo = derivedAxiom(
    "!-> deMorgan",
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
  @Axiom(
    name = "notEquiv",
    displayName = Some("¬↔"),
    displayNameAscii = Some("!<->"),
    displayConclusion = "__¬(p↔q)__↔(p∧¬q)| (¬p∧q)",
    unifier = Unifier.SurjectiveLinear,
    key = "0",
    recursor = "0.0;0.1;1.0;1.1",
  )
  lazy val notEquiv: DerivedAxiomInfo = derivedAxiom(
    "!<-> deMorgan",
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
  @Axiom(
    name = "implyExpand",
    displayName = Some("→E"),
    displayNameAscii = Some("->E"),
    unifier = Unifier.Linear,
    key = "0",
    recursor = "0;1",
  )
  lazy val implyExpand: DerivedAxiomInfo =
    derivedAxiom("-> expand", Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) <-> ((!p_()) | q_())".asFormula)), prop)

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
  @Axiom(name = "PC1", unifier = Unifier.Full)
  lazy val PC1: DerivedAxiomInfo =
    derivedAxiom("PC1", Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> p_()".asFormula)), prop)

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
  @Axiom(name = "PC2", unifier = Unifier.Full)
  lazy val PC2: DerivedAxiomInfo =
    derivedAxiom("PC2", Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> q_()".asFormula)), prop)

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
  @Axiom(name = "PC3", unifier = Unifier.Full)
  lazy val PC3: DerivedAxiomInfo = derivedAxiom(
    "PC3",
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
  @Axiom(name = "PC9", unifier = Unifier.Full)
  lazy val PC9: DerivedAxiomInfo =
    derivedAxiom("PC9", Sequent(IndexedSeq(), IndexedSeq("p_() -> p_() | q_()".asFormula)), prop)

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
  @Axiom(name = "PC10", unifier = Unifier.Full)
  lazy val PC10: DerivedAxiomInfo =
    derivedAxiom("PC10", Sequent(IndexedSeq(), IndexedSeq("q_() -> p_() | q_()".asFormula)), prop)

  /**
   * {{{
   * Axiom "-> tautology".
   *   (p() -> (q() -> p()&q())) <-> true
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(
    name = "implyTautology",
    displayName = Some("→taut"),
    displayNameAscii = Some("->taut"),
    unifier = Unifier.Full,
  )
  lazy val implyTautology: DerivedAxiomInfo = derivedAxiom(
    "-> tautology",
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
  @Axiom(
    name = "Dlessequal",
    displayName = Some("≤'"),
    displayNameAscii = Some("<='"),
    displayConclusion = "__(f(x)≤g(x))'__↔f(x)'≤g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dlessequal: DerivedAxiomInfo = derivedAxiom(
    "<=' derive <=",
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
  @Axiom(
    name = "Dless",
    displayName = Some("<'"),
    displayConclusion = "__(f(x)<g(m))'__↔f(x)'≤g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dless: DerivedAxiomInfo = derivedAxiom(
    "<' derive <",
    Sequent(IndexedSeq(), IndexedSeq("(f(||) < g(||))' <-> ((f(||))' <= (g(||))')".asFormula)),
    useAt(flipLessEqual)(1, 1 :: Nil) &
      useAt(flipLess)(1, 0 :: 0 :: Nil) &
      byUS(Dgreater),
  )

  @Axiom(
    name = "Dequal",
    displayName = Some("='"),
    displayConclusion = "__(f(x)=g(x))'__↔f(x)'=g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dequal: DerivedAxiomInfo = derivedAxiom(
    "=' derive =",
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
  @Axiom(
    name = "Dnotequal",
    displayName = Some("≠'"),
    displayNameAscii = Some("!='"),
    displayConclusion = "__(f(x)≠g(x))'__↔f(x)'=g(x)'",
    key = "0",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  val Dnotequal: DerivedAxiomInfo = derivedAxiom(
    "!=' derive !=",
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
  @Axiom(
    name = "Dimply",
    displayName = Some("→'"),
    displayNameAscii = Some("->'"),
    displayConclusion = "__(P→Q)'__↔(¬P∨Q)'",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val Dimply: DerivedAxiomInfo = derivedAxiom(
    "->' derive imply",
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
  @Axiom(
    name = "forallThenExists",
    displayName = Some("∀→∃"),
    displayNameAscii = Some("all->exists"),
    displayLevel = DisplayLevel.Internal,
  )
  lazy val forallThenExists: DerivedAxiomInfo = derivedAxiom(
    "\\forall->\\exists",
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
  @Axiom(
    name = "implyTrue",
    displayName = Some("→⊤"),
    displayNameAscii = Some("->T"),
    displayConclusion = "__(p→⊤)__↔⊤",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val implyTrue: DerivedAxiomInfo =
    derivedAxiom("->true", Sequent(IndexedSeq(), IndexedSeq("(p_()->true) <-> true".asFormula)), prop)

  /**
   * {{{
   * Axiom "true->".
   *   (true->p()) <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(
    name = "trueImply",
    displayName = Some("⊤→"),
    displayNameAscii = Some("T->"),
    displayConclusion = "__(⊤→p)__↔p",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val trueImply: DerivedAxiomInfo =
    derivedAxiom("true->", Sequent(IndexedSeq(), IndexedSeq("(true->p_()) <-> p_()".asFormula)), prop)

  /**
   * {{{
   * Axiom "&true".
   *   (p()&true) <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(
    name = "andTrue",
    displayName = Some("∧⊤"),
    displayNameAscii = Some("&T"),
    displayConclusion = "__(p∧⊤)__↔p",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val andTrue: DerivedAxiomInfo =
    derivedAxiom("&true", Sequent(IndexedSeq(), IndexedSeq("(p_()&true) <-> p_()".asFormula)), prop)

  /**
   * {{{
   * Axiom "&false".
   *   (p()&false) <-> false
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(
    name = "andFalse",
    displayName = Some("∧⊥"),
    displayNameAscii = Some("&false"),
    displayConclusion = "__(p∧⊥)__↔⊥",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val andFalse: DerivedAxiomInfo =
    derivedAxiom("&false", Sequent(IndexedSeq(), IndexedSeq("(p_()&false) <-> false".asFormula)), prop)

  /* inverse andtrue axiom for chase */
  @Axiom(name = "andTrueInv", displayName = Some("&true inv"), key = "0", recursor = "*")
  lazy val andTrueInv: DerivedAxiomInfo =
    derivedAxiom("&true inv", Sequent(IndexedSeq(), IndexedSeq("p_() <-> (p_()&true)".asFormula)), prop)

  /**
   * {{{
   * Axiom "true&".
   *   (true&p()) <-> p()
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(
    name = "trueAnd",
    displayName = Some("⊤∧"),
    displayNameAscii = Some("T&"),
    displayConclusion = "__(⊤∧p)__↔p",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val trueAnd: DerivedAxiomInfo =
    derivedAxiom("true&", Sequent(IndexedSeq(), IndexedSeq("(true&p_()) <-> p_()".asFormula)), prop)

  /**
   * {{{
   * Axiom "false&".
   *   (false&p()) <-> false
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(
    name = "falseAnd",
    displayName = Some("⊥∧"),
    displayNameAscii = Some("false&"),
    displayConclusion = "__(⊥∧p)__↔⊥",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val falseAnd: DerivedAxiomInfo =
    derivedAxiom("false&", Sequent(IndexedSeq(), IndexedSeq("(false&p_()) <-> false".asFormula)), prop)

  /**
   * {{{
   * Axiom "0*".
   *   (0*f()) = 0
   * End.
   * }}}
   *
   * @Derived
   */
  @Axiom(name = "zeroTimes", displayName = Some("0*"), unifier = Unifier.SurjectiveLinear)
  lazy val zeroTimes: DerivedAxiomInfo = derivedAxiom(
    "0*",
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
  @Axiom(name = "timesZero", displayName = Some("*0"), unifier = Unifier.SurjectiveLinear)
  lazy val timesZero: DerivedAxiomInfo = derivedAxiom(
    "*0",
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
  @Axiom(name = "negOneTimes", displayName = Some("-1*"), unifier = Unifier.SurjectiveLinear)
  lazy val negOneTimes: DerivedAxiomInfo = derivedAxiom(
    "-1*",
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
  @Axiom(name = "zeroPlus", displayName = Some("0+"), unifier = Unifier.SurjectiveLinear)
  lazy val zeroPlus: DerivedAxiomInfo = derivedAxiom(
    "0+",
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
  @Axiom(name = "plusZero", displayName = Some("+0"), unifier = Unifier.SurjectiveLinear)
  lazy val plusZero: DerivedAxiomInfo = derivedAxiom(
    "+0",
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
  @Axiom(
    name = "DW",
    displayConclusion = "__[x'=f(x)&Q]P__↔[x'=f(x)&Q](Q→P)",
    key = "0",
    recursor = "",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val DW: DerivedAxiomInfo = derivedAxiom(
    "DW differential weakening",
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
  @Axiom(
    name = "DWeakenAnd",
    displayName = Some("DW∧"),
    displayNameAscii = Some("DWand"),
    displayConclusion = "[x'=f(x)&Q]P→[x'=f(x)&Q](Q∧P)",
  )
  lazy val DWeakenAnd: DerivedAxiomInfo = derivedAxiom(
    "DW differential weakening and",
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
  @Axiom(name = "DWQinitial", displayName = Some("DW Q initial"), displayConclusion = "(Q→[x'=f(x)&Q]P) ↔ [x'=f(x)&Q]P")
  lazy val DWQinitial: DerivedAxiomInfo = derivedAxiom(
    "DW Q initial",
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
  @Axiom(
    name = "DR",
    displayConclusion = "(__[{x'=f(x)&Q}]P__←[{x'=f(x)&R}]P)←[{x'=f(x)&Q}]R",
    key = "1.1",
    unifier = Unifier.SurjectiveLinear,
    inputs = "R:formula",
  )
  lazy val DR: DerivedAxiomInfo = derivedAxiom(
    "DR differential refine",
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
  @Axiom(
    name = "DRd",
    displayConclusion = "(__<{x'=f(x)&Q}>P__←<{x'=f(x)&R}>P)←[{x'=f(x)&R}]Q",
    key = "1.1",
    unifier = Unifier.SurjectiveLinear,
    inputs = "R:formula",
  )
  lazy val DRd: DerivedAxiomInfo = derivedAxiom(
    "DR<> differential refine",
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
  @Axiom(
    name = "DCaxiom",
    displayName = Some("DC"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "(__[x'=f(x)&Q]P__↔[x'=f(x)&Q∧R]P)←[x'=f(x)&Q]R",
    key = "1.0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
    inputs = "R:formula",
  )
  lazy val DC: DerivedAxiomInfo = derivedAxiom(
    "DC differential cut",
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
  @Axiom(
    name = "DI",
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "__[{x'=f(x)&Q}]P__←(Q→P∧[{x'=f(x)&Q}](P)')",
    unifier = Unifier.SurjectiveLinear,
    key = "1",
    recursor = "1.1",
  )
  lazy val DI: DerivedAxiomInfo = derivedAxiom(
    "DI differential invariant",
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
  @Axiom(
    name = "DIoless",
    displayName = Some("DIo <"),
    displayConclusion = "(__[{x'=f(x)&Q}]g(x)<h(x)__↔[?Q]g(x)<h(x))←(Q→[{x'=f(x)&Q}](g(x)<h(x)→(g(x)<h(x))'))",
    unifier = Unifier.SurjectiveLinear,
    key = "1.0",
    recursor = "*",
  )
  lazy val DIoless: DerivedAxiomInfo = derivedAxiom(
    "DIo open differential invariance <",
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
  @Axiom(
    name = "dDX",
    displayConclusion = "Q∧P → <x'=f(x)&Q>P",
    key = "1",
    recursor = "1",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val dDX: DerivedAxiomInfo = derivedAxiom(
    "DX diamond differential skip",
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
  @Axiom(
    name = "DSnodomain",
    displayName = Some("DS"),
    displayConclusion = "__[{x'=c()}]P__ ↔ ∀t≥0 [x:=x+c()*t;]P",
    key = "0",
    recursor = "0.1.1;*",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DSnodomain: DerivedAxiomInfo = derivedAxiom(
    "DS differential equation solution",
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
  @Axiom(
    name = "DSdnodomain",
    displayName = Some("DS"),
    displayConclusion = "__<{x'=c()}>P__ ↔ ∃t≥0 <x:=x+c()*t;>P",
    key = "0",
    recursor = "0.1.1;*",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DSdnodomain: DerivedAxiomInfo = derivedAxiom(
    "Dsol differential equation solution",
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
  @Axiom(name = "DSddomain", displayName = Some("DS&"), unifier = Unifier.Linear)
  lazy val DSddomain: DerivedAxiomInfo = derivedAxiom(
    "Dsol& differential equation solution",
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
  @Axiom(name = "DGpreghost", displayName = Some("DG"))
  lazy val DGpreghost: DerivedAxiomInfo = derivedAxiom(
    "DG differential pre-ghost",
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
  @Axiom(name = "DGd")
  lazy val DGd: DerivedAxiomInfo = derivedAxiom(
    "DGd diamond differential ghost",
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
  @Axiom(name = "DGdi")
  lazy val DGdi: DerivedAxiomInfo = derivedAxiom(
    "DGd diamond inverse differential ghost implicational",
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
  @Axiom(name = "DGCd", displayName = Some("DG"), displayConclusion = "__[{x'=f(x)&Q}]P__↔∃y [{x'=f(x),y'=g()&Q}]P")
  lazy val DGCd: DerivedAxiomInfo = derivedAxiom(
    "DGd diamond differential ghost constant",
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

  @Axiom(name = "DGCdc")
  lazy val DGCdc: DerivedAxiomInfo = derivedAxiom(
    "DGd diamond differential ghost constant converse",
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

  @Axiom(name = "DGCde")
  lazy val DGCde: DerivedAxiomInfo = derivedAxiom(
    "DGd diamond differential ghost constant exists",
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
  @Axiom(name = "DWd")
  lazy val DWd: DerivedAxiomInfo = derivedAxiom(
    "DWd diamond differential weakening",
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
  @Axiom(name = "DWdQinitial", displayName = Some("DWd Q initial"))
  lazy val DWdQinitial: DerivedAxiomInfo = derivedAxiom(
    "DWd Q initial",
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
  @Axiom(name = "DWd2")
  lazy val DWd2: DerivedAxiomInfo = derivedAxiom(
    "DWd2 diamond differential weakening",
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
  @Axiom(
    name = "DCdaxiom",
    displayName = Some("DCd"),
    displayConclusion = "(__<x'=f(x)&Q>P__↔<x'=f(x)&Q∧R>P)←[x'=f(x)&Q]R",
    key = "1.0",
    recursor = "*",
  )
  lazy val DCdaxiom: DerivedAxiomInfo = derivedAxiom(
    "DCd diamond differential cut",
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
  @Axiom(name = "leaveWithinClosed", key = "1.0", recursor = "*")
  lazy val leaveWithinClosed: DerivedAxiomInfo = derivedAxiom(
    "leave within closed <=",
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
  @Axiom(name = "openInvariantClosure", key = "1.0", recursor = "*")
  lazy val openInvariantClosure: DerivedAxiomInfo = derivedAxiom(
    "open invariant closure >",
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
  @Axiom(name = "commaCommuted")
  lazy val commaCommuted: DerivedAxiomInfo = derivedAxiom(
    ",d commute",
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
  @Axiom(
    name = "DBXgt",
    displayName = Some("DBX>"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "(e>0 → __[x'=f(x)&Q]e>0__) ← [x'=f(x)&Q](e)'≥ge",
    key = "1.1",
    recursor = "1.0",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DBXgt: DerivedAxiomInfo = derivedAxiom(
    "DBX>",
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
  @Axiom(
    name = "DBXgtOpen",
    displayName = Some("DBX> open"),
    displayConclusion = "(e_>0 → __[x'=f(x)&Q]e_>0__) ← [x'=f(x)&Q](e_>0→(e_)'≥ge)",
    key = "1.1",
    recursor = "1.1.0",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DBXgtOpen: DerivedAxiomInfo = derivedAxiom(
    "DBX> open",
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
  @Axiom(
    name = "DBXge",
    displayName = Some("DBX>="),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "(e>=0 → __[x'=f(x)&Q]e>=0__) ← [x'=f(x)&Q](e)'≥ge",
    key = "1.1",
    recursor = "1.0",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DBXge: DerivedAxiomInfo = derivedAxiom(
    "DBX>=",
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
  @Axiom(
    name = "DBXeq",
    displayName = Some("DBX="),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "(e=0 → __[x'=f(x)&Q]e=0__) ← [x'=f(x)&Q](e)'=ge",
    key = "1.1",
    recursor = "1.0",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DBXeq: DerivedAxiomInfo = derivedAxiom(
    "DBX=",
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
  @Axiom(
    name = "DBXltOpen",
    displayName = Some("DBX< open"),
    displayConclusion = "(e<0 → __[x'=f(x)&Q]e<0__) ← [x'=f(x)&Q](e<0→(e)'<=ge)",
    key = "1.1",
    recursor = "1.1.0",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DBXltOpen: DerivedAxiomInfo = derivedAxiom(
    "DBX< open",
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
  @Axiom(
    name = "DBXle",
    displayName = Some("DBX<="),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "(e<=0 → __[x'=f(x)&Q]e<=0__) ← [x'=f(x)&Q](e)'<=ge",
    key = "1.1",
    recursor = "1.0",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DBXle: DerivedAxiomInfo = derivedAxiom(
    "DBX<=",
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
  @Axiom(
    name = "DBXneOpen",
    displayName = Some("DBX!= open"),
    displayConclusion = "(e!=0 → __[x'=f(x)&Q]e!=0__) ← [x'=f(x)&Q](e!=0→(e)'=ge)",
    key = "1.1",
    recursor = "1.1.0",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DBXneOpen: DerivedAxiomInfo = derivedAxiom(
    "DBX!= open",
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
  @Axiom(name = "dualIVT", key = "1", unifier = Unifier.Linear)
  lazy val dualIVT: DerivedAxiomInfo = derivedFormula(
    "dualIVT",
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

  @Axiom(name = "oneGeZero")
  lazy val oneGeZero: DerivedAxiomInfo = derivedFormula("oneGeZero", "1>=0".asFormula, QE & done)

  @Axiom(name = "timeCond")
  lazy val timeCond: DerivedAxiomInfo = derivedFormula(
    "timeCond",
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

  @Axiom(name = "timeStep", key = "1", unifier = Unifier.Linear)
  lazy val timeStep: DerivedAxiomInfo = derivedFormula(
    "timeStep",
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
  @Axiom(
    name = "dualb",
    displayName = Some("[d]"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "__[a<sup>d</sup>]P__↔¬[a]¬P",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val dualb: DerivedAxiomInfo = derivedAxiom(
    "[d] dual",
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
  @Axiom(
    name = "dualDirectb",
    displayName = Some("[d]"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "__[a<sup>d</sup>]P__↔&langle;a&rangle;P",
    key = "0",
    recursor = ".",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val dualDirectb: DerivedAxiomInfo = derivedAxiom(
    "[d] dual direct",
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
  @Axiom(
    name = "dualDirectd",
    displayName = Some("<d>"),
    displayConclusion = "__&langle;a<sup>d</sup>&rangle;P__↔[a]P",
    key = "0",
    recursor = ".",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val dualDirectd: DerivedAxiomInfo = derivedAxiom(
    "<d> dual direct",
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
  @Axiom(
    name = "DvariableCommutedAxiom",
    displayName = Some("x',C"),
    displayConclusion = "x'=__(x)'__",
    unifier = Unifier.Linear,
    key = "0",
    recursor = "",
  )
  lazy val DvariableCommutedAxiom: DerivedAxiomInfo = derivedAxiom(
    "x' derive var commuted",
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
  @Axiom(name = "DvariableAxiom", displayName = Some("x'"), displayConclusion = "__(x)'__=x'")
  lazy val DvariableAxiom: DerivedAxiomInfo = derivedFact(
    "x' derive variable",
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
  @Axiom(name = "Dlinear", displayName = Some("l'"), unifier = Unifier.Linear, key = "0", recursor = "1")
  lazy val Dlinear: DerivedAxiomInfo = derivedAxiom(
    "' linear",
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
  @Axiom(
    name = "DlinearRight",
    displayName = Some("l'"),
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinearPretend,
  )
  lazy val DlinearRight: DerivedAxiomInfo = derivedAxiom(
    "' linear right",
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
  @Axiom(
    name = "UniqIff",
    displayName = Some("Uniq"),
    displayConclusion = "<x'=f(x)&Q}>P ∧ <x'=f(x)&R>P ↔ __<x'=f(x)&Q∧R>P__",
    key = "1",
    recursor = "0;1",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val UniqIff: DerivedAxiomInfo = derivedFormula(
    "Uniq uniqueness iff",
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
  @Axiom(
    name = "equalReflexive",
    displayName = Some("=R"),
    displayConclusion = "s=s",
    unifier = Unifier.Full,
    key = "*",
  )
  lazy val equalReflexive: DerivedAxiomInfo = derivedAxiom(
    "= reflexive",
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
  @Axiom(
    name = "equalCommute",
    displayName = Some("=C"),
    displayConclusion = "__f=g__ ↔ g=f",
    key = "0",
    recursor = "*",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val equalCommute: DerivedAxiomInfo = derivedAxiom(
    "= commute",
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
  @Axiom(name = "greaterEqualReflexive", displayName = Some(">=R"), unifier = Unifier.Full, key = "", recursor = "")
  lazy val greaterEqualReflexive: DerivedAxiomInfo =
    derivedAxiom(">= reflexive", Sequent(IndexedSeq(), IndexedSeq("s_() >= s_()".asFormula)), QE & done)

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
  @Axiom(name = "lessEqual", displayName = Some("<="), unifier = Unifier.Linear)
  lazy val lessEqual: DerivedAxiomInfo = derivedAxiom(
    "<=",
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
  @Axiom(name = "greaterEqual", displayName = Some(">="), unifier = Unifier.Linear)
  lazy val greaterEqual: DerivedAxiomInfo = derivedAxiom(
    ">=",
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
  @Axiom(
    name = "notNotEqual",
    displayName = Some("¬≠"),
    displayNameAscii = Some("!!="),
    displayConclusion = "__(¬(f≠g)__↔(f=g))",
    unifier = Unifier.Linear,
  )
  lazy val notNotEqual: DerivedAxiomInfo = derivedAxiom(
    "! !=",
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
  @Axiom(
    name = "notEqual",
    displayName = Some("¬ ="),
    displayNameAscii = Some("! ="),
    displayConclusion = "__(¬(f=g))__↔(f≠g)",
    unifier = Unifier.Linear,
  )
  lazy val notEqual: DerivedAxiomInfo = derivedAxiom(
    "! =",
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
  @Axiom(
    name = "notEqual2Or",
    displayName = Some("≠2∨"),
    displayNameAscii = Some("!=2|"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__(f≠g)__ ↔ f<g ∨ f>g",
    unifier = Unifier.Linear,
  )
  lazy val notEqual2Or: DerivedAxiomInfo = derivedAxiom(
    "!=2|",
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
  @Axiom(
    name = "equal2And",
    displayName = Some("=2∧"),
    displayNameAscii = Some("=2&"),
    displayLevel = DisplayLevel.Browse,
    displayConclusion = "__(f≠g)__ ↔ f<g ∨ f>g",
    unifier = Unifier.Linear,
  )
  lazy val equal2And: DerivedAxiomInfo = derivedAxiom(
    "=2&",
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
  @Axiom(
    name = "notGreater",
    displayName = Some("¬>"),
    displayNameAscii = Some("!>"),
    displayConclusion = "__¬(f>g)__↔(f≤g)",
    unifier = Unifier.Linear,
  )
  lazy val notGreater: DerivedAxiomInfo = derivedAxiom(
    "! >",
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
  @Axiom(name = "flipGreater", displayName = Some(">F"), unifier = Unifier.Linear, key = "0", recursor = "*")
  lazy val flipGreater: DerivedAxiomInfo = derivedAxiom(
    "> flip",
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
  @Axiom(name = "flipGreaterEqual", displayName = Some(">=F"), unifier = Unifier.Linear, key = "0", recursor = "*")
  lazy val flipGreaterEqual: DerivedAxiomInfo = derivedAxiom(
    ">= flip",
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
  @Axiom(name = "flipLess", displayName = Some("<F"), unifier = Unifier.Linear)
  lazy val flipLess: DerivedAxiomInfo = derivedAxiom(
    "< flip",
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
  @Axiom(name = "flipLessEqual", displayName = Some("<=F"), unifier = Unifier.Linear)
  lazy val flipLessEqual: DerivedAxiomInfo = derivedAxiom(
    "<= flip",
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
  @Axiom(
    name = "notLess",
    displayName = Some("¬<"),
    displayNameAscii = Some("!<"),
    displayConclusion = "__¬(f<g)__↔(f≥g)",
    unifier = Unifier.Linear,
  )
  lazy val notLess: DerivedAxiomInfo = derivedAxiom(
    "! <",
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
  @Axiom(
    name = "notLessEqual",
    displayName = Some("¬≤"),
    displayNameAscii = Some("!<="),
    displayConclusion = "__(¬(f≤g)__↔(f>g)",
    unifier = Unifier.Linear,
  )
  lazy val notLessEqual: DerivedAxiomInfo = derivedAxiom(
    "! <=",
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
  @Axiom(name = "notGreaterEqual", displayName = Some("¬≥"), displayNameAscii = Some("!>="), unifier = Unifier.Linear)
  lazy val notGreaterEqual: DerivedAxiomInfo = derivedAxiom(
    "! >=",
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
  @Axiom(name = "plusAssociative", displayName = Some("+A"), unifier = Unifier.Linear)
  lazy val plusAssociative: DerivedAxiomInfo = derivedAxiom(
    "+ associative",
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
  @Axiom(name = "timesAssociative", displayName = Some("*A"), unifier = Unifier.Linear)
  lazy val timesAssociative: DerivedAxiomInfo = derivedAxiom(
    "* associative",
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
  @Axiom(name = "plusCommute", displayName = Some("+C"), unifier = Unifier.Linear)
  lazy val plusCommute: DerivedAxiomInfo = derivedAxiom(
    "+ commute",
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
  @Axiom(name = "timesCommute", displayName = Some("*C"), unifier = Unifier.Linear)
  lazy val timesCommute: DerivedAxiomInfo = derivedAxiom(
    "* commute",
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
  @Axiom(name = "distributive", displayName = Some("*+"))
  lazy val distributive: DerivedAxiomInfo = derivedAxiom(
    "distributive",
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
  @Axiom(name = "timesIdentity", displayName = Some("*I"))
  lazy val timesIdentity: DerivedAxiomInfo = derivedAxiom(
    "* identity",
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
  @Axiom(name = "identityTimes", displayName = Some("I*"))
  lazy val identityTimes: DerivedAxiomInfo = derivedAxiom(
    "identity *",
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
  @Axiom(name = "timesDivInverse", displayName = Some("1/x*"))
  lazy val timesDivInverse: DerivedAxiomInfo = derivedAxiom(
    "* div-inverse",
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
  @Axiom(name = "plusInverse", displayName = Some("+i"), unifier = Unifier.Full)
  lazy val plusInverse: DerivedAxiomInfo = derivedAxiom(
    "+ inverse",
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
  @Axiom(name = "timesInverse", displayName = Some("*i"), unifier = Unifier.Full)
  lazy val timesInverse: DerivedAxiomInfo = derivedAxiom(
    "* inverse",
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
  @Axiom(name = "positivity", displayName = Some("Pos"))
  lazy val positivity: DerivedAxiomInfo = derivedAxiom(
    "positivity",
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
  @Axiom(name = "plusClosed", displayName = Some("+c"))
  lazy val plusClosed: DerivedAxiomInfo = derivedAxiom(
    "+ closed",
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
  @Axiom(name = "timesClosed", displayName = Some("*c"))
  lazy val timesClosed: DerivedAxiomInfo = derivedAxiom(
    "* closed",
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
  @Axiom(name = "less", displayName = Some("<"), unifier = Unifier.Linear)
  lazy val less: DerivedAxiomInfo = derivedAxiom(
    "<",
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
  @Axiom(name = "greater", displayName = Some(">"), unifier = Unifier.Linear)
  lazy val greater: DerivedAxiomInfo =
    derivedAxiom(">", Sequent(IndexedSeq(), IndexedSeq("f_() > g_() <-> g_() < f_()".asFormula)), byUS(flipGreater))

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
  @Axiom(name = "oneGreaterZero", displayName = Some("1>0"), unifier = Unifier.Linear)
  lazy val oneGreaterZero: DerivedAxiomInfo =
    derivedAxiom("1>0", Sequent(IndexedSeq(), IndexedSeq("1>0".asFormula)), TactixLibrary.RCF)

  /**
   * {{{
   * Axiom "nonnegative squares".
   *   f()^2>=0
   * End.
   * }}}
   */
  @Axiom(name = "nonnegativeSquares", displayName = Some("^2>=0"), unifier = Unifier.Linear)
  lazy val nonnegativeSquares: DerivedAxiomInfo = derivedAxiom(
    "nonnegative squares",
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
  @Axiom(name = "greaterImpliesNotEqual", displayName = Some(">2!="))
  lazy val greaterImpliesNotEqual: DerivedAxiomInfo = derivedAxiom(
    ">2!=",
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
  @Axiom(name = "greaterMonotone", displayName = Some(">mon"))
  lazy val greaterMonotone: DerivedAxiomInfo = derivedAxiom(
    "> monotone",
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
  @Axiom(name = "abs")
  lazy val abs: DerivedAxiomInfo = derivedAxiom(
    "abs",
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
  @Axiom(name = "min")
  lazy val min: DerivedAxiomInfo = derivedAxiom(
    "min",
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
  @Axiom(name = "max")
  lazy val max: DerivedAxiomInfo = derivedAxiom(
    "max",
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
  @Axiom(name = "loopStuck", displayName = Some("<*> stuck"), key = "0", recursor = "")
  lazy val loopStuck: DerivedAxiomInfo = derivedAxiom(
    "<*> stuck",
    Sequent(IndexedSeq(), IndexedSeq("<{a_;}*>p_(||) <-> <{a_;}*>p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  @Axiom(name = "programStuck", displayName = Some("<a> stuck"), key = "0", recursor = "1")
  lazy val programStuck: DerivedAxiomInfo = derivedAxiom(
    "<a> stuck",
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
  @Axiom(name = "odeStuck", displayName = Some("<'> stuck"), key = "0", recursor = "")
  lazy val odeStuck: DerivedAxiomInfo = derivedAxiom(
    "<'> stuck",
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
  @Axiom(name = "andRecursor", displayName = Some("& recursor"), unifier = Unifier.Linear, key = "0", recursor = "0;1")
  lazy val andRecursor: DerivedAxiomInfo =
    derivedAxiom("& recursor", Sequent(IndexedSeq(), IndexedSeq("(p_() & q_()) <-> (p_() & q_())".asFormula)), prop)

  /**
   * {{{
   * Axiom "| recursor".
   *   p() | q() <-> p() | q()
   * End.
   * }}}
   */
  @Axiom(name = "orRecursor", displayName = Some("| recursor"), unifier = Unifier.Linear, key = "0", recursor = "0;1")
  lazy val orRecursor: DerivedAxiomInfo =
    derivedAxiom("| recursor", Sequent(IndexedSeq(), IndexedSeq("(p_() | q_()) <-> (p_() | q_())".asFormula)), prop)

  /**
   * {{{
   * Axiom "<= both".
   *   f()<=g() <- ((f() <= F() & gg() <= g()) & F() <= gg())
   * End.
   * }}}
   */
  @Axiom(name = "intervalLEBoth", displayName = Some("<= both"), key = "1", recursor = "")
  lazy val intervalLEBoth: DerivedAxiomInfo = derivedAxiom(
    "<= both",
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
  @Axiom(name = "intervalLBoth", displayName = Some("< both"), key = "1", recursor = "")
  lazy val intervalLBoth: DerivedAxiomInfo = derivedAxiom(
    "< both",
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
  @Axiom(name = "intervalUpNeg", displayName = Some("neg<="), key = "1", recursor = "0")
  lazy val intervalUpNeg: DerivedAxiomInfo = derivedAxiom(
    "neg<= up",
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
  @Axiom(name = "intervalUpAbs", displayName = Some("abs<="), key = "1", recursor = "0.0;0.1")
  lazy val intervalUpAbs: DerivedAxiomInfo = derivedAxiom(
    "abs<= up",
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
  @Axiom(name = "intervalUpMax", displayName = Some("max<="), key = "1", recursor = "0.0;0.1")
  lazy val intervalUpMax: DerivedAxiomInfo = derivedAxiom(
    "max<= up",
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
  @Axiom(name = "intervalUpMin", displayName = Some("min<="), key = "1", recursor = "0.0;0.1")
  lazy val intervalUpMin: DerivedAxiomInfo = derivedAxiom(
    "min<= up",
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
  @Axiom(name = "intervalUpPlus", displayName = Some("+<="), key = "1", recursor = "0.0;0.1")
  lazy val intervalUpPlus: DerivedAxiomInfo = derivedAxiom(
    "+<= up",
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
  @Axiom(name = "intervalUpMinus", displayName = Some("-<="), key = "1", recursor = "0.0;0.1")
  lazy val intervalUpMinus: DerivedAxiomInfo = derivedAxiom(
    "-<= up",
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

  @Axiom(name = "intervalUpTimes", displayName = Some("*<="), key = "1", recursor = "0.0.0;0.0.1;0.1.0;0.1.1")
  lazy val intervalUpTimes: DerivedAxiomInfo = derivedAxiom(
    "*<= up",
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
  @Axiom(name = "intervalUp1Divide", displayName = Some("1/<="))
  lazy val intervalUp1Divide: DerivedAxiomInfo = derivedAxiom(
    "1Div<= up",
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

  @Axiom(name = "intervalUpPower", displayName = Some("pow<="), key = "1", recursor = "0.0;0.1")
  lazy val intervalUpPower: DerivedAxiomInfo = derivedAxiom(
    "pow<= up",
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

  @Axiom(name = "intervalDownNeg", displayName = Some("<=neg"), key = "1", recursor = "0")
  lazy val intervalDownNeg: DerivedAxiomInfo = derivedAxiom(
    "<=neg down",
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

  @Axiom(name = "intervalDownAbs", displayName = Some("<=abs"), key = "1", recursor = "0.0;0.1")
  lazy val intervalDownAbs: DerivedAxiomInfo = derivedAxiom(
    "<=abs down",
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
  @Axiom(name = "intervalDownMax", displayName = Some("<=max"), key = "1", recursor = "0.0;0.1")
  lazy val intervalDownMax: DerivedAxiomInfo = derivedAxiom(
    "<=max down",
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
  @Axiom(name = "intervalDownMin", displayName = Some("<=min"), key = "1", recursor = "0.0;0.1")
  lazy val intervalDownMin: DerivedAxiomInfo = derivedAxiom(
    "<=min down",
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
  @Axiom(name = "intervalDownPlus", displayName = Some("<=+"), key = "1", recursor = "0.0;0.1")
  lazy val intervalDownPlus: DerivedAxiomInfo = derivedAxiom(
    "<=+ down",
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
  @Axiom(name = "intervalDownMinus", displayName = Some("<=-"), key = "1", recursor = "0.0;0.1")
  lazy val intervalDownMinus: DerivedAxiomInfo = derivedAxiom(
    "<=- down",
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
  @Axiom(name = "intervalDownTimes", displayName = Some("<=*"), key = "1", recursor = "0.0.0;0.0.1;0.1.0;0.1.1")
  lazy val intervalDownTimes: DerivedAxiomInfo = derivedAxiom(
    "<=* down",
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
  @Axiom(name = "intervalDown1Divide", displayName = Some("<=1/"))
  lazy val intervalDown1Divide: DerivedAxiomInfo = derivedAxiom(
    "<=1Div down",
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

  @Axiom(name = "intervalDownPower", displayName = Some("<=pow"), key = "1", recursor = "0.0;0.1")
  lazy val intervalDownPower: DerivedAxiomInfo = derivedAxiom(
    "<=pow down",
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
  @Axiom(name = "equalExpand")
  lazy val equalExpand: DerivedAxiomInfo = derivedAxiom(
    "= expand",
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
  @Axiom(name = "notEqualExpand")
  lazy val notEqualExpand: DerivedAxiomInfo = derivedAxiom(
    "!= expand",
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
  @Axiom(name = "geNeg")
  lazy val geNeg: DerivedAxiomInfo =
    derivedAxiom(">= neg", Sequent(IndexedSeq(), IndexedSeq("f_()>=g_() <-> -f_()<=-g_()".asFormula)), QE & done)

  /**
   * {{{
   * Axiom "> neg".
   *   f_()>g_() <-> -f_() < -g_()
   * End.
   * }}}
   */
  @Axiom(name = "gtNeg")
  lazy val gtNeg: DerivedAxiomInfo =
    derivedAxiom("> neg", Sequent(IndexedSeq(), IndexedSeq("f_()>g_() <-> -f_() < -g_()".asFormula)), QE & done)

  /**
   * {{{
   * Axiom "<= to <".
   *   f_()<=0 <- f_()<0
   * End.
   * }}}
   */
  @Axiom(name = "leApprox", unifier = Unifier.Linear, key = "1", recursor = "")
  lazy val leApprox: DerivedAxiomInfo =
    derivedAxiom("<= to <", Sequent(IndexedSeq(), IndexedSeq("f_()<=0 <- f_()<0".asFormula)), QE & done)

  /**
   * {{{
   * Axiom "metric <".
   *   f_()<g_() <-> f_()-g_()<0
   * End.
   * }}}
   */
  @Axiom(name = "metricLt", key = "0", recursor = "")
  lazy val metricLt: DerivedAxiomInfo =
    derivedAxiom("metric <", Sequent(IndexedSeq(), IndexedSeq("f_()<g_() <-> f_()-g_()<0".asFormula)), QE & done)

  /**
   * {{{
   * Axiom "metric <=".
   *   f_()<=g_() <-> f_()-g_()<=0
   * End.
   * }}}
   */
  @Axiom(name = "metricLe", key = "0", recursor = "")
  lazy val metricLe: DerivedAxiomInfo =
    derivedAxiom("metric <=", Sequent(IndexedSeq(), IndexedSeq("f_()<=g_() <-> f_()-g_()<=0".asFormula)), QE & done)

  /**
   * {{{
   * Axiom "metric <= & <=".
   *   f_()<=0 & g_()<=0 <-> max(f_(), g_())<=0
   * End.
   * }}}
   */
  @Axiom(name = "metricAndLe", key = "0", recursor = "")
  lazy val metricAndLe: DerivedAxiomInfo = derivedAxiom(
    "metric <= & <=",
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
  @Axiom(name = "metricAndLt", key = "0", recursor = "")
  lazy val metricAndLt: DerivedAxiomInfo = derivedAxiom(
    "metric < & <",
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
  @Axiom(name = "metricOrLe", key = "0", recursor = "")
  lazy val metricOrLe: DerivedAxiomInfo = derivedAxiom(
    "metric <= | <=",
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
  @Axiom(name = "metricOrLt", key = "0", recursor = "")
  lazy val metricOrLt: DerivedAxiomInfo = derivedAxiom(
    "metric < | <",
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
  @Axiom(name = "timesIdentityNeg", key = "0", recursor = "")
  lazy val timesIdentityNeg: DerivedAxiomInfo = derivedAxiom(
    "* identity neg",
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
  @Axiom(name = "minusNeg", unifier = Unifier.Linear, key = "0", recursor = "")
  lazy val minusNeg: DerivedAxiomInfo = derivedAxiom(
    "minus neg",
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
  @Axiom(name = "plusNeg", unifier = Unifier.Linear, key = "0", recursor = "")
  lazy val plusNeg: DerivedAxiomInfo = derivedAxiom(
    "plus neg",
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
  @Axiom(name = "negPlus", displayName = Some("plusNeg"), unifier = Unifier.Linear, key = "0", recursor = "")
  lazy val negPlus: DerivedAxiomInfo = derivedAxiom(
    "neg plus",
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
  @Axiom(name = "negNeg", unifier = Unifier.Linear, key = "0", recursor = "")
  lazy val negNeg: DerivedAxiomInfo = derivedAxiom(
    "neg neg",
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
  @Axiom(name = "minusZero", unifier = Unifier.Linear, key = "0", recursor = "")
  lazy val minusZero: DerivedAxiomInfo = derivedAxiom(
    "-0",
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
  @Axiom(name = "zeroMinus", unifier = Unifier.Linear, key = "0", recursor = "")
  lazy val zeroMinus: DerivedAxiomInfo = derivedAxiom(
    "0-",
    Sequent(IndexedSeq(), IndexedSeq("(0-f_()) = -f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(
      proveBy("\\forall x (0-x = -x)".asFormula, TactixLibrary.RCF)
    ),
  )

  // TODO: add more text to the following
  @Axiom(name = "gtzImpNez")
  lazy val gtzImpNez: DerivedAxiomInfo =
    derivedAxiom(">0 -> !=0", Sequent(IndexedSeq(), IndexedSeq("f_() > 0 -> f_()!=0".asFormula)), QE)

  @Axiom(name = "ltzImpNez")
  lazy val ltzImpNez: DerivedAxiomInfo =
    derivedAxiom("<0 -> !=0", Sequent(IndexedSeq(), IndexedSeq("f_() < 0 -> f_()!=0".asFormula)), QE)

  @Axiom(name = "zeroDivNez")
  lazy val zeroDivNez: DerivedAxiomInfo =
    derivedAxiom("!=0 -> 0/F", Sequent(IndexedSeq(), IndexedSeq("f_() != 0 -> 0/f_() = 0".asFormula)), QE)

  @Axiom(name = "powZero", key = "0", recursor = "")
  lazy val powZero: DerivedAxiomInfo =
    derivedAxiom("F^0", Sequent(IndexedSeq(), IndexedSeq("f_()^0 = 1".asFormula)), QE)

  @Axiom(name = "powOne", key = "0", recursor = "")
  lazy val powOne: DerivedAxiomInfo =
    derivedAxiom("F^1", Sequent(IndexedSeq(), IndexedSeq("f_()^1 = f_()".asFormula)), QE)

  @Axiom(name = "powNegOne", key = "0", recursor = "")
  lazy val powNegOne: DerivedAxiomInfo =
    derivedAxiom("F^(-1)", Sequent(IndexedSeq(), IndexedSeq("f_()^(-1) = 1/f_()".asFormula)), RCF)

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
  @Axiom(name = "lessNotRefl", unifier = Unifier.Full, key = "0", recursor = "")
  lazy val lessNotRefl: DerivedAxiomInfo = derivedAxiom("< irrefl", equivSequent("F_()<F_()", "false"), propQE)

  @Axiom(name = "greaterNotRefl", unifier = Unifier.Full, key = "0", recursor = "")
  lazy val greaterNotRefl: DerivedAxiomInfo = derivedAxiom("> irrefl", equivSequent("F_()>F_()", "false"), propQE)

  @Axiom(name = "notEqualNotRefl", unifier = Unifier.Full, key = "0", recursor = "")
  lazy val notEqualNotRefl: DerivedAxiomInfo = derivedAxiom("!= irrefl", equivSequent("F_()!=F_()", "false"), propQE)

  /** @see [[equivReflexive]] */
  @Axiom(name = "equalRefl", unifier = Unifier.Full, key = "0", recursor = "")
  lazy val equalRefl: DerivedAxiomInfo = derivedAxiom("= refl", equivSequent("F_() = F_()", "true"), propQE)

  @Axiom(name = "lessEqualRefl", unifier = Unifier.Full, key = "0", recursor = "")
  lazy val lessEqualRefl: DerivedAxiomInfo = derivedAxiom("<= refl", equivSequent("F_() <= F_()", "true"), propQE)

  @Axiom(name = "greaterEqualRefl", unifier = Unifier.Full, key = "0", recursor = "")
  lazy val greaterEqualRefl: DerivedAxiomInfo = derivedAxiom(">= refl", equivSequent("F_() >= F_()", "true"), propQE)

  // (anti) symmetry axioms
  @Axiom(name = "equalSym")
  lazy val equalSym: DerivedAxiomInfo =
    derivedAxiom("= sym", implySequent("F_() = G_()", "G_() = F_()", "true"), propQE)

  @Axiom(name = "notEqualSym")
  lazy val notEqualSym: DerivedAxiomInfo =
    derivedAxiom("!= sym", implySequent("F_() != G_()", "G_() != F_()", "true"), propQE)

  @Axiom(name = "greaterNotSym")
  lazy val greaterNotSym: DerivedAxiomInfo =
    derivedAxiom("> antisym", implySequent("F_() > G_()", "G_() > F_()", "false"), propQE)

  @Axiom(name = "lessNotSym")
  lazy val lessNotSym: DerivedAxiomInfo =
    derivedAxiom("< antisym", implySequent("F_() < G_()", "G_() < F_()", "false"), propQE)

  // totality axioms
  @Axiom(name = "lessEqualTotal")
  lazy val lessEqualTotal: DerivedAxiomInfo =
    derivedAxiom("<= total", "==> F_() <= G_() | G_() <= F_()".asSequent, propQE)

  @Axiom(name = "greaterEqualTotal")
  lazy val greaterEqualTotal: DerivedAxiomInfo =
    derivedAxiom(">= total", "==> F_() >= G_() | G_() >= F_()".asSequent, propQE)

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
  @Axiom(
    name = "allStutter",
    displayName = Some("all stutter"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "0",
  )
  lazy val allStutter: DerivedAxiomInfo = derivedAxiom(
    "all stutter",
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(||) <-> \\forall x_ p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  @Axiom(
    name = "allStutterPrime",
    displayName = Some("all stutter'"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "",
  )
  lazy val allStutterPrime: DerivedAxiomInfo = derivedAxiom(
    "all stutter prime",
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
  @Axiom(
    name = "existsStutter",
    displayName = Some("exists stutter"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "0",
  )
  lazy val existsStutter: DerivedAxiomInfo = derivedAxiom(
    "exists stutter",
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ p_(||) <-> \\exists x_ p_(||)".asFormula)),
    byUS(equivReflexive),
  )

  @Axiom(
    name = "existsStutterPrime",
    displayName = Some("exists stutter'"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "",
  )
  lazy val existsStutterPrime: DerivedAxiomInfo = derivedAxiom(
    "exists stutter prime",
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
  @Axiom(
    name = "andStutter",
    displayName = Some("and stutter"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "0;1",
  )
  lazy val andStutter: DerivedAxiomInfo = derivedAxiom(
    "and stutter",
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
  @Axiom(
    name = "orStutter",
    displayName = Some("or stutter"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "0;1",
  )
  lazy val orStutter: DerivedAxiomInfo = derivedAxiom(
    "or stutter",
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
  @Axiom(
    name = "implyStutter",
    displayName = Some("imply stutter"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "0;1",
  )
  lazy val implyStutter: DerivedAxiomInfo = derivedAxiom(
    "imply stutter",
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
  @Axiom(
    name = "equivStutter",
    displayName = Some("equiv stutter"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "0;1",
  )
  lazy val equivStutter: DerivedAxiomInfo = derivedAxiom(
    "equiv stutter",
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
  @Axiom(
    name = "notStutter",
    displayName = Some("not stutter"),
    displayLevel = DisplayLevel.Internal,
    key = "0",
    recursor = "0",
  )
  lazy val notStutter: DerivedAxiomInfo = derivedAxiom(
    "not stutter",
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
  @Axiom(
    name = "KDomD",
    displayConclusion = "[x'=f(x)&Q∧¬P]¬R → (__<x'=f(x)&Q>R → <x'=f(x)&Q>P__)",
    key = "1",
    recursor = "*",
  )
  lazy val KDomD: DerivedAxiomInfo = derivedAxiom(
    "K<&>",
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

  @Axiom(name = "eqNormalize", key = "0", recursor = "")
  lazy val eqNormalize: DerivedAxiomInfo =
    derivedFormula("eqNormalize", "s_() = t_() <-> s_() - t_() = 0".asFormula, QE)

  @Axiom(name = "neNormalize", key = "0", recursor = "")
  lazy val neNormalize: DerivedAxiomInfo =
    derivedFormula("neNormalize", "s_() != t_() <-> s_() - t_() != 0".asFormula, QE)

  @Axiom(name = "gtNormalize", key = "0", recursor = "")
  lazy val gtNormalize: DerivedAxiomInfo = derivedFormula("gtNormalize", "f_()>g_() <-> f_()-g_()>0".asFormula, QE)

  @Axiom(name = "geNormalize", key = "0", recursor = "")
  lazy val geNormalize: DerivedAxiomInfo = derivedFormula("geNormalize", "f_()>=g_() <-> f_()-g_()>=0".asFormula, QE)

  @Axiom(name = "divNeEq")
  lazy val divNeEq: DerivedAxiomInfo = derivedFormula("divNeEq", "G_()!=0 -> F_()/G_() = 0 -> F_() = 0".asFormula, QE)

  @Axiom(name = "divNeNe")
  lazy val divNeNe: DerivedAxiomInfo = derivedFormula("divNeNe", "G_()!=0 -> F_()/G_() != 0 -> F_() != 0".asFormula, QE)

  @Axiom(name = "divGtEq")
  lazy val divGtEq: DerivedAxiomInfo = derivedFormula("divGtEq", "G_()>0 -> F_()/G_() = 0 -> F_() = 0".asFormula, QE)

  @Axiom(name = "divLtEq")
  lazy val divLtEq: DerivedAxiomInfo = derivedFormula("divLtEq", "G_()<0 -> F_()/G_() = 0 -> F_() = 0".asFormula, QE)

  @Axiom(name = "divGtNe")
  lazy val divGtNe: DerivedAxiomInfo = derivedFormula("divGtNe", "G_()>0 -> F_()/G_() != 0 -> F_() != 0".asFormula, QE)

  @Axiom(name = "divLtNe")
  lazy val divLtNe: DerivedAxiomInfo = derivedFormula("divLtNe", "G_()<0 -> F_()/G_() != 0 -> F_() != 0".asFormula, QE)

  @Axiom(name = "divGtGt")
  lazy val divGtGt: DerivedAxiomInfo = derivedFormula("divGtGt", "G_()>0 -> F_()/G_() > 0 -> F_() > 0".asFormula, QE)

  @Axiom(name = "divLtGt")
  lazy val divLtGt: DerivedAxiomInfo = derivedFormula("divLtGt", "G_()<0 -> F_()/G_() > 0 -> F_() < 0".asFormula, QE)

  @Axiom(name = "divGtGe")
  lazy val divGtGe: DerivedAxiomInfo = derivedFormula("divGtGe", "G_()>0 -> F_()/G_() >= 0 -> F_() >= 0".asFormula, QE)

  @Axiom(name = "divLtGe")
  lazy val divLtGe: DerivedAxiomInfo = derivedFormula("divLtGe", "G_()<0 -> F_()/G_() >= 0 -> F_() <= 0".asFormula, QE)

  @Axiom(name = "divGtLt")
  lazy val divGtLt: DerivedAxiomInfo = derivedFormula("divGtLt", "G_()>0 -> F_()/G_() < 0 -> F_() < 0".asFormula, QE)

  @Axiom(name = "divLtLt")
  lazy val divLtLt: DerivedAxiomInfo = derivedFormula("divLtLt", "G_()<0 -> F_()/G_() < 0 -> F_() > 0".asFormula, QE)

  @Axiom(name = "divGtLe")
  lazy val divGtLe: DerivedAxiomInfo = derivedFormula("divGtLe", "G_()>0 -> F_()/G_() <= 0 -> F_() <= 0".asFormula, QE)

  @Axiom(name = "divLtLe")
  lazy val divLtLe: DerivedAxiomInfo = derivedFormula("divLtLe", "G_()<0 -> F_()/G_() <= 0 -> F_() >= 0".asFormula, QE)

  @Axiom(name = "coefficientTimesPrv")
  lazy val coefficientTimesPrv: DerivedAxiomInfo = derivedFormula(
    "coefficientTimesPrv",
    ("(l_() = ln_()/ld_() & r_() = rn_()/rd_() & ((ln_()*rn_() = pn_() & ld_()*rd_()=pd_() & ld_() != 0 & rd_() != 0)<-> true)) ->" +
      "l_()*r_() = pn_()/pd_()").asFormula,
    QE & done,
  )

  @Axiom(name = "coefficientPlusPrv")
  lazy val coefficientPlusPrv: DerivedAxiomInfo = derivedFormula(
    "coefficientPlusPrv",
    ("(l_() = ln_()/ld_() & r_() = rn_()/rd_() & ((ln_()*rd_() + rn_()*ld_() = pn_() & ld_()*rd_()=pd_() & ld_() != 0 & rd_() != 0)<-> true)) ->" +
      "l_()+r_() = pn_()/pd_()").asFormula,
    QE & done,
  )

  @Axiom(name = "coefficientNegPrv")
  lazy val coefficientNegPrv: DerivedAxiomInfo = derivedFormula(
    "coefficientNegPrv",
    ("(x_() = xn_()/xd_() & ((-xn_()=nxn_() & xd_() != 0)<-> true)) ->" +
      "-x_() = nxn_()/xd_()").asFormula,
    QE & done,
  )

  @Axiom(name = "coefficientBigDecimalPrv")
  lazy val coefficientBigDecimalPrv: DerivedAxiomInfo = derivedFormula(
    "coefficientBigDecimalPrv",
    ("(x_() = xn_()/xd_() & ((xn_()/xd_()=bd_() & xd_() != 0)<-> true)) ->" +
      "x_() = bd_()").asFormula,
    QE & done,
  )

  @Axiom(name = "plusTimes")
  lazy val plusTimes: DerivedAxiomInfo = derivedFormula(
    "plusTimes",
    "l_() = a_()*b_() & r_() = c_()*b_() & a_() + c_() = d_() -> l_() + r_() = d_()*b_()".asFormula,
    QE & done,
  )

  @Axiom(name = "negTimes")
  lazy val negTimes: DerivedAxiomInfo =
    derivedFormula("negTimes", "l_() = a_()*b_() & -a_() = c_() -> -l_() = c_()*b_()".asFormula, QE & done)

  @Axiom(name = "powerLemma")
  lazy val powerLemma: DerivedAxiomInfo = derivedFormula(
    "powerLemma",
    "(i_() >= 0 & j_() >= 0 & i_() + j_() = k_()) -> x_()^i_() * x_()^j_() = x_() ^ k_()".asFormula,
    prop & eqR2L(-3)(1) & cohideR(1) & QE & done,
  )

  @Axiom(name = "monomialTimesLemma")
  lazy val monomialTimesLemma: DerivedAxiomInfo = derivedFormula(
    "monomialTimesLemma",
    ("(l_() = cl_() * xls_() &" +
      " r_() = cr_() * xrs_() &" +
      " cl_() * cr_() = c_() &" +
      " xls_() * xrs_() = xs_()" +
      ") -> l_() * r_() = c_() * xs_()").asFormula,
    QE & done,
  )

  @Axiom(name = "timesPowersBoth")
  lazy val timesPowersBoth: DerivedAxiomInfo = derivedFormula(
    "timesPowersBoth",
    ("(((i_() >= 0 & j_() >= 0 & i_() + j_() = k_())<->true) & xs_() * ys_() = xys_())" +
      "->" +
      "(xs_() * x_()^i_()) * (ys_() * x_()^j_()) = xys_() * x_()^k_()").asFormula,
    prop & cutR("x_()^i_()*x_()^j_() = x_()^k_()".asFormula)(1) & Idioms.<(
      useAt(powerLemma, PosInExpr(1 :: Nil))(1) & prop & done,
      implyR(1) & eqR2L(-6)(1) & hideL(-6) & hideL(-3) & eqR2L(-1)(1) & cohideR(1) & QE & done,
    ),
  )

  @Axiom(name = "timesPowersLeft")
  lazy val timesPowersLeft: DerivedAxiomInfo = derivedFormula(
    "timesPowersLeft",
    "(xs_() * ys_() = xys_()) -> xs_() * x_() * (ys_()) = xys_() * x_()".asFormula,
    QE & done,
  )

  @Axiom(name = "timesPowersRight")
  lazy val timesPowersRight: DerivedAxiomInfo = derivedFormula(
    "timesPowersRight",
    "(xs_() * ys_() = xys_()) -> xs_() * (ys_()*y_()) = xys_() * y_()".asFormula,
    QE & done,
  )

  @Axiom(name = "timesPowers1Right")
  lazy val timesPowers1Right: DerivedAxiomInfo =
    derivedFormula("timesPowers1Right", "xs_() * 1 = xs_()".asFormula, QE & done)

  @Axiom(name = "timesPowers1Left")
  lazy val timesPowers1Left: DerivedAxiomInfo =
    derivedFormula("timesPowers1Left", "1 * ys_() = ys_()".asFormula, QE & done)

  @Axiom(name = "zez")
  lazy val zez: DerivedAxiomInfo = derivedFormula("zez", "0 = 0".asFormula, byUS(Ax.equalReflexive))

  @Axiom(name = "emptySprout")
  lazy val emptySprout: DerivedAxiomInfo =
    derivedFormula("emptySprout", "s_() = 0 & t_() = u_() -> s_() + t_() = 0 + u_() + 0".asFormula, QE & done)

  // @todo: should these be constructed more systematically?! e.g., define common subformulas only once. would make the code more robust...
  @Axiom(name = "branch2Left", displayName = Some("branch2Left "))
  lazy val branch2Left: DerivedAxiomInfo = derivedFormula(
    "branch2Left ",
    "t_() = l_() + v_() + r_() & l_() + x_() = lx_() -> t_() + x_() = lx_() + v_()  + r_() ".asFormula,
    QE & done,
  )

  @Axiom(name = "branch2Value")
  lazy val branch2Value: DerivedAxiomInfo = derivedFormula(
    "branch2Value",
    "t_() = l_() + v_() + r_() & v_() + x_() = vx_() -> t_() + x_() = l_()  + vx_() + r_() ".asFormula,
    QE & done,
  )

  @Axiom(name = "branch2Right")
  lazy val branch2Right: DerivedAxiomInfo = derivedFormula(
    "branch2Right",
    "t_() = l_() + v_() + r_() & r_() + x_() = rx_() -> t_() + x_() = l_()  + v_()  + rx_()".asFormula,
    QE & done,
  )

  /** @note for the Left case, could actually just use [[branch2Left]] */
  @Axiom(name = "branch2GrowLeft")
  lazy val branch2GrowLeft: DerivedAxiomInfo = derivedFormula(
    "branch2GrowLeft",
    "t_() = l_() + v_() + r_() & l_() + x_() = l1_() + lv_() + l2_() -> t_() + x_() = l1_() + lv_() + l2_() + v_() + r_()"
      .asFormula,
    QE & done,
  )

  @Axiom(name = "branch2GrowRight")
  lazy val branch2GrowRight: DerivedAxiomInfo = derivedFormula(
    "branch2GrowRight",
    "t_() = l_() + v_() + r_() & r_() + x_() = r1_() + rv_() + r2_() -> t_() + x_() = l_()                  + v_() + r1_() + rv_() + r2_()"
      .asFormula,
    QE & done,
  )

  @Axiom(name = "branch3Left")
  lazy val branch3Left: DerivedAxiomInfo = derivedFormula(
    "branch3Left",
    "t_() = l_() + v_() + m_() + w_() + r_() & l_() + x_() = lx_() -> t_() + x_() = lx_() + v_()  + m_()  + w_()  + r_() "
      .asFormula,
    QE & done,
  )

  @Axiom(name = "branch3Value1")
  lazy val branch3Value1: DerivedAxiomInfo = derivedFormula(
    "branch3Value1",
    "t_() = l_() + v_() + m_() + w_() + r_() & v_() + x_() = vx_() -> t_() + x_() = l_()  + vx_() + m_()  + w_()  + r_() "
      .asFormula,
    QE & done,
  )

  @Axiom(name = "branch3Mid")
  lazy val branch3Mid: DerivedAxiomInfo = derivedFormula(
    "branch3Mid",
    "t_() = l_() + v_() + m_() + w_() + r_() & m_() + x_() = mx_() -> t_() + x_() = l_()  + v_()  + mx_() + w_()  + r_() "
      .asFormula,
    QE & done,
  )

  @Axiom(name = "branch3Value2")
  lazy val branch3Value2: DerivedAxiomInfo = derivedFormula(
    "branch3Value2",
    "t_() = l_() + v_() + m_() + w_() + r_() & w_() + x_() = wx_() -> t_() + x_() = l_()  + v_()  + m_()  + wx_() + r_() "
      .asFormula,
    QE & done,
  )

  @Axiom(name = "branch3Right")
  lazy val branch3Right: DerivedAxiomInfo = derivedFormula(
    "branch3Right",
    "t_() = l_() + v_() + m_() + w_() + r_() & r_() + x_() = rx_() -> t_() + x_() = l_()  + v_()  + m_()  + w_()  + rx_()"
      .asFormula,
    QE & done,
  )

  @Axiom(name = "branch3GrowLeft")
  lazy val branch3GrowLeft: DerivedAxiomInfo = derivedFormula(
    "branch3GrowLeft",
    ("t_() = l_() + v_() + m_() + w_() + r_() & l_() + x_() = l1_() + lv_() + l2_() ->" +
      "t_() + x_() = (l1_() + lv_() + l2_()) + v_()  + (m_()  + w_()  + r_())").asFormula,
    QE & done,
  )

  @Axiom(name = "branch3GrowMid")
  lazy val branch3GrowMid: DerivedAxiomInfo = derivedFormula(
    "branch3GrowMid",
    ("t_() = l_() + v_() + m_() + w_() + r_() & m_() + x_() = m1_() + mv_() + m2_() ->" +
      "t_() + x_() = (l_() + v_() + m1_()) + mv_()  + (m2_()  + w_()  + r_())").asFormula,
    QE & done,
  )

  @Axiom(name = "branch3GrowRight")
  lazy val branch3GrowRight: DerivedAxiomInfo = derivedFormula(
    "branch3GrowRight",
    ("t_() = l_() + v_() + m_() + w_() + r_() & r_() + x_() = r1_() + rv_() + r2_() ->" +
      "t_() + x_() = (l_() + v_() + m_()) + w_()  + (r1_()  + rv_()  + r2_())").asFormula,
    QE & done,
  )

  // Lemmas for Add

  @Axiom(name = "plusEmpty")
  lazy val plusEmpty: DerivedAxiomInfo =
    derivedFormula("plusEmpty", "t_() = s_() & u_() = 0 -> t_() + u_() = s_()".asFormula, QE & done)

  @Axiom(name = "plusBranch2")
  lazy val plusBranch2: DerivedAxiomInfo = derivedFormula(
    "plusBranch2",
    ("(s_() = l_() + v_() + r_() & t_() + l_() + v_() + r_() = sum_()) ->" +
      "t_() + s_() = sum_()").asFormula,
    QE & done,
  )

  @Axiom(name = "plusBranch3")
  lazy val plusBranch3: DerivedAxiomInfo = derivedFormula(
    "plusBranch3",
    ("(s_() = l_() + v1_() + m_() + v2_() + r_() & t_() + l_() + v1_() + m_() + v2_() + r_() = sum_()) ->" +
      "t_() + s_() = sum_()").asFormula,
    QE & done,
  )

  // Lemmas for Minus

  @Axiom(name = "minusEmpty")
  lazy val minusEmpty: DerivedAxiomInfo =
    derivedFormula("minusEmpty", "t_() = s_() & u_() = 0 -> t_() - u_() = s_()".asFormula, QE & done)

  @Axiom(name = "minusBranch2")
  lazy val minusBranch2: DerivedAxiomInfo = derivedFormula(
    "minusBranch2",
    ("(s_() = l_() + v_() + r_() & t_() - l_() - v_() - r_() = sum_()) ->" +
      "t_() - s_() = sum_()").asFormula,
    QE & done,
  )

  @Axiom(name = "minusBranch3")
  lazy val minusBranch3: DerivedAxiomInfo = derivedFormula(
    "minusBranch3",
    ("(s_() = l_() + v1_() + m_() + v2_() + r_() & t_() - l_() - v1_() - m_() - v2_() - r_() = sum_()) ->" +
      "t_() - s_() = sum_()").asFormula,
    QE & done,
  )

  // Lemmas for Minus Monomial

  @Axiom(name = "plusMinus")
  lazy val plusMinus: DerivedAxiomInfo =
    derivedFormula("plusMinus", "t_() + (-x_()) = s_() -> t_() - x_() = s_()".asFormula, QE & done)

  // Lemmas for Times Monomial

  @Axiom(name = "monTimesZero")
  lazy val monTimesZero: DerivedAxiomInfo =
    derivedFormula("monTimesZero", "t_() = 0 -> t_() * x_() = 0".asFormula, QE & done)

  @Axiom(name = "monTimesBranch2")
  lazy val monTimesBranch2: DerivedAxiomInfo = derivedFormula(
    "monTimesBranch2",
    ("(t_() = l_() + v_() + r_() &" +
      "l_() * x_() = lx_() &" +
      "v_() * x_() = vx_() &" +
      "r_() * x_() = rx_()) -> t_() * x_() = lx_() + vx_() + rx_()").asFormula,
    QE & done,
  )

  @Axiom(name = "monTimesBranch3")
  lazy val monTimesBranch3: DerivedAxiomInfo = derivedFormula(
    "monTimesBranch3",
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() &" +
      "l_() * x_() = lx_() &" +
      "v1_() * x_() = v1x_() &" +
      "m_() * x_() = mx_() &" +
      "v2_() * x_() = v2x_() &" +
      "r_() * x_() = rx_()) -> t_() * x_() = lx_() + v1x_() + mx_() + v2x_() + rx_()").asFormula,
    QE & done,
  )

  // Lemmas for Times

  @Axiom(name = "timesEmpty")
  lazy val timesEmpty: DerivedAxiomInfo =
    derivedFormula("timesEmpty", "t_() = 0 -> t_() * u_() = 0".asFormula, QE & done)

  @Axiom(name = "timesBranch2")
  lazy val timesBranch2: DerivedAxiomInfo = derivedFormula(
    "timesBranch2",
    ("(t_() = l_() + v_() + r_() & l_()*u_() + u_() * v_() + r_()*u_() = sum_()) ->" +
      "t_() * u_() = sum_()").asFormula,
    QE & done,
  )

  @Axiom(name = "timesBranch3")
  lazy val timesBranch3: DerivedAxiomInfo = derivedFormula(
    "timesBranch3",
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() & l_()*u_() + u_()*v1_() + m_()*u_() + u_()*v2_() + r_()*u_() = sum_()) ->" +
      "t_() * u_() = sum_()").asFormula,
    QE & done,
  )

  // Lemmas for Power

  @Axiom(name = "powerZero")
  lazy val powerZero: DerivedAxiomInfo =
    derivedFormula("powerZero", "1 = one_() -> t_() ^ 0 = one_()".asFormula, QE & done)

  @Axiom(name = "powerOne")
  lazy val powerOne: DerivedAxiomInfo =
    derivedFormula("powerOne", "t_() = s_() -> t_() ^ 1 = s_()".asFormula, QE & done)

  @Axiom(name = "powerEven")
  lazy val powerEven: DerivedAxiomInfo = derivedFormula(
    "powerEven",
    ("((n_() = 2*m_() <-> true) & t_()^m_() = p_() & p_()*p_() = r_()) ->" +
      "t_() ^ n_() = r_()").asFormula,
    implyR(1) & andL(-1) & andL(-2) &
      useAt(Ax.equivTrue, PosInExpr(0 :: Nil))(-1) &
      eqL2R(-1)(1) & hideL(-1) &
      cutR("t_() ^ (2*m_()) = (t_()^m_())^2".asFormula)(1) & Idioms
        .<(QE & done, implyR(1) & eqL2R(-3)(1) & hideL(-3) & eqL2R(-1)(1) & hideL(-1) & QE & done),
  )

  @Axiom(name = "powerOdd")
  lazy val powerOdd: DerivedAxiomInfo = derivedFormula(
    "powerOdd",
    ("((n_() = 2*m_() + 1 <-> true) & t_()^m_() = p_() & p_()*p_()*t_() = r_()) ->" +
      "t_() ^ n_() = r_()").asFormula,
    implyR(1) & andL(-1) & andL(-2) &
      useAt(Ax.equivTrue, PosInExpr(0 :: Nil))(-1) &
      eqL2R(-1)(1) & hideL(-1) &
      cutR("t_() ^ (2*m_() + 1) = (t_()^m_())^2*t_()".asFormula)(1) & Idioms
        .<(QE & done, implyR(1) & eqL2R(-3)(1) & hideL(-3) & eqL2R(-1)(1) & hideL(-1) & QE & done),
  )

  @Axiom(name = "powerPoly")
  lazy val powerPoly: DerivedAxiomInfo = derivedFormula(
    "powerPoly",
    "(q_() = i_() & p_()^i_() = r_()) -> p_()^q_() = r_()".asFormula,
    implyR(1) & andL(-1) &
      eqL2R(-1)(1, 0 :: 1 :: Nil) &
      hideL(-1) &
      id,
  )

  // Lemmas for division

  @Axiom(name = "divideNumber")
  lazy val divideNumber: DerivedAxiomInfo =
    derivedFormula("divideNumber", "(q_() = i_() & p_()*(1/i_()) = r_()) -> p_()/q_() = r_()".asFormula, QE & done)

  @Axiom(name = "divideRat")
  lazy val divideRat: DerivedAxiomInfo =
    derivedFormula("divideRat", "(q_() = n_()/d_() & p_()*(d_()/n_()) = r_()) -> p_()/q_() = r_()".asFormula, QE & done)

  @Axiom(name = "divideNeg")
  lazy val divideNeg: DerivedAxiomInfo =
    derivedFormula("divideNeg", "-(p_()/(-q_())) = r_() -> p_()/q_() = r_()".asFormula, QE & done)

  // Lemmas for negation

  @Axiom(name = "negateEmpty")
  lazy val negateEmpty: DerivedAxiomInfo = derivedFormula("negateEmpty", "t_() = 0 -> -t_() = 0".asFormula, QE & done)

  @Axiom(name = "negateBranch2")
  lazy val negateBranch2: DerivedAxiomInfo = derivedFormula(
    "negateBranch2",
    ("(t_() = l_() + v_() + r_() & -l_() = nl_() & -v_() = nv_() & -r_() = nr_()) ->" +
      "-t_() = nl_() + nv_() + nr_()").asFormula,
    QE & done,
  )

  @Axiom(name = "negateBranch3")
  lazy val negateBranch3: DerivedAxiomInfo = derivedFormula(
    "negateBranch3",
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() & -l_() = nl_() & -v1_() = nv1_() & -m_() = nm_() & -v2_() = nv2_() & -r_() = nr_()) ->" +
      "-t_() = nl_() + nv1_() + nm_() + nv2_() + nr_()").asFormula,
    QE & done,
  )

  // Lemmas for normalization

  @Axiom(name = "normalizeCoeff0")
  lazy val normalizeCoeff0: DerivedAxiomInfo =
    derivedFormula("normalizeCoeff0", "(c_() = 0 / d_() ) -> c_() = 0".asFormula, QE & done)

  @Axiom(name = "normalizeCoeff1")
  lazy val normalizeCoeff1: DerivedAxiomInfo =
    derivedFormula("normalizeCoeff1", "(c_() = n_() / 1 ) -> c_() = n_()".asFormula, QE & done)

  @Axiom(name = "normalizeMonom0")
  lazy val normalizeMonom0: DerivedAxiomInfo =
    derivedFormula("normalizeMonom0", "(x_() = c_() * ps_() & c_() = 0) -> x_() = 0".asFormula, QE & done)

  @Axiom(name = "normalizeMonomCS")
  lazy val normalizeMonomCS: DerivedAxiomInfo = derivedFormula(
    "normalizeMonomCS",
    ("(x_() = c_() * ps_() & c_() * ps_() = cps_()) ->" +
      "x_() = cps_()").asFormula,
    QE & done,
  )

  @Axiom(name = "normalizeMonomNCS")
  lazy val normalizeMonomNCS: DerivedAxiomInfo = derivedFormula(
    "normalizeMonomNCS",
    ("(x_() = c_() * ps_() & -c_() = m_() & m_() * ps_() = cps_()) ->" +
      "x_() = -cps_()").asFormula,
    QE & done,
  )

  @Axiom(name = "normalizePowers1V")
  lazy val normalizePowers1V: DerivedAxiomInfo =
    derivedFormula("normalizePowers1V", "(c_() = 1) -> c_() * (1 * v_()^1) = v_()".asFormula, QE & done)

  @Axiom(name = "normalizePowers1R")
  lazy val normalizePowers1R: DerivedAxiomInfo =
    derivedFormula("normalizePowers1R", "(c_() = 1) -> c_() * (1 * t_()) = t_()".asFormula, QE & done)

  @Axiom(name = "normalizePowersC1")
  lazy val normalizePowersC1: DerivedAxiomInfo =
    derivedFormula("normalizePowersC1", "(c_() = d_()) -> c_() * 1 = d_()".asFormula, QE & done)

  @Axiom(name = "normalizePowersCV")
  lazy val normalizePowersCV: DerivedAxiomInfo =
    derivedFormula("normalizePowersCV", "(c_() = d_()) -> c_() * (1 * v_()^1) = d_()*v_()".asFormula, QE & done)

  @Axiom(name = "normalizePowersCP")
  lazy val normalizePowersCP: DerivedAxiomInfo =
    derivedFormula("normalizePowersCP", "(c_() = d_()) -> c_() * (1 * t_()) = d_()*t_()".asFormula, QE & done)

  @Axiom(name = "normalizePowersRV")
  lazy val normalizePowersRV: DerivedAxiomInfo = derivedFormula(
    "normalizePowersRV",
    "(c_() * ps_() = cps_()) -> c_() * (ps_() * v_()^1) = cps_() * v_()".asFormula,
    QE & done,
  )

  @Axiom(name = "normalizePowersRP")
  lazy val normalizePowersRP: DerivedAxiomInfo = derivedFormula(
    "normalizePowersRP",
    "(c_() * ps_() = cps_()) -> c_() * (ps_() * t_()) = cps_() * t_()".asFormula,
    QE & done,
  )

  @Axiom(name = "normalizeBranch2")
  lazy val normalizeBranch2: DerivedAxiomInfo = derivedFormula(
    "normalizeBranch2",
    ("(t_() = l_() + v_() + r_() & l_() = ln_() & v_() = vn_() & r_() = rn_()) ->" +
      "t_() = ln_() + vn_() + rn_()").asFormula,
    QE & done,
  )

  @Axiom(name = "normalizeBranch3")
  lazy val normalizeBranch3: DerivedAxiomInfo = derivedFormula(
    "normalizeBranch3",
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() & l_() = ln_() & v1_() = v1n_() & m_() = mn_() & v2_() = v2n_() & r_() = rn_()) ->" +
      "t_() = ln_() + v1n_() + mn_() + v2n_() + rn_()").asFormula,
    QE & done,
  )

  @Axiom(name = "reassocRight0")
  lazy val reassocRight0: DerivedAxiomInfo = derivedFormula(
    "reassocRight0",
    ("(" +
      "t_() = l_() + r_() &" +
      "r_() = 0   &" +
      "l_() = ll_()" +
      ") ->" +
      "t_() = ll_()").asFormula,
    QE & done,
  )

  @Axiom(name = "reassocRightPlus")
  lazy val reassocRightPlus: DerivedAxiomInfo = derivedFormula(
    "reassocRightPlus",
    ("(" +
      "t_() = l_() + r_() &" +
      "r_() = rs_() + rr_() &" +
      "l_() + rs_() = lrs_()" +
      ") ->" +
      "t_() = lrs_() + rr_()").asFormula,
    QE & done,
  )

  @Axiom(name = "reassocLeft0RightConst")
  lazy val reassocLeft0RightConst: DerivedAxiomInfo = derivedFormula(
    "reassocLeft0RightConst",
    ("(" +
      "t_() = l_() + r_() &" +
      "r_() = c_() &" +
      "l_() = 0" +
      ") ->" +
      "t_() = c_()").asFormula,
    QE & done,
  )

  @Axiom(name = "reassocRightConst")
  lazy val reassocRightConst: DerivedAxiomInfo = derivedFormula(
    "reassocRightConst",
    ("(" +
      "t_() = l_() + r_() &" +
      "r_() = c_() &" +
      "l_() = ll_()" +
      ") ->" +
      "t_() = ll_() + c_()").asFormula,
    QE & done,
  )

  // lemmas to prove equality

  @Axiom(name = "equalityBySubtraction")
  lazy val equalityBySubtraction: DerivedAxiomInfo =
    derivedFormula("equalityBySubtraction", "t_() - s_() = 0 -> t_() = s_()".asFormula, QE & done)

  // Lemmas for partition
  @Axiom(name = "partition2")
  lazy val partition2: DerivedAxiomInfo = derivedFormula(
    "partition2",
    "(t_() = r_() & t1_() = r1_() & t2_() = r2_() & t_() - t1_() - t2_() = 0) -> t_() = t1_() + t2_()".asFormula,
    QE & done,
  )

  // Lemmas for splitting coefficients

  @inline
  private def nz(t: Term): Formula = NotEqual(t, Number(0))

  @inline
  def splitCoefficientNumericCondition(n: Term, d: Term, n1: Term, d1: Term, n2: Term, d2: Term): Formula =
    And(Equal(Times(Times(n, d1), d2), Times(d, Plus(Times(d1, n2), Times(d2, n1)))), And(nz(d), And(nz(d1), nz(d2))))

  @Axiom(name = "splitCoefficient")
  lazy val splitCoefficient: DerivedAxiomInfo = derivedFormula(
    "splitCoefficient",
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

  @Axiom(name = "splitMonomial")
  lazy val splitMonomial: DerivedAxiomInfo = derivedFormula(
    "splitMonomial",
    "(c_() = c1_() + c2_() & m_() = c_() * x_()) -> m_() = c1_() * x_() + c2_() * x_()".asFormula,
    QE & done,
  )

  @Axiom(name = "splitEmpty", displayName = Some("splitEmpty "))
  lazy val splitEmpty: DerivedAxiomInfo = derivedFormula("splitEmpty ", "t_() = 0 -> t_() = 0 + 0".asFormula, QE & done)

  @Axiom(name = "splitBranch2", displayName = Some("splitBranch2 "))
  lazy val splitBranch2: DerivedAxiomInfo = derivedFormula(
    "splitBranch2 ",
    ("(t_() = l_() + v_() + r_() & l_() = l1_() + l2_() & v_() = v1_() + v2_() & r_() = r1_() + r2_())" +
      "->" +
      "t_() = (l1_() + v1_() + r1_()) + (l2_() + v2_() + r2_())").asFormula,
    QE & done,
  )

  @Axiom(name = "splitBranch3", displayName = Some("splitBranch3 "))
  lazy val splitBranch3: DerivedAxiomInfo = derivedFormula(
    "splitBranch3 ",
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() & l_() = l1_() + l2_() & v1_() = v11_() + v12_() & m_() = m1_() + m2_() & v2_() = v21_() + v22_() & r_() = r1_() + r2_())" +
      "->" +
      "t_() = (l1_() + v11_() + m1_() + v21_() + r1_()) + (l2_() + v12_() + m2_() + v22_() + r2_())").asFormula,
    QE & done,
  )

  @Axiom(name = "varPowerLemma")
  lazy val varPowerLemma: DerivedAxiomInfo =
    derivedFormula("varPowerLemma", "v_()^n_() = 0 + 1 / 1 * (1 * v_()^n_()) + 0".asFormula, QE & done)

  @Axiom(name = "varLemma")
  lazy val varLemma: DerivedAxiomInfo =
    derivedFormula("varLemma", "v_() = 0 + 1 / 1 * (1 * v_()^1) + 0".asFormula, QE & done)

  @Axiom(name = "constLemma")
  lazy val constLemma: DerivedAxiomInfo = derivedFormula(
    "constLemma",
    Equal(
      "n_()".asTerm,
      Seq(Number(0), Times(Divide("n_()".asTerm, Number(1)), Number(1)), Number(0)).reduceLeft(Plus),
    ),
    QE & done,
  )

  @Axiom(name = "rationalLemma")
  lazy val rationalLemma: DerivedAxiomInfo = derivedFormula(
    "rationalLemma",
    Equal("n_() / d_()".asTerm, Seq(Number(0), Times("n_()/d_()".asTerm, Number(1)), Number(0)).reduceLeft(Plus)),
    QE & done,
  )

  // Power of Divide

  @Axiom(name = "powerDivide0")
  lazy val powerDivide0: DerivedAxiomInfo =
    derivedFormula("powerDivide0", "(x_()/y_()) ^ 0 = x_()^0 / y_()^0".asFormula, QE & done)

  @Axiom(name = "powerDivideEven")
  lazy val powerDivideEven: DerivedAxiomInfo = derivedFormula(
    "powerDivideEven",
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

  @Axiom(name = "powerDivideOdd")
  lazy val powerDivideOdd: DerivedAxiomInfo = derivedFormula(
    "powerDivideOdd",
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

  @Axiom(name = "ratFormAdd")
  lazy val ratFormAdd: DerivedAxiomInfo = derivedFormula(
    "ratFormAdd",
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

  @Axiom(name = "ratFormMinus")
  lazy val ratFormMinus: DerivedAxiomInfo = derivedFormula(
    "ratFormMinus",
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

  @Axiom(name = "ratFormDivide")
  lazy val ratFormDivide: DerivedAxiomInfo = derivedFormula(
    "ratFormDivide",
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

  @Axiom(name = "ratFormTimes")
  lazy val ratFormTimes: DerivedAxiomInfo = derivedFormula(
    "ratFormTimes",
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

  @Axiom(name = "ratFormPower")
  lazy val ratFormPower: DerivedAxiomInfo = derivedFormula(
    "ratFormPower",
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

  @Axiom(name = "ratFormNeg")
  lazy val ratFormNeg: DerivedAxiomInfo = derivedFormula(
    "ratFormNeg",
    ("(x_() = nx_() / dx_() &" +
      "-nx_() = nz_())" +
      "->" +
      "-x_() = nz_() / dx_()").asFormula,
    implyR(1) & andL(Symbol("Llast")) * 1 &
      (eqL2R(-1)(1) & hideL(-1)) * 1 &
      (eqR2L(-1)(1) & hideL(-1)) * 1 &
      QE & done,
  )

  @Axiom(name = "divideIdentity")
  lazy val divideIdentity: DerivedAxiomInfo =
    derivedFormula("divideIdentity", "(x_() = y_() & 1 = z_()) -> x_() = y_() / z_()".asFormula, QE & done)

  // Taylor Model Arithmetic [[org.keymaerax.btactics.TaylorModelArith]]

  @Axiom(name = "taylorModelPlusPrv")
  lazy val taylorModelPlusPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelPlusPrv",
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() + poly2_() = poly_() &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ + i2_ & i1_ + i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() + elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelMinusPrv")
  lazy val taylorModelMinusPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelMinusPrv",
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() - poly2_() = poly_() &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ - i2_ & i1_ - i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() - elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelCollectPrv")
  lazy val taylorModelCollectPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelCollectPrv",
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

  @Axiom(name = "taylorModelPartitionPrv1")
  lazy val taylorModelPartitionPrv1: DerivedAxiomInfo = derivedFormula(
    "taylorModelPartitionPrv1",
    ("((\\exists err_ (elem_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "poly_() = polyTrue_() + polyFalse_() & " +
      "newElem_() = elem_() - polyTrue_() & " +
      "newElem_() + polyTrue_() = poly1_() & " +
      "polyFalse_() = poly2_()" +
      ") ->" +
      "\\exists err_ (elem_() = poly1_() + err_ & 0 <= err_ & err_ <= 0)").asFormula,
    QE & done,
  )
  @Axiom(name = "taylorModelPartitionPrv2")
  lazy val taylorModelPartitionPrv2: DerivedAxiomInfo = derivedFormula(
    "taylorModelPartitionPrv2",
    ("((\\exists err_ (elem_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "poly_() = polyTrue_() + polyFalse_() & " +
      "newElem_() = elem_() - polyTrue_() & " +
      "newElem_() + polyTrue_() = poly1_() & " +
      "polyFalse_() = poly2_()" +
      ") ->" +
      "\\exists err_ (newElem_() = poly2_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelTransElem")
  lazy val taylorModelTransElem: DerivedAxiomInfo = derivedFormula(
    "taylorModelTransElem",
    ("((\\exists err_ (elem_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "elem1_() = elem_()) ->" +
      "\\exists err_ (elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelIntervalPrv")
  lazy val taylorModelIntervalPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelIntervalPrv",
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "poly1_() = rem_() &" +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= rem_() + i1_ & rem_() + i1_  <= u_())))" +
      ") ->" +
      "l_() <= elem1_() & elem1_() <= u_()").asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelEmptyIntervalPrv")
  lazy val taylorModelEmptyIntervalPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelEmptyIntervalPrv",
    "(\\exists err_ (elem1_() = poly1_() + err_ & 0 <= err_ & err_ <= 0)) -> elem1_() = poly1_()".asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelTimesPrv")
  lazy val taylorModelTimesPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelTimesPrv",
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

  @Axiom(name = "taylorModelDivideExactPrv")
  lazy val taylorModelDivideExactPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelDivideExactPrv",
    ("((\\exists err_ (elem1_() * inv_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "elem1_()/elem2_() = elem1_() * inv_()" +
      ") ->" +
      "\\exists err_ (elem1_() / elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & eqL2R(-2)(1) & id,
  )

  @Axiom(name = "taylorModelSquarePrv")
  lazy val taylorModelSquarePrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelSquarePrv", // @todo: is there a better scheme than just multiplication?
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

  @Axiom(name = "taylorModelPowerOne")
  lazy val taylorModelPowerOne: DerivedAxiomInfo = derivedFormula(
    "taylorModelPowerOne",
    ("(\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_()))" +
      " ->" +
      "\\exists err_ (elem1_()^1 = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())").asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelPowerEven")
  lazy val taylorModelPowerEven: DerivedAxiomInfo = derivedFormula(
    "taylorModelPowerEven",
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

  @Axiom(name = "taylorModelPowerOdd")
  lazy val taylorModelPowerOdd: DerivedAxiomInfo = derivedFormula(
    "taylorModelPowerOdd",
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

  @Axiom(name = "taylorModelNegPrv")
  lazy val taylorModelNegPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelNegPrv",
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "-poly1_() = poly_() &" +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= -i1_ & -i1_ <= u_())))" +
      ") ->" +
      "\\exists err_ (-elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelExactPrv")
  lazy val taylorModelExactPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelExactPrv",
    ("elem_() = poly_() ->" +
      "\\exists err_ (elem_() = poly_() + err_ & 0 <= err_ & err_ <= 0)").asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelApproxPrv")
  lazy val taylorModelApproxPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelApproxPrv",
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

  @Axiom(name = "taylorModelEvalPrv")
  lazy val taylorModelEvalPrv: DerivedAxiomInfo = derivedFormula(
    "taylorModelEvalPrv",
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

  @Axiom(name = "refineTmExists")
  lazy val refineTmExists: DerivedAxiomInfo = derivedFormula(
    "refineTmExists",
    "(\\forall err_ (P(err_) -> Q(err_))) -> ((\\exists x_ P(x_)) -> (\\exists err_ Q(err_)))".asFormula,
    implyR(1) & implyR(1) & existsL(-2) & existsR("x_".asVariable)(1) & allL("x_".asVariable)(-1) & prop & done,
  )

  @Axiom(name = "taylorModelIntervalLe")
  lazy val taylorModelIntervalLe: DerivedAxiomInfo = derivedFormula(
    "taylorModelIntervalLe",
    "((l_() <= f_() - g_() & f_() - g_() <= u_()) & (u_() <= 0 <-> true)) -> f_() <= g_()".asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelIntervalLt")
  lazy val taylorModelIntervalLt: DerivedAxiomInfo = derivedFormula(
    "taylorModelIntervalLt",
    "((l_() <= f_() - g_() & f_() - g_() <= u_()) & (u_() < 0 <-> true)) -> f_() < g_()".asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelIntervalGe")
  lazy val taylorModelIntervalGe: DerivedAxiomInfo = derivedFormula(
    "taylorModelIntervalGe",
    "((l_() <= f_() - g_() & f_() - g_() <= u_()) & (l_() >= 0 <-> true)) -> f_() >= g_()".asFormula,
    QE & done,
  )

  @Axiom(name = "taylorModelIntervalGt")
  lazy val taylorModelIntervalGt: DerivedAxiomInfo = derivedFormula(
    "taylorModelIntervalGt",
    "((l_() <= f_() - g_() & f_() - g_() <= u_()) & (l_() > 0 <-> true)) -> f_() > g_()".asFormula,
    QE & done,
  )

  // Taylor Model [[org.keymaerax.btactics.TaylorModelTactics]]

  @Axiom(name = "unfoldExistsLemma")
  lazy val unfoldExistsLemma: DerivedAxiomInfo = derivedFormula(
    "unfoldExistsLemma",
    "\\exists x_ (r_() = s_() + x_ & P_(x_)) <-> P_(r_()-s_())".asFormula,
    prop & Idioms.<(
      existsL(-1) & andL(-1) & cutR("r_() - s_() = x_".asFormula)(1) & Idioms
        .<(QE & done, implyR(1) & eqL2R(-3)(1) & id),
      existsR("r_() - s_()".asTerm)(1) & prop & QE & done,
    ),
  )

  @Axiom(name = "foldAndLessEqExistsLemma")
  lazy val foldAndLessEqExistsLemma: DerivedAxiomInfo = derivedFormula(
    "foldAndLessEqExistsLemma",
    ("(a() <= x_ - b() & x_ - b() <= c()) <->" +
      "(\\exists xr_ (x_ = xr_ + b() & (a() <= xr_ & xr_ <= c())))").asFormula,
    QE & done,
  )

  @Axiom(name = "leTimesMonoLemma")
  lazy val leTimesMonoLemma: DerivedAxiomInfo = derivedFormula(
    "leTimesMonoLemma",
    "0 <= t_() & t_() <= h_() -> R_() <= t_() * U_() + cU_() -> R_() <= max((0,h_() * U_())) + cU_()".asFormula,
    QE & done,
  )

  @Axiom(name = "timesLeMonoLemma")
  lazy val timesLeMonoLemma: DerivedAxiomInfo = derivedFormula(
    "timesLeMonoLemma",
    "0 <= t_() & t_() <= h_() -> t_() * L_() + cL_() <= U_() -> min((0,h_() * L_())) + cL_() <= U_()".asFormula,
    QE & done,
  )

  @Axiom(name = "minGtNorm")
  lazy val minGtNorm: DerivedAxiomInfo =
    derivedFormula("minGtNorm", "min((f_(),g_()))>h_()<->(f_()>h_()&g_()>h_())".asFormula, QE & done)

  @Axiom(name = "minLeNorm")
  lazy val minLeNorm: DerivedAxiomInfo =
    derivedFormula("minLeNorm", "min((f_(),g_()))<=h_()<->(f_()<=h_()|g_()<=h_())".asFormula, QE & done)

  @Axiom(name = "minGeNorm")
  lazy val minGeNorm: DerivedAxiomInfo =
    derivedFormula("minGeNorm", "min((f_(),g_()))>=h_()<->(f_()>=h_()&g_()>=h_())".asFormula, QE & done)

  @Axiom(name = "leMaxNorm")
  lazy val leMaxNorm: DerivedAxiomInfo =
    derivedFormula("leMaxNorm", "h_()<=max((f_(),g_()))<->(h_()<=f_()|h_()<=g_())".asFormula, QE & done)

  @Axiom(name = "trivialInequality")
  lazy val trivialInequality: DerivedAxiomInfo =
    derivedFormula("trivialInequality", "(x_() = 0 & y_() = 0) -> x_() <= y_()".asFormula, QE & done)

  @Axiom(name = "refineConjunction")
  lazy val refineConjunction: DerivedAxiomInfo = derivedFormula(
    "refineConjunction",
    "((f_() -> h_()) & (g_() -> i_())) -> ((f_() & g_()) -> (h_() & i_()))".asFormula,
    prop & done,
  )

  @Axiom(name = "refineLe1")
  lazy val refineLe1: DerivedAxiomInfo =
    derivedFormula("refineLe1", "g()<=h()->(f()<=g()->f()<=h())".asFormula, QE & done)

  @Axiom(name = "refineLe2")
  lazy val refineLe2: DerivedAxiomInfo =
    derivedFormula("refineLe2", "h()<=f()->(f()<=g()->h()<=g())".asFormula, QE & done)

  @Axiom(name = "trivialRefineLtGt")
  lazy val trivialRefineLtGt: DerivedAxiomInfo = derivedFormula(
    "trivialRefineLtGt",
    "(w_() - v_() + y_() - x_() = 0) -> (v_() < w_() -> x_() > y_())".asFormula,
    QE & done,
  )

  @Axiom(name = "trivialRefineGeLe")
  lazy val trivialRefineGeLe: DerivedAxiomInfo = derivedFormula(
    "trivialRefineGeLe",
    "(v_() - w_() - y_() + x_() = 0) -> (v_() >= w_() -> x_() <= y_())".asFormula,
    QE & done,
  )

  @Axiom(name = "eqAddIff")
  lazy val eqAddIff: DerivedAxiomInfo =
    derivedFormula("eqAddIff", "f_() = g_() + h_() <-> h_() = f_() - g_()".asFormula, QE & done)

  @Axiom(name = "plusDiffRefl")
  lazy val plusDiffRefl: DerivedAxiomInfo =
    derivedFormula("plusDiffRefl", "f_() = g_() + (f_() - g_())".asFormula, QE & done)

  // ODELiveness

  @Axiom(name = "TExge")
  lazy val TExge: DerivedAxiomInfo =
    derivedFormula("TExge", "<{gextimevar_'=1}> (gextimevar_ >= p())".asFormula, solve(1) & QE & done)

  @Axiom(name = "TExgt")
  lazy val TExgt: DerivedAxiomInfo =
    derivedFormula("TExgt", "<{gextimevar_'=1}> (gextimevar_ > p())".asFormula, solve(1) & QE & done)

  @Axiom(name = "commaCommuteD", displayName = Some(", commute diamond"))
  lazy val commaCommuteD: DerivedAxiomInfo = derivedFormula(
    "commaCommuteD",
    "<{c,d&q(||)}>p(||) <-> <{d,c&q(||)}>p(||)".asFormula,
    prop < (
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(-1) & useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) &
        notL(-1) & notR(1) & useAt(Ax.commaCommute)(1) & close,
      useAt(Ax.diamond, PosInExpr(1 :: Nil))(-1) & useAt(Ax.diamond, PosInExpr(1 :: Nil))(1) &
        notL(-1) & notR(1) & useAt(Ax.commaCommute)(1) & close
    ),
  )

  /* ODEInvariance */

  @Axiom(
    name = "dBarcan",
    displayName = Some("D Barcan"),
    displayLevel = DisplayLevel.All,
    displayConclusion = "∃x<a>p(x)__ ↔ <a>∃x p(x) (x∉a)",
    key = "0",
    recursor = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  lazy val dBarcan: DerivedAxiomInfo = derivedAxiom(
    "D Barcan",
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
