/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

import org.keymaerax.btactics.macros.AnnotationCommon.ExprPos

import java.util.Locale
import scala.collection.immutable.{List, Nil}
import scala.language.implicitConversions
import scala.reflect.runtime.universe.TypeTag

////////////////////////////////////////////////////////////
// Type structure for central registry of derivation steps
////////////////////////////////////////////////////////////

/** Indicates that the (derived) axiom/rule/tactic of the given name could not be found. */
case class AxiomNotFoundException(axiomName: String)
    extends Exception("(Derived) Axiom or rule or tactic not found: " + axiomName)

// TODO Convert into enum after updating to Scala 3
sealed trait Unifier

/** General unification. */
case object UnifierFull extends Unifier

/**
 * No symbol can occur twice in the shape. If a symbol does occur twice, it is assumed that the identical match is found
 * in all use cases, which is a strong assumption and can lead to unpredictable behavior otherwise.
 */
case object UnifierLinear extends Unifier

/**
 * A formula is surjective iff rule US can instantiate it to any of its axiom schema instances, so those obtained by
 * uniformly replacing program constant symbols by hybrid games and unit predicationals by formulas. If no arguments
 * occur, so no function or predicate symbols or predicationals, then the axiom is surjective. UnitFunctional,
 * UnitPredicational, ProgramConst etc. can still occur. Function or predicate symbols that occur in a context without
 * any bound variables are exempt. For example [[Ax.testb]].
 */
case object UnifierSurjective extends Unifier

/** Both [[UnifierSurjective]] and [[UnifierLinear]]. */
case object UnifierSurjectiveLinear extends Unifier

/** An axiom that pretends to be surjective and linear even if it isn't necessarily so. */
case object UnifierSurjectiveLinearPretend extends Unifier

/**
 * Central meta-information on a derivation step, which is an axiom, derived axiom, proof rule, or tactic. Provides
 * information such as unique canonical names, internal code names, display information, etc.
 *
 * Each DerivationInfo is either
 *   - [[AxiomInfo]] consisting of builtin [[CoreAxiomInfo]] and derived axioms [[DerivedAxiomInfo]].
 *   - [[AxiomaticRuleInfo]] for builtin axiomatic proof rules.
 *   - [[DerivedRuleInfo]] for derived axiomatic proof rules.
 *   - [[TacticInfo]] for tactics and its various subtypes.
 *
 * Everything consisting of a proved axiom is an [[AxiomInfo]] namely [[CoreAxiomInfo]] and [[DerivedAxiomInfo]].
 * Everything consisting of a Provable is a [[ProvableInfo]], namely [[AxiomInfo]] and [[AxiomaticRuleInfo]] and
 * [[DerivedRuleInfo]].
 *
 * @see
 *   [[CoreAxiomInfo]]
 * @see
 *   [[DerivedAxiomInfo]]
 * @see
 *   [[AxiomaticRuleInfo]]
 * @see
 *   [[DerivedRuleInfo]]
 * @see
 *   [[TacticInfo]]
 */
object DerivationInfo {

  /**
   * Status of DerivationInfo initialization process. This is used to control error reporting: New @Tactic's should only
   * be found during initialization.
   */
  sealed trait InitStatus
  case object InitNotStarted extends InitStatus
  case object InitInProgress extends InitStatus
  case object InitComplete extends InitStatus
  var _initStatus: InitStatus = InitNotStarted

  /** Global map of all DerivationInfos indexed by codeName. Most readers should use the allInfo accessor. */
  var _allInfo: Map[String, DerivationInfo] = Map()
  /* All infos indexed by canonical name */
  var _byCanonicalName: Map[String, DerivationInfo] = Map()
  /* Storable infos by stored name */
  var _byStoredName: Map[String, StorableInfo] = Map()
  /* Infos for specific subclasses. These are all submaps of_allInfo and exist solely for faster access. */
  var _axiomInfo: Map[String, AxiomInfo] = Map()
  var _coreAxiomInfo: Map[String, CoreAxiomInfo] = Map()
  var _derivedAxiomInfo: Map[String, DerivedAxiomInfo] = Map()
  var _derivedRuleInfo: Map[String, DerivedRuleInfo] = Map()
  var _provableInfo: Map[String, ProvableInfo] = Map()

  /** Global list of BelleExpr names seen in any tactic expression constructor. Used to improve error-checking. */
  var _seenNames: Set[String] = Set()
  def seeName(name: String): Unit = _seenNames = _seenNames.+(name)

  /** Access allInfo with proper error-checking */
  def allInfo: Map[String, DerivationInfo] = _initStatus match {
    case InitNotStarted =>
      throw new Exception("Need to initialize DerivationInfo.allInfo by calling DerivationInfoRegistry.init ")
    case _ => _allInfo
  }

  /** Report error if new @Tactics are registered outside of global initialization routine. */
  private def requireInitInProgress(di: DerivationInfo): Unit = {
    _initStatus match {
      case InitInProgress => ()
      case InitNotStarted => throw new Exception(
          s"Tried to register ${di.codeName}, but can only register new @Tactic, @Axiom, etc. during AxiomInfo init process, but init has not started. This error usually means you forgot to initialize DerivationInfo, e.g. using withMathematica in a test suite"
        )
      case InitComplete =>
        // Allow anonymous tactic creation any time, and allow idempotent re-registration of existing tactic.
        if (di.codeName.startsWith("_") || _allInfo.contains(di.codeName)) ()
        else throw new Exception(
          s"Tried to register ${di.codeName}, but can only register new @Tactic, @Axiom, etc. during AxiomInfo init process, but init has finished. This error usually means you forgot to add a class to the list in DerivationInfoRegistry"
        )
    }
  }

  /** Adds di to all info tables. Assumes di is new. */
  private def addInfo(di: DerivationInfo): Unit = {
    _allInfo = _allInfo.+(di.codeName -> di)
    _byCanonicalName = _byCanonicalName.+(di.canonicalName -> di)
    // Note: independent pattern-matches so we don't miss infos that belong in multiple tables.
    di match {
      case (ai: AxiomInfo) => _axiomInfo = _axiomInfo.+(ai.codeName -> ai)
      case _ => ()
    }
    di match {
      case (ai: CoreAxiomInfo) => _coreAxiomInfo = _coreAxiomInfo.+(ai.codeName -> ai)
      case _ => ()
    }
    di match {
      case (ai: DerivedAxiomInfo) => _derivedAxiomInfo = _derivedAxiomInfo.+(ai.codeName -> ai)
      case _ => ()
    }
    di match {
      case (ai: DerivedRuleInfo) => _derivedRuleInfo = _derivedRuleInfo.+(ai.codeName -> ai)
      case _ => ()
    }
    di match {
      case (ai: ProvableInfo) => _provableInfo = _provableInfo.+(ai.codeName -> ai)
      case _ => ()
    }
    di match {
      case (si: StorableInfo) => _byStoredName = _byStoredName.+(si.storedName -> si)
      case _ => ()
    }
  }

  // Hack: derivedAxiom function expects its own derivedaxiominfo to be present during evaluation so that
  // it can look up a stored name rather than computing it. The actual solution is a simple refactor but it touches lots
  // of code so just delay [[value == derivedAxiom(...)]] execution till after info/
  def registerR[T, R <: DerivationInfo](value: => T, p: R): R = {
    // Note: We don't require DerivationInfo initialization to be "in progress" for registerR because it used for axioms rather than tactics.
    if (!_allInfo.contains(p.codeName)) addInfo(p)
    else if (_allInfo(p.codeName) != p) throw new IllegalArgumentException(
      "Duplicate name registration attempt: axiom " + p.codeName + " already registered as " + _allInfo(p.codeName) +
        " of " + _allInfo(p.codeName).getClass.getSimpleName
    )
    val _ = value
    p
  }

  def registerL[T, R <: DerivationInfo](value: => T, p: R): T = {
    requireInitInProgress(p)
    if (!_allInfo.contains(p.codeName)) addInfo(p)
    else if (_allInfo(p.codeName) != p) throw new IllegalArgumentException(
      "Duplicate name registration attempt: tactic " + p.codeName + " already registered as " + _allInfo(p.codeName) +
        " of " + _allInfo(p.codeName).getClass.getSimpleName
    )
    val _ = value
    value
  }

  /** code name mapped to derivation information */
  def byCodeName: Map[String, DerivationInfo] = allInfo

  /** Check whether the given `codeName` is a code name of any of the listed DerivationInfos. */
  def hasCodeName(codeName: String): Boolean = byCodeName.keySet.contains(codeName)

  def byCanonicalName: Map[String, DerivationInfo] = _byCanonicalName

  /** Throw an AssertionError if id does not conform to the rules for code names. */
  def assertValidIdentifier(id: String): Unit = { assert(id.forall(_.isLetterOrDigit), "valid code name: " + id) }

  /** Retrieve meta-information on an inference by the given code name `codeName` */
  def ofCodeName(codeName: String): DerivationInfo = {
    assert(byCodeName != null, "byCodeName should not be null.")
    assert(codeName != null, "codeName should not be null.")

    byCodeName.getOrElse(
      codeName,
      ofBuiltinName(codeName)
        .getOrElse(throw new IllegalArgumentException("No such DerivationInfo of identifier " + codeName)),
    )
  }

  /** Retrieve meta-information on a builtin tactic expression by the given `name`. */
  def ofBuiltinName(name: String): Option[DerivationInfo] = {
    val expandPattern = """(expand\("[^"]*"\))|(expandAllDefs)""".r
    name match {
      case expandPattern(_*) => Some(new BuiltinInfo(name, SimpleDisplayInfo(name, name, name, DisplayLevelInternal)))
      case _ => None
    }
  }

  /** Retrieve meta-information on an inference by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivationInfo = byCanonicalName
    .getOrElse(axiomName, ofBuiltinName(axiomName).getOrElse(throw AxiomNotFoundException(axiomName)))

}

/** Typed functions to circumvent type erasure of arguments and return types. */
abstract class TypedFunc[-A: TypeTag, +R: TypeTag] extends (A => R) {
  val retType: TypeTag[_] = scala.reflect.runtime.universe.typeTag[R]
  val argType: TypeTag[_] = scala.reflect.runtime.universe.typeTag[A]
}

/** Creates TypedFunc implicitly, e.g., by ((x: String) => x.length): TypedFunc[String, Int] */
object TypedFunc {
  implicit def apply[A: TypeTag, R: TypeTag](f: A => R): TypedFunc[A, R] = f match {
    case tf: TypedFunc[A, R] => tf
    case _ => new TypedFunc[A, R] {
        final def apply(arg: A): R = f(arg)
      }
  }
}

sealed trait DerivationInfo {

  /**
   * Canonical full name unique across all derivations (axioms or tactics). For axioms or axiomatic rules this is as
   * declared in [[AxiomBase]], for derived axioms or derived axiomatic rules as in [[DerivedAxioms]], and for
   * [[BelleExpr]] tactics it is identical to their codeName. Canonical names can and will contain spaces and special
   * chars.
   */
  val canonicalName: String

  /** How to render this inference step for display in a UI */
  val display: DisplayInfo

  /** The unique alphanumeric identifier for this inference step. Cannot contain spaces or special characters. */
  val codeName: String

  /**
   * Specification of inputs (other than positions) to the derivation, along with names to use when displaying in the
   * UI.
   */
  val inputs: List[ArgInfo] = Nil

  /** Inputs which should be serialized in tactic strings. For example, Generator args are left out. */
  val persistentInputs: List[ArgInfo] = inputs.filter {
    case (_: GeneratorArg) => false
    case _ => true
  }

  /**
   * Number of positional arguments to the derivation. Can be 0, 1 or 2.
   *   - 0 means this inference cannot be positioned but applies to the whole sequent.
   *   - 1 means this inference will be applied at one position.
   *   - 2 means this inference will be applied with two positions as input (e.g., use info at -2 to simplify 1).
   */
  val numPositionArgs: Int = 0

  /** Whether the derivation expects the caller to provide it with a way to generate invariants */
  val needsGenerator: Boolean = false

  /** Whether the derivation makes internal steps that are useful for users to see. */
  val revealInternalSteps: Boolean = false

  override def toString: String = "DerivationInfo(" + canonicalName + "," + codeName + ")"
}

// provables

/**
 * Meta-Information for a (derived) axiom or (derived) axiomatic rule
 * @see
 *   [[AxiomInfo]]
 * @see
 *   [[AxiomaticRuleInfo]]
 * @see
 *   [[DerivedRuleInfo]]
 */
sealed trait ProvableInfo extends DerivationInfo {

  /**
   * The [[ProvableSig]] representing this (derived) axiom or (derived) axiomatic rule. Needs to be [[Any]] to avoid
   * type dependency between separate modules. Implicit method [[provable: ProvableSig]] in keymaerax-core project
   * recovers intended type
   */
  private[macros] var theProvable: Option[Any] = None

  /** Formula representing this axiom/rule, if any. */
  private[macros] var theFormula: Option[Any] = None

  /**
   * Which unifier to use. For completeness, this declaration must be consistent with the default key from
   * [[AxiomIndex.axiomFor()]].
   * @see
   *   [[LinearMatcher]]
   */
  def unifier: Unifier

  /**
   * The key at which this formula will be unified against an input formula.
   * @see
   *   [[org.keymaerax.btactics.UnifyUSCalculus]]
   */
  val theKey: ExprPos = 0 :: Nil

  /**
   * The list of recursors which to look for later after using this axiom in a chase.
   * @see
   *   [[org.keymaerax.btactics.UnifyUSCalculus.chase]]
   */
  val theRecursor: List[ExprPos] = Nil
}

/**
 * Storable derivation info (e.g., as lemmas).
 * @see
 *   [[DerivedAxiomInfo]]
 * @see
 *   [[DerivedRuleInfo]]
 */
sealed trait StorableInfo extends DerivationInfo {
  val storedName: String = codeName.toLowerCase(Locale.ROOT)

  /** Gives the [[Lemma]] stored for this derivation info (after initialization). */
  // We would like to make theLemma writable only by [[Ax.scala]], but putting Ax.scala in the [[macros]] package
  // might be awkward. Instead, provide a public setter for private [[theLemma]]
  private var theLemma: Any = None
  def getLemma: Any = theLemma
  def setLemma(lem: Any): Unit = { theLemma = lem }
}

// axioms

/**
 * Meta-Information for an axiom or derived axiom, as declared by an @[[Axiom]] annotation.
 * @see
 *   [[org.keymaerax.btactics.AxIndex]]
 * @see
 *   [[Axiom]]
 */
sealed trait AxiomInfo extends ProvableInfo

/**
 * Meta-Information for an axiom from the prover core
 * @see
 *   [[org.keymaerax.core.AxiomBase]]
 * @see
 *   [[DerivedAxiomInfo]] [[theExpr]] should be [[Unit => DependentPositionTactic]], correct type recovered in
 *   keymaerax-core wrapper
 */
case class CoreAxiomInfo(
    override val canonicalName: String,
    override val display: DisplayInfo,
    override val codeName: String,
    override val unifier: Unifier,
    val theExpr: Unit => Any,
    override val theKey: ExprPos = 0 :: Nil,
    override val theRecursor: List[ExprPos] = Nil,
) extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  override val numPositionArgs = 1
}

/**
 * Information for a derived axiom proved from the core.
 * @see
 *   [[org.keymaerax.btactics.DerivedAxioms]]
 * @see
 *   [[CoreAxiomInfo]]
 * @TODO:
 *   Enforce theExpr : Unit => DependentPositionTactic
 */
case class DerivedAxiomInfo(
    override val canonicalName: String,
    override val display: DisplayInfo,
    override val codeName: String,
    override val unifier: Unifier,
    theExpr: Unit => Any,
    override val theKey: ExprPos = 0 :: Nil,
    override val theRecursor: List[ExprPos] = Nil,
) extends AxiomInfo with StorableInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  override val numPositionArgs = 1
}

// axiomatic proof rules

/**
 * Information for an axiomatic proof rule
 * @see
 *   [[org.keymaerax.core.AxiomBase]]
 * @see
 *   [[DerivedRuleInfo]]
 */
case class AxiomaticRuleInfo(
    override val canonicalName: String,
    override val display: DisplayInfo,
    override val codeName: String,
    override val unifier: Unifier,
    theExpr: Unit => Any,
    override val theKey: ExprPos = 0 :: Nil,
    override val theRecursor: List[ExprPos] = Nil,
) extends ProvableInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  override val numPositionArgs = 0
}

object AxiomaticRuleInfo {
  def apply(axiomName: String): AxiomaticRuleInfo = {
    DerivationInfo.byCanonicalName(axiomName) match {
      case info: AxiomaticRuleInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a core rule")
    }
  }
}

/**
 * Information for a derived rule proved from the core
 * @see
 *   [[org.keymaerax.btactics.DerivedAxioms]]
 * @see
 *   [[AxiomaticRuleInfo]]
 */
case class DerivedRuleInfo(
    override val canonicalName: String,
    override val display: DisplayInfo,
    override val codeName: String,
    override val unifier: Unifier,
    val theExpr: Unit => Any,
    override val theKey: ExprPos = 0 :: Nil,
    override val theRecursor: List[ExprPos] = Nil,
) extends ProvableInfo with StorableInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  override val numPositionArgs = 0
}

// tactics

/** Meta-information on builtin tactic expressions (expand etc.). */
class BuiltinInfo(
    override val codeName: String,
    override val display: DisplayInfo,
    override val needsGenerator: Boolean = false,
    override val revealInternalSteps: Boolean = false,
) extends DerivationInfo {
  val canonicalName: String = codeName
}

/** Meta-information on a tactic performing a proof step (or more) */
sealed abstract class TacticInfo(
    override val codeName: String,
    override val display: DisplayInfo,
    val theExpr: Unit => Any,
    override val needsGenerator: Boolean = false,
    override val revealInternalSteps: Boolean = false,
) extends DerivationInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  val canonicalName: String = codeName
}

case class PlainTacticInfo(
    override val codeName: String,
    override val display: DisplayInfo,
    override val needsGenerator: Boolean = false,
    override val revealInternalSteps: Boolean = false,
)(override val theExpr: Unit => Any)
    extends TacticInfo(codeName, display, theExpr, needsGenerator, revealInternalSteps) {}

case class PositionTacticInfo(
    override val codeName: String,
    override val display: DisplayInfo,
    override val needsGenerator: Boolean = false,
    override val revealInternalSteps: Boolean = false,
)(override val theExpr: Unit => Any)
    extends TacticInfo(codeName, display, theExpr, needsGenerator, revealInternalSteps) {
  override val numPositionArgs = 1
}

case class TwoPositionTacticInfo(
    override val codeName: String,
    override val display: DisplayInfo,
    override val needsGenerator: Boolean = false,
)(override val theExpr: Unit => Any)
    extends TacticInfo(codeName, display, theExpr, needsGenerator) {
  override val numPositionArgs = 2
}

case class InputTacticInfo(
    override val codeName: String,
    override val display: DisplayInfo,
    override val inputs: List[ArgInfo],
    override val needsGenerator: Boolean = false,
    override val revealInternalSteps: Boolean = false,
)(override val theExpr: Unit => TypedFunc[_, _])
    extends TacticInfo(codeName, display, theExpr, needsGenerator, revealInternalSteps)

case class InputPositionTacticInfo(
    override val codeName: String,
    override val display: DisplayInfo,
    override val inputs: List[ArgInfo],
    override val needsGenerator: Boolean = false,
    override val revealInternalSteps: Boolean = false,
)(override val theExpr: Unit => TypedFunc[_, _])
    extends TacticInfo(codeName, display, theExpr, needsGenerator, revealInternalSteps) {
  override val numPositionArgs = 1
}

case class InputTwoPositionTacticInfo(
    override val codeName: String,
    override val display: DisplayInfo,
    override val inputs: List[ArgInfo],
    override val needsGenerator: Boolean = false,
)(override val theExpr: Unit => TypedFunc[_, _])
    extends TacticInfo(codeName, display, theExpr, needsGenerator) {
  override val numPositionArgs = 2
}

object DerivedAxiomInfo {

  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def locate(axiomName: String): Option[DerivedAxiomInfo] = DerivationInfo.byCanonicalName(axiomName) match {
    case info: DerivedAxiomInfo => Some(info)
    case _ => None
  }

  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivedAxiomInfo = {
    DerivationInfo.byCanonicalName(axiomName) match {
      case info: DerivedAxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived axiom")
    }
  }

  /** All registered derived axiom info by code name. */
  def allInfo: Map[String, DerivedAxiomInfo] = DerivationInfo._derivedAxiomInfo

  /** All registered derived axiom info by stored name. */
  def allInfoByStoredName: Map[String, StorableInfo] = DerivationInfo._byStoredName
}

// axiomatic proof rules

object DerivedRuleInfo {

  /** Retrieve meta-information on a rule by the given canonical name `ruleName` */
  def locate(ruleName: String): Option[DerivedRuleInfo] = DerivationInfo.byCanonicalName(ruleName) match {
    case info: DerivedRuleInfo => Some(info)
    case _ => None
  }

  /** Retrieve meta-information on a rule by the given canonical name `ruleName` */
  def apply(ruleName: String): DerivedRuleInfo = DerivationInfo.byCanonicalName(ruleName) match {
    case info: DerivedRuleInfo => info
    case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived rule")
  }

  def allInfo: Map[String, DerivedRuleInfo] = DerivationInfo._derivedRuleInfo
}

// tactics

object TacticInfo {
  def apply(tacticName: String): TacticInfo = DerivationInfo.byCodeName(tacticName) match {
    case info: TacticInfo => info
    case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a tactic")
  }
}

////////////////////////////////////////////////////////////
// Companion objects for projections of DerivationInfo registry
////////////////////////////////////////////////////////////

// provables

object ProvableInfo {

  /** Retrieve meta-information on a (derived) axiom or (derived) axiomatic rule by the given canonical name `name` */
  def locate(name: String): Option[ProvableInfo] = DerivationInfo(name) match {
    case info: ProvableInfo => Some(info)
    case _ => None
  }

  /** Retrieve meta-information on a (derived) axiom or (derived) axiomatic rule by the given canonical name `name` */
  def apply(name: String): ProvableInfo = {
    val res = DerivationInfo(name)
    res match {
      case info: ProvableInfo => info
      case info => throw new Exception(
          "Derivation \"" + info.canonicalName + "\" is not an axiom or axiomatic rule, whether derived or not."
        )
    }
  }

  /** True if ProvableInfo with `storedName` exists, false otherwise. */
  def existsStoredName(storedName: String): Boolean = DerivationInfo._byStoredName.contains(storedName)

  /** Retrieve meta-information on an inference by the given stored name `storedName` */
  def ofStoredName(storedName: String): ProvableInfo = {
    DerivationInfo._byStoredName.get(storedName) match {
      case Some(info: ProvableInfo) => info
      case Some(info) => throw new Exception(
          "Derivation \"" + info.canonicalName + "\" is not an axiom or axiomatic rule, whether derived or not."
        )
      case _ => throw new Exception("Derivation \"" + storedName + "\" is not a derived axiom or rule.")
    }
  }

  def allInfo: Map[String, ProvableInfo] = DerivationInfo._provableInfo
}

// axioms

object AxiomInfo {

  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): AxiomInfo = DerivationInfo(axiomName) match {
    case info: AxiomInfo => info
    case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }

  /** Retrieve meta-information on an axiom by the given code name `codeName` */
  def ofCodeName(codeName: String): AxiomInfo = DerivationInfo.ofCodeName(codeName) match {
    case info: AxiomInfo => info
    case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }

  def allInfo: Map[String, AxiomInfo] = DerivationInfo._axiomInfo
}

object CoreAxiomInfo {

  /** Retrieve meta-information on a core axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): CoreAxiomInfo = DerivationInfo(axiomName) match {
    case info: CoreAxiomInfo => info
    case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a core axiom")
  }

  /** Retrieve meta-information on a core axiom by the given code name `codeName` */
  def ofCodeName(codeName: String): CoreAxiomInfo = DerivationInfo.ofCodeName(codeName) match {
    case info: CoreAxiomInfo => info
    case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }

  def allInfo: Map[String, CoreAxiomInfo] = DerivationInfo._coreAxiomInfo
}
