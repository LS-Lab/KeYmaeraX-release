/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.AxiomNotFoundException
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.HashMap

/**
  * Since axioms are always referred to by their names (which are strings), we have the following problems:
  * 1) It's hard to keep everything up to date when a new axiom is added
  * 2) We don't get any static exhaustiveness checking when we case on an axiom
  *
  * AxiomInfo exists to help fix that. An AxiomInfo is just a collection of per-axiom information. The tests for
  * this object dynamically ensure it is exhaustive with respect to AxiomBase and DerivedAxioms. By adding a new
  * field to AxiomInfo you can ensure that all new axioms will have to have that field.
  * Created by bbohrer on 12/28/15.
  */

/** UI display information on how to show an axiom, rule, or tactic application */
sealed trait DisplayInfo {
  def name: String
  def asciiName: String
}
case class SimpleDisplayInfo(override val name: String, override val asciiName: String) extends DisplayInfo
case class RuleDisplayInfo(names: SimpleDisplayInfo, conclusion: SequentDisplay, premises:List[SequentDisplay]) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}
case class SequentDisplay(ante: List[String], succ: List[String], isClosed: Boolean = false)
case class AxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}
case class InputAxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String, input: List[ArgInfo]) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}

/**
  * Central list of all derivation steps (axioms, derived axioms, proof rules, tactics)
  * with meta information of relevant names and display names and visualizations for the user interface.
  */
object DerivationInfo {
  implicit def displayInfo(name: String): SimpleDisplayInfo = {SimpleDisplayInfo(name, name)}
  implicit def displayInfo(pair: (String, String)): SimpleDisplayInfo = SimpleDisplayInfo(pair._1, pair._2)
  implicit def sequentDisplay(succAcc:(List[String], List[String])): SequentDisplay = {
    SequentDisplay(succAcc._1, succAcc._2)
  }
  implicit def sequentDisplay(succAccClosed:(List[String], List[String], Boolean)): SequentDisplay = {
    SequentDisplay(succAccClosed._1, succAccClosed._2, succAccClosed._3)
  }

  case class AxiomNotFoundException(axiomName: String) extends ProverException("Axiom with said name not found: " + axiomName)

  //@todo
  private val needsCodeName = "TODOTHISAXIOMSTILLNEEDSACODENAME"

  private def useAt(l:Lemma):DependentPositionTactic = UnifyUSCalculus.useAt(l)
  private val posnil = TacticFactory.anon((pos,seq) => TactixLibrary.nil)

  private def convert(rules: Map[String,Provable]): List[DerivationInfo] =
  //@todo display info is rather impoverished
    rules.keys.map(name => AxiomaticRuleInfo(name, SimpleDisplayInfo(name,name), canonicalize(name))).toList
  private def canonicalize(name: String): String = name.filter(c => c.isLetterOrDigit)
  /**
    * Central registry for axiom, derived axiom, proof rule, and tactic meta-information.
    * Transferred into subsequent maps etc for efficiency reasons.
    */
  private [btactics] val allInfo: List[DerivationInfo] = convert(Provable.rules) ++ List(

    // first-order logic quantifiers
    new CoreAxiomInfo("all instantiate", ("∀inst","allInst"), "allInst", {case () => ???}),
    new DerivedAxiomInfo("all distribute", ("∀→","all->"), "allDist", {case () => SequentCalculus.allDist}),
    new CoreAxiomInfo("vacuous all quantifier", ("V∀","allV"), "allV", {case () => SequentCalculus.allV}),
    new DerivedAxiomInfo("vacuous exists quantifier", ("V∃","existsV"), "existsV", {case () => SequentCalculus.existsV}),

    // more
    new CoreAxiomInfo("const congruence", "CCE", "constCongruence", {case () => ???}),
    new CoreAxiomInfo("const formula congruence", "CCQ", "constFormulaCongruence", {case () => ???}),

    new CoreAxiomInfo("all dual", ("∀d","alld"), "alld", {case () => posnil}),
    new CoreAxiomInfo("all dual time", ("∀d","alldt"), "alldt", {case () => posnil}),
    new CoreAxiomInfo("all eliminate", ("∀e","alle"), "alle", {case () => posnil}),
    new CoreAxiomInfo("exists eliminate", ("∃e","existse"), "existse", {case () => SequentCalculus.existsE}),

    new DerivedAxiomInfo("!& deMorgan"
      , AxiomDisplayInfo(("¬∧", "!&"), "<span class=\"k4-axiom-key\">¬(p∧q)</span>↔(¬p|¬q)")
      , "notAnd", {case () => useAt(DerivedAxioms.notAnd)}),
    new DerivedAxiomInfo("!| deMorgan"
      , AxiomDisplayInfo(("¬∨","!|"), "<span class=\"k4-axiom-key\">(¬(p|q))</span>↔(¬p∧¬q)")
      , "notOr", {case () => useAt(DerivedAxioms.notOr)}),

    new DerivedAxiomInfo("<-> reflexive", ("↔R","<->R"), "equivReflexive", {case () => useAt(DerivedAxioms.equivReflexiveAxiom)}),
    new DerivedAxiomInfo("-> distributes over &", ("→∧", "->&"), "implyDistAnd", {case () => useAt(DerivedAxioms.implyDistAndAxiom)}),
    new DerivedAxiomInfo("-> distributes over <->", ("→↔","-><->"), "implyDistEquiv", {case () => useAt(DerivedAxioms.implyDistEquivAxiom)}),
    new DerivedAxiomInfo("-> weaken", ("→W","->W"), "implyWeaken", {case () => useAt(DerivedAxioms.implWeaken)}),

    new DerivedAxiomInfo("& commute", ("∧C","&C"), "andCommute", {case () => useAt(DerivedAxioms.andCommute)}),
    new DerivedAxiomInfo("& reflexive", ("∧R","&R"), "andReflexive", {case () => useAt(DerivedAxioms.andReflexive)}),
    new DerivedAxiomInfo("& associative", ("∧A","&A"), "andAssoc", {case () => useAt(DerivedAxioms.andAssoc)}),
    new DerivedAxiomInfo("-> tautology", ("→taut","->taut"), "implyTautology", {case () => useAt(DerivedAxioms.implyTautology)}),

    new DerivedAxiomInfo("->true"
      , AxiomDisplayInfo(("→⊤","->T"), "<span class=\"k4-axiom-key\">(p→⊤)</span>↔⊤")
      , "implyTrue", {case () => useAt(DerivedAxioms.impliesTrue)}),
    new DerivedAxiomInfo("true->"
      , AxiomDisplayInfo(("⊤→", "T->"), "<span class=\"k4-axiom-key\">(⊤→p)</span>↔p")
      , "trueImply", {case () => useAt(DerivedAxioms.trueImplies)}),
    new DerivedAxiomInfo("&true"
      , AxiomDisplayInfo(("∧⊤","&T"), "<span class=\"k4-axiom-key\">(p∧⊤)</span>↔p")
      , "andTrue", {case () => useAt(DerivedAxioms.andTrue)}),
    new DerivedAxiomInfo("true&"
      , AxiomDisplayInfo(("⊤∧","T&"), "<span class=\"k4-axiom-key\">(⊤∧p)</span>↔p")
      , "trueAnd", {case () => useAt(DerivedAxioms.trueAnd)}),

    new DerivedAxiomInfo("-> self", ("→self","-> self"), "implySelf", {case () => useAt(DerivedAxioms.implySelf)}),
    new DerivedAxiomInfo("<-> true", ("↔true","<-> true"), "equivTrue", {case () => useAt(DerivedAxioms.equivTrue)}),
    //@todo internal only
//    new DerivedAxiomInfo("K1", "K1", "K1", {case () => useAt(DerivedAxioms.K1)}),
//    new DerivedAxiomInfo("K2", "K2", "K2", {case () => useAt(DerivedAxioms.K2)}),
    new DerivedAxiomInfo("PC1", "PC1", "PC1", {case () => useAt(DerivedAxioms.PC1)}),
    new DerivedAxiomInfo("PC2", "PC2", "PC2", {case () => useAt(DerivedAxioms.PC2)}),
    new DerivedAxiomInfo("PC3", "PC3", "PC3", {case () => useAt(DerivedAxioms.PC3)}),
    new DerivedAxiomInfo("PC9", "PC9", "PC9", {case () => useAt(DerivedAxioms.PC9)}),
    new DerivedAxiomInfo("PC10", "PC10", "PC10", {case () => useAt(DerivedAxioms.PC10)}),

    new DerivedAxiomInfo("&->", "&->", "andImplies", {case () => useAt(DerivedAxioms.andImplies)}),

    // Note: Tactic info does not cover all tactics yet.
    // Proof rule position PositionTactics
    new PositionTacticInfo("notL"
      , RuleDisplayInfo(("¬L", "!L"), (List("¬P", "&Gamma;"),List("&Delta;")), List((List("&Gamma;"),List("&Delta;","P"))))
      , {case () => SequentCalculus.notL}),
    new PositionTacticInfo("notR"
      , RuleDisplayInfo(("¬R", "!R"), (List("&Gamma;"),List("¬P","&Delta;")), List((List("&Gamma;","P"),List("&Delta;"))))
      , {case () => SequentCalculus.notR}),
    new PositionTacticInfo("andR"
      , RuleDisplayInfo(("∧R", "^R"), (List("&Gamma;"),List("P∧Q","&Delta;")),
        List((List("&Gamma;"),List("P", "&Delta;")),
          (List("&Gamma;"), List("Q", "&Delta;"))))
      , {case () => SequentCalculus.andR}),
    new PositionTacticInfo("andL"
      , RuleDisplayInfo(("∧L", "^L"), (List("P∧Q", "&Gamma;"),List("&Delta;")), List((List("&Gamma;","P","Q"),List("&Delta;"))))
      , {case () => SequentCalculus.andL}),
    new PositionTacticInfo("orL"
      , RuleDisplayInfo(("∨L", "|L"), (List("P∨Q", "&Gamma;"),List("&Delta;")),
        List((List("&Gamma;", "P"),List("&Delta;")),
          (List("&Gamma;", "Q"),List("&Delta;"))))
      , {case () => SequentCalculus.orL}),
    new PositionTacticInfo("implyR"
      , RuleDisplayInfo(("→R", "->R"), (List("&Gamma;"),List("P→Q", "&Delta;")), List((List("&Gamma;","P"),List("Q","&Delta;"))))
      , {case () => SequentCalculus.implyR}),
    new PositionTacticInfo("implyL"
      , RuleDisplayInfo(("→L", "->L"), (List("P→Q","&Gamma;"),List("&Delta;")),
        List((List("&Gamma;","P→Q"),List("&Delta;")),
          (List("&Gamma;"),List("Q"))))
      , {case () => SequentCalculus.implyL}),
    new PositionTacticInfo("equivL"
      , RuleDisplayInfo(("↔L", "<->L"), (List("P↔Q","&Gamma;"),List("&Delta;")),
        List((List("&Gamma;","P∧Q"),List("&Delta;")),
          (List("&Gamma;","¬P∧¬Q"),List("&Delta;"))
         ))
      , {case () => SequentCalculus.equivL}),
    new PositionTacticInfo("equivR"
      , RuleDisplayInfo(("↔R", "<->R"), (List("&Gamma;"),List("P↔Q","&Delta;")),
        List((List("&Gamma;","P","Q"),List("&Delta;")),
          (List("&Gamma;","¬P","¬Q"),List("&Delta;"))))
      , {case () => SequentCalculus.equivR}),
    new InputPositionTacticInfo("allL"
      , RuleDisplayInfo(("∀L", "allL"), (List("&Gamma;","∀x P(x)"), List("&Delta;")),
        List((List("&Gamma;", "P(θ)"),List("&Delta;"))))
      , List(TermArg("θ"))
      , {case () => (t:Term) => SequentCalculus.allL(t)}),
    new PositionTacticInfo("allR"
      , RuleDisplayInfo(("∀R", "allR"), (List("&Gamma;"), List("∀x P(x)", "&Delta;")),
        List((List("&Gamma;"),List("P(x)","&Delta;"))))
      , {case () => SequentCalculus.allR}),
    new PositionTacticInfo("existsL"
      , RuleDisplayInfo(("∃L", "existsL"), (List("&Gamma;","∃x P(x)"),List("&Delta;")),
        List((List("&Gamma;","P(x)"),List("&Delta;"))))
      , {case () => SequentCalculus.existsL}),
    new PositionTacticInfo("existsR"
      , RuleDisplayInfo(("∃R", "existsR"), (List("&Gamma;"),List("∃x P(x)","&Delta;")),
        List((List("&Gamma;"),List("P(&theta;)","&Delta;"))))
      , {case () => SequentCalculus.existsR}),

    new PositionTacticInfo("commuteEquivL", ("↔CL", "<->CL"), {case () => SequentCalculus.commuteEquivL}),
    new PositionTacticInfo("commuteEquivR", ("↔CR", "<->CR"), {case () => SequentCalculus.commuteEquivR}),
    new PositionTacticInfo("equivifyR", ("→↔","-><->"), {case () => SequentCalculus.equivifyR}),
    new PositionTacticInfo("hideL"
      , RuleDisplayInfo("WL", (List("&Gamma;", "P"),List("&Delta;"))
        , List((List("&Gamma;"),List("&Delta;")))),
      {case () => SequentCalculus.hideL}),
    new PositionTacticInfo("hideR"
      , RuleDisplayInfo("WR", (List("&Gamma;"),List("P", "&Delta;"))
        , List((List("&Gamma;"),List("&Delta;")))),
      {case () => SequentCalculus.hideR}),
    new PositionTacticInfo("coHideL", "W", {case () => SequentCalculus.cohideL}),
    new PositionTacticInfo("coHideR", "W", {case () => SequentCalculus.cohideR}),
    new PositionTacticInfo("closeFalse"
      , RuleDisplayInfo(("⊥L", "falseL"), (List("⊥","&Gamma;"),List("&Delta;")), List())
      , {case () => TactixLibrary.closeF}),
    new PositionTacticInfo("closeTrue"
      , RuleDisplayInfo(("⊤R","trueR"), (List("&Gamma;"), List("⊤","&Delta;")),List())
        ,{case () => TactixLibrary.closeT}),
    new PositionTacticInfo("skolemizeL", "skolem", {case () => ProofRuleTactics.skolemizeL}),
    new PositionTacticInfo("skolemizeR", "skolem", {case () => ProofRuleTactics.skolemizeR}),
    new PositionTacticInfo("skolemize", "skolem", {case () => ProofRuleTactics.skolemize}),
    new PositionTacticInfo("coHide", "W", {case () => SequentCalculus.cohide}),
    new PositionTacticInfo("hide", "W", {case () => SequentCalculus.hide}),
    new PositionTacticInfo("allL2R", "L=R all", {case () => TactixLibrary.exhaustiveEqL2R}),
    new PositionTacticInfo("allR2L", "R=L all", {case () => TactixLibrary.exhaustiveEqR2L}),

    // proof management tactics
    new TacticInfo("debug", "debug", {case () => DebuggingTactics.debug("", true)}),   // turn into input tactic if message should be stored too
    new TacticInfo("done", "done", {case () => TactixLibrary.done}), // turn into input tactic if message should be stored too

    // Proof rule two-position tactics
    new TwoPositionTacticInfo("coHide2", "W", {case () => SequentCalculus.cohide2}),
    new TwoPositionTacticInfo("equivRewriting", RuleDisplayInfo("equivRewriting", (List("&Gamma;", "∀X p(X) <-> q(X)"), List("p(Z)", "&Delta;")), List((List("&Gamma;", "∀X p(X) <-> q(X)"), List("q(Z)", "&Delta;")))), {case () => PropositionalTactics.equivRewriting}),
    //    new TwoPositionTacticInfo("exchangeL", "X", {case () => ProofRuleTactics.exchangeL}),
//    new TwoPositionTacticInfo("exchangeR", "X", {case () => ProofRuleTactics.exchangeR}),
    new TacticInfo("closeId",
      RuleDisplayInfo("closeId", (List("&Gamma;", "P"), List("P", "&Delta;")), Nil),
      {case () => TactixLibrary.closeId}),
    new TwoPositionTacticInfo("L2R",
      RuleDisplayInfo("L2R",
        /*conclusion*/ (List("&Gamma;", "x=y", "P(x)"), List("Q(x)", "&Delta;")),
        /*premise*/    List((List("&Gamma;", "x=y", "P(y)"), List("Q(y)", "&Delta;")))),
      {case () => (pos: AntePosition) => TactixLibrary.eqL2R(pos)}),
//      {case () => ProofRuleTactics.trivialCloser}), //@todo This is a 4.1b3 merge conflict. I'm not sure what the correct behavior is.

    // Proof rule input tactics
    new InputTacticInfo("cut"
      , RuleDisplayInfo(("\u2702","cut")
        ,(List("&Gamma;"), List("&Delta;"))
        ,List(
          (List("&Gamma;"),List("&Delta;","P")),
          (List("&Gamma;", "P"), List("&Delta;"))))
        ,List(FormulaArg("P")), {case () => (fml:Formula) => ProofRuleTactics.cut(fml)}),
    // Proof rule input position tactics
    //@todo Move these DependentPositionTactic wrappers to ProofRuleTactics?
    new InputPositionTacticInfo("cutL", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutL") {
        /** Create the actual tactic to be applied at position pos */
        override def factory(pos: Position): DependentTactic = new DependentTactic("cutL") {
          ProofRuleTactics.cutL(fml)(pos.checkAnte.top)
        }
      }}),
    new InputPositionTacticInfo("cutR", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutR") {
        /** Create the actual tactic to be applied at position pos */
        override def factory(pos: Position): DependentTactic = new DependentTactic("cutR") {
          ProofRuleTactics.cutR(fml)(pos.checkSucc.top)
        }
      }}),
    new InputPositionTacticInfo("cutLR", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutLR") {
          /** Create the actual tactic to be applied at position pos */
          override def factory(pos: Position): DependentTactic = new DependentTactic("cutLR") {
            ProofRuleTactics.cutLR(fml)(pos)
          }
        }}),

    new InputPositionTacticInfo("boundRename"
      , RuleDisplayInfo(("BR", "BR"), (List("&Gamma;"), List("∀x P(x)","&Delta;")),
        List((List("&Gamma;"),List("∀y P(y)","&Delta;"))))
      , List(TermArg("x"),TermArg("y"))
      , {case () => (x:Term) => (y:Term) => TactixLibrary.boundRename(x.asInstanceOf[Variable],y.asInstanceOf[Variable])}),

  //
    new TacticInfo("TrivialCloser", "TrivialCloser", {case () => ProofRuleTactics.trivialCloser}),
    new TacticInfo("close", "close", {case () => SequentCalculus.close}),
    new PositionTacticInfo("orR1", "orR1", {case () => SequentCalculus.orR1}),
    new PositionTacticInfo("orR2", "orR2", {case () => SequentCalculus.orR2}),
    new PositionTacticInfo("nil", "nil", {case () => Idioms.nil}),

    // TactixLibrary tactics
    new PositionTacticInfo("step", "step", {case () => TactixLibrary.step}),
    new PositionTacticInfo("normalize", "normalize", {case () => TactixLibrary.normalize}),
    new PositionTacticInfo("unfoldProgramNormalize", "unfoldProgramNormalize", {case () => TactixLibrary.unfoldProgramNormalize}),
    new PositionTacticInfo("prop", "prop", {case () => TactixLibrary.prop}),
    new PositionTacticInfo("chase", "chase", {case () => TactixLibrary.chase})

  ) ensuring(consistentInfo _, "meta-information on AxiomInfo is consistent with actual (derived) axioms etc.")

  private def consistentInfo(list: List[DerivationInfo]): Boolean = {
    //@note to avoid file storage issues on some OSes, lowercase versions of names are expected to be unique.
    val canonicals = list.map(i => i.canonicalName.toLowerCase())
    val codeNames = list.map(i => i.codeName.toLowerCase()).filter(n => n!=needsCodeName)
    list.forall(i => i match {
        case ax: CoreAxiomInfo => Provable.axiom.contains(ax.canonicalName) ensuring(r=>r, "core axiom correctly marked as CoreAxiomInfo: " + ax.canonicalName)
        case ax: DerivedAxiomInfo => true //@todo can't ask DerivedAxioms.derivedAxiom yet since still initializing, besides that'd be circular
        case _ => true
      }
    ) &
      (canonicals.length==canonicals.distinct.length ensuring(r=>r, "unique canonical names: " + (canonicals diff canonicals.distinct))) &
      (codeNames.length==codeNames.distinct.length ensuring(r=>r, "unique code names / identifiers: " + (codeNames diff codeNames.distinct)))
  }

  /** code name mapped to derivation information */
  private val byCodeName: Map[String, DerivationInfo] =
  /* @todo Decide on a naming convention. Until then, making everything case insensitive */
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
        acc.+((info.codeName.toLowerCase(), info))
    }

  /** canonical name mapped to derivation information */
  private val byCanonicalName: Map[String, DerivationInfo] =
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
      acc.+((info.canonicalName.toLowerCase, info))
    }

  /** Retrieve meta-information on an inference by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivationInfo = {
    byCanonicalName.getOrElse(axiomName.toLowerCase,
        throw new AxiomNotFoundException(axiomName))
  }

  /** Throw an AssertionError if id does not conform to the rules for code names. */
  def assertValidIdentifier(id:String) = { assert(id.forall{case c => c.isLetterOrDigit}, "valid code name: " + id)}

  /** Retrieve meta-information on an inference by the given code name `codeName` */
  def ofCodeName(codeName:String): DerivationInfo = {
    assert(byCodeName != null, "byCodeName should not be null.")
    assert(codeName != null, "codeName should not be null.")

    byCodeName.getOrElse(codeName.toLowerCase,
      throw new IllegalArgumentException("No such DerivationInfo of identifier " + codeName)
    )
  }

  def hasCodeName(codeName: String): Boolean = byCodeName.keySet.contains(codeName.toLowerCase)
}

object AxiomInfo {
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): AxiomInfo =
    DerivationInfo(axiomName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }

  /** Retrieve meta-information on an axiom by the given code name `codeName` */
  def ofCodeName(codeName: String): AxiomInfo =
    DerivationInfo.ofCodeName(codeName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
    }
}

object TacticInfo {
  def apply(tacticName: String): TacticInfo =
    DerivationInfo(tacticName) match {
      case info:TacticInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a tactic")
    }
}

sealed trait ArgInfo {
  val sort: String
  val name: String
}
case class FormulaArg (override val name: String) extends ArgInfo {
  val sort = "formula"
}
case class VariableArg (override val name: String) extends ArgInfo {
  val sort = "variable"
}
case class TermArg (override val name: String) extends ArgInfo {
  val sort = "term"
}
@deprecated("Until lists are actually added to the concrete syntax of Bellerophon.", "4.2b1")
case class ListArg (override val name: String, elementSort: String) extends ArgInfo {
  val sort = "list"
}

/** Meta-information on a derivation step, which is an axiom, derived axiom, proof rule, or tactic. */
sealed trait DerivationInfo {
  /** Canonical name unique across all derivations (axioms or tactics). For axioms this is as declared in the
    * axioms file, for and tactics it is identical to codeName. Can and will contain spaces and special chars. */
  val canonicalName: String
  /** How to display this inference step in a UI */
  val display: DisplayInfo
  /** The unique alphanumeric identifier for this inference step. */
  val codeName: String
  /** Specification of inputs (other than positions) to the derivation, along with names to use when displaying in the UI. */
  val inputs: List[ArgInfo] = Nil
  /** Bellerophon tactic implementing the derivation. For non-input tactics this is simply a BelleExpr. For input tactics
    * it is (curried) function which accepts the inputs and produces a BelleExpr. */
  def belleExpr: Any
  //@todo add formattedName/unicodeName: String
  /** Number of positional arguments to the derivation. Can be 0, 1 or 2. */
  val numPositionArgs: Int = 0
  /** Whether the derivation expects the caller to provide it with a way to generate invariants */
  val needsGenerator: Boolean = false
  override def toString: String = "DerivationInfo(" + canonicalName + "," + codeName + ")"
}

/** Meta-Information for a (derived) axiom or (derived) axiomatic rule */
trait ProvableInfo extends DerivationInfo {
  /** The Provable representing this (derived) axiom or (derived) axiomatic rule */
  val provable: Provable
}

object ProvableInfo {
  /** Retrieve meta-information on a (derived) axiom or (derived) axiomatic rule by the given canonical name `name` */
  def locate(name: String): Option[ProvableInfo] =
    DerivationInfo(name) match {
      case info: ProvableInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on a (derived) axiom or (derived) axiomatic rule by the given canonical name `name` */
  def apply(name: String): ProvableInfo =
    DerivationInfo(name) match {
      case info: ProvableInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom or axiomatic rule, whether derived or not.")
    }

  /** Retrieve meta-information on an inference by the given code name `codeName` */
  def ofCodeName(codeName:String): ProvableInfo = {
    DerivationInfo.ofCodeName(codeName) match {
      case info: ProvableInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom or axiomatic rule, whether derived or not.")
    }
  }

  val allInfo:List[ProvableInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[ProvableInfo]).map(_.asInstanceOf[ProvableInfo])
}


/** Meta-Information for an axiom or derived axiom */
trait AxiomInfo extends ProvableInfo {
  /** The valid formula that this axiom represents */
  def formula: Formula
}

/** Meta-Information for an axiom from the prover core */
case class CoreAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => DependentPositionTactic) extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory
  def belleExpr = codeName by ((pos:Position, seq:Sequent) => expr ()(pos))
  override val formula:Formula = {
    Provable.axiom.get(canonicalName) match {
      case Some(fml) => fml
      case None => throw new AxiomNotFoundException("No formula for core axiom " + canonicalName)
    }
  }
  override lazy val provable:Provable = Provable.axioms(canonicalName)
  override val numPositionArgs = 1
}

/** Information for a derived axiom proved from the core */
case class DerivedAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => DependentPositionTactic) extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory
  def belleExpr = codeName by ((pos:Position, seq:Sequent) => expr()(pos))
  override lazy val formula: Formula =
    DerivedAxioms.derivedAxiomOrRule(canonicalName).conclusion.succ.head
//  {
//    DerivedAxioms.derivedAxiomMap.get(canonicalName) match {
//      case Some(fml) => fml._1
//      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
//    }
//  }
  override lazy val provable:Provable = DerivedAxioms.derivedAxiomOrRule(canonicalName)
  override val numPositionArgs = 1
}

object DerivedAxiomInfo {
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def locate(axiomName: String): Option[DerivedAxiomInfo] =
    DerivationInfo(axiomName) match {
      case info: DerivedAxiomInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivedAxiomInfo =
    DerivationInfo(axiomName) match {
      case info: DerivedAxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived axiom")
    }

  val allInfo:List[DerivedAxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[DerivedAxiomInfo]).map(_.asInstanceOf[DerivedAxiomInfo])
}

// tactics

/** Meta-information on a tactic performing a proof step (or more) */
class TacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false) extends DerivationInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  val canonicalName = codeName
}

case class PositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 1
}

case class TwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 2
}

case class InputTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator)

case class InputPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 1
}

case class InputTwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 2
}

/** Information for an axiomatic rule */
case class AxiomaticRuleInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String) extends ProvableInfo {
  val expr = TactixLibrary.by(provable, codeName)
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr
  lazy val provable: Provable = Provable.rules(canonicalName)
  override val numPositionArgs = 0
}


/** Information for a derived rule proved from the core */
case class DerivedRuleInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any) extends ProvableInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  lazy val provable: Provable = DerivedAxioms.derivedAxiomOrRule(canonicalName)
  override val numPositionArgs = 0
}

object DerivedRuleInfo {
  /** Retrieve meta-information on a rule by the given canonical name `ruleName` */
  def locate(ruleName: String): Option[DerivedRuleInfo] =
    DerivationInfo(ruleName) match {
      case info: DerivedRuleInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on a rule by the given canonical name `ruleName` */
  def apply(ruleName: String): DerivedRuleInfo =
    DerivationInfo(ruleName) match {
      case info: DerivedRuleInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived rule")
    }

  val allInfo:List[DerivedAxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[DerivedAxiomInfo]).map(_.asInstanceOf[DerivedAxiomInfo])
}
