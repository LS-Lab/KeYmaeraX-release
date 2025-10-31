/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{
  BelleExpr,
  BuiltInTactic,
  DependentPositionTactic,
  DependentPositionWithAppliedInputTactic,
  OnAll,
  TacticAssertionError,
  TacticInapplicableFailure,
}
import org.keymaerax.btactics.Ax.*
import org.keymaerax.btactics.AxiomaticODESolver.ofAtoms
import org.keymaerax.btactics.DLBySubst.discreteGhost
import org.keymaerax.btactics.HilbertCalculus.{diamondd, DW}
import org.keymaerax.btactics.SequentCalculus.*
import org.keymaerax.btactics.TacticFactory.{anon, TacticForNameFactory}
import org.keymaerax.btactics.TactixLibrary.{prop, proveBy}
import org.keymaerax.btactics.UnifyUSCalculus.{useAt, CMon}
import org.keymaerax.btactics.helpers.DifferentialHelper.atomicOdes
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.btactics.macros.{
  CoreAxiomInfo,
  DerivedAxiomInfo,
  DisplayLevel,
  ExpressionArg,
  InputPositionTacticInfo,
  PositionTacticInfo,
  TacticConstructor0,
  TacticConstructor1,
  Unifier,
}
import org.keymaerax.core.*
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.Augmentors.{FormulaAugmentor, SequentAugmentor}
import org.keymaerax.infrastruct.FormulaTools.dualFree
import org.keymaerax.infrastruct.PosInExpr.HereP
import org.keymaerax.infrastruct.{PosInExpr, Position}
import org.keymaerax.parser.StringConverter.StringToStringConverter
import org.keymaerax.pt.ProvableSig

object RefinementCalculus {

  /** Refinement axioms */
  /** see [[refTrans]] */
  @Derivation
  val refTransAx: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refTransAx",
    canonicalName = "refinement transitive",
    displayName = Some("Refinement Transitive Ax"),
    displayConclusion = "__a <= b ∧ b <= c__ -> a <= c",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAntiSym: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAntiSym",
    canonicalName = "refinement antisymmetry",
    displayName = Some("Refinement Antisymmetry"),
    displayConclusion = "__a == b__ <-> (a <= b ∧ b <= a)",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refBox: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refBox",
    canonicalName = "refinement box",
    displayName = Some("Ref Box"),
    displayConclusion = "a <= b -> __[a]P <- [b]P__",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refTest: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refTest",
    canonicalName = "refinement test",
    displayName = Some("Refinement Test"),
    displayConclusion = "__?p <= ?q__ <-> (p -> q)",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refAssign: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssign",
    canonicalName = "refinement assign",
    displayName = Some("Refinement Assign"),
    displayConclusion = "__x:=f__ == x:=*;?(x=f)",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Full,
  )
  @Derivation
  val refStutter: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refStutter",
    canonicalName = "refinement stutter",
    displayName = Some("Refinement Stutter"),
    displayConclusion = "__x:=x__ == ?⊤",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceL",
    canonicalName = "refinement choice left",
    displayName = Some("Refinement Choice Left"),
    displayConclusion = "__a ∪ b <= c__ <-> (a <= c ∧ b <= c)",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refChoiceR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceR",
    canonicalName = "refinement choice right",
    displayName = Some("Refinement Choice Right"),
    displayConclusion = "__a <= b ∪ c__ <- (a <= b ∨ a <= c)",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refSeq: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refSeq",
    canonicalName = "refinement sequence",
    displayName = Some("Refinement Sequence"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "__a;b <= c;d__ <- a <= c ∧ [a](b <= d)",
    key = "1",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refLoopL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refLoopL",
    canonicalName = "refinement loop left",
    displayName = Some("Refinement Loop Left"),
    displayConclusion = "__{a*};b <= b__ <- [a*](a;b <= b)",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refLoopR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refLoopR",
    canonicalName = "refinement loop right",
    displayName = Some("Refinement Loop Right"),
    displayConclusion = "__a;{b*} <= a__ <- a;b <= a",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refTestDet: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refTestDet",
    canonicalName = "refinement test det",
    displayName = Some("Refinement Test Det"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "?p;a <= ?p;b <-> __[?p](a <= b)__",
    key = "1", // key = "0" is refSeq
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refAssignDet: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignDet",
    canonicalName = "refinement assign det",
    displayName = Some("Refinement Assignment Det"),
    displayConclusion = "x:=f;a <= x:=f;b <-> __[x:=f;](a <= b)__",
    displayLevel = DisplayLevel.Menu,
    key = "1", // key = "0" is refSeq
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refAnyMerge: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnyMerge",
    canonicalName = "refinement :* merge",
    displayName = Some("Refinement :* merge"),
    displayConclusion = "__ x:=*;?p(x);x:=* __ == x:=*;?(∃y p(y))",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Full,
  )
  @Derivation
  val refAnyAssignMerge: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnyAssignMerge",
    canonicalName = "refinement :=* merge",
    displayName = Some("Refinement :=* merge"),
    displayConclusion = "__ x:=*;?p(x);x:=f(x) __ == x:=*;?(∃y (p(y) ∧ x = f(y)))",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Full,
  )

  /** For the weaker version, see [[refUnloopWeak]] */
  @Derivation
  val refUnloop: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refUnloop",
    canonicalName = "refinement unloop",
    displayName = Some("Refinement unloop"),
    displayConclusion = "__a* <= b*__ <- [a*](a <= b)",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.SurjectiveLinear,
  )

  /* ODE refinement axioms */
  @Derivation
  val refDomainAx: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDomainAx",
    canonicalName = "refinement domain",
    displayLevel = DisplayLevel.Internal,
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )

  /** see generalisation: [[refOde]] */
  @Derivation
  val refOdeAx: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refOdeAx",
    canonicalName = "refinement ode",
    displayLevel = DisplayLevel.Internal,
    key = "0",
    unifier = Unifier.Surjective,
  )

  /** see generalisation: [[refOde]] */
  @Derivation
  val refOdesAx: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refOdesAx",
    canonicalName = "refinement ode (system)",
    displayLevel = DisplayLevel.Internal,
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refOdeIdemp: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refOdeIdemp",
    canonicalName = "ode idempotent",
    displayName = Some("Refinement ODE idempotent"),
    displayConclusion = "__{x' = f(x) & p(x)};{x' = f(x) & p(x)}__ == {x' = f(x) & p(x)}",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )

  /** see generalisation: [[refDE]] */
  @Derivation
  val refDEAx: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDEAx",
    canonicalName = "refinement DE",
    displayLevel = DisplayLevel.Internal,
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )

  /** see generalisation: [[refDE]] */
  val refDEsAx: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDEsAx",
    canonicalName = "refinement DE (system)",
    displayLevel = DisplayLevel.Internal,
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.SurjectiveLinear,
  )

  @Derivation
  val refDW: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDW",
    canonicalName = "refinement DW",
    displayName = Some("Refinement DW"),
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "__{c & P}__ == ?P;{c & P};?P",
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDX: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDX",
    canonicalName = "refinement DX",
    displayName = Some("Refinement DX"),
    displayConclusion = "x':=f(x);?p(x) <= {x' = f(x) & p(x)}",
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Full,
  )

  /* KAT axioms */
  @Derivation
  val refRefl: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refRefl",
    canonicalName = "refinement reflexive",
    displayName = Some("Refinement Reflexive"),
    displayConclusion = "a<=a",
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceId: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceId",
    canonicalName = "choice identity",
    displayName = Some("Choice Identity"),
    displayConclusion = "__a ∪ ?⊥__ == a",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceIdemp: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceIdemp",
    canonicalName = "choice idempotent",
    displayName = Some("Choice Idempotent"),
    displayConclusion = "__a ∪ a__ == a",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceComm: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceComm",
    canonicalName = "choice commute",
    displayName = Some("Choice Commutativity"),
    displayConclusion = "__a ∪ b__ == b ∪ a",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceAssoc: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceAssoc",
    canonicalName = "choice associative",
    displayName = Some("Choice Associativity"),
    displayConclusion = "a ∪ {b ∪ c} == __{a ∪ b} ∪ c__",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refSeqIdL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refSeqIdL",
    canonicalName = "sequence identity left",
    displayName = Some("Sequence Identity Left"),
    displayConclusion = "__?⊤;a__ == a",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refSeqIdR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refSeqIdR",
    canonicalName = "sequence identity right",
    displayName = Some("Sequence Identity Right"),
    displayConclusion = "__a;?⊤__ == a",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refSeqAssoc: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refSeqAssoc",
    canonicalName = "sequence associative",
    displayName = Some("Sequence Associativity"),
    displayConclusion = "a;{b;c} == __{a;b};c__",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDistrL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDistrL",
    canonicalName = "distribute left",
    displayName = Some("Distributivity Left"),
    displayConclusion = "a;b ∪ a;c == __a;{b ∪ c}__",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDistrR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDistrR",
    canonicalName = "distribute right",
    displayName = Some("Distributivity Right"),
    displayConclusion = "a;c ∪ b;c == __{a ∪ b};c__",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnnihL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnnihL",
    canonicalName = "annihile left",
    displayName = Some("Annihile Left"),
    displayConclusion = "__?⊥;a__ == a",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnnihR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnnihR",
    canonicalName = "annihile right",
    displayName = Some("Annihile Right"),
    displayConclusion = "__a;?⊥__ == a",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refUnfoldL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refUnfoldL",
    canonicalName = "unfold left",
    displayName = Some("Unfold Left"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refUnfoldR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refUnfoldR",
    canonicalName = "unfold right",
    displayName = Some("Unfold Right"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )

  /* Schematic-like KAT axioms */
  @Derivation
  val refAssignComm: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignComm",
    canonicalName = "assign commute",
    displayName = Some("Assign Commutativity"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Full,
  )
  @Derivation
  val refAssignSubst: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignSubst",
    canonicalName = "assign substitution",
    displayName = Some("Assign Substitution"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Full,
  )
  @Derivation
  val refAssignTest: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignTest",
    canonicalName = "assign test",
    displayName = Some("Assign Test Commutativity"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Full,
  )
  @Derivation
  val refAssignMerge: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignMerge",
    canonicalName = "assign merge",
    displayName = Some("Assign Merge"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnyComm: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnyComm",
    canonicalName = "nondet assign commute",
    displayName = Some("AssignAny Commutativity"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAssignAnyComm: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignAnyComm",
    canonicalName = ":=* commute",
    displayName = Some(":=* Commutativity"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnyTest: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnyTest",
    canonicalName = "nondet assign test",
    displayName = Some("AssignAny Test Commutativity"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Full,
  )

  // Congruence derived axioms
  // derived axioms used in CMonPrg (so useAt implicitely), thus given as Provables not lemmas, just in case to avoid dependencies
  // CMon seems to use lemmas just fine, so it may not be required

  lazy val congrChoiceL: ProvableSig = TactixLibrary.proveBy(
    "a{|^@|};<= b{|^@|}; -> a{|^@|};++c{|^@|};<= b{|^@|};++c{|^@|};".asFormula,
    useAt(refChoiceL)(1, 1 :: Nil) & useAt(refChoiceR)(1, 1 :: 1 :: Nil) & useAt(refChoiceR)(1, 1 :: 0 :: Nil) &
      useAt(refRefl)(1, 1 :: 1 :: 1 :: Nil) & prop,
  )

  lazy val congrChoiceR: ProvableSig = TactixLibrary.proveBy(
    "a{|^@|};<= b{|^@|}; -> c{|^@|};++a{|^@|};<= c{|^@|};++b{|^@|};".asFormula,
    useAt(refChoiceL)(1, 1 :: Nil) & useAt(refChoiceR)(1, 1 :: 1 :: Nil) & useAt(refChoiceR)(1, 1 :: 0 :: Nil) &
      useAt(refRefl)(1, 1 :: 0 :: 0 :: Nil) & prop,
  )

  lazy val congrSeqL: ProvableSig = TactixLibrary.proveBy(
    "a{|^@|};<= b{|^@|}; -> a{|^@|};c{|^@|};<= b{|^@|};c{|^@|};".asFormula,
    useAt(refSeq)(1, 1 :: Nil) & useAt(refRefl)(1, 1 :: 1 :: 1 :: Nil) & HilbertCalculus.boxTrue(1, 1 :: 1 :: Nil) &
      prop,
  )

  lazy val congrSeqR: ProvableSig = TactixLibrary.proveBy(
    "[c{|^@|};]a{|^@|};<= b{|^@|}; -> c{|^@|};a{|^@|};<= c{|^@|};b{|^@|};".asFormula,
    useAt(refSeq)(1, 1 :: Nil) & useAt(refRefl)(1, 1 :: 0 :: Nil) & prop,
  )

  lazy val congrODEDom: ProvableSig = TactixLibrary.proveBy(
    "[{c&p(||)}](p(||)->q(||))->{{c&p(||)}}<={{c&q(||)}}".asFormula,
    useAt(refDomainAx)(1, 1 :: Nil) & DW(1, 1 :: Nil) & implyR(1) & id,
  )

  val refEq: ProvableSig = TactixLibrary
    .proveBy("a{|^@|};<= b{|^@|}; <- a{|^@|};== b{|^@|};".asFormula, useAt(refAntiSym)(1, 0 :: Nil) & prop)

  val prgEqSym: ProvableSig = TactixLibrary.proveBy(
    "b{|^@|};== a{|^@|}; <- a{|^@|};== b{|^@|};".asFormula,
    useAt(refAntiSym)(1, 0 :: Nil) & useAt(refAntiSym)(1, 1 :: Nil) & prop,
  )

  /** derived axioms */
  // needed in CMon for monotonicity within diamond modalities, but this case does not appear in the proof, so no cycle
  @Derivation
  val refDiamond: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "refDiamond",
      canonicalName = "refinement diamond",
      displayName = Some("Ref Diamond"),
      displayConclusion = "a <= b -> __&langle;a&rangle;P -> &langle;b&rangle;P__",
      displayLevel = DisplayLevel.Menu,
      key = "1",
      unifier = Unifier.Surjective,
    ),
    "a{|^@|}; <= b{|^@|}; -> (<a{|^@|};>p(||) -> <b{|^@|};>p(||))".asFormula,
    diamondd(1, 1 :: 0 :: Nil) & diamondd(1, 1 :: 1 :: Nil) & useAt(converseImply, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
      useAt(refBox)(1, 1 :: Nil) & prop,
  )

  @Derivation
  val testSeq: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "testSeq",
      canonicalName = "test sequence",
      displayName = Some("Test Sequence"),
      displayConclusion = "__?p;?q__ == ?(p∧q)",
      displayLevel = DisplayLevel.Menu,
      key = "0",
      unifier = Unifier.SurjectiveLinear,
    ),
    "?p();?q(); == ?p()&q();".asFormula,
    useAt(refAntiSym)(1) & andR(1) & Idioms.<(
      useAt(refSeqIdL, PosInExpr(1 :: Nil))(1, 1 :: Nil) & useAt(refSeq)(1) & useAt(refTest)(1, 0 :: Nil) &
        useAt(refTest)(1, 1 :: 1 :: Nil) & useAt(testb)(1, 1 :: Nil) & prop,
      useAt(refSeqIdR, PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt(refSeq)(1) & useAt(refTest)(1, 0 :: Nil) &
        useAt(refTest)(1, 1 :: 1 :: Nil) & useAt(testb)(1, 1 :: Nil) & prop,
    ),
  )

  @Derivation
  val testChoice: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "testChoice",
      canonicalName = "test choice",
      displayName = Some("Test Choice"),
      displayConclusion = "__?p ∪ ?q__ == ?(p∨q)",
      displayLevel = DisplayLevel.Menu,
      key = "0",
      unifier = Unifier.SurjectiveLinear,
    ),
    "?p();++?q(); == ?p()|q();".asFormula,
    useAt(refAntiSym)(1) & andR(1) & Idioms.<(
      useAt(refChoiceL)(1) & andR(1) & OnAll(useAt(refTest)(1) & prop),
      useAt(refChoiceR)(1) & orR(1) & useAt(refTest)(1) & useAt(refTest)(2) & prop,
    ),
  )

  @Derivation
  val hideChoiceL: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "hideChoiceL",
      canonicalName = "hide choice left",
      displayConclusion = "b <= __a ∪ b__",
      displayLevel = DisplayLevel.Menu,
      key = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "b{|^@|}; <= a{|^@|};++b{|^@|};".asFormula,
    useAt(refChoiceR)(1, Nil) & useAt(refRefl)(1, 1 :: Nil) & prop,
  )

  @Derivation
  val hideChoiceR: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "hideChoiceR",
      canonicalName = "hide choice right",
      displayConclusion = "a <= __a ∪ b__",
      displayLevel = DisplayLevel.Menu,
      key = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "a{|^@|}; <= a{|^@|};++b{|^@|};".asFormula,
    useAt(refChoiceR)(1, Nil) & useAt(refRefl)(1, 0 :: Nil) & prop,
  )

  // Program equivalence version of some refinement axioms

  @Derivation
  val prgEqBox: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqBox",
      canonicalName = "program equivalence box",
      displayName = Some("Program Equivalence Box"),
      displayConclusion = "a == b -> __[a]P <-> [b]P__",
      displayLevel = DisplayLevel.Internal,
      key = "1",
      unifier = Unifier.Surjective,
    ),
    "a{|^@|}; == b{|^@|}; -> ([a{|^@|};]p(||) <-> [b{|^@|};]p(||))".asFormula,
    implyR(1) & useAt(refAntiSym)(-1) & equivR(1) &
      Idioms.<(implyRi()(-2, 1) & useAt(refBox)(1) & prop, implyRi()(-2, 1) & useAt(refBox)(1) & prop),
  )

  @Derivation
  val prgEqTest: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqTest",
      canonicalName = "program equivalence test",
      displayName = Some("Program Equivalence Test"),
      displayConclusion = "__?p == ?q__ <-> (p <-> q)",
      displayLevel = DisplayLevel.Internal,
      key = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "?p(); == ?q(); <-> (p() <-> q())".asFormula,
    useAt(refAntiSym)(1, 0 :: Nil) & useAt(refTest)(1, 0 :: 0 :: Nil) & useAt(refTest)(1, 0 :: 1 :: Nil) & prop,
  )
  @Derivation
  val prgEqSeq: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqSeq",
      canonicalName = "program equivalence sequence",
      displayName = Some("Program Equivalence Sequence"),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "__a;b == c;d__ <- a == c ∧ [a](b == d)",
      key = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "a{|^@|};b{|^@|}; == c{|^@|};d{|^@|}; <- (a{|^@|}; == c{|^@|}; & [a{|^@|};](b{|^@|}; == d{|^@|};))".asFormula,
    useAt(refAntiSym)(1, 1 :: Nil) & useAt(refAntiSym)(1, 0 :: 0 :: Nil) & useAt(refAntiSym)(1, 0 :: 1 :: 1 :: Nil) &
      useAt(boxAnd)(1, 0 :: 1 :: Nil) & useAt(refSeq)(1, 1 :: 0 :: Nil) & useAt(refSeq)(1, 1 :: 1 :: Nil) &
      SequentCalculus.cut("[a{|^@|};](d{|^@|}; <= b{|^@|};) -> [c{|^@|};](d{|^@|}; <= b{|^@|};)".asFormula) &
      Idioms.<(prop, useAt(refBox)(2) & prop),
  )

  @Derivation
  val prgEqRefl: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqRefl",
      canonicalName = "program equivalence reflexive",
      displayName = Some("Program Equivalence Reflexive"),
      displayLevel = DisplayLevel.Menu,
      displayConclusion = "a == a",
      key = "",
      unifier = Unifier.Surjective,
    ),
    "a{|^@|}; == a{|^@|};".asFormula,
    useAt(refAntiSym)(1) & useAt(refRefl)(1, 0 :: Nil) & useAt(refRefl)(1, 1 :: Nil) & prop,
  )

  @Derivation
  val prgEqTestDet: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqTestDet",
      canonicalName = "program equivalence test det",
      displayName = Some("Program Equivalence Test Det"),
      displayLevel = DisplayLevel.Internal,
      displayConclusion = "?p;a == ?p;b <-> __[?p](a == b)__",
      key = "1", // key = "0" is refSeq
      unifier = Unifier.SurjectiveLinear,
    ),
    "?p();a{|^@|}; == ?p();b{|^@|}; <-> [?p();](a{|^@|}; == b{|^@|};)".asFormula,
    useAt(refAntiSym)(1, 0 :: Nil) & useAt(refAntiSym)(1, 1 :: 1 :: Nil) & useAt(boxAnd)(1, 1 :: Nil) &
      useAt(refTestDet)(1, 1 :: 0 :: Nil) & useAt(refTestDet)(1, 1 :: 1 :: Nil) & prop,
  )

  @Derivation
  val prgEqAssignDet: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqAssignDet",
      canonicalName = "program equivalence assign det",
      displayName = Some("Program Equivalence Assignment Det"),
      displayConclusion = "x:=f;a == x:=f;b <-> __[x:=f;](a == b)__",
      displayLevel = DisplayLevel.Internal,
      key = "1", // key = "0" is refSeq
      unifier = Unifier.SurjectiveLinear,
    ),
    "x_:=f();a{|^@|}; == x_:=f();b{|^@|}; <-> [x_:=f();](a{|^@|}; == b{|^@|};)".asFormula,
    useAt(refAntiSym)(1, 0 :: Nil) & useAt(refAntiSym)(1, 1 :: 1 :: Nil) & useAt(boxAnd)(1, 1 :: Nil) &
      useAt(refAssignDet)(1, 1 :: 0 :: Nil) & useAt(refAssignDet)(1, 1 :: 1 :: Nil) & prop,
  )

  // Lazy as [[refUnloopWeak]] is initialised later in the current order
  @Derivation
  lazy val prgEqUnloop: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqUnloop",
      canonicalName = "program equivalence unloop",
      displayName = Some("Program Equivalence unloop"),
      displayConclusion = "__a* == b*__ <- [a*](a == b)",
      displayLevel = DisplayLevel.Internal,
      key = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "{a{|^@|};}* == {b{|^@|};}* <- [{a{|^@|};}*](a{|^@|}; == b{|^@|};)".asFormula,
    useAt(refAntiSym)(1, 1 :: Nil) & useAt(refAntiSym)(1, 0 :: 1 :: Nil) & useAt(boxAnd)(1, 0 :: Nil) &
      useAt(refUnloop)(1, 1 :: 0 :: Nil) & useAt(refUnloopWeak)(1, 1 :: 1 :: Nil) & prop,
  )

  @Derivation
  val prgEqDiamond: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqDiamond",
      canonicalName = "program equivalence diamond",
      displayName = Some("Program Equivalence Diamond"),
      displayConclusion = "a == b -> __&langle;a&rangle;P <-> &langle;b&rangle;P__",
      displayLevel = DisplayLevel.Internal,
      key = "1",
      unifier = Unifier.Surjective,
    ),
    "a{|^@|}; == b{|^@|}; -> (<a{|^@|};>p(||) <-> <b{|^@|};>p(||))".asFormula,
    diamondd(1, 1 :: 0 :: Nil) & diamondd(1, 1 :: 1 :: Nil) &
      useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1, 1 :: Nil) &
      useAt(prgEqBox)(1, 1 :: Nil) & prop,
  )

  /** see [[prgEqTrans]] */
  @Derivation
  val prgEqTransAx: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "prgEqTransAx",
      canonicalName = "program equivalence transitive",
      displayName = Some("Program Equivalence Transitive Ax"),
      displayConclusion = "__a == b ∧ b == c__ -> a == c",
      displayLevel = DisplayLevel.Menu,
      key = "0",
      unifier = Unifier.Surjective,
    ),
    "a{|^@|}; == c{|^@|}; & c{|^@|}; == b{|^@|}; -> a{|^@|}; == b{|^@|};".asFormula,
    useAt(refAntiSym)(1, 1 :: Nil) & useAt(refAntiSym)(1, 0 :: 0 :: Nil) & useAt(refAntiSym)(1, 0 :: 1 :: Nil) &
      refTrans("c{|^@|};".asProgram)(1, 1 :: 0 :: Nil) & refTrans("c{|^@|};".asProgram)(1, 1 :: 1 :: Nil) & prop,
  )

  /** Tactics generalising axioms (if schematic or if need additional inputs) */

  def refTrans(c: Expression): DependentPositionWithAppliedInputTactic = "refTrans".byWithInputs(
    List(c),
    (pos: Position, s: Sequent) =>
      c match {
        case c: Program =>
          assert(dualFree(c), "Refinement for games is not supported")
          val (a, b) = s.at(pos) match {
            case (_, Refinement(a, b)) => (a, b)
            case (_, f) => throw new TacticInapplicableFailure(f.toString + " should be a refinement")
          }
          useAt(
            ProvableSig.axioms("refinement transitive")(USubst(
              SubstitutionPair(SystemConst("a"), a) :: SubstitutionPair(SystemConst("b"), b) ::
                SubstitutionPair(SystemConst("c"), c) :: Nil
            )),
            PosInExpr(1 :: Nil),
          )(pos)
        case _ => throw new TacticInapplicableFailure(c.toString + " should be a program")
      },
  )

  @Derivation
  val refTransInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "refTrans",
    displayNameLong = Some("Refinement Transitivity"),
    displayPremises = "Γ |- C(a <= c), Δ ;; Γ |- C(c <= b), Δ",
    displayConclusion = "Γ |- C(a <= b), Δ",
    displayLevel = DisplayLevel.Menu,
    constructor = TacticConstructor1.create(ExpressionArg("c"))(refTrans),
  )

  def prgEqTrans(c: Expression): DependentPositionWithAppliedInputTactic = "prgEqTrans".byWithInputs(
    List(c),
    (pos: Position, s: Sequent) =>
      c match {
        case c: Program =>
          assert(dualFree(c), "Refinement for games is not supported")
          val (a, b) = s.at(pos) match {
            case (_, ProgramEquivalence(a, b)) => (a, b)
            case (_, f) => throw new TacticInapplicableFailure(f.toString + " should be a program equivalence")
          }
          useAt(
            prgEqTransAx.provable(USubst(
              SubstitutionPair(SystemConst("a"), a) :: SubstitutionPair(SystemConst("b"), b) ::
                SubstitutionPair(SystemConst("c"), c) :: Nil
            )),
            PosInExpr(1 :: Nil),
          )(pos)
        case _ => throw new TacticInapplicableFailure(c.toString + " should be a program")
      },
  )

  @Derivation
  val prgEqTransInfo: InputPositionTacticInfo = InputPositionTacticInfo.create(
    name = "prgEqTrans",
    displayNameLong = Some("Program Equivalence Transitivity"),
    displayPremises = "Γ |- C(a == c), Δ ;; Γ |- C(c == b), Δ",
    displayConclusion = "Γ |- C(a == b), Δ",
    displayLevel = DisplayLevel.Menu,
    constructor = TacticConstructor1.create(ExpressionArg("c"))(prgEqTrans),
  )

  private lazy val refOdeIndStepAux = TactixLibrary.proveBy(
    "b{|^@|};==a{|^@|}; & [b{|^@|};]p(||) -> b{|^@|};==a{|^@|}; & [a{|^@|};]p(||)".asFormula,
    implyR(1) & andR(1) &
      Idioms.<(prop, andL(-1) & useAt(prgEqSym)(-1) & useAt(refEq)(-1) & useAt(refBox, PosInExpr(0 :: Nil))(-1) & prop),
  )

  def refOde: DependentPositionTactic = "refOde".by { (pos: Position, s: Sequent) =>
    s.at(pos) match {
      case (_, prgEq @ ProgramEquivalence(ODESystem(c, p), ODESystem(d, q))) =>
        if (p != q) { throw new TacticInapplicableFailure(s"Expected identical domain, but got: $p and $q") }

        def odesToFml(dp: DifferentialProgram, dp2: DifferentialProgram): (Formula, Boolean) = {
          (dp, dp2) match {
            case (AtomicODE(xp, t), AtomicODE(xp2, t2)) if xp == xp2 => (Equal(t, t2), true)
            case (DifferentialProduct(c1, d1), DifferentialProduct(c2, d2)) =>
              (And(odesToFml(c1, c2)._1, odesToFml(d1, d2)._1), false)
            case (_: DifferentialProgramConst, _) | (DotDiffProgram, _) | (_, _: DifferentialProgramConst) |
                (_, DotDiffProgram) =>
              throw new TacticInapplicableFailure(s"Expected explicit ODEs, but got: $c and $d")
            case (_: DifferentialProduct, _) | (_, _: DifferentialProduct) =>
              throw new TacticInapplicableFailure(s"ODEs do not have compatible shape: $c and $d")
            case (AtomicODE(xp, _), AtomicODE(xp2, _)) =>
              throw new TacticInapplicableFailure(s"ODEs do not have compatible variables: $xp and $xp2")
          }
        }

        val (postCond, uniDim) = odesToFml(c, d)

        if (uniDim) {
          // Recover bound variable to rename before unifier (unifier misses that domains are bound by odes)
          val x = StaticSemantics.boundVars(c).symbols.filter(_.isInstanceOf[BaseVariable]).head
          // Unidimensional ODE is just the axiom
          useAt(refOdeAx.provable.apply(URename("x_".asVariable, x, semantic = true)))(pos)
        } else {
          val listC = atomicOdes(c)
          val listD = atomicOdes(d)
          // List of intermediate dp: one step is going from (drpg._1,drpg._2) to (drpg._2, drpg._3)
          val dprgs = (listC ++ listD)
            .sliding(listC.length + 1)
            .map(odes => (odes.head, ofAtoms(odes.tail.init), odes.last))
            .toList

          def refOdesRec(dprgs: List[(AtomicODE, DifferentialProgram, AtomicODE)], pos: Position): BelleExpr = {
            dprgs match {
              case (AtomicODE(DifferentialSymbol(x), t), dp, AtomicODE(_, t2)) :: Nil =>
                // Matching can fail due to reassociativity, so specify substitution manually
                useAt(
                  refOdesAx
                    .provable
                    .apply(URename("x_".asVariable, x, semantic = true))
                    .apply(USubst(List(
                      SubstitutionPair("f(||)".asTerm, t),
                      SubstitutionPair("g(||)".asTerm, t2),
                      SubstitutionPair("p(||)".asFormula, p),
                      SubstitutionPair("c".asDifferentialProgram, dp),
                    )))
                )(pos)
              case (AtomicODE(DifferentialSymbol(x), t), dp, atomRight @ AtomicODE(_, t2)) :: tail =>
                prgEqTrans(ODESystem(DifferentialProduct(dp, atomRight), p))(pos) &
                  refOdesRec(tail, pos ++ PosInExpr(1 :: Nil)) & useAt(refOdeIndStepAux, PosInExpr(1 :: Nil))(pos) &
                  // Matching can fail due to reassociativity, so specify substitution manually
                  useAt(
                    refOdesAx
                      .provable
                      .apply(URename("x_".asVariable, x, semantic = true))
                      .apply(USubst(List(
                        SubstitutionPair("f(||)".asTerm, t),
                        SubstitutionPair("g(||)".asTerm, t2),
                        SubstitutionPair("p(||)".asFormula, p),
                        SubstitutionPair("c".asDifferentialProgram, dp),
                      )))
                  )(pos ++ PosInExpr(0 :: Nil)) & useAt(boxAnd, PosInExpr(1 :: Nil))(pos)
              case Nil => throw new TacticAssertionError(
                  "No intermediate odes where found. I should have been caught in odesToFml."
                )
            }
          }

          // Proving schematic `[x'=f(x) & p(x)](f(x) = g(x)) -> {x'=f(x) & p(x)} == {x'=g(x) & p(x)}`
          val pr = TactixLibrary.proveBy(
            Imply(Box(ODESystem(c, p), postCond), prgEq),
            { refOdesRec(dprgs, Position(1, 1 :: Nil)) & implyR(1) & id },
          )
          assert(pr.isProved, s"refOde failed to prove the specialised instance: ${pr.conclusion}")

          useAt(pr, PosInExpr(1 :: Nil))(pos)
        }
      case (_, f) => throw new TacticInapplicableFailure(s"Expected equivalence of ODE, but got: $f")
    }
  }

  @Derivation
  def refOdeInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "refOde",
    displayNameLong = Some("Refinement ODE"),
    displayPremises = "Γ |- [x'=f(x) & p(x)](f(x) = g(x)), Δ",
    displayConclusion = "Γ |- {x'=f(x) & p(x)} == {x'=g(x) & p(x)}, Δ",
    constructor = TacticConstructor0.create()(() => refOde),
  )

  def refDE: DependentPositionTactic = "refDE".by { (pos: Position, s: Sequent) =>
    s.at(pos) match {
      case (_, ODESystem(AtomicODE(DifferentialSymbol(x), _), _)) =>
        // Manually rename: unifier misses that domains are bound by odes
        useAt(refDEAx.provable.apply(URename("x_".asVariable, x, semantic = true)))(pos)
      case (_, ODESystem(c, _)) =>
        val odeDim = StaticSemantics.boundVars(c).symbols.count(_.isInstanceOf[DifferentialSymbol])
        useAt(refDEsAx)(pos) & (useAt(refDEsAx)(pos ++ PosInExpr(0 :: Nil)) & useAt(refSeqAssoc)(pos)) * (odeDim - 1)

      case (_, f) => throw new TacticInapplicableFailure(s"Expected equivalence of ODE, but got: $f")
    }
  }

  @Derivation
  def refDEinfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "refDE",
    displayNameLong = Some("Refinement DE"),
    displayConclusion = "__{x' = f(x) & p(x)}__ == {x' = f(x) & p(x)};x':=f(x)",
    constructor = TacticConstructor0.create()(() => refDE),
  )

  private[btactics] def CPrgEimpFw(inEqPos: PosInExpr, reverse: Boolean): BuiltInTactic =
    anon { (provable: ProvableSig) =>
      require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

      val sequent = provable.subgoals.head
      require(
        sequent.ante.isEmpty && sequent.succ.length == 1,
        "Expected empty antecedent and single succedent formula, but got " + sequent,
      )
      sequent.succ.head match {
        case Imply(l, r) =>
          val provableEquiv = if (reverse) provable(equivifyR(1), 0)(commuteEquivR(1), 0) else provable(equivifyR(1), 0)
          if (inEqPos == HereP) { provableEquiv }
          else {
            val (ctxP, a: Program) = l.at(inEqPos)
            val (ctxQ, b: Program) = r.at(inEqPos)
            // @note Could skip the construction of ctxQ but it's part of the .at construction anyway.
            require(ctxP == ctxQ, "Same context expected, but got " + ctxP + " and " + ctxQ)
            Predef
              .assert(ctxP.ctx == ctxQ.ctx, "Same context formula expected, but got " + ctxP.ctx + " and " + ctxQ.ctx)
            Predef.assert(ctxP.isProgramContext, "Program context expected for CPrgE")
            val finalEquiv = if (reverse) ProgramEquivalence(b, a) else ProgramEquivalence(a, b)
            provableEquiv(UnifyUSCalculus.CE(ctxP)(ProvableSig.startPlainProof(finalEquiv)), 0)
          }
        case fml => throw new TacticInapplicableFailure("Expected implication, but got " + fml)
      }
    }

  @Derivation
  val skipRandom: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "skipRandom",
      canonicalName = "skip random",
      displayName = Some("Skip Random"),
      displayConclusion = "?⊤ <= __x:=*__",
      displayLevel = DisplayLevel.Menu,
      key = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "?true; <= x:=*;".asFormula,
    refTrans("x:=x;".asProgram)(1) & andR(1) & Idioms.<(
      useAt(refStutter)(1, 1 :: Nil) & useAt(refRefl)(1),
      discreteGhost(Variable("x"), None)(1) & useAt(refAssign)(1, 0 :: Nil) &
        useAt(refSeqIdR, PosInExpr(1 :: Nil))(1, 1 :: Nil) & CMon(1, 0 :: 1 :: 0 :: Nil) & prop,
    ),
  )

  @Derivation
  val doubleLoop: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "doubleLoop",
      canonicalName = "double loop",
      displayName = Some("Double Loop"),
      displayConclusion = "__a**__ <= a*",
      displayLevel = DisplayLevel.Menu,
      key = "0",
      unifier = Unifier.SurjectiveLinear,
    ),
    "{{a{|^@|};}*}* <= {a{|^@|};}*".asFormula,
    useAt(refUnfoldL, PosInExpr(1 :: Nil))(1, 0 :: Nil) & useAt(refChoiceL)(1) & andR(1) & Idioms.<(
      useAt(refUnfoldL, PosInExpr(1 :: Nil))(1, 1 :: Nil) & useAt(hideChoiceR)(1, 1 :: Nil) & useAt(refRefl)(1),
      useAt(refLoopR)(1) & useAt(refLoopR)(1) & useAt(refUnfoldR, PosInExpr(1 :: Nil))(1, 1 :: Nil) &
        useAt(hideChoiceL)(1, 1 :: Nil) & useAt(refRefl)(1),
    ),
  )

  /**
   * Similar to [[refUnloop]] but uses the "bigger" program for the modalities Generally simpler to use if we know more
   * about the "bigger" program, e.g. event-/time-triggered refinements
   */
  @Derivation
  val refUnloopWeak: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "refUnloopWeak",
      canonicalName = "refinement unloop weak",
      displayName = Some("Refinement unloop weak"),
      displayConclusion = "__a* <= b*__ <- [b*](a <= b)",
      displayLevel = DisplayLevel.Menu,
      key = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "[{b{|^@|};}*]a{|^@|}; <= b{|^@|}; -> {{a{|^@|};}*} <= {{b{|^@|};}*}".asFormula,
    implyR(1) & refTrans("{b{|^@|};}*{a{|^@|};}*".asProgram)(1) & andR(1) & Idioms.<(
      useAt(refUnfoldL, PosInExpr(1 :: Nil))(1, 1 :: 0 :: Nil) & useAt(hideChoiceR)(1, 1 :: 0 :: Nil) &
        useAt(refSeqIdL)(1, 1 :: Nil) & cohide(1) & useAt(refRefl)(1),
      useAt(refLoopR)(1) & useAt(refUnfoldR, PosInExpr(1 :: Nil))(1, 1 :: Nil) & useAt(hideChoiceL)(1, 1 :: Nil) &
        useAt(refSeq)(1) & useAt(refRefl)(1, 0 :: Nil) & prop,
    ),
  )

}
