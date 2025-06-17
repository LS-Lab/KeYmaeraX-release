/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{
  BelleExpr,
  BuiltInRightTactic,
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
import org.keymaerax.btactics.SequentCalculus.{andL, andR, cohide, commuteEquivR, equivifyR, id, implyR, orR}
import org.keymaerax.btactics.TacticFactory.{anon, TacticForNameFactory}
import org.keymaerax.btactics.TactixLibrary.prop
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
import org.keymaerax.core.StaticSemantics.symbols
import org.keymaerax.core.*
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.Augmentors.{FormulaAugmentor, ProgramAugmentor, SequentAugmentor}
import org.keymaerax.infrastruct.FormulaTools.dualFree
import org.keymaerax.infrastruct.PosInExpr.HereP
import org.keymaerax.infrastruct.{Context, PosInExpr, Position, SuccPosition}
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
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAssignDet: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignDet",
    canonicalName = "refinement assign det",
    displayName = Some("Refinement Assignment Det"),
    displayConclusion = "x:=f;a <= x:=f;b <-> __[x:=f;](a <= b)__",
    displayLevel = DisplayLevel.Menu,
    key = "1", // key = "0" is refSeq
    unifier = Unifier.Surjective,
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
    displayConclusion = "__{x' = f(x) & p(x)};{x' = f(x) & p(x)}__ <= {x' = f(x) & p(x)}",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDE: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDE",
    canonicalName = "refinement DE",
    displayName = Some("Refinement DE"),
    displayConclusion = "__{x' = F,c & P}__ == {x' = F,c & P};x':=F",
    displayLevel = DisplayLevel.Menu,
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
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

  /**
   * focus(pos) pushes a *top-level* refinement down to the indicated position
   *
   * {{{
   *   G |- C'{a; <= b;}, D
   *   ----------------------
   *   G |- C{a;} <= C{b;}, D
   * }}}
   *
   * The context `C` can represent an arbitrary program. The resulting context `C'` is computed from `C` and mostly of
   * the form `[a_1][a_2]...[a_n] _`
   *
   * @note
   *   `pos` can refer to the position of either `a` or `b` in the sequent.
   */
  def focus: BuiltInRightTactic = "focus".by { (provable: ProvableSig, pos: SuccPosition) =>
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)
    val sequent = provable.subgoals.head
    val inEqPos = pos.inExpr.child
    sequent(pos.top) match {
      case Refinement(a, b) =>
        val (ctxA, e) = a.at(inEqPos)
        val (ctxB, _) = b.at(inEqPos)
        val dot = e match {
          case _: Formula => DotFormula
          case _: Program => DotProgram
          case _ => throw new TacticInapplicableFailure("Expected formula or program, but got " + e)
        }
        require(ctxA == ctxB, "Same context expected, but got " + ctxA + " and " + ctxB)
        Predef.assert(ctxA.ctx == ctxB.ctx, "Same context formula expected, but got " + ctxA.ctx + " and " + ctxB.ctx)
        provable(focusFW(ctxA, pos.topLevel, dot), 0)
      case f => throw new TacticInapplicableFailure("Expected refinement, but got " + f)
    }
  }

  @Derivation
  def focusInfo: PositionTacticInfo = PositionTacticInfo.create(
    name = "focus",
    displayPremises = "C'(a<=b)",
    displayConclusion = "C{a}<=C{b}",
    constructor = TacticConstructor0.create()(() => focus),
  )

  private[btactics] def focusFW(ctx: Context[Program], pos: Position, dot: NamedSymbol): BuiltInTactic =
    anon { (provable: ProvableSig) =>
      ctx.ctx match {
        case DotProgram => provable
        case Test(_) => provable(useAt(refTest)(pos), 0)
        case Choice(c, a) if !symbols(a).contains(dot) =>
          provable(useAt(congrChoiceL, PosInExpr(1 :: Nil))(pos), 0)(focusFW(Context(c), pos, dot), 0)
        case Choice(a, c) if !symbols(a).contains(dot) =>
          provable(useAt(congrChoiceR, PosInExpr(1 :: Nil))(pos), 0)(focusFW(Context(c), pos, dot), 0)
        case Compose(c, a) if !symbols(a).contains(dot) =>
          provable(useAt(congrSeqL, PosInExpr(1 :: Nil))(pos), 0)(focusFW(Context(c), pos, dot), 0)
        case Compose(a, c) if !symbols(a).contains(dot) =>
          provable(useAt(congrSeqR, PosInExpr(1 :: Nil))(pos), 0)(
            focusFW(Context(c), pos ++ PosInExpr(1 :: Nil), dot),
            0,
          )
        case Loop(c) => provable(useAt(refUnloop, PosInExpr(1 :: Nil))(pos), 0)(
            focusFW(Context(c), pos ++ PosInExpr(1 :: Nil), dot),
            0,
          )
        case ODESystem(ode, _) if !symbols(ode).contains(dot) =>
          provable(useAt(congrODEDom, PosInExpr(1 :: Nil))(pos), 0)

        case Dual(_) => throw new TacticInapplicableFailure("Not implemented for games")
        case Assign(_, _) | ODESystem(_, _) =>
          throw new TacticInapplicableFailure("Focus down to Terms not implemented.")
        case Choice(_, _) | Compose(_, _) => throw new TacticAssertionError(
            s"Context should contain only one ${dot.getClass.getSimpleName}, but is ${ctx}"
          )
        case AssignAny(_) | ProgramConst(_, _) | SystemConst(_, _) =>
          throw new TacticAssertionError(s"Proper contexts have dots somewhere ${ctx}")
        case _: DifferentialProgram => throw new TacticAssertionError("Expected non-differential program context")
      }
    }
}
