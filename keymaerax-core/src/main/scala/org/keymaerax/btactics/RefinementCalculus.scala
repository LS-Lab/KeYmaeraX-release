/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{DependentPositionWithAppliedInputTactic, TacticInapplicableFailure}
import org.keymaerax.btactics.Ax.*
import org.keymaerax.btactics.HilbertCalculus.diamondd
import org.keymaerax.btactics.TacticFactory.TacticForNameFactory
import org.keymaerax.btactics.TactixLibrary.prop
import org.keymaerax.btactics.UnifyUSCalculus.useAt
import org.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import org.keymaerax.btactics.macros.{
  CoreAxiomInfo,
  DerivedAxiomInfo,
  DisplayLevel,
  ExpressionArg,
  InputPositionTacticInfo,
  TacticConstructor1,
  Unifier,
}
import org.keymaerax.core.*
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.infrastruct.FormulaTools.dualFree
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
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refAssign: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssign",
    canonicalName = "refinement assign",
    displayName = Some("Refinement Assign"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Full,
  )
  @Derivation
  val refStutter: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refStutter",
    canonicalName = "refinement stutter",
    displayName = Some("Refinement Stutter"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceL",
    canonicalName = "refinement choice left",
    displayName = Some("Refinement Choice Left"),
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refChoiceR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceR",
    canonicalName = "refinement choice right",
    displayName = Some("Refinement Choice Right"),
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
    key = "1",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refLoopL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refLoopL",
    canonicalName = "refinement loop left",
    displayName = Some("Refinement Loop Left"),
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refLoopR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refLoopR",
    canonicalName = "refinement loop right",
    displayName = Some("Refinement Loop Right"),
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
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAssignDet: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignDet",
    canonicalName = "refinement assign det",
    displayName = Some("Refinement Assignment Det"),
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnyMerge: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnyMerge",
    canonicalName = "refinement :* merge",
    displayName = Some("Refinement :* merge"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Full,
  )
  @Derivation
  val refAnyAssignMerge: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnyAssignMerge",
    canonicalName = "refinement :=* merge",
    displayName = Some("Refinement :=* merge"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Full,
  )
  @Derivation
  val refUnloop: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refUnloop",
    canonicalName = "refinement unloop",
    displayName = Some("Refinement unloop"),
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.SurjectiveLinear,
  )

  /* ODE refinement axioms */
  @Derivation
  val refOde: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refOde",
    canonicalName = "refinement ode",
    displayName = Some("Refinement ODE"),
    displayLevel = DisplayLevel.Menu,
    key = "0",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refOdeIdemp: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refOdeIdemp",
    canonicalName = "ode idempotent",
    displayName = Some("Refinement ODE idempotent"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDE: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDE",
    canonicalName = "refinement DE",
    displayName = Some("Refinement DE"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDW: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDW",
    canonicalName = "refinement DW",
    displayName = Some("Refinement DW"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    // Technically not surjective as ODE invariant prevents US to substitute differentials in ODE
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDX: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDX",
    canonicalName = "refinement DX",
    displayName = Some("Refinement DX"),
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
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceIdemp: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceIdemp",
    canonicalName = "choice idempotent",
    displayName = Some("Choice Idempotent"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceComm: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceComm",
    canonicalName = "choice commute",
    displayName = Some("Choice Commutativity"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceAssoc: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceAssoc",
    canonicalName = "choice associative",
    displayName = Some("Choice Associativity"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refSeqIdL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refSeqIdL",
    canonicalName = "sequence identity left",
    displayName = Some("Sequence Identity Left"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refSeqIdR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refSeqIdR",
    canonicalName = "sequence identity right",
    displayName = Some("Sequence Identity Right"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refSeqAssoc: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refSeqAssoc",
    canonicalName = "sequence associative",
    displayName = Some("Sequence Associativity"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDistrL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDistrL",
    canonicalName = "distribute left",
    displayName = Some("Distributivity Left"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refDistrR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refDistrR",
    canonicalName = "distribute right",
    displayName = Some("Distributivity Right"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnnihL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnnihL",
    canonicalName = "annihile left",
    displayName = Some("Annihile Left"),
    displayConclusion = "__?⊥;a__ == a",
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnnihR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnnihR",
    canonicalName = "annihile right",
    displayName = Some("Annihile Right"),
    displayConclusion = "__a;?⊥__ == a",
    displayLevel = DisplayLevel.Menu,
    key = "",
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
  val hideChoiceL: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "hideChoiceL",
      canonicalName = "hide choice left",
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

}
