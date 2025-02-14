/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{BuiltInRightTactic, BuiltInTactic, DependentPositionWithAppliedInputTactic, OnAll, TacticInapplicableFailure}
import org.keymaerax.btactics.Ax._
import org.keymaerax.btactics.DLBySubst.discreteGhost
import org.keymaerax.btactics.Derive.CMon
import org.keymaerax.btactics.SequentCalculus.commuteEquivR
import org.keymaerax.btactics.SimplifierV3.simplify
import org.keymaerax.btactics.TacticFactory.{anon, inputanon}
import org.keymaerax.btactics.TactixLibrary.{DW, G, andR, equivifyR, id, implyL, implyR, orR, prop, useAt}
import org.keymaerax.btactics.macros.{CoreAxiomInfo, DerivedAxiomInfo, DisplayLevel, Tactic, Unifier}
import org.keymaerax.core.StaticSemantics.symbols
import org.keymaerax.core._
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.infrastruct.Augmentors.{FormulaAugmentor, ProgramAugmentor, SequentAugmentor}
import org.keymaerax.infrastruct.FormulaTools.dualFree
import org.keymaerax.infrastruct.PosInExpr.HereP
import org.keymaerax.infrastruct.{Context, PosInExpr, Position, SuccPosition}
import org.keymaerax.parser.StringConverter.StringToStringConverter
import org.keymaerax.pt.ProvableSig

import scala.annotation.nowarn
import scala.reflect.runtime.universe

@nowarn("msg=Exhaustivity analysis reached max recursion depth") @nowarn("msg=match may not be exhaustive")
object RefinementCalculus extends TacticProvider {
  override def getInfo: (Class[_], universe.Type) =
    (RefinementCalculus.getClass, universe.typeOf[RefinementCalculus.type])

  /** Refinement axioms */
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
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Full,
  )
  @Derivation
  val refStutter: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refStutter",
    canonicalName = "refinement stutter",
    displayName = Some("Refinement Stutter"),
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
    key = "1",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAssignDet: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAssignDet",
    canonicalName = "refinement assign det",
    displayName = Some("Refinement Assignment Det"),
    displayConclusion = "x:=f;a <= x:=f;b <-> __[x:=f;](a <= b)__",
    displayLevel = DisplayLevel.Menu,
    key = "1",
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
    displayConclusion = "__a* <= b*__ <- [a*](a <= b)",
    displayLevel = DisplayLevel.Menu,
    key = "1",
    unifier = Unifier.SurjectiveLinear,
  )

  /* ODE refinement axioms */
  @Derivation
  val refOde: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refOde",
    canonicalName = "refinement ode",
    displayLevel = DisplayLevel.Menu,
    displayConclusion = "__{x' = f(x) & p(x)} <= {x' = g(x) & q(x)}__ <-> [{x' = f(x) & p(x)}](f(x) = g(x) ∧ q(x))",
    key = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refOdes: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refOdes",
    canonicalName = "refinement ode (system)",
    displayName = Some("Refinement ODE"),
    displayConclusion = "__{x' = F,c & P} <= {x' = G,c & Q}__ <-> [{x' = F,c & P}](F = G ∧ Q)",
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
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceComm: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceComm",
    canonicalName = "choice commute",
    displayName = Some("Choice Commutativity"),
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refChoiceAssoc: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refChoiceAssoc",
    canonicalName = "choice associative",
    displayName = Some("Choice Associativity"),
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
    displayConclusion = "a;{b;c} == {a;b};c",
    displayLevel = DisplayLevel.Menu,
    key = "",
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
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnnihL: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnnihL",
    canonicalName = "annihilation left",
    displayName = Some("Annihilation Left"),
    displayLevel = DisplayLevel.Menu,
    key = "",
    unifier = Unifier.Surjective,
  )
  @Derivation
  val refAnnihR: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refAnnihR",
    canonicalName = "annihilation right",
    displayName = Some("Annihilation Right"),
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

  @Tactic(
    name = "refTrans",
    displayNameLong = Some("Refinement Transitivity"),
    displayPremises = "Γ |- C(a <= c), Δ ;; Γ |- C(c <= b), Δ",
    displayConclusion = "Γ |- C(a <= b), Δ",
    revealInternalSteps = true,
    inputs = "c:expression",
    displayLevel = DisplayLevel.Menu,
  )
  def refTrans(c: Expression): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, s: Sequent) =>
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
    }
  }

  /** derived axioms */
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
    useAt(diamond, PosInExpr(1 :: Nil))(Position(1, 1 :: 0 :: Nil)) &
      useAt(diamond, PosInExpr(1 :: Nil))(Position(1, 1 :: 1 :: Nil)) &
      useAt(converseImply, PosInExpr(1 :: Nil))(Position(1, 1 :: Nil)) & useAt(refBox)(Position(1, 1 :: Nil)) & prop,
  )

  @Derivation
  val testSeq: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "testSeq",
      canonicalName = "test sequence",
      displayName = Some("Test Sequence"),
      displayLevel = DisplayLevel.Menu,
      key = "0",
      unifier = Unifier.SurjectiveLinear,
    ),
    "?p();?q(); == ?p()&q();".asFormula,
    useAt(refAntiSym)(1) & andR(1) & Idioms.<(
      useAt(refSeqIdL, PosInExpr(1 :: Nil))(Position(1, 1 :: Nil)) & useAt(refSeq)(1) &
        useAt(refTest)(Position(1, 0 :: Nil)) & useAt(refTest)(Position(1, 1 :: 1 :: Nil)) &
        useAt(testb)(Position(1, 1 :: Nil)) & prop,
      useAt(refSeqIdR, PosInExpr(1 :: Nil))(Position(1, 0 :: Nil)) & useAt(refSeq)(1) &
        useAt(refTest)(Position(1, 0 :: Nil)) & useAt(refTest)(Position(1, 1 :: 1 :: Nil)) &
        useAt(testb)(Position(1, 1 :: Nil)) & prop,
    ),
  )

  @Derivation
  val testChoice: DerivedAxiomInfo = derivedFormula(
    DerivedAxiomInfo.create(
      name = "testChoice",
      canonicalName = "test choice",
      displayName = Some("Test Choice"),
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
      displayLevel = DisplayLevel.Menu,
      key = "1",
      unifier = Unifier.SurjectiveLinear,
    ),
    "b{|^@|}; <= a{|^@|};++b{|^@|};".asFormula,
    useAt(refChoiceR)(Position(1, Nil)) & useAt(refRefl)(Position(1, 1 :: Nil)) & prop,
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
    useAt(refChoiceR)(Position(1, Nil)) & useAt(refRefl)(Position(1, 0 :: Nil)) & prop,
  )

  val refEq: ProvableSig = TactixLibrary
    .proveBy("a{|^@|};<= b{|^@|}; <- a{|^@|};== b{|^@|};".asFormula, useAt(refAntiSym)(Position(1, 0 :: Nil)) & prop)

  val prgEqSym: ProvableSig = TactixLibrary.proveBy(
    "b{|^@|};== a{|^@|}; <- a{|^@|};== b{|^@|};".asFormula,
    useAt(refAntiSym)(Position(1, 0 :: Nil)) & useAt(refAntiSym)(Position(1, 1 :: Nil)) & prop,
  )
  // Congruence derived axioms
  // derived axioms used in CMonPrg (so useAt implicitely), thus given as Provables not lemmas, just in case to avoid dependencies
  // CMon seems to use lemmas just fine, so it may not be required

  lazy val congrChoiceL: ProvableSig = TactixLibrary.proveBy(
    "a{|^@|};<= b{|^@|}; -> a{|^@|};++c{|^@|};<= b{|^@|};++c{|^@|};".asFormula,
    useAt(refChoiceL)(Position(1, 1 :: Nil)) & useAt(refChoiceR)(Position(1, 1 :: 1 :: Nil)) &
      useAt(refChoiceR)(Position(1, 1 :: 0 :: Nil)) & useAt(refRefl)(Position(1, 1 :: 1 :: 1 :: Nil)) & prop,
  )

  lazy val congrChoiceR: ProvableSig = TactixLibrary.proveBy(
    "a{|^@|};<= b{|^@|}; -> c{|^@|};++a{|^@|};<= c{|^@|};++b{|^@|};".asFormula,
    useAt(refChoiceL)(Position(1, 1 :: Nil)) & useAt(refChoiceR)(Position(1, 1 :: 1 :: Nil)) &
      useAt(refChoiceR)(Position(1, 1 :: 0 :: Nil)) & useAt(refRefl)(Position(1, 1 :: 0 :: 0 :: Nil)) & prop,
  )

  lazy val congrSeqL: ProvableSig = TactixLibrary.proveBy(
    "a{|^@|};<= b{|^@|}; -> a{|^@|};c{|^@|};<= b{|^@|};c{|^@|};".asFormula,
    useAt(refSeq)(Position(1, 1 :: Nil)) & useAt(refRefl)(Position(1, 1 :: 1 :: 1 :: Nil)) &
      TactixLibrary.boxTrue(Position(1, 1 :: 1 :: Nil)) & prop,
  )

  lazy val congrSeqR: ProvableSig = TactixLibrary.proveBy(
    "[c{|^@|};]a{|^@|};<= b{|^@|}; -> c{|^@|};a{|^@|};<= c{|^@|};b{|^@|};".asFormula,
    useAt(refSeq)(Position(1, 1 :: Nil)) & useAt(refRefl)(Position(1, 1 :: 0 :: Nil)) & prop,
  )

  lazy val congrODEDom: ProvableSig = TactixLibrary.proveBy(
    "[{x'=f(x)&p(x)}](p(x)->q(x))->{{x'=f(x)&p(x)}}<={{x'=f(x)&q(x)}}".asFormula,
    useAt(refOde)(Position(1, 1 :: Nil)) & useAt(K, PosInExpr(0 :: Nil))(Position(1, 0 :: Nil)) & implyR(Position(1)) &
      implyL(Position(-1)) < (DW(2) & G(2) & prop, simplify(Position(1, 1 :: Nil)) & id),
  )

  lazy val congrODEDoms: ProvableSig = TactixLibrary.proveBy(
    "[{x'=f(||),c&p(||)}](p(||)->q(||))->{{x'=f(||),c&p(||)}}<={{x'=f(||),c&q(||)}}".asFormula,
    useAt(refOdes)(Position(1, 1 :: Nil)) & useAt(K, PosInExpr(0 :: Nil))(Position(1, 0 :: Nil)) & implyR(Position(1)) &
      implyL(Position(-1)) < (DW(2) & G(2) & prop, simplify(Position(1, 1 :: Nil)) & id),
  )

  private[btactics] def CPrgEimpFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent formula, but got " + sequent,
    )
    sequent.succ.head match {
      case Imply(l, r) =>
        if (inEqPos == HereP) equivifyR(1).computeResult(provable)
        else {
          val (ctxP, a: Program) = l.at(inEqPos)
          val (ctxQ, b: Program) = r.at(inEqPos)
          // @note Could skip the construction of ctxQ but it's part of the .at construction anyways.
          require(ctxP == ctxQ, "Same context expected, but got " + ctxP + " and " + ctxQ)
          Predef.assert(ctxP.ctx == ctxQ.ctx, "Same context formula expected, but got " + ctxP.ctx + " and " + ctxQ.ctx)
          Predef.assert(ctxP.isProgramContext, "Program context expected for CPrgE")
          provable(equivifyR(1), 0)(UnifyUSCalculus.CE(ctxP)(ProvableSig.startPlainProof(ProgramEquivalence(a, b))), 0)
        }
      case fml => throw new TacticInapplicableFailure("Expected implication, but got " + fml)
    }
  }

  private[btactics] def CPrgErevimpFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent formula, but got " + sequent,
    )
    sequent.succ.head match {
      case Imply(l, r) =>
        if (inEqPos == HereP) commuteEquivR(1).computeResult(equivifyR(1).computeResult(provable))
        else {
          val (ctxP, a: Program) = l.at(inEqPos)
          val (ctxQ, b: Program) = r.at(inEqPos)
          // @note Could skip the construction of ctxQ but it's part of the .at construction anyways.
          require(ctxP == ctxQ, "Same context expected, but got " + ctxP + " and " + ctxQ)
          Predef.assert(ctxP.ctx == ctxQ.ctx, "Same context formula expected, but got " + ctxP.ctx + " and " + ctxQ.ctx)
          Predef.assert(ctxP.isProgramContext, "Program context expected for CPrgE")
          provable(equivifyR(1), 0)(commuteEquivR(1), 0)(
            UnifyUSCalculus.CE(ctxP)(ProvableSig.startPlainProof(ProgramEquivalence(b, a))),
            0,
          )
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
    refTrans("x:=x;".asProgram)(Position(1)) & andR(1) & Idioms.<(
      useAt(refStutter)(Position(1, 1 :: Nil)) & useAt(refRefl)(Position(1)),
      discreteGhost(Variable("x"), None)(Position(1)) & useAt(refAssign)(Position(1, 0 :: Nil)) &
        useAt(refSeqIdR, PosInExpr(1 :: Nil))(Position(1, 1 :: Nil)) & CMon(Position(1, 0 :: 1 :: 0 :: Nil)) & prop,
    ),
  )

  @Tactic(name = "focus", displayPremises = "C'(a<=b)", displayConclusion = "C{a}<=C{b}")
  def focus: BuiltInRightTactic = anon { (provable: ProvableSig, pos: SuccPosition) =>
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
        }
        require(ctxA == ctxB, "Same context expected, but got " + ctxA + " and " + ctxB)
        Predef.assert(ctxA.ctx == ctxB.ctx, "Same context formula expected, but got " + ctxA.ctx + " and " + ctxB.ctx)
        provable(focusFW(ctxA, pos.topLevel, dot), 0)
    }
  }

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
          val tactic = ode match {
            case DifferentialProduct(_, _) => congrODEDoms
            case _ => congrODEDom
          }
          provable(useAt(tactic, PosInExpr(1 :: Nil))(pos), 0)
      }
    }

}
