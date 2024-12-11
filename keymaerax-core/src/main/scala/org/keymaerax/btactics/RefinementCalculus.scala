/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.{DependentPositionWithAppliedInputTactic, TacticInapplicableFailure}
import org.keymaerax.btactics.Derive.useAt
import org.keymaerax.btactics.TacticFactory.inputanon
import org.keymaerax.btactics.macros.{CoreAxiomInfo, DisplayLevel, Tactic, Unifier}
import org.keymaerax.core.btactics.annotations.Derivation
import org.keymaerax.core.{Expression, Program, Refinement, Sequent, SubstitutionPair, SystemConst, USubst}
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.infrastruct.FormulaTools.dualFree
import org.keymaerax.infrastruct.{PosInExpr, Position}
import org.keymaerax.pt.ProvableSig

import scala.reflect.runtime.universe

object RefinementCalculus extends TacticProvider {
  override def getInfo: (Class[_], universe.Type) =
    (RefinementCalculus.getClass, universe.typeOf[RefinementCalculus.type])

  /** Refinement axioms */
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
    displayLevel = DisplayLevel.Menu,
    key = "0",
    unifier = Unifier.SurjectiveLinear,
  )
  @Derivation
  val refOdes: CoreAxiomInfo = CoreAxiomInfo.create(
    name = "refOdes",
    canonicalName = "refinement ode (system)",
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
}
