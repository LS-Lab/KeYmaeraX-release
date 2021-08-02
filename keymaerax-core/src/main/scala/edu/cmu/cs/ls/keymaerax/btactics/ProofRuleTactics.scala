package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.{Logging, core}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig


/**
 * Implementation: [[ProofRuleTactics]] contains tactical implementations of the propositional sequent calculus
 * and other proof rules that are implemented by KeYmaera X.
  *
  * @author Nathan Fulton
 * @see [[SequentCalculus]]
 */
private object ProofRuleTactics extends Logging {
  /**
   * Throw exception if there is more than one open subgoal on the provable.
   */
  private[btactics] def requireOneSubgoal(provable: ProvableSig, msg: => String): Unit =
    if(provable.subgoals.length != 1) throw new IllFormedTacticApplicationException(s"Expected exactly one subgoal sequent in Provable but found ${provable.subgoals.length}\n" + msg)

  def applyRule(rule: Rule): BuiltInTactic = new BuiltInTactic("Apply Rule") {
    override def result(provable: ProvableSig): ProvableSig = {
      requireOneSubgoal(provable, "apply " + rule)
      provable(rule, 0)
    }
  }

  /**
    * Uniform renaming `what~>repl` and vice versa.
    *
    * @param what What variable to replace (along with its associated DifferentialSymbol).
    * @param repl The target variable to replace what with.
    * @return
    * @throws RenamingClashException if uniform renaming what~>repl is not admissible for s (because a semantic symbol occurs).
    * @see [[edu.cmu.cs.ls.keymaerax.core.UniformRenaming]]
    */
  @Tactic("UR",
    premises = "P(y) |- Q(y)",
    conclusion = "P(x) |- Q(x)", inputs = "x:variable ;; y:variable")
  def uniformRename(what: Variable, repl: Variable): InputTactic = inputanonP {(provable: ProvableSig) =>
      requireOneSubgoal(provable, "UniformRename(" + what + "~~>" + repl + ")")
      provable(core.UniformRenaming(what, repl), 0)
    }

  /**
    * Bound renaming `what~>repl` renames the bound variable `what` bound at the indicated position to `what`.
    *
    * @param what the variable bound at the position where this tactic will be used.
    * @param repl the new, fresh variable to be used for this bound variable instead.
    * @author Andre Platzer
    * @incontext
    * @see [[edu.cmu.cs.ls.keymaerax.core.BoundRenaming]]
    * @see [[UnifyUSCalculus.boundRename()]]
    * @throws RenamingClashException if this bound renaming is not admissible for s at the indicated position
    *                                because repl,repl',what' already occurred, or
    *                                because a semantic symbol occurs, or
    *                                because the formula at `pos` has the wrong shape.
    */
  @Tactic("BR",
    premises = "Γ |- ∀y Q(y), Δ",
    conclusion = "Γ |- ∀x Q(x), Δ", inputs = "x:variable;;y:variable")
  def boundRename(what: Variable, repl: Variable): DependentPositionWithAppliedInputTactic = inputanon {(pos:Position, sequent:Sequent) =>
    if (pos.isTopLevel)
      topBoundRenaming(what,repl)(pos)
    else {
      //@note contextualize
        // [x:=f(x)]P(x)
        import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
        val fml = sequent.apply(pos).asInstanceOf[Formula]
        // renaming bound variable x in [x:=f()]p(x) assignment to [y:=f()]p(y) to make y not occur in f() anymore
        //@note the proof is the same for \forall x p(x) etc.
        val brenL = core.BoundRenaming(what, repl, AntePos(0))
        val brenR = core.BoundRenaming(what, repl, SuccPos(0))
        val mod = brenR(fml) ensures(r => r==brenL(fml), "bound renaming for formula is independent of position")
        // |- \forall y (y=f(x) -> P(y)) <-> [x:=f(x)]P(x)
        val side: ProvableSig = (ProvableSig.startProof(Equiv(mod, fml))
          // |- [y:=f(x)]P(y) <-> [x:=f(x)]P(x)
          (EquivRight(SuccPos(0)), 0)
          // right branch  [x:=f(x)]P(x) |- [y:=f(x)]P(y)
          (brenL, 1)
          // [y:=f(x)]P(y) |- [y:=f(x)]P(y)
          (Close(AntePos(0), SuccPos(0)), 1)
          // left branch  [y:=f(x)]P(y) |- [x:=f(x)]P(x)
          (brenR, 0)
          // [y:=f(x)]P(y) |- [y:=f(x)]P(y)
          (Close(AntePos(0), SuccPos(0)), 0)
        )
        TactixLibrary.CEat(side)(pos)
    }}

  /** Bound renaming at a position (must point to universal quantifier or assignment). */
  @Tactic("BRat",
    premises = "Γ |- ∀y Q(y), Δ",
    conclusion = "Γ |- ∀x Q(x), Δ", inputs = "y:variable", displayLevel = "browse")
  def boundRenameAt(repl: Variable): DependentPositionWithAppliedInputTactic = inputanon {(pos:Position, sequent:Sequent) =>
    sequent.sub(pos) match {
      case Some(Forall(DifferentialSymbol(v) :: Nil, p)) => DLBySubst.stutter(v)(pos) & boundRename(v, repl)(pos) & assignb(pos)
      case Some(Forall((v: BaseVariable) :: Nil, _)) => boundRename(v, repl)(pos)
      case Some(Exists(DifferentialSymbol(v) :: Nil, p)) => DLBySubst.stutter(v)(pos) & boundRename(v, repl)(pos) & assignb(pos)
      case Some(Exists((v: BaseVariable) :: Nil, _)) => boundRename(v, repl)(pos)
      case Some(Box(Assign(v, _), _)) => boundRename(v, repl)(pos)
      case Some(Box(AssignAny(v), _)) => boundRename(v, repl)(pos)
      case Some(Diamond(Assign(v, _), _)) => boundRename(v, repl)(pos)
      case Some(Diamond(AssignAny(v), _)) => boundRename(v, repl)(pos)
      case ex => throw new TacticInapplicableFailure("Expected quantifier or assignment at position " + pos.prettyString + ", but got " + ex.map(_.prettyString))
    }
  }

  private def topBoundRenaming(what: Variable, repl: Variable): PositionalTactic = anon { (provable: ProvableSig, pos: Position) => {
    requireOneSubgoal(provable, "BoundRenaming(" + what + "~~>" + repl + ")")
    require(pos.isTopLevel, "bound renaming rule only at top-level")
    provable(core.BoundRenaming(what, repl, pos.top), 0)
  }}

  /** contextualize(t) lifts (standard) top-level tactic `t` to also work on subpositions in any formula context C{_}.
    *
    * @param tactic the tactic to be lifted, which is required to
    *               work on top-level left and right
    *               and only leave a single goal with one single formula changed.
    * @author Andre Platzer
    * @note Implementation analogous to [[ProofRuleTactics.boundRename()]]
    */
  def contextualize[T <: BelleExpr](tactic: AtPosition[T], predictor: Formula=>Formula): DependentPositionTactic = anon ((pos:Position, sequent:Sequent) =>
    if (pos.isTopLevel)
      tactic(pos)
    else {
      //@note contextualize
      import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
      val fml: Formula = sequent.apply(pos).asInstanceOf[Formula]
      val mod: Formula = predictor(fml)
      // |- mod <-> fml
      val side: ProvableSig = TactixLibrary.proveBy(Equiv(mod, fml),
        // |- mod <-> fml
        equivR(1) <(
          // left branch  mod |- fml
          tactic(1) &
            // mod |- mod
            close(-1, 1)
          ,
          // right branch  fml |- mod
          tactic(-1) &
          // mod |- mod
          close(-1,1)
        )
      )
      logger.debug("contextualize.side " + side)
      TactixLibrary.CEat(side)(pos)
    })

  def contextualize[T <: BelleExpr](tactic: AtPosition[T]): DependentPositionTactic =
    contextualize(tactic, (fml:Formula) => {
      def shapeCheck(pr: ProvableSig): ProvableSig = {
        require(pr.subgoals.length==1, "one subgoal only")
        require(pr.subgoals.head.ante.isEmpty, "no antecedent")
        require(pr.subgoals.head.succ.length==1, "one subformula in succedent only")
        pr
      }
      shapeCheck(TactixLibrary.proveBy(fml, tactic(1))).subgoals.head.succ.head
    })

  /** @throws SkolemClashException if the quantified variable that is to be Skolemized already occurs free in the sequent.
    *                              Use [[BoundRenaming]] to resolve.
    */
  @Tactic(premises = "Γ |- p(x), Δ",
    conclusion = "Γ |- ∀x p(x), Δ", codeName = "skolem")
  val skolemizeR: BuiltInRightTactic = anon {(provable: ProvableSig, pos: SuccPosition) => {
    require(pos.isTopLevel, "Skolemization only at top-level")
    provable(core.Skolemize(pos.top), 0)
  }}

  @deprecated("Use SequentCalculus.closeT instead")
  @Tactic()
  private[btactics] val closeTrue: BuiltInRightTactic = anon {(provable: ProvableSig, pos: SuccPosition) =>
    requireOneSubgoal(provable, "closeTrue")
    provable(core.CloseTrue(pos.top), 0)
  }

  @deprecated("Use SequentCalculus.closeF instead")
  @Tactic()
  private[btactics] val closeFalse: BuiltInLeftTactic = anon { (provable: ProvableSig, pos: AntePosition) =>
    requireOneSubgoal(provable, "closeFalse")
    provable(core.CloseFalse(pos.top), 0)
  }

}
