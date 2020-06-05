package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.{Configuration, core}
import edu.cmu.cs.ls.keymaerax.core.{RenamingClashException, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.macros.Tactic
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.apache.logging.log4j.scala.Logging


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

  def rawCut(f: Formula): BuiltInTactic = "rawCut" by { (provable: ProvableSig) => provable(core.Cut(f), 0)}

  /** [[SequentCalculus.cut()]] */
  @Tactic(premises = "Γ, C |- Δ ;; Γ |- Δ, C", conclusion = "Γ |- Δ", inputs = "C:formula")
  def cut(f: Formula): InputTactic = inputanon {rawCut(f) & Idioms.<(label(BelleLabels.cutUse), label(BelleLabels.cutShow))}

  /** [[SequentCalculus.cutL()]] */
  @Tactic(premises = "Γ, C |- Δ ;; Γ |- Δ, P→C",
    conclusion = "Γ, P |- Δ", inputs = "C:formula")
  def cutL(f: Formula): DependentPositionWithAppliedInputTactic = inputanonL { (provable: ProvableSig, pos: AntePosition) =>
    requireOneSubgoal(provable, "cutL(" + f + ")")
    provable(core.CutLeft(f, pos.top), 0)
    //@todo label BelleLabels.cutUse/cutShow
  }

  /** [[SequentCalculus.cutR()]] */
  @Tactic(premises = "Γ |- C, Δ ;; Γ |- C→P, Δ",
    conclusion = "Γ |- P, Δ", inputs = "C:formula")
  def cutR(f: Formula): DependentPositionWithAppliedInputTactic = inputanonR { (provable: ProvableSig, pos: SuccPosition) =>
    requireOneSubgoal(provable, "cutR(" + f + ")")
    provable(core.CutRight(f, pos.top), 0)
  }

  /** [[SequentCalculus.cutLR()]] */
  @Tactic()
  def cutLR(f: Formula): DependentPositionWithAppliedInputTactic = inputanonP { (provable: ProvableSig, pos: Position) =>
    requireOneSubgoal(provable, "cutLR(" + f + ")")
    if (pos.isAnte) provable(core.CutLeft(f, pos.checkAnte.top), 0)
    else provable(core.CutRight(f, pos.checkSucc.top), 0)
  }

  //@todo this should not be a dependent tactic, just a by(Position=>Belle)
  @Tactic("W")
  val hide: DependentPositionTactic = anon { (pos:Position) => pos match {
      case p: AntePosition => SequentCalculus.hideL(p)
      case p: SuccPosition => SequentCalculus.hideR(p)
    }
  }

  @Tactic("W")
  val cohide: DependentPositionTactic = anon { (pos: Position) => pos match {
      case p: AntePosition => SequentCalculus.cohideL(p)
      case p: SuccPosition => SequentCalculus.cohideR(p)
    }
  }

  @Tactic("XL")
  val exchangeL: BuiltInTwoPositionTactic = anon { (pr: ProvableSig, posOne: Position, posTwo: Position) =>
    //require(posOne.isAnte && posTwo.isAnte, "Both positions should be in the Antecedent.")
    pr(core.ExchangeLeftRule(posOne.checkAnte.top, posTwo.checkAnte.top), 0)
  }

  @Tactic("XR")
  val exchangeR: BuiltInTwoPositionTactic = anon { (pr: ProvableSig, posOne: Position, posTwo: Position) =>
    //require(posOne.isSucc && posTwo.isSucc, "Both positions should be in the Succedent.")
    pr(core.ExchangeRightRule(posOne.checkSucc.top, posTwo.checkSucc.top), 0)
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
//@todo  @Tactic("UR",
//    premises = "P(y) |- Q(y)",
//    conclusion = "P(x) |- Q(x)", inputs = "x:variable ;; y:variable")
//  def uniformRename(what: Variable, repl: Variable): InputTactic = anon { (pr: ProvableSig) =>
//    requireOneSubgoal(pr, "UR(" + what + "~~>" + repl + ")")
//    pr(core.UniformRenaming(what, repl), 0)
//  }
  def uniformRename(what: Variable, repl: Variable): InputTactic = "uniformRename" byWithInputs(what::repl::Nil,
  new BuiltInTactic("UniformRenaming") {
    /**
      * @throws RenamingClashException if uniform renaming what~>repl is not admissible for s (because a semantic symbol occurs).
      */
    override def result(provable: ProvableSig): ProvableSig = {
      requireOneSubgoal(provable, name + "(" + what + "~~>" + repl + ")")
      provable(core.UniformRenaming(what, repl), 0)
    }
  }
)

  import TacticFactory._
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
  def boundRename(what: Variable, repl: Variable): DependentPositionTactic = anon {(pos:Position, sequent:Sequent) =>
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

  private def topBoundRenaming(what: Variable, repl: Variable): PositionalTactic = new BuiltInPositionTactic("BoundRenaming") {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      requireOneSubgoal(provable, name + "(" + what + "~~>" + repl + ")")
      require(pos.isTopLevel, "bound renaming rule only at top-level")
      provable(core.BoundRenaming(what, repl, pos.top), 0)
    }
  }

  /** contextualize(t) lifts (standard) top-level tactic `t` to also work on subpositions in any formula context C{_}.
    *
    * @param tactic the tactic to be lifted, which is required to
    *               work on top-level left and right
    *               and only leave a single goal with one single formula changed.
    * @author Andre Platzer
    * @note Implementation analogous to [[ProofRuleTactics.boundRename()]]
    */
  def contextualize[T <: BelleExpr](tactic: AtPosition[T], predictor: Formula=>Formula): DependentPositionTactic = "contextualize(" + tactic.prettyString + ")" by ((pos:Position, sequent:Sequent) =>
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
  //@todo@Tactic("skolem")
  val skolemizeR: BuiltInRightTactic = new BuiltInRightTactic("skolemizeR") {
    override def computeResult(provable: ProvableSig, pos: SuccPosition): ProvableSig = {
      requireOneSubgoal(provable, name)
      require(pos.isTopLevel, "Skolemization only at top-level")
      provable(core.Skolemize(pos.top), 0)
    }
  }

  @deprecated("Use SequentCalculus.closeT instead")
  private[btactics] def closeTrue = new BuiltInRightTactic("CloseTrue") {
    override def computeResult(provable: ProvableSig, pos: SuccPosition): ProvableSig = {
      requireOneSubgoal(provable, name)
      provable(core.CloseTrue(pos.top), 0)
    }
  }

  @deprecated("Use SequentCalculus.closeF instead")
  private[btactics] def closeFalse = new BuiltInLeftTactic("CloseFalse") {
    override def computeResult(provable: ProvableSig, pos: AntePosition): ProvableSig = {
      requireOneSubgoal(provable, name)
      provable(core.CloseFalse(pos.top), 0)
    }
  }
}
