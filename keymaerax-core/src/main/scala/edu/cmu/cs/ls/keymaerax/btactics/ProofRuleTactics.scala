package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig


/**
 * Implementation: [[ProofRuleTactics]] contains tactical implementations of the propositional sequent calculus
 * and other proof rules that are implemented by KeYmaera X.
  *
  * @author Nathan Fulton
 * @see [[SequentCalculi]]
 */
private object ProofRuleTactics {
  //@note Rule.LAX_MODE not accessible outside core
  val LAX_MODE = System.getProperty("LAX", "true")=="true"

  /**
   * Throw exception if there is more than one open subgoal on the provable.
   */
  private[btactics] def requireOneSubgoal(provable: ProvableSig, msg: => String) =
    if(provable.subgoals.length != 1) throw new BelleThrowable(s"Expected exactly one sequent in Provable but found ${provable.subgoals.length}\n" + msg)

  def applyRule(rule: Rule): BuiltInTactic = new BuiltInTactic("Apply Rule") {
    override def result(provable: ProvableSig): ProvableSig = {
      requireOneSubgoal(provable, "apply " + rule)
      provable(rule, 0)
    }
  }

  def cut(f: Formula) = new InputTactic("cut", f::Nil) {
    override def computeExpr(): BelleExpr = new BuiltInTactic(s"$name(${f.prettyString})") {
      override def result(provable: ProvableSig): ProvableSig = {
        provable(core.Cut(f), 0)
      }
    } & Idioms.<(label(BelleLabels.cutUse.label), label(BelleLabels.cutShow.label))
  }

  def cutL(f: Formula): DependentPositionWithAppliedInputTactic = "cutL" byWithInput(f, (pos: Position, _: Sequent) => {
    new BuiltInTactic("CutL") {
      override def result(provable: ProvableSig): ProvableSig = {
        requireOneSubgoal(provable, "cutL(" + f + ")")
        provable(core.CutLeft(f, pos.checkAnte.top), 0)
      }
    }
  })

  def cutR(f: Formula): DependentPositionWithAppliedInputTactic = "cutR" byWithInput(f, (pos: Position, _: Sequent) => {
    new BuiltInTactic("CutR") {
      override def result(provable: ProvableSig): ProvableSig = {
        requireOneSubgoal(provable, "cutR(" + f + ")")
        provable(core.CutRight(f, pos.checkSucc.top), 0)
      }
    }
  })

  def cutLR(f: Formula): DependentPositionWithAppliedInputTactic = "cutLR" byWithInput(f, (pos: Position, _: Sequent) => {
    new BuiltInTactic("CutLR") {
      override def result(provable: ProvableSig): ProvableSig = {
        requireOneSubgoal(provable, "cutLR(" + f + ")")
        if (pos.isAnte) provable(core.CutLeft(f, pos.checkAnte.top), 0)
        else provable(core.CutRight(f, pos.checkSucc.top), 0)
      }
    }
  })

  def hide = new DependentPositionTactic("Hide") {
    //@todo this should not be a dependent tactic, just a by(Position=>Belle)
    override def factory(pos: Position): DependentTactic = pos match {
      case p: AntePosition => new DependentTactic(name) {
        override def computeExpr(v: BelleValue): BelleExpr = hideL(p)
      }
      case p: SuccPosition => new DependentTactic(name) {
        override def computeExpr(v: BelleValue): BelleExpr = hideR(p)
      }
    }
  }


  def coHide = new DependentPositionTactic("CoHide") {
    override def factory(pos: Position): DependentTactic = pos match {
      case p: AntePosition => new DependentTactic(name) {
        override def computeExpr(v: BelleValue): BelleExpr = SequentCalculus.cohideL(p)
      }
      case p: SuccPosition => new DependentTactic(name) {
        override def computeExpr(v: BelleValue): BelleExpr = SequentCalculus.cohideR(p)
      }
    }
  }

//  def exchangeL = new BuiltInTwoPositionTactic("ExchangeL") {
//    override def computeResult(provable: Provable, posOne: Position, posTwo: Position): Provable = {
//      requireOneSubgoal(provable)
//      require(posOne.isAnte && posTwo.isAnte, "Both positions should be in the Antecedent.")
//      provable(core.ExchangeLeftRule(posOne.checkAnte.top, posTwo.checkAnte.top), 0)
//    }
//  }

  def exchangeR = new BuiltInTwoPositionTactic("ExchangeR") {
    def computeResult(provable : ProvableSig, posOne: Position, posTwo: Position) : ProvableSig = {
      require(posOne.isSucc && posTwo.isSucc, "Both positions should be in the Succedent.")
      provable(core.ExchangeRightRule(posOne.checkSucc.top, posTwo.checkSucc.top), 0)
    }
  }

  /**
    * Uniform renaming `what~>repl` and vice versa.
    *
    * @param what What variable to replace (along with its associated DifferentialSymbol).
    * @param repl The target variable to replace what with.
    * @return
    * @see [[edu.cmu.cs.ls.keymaerax.core.UniformRenaming]]
    */
  def uniformRenaming(what: Variable, repl: Variable) = new BuiltInTactic("UniformRenaming") {
    override def result(provable: ProvableSig): ProvableSig = {
      requireOneSubgoal(provable, name + "(" + what + "~~>" + repl + ")")
      provable(core.UniformRenaming(what, repl), 0)
    }
  }

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
    */
  def boundRenaming(what: Variable, repl: Variable): DependentPositionTactic = "boundRename" byWithInputs (List(what, repl), (pos:Position, sequent:Sequent) =>
    if (pos.isTopLevel)
      topBoundRenaming(what,repl)(pos)
    else {
      //@note contextualize
        // [x:=f(x)]P(x)
        import Augmentors.SequentAugmentor
        val fml = sequent.apply(pos).asInstanceOf[Formula]
        // renaming bound variable x in [x:=f()]p(x) assignment to [y:=f()]p(y) to make y not occur in f() anymore
        //@note the proof is the same for \forall x p(x) etc.
        val brenL = core.BoundRenaming(what, repl, AntePos(0))
        val brenR = core.BoundRenaming(what, repl, SuccPos(0))
        val mod = brenR(fml) ensuring(r => r==brenL(fml), "bound renaming for formula is independent of position")
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
    })

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
    * @note Implementation analogous to [[ProofRuleTactics.boundRenaming()]]
    */
  def contextualize[T <: BelleExpr](tactic: AtPosition[T], predictor: Formula=>Formula): DependentPositionTactic = "contextualize(" + tactic.prettyString + ")" by ((pos:Position, sequent:Sequent) =>
    if (pos.isTopLevel)
      tactic(pos)
    else {
      //@note contextualize
      import Augmentors.SequentAugmentor
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
      if (BelleExpr.DEBUG) println("contextualize.side " + side)
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

  def skolemizeR = new BuiltInRightTactic("skolemizeR") {
    override def computeSuccResult(provable: ProvableSig, pos: SuccPosition): ProvableSig = {
      requireOneSubgoal(provable, name)
      require(pos.isTopLevel, "Skolemization only at top-level")
      provable(core.Skolemize(pos.top), 0)
    }
  }

  @deprecated("Use SequentCalculus.closeTrue instead")
  private[btactics] def closeTrue = new BuiltInRightTactic("CloseTrue") {
    override def computeSuccResult(provable: ProvableSig, pos: SuccPosition): ProvableSig = {
      requireOneSubgoal(provable, name)
      provable(core.CloseTrue(pos.top), 0)
    }
  }

  @deprecated("Use SequentCalculus.closeFalse instead")
  private[btactics] def closeFalse = new BuiltInLeftTactic("CloseFalse") {
    override def computeAnteResult(provable: ProvableSig, pos: AntePosition): ProvableSig = {
      requireOneSubgoal(provable, name)
      provable(core.CloseFalse(pos.top), 0)
    }
  }
}
