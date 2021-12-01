package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import TacticFactory._
import edu.cmu.cs.ls.keymaerax.core.{Close, Cut, EquivLeft, NotLeft}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.{Logging, core}
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr, Position, RenUSubst, SuccPosition, UnificationMatchUSubstAboveURen}
import edu.cmu.cs.ls.keymaerax.btactics.macros.{Tactic, TacticInfo}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec

/**
 * [[PropositionalTactics]] provides tactics for propositional reasoning.
 */
private object PropositionalTactics extends Logging {
  /**
   * Inverse of [[SequentCalculus.implyR]].
   * @author Nathan Fulton
   * @author Stefan Mitsch
   * @see [[SequentCalculus.implyR]]
   */
  private[btactics] lazy val implyRi: AppliedBuiltinTwoPositionTactic = implyRi()(AntePos(0), SuccPos(0))
  private[btactics] def implyRi(keep: Boolean = false): BuiltInTwoPositionTactic = anon ((p: ProvableSig, a: Position, s: Position) => {
    assert(p.subgoals.length == 1, "Assuming one subgoal.")
    val sequent = p.subgoals.head
    require(a.isIndexDefined(sequent) && s.isIndexDefined(sequent),
      "Ante position " + a + " or succ position " + s + " is out of bounds; provable has ante size " +
        sequent.ante.length + " and succ size " + sequent.succ.length)
    val left = sequent.ante(a.checkAnte.top.getIndex)
    val impl = p(CutRight(left, s.checkSucc.top), 0)(Close(a.checkAnte.top, s.checkSucc.top), 0)
    if (keep) impl else impl(core.HideLeft(a.checkAnte.top), 0)
  })

  /**
   * Inverse of [[ProofRuleTactics.orR]].
   *
   * @author Stefan Mitsch
   * @see [[ProofRuleTactics.orR]]
   */
  private[btactics] lazy val orRi: AppliedBuiltinTwoPositionTactic = orRi(keepLeft=false)(SuccPosition.base0(0), SuccPosition.base0(1))
  private[btactics] def orRi(keepLeft: Boolean): BuiltInTwoPositionTactic = anon { (pr: ProvableSig, pos1: Position, pos2: Position) => {
    require(pos1 != pos2, "Two distinct positions required")
    val sequent = pr.subgoals.head
    require(sequent.succ.length > pos1.index0 && sequent.succ.length > pos2.index0,
      "Position " + pos1 + " or position " + pos2 + " is out of bounds; provable has succ size " + sequent.succ.length)
    val left = sequent.succ(pos1.index0)
    val right = sequent.succ(pos2.index0)
    val cutUsePos = AntePos(sequent.ante.length)

    //    cut(Or(left, right)) <(
    //      /* use */ orL(cutUsePos) & OnAll(TactixLibrary.close),
    //      /* show */
    //        if (pos1.getIndex > pos2.getIndex) (assertE(left, "")(pos1) & hideR(pos1) & assertE(right, "")(pos2) & hideR(pos2))
    //        else (assertE(right, "")(pos2) & hideR(pos2) & assertE(left, "")(pos1) & hideR(pos1))
    //      )
    //    }
    val cutPr = pr(Cut(Or(left, right)), 0)
    (if (pos1.index0 > pos2.index0) cutPr(HideRight(pos1.checkSucc.checkTop), 1)(HideRight(pos2.checkSucc.checkTop), 1)
     else cutPr(HideRight(pos2.checkSucc.checkTop), 1)(HideRight(pos1.checkSucc.checkTop), 1))(
      OrLeft(cutUsePos), 0)(
      Close(cutUsePos, pos2.checkSucc.checkTop), 2)(
      Close(cutUsePos, pos1.checkSucc.checkTop), 0)
  }}

  /**
   * Inverse of [[ProofRuleTactics.andL]].
 *
   * @author Stefan Mitsch
   * @see [[ProofRuleTactics.andL]]
   */
  private[btactics] lazy val andLi: AppliedBuiltinTwoPositionTactic = andLi(keepLeft=false)(AntePosition.base0(0), AntePosition.base0(1))
  private[btactics] def andLi(keepLeft: Boolean): BuiltInTwoPositionTactic = anon { (pr: ProvableSig, pos1: Position, pos2: Position) => {
    require(pos1 != pos2, "Two distinct positions required")
    val sequent = pr.subgoals.head
    require(sequent.ante.length > pos1.index0 && sequent.ante.length > pos2.index0,
      "Position " + pos1 + " or position " + pos2 + " is out of bounds; provable has ante size " + sequent.ante.length)
    val left = sequent.ante(pos1.index0)
    val right = sequent.ante(pos2.index0)
    val cutUsePos = SuccPos(sequent.succ.length)

    //    cut(And(left, right)) <(
    //      /* use */
    //      if (pos1.index0 > pos2.index0) assertE(left, "")(pos1) & (if (keepLeft) skip else hideL(pos1)) & assertE(right, "")(pos2) & hideL(pos2)
    //      else assertE(right, "")(pos2) & hideL(pos2) & assertE(left, "")(pos1) & (if (keepLeft) skip else hideL(pos1)),
    //      /* show */ andR(cutUsePos) & OnAll(TactixLibrary.close)
    //    )}
    val cutPr = pr(Cut(And(left, right)), 0)
    (if (pos1.index0 > pos2.index0) {
      (if (keepLeft) cutPr else cutPr(HideLeft(pos1.checkAnte.checkTop), 0))(HideLeft(pos2.checkAnte.checkTop), 0)
    } else {
      val pos2Hidden = cutPr(HideLeft(pos2.checkAnte.checkTop), 0)
      if (keepLeft) pos2Hidden else pos2Hidden(HideLeft(pos1.checkAnte.checkTop), 0)
    })(AndRight(cutUsePos), 1)(
      Close(pos2.checkAnte.checkTop, cutUsePos), 2)(
      Close(pos1.checkAnte.checkTop, cutUsePos), 1)
  }}

  /**
   * Returns a tactic for propositional CE with purely propositional unpeeling. Useful when unpeeled fact is not
   * an equivalence, as needed by CE. May perform better than CE for small contexts.
 *
   * @see [[UnifyUSCalculus.CMon(Context)]]
   * @see [[UnifyUSCalculus.CE(Context)]]
   * @example {{{
   *                  z=1 |- z>0
   *         --------------------------propCE(PosInExpr(1::Nil))
   *           x>0 -> z=1 |- x>0 -> z>0
   * }}}
   * @param at Points to the position to unpeel.
   * @return The tactic.
   */
  //@todo optimizable a lot by using technique from TactixLibrary.stepAt index instead of |
  def propCMon(at: PosInExpr): DependentTactic = new SingleGoalDependentTactic("Prop. CMon") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.length == 1 && sequent.succ.length == 1 &&
        sequent.ante.head.at(at)._1 == sequent.succ.head.at(at)._1, s"Propositional CMon requires single antecedent " +
        s"and single succedent formula with matching context to $at, but got $sequent")

      // we know that we have the same operator in antecedent and succedent with the same lhs -> we know that one
      // will branch and one of these branches will close by identity. on the other branch, we have to hide
      // list all cases explicitly, hide appropriate formulas in order to not blow up branching
      if (at.pos.length <= 0) skip
      else (sequent.succ.headOption match {
        case Some(_: Not) => notL(-1) & notR(1) & assertT(1, 1)
        case Some(_: And) => andL(-1) & andR(1) <(close | hideL(-2), close | hideL(-1)) & assertT(1, 1)
        case Some(_: Or) => orR(1) & orL(-1) <(close | hideR(2), close | hideR(1)) & assertT(1, 1)
        case Some(_: Imply) => implyR(1) & implyL(-1) <(close | hideR(1), close | hideL('Llast)) & assertT(1, 1)
        case Some(_: Box) => monb
        case Some(_: Diamond) => mond
        case Some(_: Forall) => allR(1) & allL(-1)
        case Some(_: Exists) => existsL(-1) & existsR(1)
        case Some(e) => throw new TacticInapplicableFailure("Prop. CMon not applicable to " + e.prettyString)
        // redundant to exception raised by .at(...) in contract above
        case None => throw new IllFormedTacticApplicationException("Prop. CMon: no more formulas left to descend into " + at.prettyString)
      }) & propCMon(at.child)
    }
  }

  /** @see [[SequentCalculus.modusPonens()]] */
  private[btactics] def modusPonens(assumption: AntePos, implication: AntePos): BelleExpr = anon { seq: Sequent =>
    val p = AntePos(assumption.getIndex - (if (assumption.getIndex > implication.getIndex) 1 else 0))
    //@note adapted to use implyL instead of implyLOld
    implyL(implication) <(
      closeId(p, SuccPos(seq.succ.length))
      //cohide2(p, SuccPos(sequent.succ.length)) & close
      //@todo optimizable shouldn't this suffice? close(AntePosition(assumption), SuccPosition(SuccPos(sequent.succ.length)))
      ,
      Idioms.ident
      )
  }

  /** Automated modus ponens for p->q ==> ; tries to automatically prove p from the rest of the assumptions. */
  @Tactic()
  private[btactics] val autoMP: DependentPositionTactic = anon { (pos: Position, seq: Sequent) => seq(pos.checkAnte.checkTop) match {
      case Imply(p, _) =>
        val pi = seq.ante.indexWhere(_ == p)
        if (pi >= 0) modusPonens(AntePos(pi), pos.checkAnte.checkTop)
        else {
          //@todo usually includes too many assumptions
          val notsuccs = seq.succ.map(Not).map(SimplifierV3.formulaSimp(_, scala.collection.immutable.HashSet.empty, SimplifierV3.defaultFaxs, SimplifierV3.defaultTaxs)._1)
          val antes = seq.ante.patch(pos.index0, List.empty, 1)
          val assms = (notsuccs ++ antes).reduceRightOption(And).getOrElse(True)
          val mpShow = Sequent(scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(Imply(assms, p)))
          //@todo tactic with timeouts results in proof repeatability issues
          val mpLemma = proveBy(mpShow, SaturateTactic(implyR('R) | andL('L)) & EqualityTactics.expandAll & prop &
            Idioms.doIf(_.subgoals.size <= 4)(OnAll(QEX(None, Some(Number(2))))))

          if (mpLemma.isProved) {
            cut(p) < (
              modusPonens(AntePos(seq.ante.size), pos.checkAnte.checkTop) & SaturateTactic(hideL('L, p)),
              useAt(mpLemma, PosInExpr(1 :: Nil))('Rlast) & prop & done)
          } else throw new TacticInapplicableFailure("Failed to prove assumptions")
        }
      case _ => throw new TacticInapplicableFailure("Applicable only to implications at top-level in the antecedent")
    }
  }
  private[btactics] val autoMPInfo: TacticInfo = TacticInfo("autoMP")

  /**
   * Converts a sequent into a single formula.
   * Example:
   * {{{
   *   A, B |- S, T, U
   * }}}
   * is converted into:
   * {{{
   *   (A ^ B) -> (S \/ T \/ U)
   * }}}
   */
  @Tactic()
  val toSingleFormula: DependentTactic  = anon {(sequent: Sequent) =>
    cut(sequent.toFormula) <(
      /* use */ implyL('Llast) <(
        hideR(1)*sequent.succ.size & (andR(1) <(close, skip))*(sequent.ante.size-1) & onAll(close),
        hideL(-1)*sequent.ante.size & (orL(-1) <(close, skip))*(sequent.succ.size-1) & onAll(close)),
      /* show */ cohide('Rlast)
      )
  }

  //region Equivalence Rewriting

  /**
    * Performs equivalence rewriting in either direction at any top-level position in a sequent,
    * leaving the original equivalence in place. Instantiates Forall-quantified equivalences so that they match
    * the target position when necessary. If the quantified variable is not mentioned in the targetPos, then the quantified
    * name is used.
    *
    * @todo these examples might be incorrect, and the description above might be incorrect. Correct explanation is "does whatever unification does", actually.
    *       Although we might want to change that to not use unification...
    *
    * Examples:
    * {{{
    *   \forall x. p(x) <-> q() |- p(x)
    *   --------------------------------- equivRewriting(-1,1)
    *   \forall x. p(x) <-> q() |- q()
    *
    *   \forall x. p(x) <-> q() |- q()
    *   --------------------------------- equivRewriting(-1,1)
    *   \forall x. p(x) <-> q() |- p(z)
    *
    *   \forall x. p(x) <-> q(z), p(x) |-
    *   --------------------------------- equivRewriting(-1,-2)
    *   \forall x. p(x) <-> q(z), q(z) |-
    *
    *   \forall x. p(x) <-> q(z), q(z) |-
    *   --------------------------------- equivRewriting(-1,-2)
    *   \forall x. p(x) <-> q(z), p(z) |-
    *
    *   \forall x. p(x) <-> q(z), q(z) |-
    *   --------------------------------- equivRewriting(-1,-2)
    *   \forall x. p(x) <-> q(z), p(x) |-
    * }}}
    */
  @Tactic("equivRewriting", conclusion = "Γ, ∀X p(X) <-> q(X) |- p(Z), Δ", premises = "Γ, ∀X p(X) <-> q(X) |- q(Z), Δ")
  val equivRewriting: DependentTwoPositionTactic =  anon ((p: ProvableSig, equivPos: Position, targetPos: Position) => {
    assert(p.subgoals.length == 1, "Assuming one subgoal.")
    val target = p.subgoals(0)(targetPos).asInstanceOf[Formula]
    p.subgoals(0)(equivPos) match {
      case Equiv(_,_) => builtInEquivRewriting(equivPos, targetPos)
      case fa: Forall =>
        /*
         * Game plan:
         *   1. Compute the instantiation of p(equivPos) that matches p(targetPos)
         *   2. Cut in a new quantified equivalence
         *   3. Perform instantiations on this new quantified equivalence.
         *   4. perform instantiatedEquivRewritingImpl using the newly instantiated equivalence
         *   5. Hide the instantiated equivalence OR the original assumption.
         */
        //1
        val instantiation = computeInstantiation(fa, target)

        //2: input is p and output is postCut
        val cutPos = AntePos(p.subgoals.head.ante.length) //Position of equivalence to instantiate.
        val cutExpr = TactixLibrary.cut(fa) <(
          Idioms.nil,
          TactixLibrary.closeId(equivPos.checkAnte.top, SuccPos(p.subgoals.head.succ.length))
        )

        //3: input is postCut and output is instantiatedEquivalence
        val instantiatedEquivalence = vars(fa).foldLeft(cutExpr)((e: BelleExpr, x: Variable) => {
          e & FOQuantifierTactics.allInstantiate(Some(x), Some(instantiation(x)))(cutPos)
        })

        //step 5.
        val hidingTactic = if (targetPos.isAnte) TactixLibrary.hideL(targetPos) else TactixLibrary.hideL(cutPos)

        //4 & 5
        instantiatedEquivalence & builtInEquivRewriting(cutPos, targetPos) & hidingTactic
    }
  })

  private def computeInstantiation(fa: Forall, target: Formula): RenUSubst = {
    val equiv = bodyOf(fa)

    //@note it's important to only use the renaming; otherwise unification is too clever and comes up with predicate substitutions that cannot be achieved by instantiation alone.
    val leftRenaming: Option[RenUSubst] = try {
      val renaming = new UnificationMatchUSubstAboveURen().apply(equiv.left, target).renaming
      if (renaming.isEmpty) None
      else Some(renaming)
    } catch {
      case _: UnificationException => None
    }

    val rightRenaming: Option[RenUSubst] = try {
      val renaming = new UnificationMatchUSubstAboveURen().apply(equiv.right, target).renaming
      if (renaming.isEmpty) None
      else Some(renaming)
    } catch {
      case _: UnificationException => None
    }

    //First try to left-unify, then try to right-unify. I.e., default to left-rewriting when bot hare available.
    //@note This is also the default behavior of instantiatedEquivRewriting, and the two should be consistent on defaults.
    (leftRenaming, rightRenaming) match {
      case (Some(subst), _)  => logger.trace(s"Unified ${equiv.right} with $target under $subst"); subst
      case (None, Some(subst)) => logger.trace(s"Unified ${equiv.left} with $target under $subst"); subst
      case _ => RenUSubst(Nil) //Try to go ahead with an empty renaming since it will work more often than not.
    }
  }
  private def vars(fa: Forall): Seq[Variable] = fa.vars ++ (fa.child match {
    case child: Forall => vars(child)
    case e:Equiv => Nil
    case _ => throw new Exception("Expted equiv.")
  })
  @tailrec
  private def bodyOf(fa: Forall): Equiv = fa.child match {
    case child:Forall => bodyOf(child)
    case child:Equiv  => child
    case _            => throw new Exception(s"Expected a universally quantified equivalence but found ${fa.child.getClass}")
  }


  /**
    * Performs equivalence rewriting in either direction at any top-level position in a sequent,
    * leaving the original equivalence in place.
    *
    * Examples:
    * {{{
    *   P<->Q |- Q
    *   ----------- equivRewriting(-1, 1)
    *   P<->Q |- P
    * }}}
    *
    * {{{
    *   P<->Q, Q |-
    *   ------------ equivRewriting(-1, 1)
    *   P<->Q, P |-
    * }}}
    *
    * {{{
    *   P<->Q, P |-
    *   ------------ equivRewriting(-1, 1)
    *   P<->Q, Q |-
    * }}}
    */
  private def instantiatedEquivRewritingImpl(p: ProvableSig, equivPos: Position, targetPos: Position): ProvableSig = {
    import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
    assert(p.subgoals.length == 1, "Assuming one subgoal.")

    //@note equivalence == target <-> other.
    val equivalence: Equiv = p.subgoals.head(equivPos.checkAnte) match {
      case e:Equiv => e
      case f:Formula => throw new Exception(s"Expected an Equiv but found ${f.prettyString}")
      case e@_ => throw new Exception(s"Expected an Equiv formula but found ${e.prettyString}")
    }
    val targetValue : Formula = p.subgoals.head(targetPos.top)
    val otherValue : Formula = if(equivalence.left == targetValue) equivalence.right else equivalence.left

    val newEquivPos = AntePos(p.subgoals.head.ante.length)

    //First constraint a sequent that we can close as long as we know which positions to target with CloseId
    val postCut =
      p.apply(Cut(equivalence), 0)
        .apply(Close(equivPos.checkAnte.top, SuccPos(p.subgoals.head.succ.length)), 1)
        .apply(EquivLeft(newEquivPos), 0)
        .apply(AndLeft(newEquivPos), 0)
        .apply(AndLeft(newEquivPos), 1)

    if(targetPos.isAnte) {
      /*
       * Positive subgoal (A&B) is the result branch. Cleanup as follows:
       *    1. Ante reduces from
       *          G, {target, other} |- D
       *       to
       *          G', other |- D
       *       where G' is G with targetPos hidden, and {target, other} could occur in either direction.
       *       I.e., we just hid both the original targetPos and the new targetPos that came from breaking up the And.
       */
      val positiveSubgoalCleanup = {
        val redundantTargetPosition =
          if (postCut.subgoals(0).ante.last == targetValue) AntePos(postCut.subgoals(0).ante.length - 1)
          else AntePos(postCut.subgoals(0).ante.length - 2)

        postCut
          .apply(HideLeft(redundantTargetPosition), 0)
          .apply(HideLeft(targetPos.checkAnte.top), 0)
      }

      /*
       * Negative subgoal (!A&!B) closes:
       *   1. Identify location of negated other of equivalence
       *   2.
       */
      val negatedTargetPos =
        if(positiveSubgoalCleanup.subgoals(1).ante.last == Not(targetValue))
          AntePos(positiveSubgoalCleanup.subgoals(1).ante.length - 1)
        else
          AntePos(positiveSubgoalCleanup.subgoals(1).ante.length - 2)
      val unNegatedTargetPos = SuccPos(positiveSubgoalCleanup.subgoals(1).succ.length)

      positiveSubgoalCleanup
        .apply(NotLeft(negatedTargetPos), 1)
        .apply(Close(targetPos.checkAnte.top, unNegatedTargetPos), 1)
    }
    else { //targetPos is in the succedent.
      val anteTargetPos =
        if (postCut.subgoals(0).ante.last == targetValue) AntePos(postCut.subgoals(0).ante.length - 1)
        else AntePos(postCut.subgoals(0).ante.length - 2)

      val negatedOtherPos =
        if (postCut.subgoals(1).ante.last == Not(otherValue)) AntePos(postCut.subgoals(1).ante.length - 1)
        else AntePos(postCut.subgoals(1).ante.length - 2)

      postCut
        .apply(Close(anteTargetPos, targetPos.checkSucc.top), 0)
        .apply(HideRight(targetPos.checkSucc.top), 0) //@note these are not position 0 instead of position 1 because the other goal has now closed.
        .apply(NotLeft(negatedOtherPos), 0)
        .apply(HideLeft(AntePos(postCut.subgoals(1).ante.length-2)), 0)
    }
  }
  @Tactic("instantiatedEquivRewriting")
  val instantiatedEquivRewriting: BuiltInTwoPositionTactic = anon ((p: ProvableSig, equivPos: Position, targetPos: Position) => instantiatedEquivRewritingImpl(p, equivPos, targetPos))
  /** @todo explain why this exists and maybe find a better name. */
  private def builtInEquivRewriting(equivPos: Position, targetPos: Position) = new BuiltInTactic("") {
    override def result(p:ProvableSig) = instantiatedEquivRewritingImpl(p, equivPos, targetPos)
  }

  //endregion

}
