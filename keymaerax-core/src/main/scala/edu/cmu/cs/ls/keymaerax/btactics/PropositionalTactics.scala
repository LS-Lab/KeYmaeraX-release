package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import TacticFactory._
import edu.cmu.cs.ls.keymaerax.core.{Close, Cut, EquivLeft, NotLeft}
import edu.cmu.cs.ls.keymaerax.core._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.language.postfixOps

/**
 * [[PropositionalTactics]] provides tactics for propositional reasoning.
 */
private object PropositionalTactics {
  /**
   * Inverse of [[SequentCalculus.implyR]].
   * @author Nathan Fulton
   * @author Stefan Mitsch
   * @see [[SequentCalculus.implyR]]
   */
  lazy val implyRi: AppliedBuiltinTwoPositionTactic = implyRi()(AntePos(0), SuccPos(0))
  def implyRi(keep: Boolean = false): BuiltInTwoPositionTactic = "implyRi" by ((p: ProvableSig, a: Position, s: Position) => {
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
  lazy val orRi: DependentTactic = orRi()
  def orRi(pos1: SuccPos = SuccPos(0), pos2: SuccPos = SuccPos(1)): DependentTactic = new SingleGoalDependentTactic("inverse or right") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(pos1 != pos2, "Two distinct positions required")
      require(sequent.succ.length > pos1.getIndex && sequent.succ.length > pos2.getIndex,
        "Position " + pos1 + " or position " + pos2 + " is out of bounds; provable has succ size " + sequent.succ.length)
      val left = sequent.succ(pos1.getIndex)
      val right = sequent.succ(pos2.getIndex)
      val cutUsePos = AntePos(sequent.ante.length)
      cut(Or(left, right)) <(
        /* use */ orL(cutUsePos) & OnAll(TactixLibrary.close),
        /* show */
          if (pos1.getIndex > pos2.getIndex) (assertE(left, "")(pos1) & hideR(pos1) & assertE(right, "")(pos2) & hideR(pos2)) partial
          else (assertE(right, "")(pos2) & hideR(pos2) & assertE(left, "")(pos1) & hideR(pos1)) partial
        )
    }
  }

  /**
   * Inverse of [[ProofRuleTactics.andL]].
 *
   * @author Stefan Mitsch
   * @see [[ProofRuleTactics.andL]]
   */
  lazy val andLi: DependentTactic = andLi()
  def andLi(pos1: AntePos = AntePos(0), pos2: AntePos = AntePos(1)): DependentTactic = new SingleGoalDependentTactic("inverse and left") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(pos1 != pos2, "Two distinct positions required")
      require(sequent.ante.length > pos1.getIndex && sequent.ante.length > pos2.getIndex,
        "Position " + pos1 + " or position " + pos2 + " is out of bounds; provable has ante size " + sequent.ante.length)
      val left = sequent.ante(pos1.getIndex)
      val right = sequent.ante(pos2.getIndex)
      val cutUsePos = SuccPos(sequent.succ.length)
      cut(And(left, right)) <(
        /* use */
          if (pos1.getIndex > pos2.getIndex) (assertE(left, "")(pos1) & hideL(pos1) & assertE(right, "")(pos2) & hideL(pos2)) partial
          else (assertE(right, "")(pos2) & hideL(pos2) & assertE(left, "")(pos1) & hideL(pos1)) partial,
        /* show */ andR(cutUsePos) & OnAll(TactixLibrary.close)
        )
    }
  }

  /**
   * Returns a tactic for propositional CE with purely propositional unpeeling. Useful when unpeeled fact is not
   * an equivalence, as needed by CE. May perform better than CE for small contexts.
 *
   * @see [[UnifyUSCalculus.CMon(Context)]]
   * @see [[UnifyUSCalculus.CE(Context)]]
   * @example{{{
   *                  z=1 |- z>0
   *         --------------------------propCE(PosInExpr(1::Nil))
   *           x>0 -> z=1 |- x>0 -> z>0
   * }}}
   * @param at Points to the position to unpeel.
   * @return The tactic.
   */
  def propCMon(at: PosInExpr): DependentTactic = new SingleGoalDependentTactic("Prop. CMon") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.length == 1 && sequent.succ.length == 1 &&
        sequent.ante.head.at(at)._1 == sequent.succ.head.at(at)._1, s"Propositional CMon requires single antecedent " +
        s"and single succedent formula with matching context to $at, but got $sequent")

      // we know that we have the same operator in antecedent and succedent with the same lhs -> we know that one
      // will branch and one of these branches will close by identity. on the other branch, we have to hide
      // list all cases explicitly, hide appropriate formulas in order to not blow up branching
      (((notL(-1) & notR(1) & assertT(1, 1) partial)
        | ((andL(-1) & andR(1) <((close | (hideL(-2) partial)) partial, (close | (hideL(-1) partial)) partial) & assertT(1, 1) partial)
        | ((orR(1) & orL(-1) <((close | (hideR(2) partial)) partial, (close | (hideR(1) partial)) partial) & assertT(1, 1) partial)
        | ((implyR(1) & implyL(-1) <((close | (hideR(1) partial)) partial, (close | (hideL('Llast) partial)) partial) & assertT(1, 1) partial)
        | ((monb partial)
        | ((mond partial)
        | ((allR(1) & allL(-1) partial)
        | (existsL(-1) & existsR(1) partial)
        partial) partial) partial) partial) partial) partial) partial) partial)*at.pos.length
    }
  }

  /** @see [[SequentCalculus.modusPonens()]] */
  def modusPonens(assumption: AntePos, implication: AntePos): BelleExpr = new SingleGoalDependentTactic("Modus Ponens") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      val p = AntePos(assumption.getIndex - (if (assumption.getIndex > implication.getIndex) 1 else 0))
      //@note adapted to use implyL instead of implyLOld
      implyL(implication) <(
        cohide2(p, SuccPos(sequent.succ.length)) & close
        //@todo shouldn't this suffice? close(AntePosition(assumption), SuccPosition(SuccPos(sequent.succ.length)))
        ,
        Idioms.ident
        )
    }
  }

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
  val toSingleFormula: DependentTactic  = "toSingleFormula" by ((sequent: Sequent) => {
    cut(sequent.toFormula) <(
      /* use */ implyL('Llast) <(
        hideR(1)*sequent.succ.size & (andR(1) <(close, skip))*(sequent.ante.size-1) & onAll(close),
        hideL(-1)*sequent.ante.size & (orL(-1) <(close, skip))*(sequent.succ.size-1) & onAll(close)),
      /* show */ cohide('Rlast)
      )
  })

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
    val equivRewriting = "equivRewriting" byTactic ((p: ProvableSig, equivPos: Position, targetPos: Position) => {
      assert(p.subgoals.length == 1, "Assuming one subgoal.")
      val target = p.subgoals(0)(targetPos).asInstanceOf[Formula]
      p.subgoals(0)(equivPos) match {
        case Equiv(_,_) => builtInEquivRewriting(equivPos, targetPos)
        case fa: Forall => {
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
            TactixLibrary.close(equivPos.checkAnte.top, SuccPos(p.subgoals.head.succ.length))
          )

          //3: input is postCut and output is instantiatedEquivalence
          val instantiatedEquivalence = vars(fa).foldLeft(cutExpr)((e:BelleExpr,x:Variable) => {
            e & FOQuantifierTactics.allInstantiate(Some(x), Some(instantiation(x)))(cutPos)
          })

          //step 5.
          val hidingTactic = if(targetPos.isAnte) TactixLibrary.hideL(targetPos) else TactixLibrary.hideL(cutPos)

          //4 & 5
          instantiatedEquivalence & builtInEquivRewriting(cutPos, targetPos) & hidingTactic
        }
      }
    })

  private def computeInstantiation(fa: Forall, target: Formula): RenUSubst = {
    val allVars = vars(fa)
    val equiv   = bodyOf(fa)

    //@note it's important to only use the renaming; otherwise unification is too clever and comes up with predicate substitutions that cannot be achieved by instantiation alone.
    val leftRenaming: Option[RenUSubst] = try {
      val renaming = new UnificationMatchURenAboveUSubst().apply(equiv.left, target).renaming
      if(renaming.isEmpty) None
      else Some(new UnificationMatchURenAboveUSubst().apply(equiv.left, target).renaming)
    } catch {
      case _:Throwable => None
    } finally {
      None //Maybe we actually should not catch quite everything here?
    }

    val rightRenaming: Option[RenUSubst] = try {
      val renaming = new UnificationMatchURenAboveUSubst().apply(equiv.right, target).renaming
      if(renaming.isEmpty) None
      else Some(renaming)
    } catch {
      case _:Throwable => None
    } finally {
      None //Maybe we actually should not catch quite everything here?
    }

    //First try to left-unify, then try to right-unify. I.e., default to left-rewriting when bot hare available.
    //@note This is also the default behavior of instantiatedEquivRewriting, and the two should be consistent on defaults.
    (leftRenaming, rightRenaming) match {
      case (Some(subst), _)  => { println(s"Unified ${equiv.right} with ${target} under ${subst}"); subst }
      case (None, Some(subst)) => { println(s"Unified ${equiv.left} with ${target} under ${subst}"); subst }
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
  private def instantiatedEquivRewritingImpl(p: ProvableSig, equivPos: Position, targetPos: Position) = {
    import Augmentors._
    assert(p.subgoals.length == 1, "Assuming one subgoal.")

    //@note equivalence == target <-> other.
    val equivalence: Equiv = p.subgoals.head(equivPos.checkAnte) match {
      case e:Equiv => e
      case f:Formula => throw new Exception(s"Expected an Equiv but found ${f.prettyString}")
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
  val instantiatedEquivRewriting = "instantiatedEquivRewriting" by ((p: ProvableSig, equivPos: Position, targetPos: Position) => instantiatedEquivRewritingImpl(p, equivPos, targetPos))
  /** @todo explain why this exists and maybe find a better name. */
  private def builtInEquivRewriting(equivPos: Position, targetPos: Position) = new BuiltInTactic("") {
    override def result(p:ProvableSig) = instantiatedEquivRewritingImpl(p, equivPos, targetPos)
  }

  //endregion

}
