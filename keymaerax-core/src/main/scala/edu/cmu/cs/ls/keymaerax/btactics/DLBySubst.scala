package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.axiomatic
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, Position, PosInExpr, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper

import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps

/**
  * This is an example of how to implement some of the dL tactics using substitution tactics.
  * Created by nfulton on 11/3/15.
  */
object DLBySubst {
  /**
    * Box monotonicity.
    * {{{
    *      p |- q
    *   -------------monb
    *   [a]p |- [a]q
    * }}}
    */
  val monb = new NamedTactic("monb", {
    val pattern = SequentType(Sequent(Nil, IndexedSeq("[a_;]p_(??)".asFormula), IndexedSeq("[a_;]q_(??)".asFormula)))
    USubstPatternTactic(
      (pattern, (ru:RenUSubst) => ru.getRenamingTactic & axiomatic("[] monotone", ru.substitution.usubst))::Nil //@todo not sure about how to handle the renaming portion?
    )
  })

  /**
   * Diamond monotonicity.
   * {{{
   *      p |- q
   *   -------------mond
   *   <a>p |- <a>q
   * }}}
   */
  def mond = new NamedTactic("mond", {
    val pattern = SequentType(Sequent(Nil, IndexedSeq("<a_;>p_(??)".asFormula), IndexedSeq("<a_;>q_(??)".asFormula)))
    USubstPatternTactic(
      (pattern, (ru: RenUSubst) => ru.getRenamingTactic & axiomatic("<> monotone", ru.substitution.usubst)) :: Nil //@todo not sure about how to handle the renaming portion?
    )
  }

  /** G: Gödel generalization rule reduces a proof of `|- [a;]p(x)` to proving the postcondition `|- p(x)` in isolation.
    * {{{
    *       p(??)
    *   ----------- G
    *    [a;]p(??)
    * }}}
    * @see [[monb]] with p(x)=True
    */
  lazy val G = {
    val pattern = SequentType(Sequent(Nil, IndexedSeq(), IndexedSeq("[a_;]p_(??)".asFormula)))
    USubstPatternTactic(
      (pattern, (ru:RenUSubst) => ru.getRenamingTactic & axiomatic("Goedel", ru.substitution.usubst))::Nil
    )
  }

  /**
   * Returns a tactic to abstract a box modality to a formula that quantifies over the bound variables in the program
   * of that modality.
   * @example{{{
   *           |- \forall x x>0
   *         ------------------abstractionb(1)
   *           |- [x:=2;]x>0
   * }}}
   * @example{{{
   *           |- x>0 & z=1 -> [z:=y;]\forall x x>0
   *         --------------------------------------abstractionb(1, 1::1::Nil)
   *           |- x>0 & z=1 -> [z:=y;][x:=2;]x>0
   * }}}
   * @example{{{
   *           |- x>0
   *         ---------------abstractionb(1)
   *           |- [y:=2;]x>0
   * }}}
   * @return the abstraction tactic.
   */
  def abstractionb: DependentPositionTactic = new DependentPositionTactic("Abstraction") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(!pos.isAnte, "Abstraction only in succedent")
        sequent.at(pos) match {
          case (ctx, b@Box(prg, phi)) =>
            val vars = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.to[Seq]
            val diffies = vars.filter(v => v.isInstanceOf[DifferentialSymbol])
            if (diffies.nonEmpty) throw new IllegalArgumentException("abstractionb: found differential symbols " + diffies + " in " + b + "\nFirst handle those")
            val qPhi =
              if (vars.isEmpty) phi
              else
              //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
                vars.filter(v => v.isInstanceOf[Variable]).to[scala.collection.immutable.SortedSet].
                  foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))

            cut(Imply(ctx(qPhi), ctx(b))) <(
              /* use */ (implyL('Llast) <(hideR(pos.topLevel) partial /* result remains open */ , closeId)) partial,
              /* show */ cohide('Rlast) & implyR('Rlast) & assertT(1, 1) & implyRi &
              CMon(pos.inExpr) & implyR('_) & //PropositionalTactics.propCMon(pos.inExpr) &
              assertT(1, 1) & assertT(s => s.ante.head == qPhi && s.succ.head == b, s"Formula $qPhi and/or $b are not in the expected positions in abstractionb") &
              topAbstraction('Rlast) & closeId
              )
        }
      }
    }
  }

  /** Top-level abstraction: basis for abstraction tactic */
  private def topAbstraction: DependentPositionTactic = new DependentPositionTactic("Top-level abstraction") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(!pos.isAnte, "Abstraction only in succedent")
        sequent.sub(pos) match {
          case Some(b@Box(prg, phi)) =>
            val vars = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.to[Seq]
            val qPhi =
              if (vars.isEmpty) phi
              else
              //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
                vars.filter(v=>v.isInstanceOf[Variable]).to[scala.collection.immutable.SortedSet].
                  foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))

            cut(Imply(qPhi, Box(prg, qPhi))) <(
              /* use */ (implyL('Llast) <(
                hideR(pos.topLevel) partial /* result */,
                cohide2(new AntePosition(sequent.ante.length), pos.topLevel) &
                  assertT(1, 1) & assertE(Box(prg, qPhi), "abstractionb: quantified box")('Llast) &
                  assertE(b, "abstractionb: original box")('Rlast) & ?(monb) &
                  assertT(1, 1) & assertE(qPhi, "abstractionb: quantified predicate")('Llast) &
                  assertE(phi, "abstractionb: original predicate")('Rlast) & (allL('Llast)*vars.length) &
                  assertT(1, 1) & assertT(s => s.ante.head match {
                  case Forall(_, _) => phi match {
                    case Forall(_, _) => true
                    case _ => false
                  }
                  case _ => true
                }, "abstractionb: foralls must match") & closeId
                )) partial,
              /* show */ hideR(pos.topLevel) & implyR('Rlast) & V('Rlast) & closeId
            )
        }
      }
    }
  }

  /**
   * Box assignment by substitution assignment [v:=t();]p(v) <-> p(t()) (preferred),
   * or by equality assignment [x:=f();]p(??) <-> \forall x (x=f() -> p(??)) as a fallback.
   * Universal quantifiers are skolemized if applied at top-level in the succedent; they remain unhandled in the
   * antecedent and in non-top-level context.
   * @example{{{
   *    |- 1>0
   *    --------------------assignb(1)
   *    |- [x:=1;]x>0
   * }}}
   * @example{{{
   *           1>0 |-
   *    --------------------assignb(-1)
   *    [x:=1;]x>0 |-
   * }}}
   * @example{{{
   *    x_0=1 |- [{x_0:=x_0+1;}*]x_0>0
   *    ----------------------------------assignb(1)
   *          |- [x:=1;][{x:=x+1;}*]x>0
   * }}}
   * @example{{{
   *    \\forall x_0 (x_0=1 -> [{x_0:=x_0+1;}*]x_0>0) |-
   *    -------------------------------------------------assignb(-1)
   *                           [x:=1;][{x:=x+1;}*]x>0 |-
   * }}}
   * @example{{{
   *    |- [y:=2;]\\forall x_0 (x_0=1 -> x_0=1 -> [{x_0:=x_0+1;}*]x_0>0)
   *    -----------------------------------------------------------------assignb(1, 1::Nil)
   *    |- [y:=2;][x:=1;][{x:=x+1;}*]x>0
   * }}}
   * @see [[assignEquational]]
   */
  lazy val assignb: DependentPositionTactic =
    "[:=] assign" by (pos => (useAt("[:=] assign")(pos) partial) | (assignEquational(pos) partial))

  /**
   * Equational assignment: always introduces universal quantifier, which is skolemized if applied at top-level in the
   * succedent; it remains unhandled in the antecedent and in non-top-level context.
   * @example{{{
   *    x=1 |- [{x:=x+1;}*]x>0
   *    ----------------------------------assignEquational(1)
   *        |- [x:=1;][{x:=x+1;}*]x>0
   * }}}
   * @example{{{
   *    \\forall x (x=1 -> [{x:=x+1;}*]x>0) |-
   *    ---------------------------------------assignEquational(-1)
   *                 [x:=1;][{x:=x+1;}*]x>0 |-
   * }}}
   * @example{{{
   *    x_0=2 |- [y:=2;]\\forall x (x=1 -> [{x:=x+1;}*]x>0)
   *    ----------------------------------------------------assignEquational(1, 1::Nil)
   *    x=2   |- [y:=2;][x:=1;][{x:=x+1;}*]x>0
   * }}}
   */
  lazy val assignEquational: DependentPositionTactic = "[:=] assign equality" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(Assign(x, _), _)) =>
      val y = TacticHelper.freshNamedSymbol(x, sequent)
      ProofRuleTactics.boundRenaming(x, y) &
        useAt("[:=] assign equality")(pos) &
        (if (pos.isTopLevel && pos.isSucc) allR(pos) & implyR(pos) else ident) &
        // TODO derived axiom for equality with exists left for ante
        ProofRuleTactics.uniformRenaming(y, x)
  })

  /**
   * Generalize postcondition to C and, separately, prove that C implies postcondition.
   * The operational effect of {a;b;}@generalize(f1) is generalize(f1).
   * {{{
   *   genUseLbl:        genShowLbl:
   *   G |- [a]C, D      C |- B
   *   -------------------------
   *          G |- [a]B, D
   * }}}
   * @example{{{
   *   genUseLbl:        genShowLbl:
   *   |- [x:=2;]x>1     x>1 |- [y:=x;]y>1
   *   ------------------------------------generalize("x>1".asFormula)(1)
   *   |- [x:=2;][y:=x;]y>1
   * }}}
   * @example{{{
   *   genUseLbl:                      genShowLbl:
   *   |- a=2 -> [z:=3;][x:=2;]x>1     x>1 |- [y:=x;]y>1
   *   -------------------------------------------------generalize("x>1".asFormula)(1, 1::1::Nil)
   *   |- a=2 -> [z:=3;][x:=2;][y:=x;]y>1
   * }}}
   * @todo same for diamonds by the dual of K
   */
  def generalize(c: Formula): DependentPositionTactic = new DependentPositionTactic("generalize") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.at(pos) match {
        case (ctx, Box(a, _)) =>
          cutR(ctx(Box(a, c)))(pos) <(
            /* use */ /*label(BranchLabels.genUse)*/ ident,
            /* show */(cohide(pos.top) & CMon(pos.inExpr+1) & implyR(pos.top)) partial //& label(BranchLabels.genShow)
          )
      }
    }
  }

  /**
   * Prove the given cut formula to hold for the modality at position and turn postcondition into cut->post.
   * The operational effect of {a;}*@invariant(f1,f2,f3) is postCut(f1) & postcut(f2) & postCut(f3).
   * {{{
   *   cutUseLbl:           cutShowLbl:
   *   G |- [a](C->B), D    G |- [a]C, D
   *   ---------------------------------
   *          G |- [a]B, D
   * }}}
   * @example{{{
   *   cutUseLbl:                       cutShowLbl:
   *   |- [x:=2;](x>1 -> [y:=x;]y>1)    |- [x:=2;]x>1
   *   -----------------------------------------------postCut("x>1".asFormula)(1)
   *   |- [x:=2;][y:=x;]y>1
   * }}}
   * @example{{{
   *   cutUseLbl:                                     cutShowLbl:
   *   |- a=2 -> [z:=3;][x:=2;](x>1 -> [y:=x;]y>1)    |- [x:=2;]x>1
   *   -------------------------------------------------------------postCut("x>1".asFormula)(1, 1::1::Nil)
   *   |- a=2 -> [z:=3;][x:=2;][y:=x;]y>1
   * }}}
   * @todo same for diamonds by the dual of K
   */
  def postCut(C: Formula): DependentPositionTactic = new DependentPositionTactic("postCut") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      require(pos.isSucc, "postCut only in succedent")
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.at(pos) match {
        case (ctx, Box(a, post)) =>
          // [a](cut->post) and its position in assumptions
          val conditioned = Box(a, Imply(C, post))
          val conditional = AntePosition(sequent.ante.length)
          // [a]cut and its position in assumptions
          val cutted = Box(a, C)
          cutR(ctx(conditioned))(pos) <(
            /* use */ assertE(conditioned, "[a](cut->post)")(pos) partial, //& label(BranchLabels.cutUseLbl)
            /* show */
            assertE(Imply(ctx(conditioned),ctx(Box(a,post))),"original implication")(pos.top) & CMon(pos.inExpr) &
            implyR(pos.top) &
            assertE(Box(a,post), "original postcondition expected")(pos.top) &
            assertE(conditioned, "[a](cut->post)")(conditional) &
            cutR(cutted)(pos.top.asInstanceOf[SuccPos]) <(
              /* use */ assertE(cutted,"show [a]cut")(pos.top) & debug("showing post cut") &
              hide(conditioned)(conditional) partial /*& label(BranchLabels.cutShowLbl)*/,
              /* show */
              assertE(Imply(cutted,Box(a,post)),"[a]cut->[a]post")(pos.top) &
              debug("K reduction") & useAt("K modal modus ponens", PosInExpr(1::Nil))(pos.top) &
              assertE(Box(a, Imply(C,post)), "[a](cut->post)")(pos.top) & debug("closing by K assumption") &
              closeId
            ) partial
          )
      }
    }
  }

  /**
   * Loop induction. Wipes conditions that contain bound variables of the loop.
   * {{{
   *   use:                        init:        step:
   *   I, G\BV(a) |- p, D\BV(a)    G |- I, D    I, G\BV(a) |- [a]p, D\BV(a)
   *   --------------------------------------------------------------------
   *   G |- [{a}*]p, D
   * }}}
   * @example{{{
   *   use:          init:         step:
   *   x>1 |- x>0    x>2 |- x>1    x>1 |- [x:=x+1;]x>1
   *   ------------------------------------------------I("x>1".asFormula)(1)
   *   x>2 |- [{x:=x+1;}*]x>0
   * }}}
   * @example{{{
   *   use:               init:              step:
   *   x>1, y>0 |- x>0    x>2, y>0 |- x>1    x>1, y>0 |- [x:=x+y;]x>1
   *   ---------------------------------------------------------------I("x>1".asFormula)(1)
   *   x>2, y>0 |- [{x:=x+y;}*]x>0
   * }}}
   * @param invariant The invariant.
   * @return The tactic.
   */
  def I(invariant: Formula): DependentPositionTactic = new DependentPositionTactic("I") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      require(pos.isTopLevel && pos.isSucc, "I only at top-level in succedent, but got " + pos)
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(b@Box(Loop(a), p)) =>
          val consts = constAnteConditions(sequent, StaticSemantics(a).bv.toSet)
          val q =
            if (consts.size > 1) And(invariant, consts.reduceRight(And))
            else if (consts.size == 1) And(invariant, consts.head)
            else And(invariant, True)
          cut(Box(Loop(a), q)) <(
            /* use */
            implyRi(AntePos(sequent.ante.length), pos) & cohide('Rlast) & CMon(pos.inExpr+1) & implyR(1) &
              (if (consts.nonEmpty) andL('Llast)*consts.size else andL('Llast) & hide(True)('Llast)) partial /* indUse */,
            /* show */
            hide(b)(pos) & useAt("I induction")('Rlast) & andR('Rlast) <(
              andR('Rlast) <(ident /* indInit */, ((andR('Rlast) <(closeId, ident))*(consts.size-1) & closeId) | closeT) partial,
              cohide('Rlast) & G & implyR(1) & splitb(1) & andR(1) <(
                (if (consts.nonEmpty) andL('Llast)*consts.size else andL('Llast) & hide(True)('Llast)) partial /* indStep */,
                andL(-1) & hide(invariant)(-1) & V(1) & closeId) partial) partial)
      }

      private def constAnteConditions(sequent: Sequent, taboo: Set[NamedSymbol]): IndexedSeq[Formula] = {
        sequent.ante.filter(f => StaticSemantics.freeVars(f).intersect(taboo).isEmpty)
      }
    }
  }

  /**
   * Introduces a ghost.
   * @example{{{
   *         |- [y_0:=y;]x>0
   *         ----------------discreteGhost("y".asTerm)(1)
   *         |- x>0
   * }}}
   * @example{{{
   *         |- [z:=2;][y:=5;]x>0
   *         ---------------------discreteGhost("0".asTerm, Some("y".asVariable))(1, 1::Nil)
   *         |- [z:=2;]x>0
   * }}}
   * @param t The ghost specification.
   * @param ghost The ghost. If None, the tactic chooses a name by inspecting t (must be a variable then).
   * @return The tactic.
   * @incontext
   */
  def discreteGhost(t: Term, ghost: Option[Variable] = None): DependentPositionTactic = new DependentPositionTactic("discrete ghost") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.at(pos) match {
        case (ctx, f: Formula) =>
          //def g(f: Formula) = Equiv(Box(Assign(ghostV(f), t), SubstitutionHelper.replaceFree(f)(t, ghostV(f))), f)
          cutLR(ctx(Box(Assign(ghostV(f), t), SubstitutionHelper.replaceFree(f)(t, ghostV(f)))))(pos.topLevel) <(
            /* use */ ident,
            /* show */ cohide('Rlast) & CMon(pos.inExpr) & equivifyR(1) & byUS("[:=] assign")
            )
      }
    }
    // check specified name, or construct a new name for the ghost variable if None
    private def ghostV(f: Formula): Variable = ghost match {
      case Some(gv) => require(gv == t || (!StaticSemantics.symbols(f).contains(gv))); gv
      case None => t match {
        case v: Variable => TacticHelper.freshNamedSymbol(v, f)
        case _ => throw new IllegalArgumentException("Only variables allowed when ghost name should be auto-provided")
      }
    }
  }
}
