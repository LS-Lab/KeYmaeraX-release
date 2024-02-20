/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, SequentType, USubstPatternTactic}
import edu.cmu.cs.ls.keymaerax.core.Sequent
import BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.Ax.boxTrueAxiom
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Signature, TacticReservedSymbols}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.IndexedSeq
import scala.collection.mutable.ListBuffer
import scala.reflect.runtime.universe
import scala.util.{Failure, Success, Try}

/**
  * Implementation: some dL tactics using substitution tactics.
  * Created by nfulton on 11/3/15.
  */
private object DLBySubst extends TacticProvider {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (DLBySubst.getClass, universe.typeOf[DLBySubst.type])

  private[btactics] lazy val monb2 = byUS(Ax.monb2)

  /** whether games are currently allowed */
  private[this] val isGame: Boolean = Try({Dual(AssignAny(Variable("x"))); true}).getOrElse(false)

  /** @see [[HilbertCalculus.G]] */
  lazy val G: BelleExpr = {
    //@Tactic in [[HilbertCalculus.G]]
    //@todo optimizable why is this entire tactic not just TactixLibrary.by(Ax.Goedel)?
    val pattern = SequentType(Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};]p_(||)".asFormula)))
    //@todo ru.getRenamingTactic should be trivial so can be optimized away with a corresponding assert
    if (false && isGame) //@note true changes the shape maybe?
      USubstPatternTactic(
        (pattern, (ru:RenUSubst) =>
          cut(ru.substitution.usubst("[a_;]true".asFormula)) <(
            ru.getRenamingTactic & TactixLibrary.by(Ax.monb2, ru.substitution.usubst ++ USubst(
              SubstitutionPair(UnitPredicational("q_", AnyArg), True) :: Nil
            )) &
              hideL(-1, True)
            ,
            hide(1) & useAt(boxTrueAxiom)(1)
            ))::Nil)
    else
      USubstPatternTactic(
        (pattern, (ru:RenUSubst) => {
          Predef.assert(ru.getRenamingTactic == ident, "no renaming for Goedel")
          //ru.getRenamingTactic & by("Goedel", ru.substitution.usubst)
          TactixLibrary.by(Ax.Goedel, ru.usubst)
        })::Nil
    )
  }

  /** @see [[TactixLibrary.abstractionb]] */
  @Tactic(
    names = "GV",
    codeName = "GV", //@todo code name on cheat sheet is abstract
    longDisplayName = "Gödel Vacuous",
    premises   = "Γ<sub>const</sub> |- P, Δ<sub>const</sub>",
    //       GVR --------------------------------------------
    conclusion = "Γ |- [a]P, Δ",
    contextPremises = "Γ |- C( ∀x P ), Δ",
    contextConclusion = "Γ |- C( [a]P ), Δ",
    displayLevel = "all",
    revealInternalSteps = true)
  val abstractionb: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    require(!pos.isAnte, "Abstraction only in succedent")
    sequent.at(pos) match {
      case (ctx, b@Box(prg, phi)) =>
        val vars = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.toSeq
        val diffies = vars.filter(v => v.isInstanceOf[DifferentialSymbol])
        if (diffies.nonEmpty) throw new IllegalArgumentException("abstractionb: found differential symbols " + diffies + " in " + b + "\nFirst handle those")
        val qPhi =
          if (vars.isEmpty) phi
          else
          //@todo code quality needs improved
          //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
            vars.filter(v => v.isInstanceOf[BaseVariable]).map(v => v.asInstanceOf[NamedSymbol]).
              to(scala.collection.immutable.SortedSet).
              foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))

        cut(Imply(ctx(qPhi), ctx(b))) <(
          /* use */ implyL(Symbol("Llast")) <(hideR(pos.topLevel) /* result remains open */ , closeIdWith(Symbol("Llast"))),
          /* show */ cohide(Symbol("Rlast")) & CMon(pos.inExpr) & implyR(1) &
          assertT(1, 1) & assertT(s => s.ante.head == qPhi && s.succ.head == b, s"Formula $qPhi and/or $b are not in the expected positions in abstractionb") &
          topAbstraction(1) & id
          )
      case (_, e) => throw new TacticInapplicableFailure("GV only applicable to box properties, but got " + e.prettyString)
    }
  })

  /** Safe abstraction checks to not lose information from tests and evolution domain constraints before it abstracts. */
  @Tactic()
  val safeabstractionb: DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    // internal automation support
    seq.sub(pos) match {
      case Some(Box(prg, fml)) =>
        val fv = StaticSemantics.freeVars(fml)
        val bv = StaticSemantics.boundVars(prg)
        if (!bv.intersect(fv).isEmpty) throw new TacticInapplicableFailure("Abstraction would lose information from program")
        val fmls: ListBuffer[Formula] = ListBuffer.empty
        ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
            case Test(q) if q != True => fmls.append(q); Left(Some(ExpressionTraversal.stop))
            case ODESystem(_, q) if q != True => fmls.append(q); Left(Some(ExpressionTraversal.stop))
            case _ => Left(None)
          }
        }, prg)
        if (fmls.isEmpty) abstractionb(pos)
        else throw new TacticInapplicableFailure("Abstraction would lose information from tests and/or evolution domain constraints")
      case Some(e) => throw new TacticInapplicableFailure("Inapplicable tactic: expected formula of the shape [a;]p but got " +
        e.prettyString + " at position " + pos.prettyString + " in sequent " + seq.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  })

  /**
    * Introduces a self assignment [x:=x;]p(||) in front of p(||).
    * @param x The self-assigned variable.
    */
  @Tactic(
    names = "[:=]",
    longDisplayName = "Introduce Self-Assign",
    premises =   "Γ |- [x:=x]P, Δ",
    //      [:=] ------------------
    conclusion = "Γ |- P, Δ",
    displayLevel = "browse"
  )
  def stutter(x: Variable): DependentPositionWithAppliedInputTactic = inputanon { pos: Position => stutterFw(x)(pos) }
  private[btactics] def stutterFw(x: Variable): BuiltInPositionTactic = anon { (pr: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(pr, "stutter")
    val sequent = pr.subgoals.head
    sequent.at(pos) match {
      case (ctx, f: Formula) =>
        val (hidePos, commute) = if (pos.isAnte) (SuccPosition.base0(sequent.succ.size), commuteEquivR(1).computeResult _) else (pos.topLevel, skip.result _)
        (pr(cutLRFw(ctx(Box(Assign(x, x), f)))(pos).computeResult _, 0)
          (if (hidePos.isAnte) CoHideLeft(hidePos.checkAnte.top) else CoHideRight(hidePos.checkSucc.top), 1)
          (EquivifyRight(SuccPos(0)), 1)
          (commute, 1)
          (CEFw(pos.inExpr).result _, 1)
          (x match {
            case v: BaseVariable => US(Ax.selfassignb.provable(URename("x_".asVariable, v, semantic=true))).result _
            case DifferentialSymbol(v) => US(Ax.Dselfassignb.provable(URename("x_".asVariable, v, semantic=true))).result _
          }, 1)
          )
      case (_, e) => throw new TacticInapplicableFailure("stutter only applicable to formulas, but got " + e.prettyString)
    }
  }

  /** Top-level abstraction: basis for abstraction tactic */
  val topAbstraction: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    require(!pos.isAnte, "Abstraction only in succedent")
    sequent.sub(pos) match {
      case Some(b@Box(prg, phi)) =>
        val vars: scala.collection.immutable.SortedSet[Variable] = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.
          //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
          filter(_.isInstanceOf[Variable]).to(scala.collection.immutable.SortedSet)

        val qPhi = if (vars.isEmpty) phi else vars.foldRight(phi)((v, f) => Forall(v :: Nil, f))

        val diffRenameStep: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent(AntePos(0)) match {
            case Equal(x: Variable, x0: Variable) if sequent(AntePos(sequent.ante.size - 1)) == phi =>
              stutter(x0)(pos) & ProofRuleTactics.boundRename(x0, x)(pos.topLevel) &
                eqR2L(-1)(pos.topLevel) & useAt(Ax.selfassignb)(pos.topLevel) & hide(-1)
            case _ => throw new ProverException("Expected sequent of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
          })

        val diffRename: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
          //@note allL may introduce equations of the form x=x_0, but not necessarily for all variables
          if (sequent.ante.size == 1 && sequent.succ.size == 1 && sequent.ante.head == sequent.succ.head) ident
          else if (sequent.ante.size <= 1 + vars.size && sequent.succ.size == 1) sequent(AntePos(0)) match {
            case Equal(_, _) if sequent(AntePos(sequent.ante.size - 1)) == phi => diffRenameStep(pos)*(sequent.ante.size - 1)
            case _ => throw new ProverException("Expected sequent of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
          }
          else throw new ProverException("Expected sequent either of the form p(x) |- p(x)\n or of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
        })

        cut(Imply(qPhi, Box(prg, qPhi))) <(
          /* use */ (implyL(Symbol("Llast")) <(
            hideR(pos.topLevel) /* result */,
            cohide2(AntePosition(sequent.ante.length + 1), pos.topLevel) &
              assertT(1, 1) & assertE(Box(prg, qPhi), "abstractionb: quantified box")(Symbol("Llast")) &
              assertE(b, "abstractionb: original box")(Symbol("Rlast")) & ?(monb) &
              assertT(1, 1) & assertE(qPhi, "abstractionb: quantified predicate")(Symbol("Llast")) &
              assertE(phi, "abstractionb: original predicate")(Symbol("Rlast")) & (allL(Symbol("Llast"))*vars.size) &
              diffRename(1) &
              assertT(1, 1) & assertT(s => s.ante.head match {
                case Forall(_, _) => phi match {
                  case Forall(_, _) => true
                  case _ => false
                }
                case _ => true
              }, "abstractionb: foralls must match") & id
            )),
          /* show */ hideR(pos.topLevel) & implyR(Symbol("Rlast")) & V(Symbol("Rlast")) & closeIdWith(Symbol("Llast"))
        )
      case Some(e) => throw new TacticInapplicableFailure("Top-level abstraction only applicable to box properties, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
  })

    /**
    * Equality assignment to a fresh variable.
    * Introduces a universal quantifier when applied in the succedent/existential quantifier in the antecedent,
    * which is already skolemized if applied at top-level; quantifier remains unhandled in non-top-level context.
    *
    * @example {{{
    *    x_0=x+1 |- [{x_0:=x_0+1;}*]x_0>0
    *    ----------------------------------assignEquality(1)
    *        |- [x:=x+1;][{x:=x+1;}*]x>0
    * }}}
    * @example {{{
    *    x_0=x+1, [{x_0:=x_0+1;}*]x_0>0) |-
    *    ------------------------------------ assignEquality(-1)
    *           [x:=x+1;][{x:=x+1;}*]x>0 |-
    * }}}
    * @example Other uses of the variable in the context remain unchanged.
    * {{{
    *    x=2 |- [y:=2;]\\forall x_0 (x_0=x+1 -> [{x_0:=x_0+1;}*]x_0>0)
    *    -------------------------------------------------------------- assignEquality(1, 1::Nil)
    *    x=2   |- [y:=2;][x:=x+1;][{x:=x+1;}*]x>0
    * }}}
    * @author Andre Platzer
    * @incontext
    */
  @Tactic(
    names = "[:=]=",
    longDisplayName = "Assign Equality",
    premises =   "Γ, x=e |- P, Δ",
    //    [:=]=  ------------------
    conclusion = "Γ |- [x:=e]P, Δ",
    displayLevel = "all"
  )
  private[btactics] val assignEquality: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "DLBySubst.assignEqualityFw")
    val sequent = provable.subgoals.head
    val (expand: (ProvableSig=>ProvableSig), assign: (ProvableSig=>ProvableSig)) = sequent.sub(pos) match {
      //@note have already failed assigning directly so grab fresh name index otherwise
      // [x:=f(x)]P(x)
      case Some(Box(a@Assign(x, e), p)) =>
        val universal = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(sequent(pos.top), pos.inExpr) >= 0
        val assignAx = x match {
          case v: BaseVariable =>
            if (universal) Ax.assignbeq.provable(URename("x_".asVariable, v, semantic = true))
            else Ax.assignbequalityexists.provable(URename("x_".asVariable, v, semantic = true))
          case DifferentialSymbol(v) =>
            if (universal) Ax.Dassignbeq.provable(URename("x_".asVariable, v, semantic = true))
            else Ax.Dassignbequalityexists.provable(URename("x_".asVariable, v, semantic = true))
        }

        val skolemize: ProvableSig=>ProvableSig =
          if (pos.isTopLevel && pos.isSucc) allR(pos) andThen implyR(pos)
          else if (pos.isTopLevel && pos.isAnte) existsL(pos) andThen andL(Symbol("Llast"))
          else ident

        if (StaticSemantics.freeVars(p).contains(x) && StaticSemantics.freeVars(p).isInfinite) {
          if (StaticSemantics.freeVars(e).contains(x)) {
            // case [x:=x+1;][prg;]
            StaticSemantics.symbols(p).
              filter({ case _: SystemConst | _: ProgramConst => true case _ => false }).
              map(n => expandFw(n, None)).
              reduceRightOption[ProvableSig=>ProvableSig](_ andThen _) match {
              case Some(expand) => (expand, assignEquality(pos))
              case None => throw new TacticInapplicableFailure("Assignment " + a.prettyString +
                " prevented since " + e.prettyString + " overlaps with the bound and (infinite) free variables of " + p.prettyString)
            }
          } else {
            // case [x:=y;][prg;]
            (ident, useAt(assignAx)(pos) andThen skolemize)
          }
        } else {
          if (x.isInstanceOf[BaseVariable] && StaticSemantics.freeVars(p).symbols.contains(DifferentialSymbol(x))) {
            (ident, useAt(assignAx)(pos) andThen skolemize andThen
              (if (pos.isTopLevel && pos.isSucc) eqL2R(AntePosition.base0(sequent.ante.length))(pos, p) andThen hideL(Symbol("Llast"))
              else if (pos.isTopLevel && pos.isAnte) eqL2R(AntePosition.base0(sequent.ante.length - 1))(Symbol("Llast"), p) andThen hideL(AntePosition.base0(sequent.ante.length - 1))
              else ident))
          } else {
            //@note boundRename and uniformRename for ODE/loop postconditions, and also for the desired effect of "old" having indices and "new" remaining x
            x match {
              case _: BaseVariable =>
                if (StaticSemantics.freeVars(p).isInfinite) (ident, useAt(assignAx)(pos) andThen skolemize)
                else {
                  val y = TacticHelper.freshNamedSymbol(x, sequent)
                  (ident, ProofRuleTactics.boundRenameFw(x, y)(pos) andThen useAt(assignAx)(pos) andThen ProofRuleTactics.uniformRenameFw(y, x) andThen skolemize)
                }
              case _: DifferentialSymbol => (ident, useAt(assignAx)(pos) andThen skolemize)
            }
          }
        }
      case Some(e) => throw new TacticInapplicableFailure("assignEquality only applicable to box assignments [x:=t;], but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
    expand(provable)(expand andThen assign, 0)
  }

  /** Equality assignment to a fresh variable. @see assignEquality @incontext */
  @Tactic(
    names = "<:=>=",
    longDisplayName = "Assign Equality",
    premises =   "Γ, x=e |- P, Δ",
    //     <:=>= -----------------
    conclusion = "Γ |- ⟨x:=e⟩P, Δ",
    displayLevel = "all"
  )
  private[btactics] val assigndEquality: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "DLBySubst.assigndEquality")
    val sequent = provable.subgoals.head
    sequent.sub(pos) match {
      //@note have already failed assigning directly so grab fresh name index otherwise
      // [x:=f(x)]P(x)
      case Some(Diamond(Assign(x, t), p)) =>
        val y = TacticHelper.freshNamedSymbol(x, sequent)
        val universal = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(sequent(pos.top), pos.inExpr) >= 0
        provable(
          ProofRuleTactics.boundRenameFw(x, y)(pos) andThen
          useAt(if (universal) Ax.assigndEqualityAll else Ax.assigndEqualityAxiom)(pos) andThen
          ProofRuleTactics.uniformRenameFw(y, x) andThen
          (if (pos.isTopLevel && pos.isSucc) allR(pos) andThen implyR(pos)
           else if (pos.isTopLevel && pos.isAnte) existsL(pos) andThen andL(Symbol("Llast"))
           else ident), 0)
      case Some(e) => throw new TacticInapplicableFailure("assigndEquality only applicable to diamond assignments <x:=t;>, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
  }

  /** @see [[TactixLibrary.generalize()]]
   * @todo same for diamonds by the dual of K
   */
  def generalize(c: Formula, isGame: Boolean = false): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.at(pos) match {
    //@Tactic in [[HybridProgramCalculus.generalize]]
    case (ctx, Box(a, _)) =>
      val ov = FormulaTools.argsOf(TacticReservedSymbols.old, c)

      var freshOld: Variable = TacticHelper.freshNamedSymbol(Variable(TacticReservedSymbols.old.name), sequent)
      val ghosts: List[((Term, Variable), BelleExpr)] = ov.map(old => {
        val (ghost: Variable, ghostPos: Option[Position], nextCandidate) = TacticHelper.findSubst(old, freshOld, sequent)
        freshOld = nextCandidate
        (old -> ghost,
          ghostPos match {
            case Some(gp) if pos.isTopLevel => TactixLibrary.exhaustiveEqR2L(hide=false)(gp)
            case _ => discreteGhost(old, Some(ghost))(pos)
          })
      }).toList
      val posIncrements = if (pos.isTopLevel) 0 else ghosts.size
      val afterGhostsPos = pos ++ PosInExpr(List.fill(posIncrements)(1))

      val oldifiedC = SubstitutionHelper.replaceFn(TacticReservedSymbols.old, c, ghosts.map(_._1).toMap)
      val oldifiedA = ghosts.foldLeft(a)({case (prg, ((w, r), _)) => SubstitutionHelper.replaceFree(prg)(w, r) })
      val introduceGhosts = ghosts.map(_._2).reduceOption(_ & _).getOrElse(skip)

      val (q, useCleanup, showCleanup) = {
        val aBVs = StaticSemantics.boundVars(a)
        val constConjuncts =
          if (aBVs.isInfinite) Nil
          else sequent.ante.map(fml =>
            ghosts.foldLeft(fml)({ case (f, ((what, repl), _)) => SubstitutionHelper.replaceFree(f)(what, repl) })).
            flatMap(FormulaTools.conjuncts).
            filter(StaticSemantics.freeVars(_).intersect(aBVs.toSet).isEmpty).toList
        (constConjuncts, isGame) match {
          case (Nil, _) | (_, true) => (oldifiedC, skip, implyR(1))
          case (consts, false) => (And(consts.reduceRight(And), oldifiedC),
              boxAnd(afterGhostsPos) &
              abstractionb(afterGhostsPos ++ PosInExpr(0 :: Nil)) &
              (if (afterGhostsPos.isTopLevel) andR(afterGhostsPos) & Idioms.<(prop & done, skip)
              else skip),
              implyR(1) & andL(-1)
          )
        }
      }
      label(startTx) & introduceGhosts & cutR(ctx(Box(oldifiedA, q)))(afterGhostsPos.checkSucc.top) < (
        /* use */ useCleanup & label(replaceTxWith(BelleLabels.mrUse)),
        /* show */ cohide(afterGhostsPos.top) & CMon(afterGhostsPos.inExpr ++ 1) & showCleanup & label(replaceTxWith(BelleLabels.mrShow))
      )
    case (_, e) => throw new TacticInapplicableFailure("MR only applicable to box, but got " + e.prettyString)
  })
  /** @see [[TactixLibrary.postCut()]]
   * @todo same for diamonds by the dual of K
   * @note Uses K modal modus ponens, which is unsound for hybrid games.
   */
  @Tactic(
    longDisplayName = "Cut in Postcondition",
    premises =   "Γ |- [a]C, Δ ;; Γ |- [a](C→P)",
    //   postCut -------------------------------
    conclusion = "Γ |- [a]P, Δ",
    displayLevel = "browse"
  )
  def postCut(C: Formula): DependentPositionWithAppliedInputTactic = inputanon (useAt(Ax.K, PosInExpr(1::1::Nil),
    (us: Option[Subst]) => us.getOrElse(throw new UnsupportedTacticFeature("Unexpected missing substitution in postCut")) ++ RenUSubst(("p(||)".asFormula, C)::Nil))(_: Position) <(
    label(BelleLabels.cutUse),
    label(BelleLabels.cutShow)
  ))

  /** Returns conditions in `fmls` that are unaffected by `taboo`, expanding formulas according to `defs` to determine
    * the free variables of their constituent subformulas. */
  private def constConditions(fmls: IndexedSeq[Formula], taboo: SetLattice[Variable], defs: Declaration = Declaration(Map.empty)): IndexedSeq[Formula] = {
    fmls.flatMap(FormulaTools.conjuncts).flatMap({
      case p: PredOf => FormulaTools.conjuncts(defs.exhaustiveSubst[Formula](p))
      case f => FormulaTools.conjuncts(f)
    }).filter(StaticSemantics.freeVars(_).intersect(taboo).isEmpty)
  }

  /** Expand definitions in non-loop formulas as preparation for [[loop]], which searches preconditions for constants
    * to preserve but cannot look up definitions. */
  private def expandNonloop: BelleExpr = SaturateTactic(alphaRule) & SaturateTactic(anon ((seq: Sequent) => {
    ???
  }) & SaturateTactic(alphaRule)) & DebuggingTactics.print("Loop expanded")

  /** @see [[TactixLibrary.loop]] */
  def loop(invariant: Formula, pre: BelleExpr = SaturateTactic(alphaRule)): DependentPositionTactic = inputanon { (pos: Position, sequent: Sequent, defs: Declaration) =>
    //@Tactic see [[HybridProgramCalculus.loop]]
    require(pos.isTopLevel && pos.isSucc, "Tactic loop applicable only at top-level in succedent, but got position " +
      pos.prettyString + ". Please apply more proof steps until the loop is top-level or use [*] iterateb instead.")

    //@note restrict to definitions that mention old(.) transitively
    val invOldsDefs = Declaration(defs.decls.filter({
      case (_, Signature(_, _, _, Right(interp), _)) =>
        interp.map(s => StaticSemantics.symbols(defs.exhaustiveSubst(s))).getOrElse(Set.empty).contains(TacticReservedSymbols.old)
      case _ => false
    }))
    val substInv = invOldsDefs.exhaustiveSubst(invariant)
    val ov = FormulaTools.argsOf(TacticReservedSymbols.old, substInv)
    val doloop = (ghosts: List[((Term, Variable), BelleExpr)]) => {
      val posIncrements = PosInExpr(List.fill(if (pos.isTopLevel) 0 else ghosts.size)(1))
      val oldified = SubstitutionHelper.replaceFn(TacticReservedSymbols.old, substInv, ghosts.map(_._1).toMap)
      val afterGhostsPos = if (ghosts.nonEmpty) LastSucc(0, posIncrements) else Fixed(pos.topLevel ++ posIncrements)
      val expandPrg = if (ghosts.nonEmpty) {
        sequent.sub(pos) match {
          case Some(Box(Loop(a), _)) =>
            val toExpand = defs.transitiveSubstsFrom(a)
            if (toExpand.nonEmpty) expandAllDefs(toExpand)
            else skip
          case _ => skip
        }
      } else skip
      expandPrg & ghosts.map(_._2).reduceOption(_ & _).getOrElse(skip) & inputanon {(pos, sequent) => sequent.sub(pos) match {
        case Some(Box(Loop(a), _)) =>
          if (!FormulaTools.dualFree(a)) loopRule(oldified)(pos)
          else {
            val abv = {
              val verbatimabv = StaticSemantics(a).bv
              if (verbatimabv.isInfinite) StaticSemantics(defs.exhaustiveSubst(a)).bv
              else verbatimabv
            }
            val constSuccs = (constConditions(sequent.succ, abv, defs) :+ False).map(Not)
            val constAntes = constConditions(sequent.ante, abv, defs)
            val consts = constAntes ++ constSuccs
            val q =
              if (consts.size > 1) And(oldified, consts.reduceRight(And))
              else if (consts.size == 1) And(oldified, consts.head)
              else And(oldified, True)

            val expandInit = anon ((s: Sequent) => {
              val toExpand = defs.transitiveSubstsFrom(s.toFormula)
              if (toExpand.nonEmpty) expandAllDefs(toExpand)
              else skip
            })
            val expandPrg =
              if (consts.flatMap(StaticSemantics.symbols).exists(_.isInstanceOf[Variable]) && StaticSemantics.boundVars(a).isInfinite) {
                val asymbols = StaticSemantics.symbols(a)
                expandAllDefs(defs.substs.filter({
                  case SubstitutionPair(p: ProgramConst, _) => asymbols.contains(p)
                  case SubstitutionPair(p: SystemConst, _) => asymbols.contains(p)
                  case _ => false
                }))
              }
              else skip

            label(startTx) &
            cutR(Box(Loop(a), q))(pos.checkSucc.top) <(
              /* c */ useAt(Ax.I)(pos) & andR(pos) <(
                andR(pos) <(
                  label(replaceTxWith(initCase)),
                  (andR(pos) <(expandInit & SaturateTactic(andL(Symbol("L"))) & closeIdWith(pos), TactixLibrary.nil))*constAntes.size &
                    (andR(pos) <(notR(pos) & closeIdWith(Symbol("Llast")), TactixLibrary.nil))*(constSuccs.size-1) &
                    notR(pos) & SaturateTactic(andL(Symbol("L"))) & close & done),
                cohide(pos) & G & implyR(1) & boxAnd(1) & andR(1) <(
                  (if (consts.nonEmpty) andL(Symbol("Llast"))*consts.size & hideL(Symbol("Llast"), Not(False)) & notL(Symbol("Llast"))*(constSuccs.size-1)
                   else andL(Symbol("Llast")) & hideL(Symbol("Llast"), True)) & label(replaceTxWith(indStep)),
                  andL(-1) & hideL(-1, oldified) & expandPrg & V(1) & close(-1, 1) & done)
              ),
              /* c -> d */
              cohide(pos) & CMon(pos.inExpr++1) & implyR(1) &
              andL(Symbol("Llast"))*consts.size & hideL(Symbol("Llast"), Not(False)) & notL(Symbol("Llast"))*(constSuccs.size-1) &
              label(replaceTxWith(useCase))
            )
          }
        case Some(e) => throw new TacticInapplicableFailure("loop only applicable to box loop [{}*] properties, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
      }}(afterGhostsPos)
    }
    pre & discreteGhosts(ov, sequent, doloop)(pos)
  }

  /** Analyzes a loop for counterexamples. */
  def cexLoop(inv: Formula): DependentPositionTactic = anon ((pos: Position, seq: Sequent, defs: Declaration) => {
    val cexProgram = unfoldProgramNormalize & OnAll(
      Idioms.doIfElse(_.subgoals.forall(_.isFOL))(
        //@todo nested loops, loops in postcondition, ODEs in postcondition
        expandAllDefs(Nil) & ToolTactics.assertNoCex,
        ToolProvider.invGenTool().map(t => {
          anon((pos: Position, seq: Sequent, defs: Declaration) => {
            val sexp = defs.exhaustiveSubst(seq)
            sexp.sub(pos) match {
              case Some(Box(ode: ODESystem, post)) =>
                val preImpPostCEX = Try(TactixLibrary.findCounterExample(Imply(sexp.ante.reduceRightOption(And).getOrElse(True), post))).getOrElse(None)
                if (preImpPostCEX.isDefined) throw BelleCEX("ODE Counterexample", preImpPostCEX.get, sexp)
                else Try(t.refuteODE(ode, sexp.ante, post)) match {
                  case Success(None) => skip
                  case Success(Some(cex)) => throw BelleCEX("ODE Counterexample", cex, sexp)
                  case Failure(_) => skip
                }
              case _ => skip
            }
          })(pos)
        }).getOrElse(skip)
      )
    )

    seq.sub(pos) match {
      case Some(Box(Loop(_), post)) =>
        // proveBy throws BelleCEX when counterexamples found
        proveBy(ProvableSig.startProof(seq, defs),
          //@note uses loop to preserve constants/initial conditions consistently
          loop(inv)(pos) <(
            //@todo support for non-FOL invariant
            expandAllDefs(Nil) & ToolTactics.assertNoCex,
            Idioms.doIfElse(_.subgoals.forall(_.isFOL))(expandAllDefs(Nil) & ToolTactics.assertNoCex, cexProgram),
            (if (!post.isFOL) chase(pos ++ PosInExpr(1::Nil)) else skip) & cexProgram
          )
        )
        // if proveBy succeeds, no CEX was found, so skip. otherwise BelleCEX was thrown from within proveBy.
        skip
    }
  })

  /**
    * Loop induction wiping all context.
    * {{{
    *   init:        step:       use:
    *   G |- I, D    I |- [a]I   I |- p
    *   --------------------------------
    *   G |- [{a}*]p, D
    * }}}
    *
    * @param invariant The invariant.
    */
  @Tactic(
    longDisplayName = "Loop Rule",
    premises =   "Γ |- J, Δ ;; J |- [a]J ;; J |- P",
    //  loopRule -----------------------------------
    conclusion = "Γ |- [a<sup>*</sup>]P, Δ"
  )
  def loopRule(J: Formula): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position, seq: Sequent) =>
    require(pos.isTopLevel && pos.isSucc, "loopRule only at top-level in succedent, but got " + pos)
    seq.sub(pos) match {
      case Some(Box(Loop(a),_)) =>
        label(startTx) &
        cutR(J)(pos.checkSucc.top) <(
          label(replaceTxWith(BelleLabels.initCase)),
          cohide(pos) & implyR(1) & generalize(J, isGame = !FormulaTools.dualFree(a))(1) <(
            byUS(Ax.indrule) & label(replaceTxWith(BelleLabels.indStep))
            ,
            label(replaceTxWith(BelleLabels.useCase))
          )
        )
      case _ => throw new IllegalArgumentException("requirement failed: only applicable for [a*]p(||)")
    }
  }

  /** @see [[TactixLibrary.throughout]] */
  @Tactic(
    longDisplayName = "Loop Throughout Invariant",
    premises =    "Γ |- J, Δ ;; J |- [a]J ;; J |- [b]J ;; J |- P",
    // throughout ------------------------------------------------
    conclusion =  "Γ |- [{a;b}<sup>*</sup>]P, Δ",
    displayLevel = "browse"
  )
  def throughout(J: Formula): DependentPositionWithAppliedInputTactic = inputanon (throughout(J, SaturateTactic(alphaRule))(_: Position))
  def throughout(invariant: Formula, pre: BelleExpr): DependentPositionWithAppliedInputTactic = inputanon ((pos: Position) => {
    require(pos.isTopLevel && pos.isSucc, "throughout only at top-level in succedent, but got " + pos)
    lazy val split: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(Box(Compose(_, _), _)) => composeb(pos) & generalize(invariant)(pos) & Idioms.<(skip, split(pos))
      case _ => skip
    })

    loop(invariant, pre)(pos) & Idioms.<(
      skip,
      skip,
      split(pos)
    )})

  /** [[TactixLibrary.fp()]] */
  def fpRule(fixpoint: Formula): DependentPositionWithAppliedInputTactic = inputanon {(pos: Position, seq: Sequent) =>
    require(pos.isTopLevel && pos.isAnte, "fp fixpoint only at top-level in antecedent, but got " + pos)
    require(seq(pos) match { case Diamond(Loop(_),_) => true case _ => false }, "only applicable for <a*>p(||)")
    label(startTx) &
      cut(fixpoint) <(
        label(replaceTxWith(BelleLabels.fixUseCase))
        ,
        cohide2(pos, SuccPosition(seq.succ.length+1/*'Rlast*/)) & byUS(Ax.FPrule) & label(replaceTxWith(BelleLabels.fixpoint))
      )
  }

  /** [[TactixLibrary.con()]] */
  @Tactic(
    longDisplayName = "Loop Convergence",
    premises =          "Γ |- ∃x J(x) ;; x≤0, J(x) |- P ;; x>0, J(x) |- ⟨a⟩J(x-1)",
    // Loop Convergence -----------------------------------------------------------
    conclusion =        "Γ |- ⟨a<sup>*</sup>⟩P, Δ",
    inputs = "x[x]:variable;;J(x)[x]:formula",
    displayLevel = "all"
  )
  def con(x: Variable, J: Formula): DependentPositionWithAppliedInputTactic = inputanon (con(x, J, SaturateTactic(alphaRule))(_: Position))
  def con(v: Variable, variant: Formula, pre: BelleExpr): DependentPositionWithAppliedInputTactic = inputanon ((pos: Position, sequent: Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "con only at top-level in succedent, but got " + pos)
    require(sequent(pos.top) match { case Diamond(Loop(_), _) => true case _ => false }, "only applicable for <a*>p(||), but got " + sequent(pos.top).prettyString + "\nin " + sequent.prettyString)

    pre & (inputanon {(pp, seq) => {
      seq.sub(pp) match {
        case Some(Diamond(prg: Loop, _)) if !FormulaTools.dualFree(prg) => conRule(v, variant)(pos)
        case Some(d@Diamond(prg@Loop(a), p)) if  FormulaTools.dualFree(prg) =>
          val ur = URename(Variable("x_",None,Real), v)
          val abv = StaticSemantics(a).bv
          val consts = constConditions(seq.ante, abv)
          val q =
            if (consts.size > 1) And(ur(variant), consts.reduceRight(And))
            else if (consts.size == 1) And(ur(variant), consts.head)
            else And(ur(variant), True)

          val x1 = Variable(ur.what.name, Some(ur.what.index.getOrElse(-1)+1)) //@note avoid clash with x_ when assignd uses assigndEquality
          val x2 = Variable(x1.name, Some(x1.index.get+1))          //@note result after assigndEquality
          val v0 = Variable(v.name, Some(v.index.getOrElse(-1)+1))  //@note want v__0 in result instead of x2

          def closeConsts(pos: Position) = andR(pos) <(skip, onAll(andR(pos) <(id, skip))*(consts.size-1) & close)
          val splitConsts = if (consts.nonEmpty) andL(Symbol("Llast"))*consts.size else useAt(Ax.andTrue)(Symbol("Llast"))

          val abvVars = abv.toSet[Variable].filter(_.isInstanceOf[BaseVariable]).toList
          def stutterABV(pos: Position) = abvVars.map(stutter(_)(pos)).reduceOption[BelleExpr](_&_).getOrElse(skip)
          def unstutterABV(pos: Position) = useAt(Ax.selfassignb)(pos)*abvVars.size

          label(startTx) &
          cutR(Exists(ur.what :: Nil, q))(pp.checkSucc.top) <(
            stutter(ur.what)(pos ++ PosInExpr(0::0::Nil)) &
            useAt(Ax.pexistsV)(pos) & closeConsts(pos) &
            assignb(pos ++ PosInExpr(0::Nil)) & uniformRename(ur) & label(replaceTxWith(BelleLabels.initCase))
            ,
            cohide(pp) & implyR(1) & byUS(Ax.conflat) <(
              existsL(Symbol("Llast")) & andL(Symbol("Llast")) & splitConsts & uniformRename(ur) & label(replaceTxWith(BelleLabels.useCase))
              ,
              stutter(ur.what)(1, 1::1::0::Nil) &
              useAt(Ax.pVd, PosInExpr(1::Nil))(1, 1::Nil) &
              assignb(1, 1::0::1::Nil) &
              stutterABV(SuccPosition.base0(0, PosInExpr(1::0::Nil))) &
              useAt(Ax.pVd, PosInExpr(1::Nil))(1) &
              unstutterABV(SuccPosition.base0(0, PosInExpr(0::1::Nil))) &
              splitConsts & closeConsts(SuccPos(0)) &
              (assignd(1, 1 :: Nil) & uniformRename(ur) |
                uniformRename(ur.what, x1) & assignd(1, 1 :: Nil) & boundRename(x1, v)(1, 1::Nil) & uniformRename(x2, v0)
                ) & label(replaceTxWith(BelleLabels.indStep))
            )
          )
      }
    }})(pos)
  })

  /**
    * Loop convergence wiping all context.
    * {{{
    *   init:                       use:                  step:
    *   G |- exists x. J(x), D    x<=0, J(x) |- p     x>0, J(x) |- <a>J(x-1)
    *   --------------------------------------------------------------------------
    *   G |- <{a}*>p, D
    * }}}
    * @param J The variant property or convergence property in terms of new variable `x`.
    * @example The variant J(x) ~> (x = z) is specified as x=="x".asVariable, variant == "x = z".asFormula
    */
  @Tactic(
    longDisplayName = "Loop Convergence Rule",
    premises =   "Γ |- ∃x J(x) ;; x≤0, J(x) |- P ;; x>0, J(x) |- ⟨a⟩J(x-1)",
    // conRule   -----------------------------------------------------------
    conclusion = "Γ |- ⟨a<sup>*</sup>⟩P, Δ",
    inputs = "x:variable;;J[x]:formula",
    displayLevel = "browse"
  )
  def conRule(x: Variable, J: Formula): DependentPositionWithAppliedInputTactic = inputanon((pos: Position, sequent: Sequent) => {
    require(pos.isTopLevel && pos.isSucc, "conRule only at top-level in succedent, but got " + pos)
    require(sequent(pos) match { case Diamond(Loop(_), _) => true case _ => false }, "only applicable for <a*>p(||)")
    val ur = URename(Variable("x_",None,Real), x)

    cutR(Exists(ur.what ::Nil, ur(J)))(pos.checkSucc.top) <(
      uniformRename(ur) & label(BelleLabels.initCase)
      ,
      cohide(pos) & implyR(1)
        & byUS(Ax.conflat) <(
        existsL(-1) & andL(-1) & uniformRename(ur) & label(BelleLabels.useCase)
        ,
        assignd(1, 1 :: Nil) & uniformRename(ur) & label(BelleLabels.indStep)
        )
    )
  })

  /** @see [[TactixLibrary.discreteGhost()]] */
  @Tactic(
    names = "iG",
    longDisplayName = "Discrete Ghost",
    premises =   "Γ |- [x:=e]P, Δ",
    //        iG ------------------
    conclusion = "Γ |- P, Δ",
    inputs = "e:term;;x[x]:option[variable]",
    displayLevel = "menu"
  )
  private[btactics] def discreteGhost(e: Term, x: Option[Variable]): DependentPositionWithAppliedInputTactic = inputanon (discreteGhost(e, x, assignInContext = true)(_: Position))
  /** @see [[TactixLibrary.discreteGhost]] */
  def discreteGhost(e: Term, x: Option[Variable], assignInContext: Boolean = true): DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    if (x match { case Some(g) => g != e case None => true }) {
      seq.sub(pos) match {
        case Some(f: Formula) =>
          if (StaticSemantics.freeVars(f).isInfinite) throw new TacticInapplicableFailure("discrete ghost is inapplicable, because of infinite free variables; please expand program symbols first")
          // check specified name, or construct a new name for the ghost variable if None
          def ghostV(f: Formula): Variable = x match {
            case Some(gv) => require(gv == e || (!StaticSemantics.symbols(f).contains(gv))); gv
            case None => e match {
              case v: Variable => TacticHelper.freshNamedSymbol(v, f)
              case _ => TacticHelper.freshNamedSymbol(Variable("ghost"), seq)
            }
          }
          val theGhost = ghostV(f)
          val theF = e match {
            //@note first two cases: backwards compatibility with diffSolve and others
            case _: Variable => f.replaceFree(e, DotTerm())
            case _ if StaticSemantics.boundVars(f).intersect(StaticSemantics.freeVars(e)).isEmpty => f.replaceFree(e, DotTerm())
            case _ => f //@note new: arbitrary term ghosts
          }

          val execAssignment = assignEquality(pos) &
            //@note allR2L does not allow rewriting numbers
            (if (!e.isInstanceOf[Number] && pos.isTopLevel) {
              if (pos.isSucc) TactixLibrary.exhaustiveEqR2L(hide=false)(Symbol("Llast")) // from implyR
              else TactixLibrary.exhaustiveEqR2L(hide=false)(AntePos(seq.ante.size-1)) // from andL
            } else skip)

          theGhost match {
            case DifferentialSymbol(x) =>
              val subst = (_: Option[Subst]) => RenUSubst(
                ("f()".asTerm, e) ::
                ("p(.)".asFormula, theF) ::
                Nil)
              val y = TacticHelper.freshNamedSymbol(x, f)
              useAt(Ax.Dassignb, PosInExpr(1::Nil), subst)(pos) &
                stutter("x_".asVariable)(pos) &
                stutter(x)(pos) &
                boundRename(x, y)(pos) &
                boundRename("x_".asVariable, x)(pos ++ PosInExpr(1::Nil)) &
                V(pos ++ PosInExpr(1::Nil)) & assignb(pos)
            case _ =>
              val subst = (_: Option[Subst]) => RenUSubst(
                ("x_".asVariable, theGhost) ::
                ("f()".asTerm, e) ::
                ("p(.)".asFormula, theF) ::
                Nil)
              useAt(Ax.assignbAxiom, PosInExpr(1::Nil), subst)(pos) &
                (if (assignInContext || pos.isTopLevel) execAssignment else skip)
          }


        case Some(e) => throw new TacticInapplicableFailure("discreteGhost only applicable to formulas, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
      }
    } else stutter(x.getOrElse("x_".asVariable))(pos)
  })

  /** Introduces ghost variables with a fresh name in `origSeq' for each of the terms `trms', before continuing with the
    * tactic produced by `cont`. */
  def discreteGhosts(trms: Set[Term], origSeq: Sequent,
                     cont: List[((Term, Variable), BelleExpr)] => BelleExpr): DependentPositionTactic = anon ((pos: Position) => {
    var freshOld: Variable = TacticHelper.freshNamedSymbol(Variable("old"), origSeq)
    val ghosts: List[((Term, Variable), BelleExpr)] = trms.zipWithIndex.map({ case (old, oi) =>
      val (ghost: Variable, ghostPos: Option[Position], nextCandidate) = TacticHelper.findSubst(old, freshOld, origSeq)
      freshOld = nextCandidate
      (old -> ghost,
        ghostPos match {
          case Some(gp) if pos.isTopLevel => TactixLibrary.exhaustiveEqR2L(hide=false)(gp)
          case _ =>
            //@note discreteGhost does not yet keep positions stable, formula moves to last position in succedent after the first ghost
            discreteGhost(old, Some(ghost))(if (oi > 0 && pos.isSucc) LastSucc(0, pos.inExpr) else Fixed(pos))
        })
    }).toList
    cont(ghosts)
  })

  /**
   * Turns an existential quantifier into an assignment.
    *
    * @example {{{
   *         |- [t:=e;][x:=t;]x>=0
   *         -------------------------assignbExists(e)(1)
   *         |- \exists t [x:=t;]x>=0
   * }}}
   * @param e The right-hand side term of the assignment chosen as a witness for the existential quantifier.
   * @return The tactic.
   */
  @Tactic(
    names = "[:=] assign exists",
    codeName = "assignbExistsRule",
    longDisplayName = "Translate Quantifier to Assignment",
    premises =            "Γ |- [t:=e][x:=t]P, Δ",
    // [:=] assign exists -----------------------
    conclusion =          "Γ |- ∃t [x:=t]P, Δ",
    displayLevel = "browse"
  )
  def assignbExists(e: Term): DependentPositionWithAppliedInputTactic = inputanon ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Exists(vars, _)) =>
      require(vars.size == 1, "Cannot handle existential lists")
      val subst = (s: Option[Subst]) =>
        s.getOrElse(throw new UnsupportedTacticFeature("Expected unification in assignbExists")) ++ RenUSubst(USubst("f_()".asTerm ~> e :: Nil))
      useAt(Ax.assignbexists, PosInExpr(1::Nil), subst)(pos)
    case Some(e) => throw new TacticInapplicableFailure("assignbExistsRule only applicable to existential quantifier, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
  })

  /**
    * Turns a universal quantifier into an assignment.
    *
    * @example {{{
    *         [t:=e;][x:=t;]x>=0 |-
    *         -------------------------assignbAll(e)(-1)
    *         \forall t [x:=t;]x>=0 |-
    * }}}
    * @param e The right-hand side term of the assignment chosen as a witness for the universal quantifier.
    * @return The tactic.
    */
  @Tactic(
    names = "[:=] assign all",
    codeName = "assignbAllRule",
    longDisplayName = "Translate Quantifier to Assignment",
    premises =         "Γ, [t:=e][x:=t]P |- Δ",
    // [:=] assign all -----------------------
    conclusion =       "Γ, ∀t [x:=t]P |- Δ",
    displayLevel = "browse"
  )
  def assignbAll(e: Term): DependentPositionWithAppliedInputTactic = inputanon ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Forall(vars, _)) =>
      require(vars.size == 1, "Cannot handle universal lists")
      val subst = (s: Option[Subst]) =>
        s.getOrElse(throw new UnsupportedTacticFeature("Expected unification in assignbAll")) ++ RenUSubst(USubst("f_()".asTerm ~> e :: Nil))
      useAt(Ax.assignball, PosInExpr(0::Nil), subst)(pos)
    case Some(e) => throw new TacticInapplicableFailure("[:=] assign all only applicable to box universal quantifier, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
  })

  /**
    * finds a matching Box in the antecedent to generalize the Box at succedent position pos
    * Q |- P
    * ----------------------------------- boxElim(pos)
    * Γ1, [a]Q, Γ2  |- Δ1, pos: [a]P, Δ2
    * */
  @Tactic("boxElim", longDisplayName = "Eliminate Matching Modalities", premises = "Q |- P", conclusion = "Γ1, [a]Q, Γ2  |- Δ1, [a]P, Δ2")
  val boxElim: DependentPositionTactic = anon { (pos: Position, sequent: Sequent) =>
    sequent.sub(pos) match {
      case Some(Box(prg, _)) =>
        val b = sequent.ante.find {
          case Box(prg2, _) => prg == prg2
          case _ => false
        }.getOrElse(throw new TacticInapplicableFailure("boxElim without matching assumption in the antecedent"))
        val fml2 = b.asInstanceOf[Box].child
        TactixLibrary.generalize(fml2)(pos) & Idioms.<(id, skip)
      case Some(e) => throw new TacticInapplicableFailure("boxElim not on Box but on " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
  }

}
