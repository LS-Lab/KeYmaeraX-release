/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.{mapSubpositions, opt}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors.ProvableInfoAugmentor
import edu.cmu.cs.ls.keymaerax.btactics.macros.{DisplayLevelInternal, Tactic}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.StaticSemanticsTools._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable._
import scala.reflect.runtime.universe

/** Implementation: Tactics to rewrite equalities and introduce abbreviations. */
private object EqualityTactics extends TacticProvider {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (EqualityTactics.getClass, universe.typeOf[EqualityTactics.type])

  private val namespace = "eq"

  /**
   * Rewrites free occurrences of the left-hand side of an equality into the right-hand side exhaustively.
   * @example
   *   {{{
   *   x=2, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *   --------------------------------exhaustiveEqR2L(-1)
   *   x=2, x+y=7 |- x+1<y, [x:=3;]x>0
   *   }}}
   * @return
   *   The tactic.
   */
  val exhaustiveEqL2R: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "exhaustiveEqL2R")
    val sequent = provable.subgoals.head
    // @Tactic in [[TactixLibrary]]
    require(pos.isAnte && pos.isTopLevel, "Equality must be top-level in antecedent")
    sequent.sub(pos) match {
      case Some(Equal(lhs, rhs)) =>
        // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
        require(!lhs.isInstanceOf[Number], "Rewriting numbers not supported")
        require(lhs != rhs, "LHS and RHS are not allowed to overlap")

        val freeRhs = StaticSemantics.freeVars(rhs).toSet

        val renameBoundRhs = anon { (pr: ProvableSig, pos: Position) =>
          val seq = pr.subgoals.head
          val fml = seq(pos.top)
          var nextSymbol: Option[Variable] = None
          def createNextSymbol(v: Variable): Variable = nextSymbol match {
            case None =>
              val s = TacticHelper.freshNamedSymbol(v, fml)
              nextSymbol = Some(s)
              s
            case Some(vv) => Variable(vv.name, Some(vv.index.getOrElse(-1) + 1))
          }
          Idioms
            .mapSubpositions(
              pos,
              seq,
              {
                case (q: Quantified, pp) if q.vars.toSet.intersect(freeRhs).nonEmpty =>
                  Some(
                    q.vars
                      .map(v => ProofRuleTactics.boundRenameFw(v, createNextSymbol(v))(pp))
                      .foldLeft(_: ProvableSig)({ case (pr, r) => pr(r.computeResult _, 0) })
                  )
                case (Box(Assign(x, _), _), pp) if freeRhs.contains(x) =>
                  Some(ProofRuleTactics.boundRenameFw(x, createNextSymbol(x))(pp).computeResult(_))
                case (Box(AssignAny(x), _), pp) if freeRhs.contains(x) =>
                  Some(ProofRuleTactics.boundRenameFw(x, createNextSymbol(x))(pp).computeResult(_))
                case _ => None
              },
            )
            .foldLeft(pr)({ case (pr, r) => pr(r, 0) })
        }

        val occurrences = sequent.zipWithPositions.filter({ case (f, p) => p != pos && f.find(lhs).isDefined })
        occurrences
          .map({ case (_, p) =>
            (pr: ProvableSig) => (pr(renameBoundRhs(p).computeResult _, 0)(eqL2R(pos.checkAnte)(p).computeResult _, 0))
          })
          .foldLeft(provable)({ (pr, r) => pr(r, 0) })
      case Some(e) => throw new TacticInapplicableFailure(
          "exhaustiveEqL2R only applicable to equalities l=r, but got " + e.prettyString
        )
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
        )
    }
  }

  /** @see [[TactixLibrary.eqL2R]] */
  def eqL2R(eqPos: Int): BuiltInPositionTactic = eqL2R(Position(eqPos).checkAnte)
  def eqL2R(eqPos: AntePosition): BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "eqL2R")
    val sequent = provable.subgoals.head
    sequent.sub(eqPos) match {
      case Some(eq @ Equal(lhs, rhs)) =>
        val rhsFv = StaticSemantics.freeVars(rhs)
        val lhsFv = StaticSemantics.freeVars(lhs)
        val topFml = sequent(pos.top)

        val (condEquiv @ Imply(_, Equiv(_, repl)), dottedRepl) = sequent.sub(pos) match {
          case Some(f: Formula) =>
            val diffPos = FormulaTools.posOf(
              f,
              (e: Expression) =>
                e != lhs &&
                  (e match {
                    case DifferentialSymbol(x) => lhsFv.contains(x)
                    case x: Differential => !lhsFv
                        .intersect(
                          StaticSemantics
                            .symbols(x)
                            .filter(StaticSemantics.isDifferential)
                            .map({ case DifferentialSymbol(x) => x })
                        )
                        .isEmpty
                    case _ => false
                  }),
            )
            // @note rewrites lhs at ante-pos even if it is verbatim lhs of eq (dW and other tactics rely on it);
            // as a result x=y, x=y ==> rewrites slightly surprising to y=y ==>
            val lhsPos = FormulaTools.posOf(f, _ == lhs).filterNot(p => diffPos.exists(_.isPrefixOf(p)))
            val freeRhsPos = lhsPos.filter(p => {
              val bv = boundAt(topFml, pos.inExpr ++ p)
              bv.intersect(rhsFv).isEmpty && bv.intersect(lhsFv).isEmpty
            })
            val (replaced, dotted) = freeRhsPos
              .foldLeft((f, f))({ case ((fml, d), pp) => (fml.replaceAt(pp, rhs), d.replaceAt(pp, DotTerm())) })
            if (pos.isTopLevel) (Imply(eq, Equiv(f, replaced)), dotted)
            else (
              Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, replaced))),
              sequent(pos.top).replaceAt(pos.inExpr, dotted),
            )
          case Some(t: Term) if t == lhs =>
            (
              Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, rhs))),
              sequent(pos.top).replaceAt(pos.inExpr, DotTerm()),
            )
          case Some(t: Term) if t != lhs =>
            (
              Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, t.replaceFree(lhs, rhs)))),
              sequent(pos.top).replaceAt(pos.inExpr, t.replaceFree(lhs, DotTerm())),
            )
        }

        // @note "stupid" order of cuts, since otherwise original formula not unambiguous from result (e.g., x=0, 0*y=0 ambiguous: was original formula x*y=x or x*y=0 or 0*y=x?)
        val (equivifyCommute, closeWhere) =
          if (pos.isSucc) (
            (pr: ProvableSig) => pr(EquivifyRight(pos.checkSucc.top), 0)(CommuteEquivRight(pos.checkSucc.top), 0),
            Fixed(pos),
          )
          else ((pr: ProvableSig) => pr(EquivifyRight(SuccPos(sequent.succ.length)), 0), LastSucc(0))

        val subst = RenUSubst(List(
          (FuncOf(Function("s", None, Unit, Real), Nothing), lhs),
          (FuncOf(Function("t", None, Unit, Real), Nothing), rhs),
          (PredOf(Function("ctxF_", None, Real, Bool), DotTerm()), dottedRepl),
        ))

        (provable(Cut(condEquiv), 0)
        /* show */
        (CoHideRight(SuccPos(sequent.succ.length)), 1)(subst.toForward(Ax.constFormulaCongruence.provable), 1)
        /* use */
        (ImplyLeft(AntePos(sequent.ante.length)), 0)(cutLRFw(repl)(pos).computeResult _, 1) // creates subgoals 1+2
        (HideLeft(AntePos(sequent.ante.length)), 1)(equivifyCommute, 2)(closeIdWith(closeWhere).computeResult _, 2)(
          closeIdWith(SuccPos(sequent.succ.length)).computeResult _,
          0,
        ))
      case Some(e) =>
        throw new TacticInapplicableFailure("eqL2R only applicable to equalities l=r, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + eqPos + " does not point to a valid position in sequent " + sequent.prettyString
        )
    }
  }

  /** @see [[TactixLibrary.eqR2L]] */
  def eqR2L(eqPos: Int): BuiltInPositionTactic = eqR2L(Position(eqPos).checkAnte)
  def eqR2L(eqPos: AntePosition): BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "eqR2L")
    val sequent = provable.subgoals.head
    require(eqPos.isTopLevel, "Equality must be at top level, but is " + pos)
    sequent.sub(eqPos) match {
      case Some(Equal(lhs, rhs)) => (
        provable(useAt(Ax.equalCommute)(eqPos).computeResult _, 0)(eqL2R(eqPos)(pos).computeResult _, 0)(
          useAt(Ax.equalCommute)(Symbol("L"), Equal(rhs, lhs)).computeResult _,
          0,
        )
      )
      case Some(e) =>
        throw new TacticInapplicableFailure("eqR2L only applicable to equalities l=r, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + eqPos + " does not point to a valid position in sequent " + sequent.prettyString
        )
    }
  }

  /* Rewrites equalities exhaustively with hiding, but only if left-hand side is an atom (variable or uninterpreted function) */
  @Tactic(
    name = "atomAllL2R",
    displayName = Some("L=R all atoms"),
    premises = "Γ(e) |- Δ(e)",
    // atomAllL2R -------------------------
    conclusion = "Γ(x), x=e |- Δ(e)",
  )
  val atomExhaustiveEqL2R: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "atomExhaustiveEqL2R")
    val sequent = provable.subgoals.head
    sequent.sub(pos) match {
      case Some(fml @ Equal(_: Variable, _)) =>
        TactixLibrary.exhaustiveEqL2R(hide = true)(pos, fml).computeResult(provable)
      case Some(fml @ Equal(FuncOf(Function(_, _, _, _, None), _), _)) =>
        TactixLibrary.exhaustiveEqL2R(hide = true)(pos, fml).computeResult(provable)
      case Some(e) => throw new TacticInapplicableFailure(
          "Equality rewriting only applicable to equalities l=r, but got " + e.prettyString
        )
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
        )
    }
  }

  /** Rewrites all atom equalities in the assumptions. */
  @Tactic(name = "applyEqualities", displayLevel = DisplayLevelInternal)
  val applyEqualities: BuiltInTactic = anon { (provable: ProvableSig) =>
    ProofRuleTactics.requireOneSubgoal(provable, "applyEqualities")
    val seq = provable.subgoals.head
    seq
      .zipAnteWithPositions
      .filter({
        case (Equal(v: Variable, t), _) => v != t
        case (Equal(fn @ FuncOf(Function(_, _, _, _, None), _), t), _) => fn != t
        case _ => false
      })
      .reverseIterator
      .map({ case (_, pos) =>
        Idioms.doIfFw(_.subgoals.head(pos.checkTop) match {
          case Equal(l: Variable, r) => l != r
          case Equal(l: FuncOf, r) => l != r
          case _ => false // earlier rewriting may have rewritten LHS to non-trivial term, e.g., x=y+1, x=z+5 ~> z+5=y+1
        })(EqualityTactics.atomExhaustiveEqL2R(pos).computeResult)
      })
      .foldLeft(provable)({ (pr, r) => pr(r.result _, 0) })
  }

  /**
   * Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively.
   * @example
   *   {{{
   *   2=x, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *   --------------------------------exhaustiveEqR2L(-1)
   *   2=x, x+y=7 |- x+1<y, [x:=3;]x>0
   *   }}}
   * @return
   *   The tactic.
   */
  val exhaustiveEqR2L: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "exhaustiveqR2L")
    val sequent = provable.subgoals.head
    sequent.sub(pos) match {
      // @Tactic in [[TactixLibrary]]
      case Some(fml @ Equal(lhs, rhs)) => (
        provable(useAt(Ax.equalCommute)(pos, fml).computeResult _, 0)(
          exhaustiveEqL2R(pos, Equal(rhs, lhs)).computeResult _,
          0,
        )(useAt(Ax.equalCommute)(pos, Equal(rhs, lhs)).computeResult _, 0)
      )
    }
  }

  /** @see [[TactixLibrary.abbrv()]] */
  def abbrv(abbrvV: Variable): BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "abbrv")
    val sequent = provable.subgoals.head
    sequent.sub(pos) match {
      case Some(t: Term) => abbrv(t, Some(abbrvV)).result(provable)
      case Some(e) => throw new TacticInapplicableFailure("Expected a term at position " + pos + ", but got " + e)
      case _ => throw new IllFormedTacticApplicationException("Position " + pos + " is undefined in sequent " + sequent)
    }
  }

  /**
   * Abbreviates a term `t` to a variable everywhere, except in places where some free variable of `t` is bound.
   *
   * @example
   *   {{{
   *   max_0 = max(c,d) |- a+b <= max_0+e
   *   ----------------------------------------abbrv("max(c,d)".asTerm)
   *                    |- a+b <= max(c, d) + e
   *   }}}
   * @example
   *   {{{
   *   e = max(c,d), e <= 7 |- [c:=2;]max(c, d) >= 2
   *   ---------------------------------------------abbrv("max(c,d)".asTerm, Some("e".asVariable))
   *         max(c, d) <= 7 |- [c:=2;]max(c, d) >= 2
   *   }}}
   * @param abbrvV
   *   The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
   * @return
   *   The tactic.
   */
  def abbrv(t: Term, abbrvV: Option[Variable]): BuiltInTactic = anon { provable: ProvableSig =>
    ProofRuleTactics.requireOneSubgoal(provable, "abbrv")
    val sequent = provable.subgoals.head
    // @Tactic in [[TactixLibrary.abbrvAll]]
    require(
      abbrvV.isEmpty || !(sequent.ante.flatMap(StaticSemantics.signature) ++
        sequent.succ.flatMap(StaticSemantics.signature)).contains(abbrvV.get),
      "Abbreviation must be fresh in sequent",
    )
    val v = abbrvV match {
      case Some(vv) => vv
      case None => t match {
          case FuncOf(Function(n, _, _, sort, Some(_)), _) =>
            Variable(n + "_", TacticHelper.freshIndexInSequent(n + "_", sequent), sort)
          case FuncOf(Function(n, _, _, sort, None), _) =>
            Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
          case BaseVariable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
          case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), t.sort)
        }
    }

    (provable(Cut(Exists(List(v), Equal(v, t))), 0)
    /* show */
    (CoHideRight(SuccPos(sequent.succ.length)), 1)(existsR(t)(1).computeResult _, 1)(
      US(Ax.equalReflexive.provable).result _,
      1,
    )
    /* use */
    (existsL(AntePos(sequent.ante.length)).computeResult _, 0)(
      exhaustiveEqR2L(AntePos(sequent.ante.length)).computeResult _,
      0,
    ))
  }

  /**
   * Abbreviates a term to a variable at a position.
   * @example
   *   {{{
   *   |- [x:=2;]\exists z (z=min(x,y) & z<=2)
   *   ---------------------------------------abbrvAt("min(x,y)".asTerm, Some("z".asVariable)(1,1::Nil)
   *   |- [x:=2;]min(x,y) <= 2
   *   }}}
   * @param x
   *   The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
   * @return
   *   The tactic.
   */
  @Tactic(name = "abbrvAt", displayLevel = DisplayLevelInternal)
  def abbrvAt(e: Term, x: Option[Variable]): DependentPositionWithAppliedInputTactic =
    inputanon((pos: Position, sequent: Sequent) => {
      val inFml = sequent.sub(pos) match {
        case Some(p: Formula) => p
        case Some(t: Term) => throw new TacticInapplicableFailure(
            "Position " + pos + " expected to point to a formula, but points to term " + t.prettyString
          )
        case _ => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to an expression")
      }
      require(
        x.isEmpty || !sequent.sub(pos).forall(StaticSemantics.signature(_).contains(x.get)),
        "Abbreviation must be fresh at position",
      )
      val v = x match {
        case Some(vv) => vv
        case None => e match {
            case FuncOf(Function(n, _, _, sort, _), _) =>
              Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
            case BaseVariable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
            case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), e.sort)
          }
      }

      val polarity = FormulaTools.polarityAt(sequent(pos.top), pos.inExpr) * (if (pos.isSucc) 1 else -1)

      val cutFml =
        if (polarity >= 0) /* positive and unknown polarity */
          Forall(v :: Nil, Imply(Equal(v, e), inFml.replaceFree(e, v)))
        else Exists(v :: Nil, And(Equal(v, e), inFml.replaceFree(e, v)))

      val cohidePos = if (pos.isAnte) cohide(Symbol("Rlast")) else cohide(pos.top)

      cutAt(cutFml)(pos) <
        (
          /* use */ skip,
          /* show */ cohidePos & CMon(pos.inExpr) & implyR(1) &
            (if (polarity >= 0) allL(e)(-1) & implyL(-1) < (cohide(2) & byUS(Ax.equalReflexive), id)
             else existsR(e)(1) & andR(1) < (cohide(1) & byUS(Ax.equalReflexive), id)) & done,
        )
    })

  /**
   * Expands an absolute value function.
   * @example
   *   {{{
   *   x>=0&abs_0=x | x<0&abs_0=-x |- abs_0=5
   *   ---------------------------------------abs(1, 0::Nil)
   *                               |- abs(x)=5
   *   }}}
   * @return
   *   The tactic.
   */
  @Tactic(name = "absExp", displayName = Some("Expand absolute value"))
  val abs: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "abs")
    val sequent = provable.subgoals.head
    sequent.at(pos) match {
      case (_, _: Formula) =>
        val positions = mapSubpositions(
          pos,
          sequent,
          {
            case (t @ FuncOf(InterpretedSymbols.absF, _), pp) => Some((t, (pp, (abs(pp).computeResult _)(_))))
            case _ => None
          },
        )
        // @note take only the first position, because minmax itself abbreviates before expanding and so expands other positions with it; then reverse-sort by "posInExpr" length to work inside out
        positions
          .groupBy(_._1)
          .map(_._2.head._2)
          .toList
          .sortBy(_._1.inExpr.pos.length)
          .reverseIterator
          .map(_._2)
          .foldLeft(provable)({ (pr, r) => pr(r, 0) })
      case (ctx, abs @ FuncOf(fn @ InterpretedSymbols.absF, t)) =>
        if (StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty) {
          val freshAbsIdx = TacticHelper.freshIndexInSequent(fn.name + "_", sequent)
          val absVar = Variable(fn.name + "_", freshAbsIdx)
          (provable(abbrv(abs, Some(absVar)).result _, 0)(
            useAt(Ax.equalCommute)(Symbol("L"), Equal(absVar, abs)).computeResult _,
            0,
          )(useAt(Ax.abs)(Symbol("L"), Equal(abs, absVar)).computeResult _, 0))
        } else { absAt(pos).computeResult(provable) }
      case (_, e) => throw new TacticInapplicableFailure("absExp only applicable to abs(.), but got " + e.prettyString)
    }
  }

  private lazy val absContradiction = AnonymousLemmas.remember("f()<0 & f()>=0 <-> false".asFormula, QE, namespace)
  private lazy val minContradiction = AnonymousLemmas.remember("f()>g() & f()<=g() <-> false".asFormula, QE, namespace)
  private lazy val maxContradiction = AnonymousLemmas.remember("f()<g() & f()>=g() <-> false".asFormula, QE, namespace)

  /** Expands abs only at a specific position (also works in contexts that bind the argument of abs). */
  @Tactic(name = "absAt", displayLevel = DisplayLevelInternal)
  val absAt: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "absAt")
    val sequent = provable.subgoals.head
    sequent.sub(pos) match {
      case Some(absTerm @ FuncOf(fn @ InterpretedSymbols.absF, x)) =>
        val parentPos = pos.topLevel ++ FormulaTools.parentFormulaPos(pos.inExpr, sequent(pos.top))

        val expanded = sequent.sub(parentPos) match {
          case Some(fml: Formula) => Or(
              And(GreaterEqual(x, Number(0)), fml.replaceFree(absTerm, x)),
              And(Less(x, Number(0)), fml.replaceFree(absTerm, Neg(x))),
            )
        }

        val cohidePos = if (pos.isAnte) CoHideRight(SuccPos(sequent.succ.length)) else CoHideRight(pos.checkSucc.top)

        val polarity = FormulaTools.polarityAt(sequent(pos.top), parentPos.inExpr) * (if (pos.isSucc) 1 else -1)

        val afterCMonPos =
          if (polarity >= 0) SuccPosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
          else AntePosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
        val proveAbs = (pr: ProvableSig) =>
          if (polarity >= 0) {
            /*
          abs(afterCMonPos) & orL(-1) <(
            orL(-2) <(
              andL(-2) & eqL2R(-3)(1) & andL(-1) & id,
              andL(-2) & andL(-1) & andLi(keepLeft=false)(AntePos(0), AntePos(2)) & useAt(absContradiction, PosInExpr(0::Nil))(-3) & closeF),
            orL(-2) <(
              andL(-2) & andL(-1) & andLi(keepLeft=false)(AntePos(2), AntePos(0)) & useAt(absContradiction, PosInExpr(0::Nil))(-3) & closeF,
              andL(-2) & eqL2R(-3)(1) & andL(-1) & id))
             */
            (
              pr(abs(afterCMonPos).computeResult _, 0)(OrLeft(AntePos(0)), 0)
              /* right */
              (OrLeft(AntePos(1)), 1) // creates subgoals 1+2
              (AndLeft(AntePos(1)), 2)(eqL2R(-3)(1).computeResult _, 2)(AndLeft(AntePos(0)), 2)(id.result _, 2)(
                AndLeft(AntePos(1)),
                1,
              )(AndLeft(AntePos(0)), 1)(andLi(keepLeft = false)(AntePos(2), AntePos(0)).computeResult _, 1)(
                useAt(absContradiction, PosInExpr(0 :: Nil))(-3).computeResult _,
                1,
              )(closeF.result _, 1)
              /* left */
              (OrLeft(AntePos(1)), 0) // creates subgoals 0+1
              (AndLeft(AntePos(1)), 1)(AndLeft(AntePos(0)), 1)(
                andLi(keepLeft = false)(AntePos(0), AntePos(2)).computeResult _,
                1,
              )(useAt(absContradiction, PosInExpr(0 :: Nil))(-3).computeResult _, 1)(closeF.result _, 1)(
                AndLeft(AntePos(1)),
                0,
              )(eqL2R(-3)(1).computeResult _, 0)(AndLeft(AntePos(0)), 0)(id.result _, 0)
            )
          } else {
            /*
          abs(afterCMonPos) & orR(1) & orL(-2) <(
            andL(-2) & eqL2R(-3)(-1) & andR(1) & OnAll(id),
            andL(-2) & eqL2R(-3)(-1) & andR(2) & OnAll(id))
             */
            (pr(abs(afterCMonPos).computeResult _, 0)(OrRight(SuccPos(0)), 0)(OrLeft(AntePos(1)), 0)
            /* right */
            (AndLeft(AntePos(1)), 1)(eqL2R(-3)(-1).computeResult _, 1)(AndRight(SuccPos(1)), 1)(id.result _, 2)(
              id.result _,
              1,
            )
            /* left */
            (AndLeft(AntePos(1)), 0)(eqL2R(-3)(-1).computeResult _, 0)(AndRight(SuccPos(0)), 0)(id.result _, 1)(
              id.result _,
              0,
            ))
          }

        (provable(cutAtFw(expanded)(parentPos).computeResult _, 0)
        /* show */
        (cohidePos, 1)(CMonFw(parentPos.inExpr).result _, 1)(ImplyRight(SuccPos(0)), 1)(
          assertT(
            _.at(afterCMonPos) match {
              case (ctx, FuncOf(_, t)) =>
                StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty
              case _ => false
            },
            "Unable to expand " + fn + " since its argument is bound in context",
          ).result _,
          1,
        )(proveAbs, 1))
      case Some(e) => throw new TacticInapplicableFailure("absAt only applicable to abs, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to valid position in sequent " + sequent.prettyString
        )
    }
  }

  /**
   * Expands min/max function.
   * @example
   *   {{{
   *   x>=y&max_0=x | x<y&max_0=y  |- max_0=5
   *   ------------------------------------------max(1, 0::Nil)
   *                               |- max(x,y)=5
   *   }}}
   * @return
   *   The tactic.
   */
  @Tactic(name = "minmax", displayName = Some("Expand min/max"))
  val minmax: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "minmax")
    val sequent = provable.subgoals.head
    sequent.at(pos) match {
      case (_, _: Formula) =>
        // Find all positions where the min or max functions are used
        case class PositionInfo(term: FuncOf, termPos: Position)
        val infos = mapSubpositions(
          pos,
          sequent,
          {
            case (t @ FuncOf(Function(fn, None, Tuple(Real, Real), Real, Some(_)), _), tPos)
                if fn == InterpretedSymbols.minF.name || fn == InterpretedSymbols.maxF.name =>
              Some(PositionInfo(t, tPos))
            case _ => None
          },
        )

        // Take only the first position,
        // because minmax itself abbreviates before expanding and so expands other positions with it;
        // then reverse-sort by "posInExpr" length to work inside out.
        infos
          .groupBy(_.term)
          .map { case (_, infos) => infos.head }
          .toList
          .sortBy(_.termPos.inExpr.pos.length)
          .reverseIterator
          .foldLeft(provable)({ (pr, info) =>
            val forwardTactic: ProvableSig => ProvableSig = pr => minmax(info.termPos).computeResult(pr)(pr)
            pr(forwardTactic, 0)
          })

      case (ctx, minmax @ FuncOf(Function(fn, None, Tuple(Real, Real), Real, Some(_)), t: Pair))
          if fn == InterpretedSymbols.minF.name || fn == InterpretedSymbols.maxF.name =>
        if (StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty) {
          val freshMinMaxIdx = TacticHelper.freshIndexInSequent(fn + "_", sequent)
          val minmaxVar = Variable(fn + "_", freshMinMaxIdx)

          val ax = fn match {
            case InterpretedSymbols.minF.name => Ax.min
            case InterpretedSymbols.maxF.name => Ax.max
            case _ => throw new AssertionError("Cannot happen")
          }

          provable(abbrv(minmax, Some(minmaxVar)).result _, 0)
            .apply(useAt(Ax.equalCommute)(Symbol("L"), Equal(minmaxVar, minmax)).computeResult _, 0)
            .apply(useAt(ax)(Symbol("L"), Equal(minmax, minmaxVar)).computeResult _, 0)
        } else { minmaxAt(pos).computeResult(provable) }

      case (_, e) => throw new TacticInapplicableFailure("minmax only applicable to min/max, but got " + e.prettyString)
    }
  }

  /** Expands min/max only at a specific position (also works in contexts that bind some of the arguments). */
  @Tactic(name = "minmaxAt", displayLevel = DisplayLevelInternal)
  val minmaxAt: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "minmaxAt")
    val sequent = provable.subgoals.head
    sequent.sub(pos) match {
      // todo: should match the max/min interpretation exactly
      case Some(minmaxTerm @ FuncOf(Function(fn, None, Tuple(Real, Real), Real, Some(_)), Pair(f, g)))
          if fn == InterpretedSymbols.minF.name || fn == InterpretedSymbols.maxF.name =>
        val parentPos = pos.topLevel ++ FormulaTools.parentFormulaPos(pos.inExpr, sequent(pos.top))

        val expanded = sequent.sub(parentPos) match {
          case Some(fml: Formula) if fn == InterpretedSymbols.minF.name =>
            Or(And(LessEqual(f, g), fml.replaceFree(minmaxTerm, f)), And(Greater(f, g), fml.replaceFree(minmaxTerm, g)))
          case Some(fml: Formula) if fn == InterpretedSymbols.maxF.name =>
            Or(And(GreaterEqual(f, g), fml.replaceFree(minmaxTerm, f)), And(Less(f, g), fml.replaceFree(minmaxTerm, g)))
        }

        val cohidePos = if (pos.isAnte) CoHideRight(SuccPos(sequent.succ.length)) else CoHideRight(pos.checkSucc.top)

        val polarity = FormulaTools.polarityAt(sequent(pos.top), parentPos.inExpr) * (if (pos.isSucc) 1 else -1)

        val contradiction = if (fn == InterpretedSymbols.minF.name) minContradiction else maxContradiction

        val afterCMonPos =
          if (polarity >= 0) SuccPosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
          else AntePosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))

        val proveMinMax = (pr: ProvableSig) =>
          if (polarity >= 0) {
            /*
          minmax(afterCMonPos) & orL(-1) <(
            orL(-2) <(
              andL(-2) & eqL2R(-3)(1) & andL(-1) & id,
              andL(-2) & andL(-1) & andLi(keepLeft=false)(AntePos(0), AntePos(2)) & useAt(contradiction, PosInExpr(0::Nil))(-3) & closeF),
            orL(-2) <(
              andL(-2) & andL(-1) & andLi(keepLeft=false)(AntePos(2), AntePos(0)) & useAt(contradiction, PosInExpr(0::Nil))(-3) & closeF,
              andL(-2) & eqL2R(-3)(1) & andL(-1) & id))
             */
            (
              pr(minmax(afterCMonPos).computeResult _, 0)(OrLeft(AntePos(0)), 0)
              /* right */
              (OrLeft(AntePos(1)), 1)(AndLeft(AntePos(1)), 2)(eqL2R(-3)(1).computeResult _, 2)(AndLeft(AntePos(0)), 2)(
                id.result _,
                2,
              )(AndLeft(AntePos(1)), 1)(AndLeft(AntePos(0)), 1)(
                andLi(keepLeft = false)(AntePos(2), AntePos(0)).computeResult _,
                1,
              )(useAt(contradiction, PosInExpr(0 :: Nil))(-3).computeResult _, 1)(closeF.result _, 1)
              /* left */
              (OrLeft(AntePos(1)), 0)(AndLeft(AntePos(1)), 1)(AndLeft(AntePos(0)), 1)(
                andLi(keepLeft = false)(AntePos(0), AntePos(2)).computeResult _,
                1,
              )(useAt(contradiction, PosInExpr(0 :: Nil))(-3).computeResult _, 1)(closeF.result _, 1)(
                AndLeft(AntePos(1)),
                0,
              )(eqL2R(-3)(1).computeResult _, 0)(AndLeft(AntePos(0)), 0)(id.result _, 0)
            )
          } else {
            (pr(minmax(afterCMonPos).computeResult _, 0)(OrRight(SuccPos(0)), 0)(OrLeft(AntePos(1)), 0)
            /* right */
            (AndLeft(AntePos(1)), 1)(eqL2R(-3)(-1).computeResult _, 1)(AndRight(SuccPos(1)), 1)(id.result _, 2)(
              id.result _,
              1,
            )
            /* left */
            (AndLeft(AntePos(1)), 0)(eqL2R(-3)(-1).computeResult _, 0)(AndRight(SuccPos(0)), 0)(id.result _, 1)(
              id.result _,
              0,
            ))
          }

        (provable(cutAtFw(expanded)(parentPos).computeResult _, 0)
        /* show */
        (cohidePos, 1)(CMonFw(parentPos.inExpr).result _, 1)(ImplyRight(SuccPos(0)), 1)(
          assertT(
            _.at(afterCMonPos) match {
              case (ctx, FuncOf(_, t)) =>
                StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty
              case _ => false
            },
            "Unable to expand " + fn + " since its arguments are bound in context",
          ).result _,
          1,
        )(proveMinMax, 1))
      case Some(e) =>
        throw new TacticInapplicableFailure("minmaxAt only applicable to min/max, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos.prettyString + " does not point to a valid position in " + sequent.prettyString
        )
    }
  }

  private def protectPos(tac: BuiltInPositionTactic): BuiltInPositionTactic =
    anon { (provable: ProvableSig, pos: Position) =>
      val sequent = provable.subgoals.head
      if (sequent.sub(pos).isDefined) tac(pos).computeResult(provable)
      else provable // todo: skip or throw a catchable failure?
    }

  /** Expands all special functions (abs/min/max). */
  @Tactic(name = "expandAll", displayName = Some("Expand all special functions"))
  val expandAll: BuiltInTactic = anon { (provable: ProvableSig) =>
    ProofRuleTactics.requireOneSubgoal(provable, "expandAll")
    val s = provable.subgoals.head
    val allTopPos = s.ante.indices.map(AntePos) ++ s.succ.indices.map(SuccPos)
    val tactics = allTopPos.flatMap(p =>
      Idioms.mapSubpositions(
        p,
        s,
        {
          case (FuncOf(InterpretedSymbols.absF, _), pos: Position) => Some(opt(protectPos(abs)(pos)))
          case (FuncOf(InterpretedSymbols.minF, _), pos: Position) => Some(opt(protectPos(minmax)(pos)))
          case (FuncOf(InterpretedSymbols.maxF, _), pos: Position) => Some(opt(protectPos(minmax)(pos)))
          case _ => None
        },
      )
    )
    (tactics.foldLeft(provable)({ (pr, r) => pr(r, 0) })(
      Idioms
        .doIfFw(
          _.subgoals
            .exists(
              StaticSemantics
                .symbols(_)
                .exists({
                  case InterpretedSymbols.absF | InterpretedSymbols.minF | InterpretedSymbols.maxF => true
                  case _ => false
                })
            )
        )(expandAll.result)
        .result _,
      0,
    ))
  }

  /** Expands all special functions (abs/min/max) underneath position `pos`. */
  @Tactic(name = "expandAllAt", displayLevel = DisplayLevelInternal)
  val expandAllAt: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "expandAllAt")
    val tactics = Idioms.mapSubpositions(
      pos,
      provable.subgoals.head,
      {
        case (FuncOf(InterpretedSymbols.absF, _), pos: Position) => Some(opt(protectPos(abs)(pos)))
        case (FuncOf(InterpretedSymbols.minF, _), pos: Position) => Some(opt(protectPos(minmax)(pos)))
        case (FuncOf(InterpretedSymbols.maxF, _), pos: Position) => Some(opt(protectPos(minmax)(pos)))
        case _ => None
      },
    )
    tactics.foldLeft(provable)({ (pr, r) => pr(r, 0) })
  }
}
