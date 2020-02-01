package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._
import StaticSemanticsTools._

import scala.collection.immutable._

/**
 * Implementation: Tactics to rewrite equalities and introduce abbreviations.
  *
 */
private object EqualityTactics {

  private val namespace = "eq"

  /**
   * Rewrites an equality exhaustively from right to left (i.e., replaces occurrences of left with right).
   * @note Base tactic for eqL2R and eqR2L.
   * @param name The name of the tactic.
   * @return The tactic.
   */
  private def exhaustiveEq(name: String): DependentPositionTactic = name by ((pos: Position, sequent: Sequent) => {
    require(pos.isAnte && pos.isTopLevel, "Equality must be top-level in antecedent")
    sequent.sub(pos) match {
      case Some(Equal(lhs, rhs)) =>
        // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
        require(!lhs.isInstanceOf[Number], "Rewriting numbers not supported")
        require(lhs != rhs, "LHS and RHS are not allowed to overlap")

        val freeRhs = StaticSemantics.freeVars(rhs).toSet

        val renameBoundRhs = "ANON" by ((pos: Position, seq: Sequent) => {
          val fml = seq(pos.top)
          var nextSymbol: Option[Variable] = None
          def createNextSymbol(v: Variable): Variable = nextSymbol match {
            case None =>
              val s = TacticHelper.freshNamedSymbol(v, fml)
              nextSymbol = Some(s)
              s
            case Some(vv) => Variable(vv.name, Some(vv.index.getOrElse(-1) + 1))
          }
          Idioms.mapSubpositions(pos, seq, {
            case (q: Quantified, pp) if q.vars.toSet.intersect(freeRhs).nonEmpty =>
              Some(q.vars.map(v => boundRename(v, createNextSymbol(v))(pp)).
                reduceRightOption[BelleExpr](_ & _).getOrElse(nil))
            case (Box(Assign(x, _), _), pp) if freeRhs.contains(x) =>
              Some(boundRename(x, createNextSymbol(x))(pp))
            case (Box(AssignAny(x), _), pp) if freeRhs.contains(x) =>
              Some(boundRename(x, createNextSymbol(x))(pp))
            case _ => None
          }).reduceRightOption[BelleExpr](_ & _).getOrElse(nil)
        })

        val occurrences = sequent.zipWithPositions.filter({ case (f, p) => p != pos && f.find(lhs).isDefined })
        occurrences.map({ case (_, p) => renameBoundRhs(p) & eqL2R(pos.checkAnte)(p) }).reduceOption[BelleExpr](_&_).getOrElse(skip)
    }
  })

  /** @see [[TactixLibrary.eqL2R]] */
  def eqL2R(eqPos: Int): DependentPositionTactic = eqL2R(Position(eqPos).checkAnte)
  def eqL2R(eqPos: AntePosition): DependentPositionTactic = TacticFactory.anon ((pos: Position, sequent: Sequent) => {
    sequent.sub(eqPos) match {
      case Some(eq@Equal(lhs, rhs)) =>
        val rhsFv = StaticSemantics.freeVars(rhs)
        val lhsFv = StaticSemantics.freeVars(lhs)
        val topFml = sequent(pos.top)

        val (condEquiv@Imply(_, Equiv(_, repl)), dottedRepl) = sequent.sub(pos) match {
          case Some(f: Formula) =>
            val lhsPos = FormulaTools.posOf(f, _ == lhs)
            val freeRhsPos = lhsPos.filter(p => {
              val bv = boundAt(topFml, pos.inExpr ++ p)
              bv.intersect(rhsFv).isEmpty && bv.intersect(lhsFv).isEmpty })
            val (replaced, dotted) = freeRhsPos.foldLeft((f, f))({ case ((fml, d), pp) =>
              (fml.replaceAt(pp, rhs), d.replaceAt(pp, DotTerm())) })
            if (pos.isTopLevel) (Imply(eq, Equiv(f, replaced)), dotted)
            else (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, replaced))),
              sequent(pos.top).replaceAt(pos.inExpr, dotted))
          case Some(t: Term) if t == lhs =>
            (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, rhs))),
              sequent(pos.top).replaceAt(pos.inExpr, DotTerm()))
          case Some(t: Term) if t != lhs =>
            (Imply(eq, Equiv(sequent(pos.top), sequent(pos.top).replaceAt(pos.inExpr, t.replaceFree(lhs, rhs)))),
              sequent(pos.top).replaceAt(pos.inExpr, t.replaceFree(lhs, DotTerm())))
        }

        //@note "stupid" order of cuts, since otherwise original formula not unambiguous from result (e.g., x=0, 0*y=0 ambiguous: was original formula x*y=x or x*y=0 or 0*y=x?)
        val (equivifyCommute, closeWhere) =
          if (pos.isSucc) (equivifyR(pos.top) & commuteEquivR(pos.top), Fixed(pos))
          else (equivifyR('Rlast), LastSucc(0))
        cut(condEquiv) < (
          /* use */ implyL('Llast) < (closeIdWith('Rlast), cutLR(repl)(pos) < (hide('Llast), equivifyCommute & closeIdWith(closeWhere))),
          /* show */ cohide('Rlast) & by("const formula congruence", RenUSubst(
          (FuncOf(Function("s", None, Unit, Real), Nothing), lhs) ::
            (FuncOf(Function("t", None, Unit, Real), Nothing), rhs) ::
            (PredOf(Function("ctxF_", None, Real, Bool), DotTerm()), dottedRepl) :: Nil))
        )
    }
  })

  /** @see [[TactixLibrary.eqR2L]] */
  def eqR2L(eqPos: Int): DependentPositionTactic = eqR2L(Position(eqPos).checkAnte)
  def eqR2L(eqPos: AntePosition): DependentPositionTactic = "eqR2L" by ((pos: Position, sequent: Sequent) => {
    require(eqPos.isTopLevel, "Equality must be at top level, but is " + pos)
    sequent.sub(eqPos) match {
      case Some(Equal(lhs, rhs)) =>
        useAt("= commute")(eqPos) & eqL2R(eqPos)(pos) & useAt("= commute")('L, Equal(rhs, lhs))
    }
  })

  /**
   * Rewrites free occurrences of the left-hand side of an equality into the right-hand side exhaustively.
   * @example{{{
   *    x=2, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *    --------------------------------exhaustiveEqR2L(-1)
   *    x=2, x+y=7 |- x+1<y, [x:=3;]x>0
   * }}}
   * @return The tactic.
   */
  lazy val exhaustiveEqL2R: DependentPositionTactic = exhaustiveEq("allL2R")

  /* Rewrites equalities exhaustively with hiding, but only if left-hand side is an atom (variable or uninterpreted function) */
  lazy val atomExhaustiveEqL2R: DependentPositionTactic = "atomAllL2R" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(fml@Equal(_: Variable, _)) => TactixLibrary.exhaustiveEqL2R(hide=true)(pos, fml)
    case Some(fml@Equal(FuncOf(Function(_, _, _, _, false), _), _)) => TactixLibrary.exhaustiveEqL2R(hide=true)(pos, fml)
  })

  /** Rewrites all atom equalities in the assumptions. */
  lazy val applyEqualities: DependentTactic = "ANON" by ((seq: Sequent) => {
    seq.zipAnteWithPositions.filter({
      case (Equal(v: Variable, t), _) => v != t
      case (Equal(fn@FuncOf(Function(_, _, _, _, false), _), t), _) => fn != t
      case _ => false }).
      reverse.
      map({ case (fml, pos) => Idioms.doIf(_.subgoals.head(pos.checkTop) == fml)(EqualityTactics.atomExhaustiveEqL2R(pos)) }).
      reduceOption[BelleExpr](_ & _).getOrElse(skip)
  })

  /**
   * Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively.
   * @example{{{
   *    2=x, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *    --------------------------------exhaustiveEqR2L(-1)
   *    2=x, x+y=7 |- x+1<y, [x:=3;]x>0
   * }}}
   * @return The tactic.
   */
  lazy val exhaustiveEqR2L: DependentPositionTactic = "allR2L" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(fml@Equal(lhs, rhs)) =>
      useAt("= commute")(pos, fml) & exhaustiveEq("allL2R")(pos, Equal(rhs, lhs)) & useAt("= commute")(pos, Equal(rhs, lhs))
  })


  /** @see [[TactixLibrary.abbrv()]] */
  def abbrv(abbrvV: Variable): DependentPositionTactic = "abbrv" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(t: Term) => abbrv(t, Some(abbrvV))
    case Some(e) => throw new BelleThrowable("Expected a term at position " + pos + ", but got " + e)
    case _ => throw new BelleThrowable("Position " + pos + " is undefined in sequent " + sequent)
  })

  /**
   * Abbreviates a term `t` to a variable everywhere, except in places where some free variable of `t` is bound.
    *
    * @example{{{
   *   max_0 = max(c,d) |- a+b <= max_0+e
   *   ----------------------------------------abbrv("max(c,d)".asTerm)
   *                    |- a+b <= max(c, d) + e
   * }}}
    * @example { { {
    * *   e = max(c,d), e <= 7 |- [c:=2;]max(c, d) >= 2
    * *   ---------------------------------------------abbrv("max(c,d)".asTerm, Some("e".asVariable))
    * *         max(c, d) <= 7 |- [c:=2;]max(c, d) >= 2
    * * }}}
   * @param abbrvV The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
   * @return The tactic.
   */
  def abbrv(t: Term, abbrvV: Option[Variable] = None): InputTactic = new InputTactic("abbrv",
      abbrvV match { case Some(v) => t::v::Nil case None => t::Nil }) {
    def computeExpr(): BelleExpr = new SingleGoalDependentTactic(name) {
      def computeExpr(sequent: Sequent): BelleExpr = {
        require(abbrvV.isEmpty ||
          !(sequent.ante.flatMap(StaticSemantics.signature)
            ++ sequent.succ.flatMap(StaticSemantics.signature)).contains(abbrvV.get),
          "Abbreviation must be fresh in sequent")
        val v = abbrvV match {
          case Some(vv) => vv
          case None => t match {
            case FuncOf(Function(n, _, _, sort,_), _) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
            case BaseVariable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
            case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), t.sort)
          }
        }

        cut(Exists(v :: Nil, Equal(v, t))) <(
          /* use */ existsL('Llast) & exhaustiveEqR2L('Llast),
          /* show */ cohide('Rlast) & existsR(t)(1) & byUS("= reflexive")
        )
      }
    }
  }

  /**
    * Abbreviates a term to a variable at a position.
    * @example{{{
    *   |- [x:=2;]\exists z (z=min(x,y) & z<=2)
    *   ---------------------------------------abbrvAt("min(x,y)".asTerm, Some("z".asVariable)(1,1::Nil)
    *   |- [x:=2;]min(x,y) <= 2
    * }}}
    * @param abbrvV The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
    * @return The tactic.
    */
  def abbrvAt(t: Term, abbrvV: Option[Variable] = None): DependentPositionWithAppliedInputTactic = "abbrvAt" byWithInputs(
    abbrvV match { case Some(v) => t::v::Nil case None => t::Nil }, (pos: Position, sequent: Sequent) => {
      val inFml = sequent.sub(pos) match {
        case Some(p: Formula) => p
        case Some(t: Term) => throw new BelleTacticFailure("Position " + pos + " expected to point to a formula, but points to term " + t.prettyString)
        case _ => throw new BelleIllFormedError("Position " + pos + " does not point to an expression")
      }
      require(abbrvV.isEmpty ||
        !sequent.sub(pos).map(StaticSemantics.signature).contains(abbrvV.get),
        "Abbreviation must be fresh at position")
      val v = abbrvV match {
        case Some(vv) => vv
        case None => t match {
          case FuncOf(Function(n, _, _, sort,_), _) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
          case BaseVariable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
          case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), t.sort)
        }
      }

      val polarity = FormulaTools.polarityAt(sequent(pos.top), pos.inExpr) * (if (pos.isSucc) 1 else -1)

      val cutFml =
        if (polarity >= 0) /* positive and unknown polarity */ Forall(v :: Nil, Imply(Equal(v, t), inFml.replaceFree(t, v)))
        else Exists(v :: Nil, And(Equal(v, t), inFml.replaceFree(t, v)))

      val cohidePos = if (pos.isAnte) cohide('Rlast) else cohide(pos.top)

      cutAt(cutFml)(pos) <(
        /* use */ skip,
        /* show */ cohidePos & CMon(pos.inExpr) & implyR(1) &
        (if (polarity >= 0) allL(t)(-1) & implyL(-1) <(cohide(2) & byUS(DerivedAxioms.equalReflex), closeId)
         else existsR(t)(1) & andR(1) <(cohide(1) & byUS(DerivedAxioms.equalReflex), closeId)) &
        done
      )
  })

  /**
   * Expands an absolute value function.
   * @example{{{
   *    x>=0&abs_0=x | x<0&abs_0=-x |- abs_0=5
   *    ---------------------------------------abs(1, 0::Nil)
   *                                |- abs(x)=5
   * }}}
   * @return The tactic.
   */
  lazy val abs: DependentPositionTactic = "absExp" by ((pos: Position, sequent: Sequent) => sequent.at(pos) match {
    case (ctx, abs@FuncOf(Function(fn, None, Real, Real, true), t)) if fn == "abs" =>
      if (StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty) {
        val freshAbsIdx = TacticHelper.freshIndexInSequent(fn, sequent)
        val absVar = Variable(fn, freshAbsIdx)
        abbrv(abs, Some(absVar)) &
          useAt("= commute")('L, Equal(absVar, abs)) &
          useAt(fn)('L, Equal(abs, absVar))
      } else {
        absAt(pos)
      }
  })

  private lazy val absContradiction = AnonymousLemmas.remember("f()<0 & f()>=0 <-> false".asFormula, QE, namespace)
  private lazy val minContradiction = AnonymousLemmas.remember("f()>g() & f()<=g() <-> false".asFormula, QE, namespace)
  private lazy val maxContradiction = AnonymousLemmas.remember("f()<g() & f()>=g() <-> false".asFormula, QE, namespace)

  /** Expands abs only at a specific position (also works in contexts that bind the argument of abs). */
  lazy val absAt: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(absTerm@FuncOf(Function(fn, None, Real, Real, true), x)) if fn == "abs" =>
      val parentPos = pos.topLevel ++ FormulaTools.parentFormulaPos(pos.inExpr, sequent(pos.top))

      val expanded = sequent.sub(parentPos) match {
        case Some(fml: Formula) =>
          Or(
            And(GreaterEqual(x, Number(0)), fml.replaceFree(absTerm, x)),
            And(Less(x, Number(0)), fml.replaceFree(absTerm, Neg(x))))
      }

      val cohidePos = if (pos.isAnte) cohideR('Rlast) else cohideR(pos.top)

      val polarity = FormulaTools.polarityAt(sequent(pos.top), parentPos.inExpr) * (if (pos.isSucc) 1 else -1)

      val afterCMonPos =
        if (polarity >= 0) SuccPosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
        else AntePosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
      val proveAbs = if (polarity >= 0) {
        abs(afterCMonPos) & orL(-1) <(
          orL(-2) <(
            andL(-2) & eqL2R(-3)(1) & andL(-1) & closeId,
            andL(-2) & andL(-1) & andLi(AntePos(0), AntePos(2)) & useAt(absContradiction, PosInExpr(0::Nil))(-3) & closeF),
          orL(-2) <(
            andL(-2) & andL(-1) & andLi(AntePos(2), AntePos(0)) & useAt(absContradiction, PosInExpr(0::Nil))(-3) & closeF,
            andL(-2) & eqL2R(-3)(1) & andL(-1) & closeId))
      } else {
        abs(afterCMonPos) & orR(1) & orL(-2) <(
          andL(-2) & eqL2R(-3)(-1) & andR(1) & OnAll(closeId),
          andL(-2) & eqL2R(-3)(-1) & andR(2) & OnAll(closeId))
      }

      cutAt(expanded)(parentPos) <(
        nil,
        cohidePos & CMon(parentPos.inExpr) & implyR(1) &
          assertT(_.at(afterCMonPos) match {
            case (ctx, FuncOf(_, t)) => StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty
            case _ => false
          }, "Unable to expand " + fn + " since its argument is bound in context") &
          proveAbs
      )
  })

  /**
   * Expands min/max function.
   * @example{{{
   *    x>=y&max_0=x | x<y&max_0=y  |- max_0=5
   *    ------------------------------------------max(1, 0::Nil)
   *                                |- max(x,y)=5
   * }}}
   * @return The tactic.
   */
  lazy val minmax: DependentPositionTactic = "minmax" by ((pos: Position, sequent: Sequent) => sequent.at(pos) match {
    case (ctx, minmax@FuncOf(Function(fn, None, Tuple(Real, Real), Real, true), t@Pair(f, g))) if fn == "min" || fn == "max" =>
      if (StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty) {
        val freshMinMaxIdx = TacticHelper.freshIndexInSequent(fn, sequent)
        val minmaxVar = Variable(fn, freshMinMaxIdx)
        abbrv(minmax, Some(minmaxVar)) &
          useAt("= commute")('L, Equal(minmaxVar, minmax)) &
          useAt(fn)('L, Equal(minmax, minmaxVar))
      } else {
        minmaxAt(pos)
      }
  })
  /** Expands min/max only at a specific position (also works in contexts that bind some of the arguments). */
  lazy val minmaxAt: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(minmaxTerm@FuncOf(Function(fn, None, Tuple(Real, Real), Real, true), Pair(f, g))) if fn == "min" || fn == "max" =>
      val parentPos = pos.topLevel ++ FormulaTools.parentFormulaPos(pos.inExpr, sequent(pos.top))

      val expanded = sequent.sub(parentPos) match {
        case Some(fml: Formula) if fn == "min" =>
          Or(
            And(LessEqual(f, g), fml.replaceFree(minmaxTerm, f)),
            And(Greater(f, g), fml.replaceFree(minmaxTerm, g))
          )
        case Some(fml: Formula) if fn == "max" =>
          Or(
            And(GreaterEqual(f, g), fml.replaceFree(minmaxTerm, f)),
            And(Less(f, g), fml.replaceFree(minmaxTerm, g))
          )
      }

      val cohidePos = if (pos.isAnte) cohideR('Rlast) else cohideR(pos.top)

      val polarity = FormulaTools.polarityAt(sequent(pos.top), parentPos.inExpr) * (if (pos.isSucc) 1 else -1)

      val contradiction = if (fn == "min") minContradiction else maxContradiction

      val afterCMonPos =
        if (polarity >= 0) SuccPosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
        else AntePosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
      val proveMinMax = if (polarity >= 0) {
        minmax(afterCMonPos) & orL(-1) <(
          orL(-2) <(
            andL(-2) & eqL2R(-3)(1) & andL(-1) & closeId,
            andL(-2) & andL(-1) & andLi(AntePos(0), AntePos(2)) & useAt(contradiction, PosInExpr(0::Nil))(-3) & closeF),
          orL(-2) <(
            andL(-2) & andL(-1) & andLi(AntePos(2), AntePos(0)) & useAt(contradiction, PosInExpr(0::Nil))(-3) & closeF,
            andL(-2) & eqL2R(-3)(1) & andL(-1) & closeId))
      } else {
        minmax(afterCMonPos) & orR(1) & orL(-2) <(
          andL(-2) & eqL2R(-3)(-1) & andR(1) & OnAll(closeId),
          andL(-2) & eqL2R(-3)(-1) & andR(2) & OnAll(closeId))
      }

      cutAt(expanded)(parentPos) <(
        nil,
        cohidePos & CMon(parentPos.inExpr) & implyR(1) &
          assertT(_.at(afterCMonPos) match {
            case (ctx, FuncOf(_, t)) => StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty
            case _ => false
          }, "Unable to expand " + fn + " since its arguments are bound in context") &
          proveMinMax
      )
  })

  /** Expands all special functions (abs/min/max). */
  lazy val expandAll: BelleExpr = "expandAll" by ((s: Sequent) => {
    val allTopPos = s.ante.indices.map(AntePos) ++ s.succ.indices.map(SuccPos)
    val tactics = allTopPos.flatMap(p =>
      Idioms.mapSubpositions(p, s, {
        case (FuncOf(Function("abs", _, _, _, true), _), pos: Position) => Some(?(abs(pos)))
        case (FuncOf(Function("min", _, _, _, true), _), pos: Position) => Some(?(minmax(pos)))
        case (FuncOf(Function("max", _, _, _, true), _), pos: Position) => Some(?(minmax(pos)))
        case _ => None
      })
    )
    tactics.reduceOption[BelleExpr](_ & _).getOrElse(skip)
  })
  /** Expands all special functions (abs/min/max) underneath position `pos`. */
  lazy val expandAllAt: DependentPositionTactic = "expandAllAt" by ((pos: Position, seq: Sequent) => {
    val tactics =
      Idioms.mapSubpositions(pos, seq, {
        case (FuncOf(Function("abs", _, _, _, true), _), pos: Position) => Some(?(abs(pos)))
        case (FuncOf(Function("min", _, _, _, true), _), pos: Position) => Some(?(minmax(pos)))
        case (FuncOf(Function("max", _, _, _, true), _), pos: Position) => Some(?(minmax(pos)))
        case _ => None
      })
    tactics.reduceOption(_ & _).getOrElse(skip)
  })
}
