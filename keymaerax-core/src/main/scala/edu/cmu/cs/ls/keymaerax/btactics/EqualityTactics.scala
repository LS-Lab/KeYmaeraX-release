package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.{?, mapSubpositions}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.StaticSemanticsTools._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols

import scala.collection.immutable._

/**
 * Implementation: Tactics to rewrite equalities and introduce abbreviations.
  *
 */
private object EqualityTactics {

  private val namespace = "eq"

  /**
    * Rewrites free occurrences of the left-hand side of an equality into the right-hand side exhaustively.
    * @example {{{
    *    x=2, 2+y=7 |- 2+1<y, [x:=3;]x>0
    *    --------------------------------exhaustiveEqR2L(-1)
    *    x=2, x+y=7 |- x+1<y, [x:=3;]x>0
    * }}}
    * @return The tactic.
    */
  val exhaustiveEqL2R: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    //@Tactic in [[TactixLibrary]]
    require(pos.isAnte && pos.isTopLevel, "Equality must be top-level in antecedent")
    sequent.sub(pos) match {
      case Some(Equal(lhs, rhs)) =>
        // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
        require(!lhs.isInstanceOf[Number], "Rewriting numbers not supported")
        require(lhs != rhs, "LHS and RHS are not allowed to overlap")

        val freeRhs = StaticSemantics.freeVars(rhs).toSet

        val renameBoundRhs = anon ((pos: Position, seq: Sequent) => {
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
      case Some(e) => throw new TacticInapplicableFailure("exhaustiveEqL2R only applicable to equalities l=r, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
  })

  /** @see [[TactixLibrary.eqL2R]] */
  def eqL2R(eqPos: Int): DependentPositionTactic = eqL2R(Position(eqPos).checkAnte)
  def eqL2R(eqPos: AntePosition): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    sequent.sub(eqPos) match {
      case Some(eq@Equal(lhs, rhs)) =>
        val rhsFv = StaticSemantics.freeVars(rhs)
        val lhsFv = StaticSemantics.freeVars(lhs)
        val topFml = sequent(pos.top)

        val (condEquiv@Imply(_, Equiv(_, repl)), dottedRepl) = sequent.sub(pos) match {
          case Some(f: Formula) =>
            val diffPos = FormulaTools.posOf(f, (e: Expression) => e != lhs && (e match {
              case DifferentialSymbol(x) => lhsFv.contains(x)
              case x: Differential => !lhsFv.intersect(StaticSemantics.symbols(x).
                filter(StaticSemantics.isDifferential).map({ case DifferentialSymbol(x) => x })).isEmpty
              case _ => false
            }))
            //@note rewrites lhs at ante-pos even if it is verbatim lhs of eq (dW and other tactics rely on it);
            // as a result x=y, x=y ==> rewrites slightly surprising to y=y ==>
            val lhsPos = FormulaTools.posOf(f, _ == lhs).filterNot(p => diffPos.exists(_.isPrefixOf(p)))
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
          /* show */ cohide('Rlast) & by(Ax.constFormulaCongruence, RenUSubst(
          (FuncOf(Function("s", None, Unit, Real), Nothing), lhs) ::
            (FuncOf(Function("t", None, Unit, Real), Nothing), rhs) ::
            (PredOf(Function("ctxF_", None, Real, Bool), DotTerm()), dottedRepl) :: Nil))
        )
      case Some(e) => throw new TacticInapplicableFailure("eqL2R only applicable to equalities l=r, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
  })

  /** @see [[TactixLibrary.eqR2L]] */
  def eqR2L(eqPos: Int): DependentPositionTactic = eqR2L(Position(eqPos).checkAnte)
  def eqR2L(eqPos: AntePosition): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    require(eqPos.isTopLevel, "Equality must be at top level, but is " + pos)
    sequent.sub(eqPos) match {
      case Some(Equal(lhs, rhs)) =>
        useAt(Ax.equalCommute)(eqPos) & eqL2R(eqPos)(pos) & useAt(Ax.equalCommute)('L, Equal(rhs, lhs))
      case Some(e) => throw new TacticInapplicableFailure("eqR2L only applicable to equalities l=r, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
  })

  /* Rewrites equalities exhaustively with hiding, but only if left-hand side is an atom (variable or uninterpreted function) */
  @Tactic(names = "L=R all atoms",
    codeName = "atomAllL2R",
    premises="Γ(e) |- Δ(e)",
    // atomAllL2R -------------------------
    conclusion="Γ(x), x=e |- Δ(e)"
  )
  val atomExhaustiveEqL2R: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(fml@Equal(_: Variable, _)) => TactixLibrary.exhaustiveEqL2R(hide=true)(pos, fml)
    case Some(fml@Equal(FuncOf(Function(_, _, _, _, false), _), _)) => TactixLibrary.exhaustiveEqL2R(hide=true)(pos, fml)
    case Some(e) => throw new TacticInapplicableFailure("Equality rewriting only applicable to equalities l=r, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
  })

  /** Rewrites all atom equalities in the assumptions. */
  @Tactic(displayLevel = "internal")
  val applyEqualities: DependentTactic = anon ((seq: Sequent) => {
    seq.zipAnteWithPositions.filter({
      case (Equal(v: Variable, t), _) => v != t
      case (Equal(fn@FuncOf(Function(_, _, _, _, false), _), t), _) => fn != t
      case _ => false
    }).reverseMap({ case (_, pos) => Idioms.doIf(_.subgoals.head(pos.checkTop) match {
          case Equal(l: Variable, r) => l != r
          case Equal(l: FuncOf, r) => l != r
          case _ => false // earlier rewriting may have rewritten LHS to non-trivial term, e.g., x=y+1, x=z+5 ~> z+5=y+1
        })(EqualityTactics.atomExhaustiveEqL2R(pos))
      }).reduceOption[BelleExpr](_ & _).getOrElse(skip)
  })

  /**
   * Rewrites free occurrences of the right-hand side of an equality into the left-hand side exhaustively.
   * @example {{{
   *    2=x, 2+y=7 |- 2+1<y, [x:=3;]x>0
   *    --------------------------------exhaustiveEqR2L(-1)
   *    2=x, x+y=7 |- x+1<y, [x:=3;]x>0
   * }}}
   * @return The tactic.
   */
  val exhaustiveEqR2L: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    //@Tactic in [[TactixLibrary]]
    case Some(fml@Equal(lhs, rhs)) =>
      useAt(Ax.equalCommute)(pos, fml) & exhaustiveEqL2R(pos, Equal(rhs, lhs)) & useAt(Ax.equalCommute)(pos, Equal(rhs, lhs))
  })


  /** @see [[TactixLibrary.abbrv()]] */
  def abbrv(abbrvV: Variable): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(t: Term) => abbrv(t, Some(abbrvV))
    case Some(e) => throw new TacticInapplicableFailure("Expected a term at position " + pos + ", but got " + e)
    case _ => throw new IllFormedTacticApplicationException("Position " + pos + " is undefined in sequent " + sequent)
  })

  /**
   * Abbreviates a term `t` to a variable everywhere, except in places where some free variable of `t` is bound.
    *
    * @example {{{
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
  def abbrv(t: Term, abbrvV: Option[Variable]): DependentTactic = anon ((sequent: Sequent) => {
    //@Tactic in [[TactixLibrary.abbrvAll]]
    require(abbrvV.isEmpty ||
      !(sequent.ante.flatMap(StaticSemantics.signature)
        ++ sequent.succ.flatMap(StaticSemantics.signature)).contains(abbrvV.get),
      "Abbreviation must be fresh in sequent")
    val v = abbrvV match {
      case Some(vv) => vv
      case None => t match {
        case FuncOf(Function(n, _, _, sort, true), _) => Variable(n + "_", TacticHelper.freshIndexInSequent(n + "_", sequent), sort)
        case FuncOf(Function(n, _, _, sort,_), _) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
        case BaseVariable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
        case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), t.sort)
      }
    }

    cut(Exists(v :: Nil, Equal(v, t))) <(
      /* use */ existsL('Llast) & exhaustiveEqR2L('Llast),
      /* show */ cohide('Rlast) & existsR(t)(1) & byUS(Ax.equalReflexive)
    )
  })

  /**
    * Abbreviates a term to a variable at a position.
    * @example {{{
    *   |- [x:=2;]\exists z (z=min(x,y) & z<=2)
    *   ---------------------------------------abbrvAt("min(x,y)".asTerm, Some("z".asVariable)(1,1::Nil)
    *   |- [x:=2;]min(x,y) <= 2
    * }}}
    * @param x The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
    * @return The tactic.
    */
  @Tactic(displayLevel = "internal")
  def abbrvAt(e: Term, x: Option[Variable]): DependentPositionWithAppliedInputTactic = inputanon ((pos: Position, sequent: Sequent) => {
      val inFml = sequent.sub(pos) match {
        case Some(p: Formula) => p
        case Some(t: Term) => throw new TacticInapplicableFailure("Position " + pos + " expected to point to a formula, but points to term " + t.prettyString)
        case _ => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to an expression")
      }
      require(x.isEmpty ||
        !sequent.sub(pos).forall(StaticSemantics.signature(_).contains(x.get)),
        "Abbreviation must be fresh at position")
      val v = x match {
        case Some(vv) => vv
        case None => e match {
          case FuncOf(Function(n, _, _, sort,_), _) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
          case BaseVariable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, sequent), sort)
          case _ => Variable("x", TacticHelper.freshIndexInSequent("x", sequent), e.sort)
        }
      }

      val polarity = FormulaTools.polarityAt(sequent(pos.top), pos.inExpr) * (if (pos.isSucc) 1 else -1)

      val cutFml =
        if (polarity >= 0) /* positive and unknown polarity */ Forall(v :: Nil, Imply(Equal(v, e), inFml.replaceFree(e, v)))
        else Exists(v :: Nil, And(Equal(v, e), inFml.replaceFree(e, v)))

      val cohidePos = if (pos.isAnte) cohide('Rlast) else cohide(pos.top)

      cutAt(cutFml)(pos) <(
        /* use */ skip,
        /* show */ cohidePos & CMon(pos.inExpr) & implyR(1) &
        (if (polarity >= 0) allL(e)(-1) & implyL(-1) <(cohide(2) & byUS(Ax.equalReflexive), id)
         else existsR(e)(1) & andR(1) <(cohide(1) & byUS(Ax.equalReflexive), id)) &
        done
      )
  })

  /**
   * Expands an absolute value function.
   * @example {{{
   *    x>=0&abs_0=x | x<0&abs_0=-x |- abs_0=5
   *    ---------------------------------------abs(1, 0::Nil)
   *                                |- abs(x)=5
   * }}}
   * @return The tactic.
   */
  @Tactic(names = "Expand absolute value", codeName = "absExp")
  val abs: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.at(pos) match {
    case (_, _: Formula) => mapSubpositions(pos, sequent, {
      case (FuncOf(InterpretedSymbols.absF, _), pp) => Some(?(abs(pp)))
      case _ => None
    }).reduceRightOption[BelleExpr](_ & _).getOrElse(skip)
    case (ctx, abs@FuncOf(fn@InterpretedSymbols.absF, t)) =>
      if (StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty) {
        val freshAbsIdx = TacticHelper.freshIndexInSequent(fn.name + "_", sequent)
        val absVar = Variable(fn.name + "_", freshAbsIdx)
        abbrv(abs, Some(absVar)) &
          useAt(Ax.equalCommute)('L, Equal(absVar, abs)) &
          useAt(Ax.abs)('L, Equal(abs, absVar))
      } else {
        absAt(pos)
      }
    case (_, e) => throw new TacticInapplicableFailure("absExp only applicable to abs(.), but got " + e.prettyString)
  })

  private lazy val absContradiction = AnonymousLemmas.remember("f()<0 & f()>=0 <-> false".asFormula, QE, namespace)
  private lazy val minContradiction = AnonymousLemmas.remember("f()>g() & f()<=g() <-> false".asFormula, QE, namespace)
  private lazy val maxContradiction = AnonymousLemmas.remember("f()<g() & f()>=g() <-> false".asFormula, QE, namespace)

  /** Expands abs only at a specific position (also works in contexts that bind the argument of abs). */
  @Tactic(displayLevel = "internal")
  val absAt: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(absTerm@FuncOf(fn@InterpretedSymbols.absF, x)) =>
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
            andL(-2) & eqL2R(-3)(1) & andL(-1) & id,
            andL(-2) & andL(-1) & andLi(AntePos(0), AntePos(2)) & useAt(absContradiction, PosInExpr(0::Nil))(-3) & closeF),
          orL(-2) <(
            andL(-2) & andL(-1) & andLi(AntePos(2), AntePos(0)) & useAt(absContradiction, PosInExpr(0::Nil))(-3) & closeF,
            andL(-2) & eqL2R(-3)(1) & andL(-1) & id))
      } else {
        abs(afterCMonPos) & orR(1) & orL(-2) <(
          andL(-2) & eqL2R(-3)(-1) & andR(1) & OnAll(id),
          andL(-2) & eqL2R(-3)(-1) & andR(2) & OnAll(id))
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
    case Some(e) => throw new TacticInapplicableFailure("absAt only applicable to abs, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to valid position in sequent " + sequent.prettyString)
  })

  /**
   * Expands min/max function.
   * @example {{{
   *    x>=y&max_0=x | x<y&max_0=y  |- max_0=5
   *    ------------------------------------------max(1, 0::Nil)
   *                                |- max(x,y)=5
   * }}}
   * @return The tactic.
   */
  @Tactic(names = "Expand min/max")
  val minmax: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.at(pos) match {
    case (_, _: Formula) => mapSubpositions(pos, sequent, {
      case (FuncOf(Function(fn, None, Tuple(Real, Real), Real, true), _), pp) =>
        if (fn == InterpretedSymbols.minF.name || fn == InterpretedSymbols.maxF.name) Some(?(minmax(pp)))
        else None
      case _ => None
    }).reduceRightOption[BelleExpr](_ & _).getOrElse(skip)
    case (ctx, minmax@FuncOf(Function(fn, None, Tuple(Real, Real), Real, true), t: Pair))
        if fn == InterpretedSymbols.minF.name || fn == InterpretedSymbols.maxF.name =>
      if (StaticSemantics.boundVars(ctx.ctx).intersect(StaticSemantics.freeVars(t)).isEmpty) {
        val freshMinMaxIdx = TacticHelper.freshIndexInSequent(fn + "_", sequent)
        val minmaxVar = Variable(fn + "_", freshMinMaxIdx)
        abbrv(minmax, Some(minmaxVar)) &
          useAt(Ax.equalCommute)('L, Equal(minmaxVar, minmax)) &
          (fn match {
            case InterpretedSymbols.minF.name => useAt(Ax.min)('L, Equal(minmax, minmaxVar))
            case InterpretedSymbols.maxF.name => useAt(Ax.max)('L, Equal(minmax, minmaxVar))
            case _ => throw new AssertionError("Cannot happen")
          })
      } else {
        minmaxAt(pos)
      }
    case (_, e) => throw new TacticInapplicableFailure("minmax only applicable to min/max, but got " + e.prettyString)
  })
  /** Expands min/max only at a specific position (also works in contexts that bind some of the arguments). */
  @Tactic(displayLevel = "internal")
  val minmaxAt: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(minmaxTerm@FuncOf(Function(fn, None, Tuple(Real, Real), Real, true), Pair(f, g)))
      if fn == InterpretedSymbols.minF.name || fn == InterpretedSymbols.maxF.name =>
      val parentPos = pos.topLevel ++ FormulaTools.parentFormulaPos(pos.inExpr, sequent(pos.top))

      val expanded = sequent.sub(parentPos) match {
        case Some(fml: Formula) if fn == InterpretedSymbols.minF.name =>
          Or(
            And(LessEqual(f, g), fml.replaceFree(minmaxTerm, f)),
            And(Greater(f, g), fml.replaceFree(minmaxTerm, g))
          )
        case Some(fml: Formula) if fn == InterpretedSymbols.maxF.name =>
          Or(
            And(GreaterEqual(f, g), fml.replaceFree(minmaxTerm, f)),
            And(Less(f, g), fml.replaceFree(minmaxTerm, g))
          )
      }

      val cohidePos = if (pos.isAnte) cohideR('Rlast) else cohideR(pos.top)

      val polarity = FormulaTools.polarityAt(sequent(pos.top), parentPos.inExpr) * (if (pos.isSucc) 1 else -1)

      val contradiction = if (fn == InterpretedSymbols.minF.name) minContradiction else maxContradiction

      val afterCMonPos =
        if (polarity >= 0) SuccPosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
        else AntePosition.base0(0, PosInExpr(pos.inExpr.pos.drop(parentPos.inExpr.pos.length)))
      val proveMinMax = if (polarity >= 0) {
        minmax(afterCMonPos) & orL(-1) <(
          orL(-2) <(
            andL(-2) & eqL2R(-3)(1) & andL(-1) & id,
            andL(-2) & andL(-1) & andLi(AntePos(0), AntePos(2)) & useAt(contradiction, PosInExpr(0::Nil))(-3) & closeF),
          orL(-2) <(
            andL(-2) & andL(-1) & andLi(AntePos(2), AntePos(0)) & useAt(contradiction, PosInExpr(0::Nil))(-3) & closeF,
            andL(-2) & eqL2R(-3)(1) & andL(-1) & id))
      } else {
        minmax(afterCMonPos) & orR(1) & orL(-2) <(
          andL(-2) & eqL2R(-3)(-1) & andR(1) & OnAll(id),
          andL(-2) & eqL2R(-3)(-1) & andR(2) & OnAll(id))
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
    case Some(e) => throw new TacticInapplicableFailure("minmaxAt only applicable to min/max, but got " + e.prettyString)
    case None => throw new IllFormedTacticApplicationException("Position " + pos.prettyString + " does not point to a valid position in " + sequent.prettyString)
  })

  private def protectPos(tac : DependentPositionTactic) : DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    if(sequent.sub(pos).isDefined) tac(pos)
    else skip //todo: skip or throw a catchable failure?
  })

  /** Expands all special functions (abs/min/max). */
  @Tactic(names="Expand all special functions",
    revealInternalSteps = true)
  val expandAll: BelleExpr = anon ((s: Sequent) => {
    val allTopPos = s.ante.indices.map(AntePos) ++ s.succ.indices.map(SuccPos)
    val tactics = allTopPos.flatMap(p =>
      Idioms.mapSubpositions(p, s, {
        case (FuncOf(InterpretedSymbols.absF, _), pos: Position) => Some(?(protectPos(abs)(pos)))
        case (FuncOf(InterpretedSymbols.minF, _), pos: Position) => Some(?(protectPos(minmax)(pos)))
        case (FuncOf(InterpretedSymbols.maxF, _), pos: Position) => Some(?(protectPos(minmax)(pos)))
        case _ => None
      })
    )
    tactics.reduceOption[BelleExpr](_ & _).getOrElse(skip) &
      Idioms.doIf(_.subgoals.exists(StaticSemantics.symbols(_).exists({ case Function(_, _, _, _, interpreted) => interpreted case _ => false })))(onAll(expandAll))
  })
  /** Expands all special functions (abs/min/max) underneath position `pos`. */
  @Tactic(displayLevel = "internal")
  val expandAllAt: DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    val tactics =
      Idioms.mapSubpositions(pos, seq, {
        case (FuncOf(InterpretedSymbols.absF, _), pos: Position) => Some(?(protectPos(abs)(pos)))
        case (FuncOf(InterpretedSymbols.minF, _), pos: Position) => Some(?(protectPos(minmax)(pos)))
        case (FuncOf(InterpretedSymbols.maxF, _), pos: Position) => Some(?(protectPos(minmax)(pos)))
        case _ => None
      })
    tactics.reduceOption(_ & _).getOrElse(skip)
  })
}
