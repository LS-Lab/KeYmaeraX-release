/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon._
import org.keymaerax.btactics.TacticFactory._
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.btactics.macros.DerivationInfoAugmentors._
import org.keymaerax.btactics.macros.{AxiomInfo, DisplayLevelBrowse, ProvableInfo, Tactic}
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.infrastruct._
import org.keymaerax.parser.StringConverter._
import org.keymaerax.pt.ProvableSig

import scala.collection.immutable._
import scala.reflect.runtime.universe

/** Implementation: [[FOQuantifierTactics]] provides tactics for instantiating quantifiers. */
protected object FOQuantifierTactics extends TacticProvider {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) =
    (FOQuantifierTactics.getClass, universe.typeOf[FOQuantifierTactics.type])

  /** Proves exists by duality from universal base tactic */
  // @todo use "exists eliminate" instead
  def existsByDuality(base: BuiltInPositionTactic, atTopLevel: Boolean = false): BuiltInPositionTactic =
    anon { (provable: ProvableSig, pos: Position) =>
      ProofRuleTactics.requireOneSubgoal(provable, "existsByDuality")
      val sequent = provable.subgoals.head
      sequent.sub(pos) match {
        case Some(Exists(vars, _)) =>
          require(vars.size == 1, "Exists by duality does not support block quantifiers")
          val dual = vars.head match {
            case _: BaseVariable => Ax.existsDual
            case _: DifferentialSymbol => Ax.existsPDual
          }
          val applyBase = (pr: ProvableSig) =>
            if (atTopLevel || pos.isTopLevel) {
              if (pos.isAnte) {
                (pr(NotLeft(pos.checkAnte.top), 0)(base(SuccPos(sequent.succ.length)).computeResult _, 0)(
                  NotRight(SuccPos(sequent.succ.length)),
                  0,
                ))
              } else {
                (pr(NotRight(pos.checkSucc.top), 0)(base(AntePos(sequent.ante.length)).computeResult _, 0)(
                  NotLeft(AntePos(sequent.succ.length)),
                  0,
                ))
              }
            } else {
              (pr(base(pos ++ PosInExpr(0 :: Nil)).computeResult _, 0)(
                useAt(Ax.doubleNegation)(pos).computeResult _,
                0,
              ))
            }

          (provable(useAt(dual, PosInExpr(1 :: Nil))(pos).computeResult _, 0)(applyBase, 0))
        case Some(e) => throw new TacticInapplicableFailure(
            "existsByDuality only applicable to existential quantifiers, but got " + e.prettyString
          )
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
          )
      }
    }

  /** Inverse all instantiate, i.e., introduces a universally quantified Variable for each Term as specified by what. */
  def allInstantiateInverse(what: (Term, Variable)*): BuiltInPositionTactic = anon {
    (provable: ProvableSig, pos: Position) =>
      // @todo allInstantiateInverse misleading name; allIntro instead?
      def allInstI(t: Term, v: Variable, provable: ProvableSig): ProvableSig = {
        ProofRuleTactics.requireOneSubgoal(provable, "allInst")
        val sequent = provable.subgoals.head
        val fml = sequent.sub(pos) match {
          case Some(fml: Formula) => fml
          case Some(e) => throw new TacticInapplicableFailure(
              "allInstantiateInverse only applicable to formulas, but got " + e.prettyString
            )
          case None => throw new IllFormedTacticApplicationException(
              "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
            )
        }
        val subst = RenUSubst(List(
          (Variable("x_"), v),
          (FuncOf(Function("f", None, Unit, Real), Nothing), t.replaceFree(v, Variable("x_"))),
          (PredOf(Function("p", None, Real, Bool), DotTerm()), fml.replaceFree(t, DotTerm())),
        ))
        CEat(subst.toForward(Ax.allInst.provable), PosInExpr(1 :: Nil))(pos).computeResult(provable)
      }
      what.map({ case (t, v) => allInstI(t, v, _) }).foldLeft(provable)({ (pr, r) => pr(r, 0) })
  }

  /** @see [[org.keymaerax.btactics.TactixLibrary.allL]] */
  def allInstantiate(quantified: Option[Variable], instance: Option[Term]): BuiltInPositionTactic =
    // @Tactic in [[SequentCalculus]]
    // @note can be internalized to a USubst tactic with internalized if-condition language
    anon { (pr: ProvableSig, pos: Position) =>
      ProofRuleTactics.requireOneSubgoal(pr, "allIntantiate")
      val sequent = pr.subgoals.head
      def vToInst(vars: Seq[Variable]) = if (quantified.isEmpty) vars.head else quantified.get
      def inst(vars: Seq[Variable]) = if (instance.isEmpty) vToInst(vars) else instance.get

      def ax[T <: ProvableInfo](vars: Seq[Variable], base: T, prime: T): T = {
        if (
          vars.forall({
            case _: DifferentialSymbol => false
            case _ => true
          })
        ) base
        else if (
          vars.forall({
            case _: DifferentialSymbol => true
            case _ => false
          })
        ) prime
        else throw new TacticRequirementError("No mixed variables/differential symbols in block quantifiers")
      }

      sequent.at(pos) match {
        case (_, Forall(vars, _)) if instance.isEmpty && (quantified.isEmpty || vars.contains(quantified.get)) =>
          useAt(ax(vars, Ax.alle, Ax.alleprime))(pos).computeResult(pr)
        case (_, Forall(vars, qf))
            if instance.isDefined && StaticSemantics.boundVars(qf).symbols.intersect(vars.toSet).isEmpty &&
              StaticSemantics
                .symbols(qf)
                .intersect(
                  vars
                    .filter({
                      case _: DifferentialSymbol => false
                      case _ => true
                    })
                    .map(DifferentialSymbol)
                    .toSet
                )
                .isEmpty && (quantified.isEmpty || vars.contains(quantified.get)) =>
          // @todo assumes any USubstAboveURen
          // @todo IDE does not resolve method correctly when omitting second argument nor allows .key
          val axiom = ax(vars, Ax.allInst, Ax.allInstPrime)
          useAt(
            axiom,
            AxIndex.axiomIndex(axiom)._1,
            (uso: Option[Subst]) =>
              uso match {
                case Some(us) => us ++ RenUSubst(("f()".asTerm, us.renaming(instance.get)) :: Nil)
                case None =>
                  throw new IllFormedTacticApplicationException("Expected a partial substitution, but got None")
              },
          )(pos).computeResult(pr)
        case (ctx, f @ Forall(vars, qf)) if quantified.isEmpty || vars.contains(quantified.get) =>
          if ((if (pos.isAnte) -1 else 1) * FormulaTools.polarityAt(ctx(f), pos.inExpr) >= 0)
            throw new TacticInapplicableFailure("\\forall must have negative polarity in antecedent")
          def forall(h: Formula) = if (vars.length > 1) Forall(vars.filter(_ != vToInst(vars)), h) else h
          // cut in [x:=x;]p(t) from axiom: \forall x. p(x) -> p(t)
          val x = vToInst(vars)
          val t = inst(vars)
          val p = forall(qf)

          val (assign, assignPreprocess) = t match {
            case vinst: Variable
                if !StaticSemantics.freeVars(p).symbols.exists(t => t == vinst || t == DifferentialSymbol(x)) =>
              (
                Box(Assign(vinst, vinst), p.replaceAll(x, vinst)),
                ProofRuleTactics.boundRenameFw(x, vinst)(pos).computeResult _,
              )
            case _ => (Box(Assign(x, t), p), skip.result _)
          }

          // @note stuttering needed for instantiating with terms in cases \forall x [x:=x+1;]x>0, plain useAt won't work
          // @todo forward tactic
          def assignbFw = TactixLibrary.proveBy(_: ProvableSig, assignb(pos))

          (pr(DLBySubst.stutterFw(x)(pos ++ PosInExpr(0 :: Nil)).computeResult _, 0)(assignPreprocess, 0)(
            cutLRFw(ctx(assign))(pos.topLevel).computeResult _,
            0,
          )(assignbFw, 0)(CoHideRight(SuccPos(sequent.succ.length)), 1)(CMonFw(pos.inExpr).result _, 1)(
            US(ax(vars, Ax.allInst, Ax.allInstPrime).provable).result _,
            1,
          ))
        case (_, f @ Forall(v, _)) if quantified.isDefined && !v.contains(quantified.get) =>
          throw new InputFormatFailure(
            "Cannot instantiate: universal quantifier " + f + " does not bind " + quantified.get
          )
        case (_, f) => throw new TacticInapplicableFailure(
            "Cannot instantiate: formula " + f.prettyString + " at pos " + pos + " is not a universal quantifier"
          )
        case _ => throw new IllFormedTacticApplicationException(
            "Position " + pos + " is not defined in " + sequent.prettyString
          )
      }
    }

  def existsInstantiate(quantified: Option[Variable], instance: Option[Term]): BuiltInPositionTactic =
    anon { (pr: ProvableSig, pos: Position) =>
      ProofRuleTactics.requireOneSubgoal(pr, "existsInstantiate")
      val sequent = pr.subgoals.head
      def vToInst(vars: Seq[Variable]) = if (quantified.isEmpty) vars.head else quantified.get
      def inst(vars: Seq[Variable]) = if (instance.isEmpty) vToInst(vars) else instance.get

      sequent.at(pos) match {
        case (_, Exists(vars, p)) if instance.isEmpty && (quantified.isEmpty || vars.contains(quantified.get)) =>
          val subst = RenUSubst(
            List((Variable("x_"), vars.head), (UnitPredicational("p_", AnyArg), URename(Variable("x_"), vars.head)(p)))
          )
          CEat(subst.toForward(Ax.existse.provable), PosInExpr(1 :: Nil))(pos).computeResult(pr)
        case (_, Exists(vars, qf))
            if instance.isDefined &&
              !StaticSemantics
                .freeVars(qf)
                .isInfinite && // @note useAt internal renaming introduces x_ which would clash
              StaticSemantics.freeVars(qf).intersect(StaticSemantics.freeVars(instance.get)).isEmpty &&
              StaticSemantics.boundVars(qf).symbols.intersect(vars.toSet).isEmpty &&
              (quantified.isEmpty || vars.contains(quantified.get)) =>
          val subst = RenUSubst(List(
            (Variable("x_"), vars.head),
            (PredOf(Function("p_", None, Real, Bool), DotTerm()), qf.replaceFree(vars.head, DotTerm())),
            (FuncOf(Function("f", None, Unit, Real), Nothing), URename(Variable("x_"), vars.head)(instance.get)),
          ))
          CEat(subst.toForward(Ax.existsGeneralize.provable), PosInExpr(1 :: Nil))(pos).computeResult(pr)
        case (ctx, f @ Exists(vars, qf)) if quantified.isEmpty || vars.contains(quantified.get) =>
          require(
            (if (pos.isSucc) -1 else 1) * FormulaTools.polarityAt(ctx(f), pos.inExpr) < 0,
            "\\exists must have negative polarity in antecedent",
          )
          def exists(h: Formula) = if (vars.length > 1) Exists(vars.filter(_ != vToInst(vars)), h) else h
          // cut in [x:=x;]p(t) from axiom: \exists x. p(x) -> p(t)
          val x = vToInst(vars)
          val t = inst(vars)
          val p = exists(qf)

          val (v, assign, assignPreprocess, subst) = t match {
            case vinst: Variable if !StaticSemantics.freeVars(p).contains(vinst) =>
              (
                vinst,
                Box(Assign(vinst, vinst), p.replaceAll(x, vinst)),
                ProofRuleTactics.boundRenameFw(x, vinst)(pos).computeResult _,
                RenUSubst(List(
                  (FuncOf(Function("f", None, Unit, Real), Nothing), vinst),
                  (
                    PredOf(Function("p_", None, Real, Bool), DotTerm()),
                    Box(Assign(vinst, DotTerm()), p.replaceAll(x, vinst)),
                  ),
                )),
              )
            case _ => (
                x,
                Box(Assign(x, t), p),
                skip.result _,
                RenUSubst(List(
                  (FuncOf(Function("f", None, Unit, Real), Nothing), t),
                  (PredOf(Function("p_", None, Real, Bool), DotTerm()), Box(Assign(x, DotTerm()), p)),
                )),
              )
          }
          val rename = Ax.existsGeneralize.provable(URename(Variable("x_"), v, semantic = true))

          // @note stuttering needed for instantiating with terms in cases \exists x [x:=x+1;]x>0, plain useAt won't work

          // @todo forward tactic
          def assignbFw = TactixLibrary.proveBy(_: ProvableSig, assignb(pos))

          (pr(DLBySubst.stutterFw(x)(pos ++ PosInExpr(0 :: Nil)).computeResult _, 0)(assignPreprocess, 0)(
            cutLRFw(ctx(assign))(pos.topLevel).computeResult _,
            0,
          )(assignbFw, 0)(if (pos.isAnte) CoHideLeft(pos.checkAnte.top) else CoHideRight(pos.checkSucc.top), 1)(
            CMonFw(pos.inExpr).result _,
            1,
          )(subst.toForward(rename), 1))
        case (_, f @ Exists(v, _)) if quantified.isDefined && !v.contains(quantified.get) =>
          throw new InputFormatFailure(
            "Cannot instantiate: existential quantifier " + f + " does not bind " + quantified.get
          )
        case (_, f) => throw new TacticInapplicableFailure(
            "Cannot instantiate: formula " + f.prettyString + " at pos " + pos + " is not a existential quantifier"
          )
        case _ => throw new IllFormedTacticApplicationException(
            "Position " + pos + " is not defined in " + sequent.prettyString
          )
      }
    }

  /** Finds positions where to bound rename */
  private def outerMostBoundPos(x: Variable, s: Sequent): IndexedSeq[Position] = {
    outerMostBoundPos(x, s.ante, AntePosition.apply) ++ outerMostBoundPos(x, s.succ, SuccPosition.apply)
  }

  private def outerMostBoundPos(
      x: Variable,
      fmls: IndexedSeq[Formula],
      posFactory: (Int, List[Int]) => Position,
  ): IndexedSeq[Position] = {
    fmls
      .map(outerMostBoundPos(x, _))
      .zipWithIndex
      .flatMap({ case (posInExpr, i) => posInExpr.map(pie => posFactory(i + 1, pie.pos)) })
  }

  private def outerMostBoundPos(x: Variable, fml: Formula): List[PosInExpr] = {
    var outerMostBound: List[PosInExpr] = List()
    ExpressionTraversal.traverse(
      new ExpressionTraversal.ExpressionTraversalFunction {
        override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] =
          f match {
            case Forall(xs, _) if xs.contains(x) && !outerMostBound.exists(_.isPrefixOf(p)) =>
              outerMostBound = outerMostBound :+ p; Left(None)
            case Exists(xs, _) if xs.contains(x) && !outerMostBound.exists(_.isPrefixOf(p)) =>
              outerMostBound = outerMostBound :+ p; Left(None)
            case Box(Assign(y, _), _) if x == y && !outerMostBound.exists(_.isPrefixOf(p)) =>
              outerMostBound = outerMostBound :+ p; Left(None)
            case Box(AssignAny(y), _) if x == y && !outerMostBound.exists(_.isPrefixOf(p)) =>
              outerMostBound = outerMostBound :+ p; Left(None)
            case Diamond(Assign(y, _), _) if x == y && !outerMostBound.exists(_.isPrefixOf(p)) =>
              outerMostBound = outerMostBound :+ p; Left(None)
            case Diamond(AssignAny(y), _) if x == y && !outerMostBound.exists(_.isPrefixOf(p)) =>
              outerMostBound = outerMostBound :+ p; Left(None)
            case _ => Left(None)
          }
      },
      fml,
    )
    outerMostBound
  }

  /** [[SequentCalculus.allR]] */
  private[btactics] val allSkolemize: BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "allSkolemize")
    val sequent = provable.subgoals.head
    // @Tactic in [[SequentCalculus]]
    if (!pos.isSucc) throw new IllFormedTacticApplicationException(
      "All skolemize only applicable in the succedent, not position " + pos + " in sequent " + sequent.prettyString
    )
    val (xs, p) = sequent.sub(pos) match {
      case Some(Forall(vars, p)) => (vars, p)
      case Some(e) =>
        throw new TacticInapplicableFailure("allR only applicable to universal quantifiers, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
        )
    }
    val namePairs = xs.map(x => (x, TacticHelper.freshNamedSymbol(x, sequent)))

    // No renaming necessary if the bound variables are fresh
    val noRename = StaticSemantics.freeVars(sequent).intersect(xs.toSet).isEmpty

    if (noRename) ProofRuleTactics.skolemizeR(pos).computeResult(provable)
    else {
      if (StaticSemantics.freeVars(p).isInfinite) {
        val unexpandedSymbols = StaticSemantics
          .symbols(p)
          .filter({
            case _: SystemConst => true
            case _: ProgramConst => true
            case _ => false
          })
          .map(_.prettyString)
          .mkString(",")
        throw new UnexpandedDefinitionsFailure(
          "Skolemization not possible because bound variables " + xs.map(_.prettyString).mkString(",") +
            " are not fresh in the sequent; also unable to rename, because formula " + p.prettyString +
            " contains unexpanded symbols " + unexpandedSymbols + ". Please hide all assumptions mentioning " +
            xs.map(_.prettyString).mkString("x") + ", or expand definitions first."
        )
      }
      // @todo bound renaming of x' not supported
      if (StaticSemantics.freeVars(p).symbols.intersect(xs.map(DifferentialSymbol).toSet[Variable]).nonEmpty) {
        // @note bound renaming at pos not allowed, so rename everywhere else with stuttering and bound renaming
        val np = namePairs.toMap
        // @todo assignEquality forward tactic
        def assignEqualityFw(pr: ProvableSig, p: Position) = TactixLibrary.proveBy(pr, DLBySubst.assignEquality(p))
        val stutter = xs.map(DLBySubst.stutterFw)
        val breq = xs.map(x =>
          (p: Position) =>
            (pr: ProvableSig) =>
              (pr(ProofRuleTactics.boundRenameFw(x, np(x))(p).computeResult _, 0)(assignEqualityFw(_, p), 0)(
                hideL(Symbol("L"), Equal(np(x), x)).computeResult _,
                0,
              ))
        )
        def localRename(pr: ProvableSig, p: Position): ProvableSig = {
          (stutter
            .map(_(p))
            .foldLeft(pr)({ (pr, r) => pr(r.computeResult _, 0) })(
              breq.map(_(p)).foldLeft(_: ProvableSig)({ case (pr, r) => pr(r, 0) }),
              0,
            ))
        }
        val fmls =
          (sequent.ante.zipWithIndex.map({ case (f, i) => (f, AntePosition.base0(i)) }) ++
            sequent.succ.zipWithIndex.map({ case (f, i) => (f, SuccPosition.base0(i)) })).filter(_._2 != pos.topLevel)
        val rename = (pr: ProvableSig) =>
          fmls
            .map({ case (f, p) =>
              if (StaticSemantics.freeVars(f).intersect(xs.toSet).isEmpty) { (pr: ProvableSig) => pr }
              else { localRename(_, p) }
            })
            .foldLeft(pr)({ (pr, r) => pr(r, 0) })
        (provable(rename, 0)(ProofRuleTactics.skolemizeR(pos).computeResult _, 0))
      } else {
        // @note rename variable x wherever bound to fresh x_0, so that final uniform renaming step renames back
        val renaming = (pr: ProvableSig) =>
          if (namePairs.size > 1) {
            namePairs
              .map(np =>
                (nppr: ProvableSig) =>
                  outerMostBoundPos(np._1, sequent)
                    .map(ProofRuleTactics.boundRenameFw(np._1, np._2)(_))
                    .foldLeft(nppr)({ (pr, r) => pr(r.computeResult _, 0) })
              )
              .foldLeft(pr)({ (pr, r) => pr(r, 0) })
          } else {
            assert(namePairs.size == 1)
            outerMostBoundPos(namePairs.head._1, sequent)
              .map(ProofRuleTactics.boundRenameFw(namePairs.head._1, namePairs.head._2)(_))
              .foldLeft(pr)({ (pr, r) => pr(r.computeResult _, 0) })
          }
        // uniformly rename variable x to x_0 and simultaneously x_0 to x, effectively swapping \forall x_0 p(x_0) back to \forall x p(x) but renaming all outside occurrences of x in context to x_0.
        val backrenaming = (pr: ProvableSig) =>
          if (namePairs.size > 1) {
            namePairs
              .map(np => ProofRuleTactics.uniformRenameFw(np._2, np._1))
              .foldLeft(pr)({ (pr, r) => pr(r.result _, 0) })
          } else {
            assert(namePairs.size == 1)
            ProofRuleTactics.uniformRenameFw(namePairs.head._2, namePairs.head._1).result(pr)
          }
        (provable(renaming, 0)(ProofRuleTactics.skolemizeR(pos).computeResult _, 0)(backrenaming, 0))
      }
    }
  }

  /** [[SequentCalculus.existsL]] Skolemizes an existential quantifier in the antecedent. */
  private[btactics] val existsSkolemize: BuiltInPositionTactic = existsByDuality(allSkolemize, atTopLevel = true)

  /**
   * Generalizes existential quantifiers, but only at certain positions. All positions have to refer to the same term.
   * @example
   *   {{{
   *   \exists z z=a+b |-
   *   ------------------existentialGenPosT(Variable("z"), PosInExpr(0::Nil) :: Nil)(AntePosition(0))
   *         a+b = a+b |-
   *   }}}
   * @example
   *   {{{
   *   \exists z z=z |-
   *   ----------------existentialGenPosT(Variable("z"), PosInExpr(0::Nil) :: PosInExpr(1::Nil) :: Nil)(AntePosition(0))
   *       a+b = a+b |-
   *   }}}
   * @param x
   *   The new existentially quantified variable.
   * @param where
   *   Points to the term to generalize.
   * @return
   *   The tactic.
   */
  private[btactics] def existsGeneralize(x: Variable, where: List[PosInExpr]): BuiltInPositionTactic =
    anon { (provable: ProvableSig, pos: Position) =>
      def replaceWheres(fml: Formula, repl: Term): Formula = ExpressionTraversal.traverse(
        new ExpressionTraversal.ExpressionTraversalFunction {
          override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] =
            if (where.contains(p)) Right(repl) else Left(None)
        },
        fml,
      ) match {
        case Some(f) => f
        case _ => throw new IllegalArgumentException(s"Position $where is not a term")
      }

      ProofRuleTactics.requireOneSubgoal(provable, "existsGeneralize")
      val sequent = provable.subgoals.head
      sequent.sub(pos) match {
        case Some(fml: Formula) =>
          if (where.isEmpty) throw new IllFormedTacticApplicationException("Need at least one position to generalize")
          if (where.map(w => sequent.sub(pos.topLevel ++ w)).toSet.size != 1)
            throw new IllFormedTacticApplicationException("Not all positions refer to the same term")
          val fmlRepl = replaceWheres(fml, Variable("x_"))

          // @note create own substitution since UnificationMatch doesn't get it right yet
          val aT = FuncOf(Function("f", None, Unit, Real), Nothing)
          val aP = PredOf(Function("p_", None, Real, Bool), DotTerm())
          val pDot = replaceWheres(fml, DotTerm())
          val subst = USubst(
            SubstitutionPair(aP, pDot) :: SubstitutionPair(aT, sequent.sub(pos.topLevel ++ where.head).get) :: Nil
          )

          (provable(Cut(Imply(fml, Exists(Variable("x_") :: Nil, fmlRepl))), 0)(
            CoHideRight(SuccPos(sequent.succ.length)),
            1,
          )(Ax.existsGeneralize.provable(subst), 1) // closes goal 1
          (ImplyLeft(AntePos(sequent.ante.length)), 0) // creates goals 0+1
          (if (pos.isAnte) HideLeft(pos.checkAnte.top) else HideRight(pos.checkSucc.top), 1)(
            ProofRuleTactics.boundRenameFw(Variable("x_"), x)(AntePos(sequent.ante.length - 1)).computeResult _,
            1,
          )(Close(pos.checkAnte.top, SuccPos(sequent.succ.length)), 0))
        case Some(e) =>
          throw new TacticInapplicableFailure("existsGeneralize only applicable to formulas, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
          )
      }
    }

  /**
   * Converse of all instantiate.
   * @param x
   *   The universally quantified variable to introduce.
   * @param t
   *   The term to generalize.
   * @return
   *   The position tactic.
   * @example
   *   {{{
   *   \forall z \forall x x^2 >= -z^2
   *   ------------------------------- universalGenT(z, f())
   *   \forall x x^2 >= -f()^2
   *   }}}
   * @example
   *   {{{
   *   \forall z \forall x x^2 >= -z^2
   *   ------------------------------- universalGenT(z, y+5)
   *   \forall x x^2 >= -(y+5)^2
   *   }}}
   */
  // was named "allGeneralize"
  def universalGen(x: Option[Variable], t: Term): BuiltInPositionTactic =
    anon { (provable: ProvableSig, pos: Position) =>
      ProofRuleTactics.requireOneSubgoal(provable, "universalGen")
      val sequent = provable.subgoals.head
      val quantified: Variable = x match {
        case Some(xx) => xx
        case None =>
          val bv = StaticSemantics.boundVars(sequent)
          t match {
            case v: Variable if !bv.contains(v) => v
            case v: Variable if bv.contains(v) => TacticHelper.freshNamedSymbol(v, sequent)
            case FuncOf(fn, _) =>
              val funcVar = Variable(fn.name, fn.index, fn.sort)
              if (bv.contains(funcVar)) {
                val fresh = TacticHelper.freshNamedSymbol(fn, sequent)
                Variable(fresh.name, fresh.index, fresh.sort)
              } else funcVar
            case _ => throw new InputFormatFailure(
                "Please provide second argument with variable name to use for generalizing term " + t.prettyString
              )
          }
      }

      val (genFml, axiomLemma: AxiomInfo, subst) = sequent.sub(pos) match {
        case Some(f: Formula) if quantified == t =>
          val subst = (s: Option[Subst]) =>
            s match {
              case Some(us) => us ++ RenUSubst(("x_".asTerm, t) :: Nil)
              case None =>
                throw new IllFormedTacticApplicationException("Expected a partial substitution, but got None")
            }
          (Forall(Seq(quantified), f), Ax.alle, subst)
        case Some(f: Formula) if quantified != t =>
          val subst = (s: Option[Subst]) =>
            s match {
              case Some(us) => us ++ RenUSubst(USubst("f()".asTerm ~> t :: Nil))
              case None =>
                throw new IllFormedTacticApplicationException("Expected a partial substitution, but got None")
            }
          (Forall(Seq(quantified), SubstitutionHelper.replaceFree(f)(t, quantified)), Ax.allInst, subst)
        case Some(e) =>
          throw new TacticInapplicableFailure("allGeneralize only applicable to formulas, but got " + e.prettyString)
        case None => throw new IllFormedTacticApplicationException(
            "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
          )
      }
      (provable(cutAtFw(genFml)(pos).computeResult _, 0)(
        useAt(axiomLemma, PosInExpr(0 :: Nil), subst)(pos.topLevel ++ PosInExpr(0 +: pos.inExpr.pos)).computeResult _,
        1,
      )(useAt(Ax.implySelf)(pos.top).computeResult _, 1)(CloseTrue(pos.checkSucc.top), 1))
    }

  /**
   * Converse of exists instantiate.
   * @param x
   *   The existentially quantified variable to introduce.
   * @param t
   *   The term to generalize.
   * @return
   *   The position tactic.
   * @example
   *   {{{
   *   \exists z \exists x x^2 >= -z^2 |-
   *   ----------------------------------- existsGen(z, f())
   *           \exists x x^2 >= -f()^2 |-
   *   }}}
   * @example
   *   {{{
   *   \exists z \exists x x^2 >= -z^2 |-
   *   ----------------------------------- existsGen(z, y+5)
   *         \exists x x^2 >= -(y+5)^2 |-
   *   }}}
   */
  def existsGen(x: Option[Variable], t: Term): BuiltInPositionTactic = anon { (provable: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(provable, "existsGen")
    val sequent = provable.subgoals.head
    val quantified: Variable = x match {
      case Some(xx) => xx
      case None =>
        val bv = StaticSemantics.boundVars(sequent)
        t match {
          case v: Variable if !bv.contains(v) => v
          case v: Variable if bv.contains(v) => TacticHelper.freshNamedSymbol(v, sequent)
          case FuncOf(fn, _) =>
            val funcVar = Variable(fn.name, fn.index, fn.sort)
            if (bv.contains(funcVar)) {
              val fresh = TacticHelper.freshNamedSymbol(fn, sequent)
              Variable(fresh.name, fresh.index, fresh.sort)
            } else funcVar
          case _ => throw new InputFormatFailure(
              "Please provide second argument with variable name to use for generalizing term " + t.prettyString
            )
        }
    }

    val (genFml, axiomLemma: AxiomInfo, subst) = sequent.sub(pos) match {
      case Some(f: Formula) if quantified == t =>
        val subst = (s: Option[Subst]) =>
          s match {
            case Some(us) => us ++ RenUSubst(("x_".asTerm, t) :: Nil)
            case None => throw new IllFormedTacticApplicationException("Expected a partial substitution, but got None")
          }
        (Exists(Seq(quantified), f), Ax.existse, subst)
      case Some(f: Formula) if quantified != t =>
        val subst = (s: Option[Subst]) =>
          s match {
            case Some(us) => us ++ RenUSubst(USubst("f()".asTerm ~> t :: Nil))
            case None => throw new IllFormedTacticApplicationException("Expected a partial substitution, but got None")
          }
        (Exists(Seq(quantified), SubstitutionHelper.replaceFree(f)(t, quantified)), Ax.existsGeneralize, subst)
      case Some(e) =>
        throw new TacticInapplicableFailure("existsGen only applicable to formulas, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException(
          "Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString
        )
    }
    (provable(cutAtFw(genFml)(pos).computeResult _, 0)(
      useAt(axiomLemma, PosInExpr(1 :: Nil), subst)(
        SuccPosition.base0(sequent.succ.length, PosInExpr(1 +: pos.inExpr.pos))
      ).computeResult _,
      1,
    )(useAt(Ax.implySelf)(SuccPos(sequent.succ.length)).computeResult _, 1)(CloseTrue(SuccPos(sequent.succ.length)), 1))
  }

  /**
   * Computes the universal closure of the formula at the specified position. Uses the provided order of quantifiers.
   * Reverse alphabetical order for non-mentioned variables (for all variables if order == Nil).
   * @example
   *   {{{
   *   |- \forall a forall z forall x (x>0 & a=2 & z<5)
   *   -------------------------------------------------universalClosure(Variable("a")::Nil)
   *   |- x>0 & a=2 & z<5
   *   }}}
   * @example
   *   {{{
   *   |- \forall z forall x forall a (x>0 & a=2 & z<5)
   *   -------------------------------------------------universalClosure()
   *   |- x>0 & a=2 & z<5
   *   }}}
   * @param order
   *   The order of quantifiers.
   * @return
   *   The tactic.
   */
  @Tactic(
    name = "universalClosure",
    displayName = Some("∀Cl"),
    displayNameAscii = Some("allClosure"),
    displayLevel = DisplayLevelBrowse,
    displayPremises = "Γ |- \\forall order p(x,y,z), Δ",
    displayConclusion = "Γ |- p(x,y,z), Δ",
    inputs = "order:list[variable]",
  )
  def universalClosure(order: List[Variable]): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    universalClosureFw(order)(pos)
  }

  /** Builtin forward implementation of universalClosure. */
  private[btactics] def universalClosureFw(order: List[Variable]): BuiltInPositionTactic =
    anon { (provable: ProvableSig, pos: Position) =>
      ProofRuleTactics.requireOneSubgoal(provable, "universalClosureFw")
      val sequent = provable.subgoals.head
      // fetch non-bound variables and parameterless function symbols
      require(pos.isTopLevel, "Universal closure only at top-level")
      val varsFns: Set[NamedSymbol] = StaticSemantics.freeVars(sequent(pos.top)).toSet ++
        StaticSemantics.signature(sequent(pos.top))
      require(
        order.toSet[NamedSymbol].subsetOf(varsFns),
        "Order of variables must be a subset of the free symbols+signature, but " +
          (order.toSet[NamedSymbol] -- varsFns) + " is not in the subset",
      )
      // use specified order in reverse, prepend the rest alphabetically
      // @note get both: specified order and compatibility with previous sorting, which resulted in
      //       reverse-alphabetical ordering of quantifiers
      val sorted: Seq[Term] =
        ((varsFns -- order)
          .filter({
            case BaseVariable(_, _, _) => true
            case Function(_, _, Unit, _, None) => true
            case _ => false
          })
          .
          // guarantee stable sorting of quantifiers so that Mathematica behavior is predictable
          toList
          .sorted ++ order.reverse).map({
          case v @ BaseVariable(_, _, _) => v
          case fn @ Function(_, _, Unit, _, None) => FuncOf(fn, Nothing)
          case _ => throw new IllegalArgumentException("Should have been filtered")
        })

      if (sorted.isEmpty) provable
      else sorted.map(t => universalGen(None, t)(pos)).foldLeft(provable)({ (pr, r) => pr(r.computeResult _, 0) })
    }

  /** Repeated application of [[TactixLibrary.allL]] */
  // @todo won't compile @Tactic(displayLevel = "internal")
  def allLs(vs: List[Term]): DependentPositionTactic = anon { pos: Position =>
    vs.map(allL(_)(pos): BelleExpr).reduceLeft(_ & _)
  }
}
