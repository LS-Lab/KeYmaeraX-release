package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, NamedTactic, SequentType, USubstPatternTactic}
import edu.cmu.cs.ls.keymaerax.core.Sequent
import BelleLabels._

import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._

import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps

/**
  * Implementation: some dL tactics using substitution tactics.
  * Created by nfulton on 11/3/15.
  */
private object DLBySubst {

  private[btactics] lazy val monb2 = byUS("[] monotone 2")

  /** whether games are currently allowed */
  private[this] val isGame: Boolean = try {Dual(AssignAny(Variable("x"))); true} catch {case ignore: IllegalArgumentException => false }

  /** G: Gödel generalization rule reduces a proof of `|- [a;]p(x)` to proving the postcondition `|- p(x)` in isolation.
    * {{{
    *       p(||)
    *   ----------- G
    *    [a;]p(||)
    * }}}
    *
    * @see [[monb]] with p(x)=True
    * @note Unsound for hybrid games where [[monb]] and dualFree is used instead.
    */
  lazy val G: BelleExpr = {
    val pattern = SequentType(Sequent(IndexedSeq(), IndexedSeq("[a_;]p_(||)".asFormula)))
    //@todo ru.getRenamingTactic should be trivial so can be optimized away with a corresponding assert
    if (isGame)
      USubstPatternTactic(
        (pattern, (ru:RenUSubst) =>
          cut(ru.substitution.usubst("[a_;]true".asFormula)) <(
            ru.getRenamingTactic & TactixLibrary.by("[] monotone 2", ru.substitution.usubst ++ USubst(
              SubstitutionPair(UnitPredicational("q_", AnyArg), True) :: Nil
            )) &
              hideL(-1, True)
              partial
            ,
            dualFree(2)
            ))::Nil)
    else
      USubstPatternTactic(
        (pattern, (ru:RenUSubst) => {
          Predef.assert(ru.getRenamingTactic == ident, "no renaming for Goedel");
          //ru.getRenamingTactic & by("Goedel", ru.substitution.usubst)
          TactixLibrary.by("Goedel", ru.usubst)
        })::Nil
    )
  }

  /** @see [[TactixLibrary.abstractionb]] */
  def abstractionb: DependentPositionTactic = new DependentPositionTactic("abstractionb") {
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
              //@todo code quality needs improved
              //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
                vars.filter(v => v.isInstanceOf[BaseVariable]).map(v => v.asInstanceOf[NamedSymbol]).
                  to[scala.collection.immutable.SortedSet].
                  foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))

            cut(Imply(ctx(qPhi), ctx(b))) <(
              /* use */ (implyL('Llast) <(hideR(pos.topLevel) partial /* result remains open */ , closeIdWith('Llast))) partial,
              /* show */ cohide('Rlast) & CMon(pos.inExpr) & implyR(1) &
              assertT(1, 1) & assertT(s => s.ante.head == qPhi && s.succ.head == b, s"Formula $qPhi and/or $b are not in the expected positions in abstractionb") &
              topAbstraction(1) & ProofRuleTactics.trivialCloser
              )
        }
      }
    }
  }

  /**
   * Introduces a self assignment [x:=x;]p(||) in front of p(||).
    *
    * @param x The self-assigned variable.
   * @return The tactic.
   */
  def selfAssign(x: Variable): DependentPositionTactic = "[:=] self assign inverse" by ((pos: Position, sequent: Sequent) => sequent.at(pos) match {
    case (ctx, f: Formula) =>
      val commute = if (pos.isAnte) commuteEquivR(1) else skip
      cutLR(ctx(Box(Assign(x, x), f)))(pos) <(
        skip,
        cohide('Rlast) & equivifyR(1) & commute & CE(pos.inExpr) &
          byUS("[:=] self assign")
      )
  })

  /** Top-level abstraction: basis for abstraction tactic */
  private def topAbstraction: DependentPositionTactic = new DependentPositionTactic("Top-level abstraction") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(!pos.isAnte, "Abstraction only in succedent")
        sequent.sub(pos) match {
          case Some(b@Box(prg, phi)) =>
            val vars: scala.collection.immutable.SortedSet[Variable] = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.
              //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
              filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable]).to[scala.collection.immutable.SortedSet](
                //@note provide canBuildFrom and ordering because Scala implicit conversions won't compile
                scala.collection.immutable.SortedSet.canBuildFrom(new Ordering[Variable] {
                  override def compare(x: Variable, y: Variable): Int = x.compare(y)
                }))

            val qPhi = if (vars.isEmpty) phi else vars.foldRight(phi)((v, f) => Forall(v :: Nil, f))

            val diffRenameStep: DependentPositionTactic = "diffRenameStep" by ((pos: Position, sequent: Sequent) => sequent(AntePos(0)) match {
                case Equal(x: Variable, x0: Variable) if sequent(AntePos(sequent.ante.size - 1)) == phi =>
                  DebuggingTactics.print("Foo") & selfAssign(x0)(pos) & DebuggingTactics.print("Bar") & ProofRuleTactics.boundRenaming(x0, x)(pos.topLevel) & DebuggingTactics.print("Zee") &
                    eqR2L(-1)(pos.topLevel) & useAt("[:=] self assign")(pos.topLevel) & hide(-1)
                case _ => throw new ProverException("Expected sequent of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
              })

            val diffRename: DependentPositionTactic = "diffRename" by ((pos: Position, sequent: Sequent) => {
              //@note allL may introduce equations of the form x=x_0, but not necessarily for all variables
              if (sequent.ante.size == 1 && sequent.succ.size == 1 && sequent.ante.head == sequent.succ.head) ident
              else if (sequent.ante.size <= 1 + vars.size && sequent.succ.size == 1) sequent(AntePos(0)) match {
                case Equal(_, _) if sequent(AntePos(sequent.ante.size - 1)) == phi => diffRenameStep(pos)*(sequent.ante.size - 1)
                case _ => throw new ProverException("Expected sequent of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
              }
              else throw new ProverException("Expected sequent either of the form p(x) |- p(x)\n or of the form x=x_0, ..., p(x) |- p(x_0) as created by assign equality,\n but got " + sequent)
            })

            cut(Imply(qPhi, Box(prg, qPhi))) <(
              /* use */ (implyL('Llast) <(
                hideR(pos.topLevel) partial /* result */,
                cohide2(AntePosition(sequent.ante.length + 1), pos.topLevel) &
                  assertT(1, 1) & assertE(Box(prg, qPhi), "abstractionb: quantified box")('Llast) &
                  assertE(b, "abstractionb: original box")('Rlast) & ?(monb) &
                  assertT(1, 1) & assertE(qPhi, "abstractionb: quantified predicate")('Llast) &
                  assertE(phi, "abstractionb: original predicate")('Rlast) & (allL('Llast)*vars.size) &
                  diffRename(1) &
                  assertT(1, 1) & assertT(s => s.ante.head match {
                    case Forall(_, _) => phi match {
                      case Forall(_, _) => true
                      case _ => false
                    }
                    case _ => true
                  }, "abstractionb: foralls must match") & ProofRuleTactics.trivialCloser
                )) partial,
              /* show */ hideR(pos.topLevel) & implyR('Rlast) & V('Rlast) & closeIdWith('Llast)
            )
        }
      }
    }
  }

  /**
   * Box assignment by substitution assignment [v:=t();]p(v) <-> p(t()) (preferred),
   * or by equality assignment [x:=f();]p(||) <-> \forall x (x=f() -> p(||)) as a fallback.
   * Universal quantifiers are skolemized if applied at top-level in the succedent; they remain unhandled in the
   * antecedent and in non-top-level context.
    *
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
   * @see [[assignEquality]]
   */
  lazy val assignb: DependentPositionTactic =
    "[:=] assign" by ((pos: Position) => (useAt("[:=] assign")(pos) partial) | (useAt("[:=] self assign")(pos) partial) | (assignEquality(pos) partial))

  /**
    * Equality assignment to a fresh variable.
    * Always introduces universal quantifier, which is already skolemized if applied at top-level in the
    * succedent; quantifier remains unhandled in the antecedent and in non-top-level context.
    *
    * @example{{{
    *    x_0=x+1 |- [{x_0:=x_0+1;}*]x_0>0
    *    ----------------------------------assignEquality(1)
    *        |- [x:=x+1;][{x:=x+1;}*]x>0
    * }}}
    * @example{{{
    *    \\forall x_0 (x_0=x+1 -> [{x_0:=x_0+1;}*]x_0>0) |-
    *    --------------------------------------------------- assignEquality(-1)
    *                 [x:=x+1;][{x:=x+1;}*]x>0 |-
    * }}}
    * @example Other uses of the variable in the context remain unchanged.
    * {{{
    *    x=2 |- [y:=2;]\\forall x_0 (x_0=x+1 -> [{x_0:=x_0+1;}*]x_0>0)
    *    -------------------------------------------------------------- assignEquational(1, 1::Nil)
    *    x=2   |- [y:=2;][x:=x+1;][{x:=x+1;}*]x>0
    * }}}
    * @author Andre Platzer
    * @incontext
    */
  lazy val assignEquality: DependentPositionTactic = "[:=] assign equality" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    // [x:=f(x)]P(x)
    case Some(fml@Box(Assign(x, t), p)) =>
      val y = TacticHelper.freshNamedSymbol(x, sequent)
      ProofRuleTactics.boundRenaming(x, y)(pos) &
      useAt("[:=] assign equality")(pos) &
      ProofRuleTactics.uniformRenaming(y, x) &
      (if (pos.isTopLevel && pos.isSucc) allR(pos) & implyR(pos) else ident)
  })

  /** @see [[TactixLibrary.generalize()]]
   * @todo same for diamonds by the dual of K
   */
  def generalize(c: Formula): DependentPositionTactic = new DependentPositionTactic("generalizeb") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.at(pos) match {
        case (ctx, Box(a, _)) =>
          cutR(ctx(Box(a, c)))(pos.checkSucc.top) <(
            /* use */ /*label(BranchLabels.genUse)*/ ident,
            /* show */(cohide(pos.top) & CMon(pos.inExpr++1) & implyR(pos.top)) partial //& label(BranchLabels.genShow)
          )
      }
    }
  }

  /** @see [[TactixLibrary.postCut()]]
   * @todo same for diamonds by the dual of K
   * @note Uses K modal modus ponens, which is unsound for hybrid games.
   */
  def postCut(C: Formula): DependentPositionTactic = useAt("K modal modus ponens &", PosInExpr(1::Nil),
    (us: Subst) => us ++ RenUSubst(("p_(||)".asFormula, C)::Nil))

  private def constAnteConditions(sequent: Sequent, taboo: Set[Variable]): IndexedSeq[Formula] = {
    sequent.ante.filter(f => StaticSemantics.freeVars(f).intersect(taboo).isEmpty)
  }

  /** @see [[TactixLibrary.loop]] */
  def loop(invariant: Formula) = "loop" byWithInput(invariant, (pos, sequent) => {
    require(pos.isTopLevel && pos.isSucc, "loop only at top-level in succedent, but got " + pos)
    (alphaRule*) & ("doLoop" byWithInput(invariant, (pos, sequent) => {
       sequent.sub(pos) match {
          case Some(b@Box(Loop(a), p)) =>
            val consts = constAnteConditions(sequent, StaticSemantics(a).bv.toSet)
            val q =
              if (consts.size > 1) And(invariant, consts.reduceRight(And))
              else if (consts.size == 1) And(invariant, consts.head)
              else And(invariant, True)
            cutR(Box(Loop(a), q))(pos.checkSucc.top) <(
              /* c */ useAt("I induction")(pos) & andR(pos) <(
                andR(pos) <(ident /* indInit */, ((andR(pos) <(closeIdWith(pos), ident))*(consts.size-1) & closeIdWith(pos)) | closeT) partial(initCase),
                cohide(pos) & G & implyR(1) & boxAnd(1) & andR(1) <(
                  (if (consts.nonEmpty) andL('Llast)*consts.size else andL('Llast) & hide('Llast,True)) partial(indStep),
                  andL(-1) & hide(Fixed(-1,Nil,Some(invariant)))/*hide(-1,invariant)*/ & V(1) & ProofRuleTactics.trivialCloser) partial
              ) partial,
              /* c -> d */ cohide(pos) & CMon(pos.inExpr++1) & implyR(1) &
                (if (consts.nonEmpty) andL('Llast)*consts.size else andL('Llast) & hide('Llast, True)) partial(useCase)
            )
        }}))(pos)})
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
  def loopRule(invariant: Formula) = "loopRule" byWithInput(invariant, (pos, sequent) => {
    require(pos.isTopLevel && pos.isSucc, "loopRule only at top-level in succedent, but got " + pos)
    require(sequent(pos) match { case Box(Loop(_),_)=>true case _=>false}, "only applicable for [a*]p(||)")
    val alast = AntePosition(sequent.ante.length)
    cutR(invariant)(pos.checkSucc.top) <(
      ident partial(BelleLabels.initCase)
      ,
      cohide(pos) & implyR(1) & generalize(invariant)(1) <(
        byUS("ind induction") partial(BelleLabels.indStep)
        ,
        ident partial(BelleLabels.useCase)
        )
      )
    /*
    * {{{
    *   step:           use:      init:
    *   I |- [a]I       I |- p    G |- I, D
    *   ------------------------------------
    *   G |- [{a}*]p, D
    * }}}
    */
//    cut(invariant) <(
//      cohide2(alast, pos) & generalize(invariant)(1) <(
//        byUS("ind induction") partial(BelleLabels.indStep)
//        ,
//        ident partial(BelleLabels.useCase)
//        )
//      ,
//      ident partial(BelleLabels.initCase)
//      )
  })

  /** @see [[TactixLibrary.discreteGhost()]] */
  def discreteGhost(t: Term, ghost: Option[Variable] = None): DependentPositionTactic = new DependentPositionTactic("discrete ghost") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.at(pos) match {
        case (ctx, f: Formula) =>
          //def g(f: Formula) = Equiv(Box(Assign(ghostV(f), t), SubstitutionHelper.replaceFree(f)(t, ghostV(f))), f)
          val ghost = ghostV(f)
          cutLR(ctx(Box(Assign(ghost, t), f.replaceFree(t, ghost))))(pos.topLevel) <(
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

  /**
   * Turns an existential quantifier into an assignment.
    *
    * @example{{{
   *         |- [t:=f;][x:=t;]x>=0
   *         -------------------------assignbExists(f)(1)
   *         |- \exists t [x:=t;]x>=0
   * }}}
   * @param f The right-hand side term of the assignment chosen as a witness for the existential quantifier.
   * @return The tactic.
   */
  def assignbExists(f: Term): DependentPositionTactic = "[:=] assign exists" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Exists(vars, p)) =>
      require(vars.size == 1, "Cannot handle existential lists")
      val x = vars.head
      cutR(Box(Assign(x, f), p))(pos.checkSucc.top) <(
        skip,
        cohide(pos.top) & byUS("[:=] assign exists")
        )
  })
}
