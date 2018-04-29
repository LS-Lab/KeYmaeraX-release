package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.bellerophon.UnificationMatch
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools._

import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable
import scala.collection.immutable.{IndexedSeq, List}
import scala.language.postfixOps

/**
 * Implementation: provides tactics for differential equations.
  *
  * @note Container for "complicated" tactics. Single-line implementations are in [[TactixLibrary]].
 * @see [[TactixLibrary.DW]], [[TactixLibrary.DC]]
 */
private object DifferentialTactics extends Logging {

  /** @see [[HilbertCalculus.DE]] */
  lazy val DE: DependentPositionTactic = new DependentPositionTactic("DE") {
    //@todo investigate why unification fails and causes unnecessarily complicated tactic. And get rid of duplicate implementation
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = if (RenUSubst.semanticRenaming) {
        if (isODESystem(sequent, pos)) {
          DESystemStep_SemRen(pos)*getODEDim(sequent, pos)
          //@todo unification fails
          // TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(provable.subgoals.head, pos)
        } else {
          useAt("DE differential effect")(pos)
        }
      } else {
        import ProofRuleTactics.contextualize
        if (isODESystem(sequent, pos)) {
          if (HilbertCalculus.INTERNAL) TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(sequent, pos)
          else contextualize(DESystemStep_NoSemRen, predictor)(pos)*getODEDim(sequent, pos)
          //@todo unification fails
          // TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(provable.subgoals.head, pos)
        } else {
          if (HilbertCalculus.INTERNAL) useAt("DE differential effect")(pos)
          else contextualize(DESystemStep_NoSemRen, predictor)(pos)
        }
      }

      private def predictor(fml: Formula): Formula = fml match {
        case Box(ODESystem(DifferentialProduct(AtomicODE(xp@DifferentialSymbol(x), t), c), h), p) =>
          Box(
            ODESystem(DifferentialProduct(c, AtomicODE(xp, t)), h),
            Box(Assign(xp, t), p)
          )

        case Box(ODESystem(AtomicODE(xp@DifferentialSymbol(x), t), h), p) =>
          Box(
            ODESystem(AtomicODE(xp, t), h),
            Box(Assign(xp, t), p)
          )
        case _ => logger.fatal("Unsure how to predict DE outcome for " + fml); ???
      }
    }

    /** A single step of DE system (@todo replace with useAt when unification for this example works) */
    // semanticRenaming
    private lazy val DESystemStep_SemRen: DependentPositionTactic = new DependentPositionTactic("DE system step") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
          case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(d@DifferentialSymbol(x), t), c), h), p)) =>
            val g = Box(
              ODESystem(DifferentialProduct(c, AtomicODE(d, t)), h),
              Box(Assign(d, t), p)
            )

            //construct substitution
            val aF = UnitFunctional("f", AnyArg, Real)
            val aH = UnitPredicational("H", AnyArg)
            val aC = DifferentialProgramConst("c", AnyArg)
            val aP = UnitPredicational("p", AnyArg)
            val aX = Variable("x_")

            val subst = USubst(SubstitutionPair(aF, t) :: SubstitutionPair(aC, c) :: SubstitutionPair(aP, p) ::
              SubstitutionPair(aH, h) :: Nil)
            val uren = ProofRuleTactics.uniformRenaming(aX, x)
            val origin = Sequent(IndexedSeq(), IndexedSeq(s"[{${d.prettyString}=f(||),c&H(||)}]p(||) <-> [{c,${d.prettyString}=f(||)&H(||)}][${d.prettyString}:=f(||);]p(||)".asFormula))

            cutLR(g)(pos) <(
              /* use */ skip,
              //@todo conditional commuting (if (pos.isSucc) commuteEquivR(1) else Idioms.ident) instead?
              /* show */ cohide('Rlast) & equivifyR(1) & commuteEquivR(1) &
              TactixLibrary.US(subst, TactixLibrary.uniformRenameF(aX, x)(AxiomInfo("DE differential effect (system)").provable)))
              //TactixLibrary.US(subst, "DE differential effect (system)"))
        }
      }
    }

    /** A single step of DE system */
    // !semanticRenaming
    private lazy val DESystemStep_NoSemRen: DependentPositionTactic = new DependentPositionTactic("DE system step") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
          case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(xp@DifferentialSymbol(x), t), c), h), p)) =>
            useAt("DE differential effect (system)")(pos)
          case Some(f@Box(ODESystem(AtomicODE(xp@DifferentialSymbol(x), t), h), p)) =>
            useAt("DE differential effect")(pos)
        }
      }
    }
  }

  /** @see [[TactixLibrary.dI]] */
  def diffInd(auto: Symbol = 'full): DependentPositionTactic = new DependentPositionTactic("dI") {
    require(auto == 'full || auto == 'none || auto == 'diffInd, "Expected one of ['none, 'diffInd, 'full] automation values, but got " + auto)
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc && (sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _)) => true
          case _ => false
        }), "diffInd only at ODE system in succedent, but got " + sequent.sub(pos))
        if (pos.isTopLevel) {
          val t = DI(pos) &
            implyR(pos) & andR(pos) & Idioms.<(
              if (auto == 'full) ToolTactics.hideNonFOL & QE & done else skip,
              if (auto != 'none) {
                //@note derive before DE to keep positions easier
                derive(pos ++ PosInExpr(1 :: Nil)) &
                DE(pos) &
                (if (auto == 'full) Dassignb(pos ++ PosInExpr(1::Nil))*getODEDim(sequent, pos) &
                  //@note DW after DE to keep positions easier
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) & abstractionb(pos) & ToolTactics.hideNonFOL & QE & done
                 else {
                  assert(auto == 'diffInd)
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                  abstractionb(pos) & (allR(pos)*) & ?(implyR(pos)) })
              } else skip
              )
          if (auto == 'full) Dconstify(t)(pos)
          else t
        } else {
          val t = DI(pos) &
            (if (auto != 'none) {
              shift(PosInExpr(1 :: 1 :: Nil), "ANON" by ((pos: Position, sequent: Sequent) =>
                //@note derive before DE to keep positions easier
                shift(PosInExpr(1 :: Nil), derive)(pos) &
                  DE(pos) &
                  (if (auto == 'full) shift(PosInExpr(1 :: Nil), Dassignb)(pos)*getODEDim(sequent, pos) &
                    //@note DW after DE to keep positions easier
                    (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                    abstractionb(pos)
                  else abstractionb(pos))
                )
              )(pos)
            } else ident)
          if (auto == 'full) Dconstify(t)(pos)
          else t
        }
      }
    }
  }

  /**
   * diffInd: Differential Invariant proves a formula to be an invariant of a differential equation (by DI, DW, DE, QE)
    *
    * @example{{{
   *    x>=5 |- x>=5    x>=5 |- [{x'=2}](x>=5)'
   *    ---------------------------------------DIRule(qeTool)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5 |- [x:=x+1;](true->x>=5&[{x'=2}](x>=5)')
   *    ---------------------------------------------DIRule(qeTool)(1, 1::Nil)
   *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
   * }}}
   * @incontext
   */
  lazy val DIRule: DependentPositionTactic = diffInd('none)
  lazy val diffIndRule: DependentPositionTactic = diffInd('diffInd)

  /** @see [[TactixLibrary.openDiffInd]] */
  val openDiffInd: DependentPositionTactic = new DependentPositionTactic("openDiffInd") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc && pos.isTopLevel, "openDiffInd only at ODE system in succedent")
        val (axUse,der) = sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _: Greater)) => ("DIo open differential invariance >",true)
          case Some(Box(_: ODESystem, _: Less)) => ("DIo open differential invariance <",true)

          case _ => throw new IllegalArgumentException("openDiffInd only at ODE system in succedent with an inequality in the postcondition (f>g,f<g), but got " + sequent.sub(pos))
        }
        if (pos.isTopLevel) {
          val t = useAt(axUse)(pos) <(
              testb(pos) & ToolTactics.hideNonFOL & QE & done,
              //@note derive before DE to keep positions easier
              implyR(pos) & (
                if(der) derive(pos ++ PosInExpr(1::1::Nil))
                else derive(pos ++ PosInExpr(1::1::0::Nil)) & derive(pos ++ PosInExpr(1::1::1::Nil))) &

                DE(pos) &
                (Dassignb(pos ++ PosInExpr(1::Nil))*getODEDim(sequent, pos) &
                  //@note DW after DE to keep positions easier
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) & abstractionb(pos) & ToolTactics.hideNonFOL & QE & done
                  )
              )
          Dconstify(t)(pos)
        } else {
          //@todo positional tactics need to be adapted
          val t = useAt(axUse)(pos) &
              shift(PosInExpr(1 :: 1 :: Nil), new DependentPositionTactic("Shift") {
                override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
                  override def computeExpr(sequent: Sequent): BelleExpr = {
                    //@note derive before DE to keep positions easier
                    //todo: needs fixing
                    (if(der) shift(PosInExpr(1 :: Nil), derive)(pos) else ident) &
                      DE(pos) &
                      shift(PosInExpr(1 :: Nil), Dassignb)(pos)*getODEDim(sequent, pos) &
                      //@note DW after DE to keep positions easier
                      (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                      abstractionb(pos)
                  }
                }
              }
              )(pos)
          Dconstify(t)(pos)
        }
      }
    }
  }

  /** @see [[TactixLibrary.diffVar]] */
  val diffVar: DependentPositionTactic = new DependentPositionTactic("diffVar") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        //require(pos.isSucc, "diffVar only at ODE system in succedent")
        val greater = sequent.sub(pos) match {
          case Some(Diamond(ODESystem(_,True), _: GreaterEqual)) => true
          case Some(Diamond(ODESystem(_,True), _: LessEqual)) => false
          case _ => throw new IllegalArgumentException("diffVar currently only implemented at ODE system with postcondition f>=g or f<=g and domain true, but got " + sequent.sub(pos))
        }
        val t = (if (greater)
          useAt("DV differential variant >=")
        else
          useAt("DV differential variant <="))(pos) & (
          // \exists e_ (e_>0 & [{c&true}](f(||)<=g(||) -> f(||)'>=g(||)'+e_))
          derive(pos ++ PosInExpr(0::1::1::1::0::Nil)) &
            derive(pos ++ PosInExpr(0::1::1::1::1::0::Nil)) &
            DE(pos ++ PosInExpr(0::1::Nil)) &
            (Dassignb(pos ++ PosInExpr(0::1::1::Nil))*getODEDim(sequent, pos) &
              abstractionb(pos ++ PosInExpr(0::1::Nil)) & QE & done
              )
          )
        t
      }
    }
  }

  /** @see [[TactixLibrary.dC()]] */
  def diffCut(formulas: Formula*): DependentPositionTactic =
    "dC" byWithInputs (formulas.toList, (pos, sequent) => {
      formulas.map(ghostDC(_, pos, sequent)(pos)).foldRight[BelleExpr](skip)((cut, all) => cut & Idioms.?(<(all, skip)))
    })

  /** Looks for special 'old' function symbol in f and creates DC (possibly with ghost) */
  private def ghostDC(f: Formula, origPos: Position, origSeq: Sequent): DependentPositionTactic = "ANON" by ((pos: Position, seq: Sequent) => {
    lazy val (ode, dc) = seq.sub(pos) match {
      case Some(Box(os: ODESystem, _)) => (os, DC _)
      case Some(Diamond(os: ODESystem, _)) => (os, DCd _)
    }

    val ov = oldVars(f)
    if (ov.isEmpty) {
      if (FormulaTools.conjuncts(f).toSet.subsetOf(FormulaTools.conjuncts(ode.constraint).toSet)) skip else dc(f)(pos)
    } else {
      var freshOld = TacticHelper.freshNamedSymbol(Variable("old"), origSeq)
      val ghosts: List[((Term, Variable), BelleExpr)] = ov.map(old => {
        val (ghost: Variable, ghostPos: Option[Position]) = old match {
          case v: Variable =>
            origSeq.ante.zipWithIndex.find({
              //@note heuristic to avoid new ghosts on repeated old(v) usage
              case (Equal(x0: Variable, x: Variable), _) => v==x && x0.name==x.name
              case _ => false
            }).map[(Variable, Option[Position])]({ case (Equal(x0: Variable, _), i) => (x0, Some(AntePosition.base0(i))) }).
              getOrElse((TacticHelper.freshNamedSymbol(v, origSeq), None))
          case _ =>
            origSeq.ante.zipWithIndex.find({
              //@note heuristic to avoid new ghosts on repeated old(v) usage
              case (Equal(x0: Variable, t: Term), _) => old==t && x0.name == "old"
              case _ => false
            }).map[(Variable, Option[Position])]({ case (Equal(x0: Variable, _), i) => (x0, Some(AntePosition.base0(i))) }).
              getOrElse({
                val fo = freshOld
                freshOld = Variable("old", Some(freshOld.index.getOrElse(-1) + 1))
                (fo, None)
              })
        }
        (old -> ghost,
          ghostPos match {
            case None if pos.isTopLevel => discreteGhost(old, Some(ghost))(pos) & DLBySubst.assignEquality(pos) &
              TactixLibrary.exhaustiveEqR2L(hide=false)('Llast)
            case Some(gp) if pos.isTopLevel => TactixLibrary.exhaustiveEqR2L(hide=false)(gp)
            case _ if !pos.isTopLevel => discreteGhost(old, Some(ghost))(pos)
          })
      }).toList
      val posIncrements = if (pos.isTopLevel) 0 else ghosts.size
      val oldified = replaceOld(f, ghosts.map(_._1).toMap)
      if (FormulaTools.conjuncts(oldified).toSet.subsetOf(FormulaTools.conjuncts(ode.constraint).toSet)) skip
      else ghosts.map(_._2).reduce(_ & _) & dc(oldified)(pos ++ PosInExpr(List.fill(posIncrements)(1)))
    }
  })

  /** Returns a set of variables that are arguments to a special 'old' function */
  private def oldVars(fml: Formula): Set[Term] = {
    var oldVars = Set[Term]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case FuncOf(Function("old", None, Real, Real, false), t: Term) => oldVars += t; Left(None)
        case _ => Left(None)
      }
    }, fml)
    oldVars
  }

  /** Replaces any old(.) with . in formula fml */
  private def replaceOld(fml: Formula, ghostsByOld: Map[Term, Variable]): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case FuncOf(Function("old", None, Real, Real, false), t: Term) => Right(ghostsByOld(t))
        case _ => Left(None)
      }
    }, fml) match {
      case Some(g) => g
    }
  }

  /** @see [[TactixLibrary.diffInvariant]] */
  def diffInvariant(formulas: Formula*): DependentPositionTactic =
    "diffInvariant" byWithInputs (formulas.toList, (pos, sequent) => {
      //@note assumes that first subgoal is desired result, see diffCut
      //@note UnifyUSCalculus leaves prereq open at last succedent position
      val diffIndAllButFirst = skip +: Seq.tabulate(formulas.length)(_ => diffInd()(SuccPosition.base0(sequent.succ.size-1, pos.inExpr)) & QE & done)
      diffCut(formulas: _*)(pos) <(diffIndAllButFirst:_*)
    })

  /** Inverse differential cut, removes the last conjunct from the evolution domain constraint. */
  def inverseDiffCut: DependentPositionTactic = "dCi" by ((pos: Position, s: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)
    val fact = s.at(pos) match {
      case (ctx, fml: Modal) =>
        val (remainder, last) = fml.program match {
          case ODESystem(_, And(l, r)) => (l, r)
          case ODESystem(_, edc) => (True, edc)
        }
        val factFml =
          if (polarity > 0) Imply(last, Imply(fml.replaceAt(PosInExpr(0::1::Nil), remainder), fml))
          else Imply(last, Imply(fml, ctx(fml.replaceAt(PosInExpr(0::1::Nil), remainder))))
        proveBy(factFml,
          implyR(1)*2 & diffCut(last)(if (polarity > 0) -2 else 1) <(
            Idioms.?(useAt("true&")(-2, PosInExpr(0::1::Nil))) & close
            ,
            cohideOnlyR('Rlast) & diffInd()(1) & DebuggingTactics.done
          )
        )
    }

    useAt(fact, PosInExpr(1::(if (polarity > 0) 1 else 0)::Nil))(pos)
  })

  /**
   * Turns things that are constant in ODEs into function symbols.
    *
    * @example Turns v>0, a>0 |- [v'=a;]v>0, a>0 into v>0, a()>0 |- [v'=a();]v>0, a()>0
   * @return The tactic.
   */
  def Dconstify(inner: BelleExpr): DependentPositionTactic = TacticFactory.anon ((pos: Position, seq: Sequent) => {
    seq.sub(pos) match {
      case Some(Box(ode@ODESystem(_, _), p)) =>
        val consts = (StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.filter(_.isInstanceOf[BaseVariable])
        consts.foldLeft[BelleExpr](inner)((tactic, c) =>
          let(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c, tactic))
      case Some(Diamond(ode@ODESystem(_, _), p)) =>
        val consts = (StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.filter(_.isInstanceOf[BaseVariable])
        consts.foldLeft[BelleExpr](inner)((tactic, c) =>
          let(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c, tactic))
    }
  })

  /** DG: Differential Ghost add auxiliary differential equations with extra variables `y'=a*y+b`.
    * `[x'=f(x)&q(x)]p(x)` reduces to `\exists y [x'=f(x),y'=a*y+b&q(x)]p(x)`.
    *
    * @example{{{
    *         |- \exists y [{x'=2,y'=0*y+1}]x>0
    *         ---------------------------------- DG("{y'=0*y+1}".asDifferentialProgram)(1)
    *         |- [{x'=2}]x>0
    * }}}
    * @example{{{
    *         |- \exists y [{x'=2,y'=f()*y+g() & x>=0}]x>0
    *         --------------------------------------------- DG("{y'=f()*y+g()}".asDifferentialProgram)(1)
    *         |- [{x'=2 & x>=0}]x>0
    * }}}
    * @param ghost A differential program of the form y'=a*y+b or y'=a*y or y'=b.
    * @see [[dG()]]
    */
  private def DG(ghost: DifferentialProgram): DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => {
    val (y, a, b) = DifferentialHelper.parseGhost(ghost)

    sequent.sub(pos) match {
      case Some(Box(ode@ODESystem(c, h), p)) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(a).contains(y) && !StaticSemantics.symbols(b).contains(y) =>
                
        //SOUNDNESS-CRITICAL: DO NOT ALLOW SINGULARITIES IN GHOSTS.
        //@TODO This is a bit hacky. We should either:
        //  1) try to cut <(nil, dI(1)) NotEqual(v, Number(0)) before doing
        //     the ghost, and only check for that here; or
        //  2) insist on NotEqual and provide the user with an errormessage.
        //But ultimately, we need a systematic way of checking this in the
        //core (last-case resort could always just move this check into the core and apply
        //it whenever DG differential ghost is applied, but that's pretty
        //hacky).
        val singular = {
          val evDomFmls = flattenConjunctions(h)
          (FormulaTools.singularities(a) ++ FormulaTools.singularities(b)).filter(v =>
            !evDomFmls.contains(Less(v, Number(0)))     &&
            !evDomFmls.contains(Less(Number(0), v))     &&
            !evDomFmls.contains(Greater(v, Number(0)))  &&
            !evDomFmls.contains(Greater(Number(0), v))  &&
            !evDomFmls.contains(NotEqual(v, Number(0))) &&
            !evDomFmls.contains(Greater(Number(0), v))  
          )
        }

        if (!singular.isEmpty) 
          throw new BelleThrowable("Possible singularities during DG(" + ghost + ") will be rejected: " + 
            singular.mkString(",") + " in\n" + sequent.prettyString +
            "\nWhen dividing by a variable v, try cutting v!=0 into the evolution domain constraint"
          )

        (a, b) match {
          case (Number(n), _) if n == 0 =>
            val subst = (us: Option[Subst]) => us.getOrElse(throw BelleUnsupportedFailure("DG expects substitution result from unification")) ++ RenUSubst(
              (Variable("y_",None,Real), y) ::
                (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b) :: Nil)
            useAt("DG differential ghost constant", PosInExpr(0::Nil), subst)(pos)
          case _ =>
            val subst = (us: Option[Subst]) => us.getOrElse(throw BelleUnsupportedFailure("DG expects substitution result from unification")) ++ RenUSubst(
              (Variable("y_",None,Real), y) ::
                (UnitFunctional("a", Except(Variable("y_", None, Real)), Real), a) ::
                (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b) :: Nil)

            useAt("DG differential ghost", PosInExpr(0::Nil), subst)(pos)
        }
    }
  })

  /** @see [[TactixLibrary.dG]] */
  def dG(ghost: DifferentialProgram, r: Option[Formula]): DependentPositionTactic = "dG" byWithInputs (
      r match { case Some(rr) => ghost :: rr :: Nil case None => ghost :: Nil },
      (pos: Position, sequent: Sequent) => r match {
        case Some(rr) if r != sequent.sub(pos ++ PosInExpr(1::Nil)) => DG(ghost)(pos) & transform(rr)(pos ++ PosInExpr(0::1::Nil))
        case _ => DG(ghost)(pos) //@note no r or r==p
      })

  /**
    * Removes the left-most DE from a system of ODEs:
    * {{{
    *   [v'=a,t'=1 & q]p
    *   ---------------------- dGi
    *   [x'=v,v'=a,t'=1 & q]p
    * }}}
    */
  def inverseDiffGhost: DependentPositionTactic = "dGi" by ((pos: Position, s: Sequent) => {
    val polarity = (if (pos.isSucc) 1 else -1) * FormulaTools.polarityAt(s(pos.top), pos.inExpr)
    s.sub(pos) match {
      case Some(f@Box(ODESystem(DifferentialProduct(y_DE: AtomicODE, _), _), _)) if polarity > 0 =>
        val axiomName = "DG inverse differential ghost implicational"
        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then performing rewriting.
        TactixLibrary.cutAt(Forall(y_DE.xp.x::Nil, f))(pos) <(
          HilbertCalculus.useExpansionAt(axiomName)(pos)
          ,
          (if (pos.isSucc) TactixLibrary.cohideR(pos.top) else TactixLibrary.cohideR('Rlast)) &
            HilbertCalculus.useAt("all eliminate")(1, PosInExpr((if (pos.isSucc) 0 else 1) +: pos.inExpr.pos)) &
            TactixLibrary.useAt(DerivedAxioms.implySelf)(1) & TactixLibrary.closeT & DebuggingTactics.done
        )
      case Some(Box(ODESystem(DifferentialProduct(y_DE: AtomicODE, c), q), p)) if polarity < 0 =>
        //@note must substitute manually since DifferentialProduct reassociates (see cutAt) and therefore unification won't match
        val subst = (_: Option[TactixLibrary.Subst]) =>
          RenUSubst(
            ("y_".asTerm, y_DE.xp.x) ::
              ("b(|y_|)".asTerm, y_DE.e) ::
              ("q(|y_|)".asFormula, q) ::
              (DifferentialProgramConst("c", Except("y_".asVariable)), c) ::
              ("p(|y_|)".asFormula, p.replaceAll(y_DE.xp.x, "y_".asVariable)) ::
              Nil)

        //Cut in the right-hand side of the equivalence in the [[axiomName]] axiom, prove it, and then rewrite.
        HilbertCalculus.useAt(", commute", PosInExpr(1::Nil))(pos) &
          TactixLibrary.cutAt(Exists(y_DE.xp.x::Nil, Box(ODESystem(DifferentialProduct(c, y_DE), q), p)))(pos) <(
            HilbertCalculus.useAt("DG differential ghost constant", PosInExpr(1::Nil), subst)(pos)
            ,
            (if (pos.isSucc) TactixLibrary.cohideR(pos.top) else TactixLibrary.cohideR('Rlast)) &
              TactixLibrary.CMon(pos.inExpr) & TactixLibrary.implyR(1) &
              TactixLibrary.existsR(y_DE.xp.x)(1) & TactixLibrary.closeId
          )
    }
  })

  /** @see [[HilbertCalculus.Derive.Dvar]] */
  //@todo could probably simplify implementation by picking atomic formula, using "x' derive var" and then embedding this equivalence into context by CE.
  //@todo Or, rather, by using CE directly on a "x' derive var" provable fact (z)'=1 <-> z'=1.
  lazy val Dvariable: DependentPositionTactic = new DependentPositionTactic("Dvariable") {
    private val OPTIMIZED = true //@todo true
    private val axiom = AxiomInfo("x' derive var commuted")
    private val (keyCtx:Context[_],keyPart) = axiom.formula.at(PosInExpr(1::Nil))
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {

      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(Differential(x: Variable)) =>
          if (OPTIMIZED) {
            logger.debug("Dvariable " + keyPart + " on " + x)
            val fact = UnificationMatch.apply(keyPart, Differential(x)).toForward(axiom.provable)
            CEat(fact)(pos)
          } else {
            val withxprime: Formula = sequent.replaceAt(pos, DifferentialSymbol(x)).asInstanceOf[Formula]
            val axiom = s"\\forall ${x.prettyString} (${x.prettyString})' = ${x.prettyString}'".asFormula
            cutLR(withxprime)(pos.topLevel) <(
              /* use */ skip,
              /* show */ cohide(pos.top) & CMon(formulaPos(sequent(pos.top), pos.inExpr)) & cut(axiom) <(
              useAt("all eliminate")(-1) & eqL2R(-1)(1) & useAt("-> self")(1) & close,
              cohide('Rlast) & byUS(DerivedAxioms.Dvariable))
              )
          }
        }
      }

    /** Finds the first parent of p in f that is a formula. Returns p if f at p is a formula. */
    private def formulaPos(f: Formula, p: PosInExpr): PosInExpr = {
      f.sub(p) match {
        case Some(_: Formula) => p
        case _ => formulaPos(f, p.parent)
      }
    }
  }

  /**
   * Unpacks the evolution domain of an ODE at time zero. Useful for proofs that rely on contradictions with other
   * conditions at time zero preventing continuous evolution in the ODE.
   * {{{
   *  x<0, x>=0 |- [x'=3,y'=2 & x>=0]y>0
   *  -----------------------------------diffUnpackEvolutionDomainInitially(1)
   *        x<0 |- [x'=3,y'=2 & x>=0]y>0
   * }}}
   */
  lazy val diffUnpackEvolutionDomainInitially: DependentPositionTactic = "diffUnpackEvolDomain" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(ODESystem(_, q), _)) =>
      require(pos.isSucc && pos.isTopLevel, "diffUnpackEvolDomain only at top-level in succedent")
      cut(q) <(
        /* use */ skip,
        /* show */ DI(pos) & implyR(pos) & closeIdWith('Llast)
        )
  })

  /** diffWeaken by diffCut(consts) <(diffWeakenG, V&close) */
  lazy val diffWeaken: DependentPositionTactic = "dW" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(a: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeaken only at top level in succedent")

      if (sequent.succ.size <= 1) {
        val primedVars = DifferentialHelper.getPrimedVariables(a)

        val rewriteExistingGhosts = sequent.ante.zipWithIndex.filter({
          case (Equal(l: Variable, r: Variable), _) => primedVars.contains(r) && !primedVars.contains(l)
          case _ => false
        }).reverse.map({ case (_, i) => exhaustiveEqR2L(hide=true)(AntePosition.base0(i)) }).
          reduceOption[BelleExpr](_&_).getOrElse(skip)


        val storeInitialVals = "ANON" by ((seq: Sequent) => {
          val anteSymbols = seq.ante.flatMap(StaticSemantics.symbols)
          val storePrimedVars = primedVars.filter(anteSymbols.contains)
          storePrimedVars.
            map(discreteGhost(_)(pos)).reduceOption[BelleExpr](_&_).getOrElse(skip) &
            (DLBySubst.assignEquality(pos) & exhaustiveEqR2L(hide=true)('Llast))*storePrimedVars.size
        })

        val dw = "ANON" by ((seq: Sequent) => {
          diffWeakenG(pos) & implyR(1) & andL('Llast)*seq.ante.size & implyRi
        })

        val cutAllAntes = "ANON" by ((seq: Sequent) => {
          if (seq.ante.isEmpty) skip
          //@note all ante formulas rewritten to initial values at this point
          else diffCut(seq.ante.reduceRight(And))(pos) <(
            skip,
            V('Rlast) & (andR('Rlast) <(closeIdWith('Rlast) & done, skip))*(seq.ante.size-1) & closeIdWith('Rlast) & done
          )
        })

        rewriteExistingGhosts & storeInitialVals & cutAllAntes & dw
      } else {
        useAt("DW differential weakening")(pos) & abstractionb(pos) & (allR('Rlast)*)
      }
  })

  /** diffWeaken by DW & G */
  lazy val diffWeakenG: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(_: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeakenG only at top level in succedent")
      cohide(pos.top) & DW(1) & G(1)
  })

  //A user-friendly error message displayed when ODE can't find anything useful to do.
  private val failureMessage = "The automatic tactic does not currently provide automated proving capabilities for this " +
    "combination of system and post-condition. Consider using the individual ODE tactics and/or submitting a feature request."

  /**
    * @see [[TactixLibrary.ODE]]
    * @author Andre Platzer
    * @author Nathan Fulton
    */
  lazy val ODE: DependentPositionTactic = "ODE" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Box(ODESystem(ode, q), _)) =>
      val odeAtoms = DifferentialHelper.atomicOdes(ode).toSet
      val qAtoms = FormulaTools.conjuncts(q).toSet
      ODE(introduceStuttering=true,
        //@note abort if unchanged
        assertT((sseq: Sequent, ppos: Position) => sseq.sub(ppos) match {
          case Some(Box(ODESystem(extendedOde, extendedQ), _)) =>
            odeAtoms.subsetOf(DifferentialHelper.atomicOdes(extendedOde).toSet) ||
            qAtoms.subsetOf(FormulaTools.conjuncts(extendedQ).toSet)
          case _ => false
        }, failureMessage)(pos) &
          ("ANON" by ((ppos: Position, sseq: Sequent) => sseq.sub(ppos) match {
            case Some(ODESystem(_, extendedQ)) =>
              if (q == True) useAt("true&")(ppos ++
                PosInExpr(1 +: FormulaTools.posOf(extendedQ, q).getOrElse(PosInExpr.HereP).pos.dropRight(1)))
              else skip
          }))(pos ++ PosInExpr(0::Nil))
    )(pos)
  })
  def ODE(introduceStuttering: Boolean, finish: BelleExpr): DependentPositionTactic = "ODE" by ((pos: Position, seq: Sequent) => {
    val invariantCandidates = try {
      InvariantGenerator.differentialInvariantGenerator(seq,pos)
    } catch {
      case err: Exception =>
        logger.warn("Failed to produce a proof for this ODE. Underlying cause: ChooseSome: error listing options " + err)
        List[Formula]().iterator
    }

    //Tries to prove without any invariant generation or solving.
    val proveWithoutCuts = "ANON" by ((pos: Position) => {
      ((boxAnd(pos) & andR(pos))*) &
        onAll(("ANON" by ((pos: Position, seq: Sequent) => {
          val (ode:ODESystem, post:Formula) = seq.sub(pos) match {
            case Some(Box(ode: ODESystem, pf)) => (ode, pf)
            case Some(ow) => throw new BelleThrowable("ill-positioned " + pos + " does not give a differential equation in " + seq)
            case None => throw new BelleThrowable("ill-positioned " + pos + " undefined in " + seq)
          }

          val bounds = StaticSemantics.boundVars(ode.ode).symbols //@note ordering irrelevant, only intersecting/subsetof
          val frees = StaticSemantics.freeVars(post).symbols      //@note ordering irrelevant, only intersecting/subsetof

          val isOpen = post match {
            case  _: Greater => true
            case _: Less => true
            case _ => false
          }

          //@note diffWeaken will already include all cases where V works, without much additional effort.
          (if (frees.intersect(bounds).subsetOf(StaticSemantics.freeVars(ode.constraint).symbols))
            diffWeaken(pos) & QE(Nil, None, Some(Integer.parseInt(Configuration(Configuration.Keys.ODE_TIMEOUT_FINALQE)))) & done else fail
          ) |
          ( DebuggingTactics.assert((invSeq: Sequent, invPos: Position) => {
              invSeq.sub(invPos) match {
                case Some(Box(ode@ODESystem(_, q), invCandidate)) => ToolProvider.invGenTool() match {
                  case Some(invTool) => invTool.lzzCheck(ode, invCandidate)
                  case _ => true
                }
                case _ => false
              }
            }, "Invariant fast-check failed")(pos) &
            (if (isOpen) {
              (openDiffInd(pos) | DGauto(pos)) //> TODO: needs updating
            } else {
              diffInd()(pos)       | // >= to >=
                (dgBarrier(ToolProvider.simplifierTool())(pos) & done) |
                (dgDbxAuto(pos) & done) |
                DGauto(pos)          |
                dgZeroMonomial(pos)  | //Equalities
                dgZeroPolynomial(pos)  //Equalities
            })
          )
        })) (pos))
    })

    //Adds an invariant to the system's evolution domain constraint and tries to establish the invariant via proveWithoutCuts.
    //Fails if the invariant cannot be established by proveWithoutCuts.
    val addInvariant = ChooseSome(
      () => invariantCandidates,
      (inv: Formula) => {
        debug(s"[ODE] Trying to cut in invariant candidate: $inv", true) &
        /*@note diffCut skips previously cut in invs, which means <(...) will fail and we try the next candidate */
        diffCut(inv)(pos) <(skip, proveWithoutCuts(pos) & done)
      }
    )

    //If lateSolve is true then diffSolve will be run last, if at all.
    val insistOnProof = pos.isTopLevel //@todo come up wtih better heuristic for determining when to insist on a proof being completed. Solvability is a pretty decent heuristic.

    /** Introduces stuttering assignments for each BV of the ODE */
    val stutter = "ANON" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(a: ODESystem, _)) =>
        val primedVars = StaticSemantics.boundVars(a).toSet[Variable].filter(_.isInstanceOf[BaseVariable])
        primedVars.map(DLBySubst.stutter(_)(pos ++ PosInExpr(1::Nil))).reduceOption[BelleExpr](_&_).getOrElse(skip)
    })

    val unstutter = "ANON" by ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Box(a: ODESystem, _)) =>
        val primedVars = StaticSemantics.boundVars(a).toSet[Variable].filter(_.isInstanceOf[BaseVariable])
        (1 to primedVars.size).reverse.map(i => ?(assignb(pos ++ PosInExpr(List.fill(i)(1))))).
          reduceOption[BelleExpr](_&_).getOrElse(skip)
      case _ => skip
    })

    //The tactic:
    //@todo do at least proveWithoutCuts before diffSolve, but find some heuristics for figuring out when a simpler argument will do the trick.
    if (insistOnProof)
      proveWithoutCuts(pos)        |
      (addInvariant & ODE(introduceStuttering,finish)(pos))    |
      TactixLibrary.solve(pos) |
      splitWeakInequality(pos)<(ODE(introduceStuttering,finish)(pos), ODE(introduceStuttering,finish)(pos)) |
      (if (introduceStuttering) stutter(pos) & ODE(introduceStuttering=false,finish)(pos) & unstutter(pos)
       else finish)
    else
      (proveWithoutCuts(pos) & done)   |
      (addInvariant & ODE(introduceStuttering,finish)(pos) & done) |
      TactixLibrary.solve(pos)     |
      (splitWeakInequality(pos)<(ODE(introduceStuttering,finish)(pos), ODE(introduceStuttering,finish)(pos)) & done) |
      (if (introduceStuttering) stutter(pos) & ODE(introduceStuttering=false,finish)(pos) & unstutter(pos) & done
       else finish)
  })

  /** Splits a post-condition containing a weak inequality into an open set case and an equillibrium point case.
    * Given a formula of the form [ode]p<=q, produces two new subgoals of the forms [ode]p < q and  [ode]p=q.
    * @see http://nfulton.org/2017/01/14/Ghosts/#ghosts-for-closedclopen-sets
    * @author Nathan Fulton */
  def splitWeakInequality : DependentPositionTactic = "splitWeakInequality" by ((pos: Position, seq: Sequent) => {
    val postcondition = seq.at(pos)._2 match {
      case Box(ODESystem(_,_), p) => p
      case _ => throw new BelleThrowable("splitWeakInequality is only applicable for ODE's with weak inequalities as post-conditions.")
    }
    val (lhs, rhs, openSetConstructor) = postcondition match {
      case GreaterEqual(l,r) => (l,r,Greater)
      case LessEqual(l,r)    => (l,r,Less)
      case _                 => throw new BelleThrowable(s"splitWeakInequality Expected a weak inequality in the post condition (<= or >=) but found: ${postcondition}")
    }

    val caseDistinction = Or(openSetConstructor(lhs,rhs), Equal(lhs,rhs))

    cut(caseDistinction) <(
      orL('Llast) <(
        generalize(openSetConstructor(lhs,rhs))(1) <(skip, QE & done),
        generalize(Equal(lhs,rhs))(1) <(skip, QE & done)
      )
      ,
      (hide(pos.topLevel) & QE & done) | //@todo write a hideNonArithmetic tactic.
      DebuggingTactics.assert(_=>false, s"splitWeakInequality failed because $caseDistinction does not hold initially.")
    )
  })

  def dgZeroPolynomial : DependentPositionTactic = "dgZeroPolynomial" by ((pos: Position, seq:Sequent) => {
    val Some(Box(ODESystem(system, constraint), property)) = seq.sub(pos)

    val lhs = property match {
      case Equal(term, Number(n)) if n == 0 => term
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}")
    }

    val (x: Variable, derivative:Term) = system match {
      case AtomicODE(xp, t) => (xp.x, t)
      case _ => throw new BelleThrowable("Systems not currently supported by dgZeroPolynomialDerivative")
    }
    require(lhs == x, "Currently require that the post-condition is of the form x=0 where x is the primed variable in the ODE.")

    val ghostVar = "z_".asVariable
    require(!StaticSemantics.vars(system).contains(ghostVar), "fresh ghost " + ghostVar + " in " + system.prettyString) //@todo should not occur anywhere else in the sequent either...

    val negOneHalf: Term = Divide(Number(-1), Number(2))
    //Given a system of the form x'=f(x), this returns (f(x))'/x simplified so that x does not occur on the denom.
    //@note this is done because we can't ghost in something that contains a division by a possibly zero-valued variable (in this case, x).
    val xPrimeDividedByX = TacticHelper.transformMonomials(derivative, (t:Term) => t match {
      case Times(coeff, Power(v,exp)) if(v == x) => 
        Times(coeff, Power(v, Minus(exp, Number(1))))
      case Times(coeff, v:Variable) if(v==x) => coeff
      case v:Variable if(v==x) => Number(1)
      case t:Term => t
    })

    /* construct the arguments ti diff aux:
     * y' = -xPrimeDividedByX/2 * y
     * x=0 <-> \exists y x*y^2=0 & y>0 */
    //@todo At some point I was not sure if this works for no exponent (i.e. x, x+x, x+x+x and so on b/c of the pattern matching in dgZero. But it does. So review dgZero and this to see what's up.
    val (ghostODE, ghostEqn) = (
      AtomicODE(DifferentialSymbol(ghostVar), Times(Times(negOneHalf,xPrimeDividedByX) , ghostVar)),
      And(
        Equal(
          Times(x, Power(ghostVar, Number(2)) ),
          Number(0)
        ),
        Greater(ghostVar, Number(0))
      )
    )

    dG(ghostODE, Some(ghostEqn))(pos) & boxAnd(pos ++ PosInExpr(0::Nil)) &
      DifferentialTactics.diffInd()(pos ++ PosInExpr(0::0::Nil)) &
      //@note would be more robust to do the actual derivation here the way it's done in [[AutoDGTests]], but I'm leaving it like this so that we can find the bugs/failures in DGauto
      DGauto(pos ++ PosInExpr(0::1::Nil)) & QE & done
  })

  /** Proves properties of the form {{{x=0&n>0 -> [{x^n}]x=0}}}
    * @todo make this happen by usubst. */
  def dgZeroMonomial : DependentPositionTactic = "dgZeroMonomial" by ((pos: Position, seq:Sequent) => {
    if (ToolProvider.algebraTool().isEmpty) throw new BelleThrowable(s"dgZeroEquilibrium requires a AlgebraTool, but got None")

    val Some(Box(ODESystem(system, constraint), property)) = seq.sub(pos)

    /** The lhs of the post-condition {{{lhs = 0}}} */
    val lhs = property match {
      case Equal(term, Number(n)) if n == 0 => term
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}")
    }

    /** The equation in the ODE of the form {{{x'=c*x^n}}}; the n is optional.
      * @todo make this tactic work for systems of ODEs. */
    val (x: Variable, (c: Option[Term], n: Option[Term])) = system match {
      case AtomicODE(variable, equation) => (variable.x, equation match {
        case Times(c, Power(variable, n)) => (Some(c), Some(n))
        case Times(c, v:Variable) if v==variable.x => (Some(c), None)
        case Power(variable, n) => (None, Some(n))
        case v:Variable if v==variable.x => (None, None)
      })
    }
    require(lhs == x, "Currently require that the post-condition is of the form x=0 where x is the primed variable in the ODE.")

    /** The ghost variable */
    val ghostVar = "z_".asVariable
    require(!StaticSemantics.vars(system).contains(ghostVar), "fresh ghost " + ghostVar + " in " + system.prettyString) //@todo should not occur anywhere else in the sequent either...


    val (newOde: DifferentialProgram, equivFormula: Formula) = (c,n) match {
      case (Some(c), Some(n)) => (
        s"$ghostVar' = ( (-1*$c * $x^($n-1)) / 2) * $ghostVar + 0".asDifferentialProgram,
        s"$x*$ghostVar^2=0&$ghostVar>0".asFormula
      )
      case (None, Some(n)) => (
        s"$ghostVar' = ((-1*$x^($n-1)) / 2) * $ghostVar + 0".asDifferentialProgram,
        s"$x*$ghostVar^2=0&$ghostVar>0".asFormula
      )
      case (Some(c), None) => (
        s"$ghostVar' = ((-1*$c*$x) / 2) * $ghostVar + 0".asDifferentialProgram,
        s"$x*$ghostVar^2=0&$ghostVar>0".asFormula
      )
      case (None, None) => (
        s"$ghostVar' = -1 * $ghostVar + 0".asDifferentialProgram,
        s"$x * $ghostVar = 0 & $ghostVar > 0".asFormula
      )
    }

    val backupTactic = dG(newOde, Some(equivFormula))(pos) & boxAnd(pos ++ PosInExpr(0::Nil)) &
      DifferentialTactics.diffInd()(pos ++ PosInExpr(0::0::Nil)) &
      //@note would be more robust to do the actual derivation here the way it's done in [[AutoDGTests]], but I'm leaving it like this so that we can find the bugs/failures in DGauto
      DGauto(pos ++ PosInExpr(0::1::Nil)) & QE & done

    //@todo massage the other cases into a useAt.
    //@note it's more robust if we do the | backupTactic, but I'm ignore thins so that we can find and fix the bug in (this use of) useAt.
    if(c.isDefined && n.isDefined) //if has correct shape for using the derived axiom
      TactixLibrary.useAt("dgZeroEquilibrium")(1) //| backupTactic
    else
      backupTactic
  })

  /**
    * Proves Darboux properties
    * p = 0 -> [ {ODE & Q} ] p = 0
    * where Q -> p' = q p
    * (similarly for >= 0, > 0, != 0)
    * Note: this also works for fractional q, if its denominator is already in Q
    * Otherwise, DG will fail on the singularity
    */
  def dgDbx(qco: Term): DependentPositionWithAppliedInputTactic = "dbx" byWithInput (qco, (pos: Position, seq:Sequent) => {

    val Some(Box(ODESystem(system, _), property)) = seq.sub(pos)

    /** The argument works for any comparison operator */
    val (p,pop) = property match {
      case bop:ComparisonFormula if bop.right.isInstanceOf[Number] && bop.right.asInstanceOf[Number].value == 0 =>
        (bop.left,bop)
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}")
    }

    /** The ghost variable */
    val gvy = "dbxy_".asVariable
    require(!StaticSemantics.vars(system).contains(gvy), "fresh ghost " + gvy + " in " + system.prettyString)
    //@todo should not occur anywhere else in the sequent either...

    /** Another ghost variable */
    val gvz = "dbxz_".asVariable
    require(!StaticSemantics.vars(system).contains(gvz), "fresh ghost " + gvz + " in " + system.prettyString)
    //@todo should not occur anywhere else in the sequent either...

    //Construct the diff ghost y' = -qy
    val dey = AtomicODE(DifferentialSymbol(gvy), Times(Neg(qco),gvy))
    //Diff ghost z' = qz/2
    val dez = AtomicODE(DifferentialSymbol(gvz), Times(Divide(qco,Number(2)),gvz))

    val zero = Number(0)
    val one = Number(1)
    val two = Number(2)

    //Postcond:
    //For equalities, != 0 works too, but the > 0 works for >=, > as well
    val gtz = Greater(gvy,zero)
    val pcy = And(gtz, pop.reapply(Times(gvy,p),zero))
    val pcz = Equal(Times(gvy,Power(gvz,two)), one)

    DebuggingTactics.debug("Darboux postcond "+pcy.toString+" "+pcz.toString) &
      dG(dey,Some(pcy))(pos) &     //Introduce the dbx ghost
      existsR(one)(pos) &          //Anything works here, as long as it is > 0, 1 is convenient
      diffCut(gtz)(pos) <(
        boxAnd(pos) & andR(pos) <(
          dW(pos) & prop,
          diffInd('full)(pos)) // Closes p z = 0 invariant
      ,
        dG(dez,Some(pcz))(pos) &     //Introduce the dbx ghost
        existsR(one)(pos) &          //The sqrt inverse of y, 1 is convenient
        diffInd('full)(pos)          // Closes z > 0 invariant with another diff ghost
      )
  })

  /**
    * This tactic is EXPERIMENTAL: it requires the use of max in a ghost
    * Proves a strict barrier certificate property
    * p >~ 0 -> [ {ODE & Q} ] p >~ 0
    * where Q & p = 0 -> p' > 0
    * works for both > and >= (and <, <=)
    * Soundness note: this uses a ghost that is not smooth
    */
  private val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  private val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)

  def dgBarrier(tool: Option[SimplificationTool] = None): DependentPositionTactic = "barrier" by ((pos: Position, seq:Sequent) => {

    val Some(Box(ODESystem(system, dom), property)) = seq.sub(pos)

    val (barrier,flip) = property match {
      case GreaterEqual(lhs, rhs) => (Minus(lhs,rhs),false)
      case Greater(lhs, rhs) => (Minus(lhs,rhs),false)
      case LessEqual(lhs, rhs) => (Minus(lhs,rhs),true)
      case Less(lhs, rhs) => (Minus(lhs,rhs),true)
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}")
    }

    val lie = DifferentialSaturation.simplifiedLieDerivative(system, barrier, tool)

    val zero = Number(0)
    //The special max term
    val barrierAlg = if (flip) FuncOf(maxF,Pair(Times(barrier,barrier),Neg(lie))) else FuncOf(maxF,Pair(Times(barrier,barrier),lie))
    val barrierFml = Greater(barrierAlg,zero)
    //The cofactor
    val cofactor = Divide(Times(barrier,lie),barrierAlg)

    // First cut in the barrier property, then use dgdbx on it
    dC(barrierFml)(pos) <(
      dgDbx(cofactor)(pos),
      dW(pos) & QE
    )
  })

  //Keeps the top level =s in evol domain as a groebner basis of terms?
  private def domToTerms(f:Formula) : List[Term] = {
    f match {
      case Equal(l,r) => Minus(l,r) :: Nil
      case And(l,r) => domToTerms(l) ++ domToTerms(r)
      case _ => Nil
    }
  }

  //Pulls out divisions
  private def stripDenom(t:Term) : (Term,Term) = {
    t match {
      case Times(l,r) =>
        val (ln,ld) = stripDenom(l)
        val (rn,rd) = stripDenom(r)
        (Times(ln,rn),Times(ld,rd))
      case Divide(l,r) =>
        val (ln,ld) = stripDenom(l)
        val (rn,rd) = stripDenom(r)
        (Times(ln,rd),Times(ld,rn))
      case Power(tt,p:Number) if p.value < 0 =>
        (Number(1),Power(tt,Number(-p.value)))
      case Power(tt,p) =>
        val (tn,td) = stripDenom(tt)
        (Power(tn,p),Power(td,p))
      //Ignore everything else todo: could deal with common denominators
      case _ => (t,Number(1))
    }
  }

  private lazy val eqNorm: ProvableSig = proveBy(" f_() = g_() <-> f_()-g_() = 0 ".asFormula,QE)
  // Normalises to p = 0
  // then attempts to automatically guess the darboux cofactor
  def dgDbxAuto: DependentPositionTactic = "dbx" by ((pos: Position, seq:Sequent) => {
    if (ToolProvider.algebraTool().isEmpty) throw new BelleThrowable("dgDbxAuto requires a AlgebraTool, but got None")

    val Some(Box(ODESystem(system, dom), property)) = seq.sub(pos)

    val (p,bop) = property match {
      case bop:ComparisonFormula =>
        (Minus(bop.left,bop.right),bop)
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}")
    }

    val lie = DifferentialHelper.lieDerivative(system, p)
    val algTool = ToolProvider.algebraTool().get
    //val gb = p::domToTerms(dom)
    val domterms = domToTerms(dom)
    //todo: groebnerBasis seems broken for > 1 term??
    //todo: comment above might require own MathematicaToKeYmaera converter,
    //      since the default converter for QE accepts lists of length=2 only to represent Pairs
    val gb = if (domterms.nonEmpty) {
      try { algTool.groebnerBasis(domterms) } catch { case _: ToolException => Nil }
    } else Nil
    val quo = algTool.polynomialReduce(lie,p::gb)
    // quo._1.head is the cofactor of p
    // quo._2 is the remainder
    // For =darboux, attempt proof of quo._2 = 0
    // For >=,> , attempt proof of quo._2 >=0 (and similarly for <=,<)
    val cofactor = quo._1.head
    val rem = quo._2
    val (num,den) = stripDenom(cofactor) //Need to put it in a form that DG can understand

    //println("poly: "+p+" cofactor: "+cofactor+" rem: "+rem)
    val zero = Number(0)

    val remSgn = bop match {
      case GreaterEqual(lhs, rhs) => GreaterEqual(rem,zero)
      case Greater(lhs, rhs) => GreaterEqual(rem,zero)
      case LessEqual(lhs, rhs) => LessEqual(rem,zero)
      case Less(lhs, rhs) => LessEqual(rem,zero)
      case Equal(_,_) => Equal(rem,zero)
      case _ => throw new BelleThrowable(s"Not sure what to do with shape ${seq.sub(pos)}")
    }

    val denRemReq = And(NotEqual(den,zero),remSgn)

    val denRemReqTactic = (t: BelleExpr) =>
      if ((FormulaTools.conjuncts(denRemReq).toSet -- FormulaTools.conjuncts(dom)).isEmpty) {
        t
      } else {
        //First, attempt to prove denominator non-zero, and the remainder has appropriate sign
        diffCut(denRemReq)(pos) <(
          t,
          //Leaves the denonominator goal open if it isn't implied by DW
          ?(dW(pos) & QE & done)
        )
      }


    denRemReqTactic(
      // use dgDbx
      diffCut(bop.reapply(p,zero))(pos) <(
        dW(pos) & QE & done
        ,
        dgDbx(Divide(num,den))(pos)
      )
    )
  })

  /** @see [[TactixLibrary.DGauto]]
    * @author Andre Platzer */
  def DGauto: DependentPositionTactic = "DGauto" by ((pos:Position,seq:Sequent) => {
    if (ToolProvider.algebraTool().isEmpty) throw new BelleThrowable("DGAuto requires a AlgebraTool, but got None")
    /** a-b with some simplifications */
    def minus(a: Term, b: Term): Term = b match {
      case Number(n) if n == 0 => a
      case _ => a match {
        case Number(n) if n == 0 => Neg(b)
        case _ => Minus(a, b)
      }
    }
    val (quantity: Term, ode: DifferentialProgram) = seq.sub(pos) match {
      case Some(Box(ODESystem(o, _), Greater(a, b))) => (minus(a, b), o)
      case Some(Box(ODESystem(o, _), Less(a, b))) => (minus(b, a), o)
      case e => throw new BelleThrowable("DGauto does not support argument shape: " + e)
    }
    //@todo find a ghost that's not in ode
    val ghost: Variable = Variable("y_")
    require(!StaticSemantics.vars(ode).contains(ghost), "fresh ghost " + ghost + " in " + ode)
    // [x':=f(x)](quantity)'
    val lie = DifferentialHelper.lieDerivative(ode, quantity)

    lazy val constrGGroebner: Term = {
      val groebnerBasis: List[Term] = ToolProvider.algebraTool().getOrElse(throw new BelleThrowable("DGAuto requires an AlgebraTool, but got None")).groebnerBasis(
        quantity :: Nil)
      ToolProvider.algebraTool().getOrElse(throw new BelleThrowable("DGAuto requires an AlgebraTool, but got None")).polynomialReduce(
        lie match {
          case Minus(Number(n), l) if n == 0 => l //@note avoid negated ghost from (f()-x)'
          case _ => lie
        },
        groebnerBasis.map(Times(Number(-2), _))
      )._1.head
    }

    val odeBoundVars = StaticSemantics.boundVars(ode).symbols[NamedSymbol].toList.filter(_.isInstanceOf[BaseVariable]).sorted.map(_.asInstanceOf[BaseVariable])
    val constrG: Term = ToolProvider.algebraTool().getOrElse(throw new BelleThrowable("DGAuto requires an AlgebraTool, but got None")).quotientRemainder(
      lie, Times(Number(-2), quantity), odeBoundVars.headOption.getOrElse(Variable("x")))._1

    // Formula that must be valid: quantity <-> \exists ghost. quantity * ghost^2 > 0
    // Ghosted-in differential equation: ghost' = constrG*ghost + 0
    def dg(g: Term): BelleExpr = {
      val de = AtomicODE(DifferentialSymbol(ghost), Plus(Times(g, ghost), Number(0)))
      val p = Greater(Times(quantity, Power(ghost, Number(2))), Number(0))
      DebuggingTactics.debug(s"DGauto: trying $de with $p") &
      dG(de,Some(p))(pos) & diffInd()(pos ++ PosInExpr(0::Nil)) & QE & done
    }

    // try guessing first, groebner basis if guessing fails
    dg(constrG) | TacticFactory.anon((seq: Sequent) => dg(constrGGroebner))
  })

  /** Search-and-rescue style DGauto.
    * @author Andre Platzer
    */
  def DGautoSandR: DependentPositionTactic = "DGauto" by ((pos:Position,seq:Sequent) => {
    if (!ToolProvider.solverTool().isDefined) throw new BelleThrowable("DGAuto requires a SolutionTool, but got None")
    /** a-b with some simplifications */
    def minus(a: Term, b: Term): Term = b match {
      case Number(n) if n==0 => a
      case _ => a match {
        case Number(n) if n==0 => Neg(b)
        case _ => Minus(a,b)
      }
    }
    val (quantity: Term, ode: DifferentialProgram) = seq.sub(pos) match {
      case Some(Box(ODESystem(ode, _), Greater(a, b))) => (minus(a,b), ode)
      case Some(Box(ODESystem(ode, _), Less(a, b))) => (minus(b,a), ode)
      case e => throw new BelleThrowable("DGauto does not support argument shape: " + e)
    }
    //@todo find a ghost that's not in ode
    val ghost: Variable = Variable("y_")
    require(!StaticSemantics.vars(ode).contains(ghost), "fresh ghost " + ghost + " in " + ode)
    val spooky: Term = if (false) //@todo ultimate substitution won't work if it ain't true. But intermediate semantic renaming won't work if it's false.
      UnitFunctional("jj",Except(ghost),Real)
    else
      FuncOf(Function("jj",None,Unit,Real),Nothing) //Variable("jj")
    //@todo should allocate space maybe or already actually by var in this lambda
    var constructedGhost: Option[Term] = None
    // proper search & rescue tactic
    val SandR: BelleExpr = LetInspect(
      spooky,
      (pr:ProvableSig) => {
        assume(pr.subgoals.length==1, "exactly one subgoal from DA induction step expected")
        logger.debug("Instantiate::\n" + pr)
        // induction step condition \forall x \forall ghost condition>=0
        val condition = FormulaTools.kernel(pr.subgoals.head.succ.head) match {
          case Imply(domain, GreaterEqual(condition, Number(n))) if n==0 => condition
          case GreaterEqual(condition, Number(n)) if n==0 => condition
          case _ => throw new AssertionError("DGauto: Unexpected shape " + pr)
        }
        //@todo a witness of Reduce of >=0 would suffice
        logger.debug("Solve[" + condition + "==0" + "," + spooky + "]")
        ToolProvider.solverTool().getOrElse(throw new BelleThrowable("DGAuto requires a SolutionTool, but got None")).solve(Equal(condition, Number(0)), spooky::Nil) match {
          case Some(Equal(l,r)) if l==spooky => logger.debug("Need ghost " + ghost + "'=(" + r + ")*" + ghost + " for " + quantity)
            constructedGhost = Some(r)
            r
          case None => logger.debug("Solve[" + condition + "==0" + "," + spooky + "]")
            throw new BelleThrowable("DGauto could not solve conditions: " + condition + ">=0")
          case Some(stuff) => logger.debug("Solve[" + condition + "==0" + "," + spooky + "]")
            throw new BelleThrowable("DGauto got unexpected solution format: " + condition + ">=0\n" + stuff)
        }
      }
      ,
      dG(AtomicODE(DifferentialSymbol(ghost), Plus(Times(spooky, ghost), Number(0))),
        Some(Greater(Times(quantity, Power(ghost,Number(2))), Number(0)))
      )(pos) & diffInd()(pos ++ PosInExpr(0::Nil))
    ) & QE & done
    // fallback rescue tactic if proper misbehaves
    val fallback: DependentPositionTactic = "ANON" by ((pos:Position,seq:Sequent) => {
      logger.debug("DGauto falling back on ghost " + ghost + "'=(" + constructedGhost + ")*" + ghost)
      // terrible hack that accesses constructGhost after LetInspect was almost successful except for the sadly failing usubst in the end.
      dG(AtomicODE(DifferentialSymbol(ghost), Plus(Times(constructedGhost.getOrElse(throw new BelleThrowable("DGauto construction was unsuccessful in constructing a ghost")), ghost), Number(0))),
        Some(Greater(Times(quantity, Power(ghost, Number(2))), Number(0)))
      )(pos) <(
        QE & done,
        //@todo could optimize for RCF cache when doing the same decomposition as during SandR
        //diffInd()(pos ++ PosInExpr(1::Nil)) & QE
        implyR(pos) & diffInd()(pos) & QE & done
        )
    })
    SandR | fallback(pos)
  })

  //A start on the LZZ procedure
  /**
    * Vectorial Darboux, currently just constructs and returns an appropriate provable
    * because we do not yet have vectorial dG
    *
    * @param odesys the ODE system
    * @param Gco the cofactor matrix
    * @param p the polynomial vector
    * @return provable with extra ghosts
    */

  def dgVdbx(odesys : ODESystem,Gco:List[List[Term]],p:List[Term]) : ProvableSig = {
    val dim = p.length
    assert(Gco.length == dim && Gco.forall(gs => gs.length == dim))
    val diffeqs = odesys.ode
    val dom = odesys.constraint

    val ghostPrefix = "vdbxy_"
    //Doubly indexed ghost variables
    val ghostVars = List.range(0,dim).map( i => List.range(0,dim).map( j => Variable(ghostPrefix,Some(i*dim+j))))
    println("Ghost vars: "+ghostVars)

    val Gcotrans = Gco.transpose

    //Construct the system of equations
    val ghostRHS = List.range(0,dim).map( i => matvec_prod(Gcotrans,ghostVars(i)).map(t => Neg(t)))
    val ghostEqs = (ghostVars zip ghostRHS).map(p => p._1 zip p._2)
    //Each ghostEqs at this point is a separate vectorial diff ghost
    //We could also work directly with the flattened versions, but this is just for easier portability when we get vDG
    println("Ghost eqs: "+ghostEqs)

    //For now, construct the differential equations obtained from ghosts
    val ghostDiffEqs = ghostEqs.flatten.map(p => AtomicODE(DifferentialSymbol(p._1),p._2)).reduce(DifferentialProduct.apply)
    val ghostSys = ODESystem(DifferentialProduct(diffeqs,ghostDiffEqs),dom)
    println("Extended system: "+ghostSys)

    val zero = Number(0)
    val one = Number(1)
    //Constructing the p=0 invariant (using conjunctions)
    val inv = p.foldLeft[Formula](True)((fml,trm)=> And(Equal(trm,zero),fml))
    val boxfml = Box(ghostSys,inv)
    val fml = ghostVars.foldRight[Formula](boxfml)((vs,fml)=> (vs.foldRight[Formula](fml)((v,fml)=>Exists(v::Nil,fml))))
    println("Formula: "+fml)

    //Finally, we can now prove the invariant property
    val seq = ProvableSig.startProof( Imply(inv,fml) )
    println("Seq: "+seq)

    val determinant = sym_det(ghostVars)
    val trace = sym_trace(Gco)
    println("Symbolic Det: "+determinant)
    println("Symbolic Trace: "+trace)

    //Relevant tactics

    //Explicitly instantiate the sequence of ghost variables with the identity matrix
    val idExistsTac = List.range(0,dim).map( i => List.range(0,dim).map( j => existsR(Variable(ghostPrefix,Some(i*dim+j)),
      if(i==j) one else zero)))
    val idExistsTacPos = idExistsTac.foldRight(skip)( (exts,tac) => exts.foldRight(tac)( (ext,tac) => ext(1) & tac )  )

    //Cut in the symbolic dot products p.y = 0
    val dotprods = ghostVars.map( ls => Equal(dot_prod(ls,p),zero))
    val dITac = diffInvariant(dotprods:_*)(1)

    val pr = proveBy(seq,
      implyR(1) & idExistsTacPos & dITac &
      diffCut(Greater(determinant,zero))(1) <(
        dW(1) & QE,
        //Prove Darboux invariance for the determinant
        dgDbx(Neg(trace))(1))
    )

    pr
  }

  // implementation helpers

  //Explicit symbolic expression for the determinant of a matrix
  //Currently just explicitly calculated, but can use Mathematica's det if available
  //Also, this probably doesn't actually need to be explicitly calculated everytime since we always apply it on ghost variables
  private def sym_det (m:List[List[Term]]) : Term = {
    val dim = m.length
    assert(m.forall(ls => ls.length == dim))
    if(dim==1)
      return m(0)(0)
    else if(dim==2) //det ((a b)(c d)) = a d - b c
      return Minus(Times(m(0)(0),m(1)(1)),Times(m(0)(1),m(1)(0)))
    else if(dim==3) //det ((a b c)(d e f)(g h i)) = -c e g + b f g + c d h - a f h - b d i + a e i
      ???
    else
      ???
  }

  //Symbolic trace
  private def sym_trace (m:List[List[Term]]) : Term = {
    val dim = m.length
    assert(m.forall(ls => ls.length == dim))
    return List.range(0,dim).map(i=>m(i)(i)).foldLeft[Term](Number(0))(Plus.apply)
  }

  // Symbolic matrix and vector products, assuming that the dimensions all match up
  private def dot_prod (v1:List[Term],v2:List[Term]) : Term = {
    val zipped = (v1 zip v2).map({case (t1,t2)=>Times(t1,t2)})
    return zipped.reduce(Plus.apply)
  }

  private def matvec_prod (m:List[List[Term]],v:List[Term]) : List[Term] ={
    return m.map(ls => dot_prod(ls,v))
  }

  @deprecated("Possible duplicate of DifferentialHelper.flattenAnds")
  private def flattenConjunctions(f: Formula): List[Formula] = {
    var result: List[Formula] = Nil
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = f match {
        case And(l, r) => result = result ++ flattenConjunctions(l) ++ flattenConjunctions(r); Left(Some(ExpressionTraversal.stop))
        case a => result = result :+ a; Left(Some(ExpressionTraversal.stop))
      }
    }, f)
    result
  }

  //@todo possibly should ask StaticSemantics.boundVars(ode).filter(_.isInstanceOf[DifferentialSymbol)
  private def primedSymbols(ode: DifferentialProgram) = {
    var primedSymbols = Set[Variable]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case DifferentialSymbol(ps) => primedSymbols += ps; Left(None)
        case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
        case _ => Left(None)
      }
    }, ode)
    primedSymbols
  }

  /** Indicates whether there is an ODE at the indicated position of a sequent */
  private val isODE: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(_: ODESystem, _))     => true
      case Some(Diamond(_: ODESystem, _)) => true
      case Some(e) => false
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Indicates whether there is a proper ODE System at the indicated position of a sequent with >=2 ODEs */
  private val isODESystem: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ODESystem(_:DifferentialProduct,_), _))     => true
      case Some(Diamond(ODESystem(_:DifferentialProduct,_), _)) => true
      case Some(e) => false
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Computes the dimension of ODE at indicated position of a sequent */
  private[btactics] val getODEDim: (Sequent,Position)=>Int = (sequent,pos) => {
    def odeDim(ode: ODESystem): Int = StaticSemantics.boundVars(ode).symbols.count(_.isInstanceOf[DifferentialSymbol])
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => odeDim(ode)
      case Some(Diamond(ode: ODESystem, _)) => odeDim(ode)
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Whether the ODE at indicated position of a sequent has a nontrivial domain */
  private val hasODEDomain: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => ode.constraint != True
      case Some(Diamond(ode: ODESystem, _)) => ode.constraint != True
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }


  private def dottedSymbols(ode: DifferentialProgram) = {
    var dottedSymbols = List[Variable]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case DifferentialSymbol(ps) => ps :: dottedSymbols; Left(None)
        case Differential(_) => throw new IllegalArgumentException("Only derivatives of variables supported")
        case _ => Left(None)
      }
    }, ode)
    dottedSymbols.reverse
  }

  /** @see [[TactixLibrary.dC()]] */
  val contInvGen: DependentPositionTactic = new DependentPositionTactic("contInvGen") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        val (ode, postcond) = sequent.sub(pos) match {
          case Some(Box(odesys: ODESystem, post: Formula)) => (odesys, post)
          case _ => throw new IllegalArgumentException("Not a continuous safety goal " + sequent.sub(pos))
        }

        val continvs: Seq[Formula] = ToolProvider.invGenTool().
          getOrElse(throw new BelleThrowable("InvGenTool needed, but got None")).
          invgen(ode, sequent.ante, postcond)

        diffCut(continvs:_*)(pos)
      }
    }
  }

}
