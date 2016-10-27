package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.bellerophon.UnificationMatch
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.tools.ODESolverTool

import scala.collection.immutable
import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps

/**
 * Implementation: provides tactics for differential equations.
  *
  * @note Container for "complicated" tactics. Single-line implementations are in [[TactixLibrary]].
 * @see [[TactixLibrary.DW]], [[TactixLibrary.DC]]
 */
private object DifferentialTactics {

  /** @see [[HilbertCalculus.DE]] */
  lazy val DE: DependentPositionTactic = new DependentPositionTactic("DE") {
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
        //@todo wrap within a CE to make sure it also works in context
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
        case _ => println("Unsure how to predict DE outcome for " + fml); ???
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

  /** @see [[TactixLibrary.diffInd]] */
  def diffInd(auto: Symbol = 'full): DependentPositionTactic = new DependentPositionTactic("diffInd") {
    require(auto == 'full || auto == 'none || auto == 'diffInd, "Expected one of ['none, 'diffInd, 'full] automation values, but got " + auto)
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc && (sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _)) => true
          case _ => false
        }), "diffInd only at ODE system in succedent, but got " + sequent.sub(pos))
        if (pos.isTopLevel) {
          val t = DI(pos) &
            (implyR(pos) & andR(pos)) <(
              if (auto == 'full) close | QE else skip,
              if (auto != 'none) {
                //@note derive before DE to keep positions easier
                derive(pos ++ PosInExpr(1 :: Nil)) &
                DE(pos) &
                (if (auto == 'full) Dassignb(pos ++ PosInExpr(1::Nil))*getODEDim(sequent, pos) &
                  //@note DW after DE to keep positions easier
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) & abstractionb(pos) & (close | QE)
                 else {
                  assert(auto == 'diffInd)
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                  abstractionb(pos) & (allR(pos)*) & ?(implyR(pos)) }) partial
              } else skip
              )
          if (auto == 'full) Dconstify(t)(pos)
          else t
        } else {
          val t = DI(pos) &
            (if (auto != 'none) {
              shift(PosInExpr(1 :: 1 :: Nil), new DependentPositionTactic("Shift") {
                override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
                  override def computeExpr(sequent: Sequent): BelleExpr = {
                    //@note derive before DE to keep positions easier
                    shift(PosInExpr(1 :: Nil), derive)(pos) &
                      DE(pos) &
                      (if (auto == 'full) shift(PosInExpr(1 :: Nil), Dassignb)(pos)*getODEDim(sequent, pos) &
                        //@note DW after DE to keep positions easier
                        (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                        abstractionb(pos)
                      else abstractionb(pos))
                  }
                }
              }
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
        val greater = sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _: Greater)) => true
          case Some(Box(_: ODESystem, _: Less)) => false
          case _ => throw new IllegalArgumentException("openDiffInd only at ODE system in succedent with postcondition f>g or f<g, but got " + sequent.sub(pos))
        }
        if (pos.isTopLevel) {
          val t = (
            if (greater)
              HilbertCalculus.namedUseAt("DIogreater", "DIo open differential invariance >")
            else
              HilbertCalculus.namedUseAt("DIoless", "DIo open differential invariance <"))(pos) <(
              testb(pos) & (close | QE),
              //@note derive before DE to keep positions easier
              implyR(pos) & derive(pos ++ PosInExpr(1::1::Nil)) &
                DE(pos) &
                (Dassignb(pos ++ PosInExpr(1::Nil))*getODEDim(sequent, pos) &
                  //@note DW after DE to keep positions easier
                  (if (hasODEDomain(sequent, pos)) DW(pos) else skip) & abstractionb(pos) & (close | QE)
                  ) partial
              )
          Dconstify(t)(pos)
        } else {
          //@todo positional tactics need to be adapted
          val t = (
            if (greater)
              HilbertCalculus.namedUseAt("DIogreater", "DIo open differential invariance >")
            else
              HilbertCalculus.namedUseAt("DIoless", "DIo open differential invariance <"))(pos) &
              shift(PosInExpr(1 :: 1 :: Nil), new DependentPositionTactic("Shift") {
                override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
                  override def computeExpr(sequent: Sequent): BelleExpr = {
                    //@note derive before DE to keep positions easier
                    shift(PosInExpr(1 :: Nil), derive)(pos) &
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
          HilbertCalculus.namedUseAt("DVgeq", "DV differential variant >=")
        else
          HilbertCalculus.namedUseAt("DVleq", "DV differential variant <="))(pos) & (
          // \exists e_ (e_>0 & [{c&true}](f(||)<=g(||) -> f(||)'>=g(||)'+e_))
          derive(pos ++ PosInExpr(0::1::1::1::0::Nil)) &
            derive(pos ++ PosInExpr(0::1::1::1::1::0::Nil)) &
            DE(pos ++ PosInExpr(0::1::Nil)) &
            (Dassignb(pos ++ PosInExpr(0::1::1::Nil))*getODEDim(sequent, pos) &
              abstractionb(pos ++ PosInExpr(0::1::Nil)) & QE
              )
          )
        t
      }
    }
  }

  /** @see [[TactixLibrary.diffCut()]] */
  def diffCut(formulas: Formula*): DependentPositionTactic =
    "diffCut" byWithInputs (formulas.toList, (pos, sequent) => {nestDCs(formulas.map(ghostDC(_, pos, sequent)))})

  /** Looks for special 'old' function symbol in f and creates DC (possibly with ghost) */
  private def ghostDC(f: Formula, pos: Position, sequent: Sequent): BelleExpr = {
    val ov = oldVars(f)
    if (ov.isEmpty) {
      DC(f)(pos)
    } else {
      val ghosts: List[((Term, Variable), BelleExpr)] = ov.map(old => {
        val ghost = old match {
          case v: Variable => TacticHelper.freshNamedSymbol(v, sequent)
          case _ => TacticHelper.freshNamedSymbol(Variable("old"), sequent)
        }
        (old -> ghost,
          discreteGhost(old, Some(ghost))(pos) & DLBySubst.assignEquality(pos))
      }).toList
      ghosts.map(_._2).reduce(_ & _) & DC(replaceOld(f, ghosts.map(_._1).toMap))(pos)
    }
  }

  /** Turns a list of diff cuts (with possible 'old' ghost creation) tactics into nested DCs */
  private def nestDCs(dcs: Seq[BelleExpr]): BelleExpr = {
    dcs.head <(
      /* use */ (if (dcs.tail.nonEmpty) nestDCs(dcs.tail) partial else skip) partial,
      /* show */ skip
      )
  }

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
      //@todo why is this 'Rlast instead of pos?
      val diffIndAllButFirst = skip +: Seq.tabulate(formulas.length)(_ => diffInd()('Rlast))
      diffCut(formulas: _*)(pos) <(diffIndAllButFirst:_*) partial
    })

  /**
   * Turns things that are constant in ODEs into function symbols.
    *
    * @example Turns v>0, a>0 |- [v'=a;]v>0, a>0 into v>0, a()>0 |- [v'=a();]v>0, a()>0
   * @return The tactic.
   */
  def Dconstify(inner: BelleExpr): DependentPositionTactic = new DependentPositionTactic("IDC introduce differential constants") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(Box(ode@ODESystem(_, _), p)) =>
          val consts = (StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.
            filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])
          consts.foldLeft[BelleExpr](inner)((tactic, c) =>
            let(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c, tactic))
        case Some(Diamond(ode@ODESystem(_, _), p)) =>
          val consts = (StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.
            filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])
          consts.foldLeft[BelleExpr](inner)((tactic, c) =>
            let(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c, tactic))
      }
    }
  }

  /** @see [[TactixLibrary.DG]] */
  def DG(ghost: DifferentialProgram): DependentPositionTactic = "DGTactic" byWithInputs (listifiedGhost(ghost), (pos: Position, sequent: Sequent) => {
    val (y, a, b) = parseGhost(ghost)
    sequent.sub(pos) match {
      case Some(Box(ode@ODESystem(c, h), p)) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(a).contains(y) && !StaticSemantics.symbols(b).contains(y) =>
        val singular = FormulaTools.singularities(a) ++ FormulaTools.singularities(b)
        if (!singular.isEmpty) throw new BelleError("Possible singularities during DG(" + ghost + ") will be rejected: " + singular.mkString(",") + " in\n" + sequent.prettyString)

        val subst = (us: Subst) => us ++ RenUSubst(
          (Variable("y_",None,Real), y) ::
          (UnitFunctional("a", Except(Variable("y_", None, Real)), Real), a) ::
          (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b) :: Nil)

        useAt("DG differential ghost", PosInExpr(0::Nil), subst)(pos)
    }
  })

  private def listifiedGhost(ghost: DifferentialProgram): List[Expression] = {
    val ghostParts = try {
      parseGhost(ghost)
    } catch {
      case ex: CoreException => throw new BelleError("Unable to parse ghost " + ghost.prettyString, ex)
    }
    List(ghostParts._1, ghostParts._2, ghostParts._3)
  }

  def diffGhost(ghost: DifferentialProgram, initialValue: Term) = "diffGhost" byWithInputs (/* match AxiomInfo arguments */ listifiedGhost(ghost) :+ initialValue, (pos: Position, sequent: Sequent) => {
    DG(ghost)(pos) &
    DLBySubst.assignbExists(initialValue)(pos) &
    DLBySubst.assignEquality(pos)
  })

  /** Split a differential program into its ghost constituents: parseGhost("y'=a*x+b".asProgram) is (y,a,b) */
  private def parseGhost(ghost: DifferentialProgram): (Variable,Term,Term) = {
    UnificationMatch.unifiable("{y_'=a(|y_|)*y_+b(|y_|)}".asDifferentialProgram, ghost) match {
      case Some(s) => (s("y_".asVariable).asInstanceOf[Variable], s("a(|y_|)".asTerm), s("b(|y_|)".asTerm))
      case None => UnificationMatch.unifiable("{y_'=a(|y_|)*y_}".asDifferentialProgram, ghost) match {
        case Some(s) => (s("y_".asVariable).asInstanceOf[Variable], s("a(|y_|)".asTerm), "0".asTerm)
        case None => UnificationMatch.unifiable("{y_'=b(|y_|)}".asDifferentialProgram, ghost) match {
          case Some(s) => (s("y_".asVariable).asInstanceOf[Variable], "0".asTerm, s("b(|y_|)".asTerm))
          case None => UnificationMatch.unifiable("{y_'=a(|y_|)*y_-b(|y_|)}".asDifferentialProgram, ghost) match {
            case Some(s) => (s("y_".asVariable).asInstanceOf[Variable], s("a(|y_|)".asTerm), Neg(s("b(|y_|)".asTerm)))
            case None => UnificationMatch.unifiable("{y_'=y_}".asDifferentialProgram, ghost) match {
              case Some(s) => (s("y_".asVariable).asInstanceOf[Variable], "1".asTerm, "0".asTerm)
              case None => UnificationMatch.unifiable("{y_'=-y_}".asDifferentialProgram, ghost) match {
                case Some(s) => (s("y_".asVariable).asInstanceOf[Variable], "-1".asTerm, "0".asTerm)
                case None => throw new IllegalArgumentException("Ghost is not of the form y'=a*y+b or y'=a*y or y'=b or y'=a*y-b or y'=y")
              }
            }
          }
        }
      }
    }
  }

  /** @see [[TactixLibrary.DA]] */
  def DA(ghost: DifferentialProgram, r: Formula): DependentPositionTactic =
    "DA2" by ((pos: Position) => {
      val (y,a,b) = parseGhost(ghost)
      DA(y, a, b, r)(pos)
    })

  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and postcondition replaced by r.
    * {{{
    * G |- p(x), D   |- r(x,y) -> [x'=f(x),y'=g(x,y)&q(x)]r(x,y)
    * ----------------------------------------------------------  DA using p(x) <-> \exists y. r(x,y) by QE
    * G |- [x'=f(x)&q(x)]p(x), D
    * }}}
    *
    * @see[[DA(Variable, Term, Term, Provable)]]
    * @note Uses QE to prove p(x) <-> \exists y. r(x,y)
    */
  @deprecated("Use DA(\"{y'=a*y+b}\".asDifferentialProgram, r) instead.")
  def DA(y: Variable, a: Term, b: Term, r: Formula): DependentPositionTactic =
    "DA4" byWithInputs(List(r,y,a,b),(pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(Box(_: ODESystem, p)) => DA(y, a, b, proveBy(Equiv(p, Exists(y::Nil, r)), TactixLibrary.QE))(pos)
    })



  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and postcondition replaced by r.
    * {{{
    * G |- p(x), D   |- r(x,y) -> [x'=f(x),y'=g(x,y)&q(x)]r(x,y)
    * ----------------------------------------------------------  DA using p(x) <-> \exists y. r(x,y) by auxEquiv
    * G |- [x'=f(x)&q(x)]p(x), D
    * }}}
    */
  //@todo replace this by an interface DifferentialProgram, Provable, because DG(DifferentialProgram) is called from here anyhow.
  @deprecated("Use DA(DifferentialProgram, Provable) instead")
  def DA(y: Variable, a: Term, b: Term, auxEquiv: Provable): DependentPositionTactic =
    "DAbase" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(Box(ode@ODESystem(c, h), p)) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(a).contains(y) && !StaticSemantics.symbols(b).contains(y) => null

        val Equiv(p, _) = auxEquiv.conclusion.succ.head

        cutR(p)(pos.checkSucc.top) <(
          skip,
          implyR(pos) & useAt("TODODAbaseaux", auxEquiv, PosInExpr(0::Nil))('Llast) & existsL('Llast) &
            DG(AtomicODE(DifferentialSymbol(y), Plus(Times(a, y), b)))(pos) &
            existsR(pos) & ?(exhaustiveEqR2L(hide=true)('Llast)) &
            useAt("TODODAbaseaux", auxEquiv, PosInExpr(0::Nil))(pos ++ PosInExpr(1::Nil)) &
            existsR(pos ++ PosInExpr(1::Nil)) & implyRi(AntePos(sequent.ante.length), pos.checkSucc.top)
          )
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
            if (DEBUG) println("Dvariable " + keyPart + " on " + x)
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

  /** @see [[TactixLibrary.diffSolve]] */
  def diffSolve(solution: Option[Formula] = None, preDITactic: BelleExpr = skip)(tool: ODESolverTool): DependentPositionTactic = "diffSolve" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(odes: ODESystem, _)) =>
      require(pos.isSucc && pos.isTopLevel, "diffSolve only at top-level in succedent")

      val time: Variable = TacticHelper.freshNamedSymbol(Variable("t_", None, Real), sequent)
      val introTime =
        DG(AtomicODE(DifferentialSymbol(time), Plus(Times("0".asTerm, time), "1".asTerm)))(pos) &
            DLBySubst.assignbExists("0".asTerm)(pos) &
            DLBySubst.assignEquality(pos)

      def createTactic(ode: ODESystem, solution: Formula, time: Variable, iv: Map[Variable, Variable],
                       diffEqPos: SeqPos): BelleExpr = {
        val initialGhosts = (primedSymbols(ode.ode) + time).foldLeft(skip)((a, b) =>
          a & (discreteGhost(b)(diffEqPos) & DLBySubst.assignEquality(diffEqPos)))

        // flatten conjunctions and sort by number of right-hand side symbols to approximate ODE dependencies
        val flatSolution = flattenConjunctions(solution).
          sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size)

        diffUnpackEvolutionDomainInitially(diffEqPos) &
          initialGhosts &
          diffInvariant(flatSolution:_*)(diffEqPos) &
          // initial ghosts are at the end of the antecedent
          exhaustiveEqR2L(hide=true)('Llast)*flatSolution.size &
          diffWeaken(diffEqPos)
      }

      // initial values (from only the formula at pos, because allR will increase index of other occurrences elsewhere in the sequent)
      val iv: Map[Variable, Variable] =
        primedSymbols(odes.ode).map(v => v -> TacticHelper.freshNamedSymbol(v, sequent(pos.top))).toMap

      val theSolution = solution match {
        case sol@Some(_) => sol
        case None => tool.odeSolve(odes.ode, time, iv)
      }

      val diffEqPos = SuccPos(sequent.succ.length-1) //@note introTime moves ODE to the end of the succedent
      theSolution match {
        // add relation to initial time
        case Some(s) =>
          val sol = And(s, GreaterEqual(time, Number(0)))
          introTime & createTactic(odes, sol, time, iv, diffEqPos)
        case None => throw new BelleError("No solution found")
      }

  })

  /** diffWeaken by diffCut(consts) <(diffWeakenG, V&close) */
  lazy val diffWeaken: DependentPositionTactic = "diffWeaken" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(a: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeaken only at top level in succedent")

      if (sequent.succ.size <= 1) {
        def constAnteConditions(sequent: Sequent, taboo: Set[Variable]): IndexedSeq[(Formula, Int)] = {
          sequent.ante.zipWithIndex.filter(f => StaticSemantics.freeVars(f._1).intersect(taboo).isEmpty)
        }
        val consts = constAnteConditions(sequent, StaticSemantics(a).bv.toSet)

        if (consts.nonEmpty) {
          val dw = diffWeakenG(pos) & implyR(1) & andL('Llast)*consts.size & implyRi(AntePos(0), SuccPos(0))
          val constFml = consts.map(_._1).reduceRight(And)
          diffCut(constFml)(pos) <(dw, V('Rlast) & (andR('Rlast) <(closeIdWith('Rlast) & done, skip))*(consts.size-1) & closeIdWith('Rlast) & done)
        } else {
          diffWeakenG(pos)
        }
      } else {
        useAt("DW differential weakening")(pos) & abstractionb(pos) & (allR('Rlast)*)
      }
  })

  /** diffWeaken by DW & G */
  lazy val diffWeakenG: DependentPositionTactic = "diffWeakenG" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(_: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeakenG only at top level in succedent")
      cohide(pos.top) & DW(1) & G(1)
  })


  /** @see [[TactixLibrary.ODE]]
    * @author Andre Platzer */
  def ODE: DependentPositionTactic = "ODE" by ((pos:Position,seq:Sequent) => {
    require(pos.isTopLevel && pos.isSucc && isODE(seq,pos), "ODE only applies to differential equations and currently only top-level succedent")
    val noCut = "ANON" by ((pos: Position) =>
      ((boxAnd(pos) & andR(pos))*) &
        onAll(("ANON" by ((pos: Position, seq: Sequent) => {
        val (ode:ODESystem, post:Formula) = seq.sub(pos) match {
          case Some(Box(ode: ODESystem, pf)) => (ode, pf)
          case Some(ow) => throw new IllegalArgumentException("ill-positioned " + pos + " does not give a differential equation in " + seq)
          case None => throw new IllegalArgumentException("ill-positioned " + pos + " undefined in " + seq)
        }
        val bounds = StaticSemantics.boundVars(ode.ode).symbols //@note ordering irrelevant, only intersecting/subsetof
        val frees = StaticSemantics.freeVars(post).symbols      //@note ordering irrelevant, only intersecting/subsetof
        //@note diffWeaken will already include all cases where V works, without much additional effort.
        (if (frees.intersect(bounds).subsetOf(StaticSemantics.freeVars(ode.constraint).symbols))
          diffWeaken(pos) & QE else fail) |
          (if (post match {
            case  _: Greater => true
            case _: Less => true
            case _ => false
          })
          // if openDiffInd does not work for this class of systems, only diffSolve or diffGhost or diffCut
            openDiffInd(pos) | DGauto(pos)
          else
          //@todo check degeneracy for split to > or =
            diffInd()(pos)
              | DGauto(pos)
            )
      })) (pos))
      )

    //@todo in fact even ChooseAll would work, just not recursively so.
    //@todo performance: repeat from an updated version of the same generator until saturation
    //@todo turn this into repeat
    ChooseSome(
      //@todo should memoize the results of the differential invariant generator
      () => InvariantGenerator.differentialInvariantGenerator(seq,pos),
      (inv:Formula) => if (false)
        diffInvariant(inv)(pos)
      else
        diffCut(inv)(pos) <(
          // use diffCut
          skip,
          // show diffCut, but don't use yet another diffCut
          noCut(pos) & done
          )
    ) & ODE(pos) | noCut(pos) |
      // if no differential cut succeeded, just skip and go for a direct proof.
      //@todo could swap diffSolve before above line with noCut once diffSolve quickly detects by dependencies whether it solves
      TactixLibrary.diffSolve()(pos) |
      ChooseSome(
        //@todo should memoize the results of the differential invariant generator
        () => InvariantGenerator.extendedDifferentialInvariantGenerator(seq,pos),
        (inv:Formula) => if (false)
          diffInvariant(inv)(pos)
        else
          diffCut(inv)(pos) <(
            // use diffCut
            skip,
            // show diffCut, but don't use yet another diffCut
            noCut(pos) & done
            )
      ) & ODE(pos)
  })

  /** Proves properties of the form {{{x=0&n>0 -> [{x^n}]x=0}}}
    * @todo make this happen by usubst. */
  def dgZero : DependentPositionTactic = "dgZero" by ((pos: Position, seq:Sequent) => {
    val ONE = Number(1)

    if (ToolProvider.algebraTool().isEmpty) throw new BelleError(s"dgZeroEquilibrium requires a AlgebraTool, but got None")

    val Some(Box(ODESystem(system, constraint), property)) = seq.sub(pos)

    /** The lhs of the post-condition {{{lhs = 0}}} */
    val lhs = property match {
      case Equal(term, Number(n)) if n == 0 => term
      case _ => throw new BelleError(s"Not sure what to do with shape ${seq.sub(pos)}")
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
      case (Some(c), None) => (
        s"$ghostVar' = ((-1*$c*$x) / 2) * $ghostVar + 0".asDifferentialProgram,
        s"$x*$ghostVar^2=0&$ghostVar>0".asFormula
      )
      case (None, Some(n)) => (
        s"$ghostVar' = ((-1*$x^($n-1)) / 2) * $ghostVar + 0".asDifferentialProgram,
        s"$x*$ghostVar^2=0&$ghostVar>0".asFormula
      )
      case (None, None) => (
        s"$ghostVar' = -1 * $ghostVar + 0".asDifferentialProgram,
        s"$x * $ghostVar = 0 & $ghostVar > 0".asFormula
      )
    }

    val backupTactic =
      DA(newOde, equivFormula)(pos) <(
        TactixLibrary.QE,
        implyR(pos) & boxAnd(pos) & andR(pos) <(
          DifferentialTactics.diffInd()(pos) & QE,
          DGauto(pos) //@note would be more robust to do the actual derivation here the way it's done in [[AutoDGTests]], but I'm leaving it like this so that we can find the bugs/failures in DGauto
          )
        )

    //@todo massage the other cases into a useAt.
    //@note it's more robust if we do the | backupTactic, but I'm ignore thins so that we can find and fix the bug in (this use of) useAt.
    if(c.isDefined && n.isDefined) //if has correct shape for using the derived axiom
      TactixLibrary.useAt("dgZeroEquilibrium")(1) //| backupTactic
    else
      backupTactic
  })

  /** @see [[TactixLibrary.DGauto]]
    * @author Andre Platzer */
  def DGauto: DependentPositionTactic = "DGauto" by ((pos:Position,seq:Sequent) => {
    if (ToolProvider.algebraTool().isEmpty) throw new BelleError("DGAuto requires a AlgebraTool, but got None")
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
      case e => throw new BelleError("DGauto does not support argument shape: " + e)
    }
    //@todo find a ghost that's not in ode
    val ghost: Variable = Variable("y_")
    require(!StaticSemantics.vars(ode).contains(ghost), "fresh ghost " + ghost + " in " + ode)
    // [x':=f(x)](quantity)'
    val lie = DifferentialHelper.lieDerivative(ode, quantity)

    lazy val constrGGroebner: Term = {
      val groebnerBasis: List[Term] = ToolProvider.algebraTool().getOrElse(throw new BelleError("DGAuto requires an AlgebraTool, but got None")).groebnerBasis(
        quantity :: Nil)
      ToolProvider.algebraTool().getOrElse(throw new BelleError("DGAuto requires an AlgebraTool, but got None")).polynomialReduce(
        lie match {
          case Minus(Number(n), l) if n == 0 => l //@note avoid negated ghost from (f()-x)'
          case _ => lie
        },
        groebnerBasis.map(Times(Number(-2), _))
      )._1.head
    }

    val odeBoundVars = StaticSemantics.boundVars(ode).symbols[NamedSymbol].toList.filter(_.isInstanceOf[BaseVariable]).sorted.map(_.asInstanceOf[BaseVariable])
    val constrG: Term = ToolProvider.algebraTool().getOrElse(throw new BelleError("DGAuto requires an AlgebraTool, but got None")).quotientRemainder(
      lie, Times(Number(-2), quantity), odeBoundVars.headOption.getOrElse(Variable("x")))._1

    // Formula that must be valid: quantity <-> \exists ghost. quantity * ghost^2 > 0
    // Ghosted-in differential equation: ghost' = constrG*ghost + 0
    def dg(g: Term): BelleExpr = {
      val de = AtomicODE(DifferentialSymbol(ghost), Plus(Times(g, ghost), Number(0)))
      val p = Greater(Times(quantity, Power(ghost, Number(2))), Number(0))
      DebuggingTactics.debug(s"DGauto: trying $de with $p") &
      DA(de,p)(pos) < (
        (close | QE) & done,
        diffInd()(pos ++ PosInExpr(1 :: Nil)) & QE
        )
    }

    // try guessing first, groebner basis if guessing fails
    dg(constrG) | TacticFactory.anon((seq: Sequent) => dg(constrGGroebner))
  })

  /** Search-and-rescue style DGauto.
    * @author Andre Platzer
    */
  def DGautoSandR: DependentPositionTactic = "DGauto" by ((pos:Position,seq:Sequent) => {
    if (!ToolProvider.solverTool().isDefined) throw new BelleError("DGAuto requires a SolutionTool, but got None")
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
      case e => throw new BelleError("DGauto does not support argument shape: " + e)
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
      (pr:Provable) => {
        assume(pr.subgoals.length==1, "exactly one subgoal from DA induction step expected")
        if (BelleExpr.DEBUG) println("Instantiate::\n" + pr)
        // induction step condition \forall x \forall ghost condition>=0
        val condition = FormulaTools.kernel(pr.subgoals.head.succ.head) match {
          case Imply(domain, GreaterEqual(condition, Number(n))) if n==0 => condition
          case GreaterEqual(condition, Number(n)) if n==0 => condition
          case _ => throw new AssertionError("DGauto: Unexpected shape " + pr)
        }
        //@todo a witness of Reduce of >=0 would suffice
        if (BelleExpr.DEBUG) println("Solve[" + condition + "==0" + "," + spooky + "]")
        ToolProvider.solverTool().getOrElse(throw new BelleError("DGAuto requires a SolutionTool, but got None")).solve(Equal(condition, Number(0)), spooky::Nil) match {
          case Some(Equal(l,r)) if l==spooky => if (BelleExpr.DEBUG) println("Need ghost " + ghost + "'=(" + r + ")*" + ghost + " for " + quantity);
            constructedGhost = Some(r)
            r
          case None => if (BelleExpr.DEBUG) println("Solve[" + condition + "==0" + "," + spooky + "]")
            throw new BelleError("DGauto could not solve conditions: " + condition + ">=0")
          case Some(stuff) => if (BelleExpr.DEBUG) println("Solve[" + condition + "==0" + "," + spooky + "]")
            throw new BelleError("DGauto got unexpected solution format: " + condition + ">=0\n" + stuff)
        }
      }
      ,
      DA(AtomicODE(DifferentialSymbol(ghost), Plus(Times(spooky, ghost), Number(0))),
        Greater(Times(quantity, Power(ghost,Number(2))), Number(0))
      )(pos) <(
        (close | QE) & done,
        diffInd()(pos ++ PosInExpr(1::Nil))
          & implyR(pos) // initial assumption
          & implyR(pos) // domain
          & andR(pos) <(
          // initial condition
          (close | QE) & done,
          // universal closure of induction step
          skip
          )
        )
    ) & QE & done;
    // fallback rescue tactic if proper misbehaves
    val fallback: DependentPositionTactic = "ANON" by ((pos:Position,seq:Sequent) => {
      if (BelleExpr.DEBUG) println("DGauto falling back on ghost " + ghost + "'=(" + constructedGhost + ")*" + ghost);
      // terrible hack that accesses constructGhost after LetInspect was almost successful except for the sadly failing usubst in the end.
      DA(AtomicODE(DifferentialSymbol(ghost), Plus(Times(constructedGhost.getOrElse(throw new BelleError("DGauto construction was unsuccessful in constructing a ghost")), ghost), Number(0))),
        Greater(Times(quantity, Power(ghost, Number(2))), Number(0))
      )(pos) <(
        (close | QE) & done,
        //@todo could optimize for RCF cache when doing the same decomposition as during SandR
        //diffInd()(pos ++ PosInExpr(1::Nil)) & QE
        implyR(pos) & diffInd()(pos) & QE & done
        )
    });
    SandR | fallback(pos)
  })



  // implementation helpers

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

  //region DRI proof rule

  private[btactics] val DRIStep = useAt("DRIStep")

  /** Implements the DRI proof rule by successive DRIStep applications followed by a diffWeaken. */
  val DRI: DependentPositionTactic = "DRI" by ((pos: Position) => {
    SaturateTactic(
      DebuggingTactics.debug("Doing a DRIStep", true) &
      DRIStep(pos) & TactixLibrary.andR(pos) & DebuggingTactics.debug("here", true)  <(
        DebuggingTactics.debug("First branch", true) & TactixLibrary.master() & DebuggingTactics.done("f=0 -> f'=0 should close automatically.") //Proves f=0 -> f'=0
        ,
        DebuggingTactics.debug("Second branch", true) & (diffWeaken(pos) & master() & DebuggingTactics.done) | DRI(pos)
      )
    )
  })

  //endregion
}
