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
import edu.cmu.cs.ls.keymaerax.tools.DiffSolutionTool

import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps

/**
 * Implementation: provides tactics for differential equations.
  *
  * @note Container for "complicated" tactics. Single-line implementations are in [[TactixLibrary]].
 * @see [[TactixLibrary.DW]], [[TactixLibrary.DC]]
 */
private object DifferentialTactics {

  def ODE: DependentPositionTactic = "ODE" by ((pos:Position,seq:Sequent) => {require(pos.isTopLevel, "currently only top-level positions are supported")
    ((boxAnd(pos) & andR(pos))*) & onAll(("" by ((pos:Position,seq:Sequent) =>
      (diffWeaken(pos) & QE) |
        (if (seq.sub(pos) match {
          case Some(Box(_: ODESystem, _: Greater)) => true
          case Some(Box(_: ODESystem, _: Less)) => true
          case _ => false})
        // if openDiffInd does not work for this class of systems, only diffSolve or diffGhost
          openDiffInd(pos) | DGauto(pos) | TactixLibrary.diffSolve()(pos)
        else
        //@todo check degeneracy for split to > or =
          diffInd()(pos)
            | DGauto(pos)
            //@todo | diffInvariant(cuts) | DA ...
            | TactixLibrary.diffSolve()(pos)
          ))
      )(pos))
  })

  def DGauto: DependentPositionTactic = "DGauto" by ((pos:Position,seq:Sequent) => {
    //import TactixLibrary._
    val quantity = seq.sub(pos) match {
      case Some(Box(ODESystem(ode, _), Greater(a, b))) => Minus(a,b)
      case Some(Box(ODESystem(ode, _), Less(a, b))) => Minus(b,a)
      case e => throw new BelleError("DGauto does not support argument shape: " + e)
    }
    //@todo find a ghost that's not in ode
    val ghost = Variable("y_")
    val spooky = if (false) //@todo ultimate substitution won't work if it ain't true. But intermediate semantic renaming won't work if it's false.
      UnitFunctional("jj",Except(ghost),Real)
    else
      FuncOf(Function("jj",None,Unit,Real),Nothing) //Variable("jj")
    //@todo should allocate space
    var constructedGhost: Option[Term] = None
    val cleanup = "" by ((pos:Position,seq:Sequent) =>
      // terrible hack that accesses constructGhost after LetInspect was almost successful except for the sadly failing usubst in the end.
      DA(AtomicODE(DifferentialSymbol(ghost), Plus(Times(constructedGhost.getOrElse(throw new BelleError("DGauto construction unsuccessful")), ghost), Number(0))),
        Greater(Times(quantity, Power(ghost,Number(2))), Number(0))
      )(pos) <(
        (close | QE) & done,
        //diffInd()(pos ++ PosInExpr(1::Nil)) & QE
        implyR(pos) & diffInd()(pos) & QE & done
        )
    )
    LetInspect(
      spooky,
      (pr:Provable) => {
        assume(pr.subgoals.length==1, "exactly one subgoal from DA induction step expected")
        println("Instantiate::\n" + pr)
        // induction step condition \forall x \forall ghost condition>=0
        FormulaTools.kernel(pr.subgoals.head.succ.head) match {
          case GreaterEqual(condition, Number(_/*@todo BigDecimal(0)*/)) =>
            //@todo call Mathematica. And in fact a witness of Reduce of >=0 would suffice
            println("Solve[" + condition + "==0" + "," + spooky + "]")
            ToolProvider.solverTool().solve(Equal(condition, Number(0)), spooky::Nil) match {
              case Some(Equal(l,r)) if l==spooky => println("Need ghost " + ghost + "'=" + r + "*" + ghost);
                constructedGhost = Some(r)
                r
              case None => println("Solve[" + condition + "==0" + "," + spooky + "]")
                throw new BelleError("DGauto could not solve conditions: " + condition + ">=0")
              case Some(stuff) => println("Solve[" + condition + "==0" + "," + spooky + "]")
                throw new BelleError("DGauto got unexpected solution format: " + condition + ">=0\n" + stuff)
            }
          case _ => throw new AssertionError("Unexpected shape " + pr)
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
    ) & QE & done | cleanup(pos)
  })

  /**
   * Differential effect: exhaustively extracts differential equations from an atomic ODE or an ODE system into
   * differential assignments.
   * {{{
   *   G |- [{x'=f(||)&H(||)}][x':=f(||);]p(||), D
   *   -------------------------------------------
   *   G |- [{x'=f(||)&H(||)}]p(||), D
   * }}}
    *
    * @example{{{
   *    |- [{x'=1}][x':=1;]x>0
   *    -----------------------DE(1)
   *    |- [{x'=1}]x>0
   * }}}
   * @example{{{
   *    |- [{x'=1, y'=x & x>0}][y':=x;][x':=1;]x>0
   *    -------------------------------------------DE(1)
   *    |- [{x'=1, y'=x & x>0}]x>0
   * }}}
   */
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

  /**
   * diffInd: Differential Invariant proves a formula to be an invariant of a differential equation (by DI, DW, DE, QE)
    *
    * @param qeTool Quantifier elimination tool for final QE step of tactic.
   * @param auto One of 'none, 'diffInd, 'full. Whether or not to automatically close and use DE, DW.
   *             'none: behaves as DI rule per cheat sheet
   *                    {{{
   *                      G, q(x) |- p(x), D    G, q(x) |- [x'=f(x)&q(x)](p(x))', D
   *                      ---------------------------------------------------------
   *                                  G |- [x'=f(x)&q(x)]p(x), D
   *                    }}}
   *             'diffInd: behaves as diffInd rule per cheat sheet
   *                    {{{
   *                      G, q(x) |- p(x), D     q(x) |- [x':=f(x)]p(x')    @note derive on (p(x))' already done
   *                      ----------------------------------------------
   *                                  G |- [x'=f(x)&q(x)]p(x), D
   *                    }}}
   *             'full: tries to close everything after diffInd rule
   *                    {{{
   *                        *
   *                      --------------------------
   *                      G |- [x'=f(x)&q(x)]p(x), D
   *                    }}}
   * @example{{{
   *         *
   *    ---------------------diffInd(qeTool, 'full)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5, true |- x>=5    true |- [{x':=2}]x'>=0
   *    --------------------------------------------diffInd(qeTool, 'diffInd)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5, true |- x>=5    x>=5, true |- [{x'=2}](x>=5)'
   *    ---------------------------------------------------diffInd(qeTool, 'none)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5 |- [x:=x+1;](true -> x>=5&2>=0)
   *    -------------------------------------diffInd(qeTool, 'full)(1, 1::Nil)
   *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
   * }}}
   * @incontext
   */
  def diffInd(auto: Symbol = 'full): DependentPositionTactic = new DependentPositionTactic("diffInd") {
    require(auto == 'none || auto == 'diffInd || auto == 'full, "Expected one of ['none, 'diffInd, 'full] automation values, but got " + auto)
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

  /**
    * openDiffInd: Open Differential Invariant proves an open formula to be an invariant of a differential equation (by DIo, DW, DE, QE)
    *
    * @example{{{
    *         *
    *    ---------------------openDiffInd(1)
    *    x^2>5 |- [{x'=x^3+x^4}]x^2>5
    * }}}
    * @example{{{
    *         *
    *    ---------------------openDiffInd(1)
    *    x^3>5 |- [{x'=x^3+x^4}]x^3>5
    * }}}
    * @incontext
    */
  val openDiffInd: DependentPositionTactic = new DependentPositionTactic("openDiffInd") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc && pos.isTopLevel && (sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _: Greater)) => true
          case Some(Box(_: ODESystem, _: Less)) => true
          case _ => false
        }), "openDiffInd only at ODE system in succedent with postcondition f>g or f<g, but got " + sequent.sub(pos))
        val greater = sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _: Greater)) => true
          case Some(Box(_: ODESystem, _: Less)) => false
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

  /**
   * Differential cut. Use special function old(.) to introduce a ghost for the starting value of a variable that can be
   * used in the evolution domain constraint.
    *
    * @example{{{
   *         x>0 |- [{x'=2&x>0}]x>=0     x>0 |- [{x'=2}]x>0
   *         -----------------------------------------------diffCut("x>0".asFormula)(1)
   *         x>0 |- [{x'=2}]x>=0
   * }}}
   * @example{{{
   *         x>0, x_0=x |- [{x'=2&x>=x_0}]x>=0     x>0, x_0=x |- [{x'=2}]x>=x_0
   *         -------------------------------------------------------------------diffCut("x>=old(x)".asFormula)(1)
   *         x>0 |- [{x'=2}]x>=0
   * }}}
   * @example{{{
   *         x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0&x>=x_0}]x>=0
   *                x>0, v>=0 |- [{x'=v,v'=1}]v>=0
   *         x>0, v>=0, x_0=x |- [{x'=v,v'=1&v>=0}]x>=x_0
   *         --------------------------------------------------diffCut("v>=0".asFormula, "x>=old(x)".asFormula)(1)
   *                x>0, v>=0 |- [{x'=v,v'=1}]x>=0
   * }}}
   * @param formulas The formulas to cut in as evolution domain constraint.
   * @return The tactic.
   */
  def diffCut(formulas: Formula*): DependentPositionTactic =
    "diffCut" byWithInputs (formulas.toList, (pos, sequent) => {nestDCs(formulas.map(ghostDC(_, pos, sequent)))})

  /** Looks for special 'old' function symbol in f and creates DC (possibly with ghost) */
  private def ghostDC(f: Formula, pos: Position, sequent: Sequent): BelleExpr = {
    val ov = oldVars(f)
    if (ov.isEmpty) {
      DC(f)(pos)
    } else {
      val ghosts: Set[((Variable, Variable), BelleExpr)] = ov.map(old => {
        val ghost = TacticHelper.freshNamedSymbol(Variable(old.name), sequent)
        (old -> ghost,
          discreteGhost(old, Some(ghost))(pos) & DLBySubst.assignEquality(pos))
      })
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
  private def oldVars(fml: Formula): Set[Variable] = {
    var oldVars = Set[Variable]()
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case FuncOf(Function("old", None, Real, Real, false), v: Variable) => oldVars += v; Left(None)
        case _ => Left(None)
      }
    }, fml)
    oldVars
  }

  /** Replaces any old(.) with . in formula fml */
  private def replaceOld(fml: Formula, ghostsByOld: Map[Variable, Variable]): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case FuncOf(Function("old", None, Real, Real, false), v: Variable) => Right(ghostsByOld(v))
        case _ => Left(None)
      }
    }, fml) match {
      case Some(g) => g
    }
  }

  /**
   * Combines differential cut and differential induction. Use special function old(.) to introduce a ghost for the
   * starting value of a variable that can be used in the evolution domain constraint. Uses diffInd to prove that the
   * formulas are differential invariants. Fails if diffInd cannot prove invariants.
    *
    * @example{{{
   *         x>0 |- [{x'=2&x>0}]x>=0
   *         ------------------------diffInvariant("x>0".asFormula)(1)
   *         x>0 |- [{x'=2}]x>=0
   * }}}
   * @example{{{
   *         x>0, x_0=x |- [{x'=2&x>x_0}]x>=0
   *         ---------------------------------diffInvariant("x>old(x)".asFormula)(1)
   *                x>0 |- [{x'=2}]x>=0
   * }}}
   * @example{{{
   *         x>0, v>=0, x_0=x |- [{x'=v,v'=1 & v>=0&x>x_0}]x>=0
   *         ---------------------------------------------------diffInvariant("v>=0".asFormula, "x>old(x)".asFormula)(1)
   *                x>0, v>=0 |- [{x'=v,v'=1}]x>=0
   * }}}
   * @param formulas The differential invariants to cut in as evolution domain constraint.
   * @return The tactic.
   * @see [[diffCut]]
   * @see [[diffInd]]
   */
  def diffInvariant(formulas: Formula*): DependentPositionTactic =
    "diffInvariant" byWithInputs (formulas.toList, (pos, sequent) => {
      //@note assumes that first subgoal is desired result, see diffCut
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

  /**
   * Differential ghost. Adds an auxiliary differential equation y'=a*y+b
    *
    * @example{{{
   *         |- \exists y [{x'=2,y'=0*y+1}]x>0
   *         ---------------------------------- DG("y".asVariable, "0".asTerm, "1".asTerm)(1)
   *         |- [{x'=2}]x>0
   * }}}
   * @example{{{
   *         |- \exists y [{x'=2,y'=f()*y+g() & x>=0}]x>0
   *         --------------------------------------------- DG("y".asVariable, "f()".asTerm, "g()".asTerm)(1)
   *         |- [{x'=2 & x>=0}]x>0
   * }}}
   * @param ghost A differential program of the form y'=a*y+b.
   * @return The tactic.
   */
  def DG(ghost: DifferentialProgram): DependentPositionTactic = "DGTactic" by ((pos: Position, sequent: Sequent) => {
    val (y, a, b) = parseGhost(ghost)
    sequent.sub(pos) match {
      case Some(Box(ode@ODESystem(c, h), p)) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(a).contains(y) && !StaticSemantics.symbols(b).contains(y) =>
        cutR(Exists(y :: Nil, Box(ODESystem(DifferentialProduct(c, AtomicODE(DifferentialSymbol(y), Plus(Times(a, y), b))), h), p)))(pos.checkSucc.top) < (
          /* use */ skip,
          /* show */ cohide(pos.top) &
          //@todo why is this renaming here? Makes no sense to me.
          ///* rename first, otherwise byUS fails */ ProofRuleTactics.uniformRenaming("y".asVariable, y) &
          equivifyR('Rlast) & commuteEquivR('Rlast) & byUS("DG differential ghost")
          )
    }
  })

  //@todo might work instead of implementation above after some tweaking
  /** DG: Differential Ghost add auxiliary differential equations with extra variables `y'=a*y+b`.
    * `[x'=f(x)&q(x)]p(x)` reduces to `\exists y [x'=f(x),y'=a*y+b&q(x)]p(x)`.
    */
//  private[btactics] def DG(y:Variable, a:Term, b:Term) = useAt("DG differential ghost", PosInExpr(0::Nil),
//    (us:Subst)=>us++RenUSubst(Seq(
//      (Variable("y_",None,Real), y),
//      (UnitFunctional("a", Except(Variable("y_", None, Real)), Real), a),
//      (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b)
//    ))
//  )

  def diffGhost(ghost: DifferentialProgram, initialValue: Term) = "diffGhost" by ((pos: Position, sequent: Sequent) => {
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

  /** DA(ghost,r): Differential Ghost add auxiliary differential equations with extra variables
    * ghost of the form y'=a*y+b and postcondition replaced by r.
    * {{{
    * G |- p(x), D   |- r(x,y) -> [x'=f(x),y'=g(x,y)&q(x)]r(x,y)
    * ----------------------------------------------------------  DA using p(x) <-> \exists y. r(x,y) by QE
    * G |- [x'=f(x)&q(x)]p(x), D
    * }}}
    *
    * @note Uses QE to prove p(x) <-> \exists y. r(x,y)
    */
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
  def DA(y: Variable, a: Term, b: Term, auxEquiv: Provable): DependentPositionTactic =
    "DAbase" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
      case Some(Box(ode@ODESystem(c, h), p)) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(a).contains(y) && !StaticSemantics.symbols(b).contains(y) => null

        val Equiv(p, _) = auxEquiv.conclusion.succ.head

        cutR(p)(pos.checkSucc.top) <(
          skip,
          implyR(pos) & useAt(auxEquiv, PosInExpr(0::Nil))('Llast) & existsL('Llast) &
            DG(AtomicODE(DifferentialSymbol(y), Plus(Times(a, y), b)))(pos) &
            existsR(pos) & ?(exhaustiveEqR2L(hide=true)('Llast)) &
            useAt(auxEquiv, PosInExpr(0::Nil))(pos ++ PosInExpr(1::Nil)) &
            existsR(pos ++ PosInExpr(1::Nil)) & implyRi(AntePos(sequent.ante.length), pos.checkSucc.top)
          )
    })

  /**
   * Syntactically derives a differential of a variable to a differential symbol.
   * {{{
   *   G |- x'=f, D
   *   --------------
   *   G |- (x)'=f, D
   * }}}
    *
    * @example{{{
   *   |- x'=1
   *   ----------Dvariable(1, 0::Nil)
   *   |- (x)'=1
   * }}}
   * @example{{{
   *   |- [z':=1;]z'=1
   *   ------------------Dvariable(1, 1::0::Nil)
   *   |- [z':=1;](z)'=1
   * }}}
   * @incontext
   * @todo could probably simplify implementation by picking atomic formula, using "x' derive var" and then embedding this equivalence into context by CE.
    *       Or, rather, by using CE directly on a "x' derive var" provable fact (z)'=1 <-> z'=1.
   */
  lazy val Dvariable: DependentPositionTactic = new DependentPositionTactic("Dvariabletactic") {
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

  def diffSolve(solution: Option[Formula] = None, preDITactic: BelleExpr = skip)(tool: DiffSolutionTool): DependentPositionTactic = "diffSolve" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
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
        case None => tool.diffSol(odes.ode, time, iv)
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
    case Some(Box(a, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeaken only at top level in succedent")

      def constAnteConditions(sequent: Sequent, taboo: Set[Variable]): IndexedSeq[Formula] = {
        sequent.ante.filter(f => StaticSemantics.freeVars(f).intersect(taboo).isEmpty)
      }
      val consts = constAnteConditions(sequent, StaticSemantics(a).bv.toSet)

      if (consts.nonEmpty) {
        val dw = diffWeakenG(pos) & implyR(1) & andL('Llast)*consts.size & implyRi(AntePos(0), SuccPos(0)) partial
        val constFml = consts.reduceRight(And)
        diffCut(constFml)(pos) <(dw, V('Rlast) & (andR('Rlast) <(closeIdWith('Rlast), skip))*(consts.size-1) & closeIdWith('Rlast)) partial
      } else {
        diffWeakenG(pos)
      }
  })

  /** diffWeaken by DW & G */
  lazy val diffWeakenG: DependentPositionTactic = "diffWeakenG" by ((pos: Position, sequent: Sequent) => sequent.sub(pos) match {
    case Some(Box(_: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeakenG only at top level in succedent")
      cohide(pos.top) & DW(1) & G(1)
  })

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
  private val getODEDim: (Sequent,Position)=>Int = (sequent,pos) => {
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
}
