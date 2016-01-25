package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.bellerophon.UnificationMatch
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaerax.tactics.{TacticLibrary, AlphaConversionHelper, AxiomaticRuleTactics, ContextTactics}
import edu.cmu.cs.ls.keymaerax.tools.{Tool, DiffSolutionTool}

import scala.collection.immutable.{List, IndexedSeq}
import scala.language.postfixOps

/**
 * [[DifferentialTactics]] provides tactics for differential equations.
 * @note Container for "complicated" tactics. Single-line implementations are in [[TactixLibrary]].
 * @see [[TactixLibrary.DW]], [[TactixLibrary.DC]]
 */
object DifferentialTactics {

  /**
   * Differential effect: exhaustively extracts differential equations from an atomic ODE or an ODE system into
   * differential assignments.
   * {{{
   *   G |- [{x'=f(??)&H(??)}][x':=f(??);]p(??), D
   *   -------------------------------------------
   *   G |- [{x'=f(??)&H(??)}]p(??), D
   * }}}
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
            Box(DiffAssign(xp, t), p)
          )

        case Box(ODESystem(AtomicODE(xp@DifferentialSymbol(x), t), h), p) =>
          Box(
            ODESystem(AtomicODE(xp, t), h),
            Box(DiffAssign(xp, t), p)
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
              Box(DiffAssign(d, t), p)
            )

            //construct substitution
            val aF = FuncOf(Function("f", None, Real, Real), Anything)
            val aH = PredOf(Function("H", None, Real, Bool), Anything)
            val aC = DifferentialProgramConst("c")
            val aP = PredOf(Function("p", None, Real, Bool), Anything)

            val subst = SubstitutionPair(aF, t) :: SubstitutionPair(aC, c) :: SubstitutionPair(aP, p) ::
              SubstitutionPair(aH, h) :: Nil
            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(s"[{${d.prettyString}=f(??),c&H(??)}]p(??) <-> [{c,${d.prettyString}=f(??)&H(??)}][${d.prettyString}:=f(??);]p(??)".asFormula))

            cutLR(g)(pos) <(
              /* use */ skip,
              //@todo conditional commuting (if (pos.isSucc) commuteEquivR(1) else Idioms.ident) instead?
              /* show */ cohide('Rlast) & equivifyR(1) & commuteEquivR(1) & US(USubst(subst), origin) & byUS("DE differential effect (system)"))
        }
      }
    }

    /** A single step of DE system (@todo replace with useAt when unification for this example works) */
    // !semanticRenaming
    private lazy val DESystemStep_NoSemRen: DependentPositionTactic = new DependentPositionTactic("DE system step") {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
          case Some(f@Box(ODESystem(DifferentialProduct(AtomicODE(xp@DifferentialSymbol(x), t), c), h), p)) =>
            val g = Box(
              ODESystem(DifferentialProduct(c, AtomicODE(xp, t)), h),
              Box(DiffAssign(xp, t), p)
            )

            //construct substitution
            val aF = FuncOf(Function("f", None, Real, Real), Anything)
            val aH = PredOf(Function("H", None, Real, Bool), Anything)
            val aC = DifferentialProgramConst("c")
            val aP = PredOf(Function("p", None, Real, Bool), Anything)
            val aX = Variable("x_", None, Real)

            val uren = URename(x, aX)

            val subst = SubstitutionPair(aF, t) :: SubstitutionPair(aC, uren(c)) :: SubstitutionPair(aP, uren(p)) ::
              SubstitutionPair(aH, uren(h)) :: Nil
            //            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(s"[{${xp.prettyString}=f(??),c&H(??)}]p(??) <-> [{c,${xp.prettyString}=f(??)&H(??)}][${xp.prettyString}:=f(??);]p(??)".asFormula))
            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms("DE differential effect (system)")))

            if (true || DEBUG) println("DE: manual " + USubst(subst) + " above " + uren + " to prove " + sequent.prettyString)

            cutLR(g)(pos) <(
              /* use */ skip,
              /* show */ cohide('Rlast) & equivifyR(1) & (if (pos.isSucc) commuteEquivR(1) else Idioms.ident) &
              ProofRuleTactics.uniformRenaming(x, aX) & US(USubst(subst), origin) & byVerbatim("DE differential effect (system)"))

          case Some(f@Box(ODESystem(AtomicODE(xp@DifferentialSymbol(x), t), h), p)) =>
            val g = Box(
              ODESystem(AtomicODE(xp, t), h),
              Box(DiffAssign(xp, t), p)
            )

            //construct substitution
            val aF = FuncOf(Function("f", None, Real, Real), Anything)
            val aQ = PredOf(Function("q", None, Real, Bool), Anything)
            val aP = PredOf(Function("p", None, Real, Bool), Anything)
            val aX = Variable("x_", None, Real)

            val uren = URename(x, aX)

            val subst = SubstitutionPair(aF, t) :: SubstitutionPair(aP, uren(p)) ::
              SubstitutionPair(aQ, uren(h)) :: Nil
            val origin = Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms("DE differential effect")))

            if (true || DEBUG) println("DE: manual " + USubst(subst) + " above " + uren + " to prove " + sequent.prettyString)

            cutLR(g)(pos) <(
              /* use */ skip,
              /* show */ cohide('Rlast) & equivifyR(1) & (if (pos.isSucc) commuteEquivR(1) else Idioms.ident) &
              ProofRuleTactics.uniformRenaming(x, aX) & US(USubst(subst), origin) & byVerbatim("DE differential effect"))

        }
      }
    }
  }

  /**
   * diffInd: Differential Invariant proves a formula to be an invariant of a differential equation (by DI, DW, DE, QE)
   * @param qeTool Quantifier elimination tool for final QE step of tactic.
   * @example{{{
   *         *
   *    ---------------------diffInd(qeTool)(1)
   *    x>=5 |- [{x'=2}]x>=5
   * }}}
   * @example{{{
   *    x>=5 |- [x:=x+1;](true -> x>=5&2>=0)
   *    -------------------------------------diffInd(qeTool)(1, 1::Nil)
   *    x>=5 |- [x:=x+1;][{x'=2}]x>=5
   * }}}
   * @incontext
   */
  def diffInd(implicit qeTool: QETool): DependentPositionTactic = new DependentPositionTactic("diffInd") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(pos.isSucc && (sequent.sub(pos) match {
          case Some(Box(_: ODESystem, _)) => true
          case _ => false
        }), "diffInd only at ODE system in succedent, but got " + sequent.sub(pos))
        if (pos.isTopLevel)
          Dconstify(pos) & DI(pos) &
            (implyR(pos) & andR(pos)) <(
              close | QE,
              //@note derive before DE to keep positions easier
              derive(pos + PosInExpr(1::Nil)) &
                DE(pos) &
                Dassignb(pos + PosInExpr(1::Nil))*getODEDim(sequent,pos) &
                //@note DW after DE to keep positions easier
                (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                abstractionb(pos) & (close | QE)
              )
        else
          Dconstify(pos) & DI(pos) &
            //@note derive before DE to keep positions easier
            shift(PosInExpr(1::1::Nil), new DependentPositionTactic("Shift") {
              override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
                override def computeExpr(sequent: Sequent): BelleExpr = {
                  shift(PosInExpr(1::Nil), derive)(pos) &
                    DE(pos) &
                    (shift(PosInExpr(1::Nil), Dassignb)(pos) * getODEDim(sequent, pos)) &
                    //@note DW after DE to keep positions easier
                    (if (hasODEDomain(sequent, pos)) DW(pos) else skip) &
                    abstractionb(pos)
                }
              }
            }
            )(pos)
      }
    }
  }

  /**
   * Differential cut. Use special function old(.) to introduce a ghost for the starting value of a variable that can be
   * used in the evolution domain constraint.
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
  def diffCut(formulas: Formula*): DependentPositionTactic = new DependentPositionTactic("diff cut") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = nestDCs(formulas.map(ghostDC(_, pos, sequent)))
    }

    /** Looks for special 'old' function symbol in f and creates DC (possibly with ghost) */
    private def ghostDC(f: Formula, pos: Position, sequent: Sequent): BelleExpr = {
      val ov = oldVars(f)
      if (ov.isEmpty) {
        DC(f)(pos)
      } else {
        val ghosts: Set[((Variable, Variable), BelleExpr)] = ov.map(old => {
          val ghost = TacticHelper.freshNamedSymbol(Variable(old.name), sequent)
          (old -> ghost,
            discreteGhost(old, Some(ghost))(pos) & DLBySubst.assignEquational(pos))
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
          case FuncOf(Function("old", None, Real, Real), v: Variable) => oldVars += v; Left(None)
          case _ => Left(None)
        }
      }, fml)
      oldVars
    }

    /** Replaces any old(.) with . in formula fml */
    private def replaceOld(fml: Formula, ghostsByOld: Map[Variable, Variable]): Formula = {
      ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
          case FuncOf(Function("old", None, Real, Real), v: Variable) => Right(ghostsByOld(v))
          case _ => Left(None)
        }
      }, fml) match {
        case Some(g) => g
      }
    }
  }

  /**
   * Combines differential cut and differential induction. Use special function old(.) to introduce a ghost for the
   * starting value of a variable that can be used in the evolution domain constraint. Uses diffInd to prove that the
   * formulas are differential invariants. Fails if diffInd cannot prove invariants.
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
  def diffInvariant(qeTool: QETool, formulas: Formula*): DependentPositionTactic = new DependentPositionTactic("diff invariant") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        //@note assumes that first subgoal is desired result, see diffCut
        val diffIndAllButFirst = skip +: Seq.tabulate(formulas.length)(_ => diffInd(qeTool)('Rlast))
        diffCut(formulas: _*)(pos) <(diffIndAllButFirst:_*) partial
      }
    }
  }

  /**
   * Turns things that are constant in ODEs into function symbols.
   * @example Turns v>0, a>0 |- [v'=a;]v>0, a>0 into v>0, a()>0 |- [v'=a();]v>0, a()>0
   * @return The tactic.
   */
  def Dconstify: DependentPositionTactic = new DependentPositionTactic("IDC introduce differential constants") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(Box(ode@ODESystem(_, _), p)) =>
          introduceConstants((StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.
            filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable]), sequent)
        case Some(Diamond(ode@ODESystem(_, _), p)) =>
          introduceConstants((StaticSemantics.freeVars(p) -- StaticSemantics.boundVars(ode)).toSet.
            filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable]), sequent)
      }

      /** Derives non-const current sequent by substitution from consts */
      private def introduceConstants(cnsts: Set[Variable], sequent: Sequent): BelleExpr = {
        if (cnsts.isEmpty) {
          skip
        } else {
          val subst = cnsts.map(c => SubstitutionPair(FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing), c)).toList
          val origin = Sequent(Nil, sequent.ante.map(constify(_, cnsts)), sequent.succ.map(constify(_, cnsts)))
          US(USubst(subst), origin)
        }
      }

      /** Recursively replaces variables in consts with constant function symbols in formula f. */
      private def constify(f: Formula, consts: Set[Variable]): Formula = {
        if (consts.isEmpty) f
        else {
          val c = consts.head
          constify(SubstitutionHelper.replaceFree(f)(c, FuncOf(Function(c.name, c.index, Unit, c.sort), Nothing)),
            consts.tail)
        }
      }
    }
  }

  /**
   * Differential ghost. Adds an auxiliary differential equation y'=a*y+b
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
   * @param y The differential ghost variable.
   * @param a The linear term in y'=a*y+b.
   * @param b The constant term in y'=a*y+b.
   * @return The tactic.
   */
  def DG(y: Variable, a: Term, b: Term): DependentPositionTactic = "DG" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(ode@ODESystem(c, h), p)) if !StaticSemantics(ode).bv.contains(y) &&
        !StaticSemantics.symbols(a).contains(y) && !StaticSemantics.symbols(b).contains(y) =>
      cutR(Exists(y::Nil, Box(ODESystem(DifferentialProduct(c, AtomicODE(DifferentialSymbol(y), Plus(Times(a, y), b))), h), p)))(pos.checkSucc.top) <(
        /* use */ skip,
        /* show */ cohide(pos.top) &
          /* rename first, otherwise byUS fails */ ProofRuleTactics.uniformRenaming("y".asVariable, y) &
          equivifyR('Rlast) & commuteEquivR('Rlast) & byUS("DG differential ghost")
        )
  })

  /**
   * Syntactically derives a differential of a variable to a differential symbol.
   * {{{
   *   G |- x'=f, D
   *   --------------
   *   G |- (x)'=f, D
   * }}}
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
  lazy val Dvariable: DependentPositionTactic = new DependentPositionTactic("x' derive variable") {
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

  def diffSolve(solution: Option[Formula] = None, preDITactic: BelleExpr = skip)(implicit tool: DiffSolutionTool with QETool): DependentPositionTactic = "diffSolve" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(odes: DifferentialProgram, _)) =>
      require(pos.isSucc && pos.isTopLevel, "diffSolve only at top-level in succedent")

      val (time, timeTactic, timeZeroInitially) = findTimeInOdes(odes) match {
        case Some(existingTime) => (existingTime, skip, false)
        case None =>
          val time: Variable = TacticHelper.freshNamedSymbol(Variable("t", None, Real), sequent)
          val introTime =
            DG(time, "0".asTerm, "1".asTerm)(pos) &
              DLBySubst.assignbExists("0".asTerm)(pos) &
              DLBySubst.assignEquational(pos)
          (time, introTime, true)
      }

      def createTactic(ode: DifferentialProgram, solution: Formula, time: Variable, iv: Map[Variable, Variable],
                       diffEqPos: Position): BelleExpr = {
        val initialGhosts = (primedSymbols(ode) + time).foldLeft(skip)((a, b) =>
          a & (discreteGhost(b)(diffEqPos) & DLBySubst.assignEquational(diffEqPos)))

        // flatten conjunctions and sort by number of right-hand side symbols to approximate ODE dependencies
        val flatSolution = flattenConjunctions(solution).
          sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size)

        initialGhosts & diffInvariant(tool, flatSolution:_*)(pos) &
          // initial ghosts are at the end of the antecedent
          exhaustiveEqR2L(hide=true)('Llast)*flatSolution.size &
          diffWeaken(pos)
      }

      // initial values
      val iv: Map[Variable, Variable] =
        primedSymbols(odes).map(v => v -> TacticHelper.freshNamedSymbol(v, sequent(pos.top))).toMap

      val theSolution = solution match {
        case sol@Some(_) => sol
        case None => tool.diffSol(odes, time, iv)
      }

      val diffEqPos = pos.topLevel
      theSolution match {
        // add relation to initial time
        case Some(s) =>
          val sol = And(
            if (timeZeroInitially) s
            else SubstitutionHelper.replaceFree(s)(time, Minus(time, iv(time))),
            GreaterEqual(time, if (timeZeroInitially) "0".asTerm else iv(time)))
          timeTactic & createTactic(odes, sol, time, iv, diffEqPos)
        case None => throw new BelleError("No solution found")
      }
  })

  def alphaRenaming(from: Variable, to: Variable): DependentPositionTactic = "Bound Renaming" by ((p:Position, sequent:Sequent) => {
      val fml = sequent.at(p)._1.ctx
      val findResultProof = Provable.startProof(Sequent(sequent.pref, IndexedSeq(), IndexedSeq(fml)))
      val desiredResult = findResultProof(new BoundRenaming(from, to, ???), 0).subgoals.head.succ.head
      def br = ProofRuleTactics.applyRule(new BoundRenaming(from, to, ???))
      if (p.isAnte) {
        ProofRuleTactics.cut(sequent(p.top).replaceAt(p.inExpr, desiredResult).asInstanceOf[Formula]) <(
          /* use */
          hide(p.topLevel),
          /* show */
          cohide2(p.topLevel, SuccPos(sequent.succ.length)) &
            ProofRuleTactics.onesidedCongruence(p.inExpr) & assertT(0, 1) & /*DebuggingTactics.assert(Equiv(fml, desiredResult))(SuccPosition(0)) & */
            equivR(SuccPosition(0)) & br & (ProofRuleTactics.trivialCloser /*(| DebuggingTactics.assert("alpha: AxiomCloseT failed unexpectedly")*/))
      } else {
        ProofRuleTactics.cut(sequent(p.top).replaceAt(p.inExpr, desiredResult).asInstanceOf[Formula]) <(
          /* use case */
          cohide2(AntePos(sequent.ante.length), p.topLevel) &
          ProofRuleTactics.onesidedCongruence(p.inExpr) & DebuggingTactics.assert(0, 1) /*& assert(Equiv(desiredResult, fml))(SuccPosition(0)) */&
          equivR(SuccPosition(0)) & br & (ProofRuleTactics.trivialCloser | DebuggingTactics.debug("alpha: AxiomCloseT failed unexpectedly")),
          /* show case */
            hide(p.topLevel))
      }
  })

  /**
    * Creates a new position tactic for box assignment [x := t;], for the case when followed by ODE or loop.
    * Alpha renaming in ODEs and loops introduces initial value assignments. This tactic is designed to handle those.
    * @return The tactic.
    * @author Stefan Mitsch
    */
  def v2vAssign: DependentPositionTactic = "[:=]/<:=> assign" by ((p:Position, sequent:Sequent) => {
    val succLength = sequent.succ.length
    val anteLength = sequent.ante.length

    def createTactic(m: Formula, pred: Formula, v: Variable, t: Variable) = {
      ContextTactics.cutInContext(Equiv(m, AlphaConversionHelper.replace(pred)(v, t)), p) <(
        EqualityTactics.equivRewriting(AntePosition(anteLength))(p.topLevel),
        // TODO does not work in mixed settings such as <x:=t>[x'=2] and [x:=t]<x'=2>
        cohide(SuccPosition(succLength)) & assertT(0, 1) &
          alphaRenaming(t, v)(SuccPosition(SuccPos(0), PosInExpr(1 :: p.inExpr.pos))) &
          equivR(SuccPosition(0)) & (ProofRuleTactics.trivialCloser | debug("v2vAssign: Axiom close failed unexpectedly"))

      )
    }
      sequent.at(p)._1.ctx match {
        case b@Box(Assign(v: Variable, t: Variable), pred) => createTactic(b, pred, v, t)
        case d@Diamond(Assign(v: Variable, t: Variable), pred) => createTactic(d, pred, v, t)
      }
    }
  )

  /*Returns a new tactic for universal/existential quantifier instantiation. The tactic performs self-instantiation
  * with the quantified variable.
    * @example{{{
    *           |- x>0
    *         ------------------instantiateT(SuccPosition(0))
    *           |- \exists x x>0
    * }}}
  * @example{{{
    *                     x>0 |-
      *         ------------------instantiateT(AntePosition(0))
    *           \forall x x>0 |-
      * }}}
  * @return The tactic.
  */
  def instantiate: DependentPositionTactic = "Quantifier Instantiation" by ((p:Position, sequent:Sequent) => {
    sequent.at(p)._1.ctx match {
        case Forall(vars, phi) => vars.map(v => instantiate(v, v)(p)).fold(TactixLibrary.nil)((a, b) => a & b)
        case Exists(vars, phi) => vars.map(v => instantiate(v, v)(p)).fold(TactixLibrary.nil)((a, b) => a & b)
        case _ => ???
      }
    })


  /**
    * Creates a tactic which does quantifier instantiation.
    * @param quantified The quantified variable.
    * @param instance The instance.
    * @return The tactic.
    */
  def instantiate(quantified: Variable, instance: Term): DependentPositionTactic = "Quantifier Instantiation" by ((pos:Position, sequent:Sequent) => {
    def withStuttering(s: Sequent, quantStillPresentAfterAround: Boolean, around: BelleExpr): BelleExpr = {
      var stutteringAt: Set[PosInExpr] = Set.empty[PosInExpr]

      // HACK don't need stuttering for dummy variable introduced in abstractionT
      // (no longer necessary when we have the correct condition on filtering stutteringAt)
      if (quantified.name != "$abstractiondummy") {
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
            case Box(prg, _) if /*StaticSemantics(prg).bv.contains(quantified) &&*/ !stutteringAt.exists(_.isPrefixOf(p)) => stutteringAt += p; Left(None)
            case Diamond(prg, _) if /*StaticSemantics(prg).bv.contains(quantified) &&*/ !stutteringAt.exists(_.isPrefixOf(p)) => stutteringAt += p; Left(None)
            case _ => Left(None)
          }
        }, s.at(pos)._1.ctx)
      }

      if (stutteringAt.nonEmpty) {
        val pPos = stutteringAt.map(p => pos + p)
        val assignPos = stutteringAt.map(p => pos + PosInExpr(p.pos.tail))
        val alpha = pPos.foldRight(TactixLibrary.nil)((p, r) => r & (alphaRenaming(quantified, quantified) | TactixLibrary.nil))
        val v2v =
          if (quantStillPresentAfterAround) assignPos.foldRight(TactixLibrary.nil)((p, r) => r & v2vAssign(p + PosInExpr(0 :: p.inExpr.pos)) | TactixLibrary.nil)
          else assignPos.foldRight(TactixLibrary.nil)((p, r) => r & (v2vAssign(p) | TactixLibrary.nil))
        alpha & around & v2v
      } else around
    }
    sequent.at(pos)._1.ctx match {
      case Forall(vars, _) =>
        withStuttering(sequent, vars.length > 1, instantiateUniversalQuanT(quantified, instance)(pos))
      case Exists(vars, _) =>
        withStuttering(sequent, vars.length > 1, instantiateExistentialQuanT(quantified, instance)(pos))
      case _ => ???
    }})

  def instantiateUniversalQuanT(quantified: Variable, instance: Term): DependentPositionTactic = "Universal Quantifier Instantiation" by ((p: Position, sequent:Sequent) => {
    val axiomName = "all instantiate"
    val axiom = Axiom.axioms.get(axiomName)
    require(axiom.isDefined)
    def replace(f: Formula)(o: NamedSymbol, n: Variable): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Forall(v, fa) => Right(Forall(v.map(name => if(name == o) n else name ), fa))
          case Exists(v, fa) => Right(Exists(v.map(name => if(name == o) n else name ), fa))
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
      }, f) match {
        case Some(g) => g
        case None => throw new IllegalStateException("Replacing one variable by another should not fail")
      }

      def constructInstanceAndSubst(f: Formula): Option[(Formula, List[SubstitutionPair], (Variable, Variable), (Term, Term))] = f match {
        case Forall(x, qf) if x.contains(quantified) =>
          def forall(h: Formula) = if (x.length > 1) Forall(x.filter(_ != quantified), h) else h
          // construct substitution
          val aX = Variable("x", None, Real)
          val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
          val aP = Function("p", None, Real, Bool)
          val l = List(SubstitutionPair(aT, instance), SubstitutionPair(PredOf(aP, DotTerm),
            forall(SubstitutionHelper.replaceFree(qf)(quantified, DotTerm))))
          // construct axiom instance: \forall x. p(x) -> p(t)
          val g = SubstitutionHelper.replaceFree(qf)(quantified, instance)
          val axiomInstance = Imply(f, forall(g))
          Some(axiomInstance, l, (quantified, aX), (instance, aT))
        case Forall(x, qf) if !x.contains(quantified) => None
        case _ => None
      }

      def decompose(d: Formula): Formula = d match {
        case Forall(v, f) if v.length > 1 => Forall(v.take(1), Forall(v.drop(1), f))
        case Exists(v, f) if v.length > 1 => Exists(v.take(1), Exists(v.drop(1), f))
        case _ => d
      }

       axiom match {
        case Some(a) =>
          constructInstanceAndSubst(sequent.at(p)._1.ctx) match {
            case Some((axiomInstance, subst, (quant, aX), (inst, aT))) =>
              val eqPos = AntePosition(sequent.ante.length)
              val branch1Tactic = SequentCalculus.modusPonens(p.checkAnte.top, eqPos.checkAnte.top)
              // val hideAllAnte = for (i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
              // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
              // val hideAllSuccButLast = for (i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
              // val hideSllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
              def repl(f: Formula, v: Variable):Formula = f match {
                case Imply(Forall(vars, aa), b) =>
                  Imply(
                    decompose(
                      Forall(vars.map(qv => if (qv == v) quantified else qv), SubstitutionHelper.replaceFree(aa)(v, quantified))),
                    b)
                case _ => throw new IllegalArgumentException("...")
              }

              val (renAxiom, alpha) =
                if (quantified.name != aX.name || quantified.index != aX.index)
                  (repl(a, aX), alphaRenaming(quantified, aX)(SuccPosition(SuccPos(0), PosInExpr(0::Nil))))
                else (a, TactixLibrary.nil)

              val axInstance = axiomInstance match {
                case Imply(lhs, rhs) => Imply(decompose(lhs), rhs)
              }

              val replMap = Map[Formula, Formula](axInstance -> renAxiom)
              def compose(t1:BelleExpr, t2: BelleExpr) = (t1 & t2) | t2
              val branch2Tactic = compose(ProofRuleTactics.coHide(SuccPosition(sequent.succ.length)),
                (PropositionalTactics.uniformSubst(subst, replMap) & alpha & AxiomTactic.axiom(axiomName)))
              ProofRuleTactics.cut(axiomInstance) <( /*use*/branch1Tactic, /*show*/branch2Tactic)
            case None => println("Giving up " + axiomName); ???
          }
        case None => println("Giving up because the axiom does not exist " + axiomName); ???
      }
    })

  /**
    * Tactic for existential quantifier generalization. Generalizes only at certain positions. All positions have to
    * refer to the same term.
    * @example{{{
    *           \exists z z=a+b |-
    *           ------------------existentialGenPosT(Variable("z"), PosInExpr(0::Nil) :: Nil)(AntePosition(0))
    *                 a+b = a+b |-
    * }}}
    * @example{{{
    *           \exists z z=z |-
    *           ----------------existentialGenPosT(Variable("z"), PosInExpr(0::Nil) :: PosInExpr(1::Nil) :: Nil)(AntePosition(0))
    *               a+b = a+b |-
    * }}}
    * @param x The new existentially quantified variable.
    * @param where The term to generalize.
    * @return The tactic.
    */
  def existentialGenPos(x: Variable, where: List[PosInExpr]): DependentPositionTactic = {
    // construct axiom instance: p(t) -> \exists x. p(x)
    def axiomInstance(fml: Formula): Formula = {
      require(where.nonEmpty, "need at least one position to generalize")
      require(where.map(w => fml.at(w)).toSet.size == 1, "not all positions refer to the same term")
      val t = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          if (where.contains(p)) Right(x)
          else Left(None)
      }, fml) match {
        case Some(f) => f
        case _ => throw new IllegalArgumentException(s"Position $where is not a term")
      }
      Imply(fml, Exists(x :: Nil, t))
    }
    AxiomTactic.uncoverAxiom("exists generalize", axiomInstance, _ => existentialGenPosBaseT(x, where))
  }
  /** Base tactic for existential generalization */
  private def existentialGenPosBaseT(x: Variable, where: List[PosInExpr]): DependentPositionTactic = {
    def subst(fml: Formula): List[SubstitutionPair] = fml match {
      case Imply(p, Exists(_, _)) =>
        assert(where.map(w => p.at(w)).toSet.size == 1, "not all positions refer to the same term")

        val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
        val aP = PredOf(Function("p", None, Real, Bool), DotTerm)

        val t = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
            if (where.contains(p)) Right(DotTerm)
            else Left(None)
        }, p) match {
          case Some(f) => f
          case _ => throw new IllegalArgumentException(s"Position $where is not a term")
        }

        SubstitutionPair(aT, p.at(where.head)._1.ctx) ::
          SubstitutionPair(aP, t) :: Nil
    }

    val aX = Variable("x", None, Real)
    def alpha(fml: Formula): DependentPositionTactic = "Alpha" by ((p:Position, sequent:Sequent) => {
      alphaRenaming(x, aX)(p + PosInExpr(1::Nil))})

    def axiomInstance(fml: Formula, axiom: Formula): Formula = {
      val Imply(left, right) = axiom
      if (x.name != aX.name || x.index != aX.index) Imply(left, SubstitutionHelper.replaceFree(right)(aX, x))
      else Imply(left, right)
    }

    AxiomTactic.axiomLookupBase("exists generalize", subst, alpha, axiomInstance)
  }

  /**
    * Returns a tactic to instantiate an existentially quantified formula that occurs in positive polarity in the
    * succedent or in negative polarity in the antecedent.
    * @example{{{
    *         |- y+2>0
    *         ----------------instantiateExistentialQuanT(Variable("x"), "y+2".asTerm)(SuccPosition(0))
    *         |- \exists x x>0
    * }}}
    * @example{{{
    *                 !(y+2>0) |-
    *         -------------------instantiateExistentialQuanT(Variable("x"), "y+2".asTerm)(AntePosition(0, PosInExpr(0::Nil)))
    *         !(\exists x x>0) |-
    * }}}
    * @example{{{
    *         y>0 -> y>0
    *         -----------------------instantiateExistentialQuanT(Variable("x"), Variable("y"))(AntePosition(0, PosInExpr(0::Nil)))
    *         \exists x x>0 -> y>0 |-
    * }}}
    * @param quantified The variable to instantiate.
    * @param t The instance.
    * @return The tactic which performs the instantiation.
    */
  def instantiateExistentialQuanT(quantified: Variable, t: Term): DependentPositionTactic = "exists instantiate" by ((p:Position, sequent:Sequent) => {
    def createDesired(s: Sequent) = {
      ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
          case Exists(_, phi) => Right(AlphaConversionHelper.replace(phi)(quantified, t))
          case _ => Left(Some(ExpressionTraversal.stop))
        }
      }), s.apply(p).asInstanceOf[Term])
    }
    def generalize(where: List[PosInExpr]) = {
      if (p.isTopLevel) {
        existentialGenPos(quantified, where)(AntePosition(0)) & closeId
      } else {
        ProofRuleTactics.propositionalCongruence(p.inExpr) &
          existentialGenPos(quantified, where)('Llast) &
          (closeId | DebuggingTactics.debug("Instantiate existential: axiom close failed"))
      }
    }
    sequent.at(p)._1.ctx match {
      case Exists(vars, phi) =>
        var varPos = List[PosInExpr]()
        ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
            case n: NamedSymbol if vars.contains(n) && !StaticSemanticsTools.boundAt(phi, p).contains(n) =>
              varPos = varPos :+ p
              Left(None)
            case _ => Left(None)
          }
        }, phi)
        val desired = createDesired(sequent)
        val cutFrm = Imply(desired.asInstanceOf[Formula], sequent.at(p)._1.ctx)
        cut(cutFrm) < (
          /* use */
          /*DebuggingTactics.assert(cutFrm, 'Llast)) & */ implyR('Llast) <(hide(p.topLevel), SequentCalculus.closeId),
      /* show */
      /*assertPT (cutFrm, 'Rlast) & */cohide ('Rlast) & DebuggingTactics.assert (0, 1) & /*DebuggingTactics.assert (cutFrm, SuccPosition (0) ) &*/
      implyR (SuccPosition (0) ) & assertT (1, 1) &
      generalize (varPos))
      }
    })


  private def topLevelAbstraction: DependentPositionTactic = "Abstraction" by ((p:Position, sequent:Sequent) => {
      assert(!p.isAnte, "no abstraction in antecedent")
      sequent.at(p)._1.ctx match {
        case b@Box(prg, phi) =>
          val vars = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.to[Seq]
          //else throw new IllegalArgumentException("Cannot handle non-concrete programs")
          val qPhi =
            if (vars.isEmpty) phi //Forall(Variable("$abstractiondummy", None, Real)::Nil, phi)
            else
            //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
              vars.filter(v=>v.isInstanceOf[Variable]).to[scala.collection.immutable.SortedSet]. //sortWith((l, r) => l.name < r.name || l.index.getOrElse(-1) < r.index.getOrElse(-1)). // sort by name; if same name, next by index
                foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))
          cut(Imply(qPhi, Box(prg, qPhi))) <(implyL('Llast) <(
              hide(p) /* result */ ,
              cohide2(AntePosition(sequent.ante.length), p.topLevel)
              & (monb | TactixLibrary.nil) &
              instantiate('Llast)*vars.length
            /*&
                assertT(1, 1) & DebuggingTactics.assert(Box(prg, qPhi), 'Llast) & DebuggingTactics.assert(b, 'Rlast) & (monb | TactixLibrary.nil) &
                assertT(1, 1) & DebuggingTactics.assert(qPhi, 'Llast) & DebuggingTactics.assert(phi, 'Rlast) & instantiate('Llast) * vars.length) &
                assertT(1, 1) & DebuggingTactics.assert(s => s.ante.head match {
                case Forall(_, _) => phi match {
                  case Forall(_, _) => true
                  case _ => false
                }
                case _ => true
              }*/) &
                (closeT | DebuggingTactics.debug("Abstraction cut use: Axiom close failed unexpectedly")),
            hide(p) & implyR('Rlast) & HilbertCalculus.V('Rlast) &
              (closeT | DebuggingTactics.debug("Abstraction cut show: Axiom close failed unexpectedly")))}})

  lazy val diffWeakenAbstraction: DependentPositionTactic = "diffWeaken" by ((p, sequent) => sequent.sub(p) match {
    case Some(b@Box(prg, phi)) =>
      require(p.isTopLevel && p.isSucc, "diffWeaken only at top level in succedent")
      val vars = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.to[Seq]
      val diffies = vars.filter(v=>v.isInstanceOf[DifferentialSymbol])
      if (diffies.nonEmpty) throw new IllegalArgumentException("abstractionT: found differential symbols " + diffies + " in " + b + "\nFirst handle those")
      //else throw new IllegalArgumentException("Cannot handle non-concrete programs")
      val qPhi =
        if (vars.isEmpty) phi //Forall(Variable("$abstractiondummy", None, Real)::Nil, phi)
        else
        //@todo what about DifferentialSymbols in boundVars? Decided to filter out since not soundness-critical.
          vars.filter(v=>v.isInstanceOf[Variable]).to[scala.collection.immutable.SortedSet]. //sortWith((l, r) => l.name < r.name || l.index.getOrElse(-1) < r.index.getOrElse(-1)). // sort by name; if same name, next by index
            foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))
      ContextTactics.cutImplyInContext(Imply(qPhi, b), p) <(
        implyL('Llast) <(hide(p.topLevel) /* result remains open */, TactixLibrary.close),
        cohide('Rlast) & implyR('Rlast) & DebuggingTactics.assert(1, 1) &
          ProofRuleTactics.propositionalCongruence(p.inExpr) &
          DebuggingTactics.assert(1, 1) & DebuggingTactics.assert(s => s.ante.head == qPhi && s.succ.head == b, s"Formula $qPhi and/or $b are not in the expected positions in abstractionT") &
          topLevelAbstraction('Rlast) & TactixLibrary.close)
      ???
    case _ => ???
  })

  /** diffWeaken by diffCut(consts) <(diffWeakenG, V&close) */
  lazy val diffWeaken: DependentPositionTactic = "diffWeaken" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(a, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeaken only at top level in succedent")

      def constAnteConditions(sequent: Sequent, taboo: Set[NamedSymbol]): IndexedSeq[Formula] = {
        sequent.ante.filter(f => StaticSemantics.freeVars(f).intersect(taboo).isEmpty)
      }
      val consts = constAnteConditions(sequent, StaticSemantics(a).bv.toSet)

      if (consts.nonEmpty) {
        // andL puts both conjuncts at the end of ante -> andL second-to-last (except first, where there's only 1 formula)
        val dw = diffWeakenG(pos) & implyR(1) & andL(-1) & andLSecondToLast*(consts.size-1) &
          // original evolution domain is in second-to-last ante position
          implyRi(AntePos(consts.size-1), SuccPos(0)) partial

        //@note assumes that first subgoal is desired result, see diffCut
        val vAllButFirst = dw +: Seq.tabulate(consts.length)(_ => V('Rlast) & close)
        //@note cut in reverse so that andL after diffWeakenG turns them into the previous order
        diffCut(consts.reverse: _*)(pos) <(vAllButFirst:_*) partial
      } else {
        diffWeakenG(pos)
      }
  })

  /** diffWeaken by DW & G */
  lazy val diffWeakenG: DependentPositionTactic = "diffWeakenG" by ((pos, sequent) => sequent.sub(pos) match {
    case Some(Box(_: ODESystem, p)) =>
      require(pos.isTopLevel && pos.isSucc, "diffWeakenG only at top level in succedent")
      cohide(pos.top) & DW(pos) & G
  })

  /** Helper for diffWeaken: andL the second-to-last formula */
  private lazy val andLSecondToLast: DependentTactic = new SingleGoalDependentTactic("andL-2nd-to-last") {
    override def computeExpr(sequent: Sequent): BelleExpr = andL(-(sequent.ante.length-1))
  }

  /** Searches for a time variable (some derivative x'=1) in the specified ODEs, returns None if not found. */
  private def findTimeInOdes(odes: DifferentialProgram): Option[Variable] = {
    var timeInOde: Option[Variable] = None
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preP(p: PosInExpr, prg: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = prg match {
        case AtomicODE(DifferentialSymbol(v), theta) =>
          if(theta == Number(1)) { timeInOde = Some(v); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
        case _ => Left(None)
      }
    }, odes)
    timeInOde
  }

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
    def odeDim(ode: ODESystem): Int = StaticSemantics.boundVars(ode).toSymbolSet.count(_.isInstanceOf[DifferentialSymbol])
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
