package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, ExpressionTraversal, Position, PosInExpr, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tools.DiffSolutionTool

import scala.collection.immutable.IndexedSeq
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
      override def computeExpr(sequent: Sequent): BelleExpr =
        if (isODESystem(sequent, pos)) {
          DESystemStep(pos)*getODEDim(sequent, pos)
          //@todo unification fails
          // TactixLibrary.useAt("DE differential effect (system)")(pos)*getODEDim(provable.subgoals.head, pos)
        } else {
          useAt("DE differential effect")(pos)
        }
      }

    /** A single step of DE system (@todo replace with useAt when unification for this example works) */
    private lazy val DESystemStep: DependentPositionTactic = new DependentPositionTactic("DE system step") {
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
              /* show */ cohide('Rlast) & equivifyR(1) & commuteEquivR(1) & US(USubst(subst), origin) & byUS("DE differential effect (system)"))
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
              derive(pos.append(PosInExpr(1::Nil))) &
                DE(pos) &
                Dassignb(pos.append(PosInExpr(1::Nil)))*getODEDim(sequent,pos) &
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
        val diffIndAllButFirst = skip +: Seq.tabulate(formulas.length)(_ => diffInd(qeTool)('Rlast) partial)
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
      cutR(Exists(y::Nil, Box(ODESystem(DifferentialProduct(c, AtomicODE(DifferentialSymbol(y), Plus(Times(a, y), b))), h), p)))(pos) <(
        /* use */ skip,
        /* show */ cohide(pos.topLevel) &
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
   */
  lazy val Dvariable: DependentPositionTactic = new DependentPositionTactic("x' derive variable") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = sequent.sub(pos) match {
        case Some(Differential(x: Variable)) =>
          val withxprime: Formula = sequent.replaceAt(pos, DifferentialSymbol(x)).asInstanceOf[Formula]
          val axiom = s"\\forall ${x.prettyString} (${x.prettyString})' = ${x.prettyString}'".asFormula
          cutLR(withxprime)(pos.topLevel) <(
              /* use */ skip,
              /* show */ cohide(pos.topLevel) & CMon(formulaPos(sequent(pos.topLevel), pos.inExpr)) & cut(axiom) <(
                useAt("all eliminate")(-1) & eqL2R(new AntePosition(0))(1) & useAt("-> self")(1) & close,
                cohide('Rlast) & byUS("x' derive variable"))
            )
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
          // HACK need some convention for internal names
//          val initialTime: Variable = freshNamedSymbol(Variable("kxtime", None, Real), node.sequent)
//          // universal quantifier and skolemization in ghost tactic (t:=0) will increment index twice
//          val time = Variable(initialTime.name,
//            initialTime.index match { case None => Some(1) case Some(a) => Some(a+2) }, initialTime.sort)
//          // boxAssignT and equivRight will extend antecedent by 2 -> length + 1
//          val introTime = nonAbbrvDiscreteGhostT(Some(initialTime), Number(0))(p) & boxAssignT(p) &
//            diffAuxiliaryT(time, Number(0), Number(1))(p) & FOQuantifierTacticsImpl.instantiateT(time, time)(p)
//          (time, introTime, true)
          throw new BelleError("diffSolve requires time t'=1 in ODE")
      }

      def createTactic(ode: DifferentialProgram, solution: Formula, time: Variable, iv: Map[Variable, Variable],
                       diffEqPos: Position): BelleExpr = {
        val initialGhosts = primedSymbols(ode).foldLeft(skip)((a, b) =>
          a & (discreteGhost(b)(diffEqPos) & DLBySubst.assignEquational(diffEqPos)))

        // flatten conjunctions and sort by number of right-hand side symbols to approximate ODE dependencies
        val flatSolution = flattenConjunctions(solution).
          sortWith((f, g) => StaticSemantics.symbols(f).size < StaticSemantics.symbols(g).size)

        initialGhosts & diffInvariant(tool, flatSolution:_*)(pos) & diffWeaken(pos) &
          exhaustiveEqR2L(hide = true)('Llast)*flatSolution.size

      }

      // initial values
      val iv: Map[Variable, Variable] =
        primedSymbols(odes).map(v => v -> TacticHelper.freshNamedSymbol(v, sequent(pos.topLevel))).toMap

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
            GreaterEqual(time, iv(time)))
          createTactic(odes, sol, time, iv, diffEqPos)
        case None => throw new BelleError("No solution found")
      }

  })

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
