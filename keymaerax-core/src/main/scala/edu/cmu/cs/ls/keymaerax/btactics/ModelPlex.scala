/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.StopTraversal
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.SimplificationTool

import scala.collection.immutable
import scala.compat.Platform
import scala.language.postfixOps

/**
 * ModelPlex: Verified runtime validation of verified cyber-physical system models.
  *
  * @author Stefan Mitsch
 * @author Andre Platzer
 * @see Stefan Mitsch and André Platzer. [[http://dx.doi.org/10.1007/s10703-016-0241-z ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *      Formal Methods in System Design, 42 pp. 2016. Special issue for selected papers from RV'14.
 * @see Stefan Mitsch and André Platzer. [[http://dx.doi.org/10.1007/978-3-319-11164-3_17 ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *      In Borzoo Bonakdarpour and Scott A. Smolka, editors, Runtime Verification - 5th International Conference, RV 2014, Toronto, ON, Canada, September 22-25, 2014. Proceedings, volume 8734 of LNCS, pages 199-214. Springer, 2014.
 */
object ModelPlex extends ModelPlexTrait {
  /**
   * Synthesize the ModelPlex (Controller) Monitor for the given formula for monitoring the given variable.
   */
  def apply(formula: Formula, kind: Symbol, checkProvable: Option[(ProvableSig => Unit)] = Some({case _ => ()})): Formula = formula match {
    case Imply(assumptions, Box(prg, _)) =>
      val vars = StaticSemantics.boundVars(prg).symbols.filter(v => v.isInstanceOf[Variable] && !v.isInstanceOf[DifferentialSymbol]).map((x:NamedSymbol)=>x.asInstanceOf[Variable]).toList
      val sortedVars = vars.sortWith((x,y)=>x<y)
      apply(sortedVars, kind, checkProvable)(formula)
    case _ => throw new IllegalArgumentException("Unsupported shape of formula " + formula)
  }

  /**
   * Synthesize the ModelPlex (Controller) Monitor for the given formula for monitoring the given variable.
   */
  def apply(vars: List[Variable], kind: Symbol): (Formula => Formula) = apply(vars, kind, checkProvable=Some({case _ => ()}))

  /**
   * Synthesize the ModelPlex (Controller) Monitor for the given formula for monitoring the given variable.
    * @ param kind The kind of monitor, either 'ctrl or 'model.
    *
    * @param checkProvable true to check the Provable proof certificates (recommended).
   */
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Option[(ProvableSig => Unit)]): (Formula => Formula) = formula => {
    require(kind == 'ctrl || kind == 'model, "Unknown monitor kind " + kind + ", expected one of 'ctrl or 'model")
    val (mxInputFml, assumptions) = createMonitorSpecificationConjecture(formula, vars:_*)
    val mxInputSequent = Sequent(immutable.IndexedSeq[Formula](), immutable.IndexedSeq(mxInputFml))
    //@note SimplifierV2 disabled as precaution in case Z3 cannot prove one of its lemmas
    val tactic = (kind, ToolProvider.simplifierTool()) match {
      case ('ctrl, tool) => controllerMonitorByChase(1) & (optimizationOneWithSearch(tool, assumptions)(1)*) &
        (if (tool.isDefined) SimplifierV2.simpTac(1) else skip)
      case ('model, tool) => modelMonitorByChase(1) & (optimizationOneWithSearch(tool, assumptions)(1)*) &
        (if (tool.isDefined) SimplifierV2.simpTac(1) else skip)
      case _ => throw new IllegalArgumentException("Unknown monitor kind " + kind + ", expected one of 'ctrl or 'model; both require a simplification tool")
    }

    val proofStart = Platform.currentTime
    val result = TactixLibrary.proveBy(ProvableSig.startProof(mxInputSequent), tactic)
    val proofDuration = Platform.currentTime - proofStart
    Console.println("[proof time " + proofDuration + "ms]")

    assert(result.subgoals.size == 1 && result.subgoals.head.ante.isEmpty &&
      result.subgoals.head.succ.size == 1, "ModelPlex tactic expected to provide a single formula (in place version)")
    assert(result.conclusion == mxInputSequent, "Proof was a proof of the ModelPlex specification")
    // @todo conjunction with phi|_cnst when monitor should also check the conditions on constants
    val mxOutputProofTree = result.subgoals.head.succ.head
    checkProvable match {
      case Some(report) =>
        report(result)
        println("ModelPlex Proof certificate: Produced")
        mxOutputProofTree
      case None =>
        println("ModelPlex Proof certificate: Skipped")
        mxOutputProofTree
    }
  }

  /** Returns the post variable of `v` */
  private def postVar = (v: Variable) => BaseVariable(v.name + "post", v.index)
  private def preVar = (v: Variable) => BaseVariable(v.name + "pre", v.index)

  /**
    * Construct ModelPlex monitor specification conjecture corresponding to given formula.
    *
    * @param fml A formula of the form p -> [a]q, which was proven correct.
    * @param vars A list of variables V, superset of BV(a).
    * @return A tuple of monitor conjecture and assumptions
    * @see Mitsch, Platzer: ModelPlex (Definition 3, Lemma 4, Corollary 1).
    */
  def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): (Formula, List[Formula]) = {
    require(vars.nonEmpty, "ModelPlex expects non-empty list of variables to monitor")
    require(StaticSemantics.symbols(fml).intersect(vars.map(postVar).toSet).isEmpty,
      "ModelPlex post symbols must not occur in original formula")

    def conjectureOf(assumptions: Formula, prg: Program): (Formula, List[Formula]) = {
      val boundVars = StaticSemantics.boundVars(prg).symbols
      assert(boundVars.forall(v => !v.isInstanceOf[Variable] || v.isInstanceOf[DifferentialSymbol] || vars.contains(v)),
        "All bound variables " + StaticSemantics.boundVars(prg).prettyString + " must occur in monitor list " + vars.mkString(", ") +
          "\nMissing: " + (StaticSemantics.boundVars(prg).symbols.toSet diff vars.toSet).mkString(", "))
      val posteqs = vars.map(v => Equal(postVar(v), v)).reduceRight(And)
      //@note suppress assumptions mentioning bound variables
      val nonboundAssumptions = FormulaTools.conjuncts(assumptions).filter(a => boundVars.intersect(StaticSemantics.freeVars(a).symbols).isEmpty)
      (Diamond(prg, posteqs), nonboundAssumptions)
    }

    fml match {
      case Imply(assumptions, Box(prg, _)) => conjectureOf(assumptions, prg)
      case _ => throw new IllegalArgumentException("Unsupported shape of formula " + fml)
    }
  }

  /** Conjecture for double-checking a monitor formula for correctness: assumptions -> (monitor -> < prg; >Upsilon). */
  def createMonitorCorrectnessConjecture(vars: List[Variable], kind: Symbol, checkProvable: Option[(ProvableSig => Unit)]): (Formula => Formula) = formula => {
    val monitor = apply(vars, kind, checkProvable)(formula)
    val (monitorConjecture, assumptions) = createMonitorSpecificationConjecture(formula, vars:_*)
    Imply(assumptions.reduceOption(And).getOrElse(True), Imply(monitor, monitorConjecture))
  }

  /** Creates a sandbox safety conjecture from a formula of the shape init->[{ctrl;plant}*]safe. The sandbox embeds
    * an (unverified) external controller in monitor checks of `kind`. It approximates the external controller behavior
    * with nondeterministic values for each of the `ctrlVars`. Input to the external controller is measured with
    * nondeterministic values for each of the `senseVars`, but restricted to those satisfying the `plantApprox`
    * formula and the plant evolution domain constraints. If the monitor is satisfied, the external controller's
    * decision are actuated. Otherwise (monitor unsatisfied) `fallback` (if specified, ctrl by default) is executed.
    */
  def createSandbox(vars: List[Variable], consts: List[FuncOf], senseVars: List[Variable], ctrlVars: List[Variable],
                    fallback: Option[Program], plantApprox: Formula, kind: Symbol,
                    checkProvable: Option[(ProvableSig => Unit)]): (Formula => Formula) = formula => {
    require(kind == 'ctrl, s"Unable to create a sandbox of kind $kind, so far only controller monitors supported")
    val monitor = apply(vars, kind, checkProvable)(formula)
    formula match {
      case Imply(init, Box(Compose(Test(bounds), Loop(Compose(ctrlPrg, ODESystem(ode, q)))), safe)) =>
        // todo sanity check consts, senseVars, ctrlVars with bound and free vars of the programs
        assert(proveBy(Imply(init,bounds), auto).isProved)
        val preVars = senseVars.map(v => preVar(v) -> v)
        assert((StaticSemantics(And(plantApprox,q)).fv -- senseVars).toSet.subsetOf(preVars.map(_._1).toSet),
          "Plant approximation only allowed to mention sensed variables and their initial states")
        val pre = preVars.map(Assign.tupled).reduceOption(Compose).getOrElse(Test(True))
        // senseVars0:=senseVars; senseVars:=*; ?Q;
        val readSensors = senseVars.map(AssignAny).reduceOption(Compose).getOrElse(Test(True))
        val sense = Compose(pre, Compose(readSensors, Test(And(plantApprox, q))))
        // ctrlVarsTemp:=*;
        val ctrl = ctrlVars.map(postVar).map(AssignAny).reduceOption(Compose).getOrElse(Test(True))
        // ctrlVars:=ctrlVarsTemp
        val operationalize = ctrlVars.map(v => Assign(v, postVar(v))).reduceOption(Compose).getOrElse(Test(True))
        // if (monitor) ctrlVars:=ctrlVarsTemp else ctrlVars:=fallback
        val act = Choice(Compose(Test(monitor), operationalize), Compose(Test(Not(monitor)), fallback.getOrElse(ctrlPrg)))

        Imply(init, Box(Compose(Test(bounds), Loop(Compose(sense, Compose(ctrl, act)))), safe))
    }
  }

  /**
   * Returns a tactic to derive a controller monitor in axiomatic style using forward chase. The tactic is designed to
   * operate on input produced by createMonitorSpecificationConjecture.
    *
    * @see [[createMonitorSpecificationConjecture]]
   * @example{{{
   *        |- xpost=1
   *        ------------------------------controllerMonitorByChase(1)
   *        |- <{x:=1; {x'=2}}*>xpost=x
   * }}}
   * In order to produce the result above, the tactic performs intermediate steps as follows.
   * @example{{{
   *        |- xpost=1
   *        ------------------------------true&
   *        |- (true & xpost=1)
   *        ------------------------------<:=> assign
   *        |- <x:=1;>(true & xpost=x)
   *        ------------------------------DX diamond differential skip
   *        |- <x:=1; {x'=2}>xpost=x
   *        ------------------------------<*> approx
   *        |- <{x:=1; {x'=2}}*>xpost=x
   * }}}
   * @return The tactic.
   */
  def controllerMonitorByChase: DependentPositionTactic = chase(3,3, (e:Expression) => e match {
    // remove loops
    case Diamond(Loop(_), _) => "<*> approx" :: Nil
    // remove ODEs for controller monitor
    case Diamond(ODESystem(_, _), _) => "DX diamond differential skip" :: Nil
    case _ => println("Chasing " + e.prettyString); AxiomIndex.axiomsFor(e)
  })

  /**
    * Returns a tactic to derive a model monitor in axiomatic style using forward chase + diffSolve. The tactic is
    * designed to operate on input produced by createMonitorSpecificationConjecture.
    *
    * @see [[createMonitorSpecificationConjecture]]
    * @return The tactic.
    */
  lazy val modelMonitorByChase: DependentPositionTactic = modelMonitorByChase()
  def modelMonitorByChase(ode: DependentPositionTactic = AxiomaticODESolver.axiomaticSolve()): DependentPositionTactic = "modelMonitor" by ((pos: Position, seq: Sequent) => chase(3,3, (e:Expression) => e match {
    // remove loops and split compositions to isolate differential equations before splitting choices
    case Diamond(Loop(_), _) => "<*> approx" :: Nil
    case Diamond(Compose(_, _), _) => AxiomIndex.axiomsFor(e)
    case _ => Nil
  })(pos) &
    applyAtAllODEs(ode)(pos) & // solve isolated ODEs once before splitting choices
    // chase and solve remaining
    chase(3,3, (e:Expression) => e match {
      // remove loops
      case Diamond(Loop(_), _) => "<*> approx" :: Nil
      // keep ODEs, solve later
      case Diamond(ODESystem(_, _), _) => Nil
      case _ => println("Chasing " + e.prettyString); AxiomIndex.axiomsFor(e)
    })(pos) &
    applyAtAllODEs(ode)(pos))

  /** Applies tatic `t` at all ODEs underneath this tactic's position. */
  def applyAtAllODEs(t: DependentPositionTactic): DependentPositionTactic = TacticFactory.anon((pos: Position, sequent: Sequent) => {
    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
      case (Diamond(_: ODESystem, _), pp) => Some(t(pp))
      case _ => None
    })
    positions.reduceRightOption[BelleExpr](_ & _).getOrElse(skip)
  })

  /** Euler-approximates all atomic ODEs somewhere underneath pos */
  def eulerAllIn: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => {
    val eulerAxiom = "<{x_'=f(x_)}>p(x_) <-> \\exists t_ (t_>=0 & \\forall e_ (e_>0 -> \\forall h0_ (h0_>0 -> \\exists h_ (0<h_&h_<h0_&<{x_:=x_+h_*f(x_);}*>(t_>=0 & \\exists y_ (abs(x_-y_) < e_ & p(y_))) ))))".asFormula
    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
      case (Diamond(_: ODESystem, _), pp) => Some(useAt(ProvableSig.startProof(eulerAxiom), PosInExpr(0::Nil))(pp))
      case _ => None
    })
    positions.reduceRightOption[BelleExpr](_ & _).getOrElse(skip)
  })

  /** Euler-approximates all ODEs somewhere underneath pos. Systematic tactic, but not a proof. */
  def eulerSystemAllIn: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => {
    /** Simultaneous updates of all variables with step size h */
    def createSystemApprox(atoms: List[AtomicODE], h: Term): Program = {
      val initial: Map[Variable, Variable] = atoms.map({ case AtomicODE(DifferentialSymbol(x), _) =>
        x -> TacticHelper.freshNamedSymbol(x, sequent)}).toMap
      val initials = initial.map({case (v, v0) => Assign(v0, v)}).reduce(Compose)
      val eulerSteps: Program = atoms.map({case AtomicODE(DifferentialSymbol(x), f) =>
        Assign(x, Plus(x, Times(h, initial.foldLeft(f)({case (ff, (y, y0)) => ff.replaceFree(y, y0)}))))}).reduce(Compose)
      Compose(initials, eulerSteps)
    }

    /** Error norm */
    def createErrorMargin(primed: List[Variable], e: Term, p: Formula): Formula = {
      // \exists y_ (norm(x_-y_) < e_ & p(y_))
      val ys: Map[Variable, Variable] = primed.map(x => x -> TacticHelper.freshNamedSymbol(Variable("y" + x.name, x.index, x.sort), sequent)).toMap
      val py = ys.foldLeft(p)({case (pp, (x, y)) => pp.replaceFree(x, y)})
      val norm = ys.map({case (x, y) => Power(Minus(x, y), Number(2))}).reduce(Plus)
      val marginP = And(Less(norm, Power(e, Number(2))), py)
      //Exists(ys.values.toList, margin)
      ys.foldLeft[Formula](marginP)({case (m, (_, y)) => Exists(y::Nil, m)})
    }

    def createEulerAxiom(ode: ODESystem, p: Formula): Formula = {
      val h = "h_".asVariable
      val e = "e_".asVariable
      val systemApprox = createSystemApprox(DifferentialHelper.atomicOdes(ode), h)
      val errorMargin = createErrorMargin(DifferentialHelper.getPrimedVariables(ode), e, p)
      s"<{c_&q_(||)}>p_(||) <-> \\exists t_ (t_>=0 & \\forall $e ($e>0 -> \\forall h0_ (h0_>0 -> \\exists $h (0<$h&$h<h0_&<{$systemApprox}*>(t_>=0 & $errorMargin) ))))".asFormula
    }

    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
      //@note OnAll necessary since the "show axiom" branches are left open by useAt (because we cut in the desired result, not use an actual axiom)
      case (Diamond(ode: ODESystem, p), dpos) => Some(OnAll(useAt(ProvableSig.startProof(createEulerAxiom(ode, p)), PosInExpr(0::Nil))(dpos) | skip))
      case _ => None
    })
    positions.reduceRightOption[BelleExpr](_ & _).getOrElse(skip)
  })

  /** Unsound approximation step */
  def flipUniversalEulerQuantifiers(fml: Formula): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
        case Forall(e, Imply(pe, Forall(h0, Imply(ph0, ph)))) => Right(Exists(e, And(pe, Exists(h0, And(ph0,ph)))))
        case _ => Left(None)
      }
    }, fml).getOrElse(fml)
  }

  /** Unrolls diamond loops */
  def unrollLoop(n: Int): DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => {
    if (n <= 0) skip
    else {
      val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
        case (Diamond(_: Loop, _), pp) =>
          if (n == 1) Some(useAt("<*> approx")(pp))
          else Some(useAt("<*> iterate", PosInExpr(0 :: Nil))(pp))
        case _ => None
      })
      positions.reduceRightOption[BelleExpr](_ & _).getOrElse(skip) & unrollLoop(n-1)(pos)
    }
  })

  /** Chases remaining assignments. */
  lazy val chaseEulerAssignments: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => {
    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
      case (Diamond(_, _), pp) => Some(chase(pp))
      case _ => None
    })
    positions.lastOption.getOrElse(skip)
  })

  /**
   * ModelPlex sequent-style synthesis technique, i.e., with branching so that the tactic can operate on top-level
   * operators. Operates on monitor specification conjectures.
    *
    * @see[[createMonitorSpecificationConjecture]]
   * @return The tactic.
   */
  def modelplexSequentStyle: DependentPositionTactic = ???

  /**
   * ModelPlex backward proof tactic for axiomatic-style monitor synthesis, i.e., avoids proof branching as occuring in
   * the sequent-style synthesis technique. The tactic 'unprog' determines what kind of monitor (controller monitor,
   * model monitor) to synthesize. Operates on monitor specification conjectures.
    *
    * @param useOptOne Indicates whether or not to use Opt. 1 at intermediate steps.
   * @param unprog A tactic for a specific monitor type (either controller monitor or model monitor).
   * @see [[createMonitorSpecificationConjecture]]
   * @see [[controllerMonitorT]]
   * @see [[modelMonitorT]]
   */
  def modelplexAxiomaticStyle(useOptOne: Boolean)
                             (unprog: Boolean => DependentPositionTactic): DependentPositionTactic = "Modelplex In-Place" by ((pos: Position, sequent: Sequent) => {
    sequent.sub(pos) match {
      case Some(Diamond(_, _)) =>
        ((debug("Before HP") & unprog(useOptOne)(pos) & debug("After  HP"))*) &
          debug("Done with transformation, now looking for quantifiers") &
          debug("Modelplex done")
    }
  })

  /**
   * Returns a backward tactic for deriving controller monitors. Uses Opt. 1 immediately after nondeterministic
   * assignments if useOptOne, avoids Opt. 1 at intermediate steps if !useOptOne.
    *
    * @param useOptOne Indicates whether or not to use Opt. 1 at intermediate steps.
   * @return The tactic.
   */
  def controllerMonitorT(useOptOne: Boolean): DependentPositionTactic =
    "Axiomatic controller monitor" by ((pos: Position) =>
      locateT(
        useAt("<*> approx", PosInExpr(1::Nil)) ::
        useAt("DX diamond differential skip", PosInExpr(1::Nil)) ::
        useAt("<;> compose") ::
        useAt("<++> choice") ::
        ("<:*> nondet assign opt. 1" by ((p: Position) => useAt("<:*> assign nondet")(p) & (if (useOptOne) optimizationOne()(p) else skip))) ::
        useAt("<?> test") ::
        useAt("<:=> assign") ::
        ("<:=> assign opt. 1" by ((p: Position) => useAt("<:=> assign equality")(p) & (if (useOptOne) optimizationOne()(p) else skip))) ::
        Nil)(pos))

  /**
   * Returns a backward tactic for deriving model monitors. Uses Opt. 1 immediately after nondeterministic
   * assignments if useOptOne, avoids Opt. 1 at intermediate steps if !useOptOne.
    *
    * @param useOptOne Indicates whether or not to use Opt. 1 at intermediate steps.
   * @return The tactic.
   */
  def modelMonitorT(useOptOne: Boolean): DependentPositionTactic = "Axiomatic model monitor" by ((pos: Position) =>
    locateT(
      useAt("<*> approx", PosInExpr(1::Nil)) ::
        AxiomaticODESolver.axiomaticSolve() ::
        useAt("<;> compose") ::
        useAt("<++> choice") ::
        ("<:*> nondet assign opt. 1" by ((p: Position) => useAt("<:*> assign nondet")(p) & (if (useOptOne) optimizationOne()(p) else skip))) ::
        useAt("<?> test") ::
        useAt("<:=> assign") ::
        ("<:=> assign opt. 1" by ((p: Position) => useAt("<:=> assign equality")(p) & (if (useOptOne) optimizationOne()(p) else skip))) ::
        Nil)(pos))

  /**
   * Returns a tactic to solve two-dimensional differential equations. Introduces constant function symbols for
   * variables that do not change in the ODE, before it hands over to the actual diff. solution tactic.
    *
    * @return The tactic.
   */
  def diamondDiffSolve2DT: DependentPositionTactic = "<','> differential solution" by ((pos: Position, sequent: Sequent) => {
    ??? //(diffIntroduceConstantT & ODETactics.diamondDiffSolve2DT)(p)
  })

  /**
   * Returns a modified test tactic for axiom <?H>p <-> H & (H->p)
    *
    * @example{{{
   *          |- x>0 & (x>0 -> [x'=x]x>0)
   *          ---------------------------diamondTestRetainCondition
   *          |- <?x>0>[x'=x]x>0
   * }}}
   * @return The tactic.
   * @note Unused so far, for deriving prediction monitors where DI is going to rely on knowledge from prior tests.
   */
  def diamondTestRetainConditionT: DependentPositionTactic = ???

  /**
   * Performs a tactic from the list of tactics that is applicable somewhere underneath position p in sequent s,
   * taking the outermost such sub-position of p. Formulas only.
    *
    * @example{{{
   *           |- a=1 & (<x:=2;>x+y>0 & <y:=3;>x+y>0)
   *           ---------------------------------------locateT(diamondSeqT :: diamondChoiceT :: Nil)(1)
   *           |- a=1 & <x:=2; ++ y:=3;>x+y>0
   * }}}
   * @param tactics The list of tactics.
   * @return The tactic.
   */
  def locateT(tactics: List[DependentPositionTactic]): DependentPositionTactic = "Modelplex Locate" by ((pos: Position, sequent: Sequent) => {
    require(tactics.nonEmpty, "At least 1 tactic required")
    val here = tactics.map(_(pos)).reduceRight[BelleExpr](_ | _)

    def recurseOnFormula(p: Position) = sequent.sub(p) match {
      case Some(_: Formula) => locateT(tactics)(p)
      case _ => DebuggingTactics.error("Stop recursion")
    }

    val left: BelleExpr = recurseOnFormula(pos ++ PosInExpr(0::Nil))
    val right: BelleExpr = recurseOnFormula(pos ++ PosInExpr(1::Nil))

    here | left | right
  })

  /** Opt. 1 from Mitsch, Platzer: ModelPlex, i.e., instantiates existential quantifiers with an equal term phrased
    * somewhere in the quantified formula.
    *
    * @example{{{
    *           |- xpost>0 & xpost=xpost
    *           ------------------------------optimizationOneWithSearch
    *           |- \exists x x>0 & xpost=x
    * }}}
    * @see[[optimizationOneWithSearchAt]]
    */
  def optimizationOneWithSearch(tool: Option[SimplificationTool], assumptions: List[Formula]): DependentPositionTactic = "Optimization 1 with instance search" by ((pos: Position, sequent: Sequent) => {
    val simplForall1 = proveBy("p(f()) -> \\forall x_ (x_=f() -> p(x_))".asFormula, implyR(1) & allR(1) & implyR(1) & eqL2R(-2)(1) & close)
    val simplForall2 = proveBy("p(f()) -> \\forall x_ (f()=x_ -> p(x_))".asFormula, implyR(1) & allR(1) & implyR(1) & eqR2L(-2)(1) & close)

    def solutionQE(existsFml: Formula, qeFml: Formula, signature: Set[Function], assumptions: List[Formula]) = "ANON" by ((pp: Position, seq: Sequent) => {
      tool match {
        case None => skip
        case Some(t) =>
          val simplified = t.simplify(qeFml, assumptions)
          val backSubst = And(
            assumptions.reduceOption(And).getOrElse(True),
            signature.foldLeft[Formula](simplified)((fml, t) => fml.replaceAll(Variable(t.name, t.index), FuncOf(t, Nothing))))
          val pqe = proveBy(Imply(backSubst, existsFml), QE & done)
          cutAt(backSubst)(pp) < (skip, (if (pp.isSucc) cohideR(pp.topLevel) else cohideR('Rlast)) & CMon(pp.inExpr) & by(pqe))
      }
    })

    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
        case (Forall(xs, Imply(Equal(x, _), _)), pp) if pp.isSucc && xs.contains(x) => Some(useAt(simplForall1, PosInExpr(1::Nil))(pp))
        case (Forall(xs, Imply(Equal(_, x), _)), pp) if pp.isSucc && xs.contains(x) => Some(useAt(simplForall2, PosInExpr(1::Nil))(pp))
        // @note shape of ode solution
        case (ode@Exists(t::Nil, And(GreaterEqual(_, _), And(Forall(s::Nil, Imply(And(_, _), _)), _))), pp)
            if tool.isDefined && pp.isSucc && t == "t_".asVariable && s == "s_".asVariable =>
          val signature = StaticSemantics.signature(ode).filter({
            case Function(_, _, Unit, _, false) => true case _ => false }).map(_.asInstanceOf[Function])
          val edo = signature.foldLeft[Formula](ode)((fml, t) => fml.replaceAll(FuncOf(t, Nothing), Variable(t.name, t.index)))
          val transformed = proveBy(edo, partialQE)
          Some(solutionQE(ode, transformed.subgoals.head.succ.head, signature, assumptions)(pp) |
               solutionQE(ode, transformed.subgoals.head.succ.head, signature, Nil)(pp) |
               skip)
        case (Exists(_, _), pp) if pp.isSucc => Some(optimizationOneWithSearchAt(pp))
        case (Forall(_, _), pp) if pp.isAnte => Some(optimizationOneWithSearchAt(pp))
        case _ => None
      })
    positions.reduceRightOption[BelleExpr]((a, b) => a & b).getOrElse(skip)
  })

  /** Opt. 1 at a specific position, i.e., instantiates the existential quantifier with an equal term phrased
    * somewhere in the quantified formula. */
  private def optimizationOneWithSearchAt: DependentPositionTactic = "Optimization 1 with instance search at" by ((pos: Position, sequent: Sequent) => {
    sequent.sub(pos) match {
      case Some(Exists(vars, And(Equal(l, r), _))) if pos.isSucc && vars.contains(l) =>
        // case from deterministic assignments
        val equality: Option[(Variable, Term)] = Some(l.asInstanceOf[BaseVariable] -> r)
        debug("Running optimization 1 at " + pos + " using equality " + equality) & optimizationOneAt(equality)(pos)
      case Some(Exists(vars, phi)) if pos.isSucc =>
        // case from nondeterministic assignments

        class SynonymFinder(v: NamedSymbol) extends ExpressionTraversalFunction {
          var synonyms: Set[Term] = Set()
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
            case Equal(l, r) if v==l => synonyms = synonyms + r; Left(None)
            case Equal(l, r) if v==r => synonyms = synonyms + l; Left(None)
            case Or(l, r) =>
              val lFinder = new SynonymFinder(v)
              val rFinder = new SynonymFinder(v)
              ExpressionTraversal.traverse(lFinder, l)
              ExpressionTraversal.traverse(rFinder, r)
              synonyms = synonyms ++
                (if (lFinder.synonyms.nonEmpty && rFinder.synonyms.nonEmpty) lFinder.synonyms & rFinder.synonyms
                 else lFinder.synonyms | rFinder.synonyms)
              Right(e)
            case _ => Left(None)
          }
        }

        val v = vars.head
        val vFinder = new SynonymFinder(v)
        ExpressionTraversal.traverse(vFinder, phi)

        //@note use synonym if all equalities (except x=xpost) agree across branches, otherwise instantiate with "xpost"
        val postEquality = vFinder.synonyms.find({
          case r: Variable => v.name + "post" == r.name
          case _ => false})
        val remainingEqs = vFinder.synonyms.filter(Some(_) != postEquality)
        val equality: Option[Term] =
          if (remainingEqs.size == 1) Some(remainingEqs.head)
          else postEquality
        optimizationOneAt(equality.map(v -> _))(pos)
    }
  })


  /**
   * Opt. 1 from Mitsch, Platzer: ModelPlex, i.e., instantiates an existential quantifier with a post-variable. Since
   * the tactic may be used in intermediate steps of ModelPlex, it uses fresh variants of the post-variable for
   * instantiation, if asked to automatically instantiate.
    *
    * @example{{{
   *           |- z>0 & xpost=z
   *           -----------------------------------optimizationOne(Some(Variable("x"), Variable("z")))
   *           |- \exists x (x>0 & xpost=x)
   * }}}
   * @example{{{
   *           |- xpost_0>0 & xpost=xpost_0
   *           -----------------------------------optimizationOne(None)
   *           |- \exists x (x>0 & xpost=x)
   * }}}
   * @param inst The instance for a quantified variable. If None, the tactic will use a fresh variant of the
   *             corresponding post-variable.
   * @return The tactic.
   */
  def optimizationOne(inst: Option[(Variable, Term)] = None): DependentPositionTactic = locateT(optimizationOneAt(inst)::Nil)

  /** Opt. 1 at a specific position */
  private def optimizationOneAt(inst: Option[(Variable, Term)] = None): DependentPositionTactic = "Optimization 1" by ((pos: Position, sequent: Sequent) => {
    sequent.sub(pos) match {
      case Some(Exists(vars, phi)) if pos.isSucc => inst match {
          case Some(i) => existsR(i._1, i._2)(pos)
          case None =>
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, BaseVariable(s"${v.name.replaceAllLiterally("_", "")}post", Some(0)))).head
            existsR(v, post)(pos)
        }
        case Some(Forall(vars, phi)) if pos.isAnte => inst match {
          case Some(i) => allL(i._1, i._2)(pos)
          case None =>
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, BaseVariable(s"${v.name.replaceAllLiterally("_", "")}post", Some(0)))).head
            allL(v, post)(pos)
        }
    }
  })

  /** Simplifies reflexive comparisons and implications/conjunctions/disjunctions with true. */
  def simplify(): DependentTactic = "ModelPlex Simplify" by ((sequent: Sequent) => {
    sequent.ante.indices.map(i => SimplifierV2.simpTac(AntePosition.base0(i))).reduceOption[BelleExpr](_ & _).getOrElse(skip) &
    sequent.succ.indices.map(i => SimplifierV2.simpTac(SuccPosition.base0(i))).reduceOption[BelleExpr](_ & _).getOrElse(skip)
  })

  /** Turns the formula `fml` into a single inequality. */
  def toMetric(fml: Formula): Formula = {
    val cmpNF = chase(3, 3, (e: Expression) => e match {
      case NotEqual(_, _) => "!= expand"::Nil
      case Equal(_, _) => "= expand"::Nil
      case And(_, _) => "& recursor"::Nil
      case Or(_, _) => "| recursor"::Nil
      case _ => Nil
    })

    val arithNF = chase(3, 3, (e: Expression) => e match {
      case Less(_, r) if r != Number(0) => "metric <"::Nil
      case LessEqual(_, r) if r != Number(0) => "metric <="::Nil
      case And(_,_) => "& recursor"::Nil
      case Or(_,_) => "| recursor"::Nil
      case _ => Nil
    })

    val propNF = chaseCustom({
      case LessEqual(_, _) => fromAxIndex("<= to <")::Nil
      case And(Less(_, _), Less(_, _)) => fromAxIndex("metric < & <")::Nil
      case And(LessEqual(_, _), LessEqual(_, _)) => fromAxIndex("metric <= & <=")::Nil
      case And(LessEqual(_, _), Less(_, _)) => fromAxIndex("& recursor")::Nil
      case And(Less(_, _), LessEqual(_, _)) => fromAxIndex("& recursor")::Nil
      case And(_: BinaryCompositeFormula, _: BinaryCompositeFormula) => fromAxIndex("& recursor")::Nil
      case And(_: BinaryCompositeFormula, _) => (DerivedAxioms.andRecursor.fact, PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)::Nil
      case And(_, _: BinaryCompositeFormula) => (DerivedAxioms.andRecursor.fact, PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)::Nil
      case Or(Less(_, _), Less(_, _)) => fromAxIndex("metric < | <")::Nil
      case Or(LessEqual(_, _), LessEqual(_, _)) => fromAxIndex("metric <= | <=")::Nil
      case Or(LessEqual(_, _), Less(_, _)) => fromAxIndex("| recursor")::Nil
      case Or(Less(_, _), LessEqual(_, _)) => fromAxIndex("| recursor")::Nil
      case Or(_: BinaryCompositeFormula, _: BinaryCompositeFormula) => fromAxIndex("| recursor")::Nil
      case Or(_: BinaryCompositeFormula, _) => (DerivedAxioms.orRecursor.fact, PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)::Nil
      case Or(_, _: BinaryCompositeFormula) => (DerivedAxioms.orRecursor.fact, PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)::Nil
      case _ => Nil
    })

    val (nnf, _) = IsabelleSyntax.normalise(fml)
    val result = proveBy(nnf, cmpNF(1) & arithNF(1) &
      Idioms.repeatWhile(_.isInstanceOf[BinaryCompositeFormula])(propNF(1))(1))
    assert(result.subgoals.length == 1 && result.subgoals.head.ante.isEmpty && result.subgoals.head.succ.length == 1)
    result.subgoals.head.succ.head
  }

  private def mapSubpositions[T](pos: Position, sequent: Sequent, trafo: (Expression, Position) => Option[T]): List[T] = {
    var result: List[T] = Nil
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = trafo(e, pos ++ p) match {
        case Some(tt) => result = tt +: result; Left(None)
        case None => Left(None)
      }
      override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = trafo(t, pos ++ p) match {
        case Some(tt) => result = tt +: result; Left(None)
        case None => Left(None)
      }
    }, sequent.sub(pos).get.asInstanceOf[Formula])
    result
  }
}
