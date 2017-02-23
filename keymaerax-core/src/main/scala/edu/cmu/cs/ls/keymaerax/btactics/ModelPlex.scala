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
  def apply(formula: Formula, kind: Symbol, checkProvable: Boolean = true): Formula = formula match {
    case Imply(assumptions, Box(prg, _)) =>
      val vars = StaticSemantics.boundVars(prg).symbols.filter(v => v.isInstanceOf[Variable] && !v.isInstanceOf[DifferentialSymbol]).map((x:NamedSymbol)=>x.asInstanceOf[Variable]).toList
      val sortedVars = vars.sortWith((x,y)=>x<y)
      apply(sortedVars, kind, checkProvable)(formula)
    case _ => throw new IllegalArgumentException("Unsupported shape of formula " + formula)
  }

  /**
   * Synthesize the ModelPlex (Controller) Monitor for the given formula for monitoring the given variable.
   */
  def apply(vars: List[Variable], kind: Symbol): (Formula => Formula) = apply(vars, kind, checkProvable=true)

  /**
   * Synthesize the ModelPlex (Controller) Monitor for the given formula for monitoring the given variable.
    * @ param kind The kind of monitor, either 'ctrl or 'model.
    *
    * @param checkProvable true to check the Provable proof certificates (recommended).
   */
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Boolean): (Formula => Formula) = formula => {
    require(kind == 'ctrl || kind == 'model, "Unknown monitor kind " + kind + ", expected one of 'ctrl or 'model")
    val (mxInputFml, assumptions) = createMonitorSpecificationConjecture(formula, vars:_*)
    val mxInputSequent = Sequent(immutable.IndexedSeq[Formula](), immutable.IndexedSeq(mxInputFml))
    val tactic = (kind, ToolProvider.simplifierTool()) match {
      case ('ctrl, Some(tool)) => controllerMonitorByChase(1) & (optimizationOneWithSearch(tool, assumptions)(1)*) & SimplifierV2.simpTac(1)
      case ('model, Some(tool)) => modelMonitorByChase(1) & (optimizationOneWithSearch(tool, assumptions)(1)*) & SimplifierV2.simpTac(1)
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
    if (checkProvable) {
      //@todo probably doesn't make much sense anymore in new version
      val witnessStart= Platform.currentTime
      val provable = result.proved
      assert(provable.ante.size == 1 && provable.succ.size == 1, "ModelPlex tactic expected to provide a single formula (in place version)")
      assert(provable == mxInputSequent, "Provable is a proof of the ModelPlex specification")
      assert(provable.ante.head == True)
      val mxOutput = provable.succ.head
      assert(mxOutput == mxOutputProofTree, "ModelPlex output from Provable and from ProofNode agree (if ProofNode is correct)")
      val witnessDuration = Platform.currentTime - witnessStart
      Console.println("[proof time       " + proofDuration + "ms]")
      Console.println("[certificate time " + witnessDuration + "ms]")
      println("ModelPlex Proof certificate: Passed")
      mxOutput
    } else {
      println("ModelPlex Proof certificate: Skipped")
      mxOutputProofTree
    }
  }

  /**
   * Construct ModelPlex monitor specification conjecture corresponding to given formula.
    *
    * @param fml A formula of the form p -> [a]q, which was proven correct.
   * @param vars A list of variables V, superset of BV(a).
   * @see Mitsch, Platzer: ModelPlex (Definition 3, Lemma 4, Corollary 1).
   */
  def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): (Formula, List[Formula]) = {
    require(vars.nonEmpty, "ModelPlex expects non-empty list of variables to monitor")
    require(StaticSemantics.symbols(fml).intersect(
      vars.toSet[Variable].map(v=>Function(v.name + "pre", v.index, Unit, v.sort).asInstanceOf[NamedSymbol]) ++
        vars.toSet[Variable].map(v=>Function(v.name + "post", v.index, Unit, v.sort))
    ).isEmpty, "ModelPlex pre and post function symbols do not occur in original formula")

    def conjectureOf(assumptions: Formula, prg: Program): (Formula, List[Formula]) = {
      val boundVars = StaticSemantics.boundVars(prg).symbols
      assert(boundVars.forall(v => !v.isInstanceOf[Variable] || v.isInstanceOf[DifferentialSymbol] || vars.contains(v)),
        "all bound variables " + StaticSemantics.boundVars(prg).prettyString + " must occur in monitor list " + vars.mkString(", ") +
          "\nMissing: " + (StaticSemantics.boundVars(prg).symbols.toSet diff vars.toSet).mkString(", "))
      val posteqs = vars.map(v => Equal(FuncOf(Function(v.name + "post", v.index, Unit, v.sort), Nothing), v)).reduceRight(And)
      //@note suppress assumptions mentioning bound variables
      val nonboundAssumptions = FormulaTools.conjuncts(assumptions).filter(a => boundVars.intersect(StaticSemantics.freeVars(a).symbols).isEmpty)
      (Diamond(prg, posteqs), nonboundAssumptions)
    }

    fml match {
      case Imply(assumptions, Box(prg, _)) => conjectureOf(assumptions, prg)
      case _ => throw new IllegalArgumentException("Unsupported shape of formula " + fml)
    }
  }

  /**
   * Returns a tactic to derive a controller monitor in axiomatic style using forward chase. The tactic is designed to
   * operate on input produced by createMonitorSpecificationConjecture.
    *
    * @see [[createMonitorSpecificationConjecture]]
   * @example{{{
   *        |- xpost()=1
   *        ------------------------------controllerMonitorByChase(1)
   *        |- <{x:=1; {x'=2}}*>xpost()=x
   * }}}
   * In order to produce the result above, the tactic performs intermediate steps as follows.
   * @example{{{
   *        |- xpost()=1
   *        ------------------------------true&
   *        |- (true & xpost()=1)
   *        ------------------------------<:=> assign
   *        |- <x:=1;>(true & xpost()=x)
   *        ------------------------------DX diamond differential skip
   *        |- <x:=1; {x'=2}>xpost()=x
   *        ------------------------------<*> approx
   *        |- <{x:=1; {x'=2}}*>xpost()=x
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
  def modelMonitorByChase(ode: DependentPositionTactic = solveAllIn): DependentPositionTactic = "modelMonitor" by ((pos: Position, seq: Sequent) => chase(3,3, (e:Expression) => e match {
    // remove loops
    case Diamond(Loop(_), _) => "<*> approx" :: Nil
    // keep ODEs, solve later
    case Diamond(ODESystem(_, _), _) => Nil
    case _ => println("Chasing " + e.prettyString); AxiomIndex.axiomsFor(e)
  })(pos) & ode(pos))

  /** Solve all ODEs somewhere underneath pos */
  def solveAllIn: DependentPositionTactic = TacticFactory.anon((pos: Position, sequent: Sequent) => {
    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
      case (Diamond(_: ODESystem, _), pp) => Some(AxiomaticODESolver.axiomaticSolve()(pp))
      case _ => None
    })
    positions.reduceRightOption[BelleExpr](_ & _).getOrElse(skip)
  })

  /** Euler-approximates all ODEs somewhere underneat pos */
  def eulerAllIn: DependentPositionTactic = "ANON" by ((pos: Position, sequent: Sequent) => {
    //@todo evolution domain
    val eulerAxiom = "<{x_'=f(x_)}>p(x_) <-> \\exists t_ (t_>=0 & \\forall e_ (e_>0 -> \\forall h0_ (h0_>0 -> \\exists h_ (0<h_&h_<h0_&<{x_:=x_+h_*f(x_);}*>(t_>=0 & \\exists y_ (abs(x_-y_) < e_ & p(y_))) ))))".asFormula
    //@todo systems as follows?
    //val eulerAxiom = "<{x_'=f(x_),c&q(||)}>p(x_) <-> <{c,x_'=f(x_)&q(||)}>(\\exists t_ (t_>=0 & \\forall e_ (e_>0 -> \\forall h0_ (h0_>0 -> \\exists h_ (0<h_&h_<h0_&<{x_:=x_+h_*f(x);}*>(t_>=0 -> \\exists y_ (abs(x_-y_) < e_ & p(y_)) )))))".asFormula

    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
      case (Diamond(_: ODESystem, _), pp) => Some(useAt(ProvableSig.startProof(eulerAxiom), PosInExpr(0::Nil))(pp))
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
      case (Diamond(_: Assign, _), pp) => Some(chase(pp))
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
    *           |- xpost()>0 & xpost()=xpost()
    *           ------------------------------optimizationOneWithSearch
    *           |- \exists x x>0 & xpost()=x
    * }}}
    * @see[[optimizationOneWithSearchAt]]
    */
  def optimizationOneWithSearch(tool: SimplificationTool, assumptions: List[Formula]): DependentPositionTactic = "Optimization 1 with instance search" by ((pos: Position, sequent: Sequent) => {
    val simplForall1 = proveBy("p(f()) -> \\forall x_ (x_=f() -> p(x_))".asFormula, implyR(1) & allR(1) & implyR(1) & eqL2R(-2)(1) & close)
    val simplForall2 = proveBy("p(f()) -> \\forall x_ (f()=x_ -> p(x_))".asFormula, implyR(1) & allR(1) & implyR(1) & eqR2L(-2)(1) & close)

    def solutionQE(existsFml: Formula, qeFml: Formula, signature: Set[Function], assumptions: List[Formula]) = "ANON" by ((pp: Position, seq: Sequent) => {
      val simplified = tool.simplify(qeFml, assumptions)
      val backSubst = signature.foldLeft[Formula](simplified)((fml, t) => fml.replaceAll(Variable(t.name, t.index), FuncOf(t, Nothing)))
      val pqe = proveBy(Imply(backSubst, existsFml), QE)
      cutAt(backSubst)(pp) < (skip, (if (pp.isSucc) cohideR(pp.topLevel) else cohideR('Rlast)) & CMon(pp.inExpr) & by(pqe))
    })

    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
        case (Forall(xs, Imply(Equal(x, _), _)), pp) if pp.isSucc && xs.contains(x) => Some(useAt(simplForall1, PosInExpr(1::Nil))(pp))
        case (Forall(xs, Imply(Equal(_, x), _)), pp) if pp.isSucc && xs.contains(x) => Some(useAt(simplForall2, PosInExpr(1::Nil))(pp))
        // @note shape of ode solution
        case (ode@Exists(ts, And(GreaterEqual(_, _), And(Forall(ss, Imply(And(_, _), _)), _))), pp) if pp.isSucc && ts.contains("t_".asVariable) && ss.contains("s_".asVariable)=>
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
      case Some(Exists(vars, phi)) if pos.isSucc =>
          var equality: Option[(Variable, Term)] = None
          ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
            override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
              case Equal(l, r) if vars.contains(l) => equality = Some(l.asInstanceOf[Variable], r); Left(Some(ExpressionTraversal.stop))
              case Equal(l, r) if vars.contains(r) => equality = Some(r.asInstanceOf[Variable], l); Left(Some(ExpressionTraversal.stop))
              case _ => Left(None)
            }
          }, phi)
          debug("Running optimization 1 at " + pos + " using equality " + equality) & optimizationOneAt(equality)(pos)
    }
  })


  /**
   * Opt. 1 from Mitsch, Platzer: ModelPlex, i.e., instantiates an existential quantifier with a post-variable. Since
   * the tactic may be used in intermediate steps of ModelPlex, it uses fresh variants of the post-variable for
   * instantiation, if asked to automatically instantiate.
    *
    * @example{{{
   *           |- z>0 & xpost()=z
   *           -----------------------------------optimizationOne(Some(Variable("x"), Variable("z")))
   *           |- \exists x (x>0 & xpost()=x)
   * }}}
   * @example{{{
   *           |- xpost_0()>0 & xpost()=xpost_0()
   *           -----------------------------------optimizationOne(None)
   *           |- \exists x (x>0 & xpost()=x)
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
            val (v, post) = vars.map(v => (v, Function(s"${v.name.replaceAllLiterally("_", "")}post", Some(0), Unit, v.sort))).head
            val postFn = FuncOf(post, Nothing)
            existsR(v, postFn)(pos)
        }
        case Some(Forall(vars, phi)) if pos.isAnte => inst match {
          case Some(i) => allL(i._1, i._2)(pos)
          case None =>
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, Function(s"${v.name.replaceAllLiterally("_", "")}post", Some(0), Unit, v.sort))).head
            val postFn = FuncOf(post, Nothing)
            allL(v, postFn)(pos)
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
