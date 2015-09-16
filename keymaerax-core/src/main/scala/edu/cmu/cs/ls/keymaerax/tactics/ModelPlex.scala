/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal, TraverseToPosition}
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl.localQuantifierElimination
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ConstructionTactic, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.instantiateT
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.diffIntroduceConstantT
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{onBranch,locateAnte,locateSucc}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT,cutT,hideT}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper.isFormula
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{NilT,NilPT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tools.Tool
import scala.collection.immutable
import scala.compat.Platform
import scala.language.postfixOps

/**
 * ModelPlex: Verified runtime validation of verified cyber-physical system models.
 * Created by smitsch on 3/6/15.
 * @author Stefan Mitsch
 * @author Andre Platzer
 * @see "Stefan Mitsch and André Platzer. ModelPlex: Verified runtime validation of verified cyber-physical system models.
In Borzoo Bonakdarpour and Scott A. Smolka, editors, Runtime Verification - 5th International Conference, RV 2014, Toronto, ON, Canada, September 22-25, 2014. Proceedings, volume 8734 of LNCS, pages 199-214. Springer, 2014."
 */
object ModelPlex extends ((List[Variable], Symbol) => (Formula => Formula)) {

  /**
   * Synthesize the ModelPlex (Controller) Monitor for the given formula for monitoring the given variable.
   */
  def apply(formula: Formula, kind: Symbol, checkProvable: Boolean = true): Formula = formula match {
    case Imply(assumptions, Box(Loop(Compose(controller, ODESystem(_, _))), _)) =>
      //@todo explicitly address DifferentialSymbol instead of exception
      val vars = StaticSemantics.boundVars(controller).toSymbolSet.map((x:NamedSymbol)=>x.asInstanceOf[Variable]).toList
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
   @ param kind The kind of monitor, either 'ctrl or 'model.
   * @param checkProvable true to check the Provable proof certificates (recommended).
   */
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Boolean): (Formula => Formula) = formula => {
    require(kind == 'ctrl || kind == 'model, "Unknown monitor kind " + kind + ", expected one of 'ctrl or 'model")
    val mxInputFml = createMonitorSpecificationConjecture(formula/*, vars*/)
    val mxInputSequent = Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(mxInputFml))
    val tactic = kind match {
      case 'ctrl => locateSucc(modelplexAxiomaticStyle(useOptOne=true)(controllerMonitorT))
      case 'model => locateSucc(modelplexAxiomaticStyle(useOptOne=true)(modelMonitorT))
      case _ => throw new IllegalArgumentException("Unknown monitor kind " + kind + ", expected one of 'ctrl or 'model")
    }

    val proofStart = Platform.currentTime
    val rootNode = new RootNode(mxInputSequent)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))
    val proofDuration = Platform.currentTime - proofStart
    Console.println("[proof time " + proofDuration + "ms]")

    assert(rootNode.openGoals().size == 1 && rootNode.openGoals().head.sequent.ante.size == 1 &&
      rootNode.openGoals().head.sequent.succ.size == 1, "ModelPlex tactic expected to provide a single formula (in place version)")
    assert(rootNode.sequent == mxInputSequent, "Proof was a proof of the ModelPlex specification")
    // @todo conjunction with phi|_cnst when monitor should also check the conditions on constants
    val mxOutputProofTree = rootNode.openGoals().head.sequent.succ.head
    if (checkProvable) {
      val witnessStart= Platform.currentTime
      val provable = rootNode.provableWitness
      assert(provable.subgoals.size == 1 && provable.subgoals.head.ante.size == 1 &&
        provable.subgoals.head.succ.size == 1, "ModelPlex tactic expected to provide a single formula (in place version)")
      assert(provable.conclusion == mxInputSequent, "Provable is a proof of the ModelPlex specification")
      assert(provable.subgoals.head.ante.head == True)
      val mxOutput = provable.subgoals.head.succ.head
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
   * @param fml A formula of the form p -> [a]q, which was proven correct.
   * @param vars A list of variables V, superset of BV(a).
   * @see Mitsch, Platzer: ModelPlex (Definition 3, Lemma 4, Corollary 1).
   */
  def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): Formula = {
    require(vars.nonEmpty, "ModelPlex expects non-empty list of variables to monitor")
    val varsSet = vars.toSet
    require(StaticSemantics.symbols(fml).intersect(
      vars.toSet[Variable].map(v=>Function(v.name + "pre", v.index, Unit, v.sort).asInstanceOf[NamedSymbol]) ++
        vars.toSet[Variable].map(v=>Function(v.name + "post", v.index, Unit, v.sort))
    ).isEmpty, "ModelPlex pre and post function symbols do not occur in original formula")
    fml match {
      case Imply(assumptions, Box(prg, _)) =>
        assert(StaticSemantics.boundVars(prg).toSymbolSet.forall(v => !v.isInstanceOf[Variable] || vars.contains(v.asInstanceOf[Variable])),
          "all bound variables " + StaticSemantics.boundVars(prg).prettyString + " must occur in monitor list " + vars.mkString(", ") +
            "\nMissing: " + (StaticSemantics.boundVars(prg).toSymbolSet.toSet diff vars.toSet).mkString(", "))
        val posteqs = vars.map(v => Equal(FuncOf(Function(v.name + "post", v.index, Unit, v.sort), Nothing), v)).reduce(And)
        //@note suppress assumptions since at most those without bound variables are still around.
        //@todo remove implication
        Imply(True, Diamond(prg, posteqs))
      case _ => throw new IllegalArgumentException("Unsupported shape of formula " + fml)
    }
  }

  /**
   * Returns a tactic to derive a controller monitor in axiomatic style using forward chase. The tactic is designed to
   * operate on input produced by createMonitorSpecificationConjecture.
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
  def controllerMonitorByChase: PositionTactic = chase(3,3, e => e match {
    // no equational assignments
    case Box(Assign(_,_),_) => "[:=] assign" :: "[:=] assign update" :: Nil
    case Diamond(Assign(_,_),_) => "<:=> assign" :: "<:=> assign update" :: Nil
    // remove loops
    case Diamond(Loop(_), _) => "<*> approx" :: Nil
    // remove ODEs for controller monitor
    case Diamond(ODESystem(_, _), _) => "DX diamond differential skip" :: Nil
    case _ => AxiomIndex.axiomsFor(e)
  })

  /**
   * ModelPlex sequent-style synthesis technique, i.e., with branching so that the tactic can operate on top-level
   * operators. Operates on monitor specification conjectures.
   * @see[[createMonitorSpecificationConjecture]]
   * @return The tactic.
   */
  def modelplexSequentStyle: PositionTactic = new PositionTactic("Modelplex Sequent-Style") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.top) match {
      case Imply(_, Diamond(_, _)) => true
      case _ => false
    }

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(ImplyRightT(p) & ((AxiomCloseT |
            (debugT("Before HP") &
            (locateSucc(diamondSeqT) | locateSucc(diamondChoiceT) | locateSucc(diamondNDetAssign) |
             locateSucc(diamondTestRetainConditionT) | locateSucc(diamondAssignEqualT) |
             locateSucc(substitutionDiamondAssignT) | locateSucc(v2vAssignT) |
             locateSucc(diamondDiffSolve2DT)) &
            debugT("After  HP") &
            ((locateSucc(mxPropositionalRightT) | locateSucc(optimizationOneAt()) | locateAnte(PropositionalLeftT) |
              locateAnte(optimizationOneAt()))*)
            )
          )*)
        )
      }
    }
  }

  /**
   * ModelPlex backward proof tactic for axiomatic-style monitor synthesis, i.e., avoids proof branching as occuring in
   * the sequent-style synthesis technique. The tactic 'unprog' determines what kind of monitor (controller monitor,
   * model monitor) to synthesize. Operates on monitor specification conjectures.
   * @param useOptOne Indicates whether or not to use Opt. 1 at intermediate steps.
   * @param unprog A tactic for a specific monitor type (either controller monitor or model monitor).
   * @see [[createMonitorSpecificationConjecture]]
   * @see [[controllerMonitorT]]
   * @see [[modelMonitorT]]
   */
  def modelplexAxiomaticStyle(useOptOne: Boolean)
                             (unprog: Boolean => PositionTactic): PositionTactic = new PositionTactic("Modelplex In-Place") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.top).subFormulaAt(p.inExpr) match {
      case Some(Imply(_, Diamond(_, _))) => true
      case _ => false
    }

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(ImplyRightT(p) & ((debugT("Before HP") & unprog(useOptOne)(p) & debugT("After  HP"))*) &
          debugT("Done with transformation, now looking for quantifiers") &
          (atOutermostQuantifier(TacticLibrary.debugAtT("Local quantifier elimination") & localQuantifierElimination)(p) | NilT) &
          debugT("Modelplex done")
        )
      }
    }
  }

  /**
   * Returns a backward tactic for deriving controller monitors. Uses Opt. 1 immediately after nondeterministic
   * assignments if useOptOne, avoids Opt. 1 at intermediate steps if !useOptOne.
   * @param useOptOne Indicates whether or not to use Opt. 1 at intermediate steps.
   * @return The tactic.
   */
  def controllerMonitorT(useOptOne: Boolean): PositionTactic =
    locateT(
      TactixLibrary.useAt("<*> approx", PosInExpr(1::Nil)) ::
      diamondSeqT ::
      TactixLibrary.useAt("DX diamond differential skip", PosInExpr(1::Nil)) :: Nil) &
    locateT(
      TactixLibrary.useAt("<*> approx", PosInExpr(1::Nil)) ::
      TactixLibrary.useAt("DX diamond differential skip", PosInExpr(1::Nil)) ::
      diamondSeqT ::
      diamondChoiceT ::
      (diamondNDetAssign & (if (useOptOne) optimizationOne() else NilPT)) ::
      diamondTestT ::
      substitutionDiamondAssignT ::
      v2vAssignT ::
      (diamondAssignEqualT & (if (useOptOne) optimizationOne() else NilPT)) ::
      (diamondDiffSolve2DT & (if (useOptOne) optimizationOne() else NilPT)) ::
      boxAssignBaseT ::
      Nil)

  /**
   * Returns a backward tactic for deriving model monitors. Uses Opt. 1 immediately after nondeterministic
   * assignments if useOptOne, avoids Opt. 1 at intermediate steps if !useOptOne.
   * @param useOptOne Indicates whether or not to use Opt. 1 at intermediate steps.
   * @return The tactic.
   */
  def modelMonitorT(useOptOne: Boolean): PositionTactic =
    locateT(diamondSeqT :: TactixLibrary.useAt("<*> approx", PosInExpr(1::Nil)) :: Nil) &
    locateT(
      TactixLibrary.useAt("<*> approx", PosInExpr(1::Nil)) ::
      diamondSeqT ::
      diamondChoiceT ::
      (diamondNDetAssign & (if (useOptOne) optimizationOne() else NilPT)) ::
      diamondTestT ::
      substitutionDiamondAssignT ::
      v2vAssignT ::
      (diamondAssignEqualT & (if (useOptOne) optimizationOne() else NilPT)) ::
      (diamondDiffSolve2DT & (if (useOptOne) optimizationOne() else NilPT)) ::
      boxAssignBaseT ::
      Nil)

  /** Propositional tactic that avoids branching in formulas without modalities. */
  private def mxPropositionalRightT = new PositionTactic("Modelplex Propositional Right") {
    override def applies(s: Sequent, p: Position): Boolean = {
      var containsPrg = false
      s(p.top) match {
        // only apply to formulas that contain programs
        case f: Formula => ExpressionTraversal.traverse(new ExpressionTraversalFunction {
          override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = {
            containsPrg = true
            Left(Some(ExpressionTraversal.stop))
          }
        }, f)
        case _ => // nothing to do
      }
      containsPrg && PropositionalRightT.applies(s, p)
    }

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = Some(PropositionalRightT(p))
    }
  }

  /** Performs tactic t at the outermost quantifier underneath position p, if any. */
  private def atOutermostQuantifier(t: PositionTactic): PositionTactic = new PositionTactic("ModelPlex at outermost quantifier") {
    override def applies(s: Sequent, p: Position): Boolean = positionOfOutermostQuantifier(s, p).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        positionOfOutermostQuantifier(node.sequent, p) match {
          case Some(pos) => Some(t(pos))
          case None => None
        }
      }
    }
  }

  /**
   * Returns a tactic to solve two-dimensional differential equations. Introduces constant function symbols for
   * variables that do not change in the ODE, before it hands over to the actual diff. solution tactic.
   * @return The tactic.
   * @see[[ODETactics.diamondDiffSolve2DT]]
   */
  def diamondDiffSolve2DT: PositionTactic = new PositionTactic("<','> differential solution") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.top).subFormulaAt(p.inExpr) match {
      case Some(Diamond(ODESystem(DifferentialProduct(
        AtomicODE(DifferentialSymbol(_), _),
        AtomicODE(DifferentialSymbol(_), _)), _), _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = (diffIntroduceConstantT & ODETactics.diamondDiffSolve2DT)(p)
  }

  /**
   * Returns a modified test tactic for axiom <?H>p <-> H & (H->p)
   * @example{{{
   *          |- x>0 & (x>0 -> [x'=x]x>0)
   *          ---------------------------diamondTestRetainCondition
   *          |- <?x>0>[x'=x]x>0
   * }}}
   * @return The tactic.
   * @note Unused so far, for deriving prediction monitors where DI is going to rely on knowledge from prior tests.
   */
  def diamondTestRetainConditionT: PositionTactic = new PositionTactic("<?H> modelplex test") {
    //@todo introduce a derived axiom
    override def applies(s: Sequent, p: Position): Boolean = s(p.top).subFormulaAt(p.inExpr) match {
      case Some(Diamond(Test(_), _)) => true
      case _ => false
    }

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def constructCut(f: Formula) = ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
          case Diamond(Test(h), phi) => Right(And(h, Imply(h, phi)))
          case _ => Left(Some(ExpressionTraversal.stop))
        }
      }), f)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        node.sequent(p.top).subFormulaAt(p.inExpr) match {
          case Some(Diamond(Test(h), phi)) =>
            Some(
              diamondTestT(p) &
                cutT(constructCut(node.sequent(p))) & onBranch(
                  (cutUseLbl, debugT("use cut") & ((AxiomCloseT | locateAnte(PropositionalLeftT) | locateSucc(PropositionalRightT))*)
                    & debugT("Modelplex: Expected axiom close, but did not close")),
                  (cutShowLbl, debugT("show cut") & hideT(p.topLevel))
              )
            )
        }
      }
    }
  }

  /**
   * Performs a tactic from the list of tactics that is applicable somewhere underneath position p in sequent s,
   * taking the outermost such sub-position of p.
   * @example{{{
   *           |- a=1 & (<x:=2;>x+y>0 & <y:=3;>x+y>0)
   *           ---------------------------------------locateT(diamondSeqT :: diamondChoiceT :: Nil)(1)
   *           |- a=1 & <x:=2; ++ y:=3;>x+y>0
   * }}}
   * @param tactics The list of tactics.
   * @return The tactic.
   * @see[[locate]]
   */
  def locateT(tactics: List[PositionTactic]): PositionTactic = new PositionTactic("Modelplex Locate") {
    override def applies(s: Sequent, p: Position): Boolean = locate(tactics, s, p) != NilT

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(locate(tactics, node.sequent, p))
      }
    }
  }

  /**
   * Returns a tactic from the list of tactics ts that is applicable somewhere underneath position p in sequent s,
   * taking the outermost such sub-position of p.
   * @param ts The list of tactics.
   * @param s The sequent.
   * @param p The position.
   * @return The found tactic, pointed to the outermost sub-position of p where it is applicable.
   */
  private def locate(ts: List[PositionTactic], s: Sequent, p: Position): Tactic = {
    var outerMostPos = p
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = {
        val subP = if (p.isAnte) new AntePosition(p.index, pos) else new SuccPosition(p.index, pos)
        if (ts.exists(_.applies(s, subP))) {
          outerMostPos = subP
          Left(Some(ExpressionTraversal.stop))
        } else Left(None)
      }
    }, s(p.top).subFormulaAt(p.inExpr).getOrElse(throw new IllegalArgumentException("Sequent " + s(p) + " is not a formula at " + p.inExpr)))
    println(s"Looking for tactic at $outerMostPos: ${s(outerMostPos).subFormulaAt(outerMostPos.inExpr)}")
    ts.find(_.applies(s, outerMostPos)) match {
      case Some(t) => println(s"Applying ${t.name} at $outerMostPos"); t(outerMostPos)
      case _ => NilT
    }
  }

  /** Returns the position of the outermost universal quantifier underneath position p in sequent s, if any. None otherwise. */
  private def positionOfOutermostQuantifier(s: Sequent, p: Position): Option[Position] = {
    var outermostPos: Option[Position] = None
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
        case Forall(_, _) =>
          outermostPos = Some(if (p.isAnte) new AntePosition(p.index, pos) else new SuccPosition(p.index, pos))
          Left(Some(ExpressionTraversal.stop))
        case _ => Left(None)
      }
    }, s(p.top).subFormulaAt(p.inExpr).getOrElse(throw new IllegalArgumentException("Formula " + s(p) + " is not a formula at sub-position " + p.inExpr)))
    outermostPos
  }

  /** Opt. 1 from Mitsch, Platzer: ModelPlex, i.e., instantiates existential quantifiers with an equal term phrased
    * somewhere in the quantified formula.
    * @example{{{
    *           |- xpost()>0 & xpost()=xpost()
    *           ------------------------------optimizationOneWithSearch
    *           |- \exists x x>0 & xpost()=x
    * }}}
    * @see[[optimizationOneWithSearchAt]]
    */
  def optimizationOneWithSearch: PositionTactic = locateT(optimizationOneWithSearchAt::Nil)

  /** Opt. 1 at a specific position, i.e., instantiates the existential quantifier with an equal term phrased
    * somewhere in the quantified formula. */
  private def optimizationOneWithSearchAt: PositionTactic = new PositionTactic("Optimization 1 with instance search") {
    override def applies(s: Sequent, p: Position): Boolean = isFormula(s, p) && (s(p.top).subFormulaAt(p.inExpr) match {
      case Some(Exists(vars, _)) => !p.isAnte && vars.size == 1
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.top).subFormulaAt(p.inExpr) match {
        case Some(Exists(vars, phi)) if !p.isAnte =>
          var equality: Option[(Variable, Term)] = None
          ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
            override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
              case Equal(l, r) if vars.contains(l) => equality = Some(l.asInstanceOf[Variable], r); Left(Some(ExpressionTraversal.stop))
              case Equal(l, r) if vars.contains(r) => equality = Some(r.asInstanceOf[Variable], l); Left(Some(ExpressionTraversal.stop))
              case _ => Left(None)
            }
          }, phi)
          Some(optimizationOneAt(equality)(p))
      }
    }
  }

  /**
   * Opt. 1 from Mitsch, Platzer: ModelPlex, i.e., instantiates an existential quantifier with a post-variable. Since
   * the tactic may be used in intermediate steps of ModelPlex, it uses fresh variants of the post-variable for
   * instantiation, if asked to automatically instantiate.
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
  def optimizationOne(inst: Option[(Variable, Term)] = None): PositionTactic = locateT(optimizationOneAt(inst)::Nil)

  /** Opt. 1 at a specific position */
  private def optimizationOneAt(inst: Option[(Variable, Term)] = None): PositionTactic = new PositionTactic("Optimization 1") {
    override def applies(s: Sequent, p: Position): Boolean = isFormula(s, p) && (s(p.top).subFormulaAt(p.inExpr) match {
      case Some(Exists(vars, _)) => !p.isAnte && vars.size == 1
      case Some(Forall(vars, _)) => p.isAnte && vars.size == 1
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.top).subFormulaAt(p.inExpr) match {
        case Some(Exists(vars, phi)) if !p.isAnte => inst match {
          case Some(i) => Some(instantiateT(i._1, i._2)(p))
          case None =>
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, Function(s"${v.name}post", Some(0), Unit, v.sort))).head
            val postFn = FuncOf(post, Nothing)
            Some(instantiateT(v, postFn)(p))
        }
        case Some(Forall(vars, phi)) if p.isAnte => inst match {
          case Some(i) => Some(instantiateT(i._1, i._2)(p))
          case None =>
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, Function(s"${v.name}post", Some(0), Unit, v.sort))).head
            val postFn = FuncOf(post, Nothing)
            Some(instantiateT(v, postFn)(p))
        }
      }
    }
  }
}
