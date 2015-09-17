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
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.{diamondDiffSolve2DT, diffIntroduceConstantT}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{onBranch,locateAnte,locateSucc}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT,cutT,hideT}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper.{getFormula,isFormula}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{NilT,NilPT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tools.Tool
import scala.collection.immutable
import scala.collection.mutable
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
    val mxInputFml = modelplexControllerMonitorTrafo(formula/*, vars*/)
    val mxInputSequent = Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(mxInputFml))
    val tactic = kind match {
      case 'ctrl => locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
      case 'model => locateSucc(modelplexInPlace(useOptOne=true)(modelMonitorT))
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

  /** Construct ModelPlex Controller Monitor specification formula corresponding to given formula. */
  def modelplexControllerMonitorTrafo(fml: Formula, vars: Variable*): Formula = {
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
   * Returns a tactic to derive a controller monitor using chase. The tactic is designed to operate on input produced
   * by modelPlexControllerMonitorTrafo.
   * @see [[modelplexControllerMonitorTrafo]]
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
   * @return The position tactic.
   */
  def controllerMonitorByChase: PositionTactic = chase(3,3, (e:Expression) => e match {
    // no equational assignments
    case Box(Assign(_,_),_) => "[:=] assign" :: "[:=] assign update" :: Nil
    case Diamond(Assign(_,_),_) => "<:=> assign" :: "<:=> assign update" :: Nil
    // remove loops
    case Diamond(Loop(_), _) => "<*> approx" :: Nil
    // remove ODEs for controller monitor
    case Diamond(ODESystem(_, _), _) => "DX diamond differential skip" :: Nil
    case _ => AxiomIndex.axiomsFor(e)
  })

  /** @todo document */
  def modelplex = new PositionTactic("Modelplex") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      // TODO generate from phi -> [alpha*]psi
      case Imply(_, Diamond(_, _)) => true
      case _ => false
    }

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(ImplyRightT(p) & ((AxiomCloseT |
            (debugT("Before HP") &
            (locateSucc(diamondSeqT) | locateSucc(diamondChoiceT) | locateSucc(diamondNDetAssign) |
             locateSucc(diamondModelplexTestT) | locateSucc(diamondAssignEqualT) |
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

  private def mxPropositionalRightT = new PositionTactic("Modelplex Propositional Right") {
    override def applies(s: Sequent, p: Position): Boolean = {
      var containsPrg = false
      s(p) match {
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

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(PropositionalRightT(p))
      }
    }
  }

  /** ModelPlex proof tactic for monitor synthesis (in-place version) */
  def modelplexInPlace(useOptOne: Boolean, time: Option[Variable] = None)
                      (unprog: (Boolean, Option[Variable]) => PositionTactic) = new PositionTactic("Modelplex In-Place") {
    override def applies(s: Sequent, p: Position): Boolean = s(p).subFormulaAt(p.inExpr) match {
      case Some(Imply(_, Diamond(_, _))) => true
      case _ => false
    }

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(ImplyRightT(p) & ((debugT("Before HP") & unprog(useOptOne, time)(p) & debugT("After  HP"))*) &
          debugT("Done with transformation, now looking for quantifiers") &
          (atOutermostQuantifier(TacticLibrary.debugAtT("Local quantifier elimination") & localQuantifierElimination)(p) | NilT) &
          debugT("Modelplex done")
        )
      }
    }
  }

  def controllerMonitorT(useOptOne: Boolean, time: Option[Variable]): PositionTactic = locateT(
    TactixLibrary.useAt("<*> approx", PosInExpr(1::Nil)) ::
    TactixLibrary.useAt("DX diamond differential skip", PosInExpr(1::Nil)) ::
    diamondSeqT ::
    diamondChoiceT ::
    (diamondNDetAssign & (if (useOptOne) optimizationOne() else NilPT)) ::
    diamondTestT ::
    substitutionDiamondAssignT ::
    v2vAssignT ::
    (diamondAssignEqualT & (if (useOptOne) optimizationOne() else NilPT)) ::
    (mxDiamondDiffSolve2DT & (if (useOptOne) optimizationOne() else NilPT)) ::
    boxAssignBaseT ::
    Nil)

  def modelMonitorT(useOptOne: Boolean, time: Option[Variable]): PositionTactic = locateT(
    TactixLibrary.useAt("<*> approx", PosInExpr(1::Nil)) ::
    diamondSeqT ::
    diamondChoiceT ::
    (diamondNDetAssign & (if (useOptOne) optimizationOne() else NilPT)) ::
    diamondTestT ::
    substitutionDiamondAssignT ::
    v2vAssignT ::
    (diamondAssignEqualT & (if (useOptOne) optimizationOne() else NilPT)) ::
    (mxDiamondDiffSolve2DT & (if (useOptOne) optimizationOne() else NilPT)) ::
    boxAssignBaseT ::
    Nil)

  def mxDiamondDiffSolve2DT: PositionTactic = new PositionTactic("<','> differential solution") {
    override def applies(s: Sequent, p: Position): Boolean = s(p).subFormulaAt(p.inExpr) match {
      case Some(Diamond(ODESystem(DifferentialProduct(
      AtomicODE(DifferentialSymbol(_), _),
      AtomicODE(DifferentialSymbol(_), _)), _), _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = (diffIntroduceConstantT & diamondDiffSolve2DT)(p)
  }

  def locateT(tactics: List[PositionTactic]): PositionTactic = new PositionTactic("Modelplex Locate") {
    override def applies(s: Sequent, p: Position): Boolean = locate(tactics, s, p) != NilT

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(locate(tactics, node.sequent, p))
      }
    }
  }

  private def atOutermostQuantifier(t: PositionTactic) = new PositionTactic("ModelPlex at outermost quantifier") {
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
   * Returns a modified test tactic < ?H>p <-> H & (H->p)
   * @return The new tactic.
   */
  def diamondModelplexTestT = new PositionTactic("<?H> modelplex test") {
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case Diamond(Test(_), _) => true
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
        getFormula(node.sequent, p) match {
          case Diamond(Test(h), phi) =>
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
   * Locates the tactic that is applicable at the outermost sub-position of p.
   * @param ts The list of tactics.
   * @param s The sequent.
   * @param p The position.
   * @return The found tactic.
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
    }, getFormula(s, p))
    println(s"Looking for tactic at $outerMostPos: ${getFormula(s, outerMostPos)}")
    ts.find(_.applies(s, outerMostPos)) match {
      case Some(t) => println(s"Applying ${t.name} at $outerMostPos"); t(outerMostPos)
      case _ => NilT
    }
  }

  private def positionOfOutermostQuantifier(s: Sequent, p: Position): Option[Position] = {
    var outermostPos: Option[Position] = None
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
        case Forall(_, _) =>
          outermostPos = Some(if (p.isAnte) new AntePosition(p.index, pos) else new SuccPosition(p.index, pos))
          Left(Some(ExpressionTraversal.stop))
        case _ => Left(None)
      }
    }, getFormula(s, p))
    outermostPos
  }

  def optimizationOneWithSearch = locateT(optimizationOneWithSearchAt::Nil)

  def optimizationOneWithSearchAt = new PositionTactic("Optimization 1 with instance search") {
    override def applies(s: Sequent, p: Position): Boolean = isFormula(s, p) && (s(p).subFormulaAt(p.inExpr) match {
      case Some(Exists(vars, _)) => !p.isAnte && vars.size == 1
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p).subFormulaAt(p.inExpr) match {
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

  def optimizationOne(inst: Option[(Variable, Term)] = None) = locateT(optimizationOneAt(inst)::Nil)

  def optimizationOneAt(inst: Option[(Variable, Term)] = None) = new PositionTactic("Optimization 1") {
    override def applies(s: Sequent, p: Position): Boolean = isFormula(s, p) && (s(p).subFormulaAt(p.inExpr) match {
      case Some(Exists(vars, _)) => !p.isAnte && vars.size == 1
      case Some(Forall(vars, _)) => p.isAnte && vars.size == 1
      case _ => false
    })

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p).subFormulaAt(p.inExpr) match {
        case Some(Exists(vars, phi)) if !p.isAnte => inst match {
          case Some(i) => Some(instantiateT(i._1, i._2)(p))
          case None => //Some(instantiateT(p))
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, Function(s"${v.name}post", Some(0), Unit, v.sort))).head
            val postFn = FuncOf(post, Nothing)
            Some(instantiateT(v, postFn)(p))
        }
        case Some(Forall(vars, phi)) if p.isAnte => inst match {
          case Some(i) => Some(instantiateT(i._1, i._2)(p))
          case None => //Some(instantiateT(p))
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, Function(s"${v.name}post", Some(0), Unit, v.sort))).head
            val postFn = FuncOf(post, Nothing)
            Some(instantiateT(v, postFn)(p))
        }
      }
    }
  }

  private def substFromTemp(postTempFn: Term, postFn: Term) = new PositionTactic("Modelplex Subst from Temp") {
    override def applies(s: Sequent, p: Position): Boolean = true

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val f = getFormula(node.sequent, p)
        val substFromTemp = SubstitutionPair(postFn, postTempFn) :: Nil
        val concFromTemp = SubstitutionHelper.replaceFree(f)(postTempFn, postFn)
        Some(uniformSubstT(substFromTemp, Map(f -> concFromTemp)))
      }
    }
  }
}
