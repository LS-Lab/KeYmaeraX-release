/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.mapSubpositions
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.btactics.TacticHelper.timed
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.{Atom, OneOf, QETacticTool, SimplificationTool}
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.btactics.macros.{AxiomInfo, Tactic}
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, TacticReservedSymbols}

import scala.collection.immutable.{List, ListMap, Nil}
import scala.collection.mutable.ListBuffer
import scala.collection.{immutable, mutable}
import scala.compat.Platform

/**
 * ModelPlex: Verified runtime validation of verified cyber-physical system models.
  *
  * @author Stefan Mitsch
 * @author Andre Platzer
 * @see Stefan Mitsch and André Platzer. [[https://doi.org/10.1007/s10703-016-0241-z ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *      Formal Methods in System Design, 42 pp. 2016. Special issue for selected papers from RV'14.
 * @see Stefan Mitsch and André Platzer. [[https://doi.org/10.1007/978-3-319-11164-3_17 ModelPlex: Verified runtime validation of verified cyber-physical system models]].
 *      In Borzoo Bonakdarpour and Scott A. Smolka, editors, Runtime Verification - 5th International Conference, RV 2014, Toronto, ON, Canada, September 22-25, 2014. Proceedings, volume 8734 of LNCS, pages 199-214. Springer, 2014.
 */
object ModelPlex extends ModelPlexTrait with Logging {
  private val NAMESPACE = "modelplex"

  // supporting-lemmas
  lazy val simplForall1: Lemma = AnonymousLemmas.remember("p(f()) -> \\forall x_ (x_=f() -> p(x_))".asFormula, implyR(1) & allR(1) & implyR(1) & eqL2R(-2)(1) & close, NAMESPACE)
  lazy val simplForall2: Lemma = AnonymousLemmas.remember("p(f()) -> \\forall x_ (f()=x_ -> p(x_))".asFormula, implyR(1) & allR(1) & implyR(1) & eqR2L(-2)(1) & close, NAMESPACE)

  /**
   * Synthesize the ModelPlex (Controller) Monitor for the given formula for monitoring the given variable.
   */
  def apply(formula: Formula, kind: Symbol, checkProvable: Option[ProvableSig => Unit] = Some(_ => ()),
            unobservable: ListMap[_ <: NamedSymbol, Option[Formula]] = ListMap.empty): Formula = {
    val vars = StaticSemantics.boundVars(formula).symbols.filter(v => v.isInstanceOf[Variable] && !v.isInstanceOf[DifferentialSymbol]).map((x:NamedSymbol)=>x.asInstanceOf[Variable]).toList
    val sortedVars = vars.sortWith((x,y)=>x<y)
    apply(sortedVars, kind, checkProvable)(formula)
  }

  /**
   * Synthesize the ModelPlex (Controller) Monitor for the given formula for monitoring the given variable.
    * @ param kind The kind of monitor, either 'ctrl or 'model.
    *
    * @param checkProvable true to check the Provable proof certificates (recommended).
   */
  def apply(vars: List[Variable], kind: Symbol, checkProvable: Option[ProvableSig => Unit]): Formula => Formula = formula => {
    require(kind == 'ctrl || kind == 'model, "Unknown monitor kind " + kind + ", expected one of 'ctrl or 'model")
    val ModelPlexConjecture(_, mxInputFml, assumptions) = createMonitorSpecificationConjecture(formula, vars, ListMap.empty)
    val mxInputSequent = Sequent(immutable.IndexedSeq[Formula](), immutable.IndexedSeq(mxInputFml))
    //@note SimplifierV2 disabled as precaution in case Z3 cannot prove one of its lemmas
    val tactic = (kind, ToolProvider.simplifierTool()) match {
      case ('ctrl, tool) => controllerMonitorByChase(1) & SaturateTactic(optimizationOneWithSearch(tool, assumptions, Nil, Some(mxSimplify))(1)) &
        (if (tool.isDefined) SimplifierV2.simpTac(1) else skip)
      case ('model, tool) => modelMonitorByChase(1) & SaturateTactic(optimizationOneWithSearch(tool, assumptions, Nil, Some(mxSimplify))(1)) &
        (if (tool.isDefined) SimplifierV2.simpTac(1) else skip)
      case _ => throw new IllegalArgumentException("Unknown monitor kind " + kind + ", expected one of 'ctrl or 'model; both require a simplification tool")
    }

    val proofStart = Platform.currentTime
    val result = TactixLibrary.proveBy(ProvableSig.startPlainProof(mxInputSequent), tactic)
    val proofDuration = Platform.currentTime - proofStart
    logger.info("[proof time " + proofDuration + "ms]")

    assert(result.subgoals.size == 1 && result.subgoals.head.ante.isEmpty &&
      result.subgoals.head.succ.size == 1, "ModelPlex tactic expected to provide a single formula (in place version)")
    assert(result.conclusion == mxInputSequent, "Proof was a proof of the ModelPlex specification")
    // @todo conjunction with phi|_cnst when monitor should also check the conditions on constants
    val mxOutputProofTree = result.subgoals.head.succ.head
    checkProvable match {
      case Some(report) =>
        report(result)
        logger.info("ModelPlex Proof certificate: Produced")
        mxOutputProofTree
      case None =>
        logger.info("ModelPlex Proof certificate: Skipped")
        mxOutputProofTree
    }
  }

  @Tactic(longDisplayName = "ModelPlex Monitor Synthesis")
  def mxSynthesize(kind: String): InputTactic = inputanon {
    kind match {
      case "controller" => controllerMonitorByChase(1)
      case "model" => modelMonitorByChase(1)
      case _ => throw new IllFormedTacticApplicationException("Unknown ModelPlex option '" + kind + "'; please use one of [controller|model]")
    }
  }

  @Tactic(longDisplayName = "ModelPlex Auto-Instantiation")
  def mxAutoInstantiate(assumptions: List[Formula]): InputTactic = inputanon {
    mxAutoInstantiate(assumptions, List.empty, Some(ModelPlex.mxSimplify))
  }

  def mxAutoInstantiate(assumptions: List[Formula], unobservable: List[_ <: NamedSymbol], simplifier: Option[BuiltInPositionTactic]): InputTactic = inputanon {
    TryCatch(SaturateTactic(optimizationOneWithSearch(ToolProvider.simplifierTool(), assumptions, unobservable, simplifier)(1)),
      classOf[Throwable], (_: Throwable) => TactixLibrary.skip)
  }

  @Tactic(longDisplayName = "ModelPlex Monitor Shape Formatting")
  def mxFormatShape(shape: String): InputTactic = inputanon ((seq: Sequent) => shape match {
    case "boolean" => PropositionalTactics.rightAssociate(SuccPos(0))
    case "metricprg" => PropositionalTactics.rightAssociate(SuccPos(0)) & ModelPlex.chaseToTests(combineTests = false)(1)*2
    case "metricfml" => toMetricT(seq.succ.head)
  })

  /** Normalizes formula `f` into the shape A -> [a;]S. */
  def normalizeInputFormula(f: Formula): Formula = {
    proveBy(f, SaturateTactic(TactixLibrary.alphaRule)).subgoals match {
      case IndexedSeq(Sequent(assumptions, alternatives)) =>
        val (boxes, negAssumptions) = alternatives.partition({ case _: Box => true case _ => false })
        require(boxes.size == 1, "Expected a single box property, but got " + boxes.mkString(","))
        Imply((assumptions ++ negAssumptions.map(Not)).reduceRightOption(And).getOrElse(True), boxes.head)
      case _ => throw new IllegalArgumentException("Unsupported shape of formula " + f.prettyString + "; formula must be propositionally equivalent to A -> [prg;]P")
    }
  }

  /** Partitions the unobservable symbols into unobservable state variables and unknown model parameters. */
  def partitionUnobservable(unobservable: ListMap[_ <: NamedSymbol, Option[Formula]]): (ListMap[Variable, Option[Formula]], ListMap[(Function, Variable), Option[Formula]], ListMap[(Function, Variable), Option[Formula]]) = {
    val unobservableStateVars: ListMap[Variable, Option[Formula]] = unobservable.filter(_._1.isInstanceOf[Variable]).
      map({ case (k: Variable, v) => k -> v })
    val unknownParams: ListMap[(Function, Variable), Option[Formula]] = unobservable.filter({ case (Function(_, _, domain, _, _), _) => domain == Unit case _ => false }).
      map({ case (k: Function, v) => (k, Variable(k.name, k.index, k.sort)) -> v })
    val unknownFunctions: ListMap[(Function, Variable), Option[Formula]] = unobservable.filter({ case (Function(_, _, domain, _, _), _) => domain != Unit case _ => false }).
      map({ case (k: Function, v) => (k, Variable(k.name, k.index, k.sort)) -> v })
    (unobservableStateVars, unknownParams, unknownFunctions)
  }

  /**
    * Construct ModelPlex monitor specification conjecture corresponding to given formula.
    *
    * @param fml A formula of the form p -> [a]q, which was proven correct.
    * @param vars A list of variables V, superset of BV(a).
    * @param unobservable Unobservable variables/parameters and their optional estimation (e.g., from a sensor),
    *                     keys subset of vars ++ any fns.
    * @return A tuple of monitor conjecture and assumptions
    * @see Mitsch, Platzer: ModelPlex (Definition 3, Lemma 4, Corollary 1).
    */
  def createMonitorSpecificationConjecture(fml: Formula, vars: List[Variable],
                                           unobservable: ListMap[_ <: NamedSymbol, Option[Formula]],
                                           postVar: Variable=>Variable = NAMED_POST_VAR): ModelPlexConjecture = {
    require(vars.nonEmpty, "ModelPlex expects non-empty list of variables to monitor")
    require(StaticSemantics.symbols(fml).intersect(vars.map(postVar).toSet).isEmpty,
      "ModelPlex post symbols must not occur in original formula")

    val (unobservableStateVars, unknownParams, unknownFunctions) = partitionUnobservable(unobservable)

    def conjectureOf(assumptions: Formula, prg: Program): (Formula, List[Formula]) = {
      val boundVars = StaticSemantics.boundVars(prg).symbols
      assert(boundVars.forall(v => !v.isInstanceOf[Variable] || v.isInstanceOf[DifferentialSymbol] || vars.contains(v)),
        "All bound variables " + StaticSemantics.boundVars(prg).prettyString + " must occur in monitor list " + vars.mkString(", ") +
          "\nMissing: " + (StaticSemantics.boundVars(prg).symbols.filterNot(_.isInstanceOf[DifferentialSymbol]) diff vars.toSet).mkString(", "))

      val unknownFnApps = ListBuffer[FuncOf]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case f@FuncOf(fn, _) =>
            if (unknownFunctions.keySet.map(_._1).contains(fn)) unknownFnApps += f
            Left(None)
          case _ => Left(None)
        }
      }, prg)
      val boundArgsFns = unknownFnApps.filter(fn => StaticSemantics.freeVars(fn).toSet.intersect(boundVars).nonEmpty)
      require(boundArgsFns.isEmpty,
        "Unable to make functions " + boundArgsFns.map(_.prettyString).mkString(",") +
          " unobservable, because their arguments are bound in program; replace manually with non-deterministic assignments (e.g., replace x:=2; y:=f(x) with x:=2; fx:=*; y:=fx)")

      val postEstimators = unobservableStateVars.
        filter(_._2.isDefined).
        map({ case (v, Some(e)) =>
          (StaticSemantics.freeVars(e).toSet - v).toList match {
            case Nil => ???
            case sensorVar :: Nil => v -> e.replaceFree(v, postVar(v)).replaceFree(sensorVar, postVar(sensorVar))
            case s => throw new IllegalArgumentException("Sensor specifications with multiple variables not supported, please use function symbols for uncertainty and other parameters")
          }
        })

      val preEstimator = unobservable.
        filter(_._2.isDefined).
        map({ case (_, Some(e)) => e }).
        reduceRightOption(And).getOrElse(True)

      val postEqs = unobservableStateVars.keys.
        foldRight[Formula](vars.map(v => Equal(postVar(v), v)).reduceRight(And))((v, f) => postEstimators.get(v) match {
          case Some(e) => Exists(postVar(v)::Nil, And(e, f))
          case _ => Exists(postVar(v)::Nil, f)
        })

      val varConjectureBody = if (preEstimator == True) Diamond(prg, postEqs) else And(preEstimator, Diamond(prg, postEqs))
      val varConjecture = unobservableStateVars.foldRight[Formula](varConjectureBody)((v, f) => Exists(v._1::Nil, f))
      val conjecture = (unknownParams ++ unknownFunctions).foldRight[Formula](varConjecture)({ case (((fn, v), _), f) =>
        val args = fn.domain match {
          case Unit  => Nothing
          case d => d.toDots(0)._1
        }
        Exists(v::Nil, USubst(SubstitutionPair(FuncOf(fn, args), v) :: Nil)(f))
       })
      //@note suppress assumptions mentioning bound variables
      val nonboundAssumptions = FormulaTools.conjuncts(assumptions).
        filter(a => boundVars.intersect(StaticSemantics.freeVars(a).symbols).isEmpty).
        filter(a => StaticSemantics.freeVars(a).intersect(unobservableStateVars.keySet).isEmpty)
      (conjecture, nonboundAssumptions)
    }

    normalizeInputFormula(fml) match {
      case f@Imply(init, Box(prg, _)) =>
        val (conjecture, constAssumptions) = conjectureOf(f, prg)
        ModelPlexConjecture(init, conjecture, constAssumptions)
      case _ => throw new IllegalArgumentException("Unsupported shape of formula " + fml.prettyString + "; formula must be propositionally equivalent to A -> [prg;]P")
    }
  }

  /**
    * Construct ModelPlex monitor specification conjecture corresponding to given formula for parameter estimation
    * over a sliding window.
    *
    * @param fml A formula of the form p -> [a]q, which was proven correct.
    * @param vars A list of variables V, superset of BV(a).
    * @param unobservable Unobservable variables/parameters and their optional estimation (e.g., from a sensor),
    *                     keys subset of vars, any fns.
    * @param windowSize Size of sliding window for parameter estimation.
    * @return A tuple of monitor conjecture and assumptions
    */
  def createSlidingMonitorSpec(fml: Formula, vars: List[Variable],
                               unobservable: ListMap[_ <: NamedSymbol, Option[Formula]],
                               windowSize: Int): (Formula, List[Formula]) = {
    assert(vars.forall(_.index.isEmpty), "Variables with index not allowed, since sliding window generates indices")
    assert(windowSize >= 1, "Window size must be at least 1")
    //@todo encode in dL
    val ModelPlexConjecture(_, spec, assms) = createMonitorSpecificationConjecture(fml, vars, unobservable, NAMED_POST_VAR)

    val (unobservableStateVars, unknownParams, _) = partitionUnobservable(unobservable)
    val (ctx, specFml: Formula) = spec.at(PosInExpr(List.fill(unknownParams.keys.size)(0)))
    def ithMon(mon: Formula, vars: List[Variable], i: Int): Formula = {
      (vars.toSet -- unobservableStateVars.keySet).foldLeft(mon)({ case (f, v) =>
        f.replaceAll(v, BaseVariable(v.name, Some(i-1))).replaceAll(NAMED_POST_VAR(v), BaseVariable(v.name, Some(i)))
      })
    }
    val windowMon = (2 to windowSize).foldLeft(ithMon(specFml, vars, 1))({ case (f,i) => And(f, ithMon(specFml, vars, i)) })
    (ctx(windowMon), assms)
  }

  /** Conjecture for double-checking a monitor formula for correctness: assumptions -> (monitor -> < prg; >Upsilon). */
  def createMonitorCorrectnessConjecture(vars: List[Variable], kind: Symbol, checkProvable: Option[ProvableSig => Unit],
                                         unobservable: ListMap[_ <: NamedSymbol, Option[Formula]]): (Formula => Formula) = formula => {
    val monitor = apply(vars, kind, checkProvable)(formula)
    val ModelPlexConjecture(_, monitorConjecture, assumptions) = createMonitorSpecificationConjecture(formula, vars, unobservable)
    Imply(assumptions.reduceOption(And).getOrElse(True), Imply(monitor, monitorConjecture))
  }

  private def doReplaceOld(t: Term, x0: Map[Variable, Variable]): Term = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
    override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
      case v: BaseVariable if x0.contains(v) => Right(x0(v))
      case _ => Left(None)
    }
  }, t).get

  private def replaceOld(fml: Formula, x0: Map[Variable, Term]): Formula = x0.foldRight(fml)({
    case ((v, t), f) => f.replaceFree(v, t)
  })

  private def replace[S<:Expression, T<:Term, U<:Term](fml: S, repl: Map[T, U]): S = {
    repl.foldLeft(fml)({
      case (t: Term, v)    => t.replaceFree(v._1, v._2).asInstanceOf[S]
      case (f: Formula, v) => f.replaceFree(v._1, v._2).asInstanceOf[S]
      case (p: Program, v) => p.replaceFree(v._1, v._2).asInstanceOf[S]
    })
  }

  private def proofListener(name: String, senseVars: Set[Variable], x0: Map[Variable, Term]) = new IOListener() {
    var invariant: Option[GenProduct] = None
    // initial condition and differential invariants per ODE
    val diffInvariants: mutable.ListMap[DifferentialProgram, (Formula, Formula)] = mutable.ListMap()
    var inDW = false
    var dWResult: Option[IndexedSeq[Sequent]] = None
    var odeLemmas: List[(String, Formula, BelleExpr)] = Nil
    var throughoutLemmas: List[(String, Formula, BelleExpr)] = Nil
    var loopBranch: Option[BelleExpr] = None
    override def begin(input: BelleValue, expr: BelleExpr): Unit = expr match {
      case SeqTactic((t: AppliedDependentPositionTacticWithAppliedInput) :: (b: BranchTactic) :: Nil) if t.pt.name == "throughout" =>
        loopBranch = Some(b)
      case SeqTactic((t: AppliedDependentPositionTacticWithAppliedInput) :: (b: BranchTactic) :: Nil) if t.pt.name == "loop" && loopBranch.isEmpty =>
        loopBranch = Some(b)
      case SeqTactic((t: AppliedDependentPositionTacticWithAppliedInput) :: (b: BranchTactic) :: Nil) if t.pt.name == "loopAuto" && loopBranch.isEmpty =>
        loopBranch = Some(b)
      case t: AppliedDependentPositionTactic if t.name == "dW" => input match {
        case BelleProvable(p, _, _) =>
          val dwr = proveBy(p.subgoals.head, t)
          assert(dwr.subgoals.size == 1, "dW expected to result in a single subgoal")
          dWResult = Some(dwr.subgoals)
          inDW = true
      }
      case t: AppliedDependentPositionTacticWithAppliedInput if t.pt.name == "throughout" =>
        invariant = Some(t.pt.inputs.head.asInstanceOf[Formula] -> None)
      case t: AppliedDependentPositionTacticWithAppliedInput if t.pt.name == "loop" && invariant.isEmpty =>
        invariant = Some(t.pt.inputs.head.asInstanceOf[Formula] -> None)
      case t: AppliedDependentPositionTactic if t.pt.name == "loopAuto" && invariant.isEmpty =>
        input match {
          case BelleProvable(p, _, _) =>
            invariant = TactixLibrary.invGenerator(p.subgoals(0), t.locator.toPosition(p).get).toList.headOption
        }
      case t: AppliedDependentPositionTacticWithAppliedInput if t.pt.name == "dC" && !inDW => input match {
        case BelleProvable(p, _, _) =>
          val di = ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
            override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
              case Equal(t, FuncOf(TacticReservedSymbols.const, Nothing)) =>
                val oldified = x0.foldLeft(t)({ case (t, (v, v0)) => t.replaceFree(v, v0) })
                Right(Equal(t, oldified))
              case _ => Left(None)
            }
          }, t.pt.inputs.head.asInstanceOf[List[Formula]].head).get
          p.subgoals.head.sub(t.locator.toPosition(p).get) match {
            case Some(Box(ODESystem(ode, _), _)) if !diffInvariants.contains(ode) =>
              diffInvariants(ode) = (
                DifferentialHelper.extractInitialConditions(Some(ode))(p.subgoals.head.ante.reduceOption(And).getOrElse(True)).reduceRightOption(And).getOrElse(True),
                di)
            case Some(Box(ODESystem(ode, _), _)) if diffInvariants.contains(ode) =>
              if (StaticSemantics.freeVars(di).intersect(senseVars).toSet.nonEmpty) {
                val (init, prevDi) = diffInvariants(ode)
                val newDi = FormulaTools.conjuncts(di).diff(FormulaTools.conjuncts(prevDi))
                if (newDi.nonEmpty) diffInvariants(ode) = (init, And(prevDi, newDi.reduceRight(And)))
              }
          }
      }
      case b@BranchTactic(children) if loopBranch.contains(b) => input match {
        case BelleProvable(p, _, _) =>
          //@todo make sandbox tactic synthesis more flexible for shapes other than ctrl;plant
          assert(3 <= children.size && children.size <= 4 && children.size == p.subgoals.size,
            "3 open goals expected after loop, 4 open goals expected after throughout")
          throughoutLemmas = p.subgoals.zip(children).zipWithIndex.map({ case ((s, t), i) => (name+"_"+i, s.toFormula, implyR(1) & t) }).toList
        case _ =>
      }
      case t => input match {
        case BelleProvable(p, _, _) if dWResult.contains(p.subgoals) =>
          // close after dW
          assert(p.subgoals.size == 1, "dW expected on a single subgoal")
          def unsequentTac(a:Int,s:Int):BelleExpr = {
            val aTac = if(a > 1) {andL('Llast)*(a-1)} else nil
            val sTac = if(s > 1) {orR('Rlast)*(s-1)} else nil
            implyR(1) & aTac & sTac
          }
          odeLemmas = odeLemmas :+ (name+"_dW_" + odeLemmas.size, p.subgoals.head.toFormula, unsequentTac(p.subgoals.head.ante.length, p.subgoals.head.succ.length) & t)
          dWResult = None
        case _ => // nothing to do
      }
    }
    override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = expr match {
      case b: BranchTactic if loopBranch.contains(b) => loopBranch = None
      case t: AppliedDependentPositionTactic if t.name == "dW" => (inDW = false)
      case _ =>
    }
    override def kill(): Unit = {}
  }

  /** Combines the differential invariants picked up on multiple branches into a single conjunction of implications. */
  private def combineDiffInvariants(diffInvariants: List[(DifferentialProgram, (Formula, Formula))], origOde: ODESystem,
                                    x0: Map[Variable, Term]): Formula = {
    val origOdeAtoms = DifferentialHelper.atomicOdes(origOde)
    diffInvariants.map({ case (ode, (initial, di)) =>
      val reassociatedDi = FormulaTools.conjuncts(di).reduceRightOption(And).getOrElse(True)
      if (diffInvariants.size > 1) {
        val diff = DifferentialHelper.atomicOdes(ode).filterNot(origOdeAtoms.contains)
        val rhsStartValues = diff.map(x => Equal(origOdeAtoms.find(a => a.xp == x.xp).get.e, x.e))
        val varStartValues = rhsStartValues.flatMap({ case Equal(orig, inst) =>
          val starts: mutable.Map[BaseVariable, Term] = mutable.Map.empty
          ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
            override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
              case v: BaseVariable => starts(v) = inst.sub(p).get.asInstanceOf[Term]; Left(None)
              case _ => Left(None)
            }
          }, orig)
          starts.filter(kv => kv._1 != kv._2).map(kv => Equal(kv._1, kv._2))
        }).toSet
        val initialConditions = (FormulaTools.conjuncts(initial) ++ varStartValues).reduceRightOption(And).getOrElse(True)
        val oldifiedInitialConditions = DifferentialHelper.getPrimedVariables(ode).foldLeft[Formula](initialConditions)((f, v) =>
          f.replaceAll(v, FuncOf(Function("old", None, Real, Real), v)))
        Imply(replaceOld(oldifiedInitialConditions, x0), replaceOld(reassociatedDi, x0))
      } else replaceOld(reassociatedDi, x0)
    }).reduceRightOption(And).getOrElse(True)
  }

  /** Creates a model with the ODE approximated by the evolution domain and diff. invariants from the `tactic`.
    * Returns the adapted model and a tactic to proof safety from the original proof. */
  def createNonlinearModelApprox(name: String, tactic: BelleExpr, defs: Declaration): Expression => (Formula, BelleExpr) =
      (model: Expression) => model.exhaustiveSubst(USubst(defs.substs.filter(_.what match { case _: SystemConst | _: ProgramConst => true case _ => false }))) match {
    case fml@Imply(init, Box(Loop(prg), safe)) =>
      val (ctrl, plant, evolDomain, measure) = prg match {
        case Compose(c, p@ODESystem(_, q)) => (c, p, q, None)
        case Compose(c, Compose(act, p@ODESystem(_, q))) => (Compose(c, act), p, q, None)
        case Compose(c, Compose(p@ODESystem(_, q), m)) => (c, p, q, Some(m))
        case Compose(c, Compose(act, Compose(p@ODESystem(_, q), m))) => (Compose(c, act), p, q, Some(m))
      }
      val plantVars = StaticSemantics.boundVars(plant).toSet.filter(_.isInstanceOf[BaseVariable]).toList.sorted[NamedSymbol]
      val x0 = plantVars.map(v => v -> BaseVariable(v.name, TacticHelper.freshIndexInFormula(v.name, fml))).toMap
      val x0Ghosts = x0.toList.sortBy[NamedSymbol](_._1).map({ case (v, g) => Assign(g, v) }).reduceRight(Compose)

      val pl = proofListener(name, plantVars.toSet, /*q, */x0)
      LazySequentialInterpreter(pl::/*qeDurationListener::*/Nil)(tactic, BelleProvable.withDefs(ProvableSig.startProof(model.asInstanceOf[Formula], defs), defs)) match {
        case BelleProvable(proof, _, _) => assert(proof.isProved, "Cannot derive a nonlinear model from unfinished proof")
        case _ => assert(assertion = false, "Cannot derive a nonlinear model from unfinished proof")
      }

      def pushOld(fml: Formula): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case FuncOf(TacticReservedSymbols.old, _: BaseVariable) => Left(None)
          case FuncOf(TacticReservedSymbols.old, arg: Term) => Right(replace(arg, x0))
          case _ => Left(None)
        }
      }, fml).get

      val olds = x0.map({ case (v, v0) => FuncOf(TacticReservedSymbols.old, v) -> v0 })
      val diffInvariants = replace(pushOld(combineDiffInvariants(pl.diffInvariants.toList, plant, Map())), olds)
      val internalVars = StaticSemantics.freeVars(diffInvariants).toSet.filter(_.name.endsWith("_"))

      //@note tactics (e.g., ODE's nilpotentsolve) may introduce internal symbols that become "plant" variables
      val nondetPlant = (plantVars ++ internalVars).map(AssignAny).sortBy[NamedSymbol](_.x).reduceRight(Compose)
      val odeGuard = if (evolDomain == True) diffInvariants else And(evolDomain, diffInvariants)
      val guardedPlant = Compose(Test(odeGuard), Compose(nondetPlant, Test(odeGuard)))
      val body = measure match {
        case Some(m) => Compose(ctrl, Compose(Compose(x0Ghosts, guardedPlant), m))
        case None => Compose(ctrl, Compose(x0Ghosts, guardedPlant))
      }
      val approx = Imply(init, Box(Loop(body), safe))
      (approx, skip)
    case _ => throw new IllegalArgumentException("Unsupported model shape, expected shape init -> [(ctrl;plant;)*]safe")
  }

  /** Creates a sandbox safety conjecture from a formula of the shape init->[?bounds;{ctrl;plant}*]safe. The sandbox embeds
    * an (unverified) external controller in monitor checks of `kind`. It approximates the external controller behavior
    * with nondeterministic values for each of the bound variables in `ctrl`. Input to the external controller is measured with
    * nondeterministic values for each of the bound variables in `plant`, but restricted to those satisfying the
    * evolution domain constraints and invariants of the plant. If the monitor is satisfied, the external controller's
    * decision are actuated. Otherwise (monitor unsatisfied) `fallback` (if specified, ctrl by default) is executed.
    * @param tactic The tactic used to prove safety of the original model.
    * @param fallback The fallback controller to embed in the sandbox, `ctrl` by default.
    * @param kind The kind of monitor to derive (controller or model monitor).
    * @param checkProvable Whether or not to check the ModelPlex provable.
    * @return The sandbox formula with a tactic to prove it, and a list of lemmas used in the proof.
    */
  def createSandbox(name: String,
                    tactic: BelleExpr,
                    fallback: Option[Program],
                    kind: Symbol,
                    checkProvable: Option[(ProvableSig => Unit)],
                    synthesizeProofs: Boolean,
                    defs: Declaration,
                    postVar: Variable=>Variable = NAMED_POST_VAR):
                    Formula => ((Formula,BelleExpr), List[(String,Formula,BelleExpr)]) = formula => {
    require(kind == 'ctrl, s"Unable to create a sandbox of kind $kind, so far only controller monitors supported")
    val expandedModel = defs.exhaustiveSubst(formula)
    val (initCond: Formula, sysPrg: Loop, ctrlPrg: Program, plant: ODESystem, ode: DifferentialProgram, q: Formula, safe: Formula) = expandedModel match {
      case Imply(initCond, Box(sysPrg@Loop(Compose(ctrlPrg, plant@ODESystem(ode, q))), safe)) =>
        (initCond, sysPrg, ctrlPrg, plant, ode, q, safe)
      case Imply(initCond, Box(sysPrg@Loop(Compose(ctrlPrg, Compose(timeReset, plant@ODESystem(ode, q)))), safe)) =>
        (initCond, sysPrg, Compose(ctrlPrg, timeReset), plant, ode, q, safe)
      case _ => throw new IllegalArgumentException("Sandbox synthesis supports input formulas of the shape init -> [{ctrl;ODE}*]safe. Please use {} to group program statements into exactly two blocks, e.g. { {ctrl1;ctrl2;}{ODE} }*.")
    }
    val free = StaticSemantics.symbols(Compose(Test(initCond),sysPrg))
    val bound = StaticSemantics.boundVars(sysPrg)
    val constVars = free.--(bound.toSet)
    val vars: List[BaseVariable] = StaticSemantics.symbols(expandedModel).
      filter({case _: BaseVariable => true case _ => false}).
      --(constVars).
      map(_.asInstanceOf[BaseVariable]).
      toList.sorted[NamedSymbol]

    val consts: Map[Term,Variable] =
    constVars.
      filter({ case Function(_, _, Unit, _, _) => true case _: BaseVariable => true case _ => false }).
      map({ case s: Function => FuncOf(s, Nothing) -> Variable(s.name, s.index)
      case v: BaseVariable => v -> v}).toMap
    val bounds = FormulaTools.conjuncts(initCond).
      filter(StaticSemantics.freeVars(_).intersect(StaticSemantics.boundVars(sysPrg)).isEmpty).
      map(replace(_, consts)).
      reduceRightOption(And).getOrElse(True)
    val monitor = replace(apply(vars, kind, checkProvable)(expandedModel), consts)
    val senseVars: List[Variable] = StaticSemantics.boundVars(ode).toSet.
      filterNot(StaticSemantics.isDifferential(_)).toList.sorted[NamedSymbol]
    val sensePostVars = senseVars.map(v => v -> postVar(v)).toMap
    val ctrlVars: List[Variable] = StaticSemantics.boundVars(ctrlPrg).toSet[Variable].toList.sorted[NamedSymbol]
    val ctrlOnlyVars : List[Variable] = ctrlVars.filter({ x => !(senseVars.contains(x) || constVars.contains(x)) })
    val initSensors = FormulaTools.conjuncts(initCond).
      //@todo freeVars(loopinv) would be more accurate than boundVars(ctrlPrg)
      filter(!StaticSemantics.freeVars(_).intersect(StaticSemantics.boundVars(plant) ++ StaticSemantics.boundVars(ctrlPrg)).isEmpty).
      map(replace(_, consts)).
      reduceRightOption(And).getOrElse(True)

    val x0 = Map[Variable,Term]()
    val olds = senseVars.map(v => FuncOf(Function("old", None, Real, Real), postVar(v)) -> v).toMap

    val pl = proofListener(name, senseVars.toSet, x0)
    LazySequentialInterpreter(pl::Nil)(tactic, BelleProvable.withDefs(ProvableSig.startProof(formula, defs), defs))

    assert(pl.invariant.isDefined, "Proof of model " + name + " does not provide a loop invariant. Please use tactic loop({`inv`},...) in the proof.")
    assert(pl.diffInvariants.nonEmpty, "Proof of model " + name + " does not provide sufficient insight into invariant regions of the ODE dynamics. Please use differential cuts dC in the proof.")
    assert(pl.odeLemmas.nonEmpty, "Proof of model " + name + " does not provide sufficient insight abstracting from the ODE dynamics. Please use differential weakening dW in the proof.")

    val inv = replace(pl.invariant.get._1, consts)

    val diffInvConjuncts = FormulaTools.conjuncts(combineDiffInvariants(pl.diffInvariants.toList, plant, x0)) :+ q
    val rep1 = diffInvConjuncts.map(replace(_, sensePostVars))
    val rep2 = rep1.map(replace(_, consts))
    val rep3 = rep2.map(replace(_, olds))
    val rep4 = rep3.distinct
    val plantMonitor = rep4.reduceRight(And)

    val sensePreVars = senseVars.map(v => BaseVariable(v.name, Some(v.index.getOrElse(-1)+1)) -> v).toMap
    val odeLemmas = pl.odeLemmas.map({ case (odeLemmaName, odeLemmaFml, odeLemmaTactic) =>
      (odeLemmaName, replace(replace(odeLemmaFml, sensePostVars), sensePreVars),
        sensePreVars.map({ case (v0, v) => uniformRename(v, v0) }).reduceOption[BelleExpr](_&_).getOrElse(skip) &
          sensePostVars.map({ case (v, vp) => uniformRename(v, vp) }).reduceOption[BelleExpr](_&_).getOrElse(skip) &
          odeLemmaTactic)
    })

    val monitor0 = replace(monitor, vars.map(v => postVar(v) -> v).toMap)

    def skipPostfixedAssignments(assignments: Seq[Program]): Program = (assignments :+ Test(True)).reduceRight(Compose)
    def skipPostfixFallback(fb: Program): Program = {
      def decompose(prg: Program): Seq[Program] = prg match {
        case Compose(l, r) => decompose(l) ++ decompose(r)
        case _ => prg :: Nil
      }
      skipPostfixedAssignments(decompose(fb))
    }

    // consts:=*;
    val readConsts = skipPostfixedAssignments(consts.values.toList.sorted[NamedSymbol].map(AssignAny))
    // senseVars+:=*; ?plantMonitor; senseVars:=senseVars+;
    val readInitialSensors = skipPostfixedAssignments(senseVars.map(AssignAny))
    val readSensors = skipPostfixedAssignments(sensePostVars.values.toList.sorted[NamedSymbol].map(AssignAny))
    val readCtrls = skipPostfixedAssignments(ctrlVars.sorted[NamedSymbol].map(AssignAny))
    val copySensors = skipPostfixedAssignments(sensePostVars.toList.sortBy[NamedSymbol](_._1).map(Assign.tupled))

    val sense = Compose(readSensors, Compose(Test(plantMonitor), copySensors))
    // ctrlVars+:=*;
    val ctrl = skipPostfixedAssignments(ctrlVars.map(postVar).map(AssignAny))
    // senseVars\ctrlVars:=senseVars
    val nonCtrlState = skipPostfixedAssignments((senseVars.toSet--ctrlVars.toSet).toList.sorted[NamedSymbol].
      map(v => postVar(v) -> v).map(Assign.tupled))
    // ctrlVars:=ctrlVarsTemp
    val operationalize = skipPostfixedAssignments(ctrlVars.map(v => Assign(v, postVar(v))))
    // ctrl+:=fallback
    val fb = fallback.getOrElse(ctrlPrg)
    // Note: This is an easy way to compute the union of boundVars across fallback and control program; we will need both
    val allvars = StaticSemantics.boundVars(Compose(fb,ctrlPrg)).toSet[Variable].toList.sorted[NamedSymbol]
    val fallbackCtrl = allvars.foldRight(skipPostfixFallback(fb))({ case (v, fprg) => URename(v, postVar(v))(fprg) })
    // ?monitor ++ ctrlVars+:=fallback
    val act = Choice(Test(monitor), fallbackCtrl)

    val upsilonConjuncts = vars.sorted[NamedSymbol].map(v => Equal(postVar(v), v))
    val upsilon = upsilonConjuncts.reduce(And)

    // ctrlVars+:=ctrlVars
    val tempCtrl = skipPostfixedAssignments(vars.map(v => Assign(postVar(v), v)))

    val sandbox = Imply(replace(initCond, consts), Box(
      Compose(Compose(readConsts,
        Compose(readCtrls,
          Compose(readInitialSensors,
            Test(And(bounds, initSensors))))),
        Loop(Compose(ctrl,
          Compose(nonCtrlState,
            Compose(replace(act,consts),
              Compose(operationalize, sense)))))),
      replace(safe, consts)))

    if (synthesizeProofs) {
      /* todo */
      (sandbox -> nil, Nil)
    } else {
      (sandbox -> nil, Nil)
    }
  }

  /**
    * Synthesizes a tactic to derive a sandbox safety proof from the safety proof of the original model.
    * @param name The name of the sandbox (used to prefix lemma lookup).
    * @param inv The throughout invariant used in the original safety proof.
    * @param monitor Monitor derived from the model.
    * @param ctrl Verified control program.
    * @param fallbackCtrl Fallback control with control effect set to post-vars, of the shape fallback;xp:=x;
    * @param upsilon The ModelPlex conjecture post-condition of the shape xp=x
    * @param senseVars The variables bound in the plant.
    * @return The tactic to derive a sandbox safety proof from the original safety proof.
    */
  private def sandboxTacticPlantFirst(name: String, inv: Formula, monitor: Formula, odeDomain: Formula,
                            ctrl: Program, fallbackCtrl: Program,
                            upsilon: Formula, senseVars: List[Variable]): BelleExpr = {
    val numCtrlVars = StaticSemantics.boundVars(ctrl).toSet.size
    val upsilonConjuncts = FormulaTools.conjuncts(upsilon)

    /*@note chase but stop on <ctrl>fallbackUpsilon */
    val chaseFallback = anon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Diamond(prg, _)) if prg == ctrl => nil
      case _ => step(pos) | alphaRule | allR(pos)
    })

    //@todo generalize to fallback with nondeterministic choice
    val Diamond(_, fallbackUpsilon) = proveBy(Box(fallbackCtrl, Diamond(ctrl, upsilon)),
      SaturateTactic(chaseFallback(1))).subgoals.head.succ.head

    val fallbackUpsilonConjuncts = FormulaTools.conjuncts(fallbackUpsilon)

    implyR(1) & SaturateTactic(andL('L)) & composeb(1) & testb(1) & implyR(1) & throughout(inv)(1) & Idioms.<(
      DebuggingTactics.print("Proving base case") & useLemma(name+"_0", Some(prop)) & DebuggingTactics.done("Base case")
      ,
      DebuggingTactics.print("Proving use case") & useLemma(name+"_1", Some(prop)) & DebuggingTactics.done("Use case")
      ,
      DebuggingTactics.print("Proving plant") & chase(1) & allR(1)*senseVars.size &
      DebuggingTactics.print("Applying " + name + "_dW lemma") &
      useLemma(name+"_dW", Some(prop)) & DebuggingTactics.done(name + "_dW lemma")
      ,
      DebuggingTactics.print("Proving external control") & chase(1) & allR(1)*numCtrlVars & prop &
      DebuggingTactics.done("External control")
      ,
      DebuggingTactics.print("Proving controllers") & chase(1) & andR(1) & Idioms.<(
        DebuggingTactics.print("Proving external control passes monitor") &
        useLemmaAt(name+"_MonitorCheck", Some(PosInExpr(0::Nil)))(1, 0::Nil) &
        implyR(1) & cut(Box(ctrl, inv)) & Idioms.<(
          cut(Diamond(ctrl, And(inv, And(upsilon, odeDomain)))) & Idioms.<(
            hideL('L, Box(ctrl, inv)) & hideL('L, Diamond(ctrl, And(upsilon, odeDomain))) &
            useAt(Ax.diamond, PosInExpr(1::Nil))('Llast) &
            notL('Llast) & abstractionb('Rlast) & allR('Rlast)*numCtrlVars & notR('Rlast) & SaturateTactic(andL('L)) &
            upsilonConjuncts.filter({ case Equal(l, r) => l != r }).map(c => exhaustiveEqL2R('L, c)).reduce[BelleExpr](_&_) &
            prop & DebuggingTactics.done("External control passes monitor 1")
            ,
            useAt(Ax.Kd2, PosInExpr(1::1::Nil))(2) & onAll(prop) &
            DebuggingTactics.done("External control passes monitor 2")
          ),
          useLemma(name+"_2", Some(prop)) & DebuggingTactics.done("External control passes monitor 3")
        ) & DebuggingTactics.done("External control")
        ,
        DebuggingTactics.print("Proving fallback") &
        implyR(1) & hideL('Llast) & cut(Box(fallbackCtrl, monitor)) <(
          Idioms.searchApplyIn(Box(fallbackCtrl, monitor),
            useLemmaAt(name+"_MonitorCheck", Some(PosInExpr(0::Nil))), PosInExpr(1::Nil)) &
            SaturateTactic(chaseFallback('Llast)) & cut(Box(ctrl, inv)) <(
            cut(Diamond(ctrl, And(inv, And(fallbackUpsilon, odeDomain)))) <(
              hideL('L, Box(ctrl, inv)) & hideL('L, Diamond(ctrl, And(fallbackUpsilon, odeDomain))) &
              useAt(Ax.diamond, PosInExpr(1::Nil))('Llast) &
              notL('Llast) & abstractionb('Rlast) & allR('Rlast)*numCtrlVars & notR('Rlast) & SaturateTactic(andL('L)) &
              fallbackUpsilonConjuncts.filter({ case Equal(l, r) => l != r }).
                map(c => exhaustiveEqR2L('L, c)).
                reduce[BelleExpr](_&_) &
              prop & DebuggingTactics.done("Fallback 1")
              ,
              useAt(Ax.Kd2, PosInExpr(1::1::Nil))('Rlast) & onAll(prop) &
              DebuggingTactics.done("Fallback 2")
            )
            ,
            DebuggingTactics.print("Applying " + name + "_2 lemma") &
            useLemma(name+"_2", Some(prop)) &
            DebuggingTactics.done("Applying " + name + "_2 lemma")
          )
          ,
          DebuggingTactics.print("Applying " + name + "_FallbackCheck lemma") &
          useLemma(name+"_FallbackCheck", Some(prop)) & DebuggingTactics.done("Applying " + name + "_FallbackCheck lemma")
        ) & DebuggingTactics.done("Proving fallback")
      )
    )
  }

  /**
    * Synthesizes a tactic to derive a sandbox safety proof from the safety proof of the original model.
    * @param name The name of the sandbox (used to prefix lemma lookup).
    * @param inv The throughout invariant used in the original safety proof.
    * @param monitor Monitor derived from the model.
    * @param ctrl Verified control program.
    * @param fallbackCtrl Fallback control with control effect set to post-vars, of the shape fallback;xp:=x;
    * @param upsilon The ModelPlex conjecture post-condition of the shape xp=x
    * @param senseVars The variables bound in the plant.
    * @return The tactic to derive a sandbox safety proof from the original safety proof.
    */
  private def sandboxTactic(name: String, inv: Formula, monitor: Formula, odeDomain: Formula,
                            ctrl: Program, fallbackCtrl: Program, consts: Map[FuncOf, Variable],
                            upsilon: Formula, senseVars: List[Variable]): BelleExpr = {
    val numCtrlVars = StaticSemantics.boundVars(ctrl).toSet.size
    val upsilonConjuncts = FormulaTools.conjuncts(upsilon)

    /*@note chase but stop on <ctrl>fallbackUpsilon */
    val chaseFallback = anon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
      case Some(Diamond(prg, _)) if prg == ctrl => nil
      case _ => step(pos) | alphaRule | allR(pos)
    })

    //@todo generalize to fallback with nondeterministic choice
    val Diamond(_, fallbackUpsilon) = proveBy(Box(fallbackCtrl, Diamond(ctrl, upsilon)),
      SaturateTactic(chaseFallback(1))).subgoals.head.succ.head

    val fallbackUpsilonConjuncts = FormulaTools.conjuncts(fallbackUpsilon)

    def constify(tactic: BelleExpr): BelleExpr = consts.foldLeft[BelleExpr](tactic)((tactic, c) => let(c._1, c._2, tactic))

    DebuggingTactics.print("Proving sandbox safety") &
    chase(1) & SaturateTactic((allR(1) | implyR(1))) & loop(inv)(1) <(
      DebuggingTactics.print("Proving base case") & constify(useLemma(name+"_0", Some(prop))) & DebuggingTactics.done("Base case")
      ,
      DebuggingTactics.print("Proving use case") & constify(useLemma(name+"_1", Some(prop))) & DebuggingTactics.done("Use case")
      ,
      DebuggingTactics.print("Proving induction step") &
      DebuggingTactics.print("Executing external control") &
      composeb(1) & (composeb(1) & randomb(1) & allR(1))*(numCtrlVars-1) & randomb(1) & allR(1) &
      DebuggingTactics.print("Splitting actuation/fallback from plant") &
      composeb(1) & generalize(inv)(1) <(
        DebuggingTactics.print("Proving controllers") & choiceb(1) & andR(1) <(
          DebuggingTactics.print("Proving external control actuation") &
          composeb(1) & testb(1) &
          useLemmaAt(name+"_MonitorCheck", Some(PosInExpr(0::Nil)))(1, 0::Nil) &
          implyR(1) & cut(Box(ctrl, inv)) <(
            cut(Diamond(ctrl, And(inv, And(upsilon, odeDomain)))) <(
              DebuggingTactics.print("Using external control actuation cuts") &
              chase(1) &
              hideL('L, Box(ctrl, inv)) & hideL('L, Diamond(ctrl, And(upsilon, odeDomain))) &
              useAt(Ax.diamond, PosInExpr(1::Nil))('Llast) &
              notL('Llast) & abstractionb('Rlast) & allR('Rlast)*numCtrlVars & notR('Rlast) & SaturateTactic(andL('L)) &
              upsilonConjuncts.filter({ case Equal(l, r) => l != r }).map(c => exhaustiveEqL2R('L, c)).reduce[BelleExpr](_&_) &
              prop & DebuggingTactics.done("Using external control actuation cuts")
              ,
              DebuggingTactics.print("Proving <ctrl;>(inv&upsilon&q)") &
              useAt(Ax.Kd2, PosInExpr(1::1::Nil))(2) & onAll(prop) &
              DebuggingTactics.done("Proving <ctrl;>(inv&upsilon&q)")
            )
            ,
            DebuggingTactics.print("Proving [ctrl;]inv") &
            constify(useLemma(name+"_2", Some(prop))) & DebuggingTactics.done("Proving [ctrl;]inv")
          ) &
          DebuggingTactics.done("Proving external control actuation")
          ,
          DebuggingTactics.print("Proving fallback") & composeb(1) & testb(1) & implyR(1) & hideL('Llast) &
          cut(Box(fallbackCtrl, monitor)) <(
            Idioms.searchApplyIn(Box(fallbackCtrl, monitor),
              useLemmaAt(name+"_MonitorCheck", Some(PosInExpr(0::Nil))), PosInExpr(1::Nil)) &
              SaturateTactic(chaseFallback('Llast)) & DebuggingTactics.print("Fallback chased") &
            cut(Box(ctrl, inv)) <(
              cut(Diamond(ctrl, And(inv, And(fallbackUpsilon, odeDomain)))) <(
                DebuggingTactics.print("Using fallback cuts") &
                chase(1) & hideL('L, Box(ctrl, inv)) & hideL('L, Diamond(ctrl, And(fallbackUpsilon, odeDomain))) &
                useAt(Ax.diamond, PosInExpr(1::Nil))('Llast) &
                notL('Llast) & abstractionb('Rlast) & allR('Rlast)*numCtrlVars & notR('Rlast) & SaturateTactic(andL('L)) &
                fallbackUpsilonConjuncts.filter({ case Equal(l, r) => l != r }).map(c => exhaustiveEqR2L('L, c)).reduce[BelleExpr](_&_) &
                prop & DebuggingTactics.done("Using fallback cuts")
                ,
                DebuggingTactics.print("Proving <ctrl;>(inv&upsilon&q)") &
                useAt(Ax.Kd2, PosInExpr(1::1::Nil))('Rlast) & onAll(prop) &
                DebuggingTactics.done("Proving <ctrl;>(inv&upsilon&q)")
              )
              ,
              DebuggingTactics.print("Applying " + name + "_2 lemma") &
              constify(useLemma(name+"_2", Some(prop))) &
              DebuggingTactics.done("Applying " + name + "_2 lemma")
            )
            ,
            DebuggingTactics.print("Applying " + name + "_FallbackCheck lemma") &
            useLemma(name+"_FallbackCheck", Some(prop)) &
            DebuggingTactics.done("Applying " + name + "_FallbackCheck lemma")
          ) &
          DebuggingTactics.done("Proving fallback")
        ),
        DebuggingTactics.print("Proving plant") & chase(1) & allR(1)*senseVars.size &
        DebuggingTactics.print("Applying " + name + "_dW lemma") &
        constify(useLemma(name+"_dW", Some(prop))) &
        DebuggingTactics.done(name + "_dW lemma")
      ) &
      DebuggingTactics.done("Proving induction step")
    ) &
    DebuggingTactics.done("Proving sandbox safety")
  }

  /**
   * Returns a tactic to derive a controller monitor in axiomatic style using forward chase. The tactic is designed to
   * operate on input produced by createMonitorSpecificationConjecture.
    *
    * @see [[createMonitorSpecificationConjecture]]
   * @example {{{
   *        |- xpost=1
   *        ------------------------------controllerMonitorByChase(1)
   *        |- <{x:=1; {x'=2}}*>xpost=x
   * }}}
   * In order to produce the result above, the tactic performs intermediate steps as follows.
   * @example {{{
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
  def controllerMonitorByChase: BuiltInPositionTactic = chase(3,3, (e:Expression) => e match {
    // remove loops
    case Diamond(Loop(_), _) => Ax.loopApproxd :: Nil
    // remove ODEs for controller monitor
    case Diamond(ODESystem(_, _), _) => Ax.dDX :: Nil
    // run inside quantifiers
    case _: Exists => Ax.existsStutter :: Nil
    case _: Forall => Ax.allStutter :: Nil
    case _: And => Ax.andStutter :: Nil
    case _ => logger.trace("Chasing " + e.prettyString); AxIndex.axiomsFor(e)
  })

  def chaseToTests(combineTests: Boolean): BuiltInPositionTactic = {
    chaseI(3,3, (e:Expression) => e match {
      case Or(_, _) => Ax.orRecursor :: Nil
      case And(_, _) => Ax.invtestd :: Nil
      case f: Formula if f.isFOL && f != True => Ax.andTrueInv :: Nil
      case f: Formula if f == True => Nil
      case Diamond(Test(_), Diamond(Test(_), _)) if combineTests => Ax.testdcombine :: Nil
      case _: Diamond => Ax.programStuck :: Nil
      case _: Exists => Ax.existsStutter :: Nil
      case _: Forall => Ax.allStutter :: Nil
      //case _ => logger.trace("Chasing " + e.prettyString); AxiomIndex.axiomsFor(e)
    }, (_,_) => pr=>pr, _ => us=>us, AxIndex.axiomIndex)
  }

  /** Chase index to remove loops and split sequential compositions, skip everything else. */
  private val loopComposeIndex = (e:Expression) => e match {
    // remove loops and split compositions to isolate differential equations before splitting choices
    case Diamond(Loop(_), _) => Ax.loopApproxd:: Nil
    case Diamond(Compose(_, _), _) => AxIndex.axiomsFor(e)
    // run inside quantifiers
    case _: Exists => Ax.existsStutter :: Nil
    case _: Forall => Ax.allStutter :: Nil
    // run inside sliding window conjunction
    case _: And => Ax.andStutter :: Nil
    case _ => Nil
  }

  /** Chase index to skip ODEs, remove loops, and all other programs. */
  private val skipODEIndex = (e:Expression) => e match {
    // remove loops
    case Diamond(Loop(_), _) => Ax.loopApproxd :: Nil
    // keep ODEs, solve later
    case Diamond(ODESystem(_, _), _) => Nil
    // run inside quantifiers
    case _: Exists => Ax.existsStutter :: Nil
    case _: Forall => Ax.allStutter :: Nil
    // run inside sliding window conjunction
    case _: And => Ax.andStutter :: Nil
    case _ => logger.trace("Chasing " + e.prettyString); AxIndex.axiomsFor(e)
  }

  /** Solves ODEs for model monitors, chases in ODE postcondition after solving. */
  private lazy val modelMonitorSolveChaseODE = anon ((pos: Position, seq: Sequent) => seq.sub(pos) match {
    case Some(Diamond(_: ODESystem, _)) =>
      AxiomaticODESolver.axiomaticSolve()(pos) & chase(3, 3, skipODEIndex)(pos ++ PosInExpr(0::1::Nil)) &
        SimplifierV3.simpTac()(pos ++ PosInExpr(0::1::Nil))
    case e => throw new TacticInapplicableFailure("Expected an ODE at position " + pos + ", but got " +
      e.map(_.prettyString).getOrElse("<none>"))
  })

  /**
    * Returns a tactic to derive a model monitor in axiomatic style using forward chase + diffSolve. The tactic is
    * designed to operate on input produced by createMonitorSpecificationConjecture.
    *
    * @see [[createMonitorSpecificationConjecture]]
    * @return The tactic.
    */
  lazy val modelMonitorByChase: DependentPositionTactic = modelMonitorByChase(modelMonitorSolveChaseODE)
  def modelMonitorByChase(ode: DependentPositionTactic): DependentPositionTactic = anon ((pos: Position, _: Sequent) =>
    chase(3,3, loopComposeIndex)(pos) &
    applyAtAllODEs(ode)(pos) & // solve isolated ODEs once before splitting choices
    // chase and solve remaining
    chase(3,3, skipODEIndex)(pos) &
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
  def eulerAllIn: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    val eulerAxiom = "<{x_'=f(x_)}>p(x_) <-> \\exists t_ (t_>=0 & \\forall e_ (e_>0 -> \\forall h0_ (h0_>0 -> \\exists h_ (0<h_&h_<h0_&<{x_:=x_+h_*f(x_);}*>(t_>=0 & \\exists y_ (abs(x_-y_) < e_ & p(y_))) ))))".asFormula
    val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
      case (Diamond(_: ODESystem, _), pp) => Some(useAt(ProvableSig.startPlainProof(eulerAxiom), PosInExpr(0::Nil))(pp))
      case _ => None
    })
    positions.reduceRightOption[BelleExpr](_ & _).getOrElse(skip)
  })

  /** Euler-approximates all ODEs somewhere underneath pos. Systematic tactic, but not a proof. */
  def eulerSystemAllIn: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
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
      case (Diamond(ode: ODESystem, p), dpos) => Some(OnAll(useAt(ProvableSig.startPlainProof(createEulerAxiom(ode, p)), PosInExpr(0::Nil))(dpos) | skip))
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
  def unrollLoop(n: Int): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    if (n <= 0) skip
    else {
      val positions: List[BelleExpr] = mapSubpositions(pos, sequent, {
        case (Diamond(_: Loop, _), pp) =>
          if (n == 1) Some(useAt(Ax.loopApproxd)(pp))
          else Some(useAt(Ax.iterated, PosInExpr(0 :: Nil))(pp))
        case _ => None
      })
      positions.reduceRightOption[BelleExpr](_ & _).getOrElse(skip) & unrollLoop(n-1)(pos)
    }
  })

  /** Chases remaining assignments. */
  lazy val chaseEulerAssignments: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
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
  def modelplexAxiomaticStyle(unprog: DependentPositionTactic): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    // was "Modelplex In-Place"
    sequent.sub(pos) match {
      case Some(Diamond(_, _)) =>
        SaturateTactic(debug("Before HP") & unprog(pos) & debug("After  HP")) & debug("Modelplex done")
      case Some(e) => throw new TacticInapplicableFailure("Modelplex In-Place only applicable to diamond properties, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
  })

  /** Axioms for translating programs into monitors (shared between controller and model monitor). */
  private def monitorAxioms = List(
    useAt(Ax.composed),
    useAt(Ax.choiced),
    anon ((p: Position) => useAt(Ax.randomd)(p)),
    useAt(Ax.testd),
    anon ((p: Position) => TryCatch(
      useAt(Ax.assigndAxiom)(p),
      classOf[SubstitutionClashException],
      (_: SubstitutionClashException) => fail)
    ),
    anon ((p: Position) => useAt(Ax.assigndEqualityAxiom)(p)),
  )

  /** Returns a backward tactic for deriving controller monitors. */
  def controllerMonitorT: DependentPositionTactic =
    anon ((pos: Position) =>
      locateT(List(
        useAt(Ax.loopApproxd, PosInExpr(1::Nil)),
        useAt(Ax.dDX, PosInExpr(1::Nil))) ++ monitorAxioms)(pos))

  /** Returns a backward tactic for deriving model monitors. */
  def modelMonitorT: DependentPositionTactic = anon ((pos: Position) =>
    locateT(List(
      useAt(Ax.loopApproxd, PosInExpr(1::Nil)),
      AxiomaticODESolver.axiomaticSolve()) ++ monitorAxioms)(pos))

  /**
   * Returns a tactic to solve two-dimensional differential equations. Introduces constant function symbols for
   * variables that do not change in the ODE, before it hands over to the actual diff. solution tactic.
    *
    * @return The tactic.
   */
    // was "<','> differential solution"
  def diamondDiffSolve2DT: DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    ??? //(diffIntroduceConstantT & ODETactics.diamondDiffSolve2DT)(p)
  })

  /**
   * Returns a modified test tactic for axiom <?H>p <-> H & (H->p)
    *
    * @example {{{
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
    * @example {{{
   *           |- a=1 & (<x:=2;>x+y>0 & <y:=3;>x+y>0)
   *           ---------------------------------------locateT(diamondSeqT :: diamondChoiceT :: Nil)(1)
   *           |- a=1 & <x:=2; ++ y:=3;>x+y>0
   * }}}
   * @param tactics The list of tactics.
   * @return The tactic.
   */
  def locateT(tactics: List[AtPosition[_ <: BelleExpr]]): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    require(tactics.nonEmpty, "At least 1 tactic required")
    val here = tactics.map(_(pos)).reduceRight[BelleExpr](_ | _)

    def recurseOnFormula(p: Position) = sequent.sub(p) match {
      case Some(_: Formula) => locateT(tactics)(p)
      case _ => DebuggingTactics.error("Stop recursion", new TacticInapplicableFailure(_))
    }

    val left: BelleExpr = recurseOnFormula(pos ++ PosInExpr(0::Nil))
    val right: BelleExpr = recurseOnFormula(pos ++ PosInExpr(1::Nil))

    here | left | right
  })

  /** Abbreviates functions to nullary function symbols if all their arguments are free in `fml`,
   * expand according to `defs` the functions that have at least one if their arguments bound. Returns the formula
   * with abbreviated/expanded functions, and the substitutions telling which functions were expanded/abbreviated how. */
  def mxAbbreviateFunctions(fml: Formula, defs: Declaration): (Formula, USubst) = {
    // Reduce/Resolve do not support arbitrary functions -> abbreviate to nullary functions for QE
    val is = scala.collection.mutable.Map.empty[Function, Int]
    val bv = StaticSemantics.boundVars(fml)
    var subst = USubst(List.empty)

    def replaceOrExpand[T <: Expression](expr: T): T = ExpressionTraversal.traverseExpr(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case pn@PredOf(f: Function, _) =>
          defs.substs.find(_.what match {
            case PredOf(wfn, _) => wfn == f
            case _ => false
          }) match {
            case None => ???
            case Some(d) =>
              val s = USubst(List(d))
              subst = subst ++ s
              Right(replaceOrExpand(s(pn)))
          }
        case _ => Left(None)
      }
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case fn@FuncOf(f@Function(n, i, d, _, false), args) if d != Unit =>
          if (StaticSemantics.freeVars(args).intersect(bv).isEmpty) {
            //@note can abbreviate, fn does not depend on any of the quantified variables
            if (!subst.subsDefsInput.exists(_.what == fn)) {
              is(fn.func) = is.get(fn.func).map(_ + 1).getOrElse(0)
              val abbrv = FuncOf(f.copy(
                name = n + i.map(_.toString).getOrElse(""),
                index = Some(is(fn.func)),
                domain = Unit), Nothing)
              subst = subst ++ USubst(List(SubstitutionPair(abbrv, fn)))
              Right(abbrv)
            } else Right(fn)
          } else {
            //@note expand fn to expose dependency on quantified variables
            defs.substs.find(s => s.what match {
              case FuncOf(wfn, _) => wfn == f
              case _ => false
            }) match {
              case None => throw new IllegalArgumentException("Function " + fn.prettyString + " depends on quantified variable " + bv + " and so must be expanded, but got no definition how to expand; please make unobservable")
              case Some(d) =>
                val s = USubst(List(d))
                subst = subst ++ s
                Right(replaceOrExpand(s(fn)))
            }
          }
        case _ => Left(None)
      }
    }, expr).get

    (replaceOrExpand(fml), subst)
  }

  /** Partial QE on a formula that first expands/abbreviates all uninterpreted symbols and
    * then substitutes back in on the result. */
  def mxPartialQE(fml: Formula, defs: Declaration, tool: QETacticTool): ProvableSig = mxPartialQE(List(fml), defs, tool)
  def mxPartialQE(fmlAlts: List[Formula], defs: Declaration, tool: QETacticTool, verified: Boolean = true): ProvableSig = {
    val abbreviated = fmlAlts.map(mxAbbreviateFunctions(_, defs)).toMap
    val goal = OneOf(abbreviated.map(f => Atom(f._1)).toSeq)
    tool.qe(goal, continueOnFalse=false) match {
      case (Atom(f), result) => abbreviated.get(f) match {
        case Some(subst) => if (verified) tool.qe(f).fact(subst) else ProvableSig.startProof(Equiv(f, result), defs)(subst)
        case None => throw new IllegalStateException("Unexpected parallel QE answer")
      }
    }
  }

  /** Returns the position of the innermost quantifier of `fml`. */
  private def innermostQuantifierPos(fml: Formula): PosInExpr = {
    var innermost = PosInExpr.HereP
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case q: Quantified =>
          if (StaticSemantics.boundVars(q.child).isEmpty) innermost = p
          Left(None)
        case _ => Left(None)
      }
    }, fml)
    innermost
  }

  /** Simplifies the right-hand side of the equivalence conclusion of `p`. */
  private def simplifyEquivProof(p: ProvableSig): ProvableSig = {
    val Equiv(orig, result) = p.conclusion.succ.head
    SimplifierV3.formulaSimp(result, faxs=SimplifierV3.defaultFaxs, taxs=SimplifierV3.defaultTaxs) match {
      case (simplifiedResult, Some((True, simpProof))) =>
        val Imply(True, equiv) = simpProof.conclusion.succ.head
        val uncondSimpProof = ProvableSig.startProof(equiv, p.defs)(
          CEat(Ax.trueImply.provable(USubst(List(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), equiv)))))(SuccPos(0)), 0)(
          simpProof, 0)
        ProvableSig.startProof(Equiv(orig, simplifiedResult), p.defs)(
          CEat(uncondSimpProof, PosInExpr(1::Nil))(SuccPosition.base0(0, PosInExpr(1::Nil))), 0)(
          p, 0)
      case _ => p
    }
  }

  /** Splits into separate partial QE calls and merges results.  */
  def stepwisePartialQE(fml: Formula,
                        assumptions: List[Formula],
                        defs: Declaration,
                        tool: QETacticTool with SimplificationTool,
                        preQE: (Formula, Int)=>Unit = (_, _) => {},
                        postQE: (Formula, Int)=>Unit = (_, _) => {}): ProvableSig = fml.at(innermostQuantifierPos(fml)) match {
    case (ctx, exists@Exists(x, p)) =>
      val (dnf, dnfProof) = timed(PropositionalTactics.disjunctiveNormalForm(p), "Computing disjunctive normal form")
      assert(dnfProof.isProved, "Expected a finished disjunctive normal form proof, but proof not closed")

      val monitorComponents = FormulaTools.disjuncts(dnf).map(Exists(x, _))
      val componentResults = monitorComponents.zipWithIndex.map({ case (f, i) =>
        //@note backend QE seems to not always handle f[] well in the context of existential quantifiers
        preQE(f, i)
        val consts = StaticSemantics.symbols(f).
          filter({ case Function(_, _, Unit, Real, false) => true case _ => false }).
          map({ case fn@Function(n, i, Unit, s, _) => FuncOf(fn, Nothing) -> Variable(n, i, s) }).toList
        val varified = consts.foldLeft(f)({ case (fml, (fn, v)) => fml.replaceAll(fn, v) })
        //@note first exhaustive subst, then varify, because exhaustive subst elaborates to functions and so would undo varification
        val varifiedExpanded = consts.foldLeft(defs.exhaustiveSubst(f))({ case (fml, (fn, v)) => fml.replaceAll(fn, v) })
        assert(StaticSemantics.symbols(varified).intersect(consts.map(_._1.func).toSet).isEmpty)
        assert(StaticSemantics.symbols(varifiedExpanded).intersect(consts.map(_._1.func).toSet).isEmpty)

        val qfVarifiedProof = timed({
          val partialQEProof = ModelPlex.mxPartialQE(List(varified, varifiedExpanded), defs, tool)
          //@todo
          //tool.simplify(qfResult.subgoals.head.succ.head, assumptions)
          simplifyEquivProof(partialQEProof)
        }, "QE " + (i+1) + "/" + monitorComponents.size)

        val result = qfVarifiedProof.conclusion.succ.head
        val fnified = consts.foldLeft(result)({ case (fml, (fn, v)) => fml.replaceAll(v, fn) })

        val qfProof = consts.foldLeft(ProvableSig.startProof(fnified, defs))({
          case (p, c) => p(
            FOQuantifierTactics.allInstantiateInverse(c)(SuccPos(0)) andThen
            ProofRuleTactics.skolemizeR(SuccPos(0)), 0)
        })(qfVarifiedProof, 0)

        val Equiv(_, qfResult) = qfProof.conclusion.succ.head
        postQE(qfResult, i)
        qfProof
      })

      def mergeDisjuncts(pr: List[ProvableSig]): ProvableSig = pr match {
        case p :: Nil => p
        case _ =>
          val (l, r) = pr.splitAt(pr.size/2)
          val lproof = mergeDisjuncts(l)
          val rproof = mergeDisjuncts(r)
          val Equiv(Exists(x, p), pqf) = lproof.conclusion.succ.head
          val Equiv(Exists(y, q), qqf) = rproof.conclusion.succ.head
          assert(x == y)
          val dot = DotTerm()
          val merged = ProvableSig.startProof(Equiv(Exists(x, Or(p, q)), Or(pqf, qqf)), defs)(
            CEat(RenUSubst(List(
              (PredOf(Function("p_", None, Real, Bool), dot), p.replaceFree(x.head, dot)),
              (PredOf(Function("q_", None, Real, Bool), dot), q.replaceFree(x.head, dot)),
              (Variable("x_"), x.head))).toForward(Ax.existsOr.provable), PosInExpr(List(0)))(SuccPosition.base0(0, PosInExpr(List(0)))), 0)(
            CEat(lproof, PosInExpr(List(0)))(SuccPosition.base0(0, PosInExpr(List(0, 0)))), 0)(
            CEat(rproof, PosInExpr(List(0)))(SuccPosition.base0(0, PosInExpr(List(0, 1)))), 0)(
            Ax.equivReflexive.provable(USubst(List(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), Or(pqf, qqf))))), 0)
          assert(merged.isProved, "Expected closed merge proof, but got open goals")
          merged
          //@todo
          //timed(tool.simplify(d, assumptions), "Simplifying")
      }

      val mergedProof = timed(simplifyEquivProof(mergeDisjuncts(componentResults)), "Merging QE component results")
      assert(mergedProof.isProved, "Expected a finished merge proof, but proof not closed")
      val merged@Equiv(lq, rqf) = mergedProof.conclusion.succ.head
      assert(StaticSemantics.boundVars(rqf).isEmpty, "Expected all quantifiers eliminated, but formula still has quantifiers: " + rqf.prettyString)

      val (reassociated, reassociateProof) = timed({
        val Exists(x, l) = lq
        val (lr, lp) = PropositionalTactics.rightAssociate(l)
        val (rr, rp) = PropositionalTactics.rightAssociate(rqf)
        val result = Equiv(Exists(x, lr), rr)
        val resultEquiv = Equiv(merged, result)
        val subst = USubst(List(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), result)))
        val proof = timed(ProvableSig.startProof(resultEquiv, defs)(
          CEat(lp, PosInExpr(List(0)))(SuccPosition.base0(0, PosInExpr(List(0, 0, 0)))), 0)(
          CEat(rp, PosInExpr(List(0)))(SuccPosition.base0(0, PosInExpr(List(0, 1)))), 0)(
          Ax.equivReflexive.provable(subst), 0), "Applying reassociate subproofs")

        assert(proof.isProved, "Expected a finished reassociation proof, but proof not closed")
        (resultEquiv, proof)
      }, "Reassociating")

      val Equiv(_, Equiv(_, qfResult)) = reassociated
      val es = StaticSemantics.symbols(exists)
      val qfs = StaticSemantics.symbols(qfResult)

      val expand = monitorComponents.zip(componentResults).map({ case (o, qfProof) =>
        val Equiv(_, qf) = qfProof.conclusion.succ.head
        StaticSemantics.symbols(o) -- StaticSemantics.symbols(qf)
      }).reduce(_ ++ _)

      println("Symbols: " + es.mkString(",") + "\nQF symbols: " + qfs.mkString(",") + "\nDiff: " + expand.mkString(","))
      val subst = USubst(defs.substs.filter({ case SubstitutionPair(what, _) => StaticSemantics.symbols(what).intersect(expand).nonEmpty }))
      println("Substitution: " + subst.subsDefsInput.mkString(","))

      val innerProof = timed(ProvableSig.startProof(Equiv(exists, qfResult), defs)(
        CEat(dnfProof, PosInExpr(List(0)))(SuccPosition.base0(0, PosInExpr(List(0, 0)))), 0)(
        PropositionalTactics.rightAssociate(SuccPosition.base0(0, PosInExpr(List(0, 0)))), 0)(
        subst)(
        CEat(reassociateProof(subst), PosInExpr(List(1)))(SuccPosition.base0(0)), 0)(
        mergedProof(subst), 0), "Inner proof")
      assert(innerProof.isProved, "Expected closed inner proof, but got open goals")

      val innermostPos = innermostQuantifierPos(fml)
      println("Finished quantifier " + x + " at " + innermostPos.prettyString + ", advancing outwards")

      val outerProof = stepwisePartialQE(ctx(qfResult), assumptions, defs, tool)(subst)
      val Equiv(_, outerQf) = outerProof.conclusion.succ.head

      val outerExpand = StaticSemantics.symbols(ctx(qfResult)) -- StaticSemantics.symbols(outerQf)
      val outerSubst = USubst(defs.substs.filter({ case SubstitutionPair(what, _) => StaticSemantics.symbols(what).intersect(outerExpand).nonEmpty }))

      val innerPos = PosInExpr(List(0)) ++ innermostPos
      timed(ProvableSig.startProof(Equiv(fml, outerQf), defs)(
        subst)(
        CEat(innerProof, PosInExpr(List(0)))(SuccPosition.base0(0, innerPos)), 0)(
        outerSubst)(
        outerProof, 0), "Combining inner and outer proof")
    case (ctx, p: Forall) =>
      //@todo conjunctive normal form and split
      val innerProof = ModelPlex.mxPartialQE(p, defs, tool)
      val Equiv(_, qf) = innerProof.conclusion.succ.head

      val innerExpand = StaticSemantics.symbols(p) -- StaticSemantics.symbols(qf)
      val innerSubst = USubst(defs.substs.filter({
        case SubstitutionPair(what, _) => StaticSemantics.symbols(what).intersect(innerExpand).nonEmpty
      }))

      //@todo
      //stepwisePartialQE(ctx(timed(tool.simplify(qf, assumptions), "QE 1/1")), assumptions, defs, tool)
      val outerProof = stepwisePartialQE(ctx(qf), assumptions, defs, tool)(innerSubst)
      val Equiv(_, outerQf) = outerProof.conclusion.succ.head

      val outerExpand = StaticSemantics.symbols(ctx(qf)) -- StaticSemantics.symbols(outerQf)
      val outerSubst = USubst(defs.substs.filter({
        case SubstitutionPair(what, _) => StaticSemantics.symbols(what).intersect(outerExpand).nonEmpty
      }))

      val innerPos = PosInExpr(List(0)) ++ innermostQuantifierPos(fml)
      ProvableSig.startProof(Equiv(fml, outerQf), defs)(
        innerSubst)(
        CEat(innerProof, PosInExpr(List(0)))(SuccPosition.base0(0, innerPos)), 0)(
        outerSubst)(
        outerProof, 0)
    case (ctx, f) => ProvableSig.startProof(Equiv(ctx(f), ctx(f)), defs)(byUS(Ax.equivReflexive.provable), 0)
  }

  /** Opt. 1 from Mitsch, Platzer: ModelPlex, i.e., instantiates existential quantifiers with an equal term phrased
    * somewhere in the quantified formula.
    *
    * @example {{{
    *           |- xpost>0 & xpost=xpost
    *           ------------------------------optimizationOneWithSearch
    *           |- \exists x x>0 & xpost=x
    * }}}
    * @see[[optimizationOneWithSearchAt]]
    */
  override def optimizationOneWithSearch(tool: Option[SimplificationTool], assumptions: List[Formula],
                                         unobservable: List[_ <: NamedSymbol],
                                         simplifier: Option[BuiltInPositionTactic],
                                         postVar: Variable=>Variable = NAMED_POST_VAR): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    val positions = new ListBuffer[PosInExpr]()

    sequent.sub(pos) match {
      case Some(fml) =>
        ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
            case _: Quantified =>
              positions += p
              Left(None)
            case _ => Left(None)
          }
        }, fml)
    }

    positions.map(p => instantiateQuantifiers(tool, assumptions, unobservable, simplifier, postVar)(pos ++ p)).
      reduceRightOption[BelleExpr](_ & _).getOrElse(skip) & simplifier.map(_(pos)).getOrElse(skip)
  })

  /** Returns the polarity at `pos` in the `sequent`.
    * @return <0 for positive polarity if antecedent, negative polarity in succedent;
    *         >0 for negative polarity in antecedent, positive polarity in succedent
    */
  private def polarityInSeq(sequent: Sequent, pos: Position): Int = {
    (if (pos.isSucc) 1 else -1)*FormulaTools.polarityAt(sequent(pos.top), pos.inExpr)
  }

  private def solutionQE(existsFml: Formula, qeFml: Formula, signature: Set[Function],
                         assumptions: List[Formula], tool: Option[SimplificationTool])(pp: Position) = tool match {
    case None => skip
    case Some(t) =>
      val simplified = t.simplify(qeFml, assumptions)
      val backSubst = And(
        assumptions.reduceOption(And).getOrElse(True),
        signature.foldLeft[Formula](simplified)((fml, t) => fml.replaceAll(Variable(t.name, t.index), FuncOf(t, Nothing))))
      val pqe = proveBy(Imply(backSubst, existsFml), QE & done)
      cutAt(backSubst)(pp) < (skip, (if (pp.isSucc) cohideR(pp.topLevel) else cohideR('Rlast)) & CMon(pp.inExpr) & by(pqe))
  }

  private def instantiateQuantifiers(tool: Option[SimplificationTool],
                                     assumptions: List[Formula],
                                     unobservable: List[_ <: NamedSymbol],
                                     simplifier: Option[BuiltInPositionTactic],
                                     postVar: Variable=>Variable): DependentPositionTactic =
    anon ((pos: Position, sequent: Sequent) => {
      def instantiateODESolution(odeShape: Exists): BelleExpr = {
        val signature = StaticSemantics.signature(odeShape).filter({
          case Function(_, _, Unit, _, false) => true case _ => false }).map(_.asInstanceOf[Function])
        val edo = signature.foldLeft[Formula](odeShape)((fml, t) => fml.replaceAll(FuncOf(t, Nothing), Variable(t.name, t.index)))
        val transformed = proveBy(edo, partialQE)
        solutionQE(odeShape, transformed.subgoals.head.succ.head, signature, assumptions, tool)(pos) & simplifier.map(_(pos)).getOrElse(skip) |
          solutionQE(odeShape, transformed.subgoals.head.succ.head, signature, Nil, tool)(pos) & simplifier.map(_(pos)).getOrElse(skip) |
          simplifier.map(_(pos ++ PosInExpr(0::Nil))).getOrElse(skip)
      }

      sequent.sub(pos) match {
        case Some(Forall(xs, p)) if StaticSemantics.freeVars(p).intersect(xs.toSet).isEmpty => allV(pos)
        case Some(Exists(xs, p)) if StaticSemantics.freeVars(p).intersect(xs.toSet).isEmpty => existsV(pos)
        case Some(Forall(xs, Imply(Equal(x, y), q))) =>
          if (polarityInSeq(sequent, pos) > 0 && xs.contains(x) && StaticSemantics.boundVars(q).intersect(StaticSemantics.freeVars(y)).isEmpty) {
            useAt(simplForall1, PosInExpr(1::Nil))(pos) & simplifier.map(_(pos)).getOrElse(skip)
          } else if (polarityInSeq(sequent, pos) > 0 && xs.contains(y) && StaticSemantics.boundVars(q).intersect(StaticSemantics.freeVars(x)).isEmpty) {
            useAt(simplForall2, PosInExpr(1::Nil))(pos) & simplifier.map(_(pos)).getOrElse(skip)
          } else skip
        // @note shapes of ode solution
        case Some(ode@Exists(t::Nil, And(GreaterEqual(_, _), And(Forall(s::Nil, Imply(And(_, _), _)), q))))
          if tool.isDefined && polarityInSeq(sequent, pos) > 0 && t == "t_".asVariable && s == "s_".asVariable && StaticSemantics.boundVars(q).isEmpty =>
          instantiateODESolution(ode)
        case Some(ode@Exists(t::Nil, And(GreaterEqual(_, _), q)))
          if tool.isDefined && polarityInSeq(sequent, pos) > 0 && t == "t_".asVariable && StaticSemantics.boundVars(q).isEmpty =>
          instantiateODESolution(ode)
        case Some(e: Exists) if polarityInSeq(sequent, pos) > 0 /*&& StaticSemantics.boundVars(q).isEmpty*/ =>
          val unobservableVars = unobservable.map({
            case v: Variable => v
            case Function(n, i, _, s, _) => Variable(n, i, s)
          })
          findWitness(sequent, pos, unobservableVars, simplifier, postVar) match {
            case Some(w) => optimizationOneAt(unobservableVars, Some(w), postVar)(pos) & simplifier.map(_(pos)).getOrElse(skip)
            case None => skip
          }
        case Some(Forall(_, _)) if polarityInSeq(sequent, pos) < 0 =>
          //@todo: Some(optimizationOneWithSearchAt(unobservable, simplifier)(pp)) not implemented for Forall
          skip
        case fml => skip
      }
  })

  /** Finds a witness for the quantifier at position. */
  private def findWitness(sequent: Sequent, pos: Position,
                          unobservableVars: List[Variable],
                          simplifier: Option[BuiltInPositionTactic],
                          postVar: Variable=>Variable): Option[(Variable, Term)] = {
    //@note assumes that conjecture created existentially quantified variables for unobservable parameters (functions)
    val (ctx, quant) = sequent.at(pos)
    quant match {
      case Exists(vars, And(Equal(l, r), q)) if polarityInSeq(sequent, pos) > 0 && vars.contains(l) &&
        (unobservableVars ++ unobservableVars.map(postVar)).intersect(vars).isEmpty && StaticSemantics.boundVars(q).intersect(StaticSemantics.freeVars(r)).isEmpty =>
        // case from deterministic assignments
        Some(l.asInstanceOf[BaseVariable] -> r)
      case Forall(vars, Imply(Equal(l, r), q)) if polarityInSeq(sequent, pos) < 0 && vars.contains(l) &&
        (unobservableVars ++ unobservableVars.map(postVar)).intersect(vars).isEmpty && StaticSemantics.boundVars(q).intersect(StaticSemantics.freeVars(r)).isEmpty =>
        Some(l.asInstanceOf[BaseVariable] -> r)
      case Exists(vars, phi) if polarityInSeq(sequent, pos) > 0 =>
        // case from nondeterministic assignments

        class SynonymFinder(v: Variable) extends ExpressionTraversalFunction {
          private val vs = if (v.name.endsWith("_")) List(v) else List(v, postVar(v))
          var synonyms: mutable.Map[Variable, Set[Term]] = mutable.Map(vs.map(_ -> Set[Term]()):_*)
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
            case Equal(l: Variable, r: Variable) =>
              if (vs.contains(l)) synonyms(l) = synonyms(l) + r
              if (vs.contains(r)) synonyms(r) = synonyms(r) + l
              Left(None)
            case Equal(l: Variable, r) if vs.contains(l) => synonyms(l) = synonyms(l) + r; Left(None)
            case Equal(l, r: Variable) if vs.contains(r) => synonyms(r) = synonyms(r) + l; Left(None)
            case Or(l, r) =>
              val lFinder = new SynonymFinder(v)
              val rFinder = new SynonymFinder(v)
              ExpressionTraversal.traverse(lFinder, l)
              ExpressionTraversal.traverse(rFinder, r)
              val vSyns = lFinder.flattenSynonyms(v).intersect(rFinder.flattenSynonyms(v))
              val vPostSyns = lFinder.flattenSynonyms(postVar(v)).intersect(rFinder.flattenSynonyms(postVar(v)))
              val newSyns = Map(v -> vSyns, postVar(v) -> vPostSyns)
              synonyms = synonyms.map({ case (key, value) => key -> value.union(newSyns(key)) })
              Right(e)
            case _ => Left(None)
          }

          def flattenSynonyms(of: Variable): Set[Term] = {
            //@note if v synonyms empty but vpost contains a term: then v=f(vpost) because vpost synonyms are result of [:=] subst
            if (synonyms(v).isEmpty && synonyms.contains(postVar(v))) {
              synonyms(v) = synonyms(postVar(v)).map(s =>
                if (!StaticSemantics.freeVars(s).contains(v)) {
                  s
                } else {
                  val Equal(_, syn) = ToolProvider.solverTool() match {
                    case Some(t) => t.solve(Equal(postVar(v), s), List(v)).getOrElse(Equal(v, s))
                    case None => Equal(v, s) //@note filtered afterwards
                  }
                  syn
                }
              ).filter(s => !StaticSemantics.freeVars(s).contains(v))
            }
            val direct = synonyms(of)
            val transitive1 = direct.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable]).flatMap(synonyms.getOrElse(_, Set()))
            val transitive2 = direct.flatMap(s => synonyms.filterKeys(k => synonyms.getOrElse(k, Set()).contains(s)).keySet)
            (direct ++ transitive1 ++ transitive2) - of
          }
        }

        val v = vars.head
        val vFinder = new SynonymFinder(v)
        ExpressionTraversal.traverse(vFinder, phi)

        //@note prefer x=xpost over first synonym, if no synonyms found instantiate with "xpost"
        val synonyms = vFinder.flattenSynonyms(v)
        val postEquality = {
          //@note conjecture for unobservable variables always created by named post variable since not observable over multiple states in the sliding window, see [[createSlidingMonitorSpec]]
          if (unobservableVars.contains(v) && !v.name.endsWith("_")) synonyms.find({ case r: BaseVariable => NAMED_POST_VAR(v) == r case _ => false })
          else if (unobservableVars.filterNot(_.name.endsWith("_")).map(NAMED_POST_VAR).contains(v)) synonyms.find({ case r: BaseVariable => NAMED_POST_VAR(r) == v case _ => false })
          else synonyms.find({ case r: BaseVariable => postVar(v) == r || postVar(r) == v case _ => false })
        }
        val equality: Option[Term] = postEquality match {
          case Some(_) if unobservableVars.intersect(vars).isEmpty => postEquality
          case _ =>
            if (unobservableVars.intersect(vars).nonEmpty) {
              //@note existential quantifier of an unobservable variable, e.g., \exists x ..., can instantiate x with terms that mention neither x nor xpost
              synonyms.find(StaticSemantics.freeVars(_).intersect(unobservableVars.toSet ++ Set(v, postVar(v))).isEmpty)
            } else {
              //@note existential quantifier of anything else; includes unobservable post variable e.g., \exists x .... \exists xpost ..., can instantiate xpost with anything observable or quantified unobservable
              synonyms.find(StaticSemantics.freeVars(_).intersect(unobservableVars.toSet -- StaticSemantics.boundVars(ctx(False)).toSet).isEmpty)
            }
        }
        //@note unobservable-post synonym is allowed to mention other unobservable variables, e.g. \exists x ... \exists xpost xpost=x+y*t
        if (StaticSemantics.boundVars(phi).intersect(equality.map(StaticSemantics.freeVars).getOrElse(SetLattice.bottom)).isEmpty) {
          equality.map(v -> _)
        } else None
      case e => throw new TacticInapplicableFailure("Finding witnesses only supported for existential quantifiers, but got " + e.prettyString)
    }
  }

  /** Opt. 1 at a specific position */
  private def optimizationOneAt(unobservable: List[Variable], inst: Option[(Variable, Term)] = None,
                                postVar: Variable=>Variable = NAMED_POST_VAR): DependentPositionTactic = anon ((pos: Position, sequent: Sequent) => {
    // was "Optimization 1"
    sequent.sub(pos) match {
      case Some(Exists(vars, q)) if polarityInSeq(sequent, pos) > 0 => inst match {
        case Some((what, repl)) =>
          if (StaticSemantics.boundVars(q).intersect(StaticSemantics.freeVars(repl)).isEmpty) existsR(what, repl)(pos)
          else throw new IllFormedTacticApplicationException("Unable to instantiate because instance " +
            repl.prettyString + " is bound in " + q.prettyString)
        case None if (unobservable ++ unobservable.map(postVar)).intersect(vars).isEmpty =>
          // existential quantifier from non-deterministic assignment
          require(vars.size == 1)
          val (v, post) = vars.map(v => (v, postVar(v))).head
          if (StaticSemantics.boundVars(q).intersect(StaticSemantics.freeVars(post)).isEmpty) existsR(v, post)(pos)
          else nil
        case None => nil
      }
      case Some(Forall(vars, q)) if polarityInSeq(sequent, pos) < 0 => inst match {
        case Some((what, repl)) =>
          if (StaticSemantics.boundVars(q).intersect(StaticSemantics.freeVars(repl)).isEmpty) allL(what, repl)(pos)
          else throw new IllFormedTacticApplicationException("Unable to instantiate because instance " + repl.prettyString + " is bound in " + q.prettyString)
        case None if (unobservable ++ unobservable.map(postVar)).intersect(vars).isEmpty =>
          require(vars.size == 1)
          val (v, post) = vars.map(v => (v, postVar(v))).head
          if (StaticSemantics.boundVars(q).intersect(StaticSemantics.freeVars(post)).isEmpty) allL(v, post)(pos)
          else nil
        case None => nil
      }
      case Some(e) => throw new TacticInapplicableFailure("Optimization 1 only applicable to existential quantifier in positive polarity or universal quantifier in negative polarity, but got " + e.prettyString + " with polarity " + polarityInSeq(sequent, pos))
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
  })

  /** Simplifies reflexive comparisons and implications/conjunctions/disjunctions with true. */
  // was "ModelPlex Simplify"
  lazy val mxSimplify: BuiltInPositionTactic = SimplifierV3.simpTac(
    taxs = SimplifierV3.composeIndex(SimplifierV3.groundEqualityIndex, SimplifierV3.defaultTaxs),
    faxs = SimplifierV3.defaultFaxs
  )

  private def toMetricT(fml: Formula): BelleExpr = {
    val cmpNF = chase(3, 3, (e: Expression) => e match {
      case And(_, _) => Ax.andRecursor::Nil
      case Or(_, _) => Ax.orRecursor::Nil
      case NotEqual(_, _) => Ax.notEqualExpand::Nil
      case Equal(_, _) => Ax.equalExpand::Nil
      case _ => Nil
    })

    val arithNF = chase(3, 3, (e: Expression) => e match {
      case And(_,_) => Ax.andRecursor::Nil
      case Or(_,_) => Ax.orRecursor::Nil
      case Less(Number(n), _) if n == 0 => Ax.metricLt::Nil
      case LessEqual(Number(n), _) if n == 0 => Ax.metricLe::Nil
      case Greater(_, _) => Ax.gtNeg::Nil
      case GreaterEqual(_, _) => Ax.geNeg::Nil
      case _ => Nil
    })

    def aiTupled(ai: AxiomInfo): (ProvableSig, PosInExpr, List[PosInExpr]) = (ai.provable, ai.key, ai.recursor)

    val propNF = chaseCustom({
      case LessEqual(_, _) => aiTupled(Ax.leApprox)::Nil
      case And(Less(_, _), Less(_, _)) => aiTupled(Ax.metricAndLt)::Nil
      case And(LessEqual(_, _), LessEqual(_, _)) => aiTupled(Ax.metricAndLe)::Nil
      case And(LessEqual(_, _), Less(_, _)) => aiTupled(Ax.andRecursor)::Nil
      case And(Less(_, _), LessEqual(_, _)) => aiTupled(Ax.andRecursor)::Nil
      case And(_: BinaryCompositeFormula, _: BinaryCompositeFormula) => aiTupled(Ax.andRecursor)::Nil
      case And(_: BinaryCompositeFormula, _) => (Ax.andRecursor.provable, PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)::Nil
      case And(_, _: BinaryCompositeFormula) => (Ax.andRecursor.provable, PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)::Nil
      case Or(Less(_, _), Less(_, _)) => aiTupled(Ax.metricOrLt)::Nil
      case Or(LessEqual(_, _), LessEqual(_, _)) => aiTupled(Ax.metricOrLe)::Nil
      case Or(LessEqual(_, _), Less(_, _)) => aiTupled(Ax.orRecursor)::Nil
      case Or(Less(_, _), LessEqual(_, _)) => aiTupled(Ax.orRecursor)::Nil
      case Or(_: BinaryCompositeFormula, _: BinaryCompositeFormula) => aiTupled(Ax.orRecursor)::Nil
      case Or(_: BinaryCompositeFormula, _) => (Ax.orRecursor.provable, PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)::Nil
      case Or(_, _: BinaryCompositeFormula) => (Ax.orRecursor.provable, PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)::Nil
      case _ => Nil
    })

    val normTactic = SimplifierV3.semiAlgNormalizeUnchecked(fml) match {
      case (_, Some(p)) => useAt(p, PosInExpr(0::Nil))(1)
      case (_, None) => skip
    }

    normTactic & cmpNF(1) & arithNF(1) &
      SaturateTactic(SimplifierV3.simplify(1)) /* until Simplifier saturates by itself */ &
      Idioms.repeatWhile(_.isInstanceOf[BinaryCompositeFormula])(propNF(1))(1)
  }

  /** Turns the formula `fml` into a single inequality. */
  def toMetric(fml: Formula): Formula = {
    val result = proveBy(fml, toMetricT(fml))
    assert(result.subgoals.length == 1 && result.subgoals.head.ante.isEmpty && result.subgoals.head.succ.length == 1)
    result.subgoals.head.succ.head
  }
}
