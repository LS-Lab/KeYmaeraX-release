/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.StopTraversal
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._

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
object ModelPlex extends ModelPlexTrait {

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
      case 'ctrl => modelplexAxiomaticStyle(useOptOne=true)(controllerMonitorT)('R)
      case 'model => modelplexAxiomaticStyle(useOptOne=true)(modelMonitorT)('R)
      case _ => throw new IllegalArgumentException("Unknown monitor kind " + kind + ", expected one of 'ctrl or 'model")
    }

    val proofStart = Platform.currentTime
    val result = TactixLibrary.proveBy(Provable.startProof(mxInputSequent), tactic)
    val proofDuration = Platform.currentTime - proofStart
    Console.println("[proof time " + proofDuration + "ms]")

    assert(result.subgoals.size == 1 && result.subgoals.head.ante.size == 1 &&
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
   * @param fml A formula of the form p -> [a]q, which was proven correct.
   * @param vars A list of variables V, superset of BV(a).
   * @see Mitsch, Platzer: ModelPlex (Definition 3, Lemma 4, Corollary 1).
   */
  def createMonitorSpecificationConjecture(fml: Formula, vars: Variable*): Formula = {
    require(vars.nonEmpty, "ModelPlex expects non-empty list of variables to monitor")
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
  def controllerMonitorByChase: DependentPositionTactic = chase(3,3, (e:Expression) => e match {
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
  def modelplexSequentStyle: DependentPositionTactic = ???
//    new PositionTactic("Modelplex Sequent-Style") {
//    override def applies(s: Sequent, p: Position): Boolean = s(p.top) match {
//      case Imply(_, Diamond(_, _)) => true
//      case _ => false
//    }
//
//    def apply(p: Position): Tactic = new ConstructionTactic(name) {
//      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
//
//      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
//        Some(ImplyRightT(p) & ((AxiomCloseT |
//          (debugT("Before HP") &
//            (locateSucc(diamondSeqT) | locateSucc(diamondChoiceT) | locateSucc(diamondNDetAssign) |
//              locateSucc(diamondTestRetainConditionT) | locateSucc(diamondAssignEqualT) |
//              locateSucc(substitutionDiamondAssignT) | locateSucc(v2vAssignT) |
//              locateSucc(diamondDiffSolve2DT)) &
//            debugT("After  HP") &
//            ((locateSucc(mxPropositionalRightT) | locateSucc(optimizationOneAt()) | locateAnte(PropositionalLeftT) |
//              locateAnte(optimizationOneAt()))*)
//            )
//          )*)
//        )
//      }
//    }
//  }

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
                             (unprog: Boolean => DependentPositionTactic): DependentPositionTactic = "Modelplex In-Place" by ((pos, sequent) => {
    sequent.sub(pos) match {
      case Some(Imply(_, Diamond(_, _))) =>
        implyR(pos) & ((debug("Before HP") & unprog(useOptOne)(pos) & debug("After  HP"))*@TheType()) &
          debug("Done with transformation, now looking for quantifiers") &
          //?(atOutermostQuantifier(ToolTactics.partialQE)(pos)) &
          //?(ToolTactics.partialQE) &
          debug("Modelplex done")
    }
  })

  /**
   * Returns a backward tactic for deriving controller monitors. Uses Opt. 1 immediately after nondeterministic
   * assignments if useOptOne, avoids Opt. 1 at intermediate steps if !useOptOne.
   * @param useOptOne Indicates whether or not to use Opt. 1 at intermediate steps.
   * @return The tactic.
   */
  def controllerMonitorT(useOptOne: Boolean): DependentPositionTactic =
    "Axiomatic controller monitor" by (pos =>
      locateT(
        useAt("<*> approx", PosInExpr(1::Nil)) ::
        useAt("DX diamond differential skip", PosInExpr(1::Nil)) ::
        useAt("<;> compose") ::
        useAt("<++> choice") ::
        ("<:*> nondet assign opt. 1" by (p => useAt("<:*> assign nondet")(p) & (if (useOptOne) optimizationOne()(p) else skip))) ::
        useAt("<?> test") ::
        useAt("<:=> assign") ::
        ("<:=> assign opt. 1" by (p => useAt("<:=> assign equality")(p) & (if (useOptOne) optimizationOne()(p) else skip))) ::
//          substitutionDiamondAssignT ::
//          v2vAssignT ::
//          (diamondAssignEqualT & (if (useOptOne) optimizationOne() else skip)) ::
//          (diamondDiffSolve2DT & (if (useOptOne) optimizationOne() else skip)) ::
//          boxAssignBaseT ::
        Nil)(pos))

  /**
   * Returns a backward tactic for deriving model monitors. Uses Opt. 1 immediately after nondeterministic
   * assignments if useOptOne, avoids Opt. 1 at intermediate steps if !useOptOne.
   * @param useOptOne Indicates whether or not to use Opt. 1 at intermediate steps.
   * @return The tactic.
   */
  def modelMonitorT(useOptOne: Boolean): DependentPositionTactic = ???
//    locateT(diamondSeqT :: useAt("<*> approx", PosInExpr(1::Nil)) :: Nil) &
//      locateT(
//        useAt("<*> approx", PosInExpr(1::Nil)) ::
//          diamondSeqT ::
//          diamondChoiceT ::
//          (diamondNDetAssign & (if (useOptOne) optimizationOne() else NilPT)) ::
//          diamondTestT ::
//          substitutionDiamondAssignT ::
//          v2vAssignT ::
//          (diamondAssignEqualT & (if (useOptOne) optimizationOne() else NilPT)) ::
//          (diamondDiffSolve2DT & (if (useOptOne) optimizationOne() else NilPT)) ::
//          boxAssignBaseT ::
//          Nil)

  /** Propositional tactic that avoids branching in formulas without modalities. */
  private def mxPropositionalRightT: DependentPositionTactic = "Modelplex Propositional Right" by ((pos, sequent) => {
    ???
//    var containsPrg = false
//    sequent(pos.top) match {
//      // only apply to formulas that contain programs
//      case f: Formula => ExpressionTraversal.traverse(new ExpressionTraversalFunction {
//        override def preP(p: PosInExpr, prg: Program): Either[Option[StopTraversal], Program] = {
//        containsPrg = true
//        Left(Some(ExpressionTraversal.stop))
//        }
//        }, f)
//      case _ => // nothing to do
//    }
//    require(containsPrg, "Foo")
//    PropositionalRightT(p)
  })

  /** Performs tactic t at the outermost quantifier underneath position p, if any. */
  private def atOutermostQuantifier(t: DependentPositionTactic): DependentPositionTactic = "ModelPlex at outermost quantifier" by ((pos, sequent) => {
    require(positionOfOutermostQuantifier(sequent, pos).isDefined, "Bar")
    positionOfOutermostQuantifier(sequent, pos) match {
      case Some(pos) => t(pos)
      case None => skip
    }
  })

  /**
   * Returns a tactic to solve two-dimensional differential equations. Introduces constant function symbols for
   * variables that do not change in the ODE, before it hands over to the actual diff. solution tactic.
   * @return The tactic.
   */
  def diamondDiffSolve2DT: DependentPositionTactic = "<','> differential solution" by ((pos, sequent) => {
    ??? //(diffIntroduceConstantT & ODETactics.diamondDiffSolve2DT)(p)
  })

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
  def diamondTestRetainConditionT: DependentPositionTactic = ???
//    new PositionTactic("<?H> modelplex test") {
//    //@todo introduce a derived axiom
//    override def applies(s: Sequent, p: Position): Boolean = s(p.top).subFormulaAt(p.inExpr) match {
//      case Some(Diamond(Test(_), _)) => true
//      case _ => false
//    }
//
//    def apply(p: Position): Tactic = new ConstructionTactic(name) {
//      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
//
//      def constructCut(f: Formula) = ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
//        override def preF(p: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
//          case Diamond(Test(h), phi) => Right(And(h, Imply(h, phi)))
//          case _ => Left(Some(ExpressionTraversal.stop))
//        }
//      }), f)
//
//      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
//        node.sequent(p.top).subFormulaAt(p.inExpr) match {
//          case Some(Diamond(Test(h), phi)) =>
//            Some(
//              diamondTestT(p) &
//                cutT(constructCut(node.sequent(p))) & onBranch(
//                (cutUseLbl, debugT("use cut") & ((AxiomCloseT | locateAnte(PropositionalLeftT) | locateSucc(PropositionalRightT))*)
//                  & debugT("Modelplex: Expected axiom close, but did not close")),
//                (cutShowLbl, debugT("show cut") & hideT(p.topLevel))
//              )
//            )
//        }
//      }
//    }
//  }

  /**
   * Performs a tactic from the list of tactics that is applicable somewhere underneath position p in sequent s,
   * taking the outermost such sub-position of p. Formulas only.
   * @example{{{
   *           |- a=1 & (<x:=2;>x+y>0 & <y:=3;>x+y>0)
   *           ---------------------------------------locateT(diamondSeqT :: diamondChoiceT :: Nil)(1)
   *           |- a=1 & <x:=2; ++ y:=3;>x+y>0
   * }}}
   * @param tactics The list of tactics.
   * @return The tactic.
   */
  def locateT(tactics: List[DependentPositionTactic]): DependentPositionTactic = "Modelplex Locate" by ((pos, sequent) => {
    require(tactics.nonEmpty, "At least 1 tactic required")
    val here = tactics.map(_(pos) partial).reduceRight[BelleExpr]((t, comp) => (t | comp) partial)

    def recurseOnFormula(p: Position) = sequent.sub(p) match {
      case Some(_: Formula) => locateT(tactics)(p) partial
      case _ => DebuggingTactics.error("Stop recursion")
    }

    val left: BelleExpr = recurseOnFormula(pos + PosInExpr(0::Nil))
    val right: BelleExpr = recurseOnFormula(pos + PosInExpr(1::Nil))

    ((here partial) | (((left partial) | (right partial)) partial)) partial
  })

  /** Returns the position of the outermost universal quantifier underneath position p in sequent s, if any. None otherwise. */
  private def positionOfOutermostQuantifier(s: Sequent, p: Position): Option[Position] = {
    var outermostPos: Option[Position] = None
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = f match {
        case Forall(_, _) =>
          outermostPos = Some(p + pos)
          Left(Some(ExpressionTraversal.stop))
        case _ => Left(None)
      }
    }, s.sub(p).getOrElse(throw new IllegalArgumentException("Formula " + s(p.top) + " is not a formula at sub-position " + p.inExpr)).asInstanceOf[Formula])
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
  def optimizationOneWithSearch: DependentPositionTactic = locateT(optimizationOneWithSearchAt::Nil)

  /** Opt. 1 at a specific position, i.e., instantiates the existential quantifier with an equal term phrased
    * somewhere in the quantified formula. */
  private def optimizationOneWithSearchAt: DependentPositionTactic = "Optimization 1 with instance search" by ((pos, sequent) => {
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
  private def optimizationOneAt(inst: Option[(Variable, Term)] = None): DependentPositionTactic = "Optimization 1" by ((pos, sequent) => {
    sequent.sub(pos) match {
      case Some(Exists(vars, phi)) if pos.isSucc => inst match {
          case Some(i) => debug("Foo") & existsR(i._1, i._2)(pos) & debug("Bar")
          case None =>
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, Function(s"${v.name}post", Some(0), Unit, v.sort))).head
            val postFn = FuncOf(post, Nothing)
            existsR(v, postFn)(pos)
        }
        case Some(Forall(vars, phi)) if pos.isAnte => inst match {
          case Some(i) => allL(i._1, i._2)(pos)
          case None =>
            require(vars.size == 1)
            val (v, post) = vars.map(v => (v, Function(s"${v.name}post", Some(0), Unit, v.sort))).head
            val postFn = FuncOf(post, Nothing)
            allL(v, postFn)(pos)
        }
    }
  })
}