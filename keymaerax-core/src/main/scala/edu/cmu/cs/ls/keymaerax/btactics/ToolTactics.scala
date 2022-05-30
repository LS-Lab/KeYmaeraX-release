package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics.toSingleFormula
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, InterpretedSymbols, TacticReservedSymbols}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.{MathematicaComputationAbortedException, MathematicaInapplicableMethodException, SMTQeException, SMTTimeoutException, ToolOperationManagement}
import edu.cmu.cs.ls.keymaerax.tools.ext.QETacticTool
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec

import scala.annotation.tailrec
import scala.math.Ordering.Implicits._
import scala.collection.immutable._
import scala.util.{Failure, Success, Try}

/**
 * Implementation: Tactics that execute and use the output of tools.
 * Also contains tactics for pre-processing sequents.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
private object ToolTactics {

  private val namespace = "tooltactics"

  @Tactic("useSolver", codeName = "useSolver")
  // NB: anon (Sequent) is necessary even though argument "seq" is not referenced:
  // this ensures that TacticInfo initialization routine can initialize byUSX without executing the body
  def switchSolver(tool: String): InputTactic = inputanon { _: Sequent => {
    val config = ToolConfiguration.config(tool)
    tool.toLowerCase match {
      case "mathematica" =>
        ToolProvider.setProvider(MultiToolProvider(MathematicaToolProvider(config) :: Z3ToolProvider() :: Nil))
        if (!ToolProvider.isInitialized) throw new TacticAssertionError("Failed to switch to Mathematica: unable to initialize the connection; the license may be expired.")
      case "wolframengine" =>
        Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, "true", saveToFile = false)
        ToolProvider.setProvider(MultiToolProvider(WolframEngineToolProvider(config) :: Z3ToolProvider() :: Nil))
        if (!ToolProvider.isInitialized) throw new TacticAssertionError("Failed to switch to Wolfram Engine: unable to initialize the connection; the license may be expired (try starting Wolfram Engine from the command line to renew the license)")
      case "z3" =>
        ToolProvider.setProvider(new Z3ToolProvider)
        if (!ToolProvider.isInitialized) throw new TacticAssertionError("Failed to switch to Z3: unable to initialize the connection; please check the configured path to Z3")
      case _ => throw new InputFormatFailure("Unknown tool " + tool + "; please use one of mathematica|wolframengine|z3")
    }
    Idioms.nil
  }}

  /** Assert that there is no counter example. skip if none, error if there is. */
  // was  "assertNoCEX"
  lazy val assertNoCex: BuiltInTactic = anon { (provable: ProvableSig) =>
    ProofRuleTactics.requireOneSubgoal(provable, "assertNoCex")
    val sequent = provable.subgoals.head
    val removeUscorePred: Formula => Boolean = {
      case PredOf(Function(name, _, _, _, _), _) => name.last != '_'
      case _ => true
    }
    Try(findCounterExample(sequent.copy(ante = sequent.ante.filter(removeUscorePred),
                                        succ = sequent.succ.filter(removeUscorePred)).toFormula)) match {
      case Success(Some(cex)) => throw BelleCEX("Counterexample", cex, sequent)
      case Success(None) => provable
      case Failure(_: ProverSetupException) => provable //@note no counterexample tool, so no counterexample
      case Failure(_: MathematicaComputationAbortedException) => provable
      case Failure(ex) => throw ex //@note fail with all other exceptions
    }
  }

  /** Prepares a QE call with all pre-processing steps, uses `order` to form the universal closure and finishes the
    * remaining subgoals using `doQE`. */
  def prepareQE(order: List[Variable], rcf: BuiltInTactic): BuiltInTactic = anon { (provable: ProvableSig) =>
    val closure = toSingleFormula andThen
      doIfFw(_.subgoals.head.succ.nonEmpty)(FOQuantifierTactics.universalClosureFw(order)(1))

    // Expands abs/min/max
    val expand = EqualityTactics.expandAll
//    if (Configuration.getBoolean(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS).getOrElse(false)) skip
//    else EqualityTactics.expandAll andThen
//      assertT(s => !StaticSemantics.symbols(s).exists({ case Function(_, _, _, _, interpreted) => interpreted.isDefined case _ => false }),
//        "Aborting QE since not all interpreted functions are expanded; please click 'Edit' and enclose interpreted functions with 'expand(.)', e.g. x!=0 -> expand(abs(x))>0.")

    if (!provable.isProved && provable.subgoals.forall(_.isFOL)) {
      val alpha = provable(saturate(or(alphaRule, allR('R))), 0)
      if (!alpha.isProved) {
        alpha(or(
          close,
          doIfElseFw(_.subgoals.forall(s => s.isPredicateFreeFOL && s.isFuncFreeArgsFOL))(
            // if
            EqualityTactics.applyEqualities andThen
              hideTrivialFormulas andThen
              abbreviateDifferentials andThen
              expand andThen
              abbreviateUninterpretedFuncs andThen
              abbreviateInterpretedFuncs andThen
              closure andThen
              rcf,
            // else
            (pr: ProvableSig) => try {
              pr(hidePredicates andThen
                hideQuantifiedFuncArgsFmls andThen
                assertT((s: Sequent) => s.isPredicateFreeFOL && s.isFuncFreeArgsFOL,
                  "Uninterpreted predicates and uninterpreted functions with bound arguments are not supported; attempted hiding but failed, please apply further manual steps to expand definitions and/or instantiate arguments and/or hide manually") andThen
                EqualityTactics.applyEqualities andThen
                hideTrivialFormulas andThen
                abbreviateDifferentials andThen
                expand andThen
                abbreviateUninterpretedFuncs andThen
                abbreviateInterpretedFuncs andThen
                closure andThen
                doIfFw(_ => rcf != skip)(
                  rcf andThen doIfFw(!_.isProved)(fail)
                )
              )
            } catch {
              case ex@(_: TacticInapplicableFailure | _: BelleCEX) =>
                val msg =
                  if (StaticSemantics.symbols(pr.subgoals.head).exists(n => n.name.startsWith("p_") || n.name.startsWith("q_"))) {
                    "Sequent cannot be proved. Please try to unhide some formulas."
                  } else {
                    "The sequent mentions uninterpreted functions or predicates; attempted to prove without but failed. Please apply further manual steps to expand definitions and/or instantiate arguments."
                  }
                throw new TacticInapplicableFailure(msg, ex)
            }
          )
        ), 0)
      } else alpha
    } else provable
  }

  /** Performs QE and fails if the goal isn't closed. */
  def fullQE(defs: Declaration, order: List[Variable] = Nil)(qeTool: => QETacticTool): BelleExpr = internal("_QE", (seq: Sequent) => {
    if (!seq.isFOL) throw new TacticInapplicableFailure("QE is applicable only on arithmetic questions, but got\n" +
      seq.prettyString + "\nPlease apply additional proof steps to hybrid programs first.")

    AnonymousLemmas.cacheTacticResult(
      //@note TryCatch instead of | to preserve original exception
      TryCatch(prepareQE(order, rcf(qeTool)) &
        // If not proved: check whether result false might have been caused by unexpanded definitions
        Idioms.doIf(!_.isProved)(
          DebuggingTactics.assertAt("False might be due to unexpanded definitions",
            _ != False || !StaticSemantics.symbols(seq).exists(defs.contains),
            new TacticInapplicableFailure(_))(1)
        ),
        classOf[TacticInapplicableFailure],
        (ex: TacticInapplicableFailure) =>
          if (StaticSemantics.symbols(seq).exists(defs.contains)) {
            expandAllDefs(defs.substs) & prepareQE(order, rcf(qeTool))
          } else throw ex
      )
      ,
      //@note does not evaluate qeTool since NamedTactic's tactic argument is evaluated lazily
      "qecache/" + qeTool.getClass.getSimpleName
    ) & Idioms.doIf(!_.isProved)(anon ((s: Sequent) =>
      if (s.succ.head == False) label(BelleLabels.QECEX)
      else DebuggingTactics.done("QE was unable to prove: invalid formula"))
    )
  })

  /** @see[[TactixLibrary.QE]] */
  def timeoutQE(defs: Declaration, order: List[Variable] = Nil, requiresTool: Option[String] = None,
                timeout: Option[Int] = None): BelleExpr = {
    lazy val tool = ToolProvider.qeTool(requiresTool.map(n => if (n == "M") "Mathematica" else n)).getOrElse(
      throw new ProverSetupException(s"QE requires ${requiresTool.getOrElse("a QETool")}, but got None"))
    lazy val resetTimeout: BelleExpr => BelleExpr = timeout match {
      case Some(t) => tool match {
        case tom: ToolOperationManagement =>
          val oldTimeout = tom.getOperationTimeout
          tom.setOperationTimeout(t)
          if (oldTimeout != t) {
            e: BelleExpr => TryCatch(e, classOf[Throwable],
              // catch: noop
              (_: Throwable) => skip,
              // finally: reset timeout
              Some(anon((p: ProvableSig) => { tom.setOperationTimeout(oldTimeout); p }))
            )
          } else (e: BelleExpr) => e
        case _ => throw new UnsupportedTacticFeature("Tool " + tool + " does not support timeouts")
      }
      case None => (e: BelleExpr) => e
    }
    lazy val timeoutTool: QETacticTool = timeout match {
      case Some(t) => tool match {
        case tom: ToolOperationManagement =>
          tom.setOperationTimeout(t)
          tool
        case _ => throw new UnsupportedTacticFeature("Tool " + tool + " does not support timeouts")
      }
      case None => tool
    }
    resetTimeout(ToolTactics.fullQE(defs, order)(timeoutTool))
  }

  /** Hides duplicate formulas (expensive because needs to sort positions). */
  private val hideDuplicates: BuiltInTactic = anon { (provable: ProvableSig) =>
    ProofRuleTactics.requireAtMostOneSubgoal(provable, "ToolTactics.hideDuplicates")
    provable.subgoals.headOption.map(seq => {
      val hidePos = seq.zipWithPositions.map(f => (f._1, f._2.isAnte, f._2)).groupBy(f => (f._1, f._2)).
        filter({ case (_, l) => l.size > 1 })
      val tactics = hidePos.values.flatMap({ case _ :: tail => tail.map(t =>
        (t._3, if (t._3.isAnte) HideLeft(t._3.checkAnte.top) else HideRight(t._3.checkSucc.top))) }).toList
      tactics.sortBy({ case (pos, _) => pos.index0 }).map(_._2).reverse.foldLeft(provable)({ case (p, t) => p(t, 0) })
    }).getOrElse(provable)
  }

  /** Hides useless trivial true/false formulas. */
  private val hideTrivialFormulas: BuiltInTactic = anon { (provable: ProvableSig) =>
    ProofRuleTactics.requireOneSubgoal(provable, "ToolTactics.hideTrivialFormulas")
    val seq = provable.subgoals.head
    val hidePos = seq.zipWithPositions.filter({
      case (True, pos) => pos.isAnte
      case (False, pos) => pos.isSucc
      case (Equal(l, r), pos) => pos.isAnte && l == r
      case (LessEqual(l, r), pos) => pos.isAnte && l == r
      case (GreaterEqual(l, r), pos) => pos.isAnte && l == r
      case (NotEqual(l, r), pos) => pos.isSucc && l == r
      case (Less(l, r), pos) => pos.isSucc && l == r
      case (Greater(l, r), pos) => pos.isSucc && l == r
      case _ => false
    }).map(p => if (p._2.isAnte) HideLeft(p._2.checkAnte.top) else HideRight(p._2.checkSucc.top)).reverse
    hidePos.foldLeft(provable)({ case (p, t) => p(t, 0) })
  }

  /** Returns all sub-terms of expression `e` that are differentials or differential symbols. */
  private def differentialsOf(e: Expression): List[Term] = e.matchingTerms({
    case _: Differential => true
    case _: DifferentialSymbol => true
    case _ => false
  })

  /** Returns all sub-terms of expression `e` that are uninterpreted functions. */
  private def uninterpretedFuncsOf(e: Expression): List[Term] = e.matchingTerms({
    case FuncOf(Function(_, _, domain, _, None), _) => domain != Unit
    case _ => false
  })

  /** Returns all sub-terms of `fml` that are interpreted functions. */
  def interpretedFuncsOf(e: Expression): List[Term] = e.matchingTerms({
    case FuncOf(Function(_, _, _, _, i), _) => i.isDefined
    case _ => false
  }).reverse

  /** Returns all sub-terms of `fml` that are interpreted except known functions. */
  def interpretedFuncsOfExcept(e: Expression): List[Term] = e.matchingTerms({
    case FuncOf(fn@Function(_, _, _, _, Some(_)), _) =>
      Configuration.getBoolean(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS).getOrElse(false) &&
        !MathematicaOpSpec.interpretedSymbols.exists(_._2 == fn)
    case _ => false
  }).reverse

  /** Abbreviates differentials and differential symbols to variables. */
  private val abbreviateDifferentials: BuiltInTactic = anon { (provable: ProvableSig) =>
    ProofRuleTactics.requireAtMostOneSubgoal(provable, "ToolTactics.abbreviateDifferentials")
    provable.subgoals.headOption.map(seq => {
      val abbrv = (seq.ante ++ seq.succ).
        flatMap(differentialsOf).distinct.map(d => (p: ProvableSig) => p(EqualityTactics.abbrv(d, None).result _, 0)(HideLeft(AntePos(seq.ante.size)), 0))
      abbrv.foldLeft(provable)({ case (p, t) => p(t, 0) })
    }).getOrElse(provable)
  }

  /** Abbreviates uninterpreted functions with arity>0 to variables. */
  private val abbreviateUninterpretedFuncs: BuiltInTactic = anon { (provable: ProvableSig) =>
    ProofRuleTactics.requireAtMostOneSubgoal(provable, "ToolTactics.abbreviateUninterpretedFuncs")
    provable.subgoals.headOption.map(seq => {
      val abbrv = (seq.ante ++ seq.succ).
        flatMap(uninterpretedFuncsOf).distinct.map(d => (p: ProvableSig) => p(EqualityTactics.abbrv(d, None).result _, 0)(HideLeft(AntePos(seq.ante.size)), 0))
      abbrv.foldLeft(provable)({ case (p, t) => p(t, 0) })
    }).getOrElse(provable)
  }

  /** Abbreviates interpreted functions to variables. */
  private val abbreviateInterpretedFuncsHelper: BuiltInTactic = anon { (pr: ProvableSig) =>
    ProofRuleTactics.requireOneSubgoal(pr, "ToolTactics.abbreviateInterpretedFuncsHelper")
    val seq = pr.subgoals.head
    val interpreted = (seq.ante ++ seq.succ).flatMap(interpretedFuncsOf).distinct.reverse
    val interpretedExcept = (seq.ante ++ seq.succ).flatMap(interpretedFuncsOfExcept).distinct.reverse

    // Try full abbreviation and search for cex
    pr(or(interpreted.map(EqualityTactics.abbrv(_, None) andThen hideL('Llast)).
      foldLeft(_)({ case (p, t) => p(t, 0) })(assertNoCex, 0)
      ,
      interpretedExcept.map(EqualityTactics.abbrv(_, None) andThen hideL('Llast)).foldLeft(_)({ case (p, t) => p(t, 0) })), 0)
  }

  /** Abbreviates interpreted functions to variables with 1 layer of simplification. */
  private val abbreviateInterpretedFuncs: BuiltInTactic = anon { (pr: ProvableSig) =>
    ProofRuleTactics.requireOneSubgoal(pr, "ToolTactics.abbreviateInterpretedFuncs")
    val seq = pr.subgoals.head
    val interpreted = (seq.ante ++ seq.succ).flatMap(interpretedFuncsOf).distinct.reverse

    if (interpreted.nonEmpty) {
      // Automatically apply simplifications when there are interpreted functions
      pr(SimplifierV3.fullSimplify, 0)(
        // This tries to unfold initial conditions at least once
        abbreviateInterpretedFuncsHelper, 0)
    } else pr
  }

  def fullQE(qeTool: => QETacticTool): BelleExpr = anons { (pr: ProvableSig) => fullQE(pr.defs, List.empty)(qeTool) }

  // Follows heuristic in C.W. Brown. Companion to the tutorial: Cylindrical algebraic decomposition, (ISSAC 2004)
  // www.usna.edu/Users/cs/wcbrown/research/ISSAC04/handout.pdf
  //For each variable, we need to compute:
  // 1) max degree of variable in the sequent
  // 2) max total-degree of terms containing that variable
  // 3) number of terms containing that variable
  // "Terms" ~= "monomials"
  // This isn't accurate for divisions (which is treated as a multiplication)
  // Map[String,(Int,Int,Int)]
  private def addy(p1:(Int,Int)=>Int,p2:(Int,Int)=>Int,p3:(Int,Int)=>Int,l:(Int,Int,Int),r:(Int,Int,Int)) : (Int,Int,Int) = {
    (p1(l._1,r._1), p2(l._2,r._2), p3(l._3,r._3) )
  }

  private def merge(m1:Map[Variable,(Int,Int,Int)],m2:Map[Variable,(Int,Int,Int)],p1:(Int,Int)=>Int,p2:(Int,Int)=>Int,p3:(Int,Int)=>Int) : Map[Variable,(Int,Int,Int)] = {
    val matches = m1.keySet.intersect(m2.keySet)
    val updm1 = matches.foldLeft(m1)( (m,s) => m+(s->addy(p1,p2,p3,m1(s),m2(s))))
    updm1 ++ (m2 -- m1.keySet)
  }

  private def termDegs(t:Term) : Map[Variable,(Int,Int,Int)] = t match {
    case v:Variable => Map((v,(1,1,1)))
    case Neg(tt) => termDegs(tt)
    case Plus(l,r) => merge( termDegs(l),termDegs(r), math.max, math.max, _+_)
    case Minus(l,r) => termDegs(Plus(l,r))
    case Times(l,r) =>
      val lm = termDegs(l)
      val lmax = lm.values.map(_._2).foldLeft(0)(math.max)
      val rm = termDegs(r)
      val rmax = rm.values.map(_._2).foldLeft(0)(math.max)
      val lmap = lm.mapValues(p => (p._1, p._2+rmax, p._3) )
      val rmap = rm.mapValues(p => (p._1, p._2+lmax, p._3) ) //Updated max term degrees
      merge(lmap,rmap, _+_, math.max, _+_) /* The 3rd one probably isn't correct for something like x*x*x */
    case Divide(l,r) => termDegs(Times(l,r))
    case Power(p,n:Number) =>
      val pm = termDegs(p)
      //Assume integer powers
      pm.mapValues( (p:(Int,Int,Int)) => (p._1*n.value.toInt,p._2*n.value.toInt,p._3) )
    case FuncOf(_,tt) => termDegs(tt)
    case Pair(l,r) => merge(termDegs(l),termDegs(r), math.max, math.max, _+_)
    case _ => Map[Variable,(Int,Int,Int)]()
  }

  //This just takes the max or sum where appropriate
  private def fmlDegs(f:Formula) : Map[Variable,(Int,Int,Int)] = {
    f match {
      case b:BinaryCompositeFormula => merge(fmlDegs(b.left),fmlDegs(b.right), math.max, math.max, _+_)
      case u:UnaryCompositeFormula => fmlDegs(u.child)
      case f:ComparisonFormula => merge(termDegs(f.left),termDegs(f.right), math.max, math.max, _+_)
      case q:Quantified => fmlDegs(q.child) -- q.vars
      case m:Modal => fmlDegs(m.child) //QE wouldn't understand this anyway...
      case _ => Map() //todo: pred symbols?
    }
  }

  /** Syntactic approx. of degree of variable x in term t
    *
    * @param t the term t
    * @param x the variable x to compute the degree
    * @return the degree
    */
  def varDegree(t: Term, x: Variable): Int = {
    val tx = termDegs(t)
    if (tx.contains(x)) tx(x)._1
    else 0
  }

  private def seqDegs(s: Sequent): Map[Variable, (Int,Int,Int)] = {
    (s.ante++s.succ).foldLeft(Map.empty[Variable,(Int,Int,Int)])(
      (m: Map[Variable,(Int,Int,Int)], f: Formula) => merge(m, fmlDegs(f), math.max, math.max, _+_))
  }

  private def equalityOrder[T]: Ordering[T] = (_: T, _: T) => 0

  private def orderHeuristic(s: Sequent, po: Ordering[Variable]): List[Variable] = {
    val m = seqDegs(s)
    val ls = m.keySet.toList.sortWith( (x,y) => {
      val c = po.compare(x,y)
      if (c==0) m(x) < m(y)
      else c < 0
      }
    )
    ls
  }

  private def orderedClosure(po: Ordering[Variable]): BuiltInTactic = anon { (provable: ProvableSig) =>
    ProofRuleTactics.requireOneSubgoal(provable, "orderedClosure")
    val seq = provable.subgoals.head
    val order = orderHeuristic(seq, po)
    FOQuantifierTactics.universalClosureFw(order)(SuccPos(0)).computeResult(provable)
  }

  //Note: the same as fullQE except it uses computes the heuristic order in the middle
  def heuristicQE(qeTool: => QETacticTool, po: Ordering[Variable]=equalityOrder): BelleExpr = {
    //@note labels not yet available in forward tactics
    heuristicQEImpl(qeTool, po) & (done | anon ((s: Sequent) =>
      if (s.succ.head == False) label(BelleLabels.QECEX)
      else DebuggingTactics.done("QE was unable to prove: invalid formula"))
      )
  }

  /** Heuristic QE forward implementation. */
  private def heuristicQEImpl(qeTool: => QETacticTool, po: Ordering[Variable]=equalityOrder): BuiltInTactic= internal ("_hQE", (provable: ProvableSig) => {
    require(provable.subgoals.forall(_.isFOL), "QE only on FOL formulas")
    require(qeTool != null, "No QE tool available. Use parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    provable.subgoals.toList match {
      case Nil => provable
      case _ => provable(
        //onall
        saturate(alphaRule) andThen or(
          close,
          saturate(EqualityTactics.atomExhaustiveEqL2R('L)) andThen
            hidePredicates andThen
            toSingleFormula andThen
            orderedClosure(po) andThen
            rcf(qeTool)
          )
        )
    }
  })

  /** Performs QE and allows the goal to be reduced to something that isn't necessarily true.
    * @note You probably want to use fullQE most of the time, because partialQE will destroy the structure of the sequent
    */
  // was "pQE"
  def partialQE(qeTool: => QETacticTool, reformatAssumptions: Boolean = true): BelleExpr = anon ((s: Sequent) => {
    // dependent tactic so that qeTool is evaluated only when tactic is executed, but not when tactic is instantiated
    require(qeTool != null, "No QE tool available. Use parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    hidePredicates & toSingleFormula & rcf(qeTool) &
      (if (reformatAssumptions && s.ante.exists(!_.isInstanceOf[PredOf]))
        Idioms.doIf(!_.isProved)(cut(s.ante.filterNot(_.isInstanceOf[PredOf]).reduceRight(And)) <(
          SaturateTactic(andL('L)) & SimplifierV3.fullSimpTac(),
          QE & done
        ))
       else Idioms.nil)
  })

  /** Performs Quantifier Elimination on a provable containing a single formula with a single succedent. */
  def rcf(qeTool: => QETacticTool): BuiltInTactic = internal ("_rcf", (provable: ProvableSig) => {
    ProofRuleTactics.requireAtMostOneSubgoal(provable, "ToolTactics.rcf")
    provable.subgoals.headOption.map(sequent => {
      require(qeTool != null, "No QE tool available. Use parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
      assert(sequent.ante.isEmpty && sequent.succ.length == 1, "Provable's subgoal should have only a single succedent.")
      require(sequent.succ.head.isFOL, "QE only on FOL formulas")

      //Run QE and extract the resulting provable and equivalence
      //@todo how about storing the lemma, but also need a way of finding it again
      //@todo for storage purposes, store rcf(lemmaName) so that the proof uses the exact same lemma without
      val qeFact = try {
        qeTool.qe(sequent.succ.head).fact
      } catch {
        case ex: SMTQeException => throw new TacticInapplicableFailure(ex.getMessage, ex)
        case ex: SMTTimeoutException => throw new TacticInapplicableFailure(ex.getMessage, ex)
        case ex: MathematicaInapplicableMethodException => throw new TacticInapplicableFailure(ex.getMessage, ex)
      }

      def leadingQuantOrder(fml: Formula): Seq[Variable] = fml match {
        case Forall(v, p) => v ++ leadingQuantOrder(p)
        case Exists(v, p) => v ++ leadingQuantOrder(p)
        case _ => Nil
      }

      val optCloseT: BuiltInTactic = anon { provable: ProvableSig =>
        provable.subgoals.head.succ.indexOf(True) match {
          case -1 => provable
          case i => provable(CloseTrue(SuccPos(i)), 0)
        }
      }

      def satAndL: BuiltInTactic = anon { provable: ProvableSig =>
        val andL = provable.subgoals.head.ante.zipWithIndex.filter(_._1.isInstanceOf[And]).reverseMap({ case (_, i) => AndLeft(AntePos(i)) })
        if (andL.isEmpty) provable
        else andL.foldLeft(provable)({ case (p, r) => p(r, 0) })(satAndL, 0)
      }

      def applyFacts(facts: List[Formula]): BuiltInTactic = anon { (provable: ProvableSig) =>
        facts.map({ case Equiv(f, result) => (pr: ProvableSig) =>
          (pr(toSingleFormula, 0)
          (FOQuantifierTactics.universalClosureFw(leadingQuantOrder(f).toList)(1), 0)
          (cutLRFw(result)(1), 0)
          /* show */
          (EquivifyRight(SuccPos(0)), 1)
          (CommuteEquivRight(SuccPos(0)), 1)
          (Cut(qeFact.conclusion.succ.head), 1) // creates subgoals 1+2
          (CoHideRight(SuccPos(sequent.succ.length)), 2)
          (qeFact, 2)
          (satAndL, 1)
          (close, 1)
          /* use */
          (optCloseT, 0)
          )
        }).zipWithIndex.reverse.foldLeft(provable)({ case (pr, (r, i)) => pr(r, i) })
      }

      def applySingleFact(result: Formula, fact: ProvableSig): BuiltInTactic = anon { provable: ProvableSig =>
        (provable(cutLRFw(result)(SuccPos(0)), 0)
        /* show */
        (EquivifyRight(SuccPos(0)), 1)
        (CommuteEquivRight(SuccPos(0)), 1)
        (fact, 1)
        /* use */
        (optCloseT, 0)
        )
      }

      qeFact.conclusion.succ.head match {
        case Equiv(_, result) => applySingleFact(result, qeFact).result(provable)
        case result: And =>
          //@note apply same steps as QETacticTool to use `close` in applyFacts
          val facts = FormulaTools.conjuncts(result)
          val skolemized = provable(saturate(allR('R)))
          val r = skolemized(PropositionalTactics.prop)
          //@todo sometimes expandAll does not create additional subgoals, need a better check whether to expand
          if (r.subgoals.size == facts.size) try {
            applyFacts(facts)(r)
          } catch {
            // unexpanded definitions result in inapplicable close
            case _: TacticInapplicableFailure => applyFacts(facts)(skolemized(expandAll andThen PropositionalTactics.prop, 0)(applyEqualities))
          }
          else applyFacts(facts)(skolemized(expandAll andThen PropositionalTactics.prop, 0)(applyEqualities))
      }
    }).getOrElse(provable)
  })

  /** @see [[TactixLibrary.transform()]] */
  def transform(to: Expression): DependentPositionTactic = inputanon {(pos: Position, sequent: Sequent) => {
    require(sequent.sub(pos) match {
      case Some(fml: Formula) => fml.isFOL && to.kind == fml.kind
      case Some(t: Term) => to.kind == t.kind
      case _ => false
    }, "transform only on arithmetic formulas and terms")

    to match {
      case f: Formula => transformFormula(f, sequent, pos)
      case t: Term => transformTerm(t, sequent, pos)
      case _ => assert(false, "Precondition already checked that other types cannot occur " + to); ???
    }
  }}

  /** @see [[TactixLibrary.edit()]] */
  def edit(to: Expression): DependentPositionWithAppliedInputTactic = inputanon {(pos: Position, sequent: Sequent) => {
    sequent.sub(pos) match {
      case Some(e) if e.kind != to.kind => throw new TacticInapplicableFailure("edit only applicable to terms or formulas of same kind, but " + e.prettyString + " of kind " + e.kind + " is not " + to.kind)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
      case _ => // ok
    }

    val (abbrvTo: Expression, abbrvTactic: BelleExpr) = createAbbrvTactic(to, sequent)
    val (expandTo: Expression, expandTactic: BelleExpr) = createExpandTactic(abbrvTo, sequent, pos)

    val transformTactic = anon (sequent.sub(pos) match {
      case Some(e) =>
        try {
          //@note skip transformation if diff is abbreviations only (better performance on large formulas)
          //@todo find specific transform position based on diff (needs unification for terms like 2+3, 5)
          val diff = UnificationMatch(to, e)
          if (diff.usubst.subsDefsInput.nonEmpty && diff.usubst.subsDefsInput.forall(_.what match {
            case FuncOf(Function(name, None, _, _, _), _) =>
              name == TacticReservedSymbols.abbrv.name || name == TacticReservedSymbols.expand.name
            case _ => false
          })) skip
          else TactixLibrary.transform(expandTo)(pos) & DebuggingTactics.assertE(expandTo, "Unexpected edit result", new TacticInapplicableFailure(_))(pos)
        } catch {
          case ex: UnificationException =>
            //@note looks for specific transform position until we have better formula diff
            //@note Exception reports variable unifications and function symbol unifications swapped
            if (ex.input.asExpr.isInstanceOf[FuncOf] && !ex.shape.asExpr.isInstanceOf[FuncOf]) {
              FormulaTools.posOf(e, ex.shape.asExpr) match {
                case Some(pp) =>
                  TactixLibrary.transform(ex.input.asExpr)(pos.topLevel ++ pp) &
                    DebuggingTactics.assertE(expandTo, "Unexpected edit result", new TacticInapplicableFailure(_))(pos) |
                  TactixLibrary.transform(expandTo)(pos) &
                    DebuggingTactics.assertE(expandTo, "Unexpected edit result", new TacticInapplicableFailure(_))(pos)
                case _ =>
                  TactixLibrary.transform(expandTo)(pos) &
                    DebuggingTactics.assertE(expandTo, "Unexpected edit result", new TacticInapplicableFailure(_))(pos)
              }
            } else {
              FormulaTools.posOf(e, ex.input.asExpr) match {
                case Some(pp) =>
                  TactixLibrary.transform(ex.shape.asExpr)(pos.topLevel ++ pp) &
                    DebuggingTactics.assertE(expandTo, "Unexpected edit result", new TacticInapplicableFailure(_))(pos) |
                  TactixLibrary.transform(expandTo)(pos) &
                    DebuggingTactics.assertE(expandTo, "Unexpected edit result", new TacticInapplicableFailure(_))(pos)
                case _ =>
                  TactixLibrary.transform(expandTo)(pos) &
                    DebuggingTactics.assertE(expandTo, "Unexpected edit result", new TacticInapplicableFailure(_))(pos)
              }
            }
        }
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    })

    abbrvTactic & expandTactic & transformTactic
  }}

  /** Parses `to` for occurrences of `abbrv` to create a tactic. Returns `to` with `abbrv(...)` replaced by the
    * abbreviations and the tactic to turn `to` into the returned expression by proof. */
  private def createAbbrvTactic(to: Expression, sequent: Sequent): (Expression, BelleExpr) = {
    var nextAbbrvName: Variable = TacticHelper.freshNamedSymbol(Variable(TacticReservedSymbols.abbrv.name), sequent)
    val abbrvs = scala.collection.mutable.Map[PosInExpr, Term]()

    val traverseFn = new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case FuncOf(Function(TacticReservedSymbols.abbrv.name, TacticReservedSymbols.abbrv.index, _, _, _), abbrv@Pair(_, v: Variable)) =>
          abbrvs(p) = abbrv
          Right(v)
        case FuncOf(Function(TacticReservedSymbols.abbrv.name, TacticReservedSymbols.abbrv.index, _, _, _), t) =>
          val abbrv = nextAbbrvName
          nextAbbrvName = Variable(abbrv.name, Some(abbrv.index.getOrElse(-1) + 1))
          abbrvs(p) = Pair(t, abbrv)
          Right(abbrv)
        case _ => Left(None)
      }
    }

    val abbrvTo: Expression =
      if (to.kind == FormulaKind) ExpressionTraversal.traverse(traverseFn, to.asInstanceOf[Formula]).get
      else ExpressionTraversal.traverse(traverseFn, to.asInstanceOf[Term]).get
    //@todo unify to check whether abbrv is valid; may need reassociating, e.g. in x*y*z x*abbrv(y*z)

    val abbrvTactic = abbrvs.values.map({
      case Pair(t, v: Variable) => TactixLibrary.abbrvAll(t, Some(v))
    }).reduceOption[BelleExpr](_ & _).getOrElse(skip)
    (abbrvTo, abbrvTactic)
  }

  /** Parses `to` for occurrences of `expand` to create a tactic. Returns `to` with `expand(fn)` replaced by the
    * variable corresponding to the expanded fn (abs,min,max) together with the tactic to turn `to` into the returned
    * expression by proof. */
  private def createExpandTactic(to: Expression, sequent: Sequent, pos: Position): (Expression, BelleExpr) = {
    val nextName: scala.collection.mutable.Map[String, Variable] = scala.collection.mutable.Map(
        InterpretedSymbols.absF.name -> TacticHelper.freshNamedSymbol(Variable(InterpretedSymbols.absF.name + "_"), sequent),
        InterpretedSymbols.minF.name -> TacticHelper.freshNamedSymbol(Variable(InterpretedSymbols.minF.name + "_"), sequent),
        InterpretedSymbols.maxF.name -> TacticHelper.freshNamedSymbol(Variable(InterpretedSymbols.maxF.name + "_"), sequent))

    val expandedVars = scala.collection.mutable.Map[PosInExpr, String]()

    def getNextName(s: String, p: PosInExpr): Term = {
      val nn = nextName(s)
      nextName.put(s, Variable(nn.name, Some(nn.index.getOrElse(-1) + 1)))
      expandedVars(p) = s
      nn
    }

    val traverseFn = new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case FuncOf(Function(TacticReservedSymbols.expand.name, TacticReservedSymbols.expand.index, _, _, _), t) => t match {
          case FuncOf(InterpretedSymbols.absF, _) => Right(getNextName(InterpretedSymbols.absF.name, p))
          case FuncOf(InterpretedSymbols.minF, _) => Right(getNextName(InterpretedSymbols.minF.name, p))
          case FuncOf(InterpretedSymbols.maxF, _) => Right(getNextName(InterpretedSymbols.maxF.name, p))
        }
        case _ => Left(None)
      }
    }

    val expandTo: Expression =
      if (to.kind == FormulaKind) ExpressionTraversal.traverse(traverseFn, to.asInstanceOf[Formula]).get
      else ExpressionTraversal.traverse(traverseFn, to.asInstanceOf[Term]).get

    val tactic = expandedVars.toIndexedSeq.sortWith((a, b) => a._1.pos < b._1.pos).map({
      case (p, InterpretedSymbols.absF.name) => EqualityTactics.abs(pos.topLevel ++ p)
      case (p, InterpretedSymbols.minF.name | InterpretedSymbols.maxF.name) => EqualityTactics.minmax(pos.topLevel ++ p)
    }).reduceOption[BelleExpr](_ & _).getOrElse(skip)
    (expandTo, tactic)
  }

  /** Transforms the formula at position `pos` into the formula `to`. */
  private def transformFormula(to: Formula, sequent: Sequent, pos: Position) = {
    val polarity = FormulaTools.polarityAt(sequent(pos.top), pos.inExpr)*(if (pos.isSucc) 1 else -1)

    val (src, tgt) = (sequent.sub(pos), to) match {
      case (Some(src: Formula), tgt: Formula) => if (polarity > 0) (tgt, src) else (src, tgt)
      case (Some(e), _) => throw new TacticInapplicableFailure("transformFormula only applicable to formulas, but got " + e.prettyString)
      case (None, _) => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }

    val boundVars = StaticSemantics.boundVars(sequent(pos.top))
    val gaFull =
      if (pos.isSucc) (sequent.ante ++ sequent.succ.patch(pos.top.getIndex, Nil, 1).map(Not)).flatMap(FormulaTools.conjuncts).filter(_.isFOL)
      else (sequent.ante.patch(pos.top.getIndex, Nil, 1) ++ sequent.succ.map(Not)).flatMap(FormulaTools.conjuncts).filter(_.isFOL)

    @tailrec
    def proveFact(assumptions: IndexedSeq[Formula], filters: List[IndexedSeq[Formula]=>IndexedSeq[Formula]]): (ProvableSig, IndexedSeq[Formula]) = {
      val filteredAssumptions = filters.head(assumptions)
      lazy val filteredAssumptionsFml = filteredAssumptions.reduceOption(And).getOrElse(True)
      val pr =
        if (filteredAssumptions.isEmpty) proveBy(Imply(src, tgt), master())
        else if (polarity > 0) proveBy(Imply(And(filteredAssumptionsFml, src), tgt), master())
        else proveBy(Imply(filteredAssumptionsFml, Imply(src, tgt)), master())

      if (pr.isProved || filters.tail.isEmpty) (pr, filteredAssumptions)
      else proveFact(assumptions, filters.tail)
    }
    val (fact, ga) = proveFact(gaFull,
      ( // first try without any assumptions
        (al: IndexedSeq[Formula]) => al.filter(_ => false)) ::
        // then without alternatives to prove and without irrelevant formulas (non-overlapping variables)
        ((al: IndexedSeq[Formula]) => al.filter({ case Not(_) => false case _ => true }).
          filter(StaticSemantics.freeVars(_).intersect(boundVars).isEmpty)) ::
        // then without irrelevant formulas (non-overlapping variables)
        ((al: IndexedSeq[Formula]) => al.filter(StaticSemantics.freeVars(_).intersect(boundVars).isEmpty)) ::
        // then with full sequent
        ((al: IndexedSeq[Formula]) => al.filter(_ => true)) :: Nil)

    def propPushLeftIn(op: (Formula, Formula) => Formula) = {
      val p = "p_()".asFormula
      val q = "q_()".asFormula
      val r = "r_()".asFormula
      proveBy(Imply(op(p, Imply(q, r)), Imply(op(p, q), op(p, r))), prop & done)
    }

    def propPushRightIn(op: (Formula, Formula) => Formula) = {
      val p = "p_()".asFormula
      val q = "q_()".asFormula
      val r = "r_()".asFormula
      proveBy(Imply(op(Imply(q, r), p), Imply(op(q, p), op(r, p))), prop & done)
    }

    lazy val implyFact = remember("q_() -> (p_() -> p_()&q_())".asFormula, prop & done, namespace).fact
    lazy val existsDistribute = remember("(\\forall x_ (p(x_)->q(x_))) -> ((\\exists x_ p(x_))->(\\exists x_ q(x_)))".asFormula,
      implyR(1) & implyR(1) & existsL(-2) & allL(-1) & existsR(1) & prop & done, namespace).fact

    def pushIn(remainder: PosInExpr): DependentPositionTactic = anon ((pp: Position, ss: Sequent) => (ss.sub(pp) match {
      case Some(Imply(left: BinaryCompositeFormula, right: BinaryCompositeFormula)) if left.getClass==right.getClass && left.left==right.left =>
        useAt(propPushLeftIn(left.reapply), PosInExpr(1::Nil))(pp)
      case Some(Imply(left: BinaryCompositeFormula, right: BinaryCompositeFormula)) if left.getClass==right.getClass && left.right ==right.right =>
        useAt(propPushRightIn(left.reapply), PosInExpr(1::Nil))(pp)
      case Some(Imply(Box(a, _), Box(b, _))) if a==b => useAt(Ax.K, PosInExpr(1::Nil))(pp)
      case Some(Imply(Forall(lv, _), Forall(rv, _))) if lv==rv => useAt(Ax.allDist)(pp)
      case Some(Imply(Exists(lv, _), Exists(rv, _))) if lv==rv => useAt(existsDistribute, PosInExpr(1::Nil))(pp)
      case Some(Imply(_, _)) => useAt(implyFact, PosInExpr(1::Nil))(pos)
      case _ => skip
    }) & (if (remainder.pos.isEmpty) skip else pushIn(remainder.child)(pp ++ PosInExpr(remainder.head::Nil))))

    val key = if (polarity > 0) PosInExpr(1::Nil) else if (ga.isEmpty) PosInExpr(0::Nil) else PosInExpr(1::0::Nil)

    if (fact.isProved && ga.isEmpty) useAt(fact, key)(pos)
    else if (fact.isProved && ga.nonEmpty) useAt(fact, key)(pos) & (
      if (polarity < 0) Idioms.<(skip, cohideOnlyR('Rlast) & master() & done | master())
      else cutAt(ga.reduce(And))(pos) & Idioms.<(
        //@todo ensureAt only closes branch when original conjecture is true
        ensureAt(pos) & OnAll(cohideOnlyR(pos) & master() & done | master() & done),
        pushIn(pos.inExpr)(pos.top)
      )
      )
    else throw new TacticInapplicableFailure(s"Invalid transformation: cannot transform ${sequent.sub(pos)} to $to")
  }

  /** Transforms the term at position `pos` into the term `to`. */
  private def transformTerm(to: Term, sequent: Sequent, pos: Position) = {
    val src = sequent.sub(pos) match {
      case Some(src: Term) => src
      case Some(e) => throw new TacticInapplicableFailure("transformTerm only applicable to terms, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + sequent.prettyString)
    }
    useAt(proveBy(Equal(src, to), QE & done), PosInExpr(0::Nil))(pos)
  }

  /** Ensures that the formula at position `pos` is available at that position from the assumptions. */
  private def ensureAt: DependentPositionTactic = anon ((pos: Position, seq: Sequent) => {
    lazy val ensuredFormula = seq.sub(pos) match {
      case Some(fml: Formula) => fml
      case Some(e) => throw new TacticInapplicableFailure("ensureAt only applicable to formulas, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
    lazy val skipAt = anon ((_: Position, _: Sequent) => skip)

    lazy val step = seq(pos.top) match {
      case Box(ODESystem(_, _), _) => diffInvariant(ensuredFormula)(pos.top) & dW(pos.top)
      case Box(Loop(_), _) => loop(ensuredFormula)(pos.top) & Idioms.<(master(), skip, master())
      case Box(Test(_), _) => testb(pos.top) & implyR(pos.top)
      case Box(_, _) => TactixLibrary.step(pos.top)
      case Forall(v, _) if pos.isAnte => allL(v.head)(pos.top)
      case Forall(_, _) if pos.isSucc => allR(pos.top)
      case Exists(v, _) if pos.isSucc => existsR(v.head)(pos.top)
      case Exists(_, _ ) if pos.isAnte => existsL(pos.top)
      //@todo resulting branches may not be provable when starting from wrong question, e.g., a>0&b>0 -> x=2 & a/b>0, even if locally a>0&b>0 -> (a/b>0 <-> a>0*b)
      case e if pos.isAnte => TacticIndex.default.tacticsFor(e)._1.headOption.getOrElse(skipAt)(pos.top)
      case e if pos.isSucc => TacticIndex.default.tacticsFor(e)._2.headOption.getOrElse(skipAt)(pos.top)
    }
    val recurse = if (pos.isTopLevel) skip else ensureAt(pos.top.getPos, pos.inExpr.child)
    if (seq.isFOL) QE else step & onAll(recurse)
  })

  /* Hides all predicates (QE cannot handle predicate symbols) */
  private def hidePredicates: BuiltInTactic = anon { (provable: ProvableSig) => ProofRuleTactics.onSoleSubgoal(provable,
    (sequent: Sequent) =>
      (    sequent.ante.zipWithIndex.filter({ case (f, _) => !f.isPredicateFreeFOL }).reverseMap({ case (fml, i) => hideL(AntePos(i), fml) })
        ++ sequent.succ.zipWithIndex.filter({ case (f, _) => !f.isPredicateFreeFOL }).reverseMap({ case (fml, i) => hideR(SuccPos(i), fml) })
        ).foldLeft(provable)({ (pr, r) => pr(r, 0) }),
    "hidePredicates"
    )
  }

  /* Hides all predicates (QE cannot handle predicate symbols) */
  private def hideQuantifiedFuncArgsFmls: BuiltInTactic = anon { (provable: ProvableSig) => ProofRuleTactics.onSoleSubgoal(provable,
    (sequent: Sequent) =>
      (    sequent.ante.zipWithIndex.filter({ case (f, _) => !f.isFuncFreeArgsFOL }).reverseMap({ case (fml, i) => hideL(AntePos(i), fml) })
        ++ sequent.succ.zipWithIndex.filter({ case (f, _) => !f.isFuncFreeArgsFOL }).reverseMap({ case (fml, i) => hideR(SuccPos(i), fml) })
        ).foldLeft(provable)({ (pr, r) => pr(r, 0) }),
    "hideQuantifiedFuncArgsFml"
    )
  }

  /** Hides all non-FOL formulas from the sequent. */
  def hideNonFOL: BuiltInTactic = anon { (provable: ProvableSig) => ProofRuleTactics.onSoleSubgoal(provable,
    (sequent: Sequent) =>
      (    sequent.ante.zipWithIndex.filter({ case (fml, _) => !fml.isFOL }).reverseMap({ case (fml, i) => hideL(AntePos(i), fml) })
        ++ sequent.succ.zipWithIndex.filter({ case (fml, _) => !fml.isFOL }).reverseMap({ case (fml, i) => hideR(SuccPos(i), fml) })
        ).foldLeft(provable)({ (pr, r) => pr(r, 0) }),
    "hideNonFOL"
    )
  }
}
