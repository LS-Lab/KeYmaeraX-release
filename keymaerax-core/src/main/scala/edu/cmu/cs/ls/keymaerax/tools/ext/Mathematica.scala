/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-02
  */
package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleCEX, OnAll}
import edu.cmu.cs.ls.keymaerax.btactics.{InvGenTool, PropositionalTactics, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.SimulationTool.{SimRun, SimState, Simulation}
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.tools.ext.ExtMathematicaOpSpec.{mwhile, part}
import edu.cmu.cs.ls.keymaerax.tools.ext.SOSsolveTool.Result
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion.{KExpr, MExpr}
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec._

import scala.annotation.tailrec
import scala.collection.immutable.{Map, Seq}
import scala.collection.mutable.ListBuffer
import scala.collection.immutable.IndexedSeq

/**
 * Mathematica/Wolfram Engine tool for quantifier elimination and solving differential equations.
 * @param link How to connect to the tool, either JLink or WolframScript.
 *
 * Created by smitsch on 4/27/15.
 * @author Stefan Mitsch
 * @todo Code Review: Move non-critical tool implementations into a separate package tactictools
 */
class Mathematica(private[tools] val link: MathematicaLink, override val name: String) extends Tool
    with QETacticTool with InvGenTool with ODESolverTool with CounterExampleTool
    with SimulationTool with DerivativeTool with EquationSolverTool with SimplificationTool with AlgebraTool
    with PDESolverTool with SOSsolveTool with LyapunovSolverTool with ToolOperationManagement {

  /** Indicates whether the tool is initialized. */
  private var initialized = false

  private val mQE: MathematicaQEToolBridge[Lemma] = new MathematicaQEToolBridge[Lemma](link)
  private val mPegasus = new MathematicaInvGenTool(link)
  private val mSOSsolve = new MathematicaSOSsolveTool(link)
  private val mCEX = new MathematicaCEXTool(link)
  private val mODE = new MathematicaODESolverTool(link)
  private val mPDE = new MathematicaPDESolverTool(link)
  private val mSim = new MathematicaSimulationTool(link)
  private val mSolve = new MathematicaEquationSolverTool(link)
  private val mAlgebra = new MathematicaAlgebraTool(link)
  private val mSimplify = new MathematicaSimplificationTool(link)
  private val mLyapunov = new MathematicaLyapunovSolverTool(link)

  private val qeInitialTimeout = Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_INITIAL))
  private val qeCexTimeout = Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_CEX))
  private var qeMaxTimeout = Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_MAX))

  private val memoryLimit: Long = Configuration.getLong(Configuration.Keys.MATHEMATICA_MEMORY_LIMIT).getOrElse(-1)

  override def init(config: Map[String,String]): Unit = {
    mQE.memoryLimit = memoryLimit
    mPegasus.memoryLimit = memoryLimit
    mSOSsolve.memoryLimit = memoryLimit
    mCEX.memoryLimit = memoryLimit
    mODE.memoryLimit = memoryLimit
    mPDE.memoryLimit = memoryLimit
    mSim.memoryLimit = memoryLimit
    mSolve.memoryLimit = memoryLimit
    mAlgebra.memoryLimit = memoryLimit
    mSimplify.memoryLimit = memoryLimit
    mLyapunov.memoryLimit = memoryLimit

    // initialze tool thread pools
    mQE.init()
    mPegasus.init()
    mCEX.init()
    mODE.init()
    mPDE.init()
    mSim.init()
    mSolve.init()
    mAlgebra.init()
    mSimplify.init()
    mSOSsolve.init()
    mLyapunov.init()

    initialized = link match {
      case l: JLinkMathematicaLink =>
        val linkName = config.get("linkName") match {
          case Some(ln) => ln
          case None =>
            throw new IllegalArgumentException(
              """Mathematica not configured. Missing configuration parameter 'linkName'
                |Please configure settings in the UI.
                |Or specify the paths explicitly from command line by running
                |  java -jar keymaerax.jar -mathkernel pathtokernel -jlink pathtojlink
              """.stripMargin)
        }
        val libDir = config.get("libDir") // doesn't need to be defined
        l.init(linkName, libDir, config.getOrElse("tcpip", "true"))
      case l: WolframScript => l.init()
    }
  }

  /** Closes the connection to Mathematica */
  override def shutdown(): Unit = {
    mQE.shutdown()
    mPegasus.shutdown()
    mSOSsolve.shutdown()
    mCEX.shutdown()
    mODE.shutdown()
    mPDE.shutdown()
    mSim.shutdown()
    mSolve.shutdown()
    mAlgebra.shutdown()
    mSimplify.shutdown()
    mLyapunov.shutdown()
    //@note last, because we want to shut down all executors (tool threads) before shutting down the JLink interface
    link match {
      case l: JLinkMathematicaLink => l.shutdown()
      case l: WolframScript => l.shutdown()
    }
    initialized = false
  }

  /** Quantifier elimination on the specified formula, returns an equivalent quantifier-free formula plus Mathematica input/output as evidence */
  override def qe(formula: Formula): Lemma = {
    mQE.timeout = qeInitialTimeout
    try {
      mQE.run(ProvableSig.proveArithmeticLemma(_, formula))
    } catch {
      case ex: MathematicaComputationAbortedException if !StaticSemantics.freeVars(formula).isEmpty =>
        // formulas that are not universally closed usually have a counterexample, skip to max QE right away for partial QE
        if (qeMaxTimeout == 0) throw ex
        else doMaxQE(formula)
      case ex: MathematicaComputationAbortedException if qeCexTimeout != 0 =>
        mCEX.timeout = qeCexTimeout
        val cex = try {
          mCEX.findCounterExample(stripUniversalClosure(formula))
        } catch {
          case ex: MathematicaComputationUserAbortException =>
            //@note external abort means do not try any further
            throw ex
          case _: ToolException => None
        }
        cex match {
          case None if qeMaxTimeout == 0 => throw ex
          case None if qeMaxTimeout != 0 => doMaxQE(formula)
          case Some(cex) =>
            //@note only return Lemma if no open goals (but CEX tool not trusted, so impossible to create)
            throw BelleCEX("QE counterexample", cex, Sequent(IndexedSeq(), IndexedSeq(formula)))
        }
    }
  }

  /** Runs (parallel) QE with maximum timeout. */
  private def doMaxQE(formula: Formula): Lemma = {
    mQE.timeout = qeMaxTimeout
    if (Configuration.getBoolean(Configuration.Keys.MATHEMATICA_PARALLEL_QE).getOrElse(false) && StaticSemantics.freeVars(formula).isEmpty) {
      // ask parallel QE to find out how to prove, then follow that recipe to get lemmas and return combined
      // result; double the work but prefers soundness over splitting soundness-critically inside QETool and
      // directly believing that result
      val lemmas = qe(splitFormula(formula), continueOnFalse=true) match {
        case (Atom(fml), _) => List(mQE.run(ProvableSig.proveArithmeticLemma(_, fml)))
        case (AllOf(fmls), _) => fmls.map({
          case Atom(fml) => mQE.run(ProvableSig.proveArithmeticLemma(_, fml))
          case g => throw ToolExecutionException("Unable to split goal " + g + " into separate QE calls")
        })
      }
      val combined = ProvableSig.startProof(lemmas.map(_.fact.conclusion.succ.head).reduceRight(And))
      val result = lemmas.init.foldLeft(combined)({ case (c, l) => c(AndRight(SuccPos(0)), 0)(l.fact, 0) })(lemmas.last.fact, 0)
      Lemma(result, Nil)
    } else mQE.run(ProvableSig.proveArithmeticLemma(_, formula))
  }

  /** @inheritdoc */
  override def qe(goal: Goal, continueOnFalse: Boolean): (Goal, Formula) = firstResultQE(goal, continueOnFalse)

  private val INDEX = Variable("i")
  private val RESULT = PredOf(Function("result", None, Unit, Bool, interpreted=false), Nothing)

  /** Returns the result of the first QE call to succeed among the options in `goal`. Continues executing options when
   * option succeeds with result=false when continueOnFalse is set. */
  private def firstResultQE(goal: Goal, continueOnFalse: Boolean): (Goal, Formula) = {
    val ids = ListBuffer.empty[Goal]
    // {res, id, eids} = WaitNext[...]; AbortKernels[]; res
    val input = goal match {
      case g@Atom(fml) =>
        ids.append(g)
        list(int(ids.size-1), mQE.qeTool.qe(fml))
      case OneOf(oneOfGoals) => module(
        list(
          set(symbol("res"),list(int(-1), bool(false))),
          set(symbol("eids"), list(oneOfGoals.map({
            case g@Atom(fml) =>
              ids.append(g)
              parallelSubmit(list(int(ids.size-1), mQE.qeTool.qe(fml)))
            case g@AllOf(allOfGoals) =>
              ids.append(g)
              parallelSubmit(list(int(ids.size-1), and(allOfGoals.map({
                case Atom(g) => mQE.qeTool.qe(g)
                case _ => throw new IllegalArgumentException("Unsupported parallel QE feature: nested non-atom in AllOf")
              }):_*)))
            case OneOf(_) => throw new IllegalArgumentException("Unsupported parallel QE feature: nested OneOf in OneOf")
          }):_*))
        ),
        if (continueOnFalse) {
          compoundExpr(
            mwhile(and(equal(part(symbol("res"), int(2)), bool(false)), greater(ExtMathematicaOpSpec.length(symbol("res")), int(0))),
              set(list(symbol("res"), symbol("id"), symbol("eids")), waitNext(symbol("eids")))),
            abortKernels(),
            closeKernels(),
            symbol("res")
          )
        } else {
          compoundExpr(
            set(list(symbol("res"), symbol("id"), symbol("eids")), waitNext(symbol("eids"))),
            abortKernels(),
            closeKernels(),
            symbol("res")
          )
        }
      )
      case AllOf(_) => throw new IllegalArgumentException("Unsupported parallel QE feature: top-level AllOf")
    }
    try {
      mQE.timeout = qeMaxTimeout
      val (_, result) = mQE.qeTool.link.run(input, new UncheckedBaseM2KConverter {
        override def convert(e: MExpr): KExpr = {
          if (e.listQ()) {
            val (i, fml) = e.args.toList match {
              case i :: fml :: Nil => convert(i).asInstanceOf[Term] -> convert(fml).asInstanceOf[Formula]
              case e => throw ConversionException("Expected QE result list of length 2 {i,fml}, but got " + e.mkString(","))
            }
            And(Equal(INDEX, i), Equiv(RESULT, fml))
          }
          else super.convert(e)
        }
      })
      result match {
        case And(Equal(INDEX, Number(i)), Equiv(RESULT, fml)) => ids(i.toIntExact) -> fml
        case _ => throw ConversionException("Expected a formula result but got a non-formula expression: " + result.prettyString)
      }
    } finally { input.dispose() }
  }


  /** Transforms the leaves in goal `g` according to transformation `trafo`. */
  private def applyTo(g: Goal, trafo: Formula => Formula): Goal = g match {
    case Atom(goal) => Atom(trafo(goal))
    case OneOf(goals) => OneOf(goals.map(applyTo(_, trafo)))
    case AllOf(goals) => AllOf(goals.map(applyTo(_, trafo)))
  }

  /** Splits formula `fml` into QE goals that can potentially be executed concurrently. */
  private def splitFormula(fml: Formula): Goal = fml match {
    case Forall(x, p) => applyTo(splitFormula(p), Forall(x, _))
    case _: Imply =>
      val propSubgoals = ProvableSig.startProof(fml)(PropositionalTactics.prop, 0).subgoals
      val expandedSubgoals = ProvableSig.startProof(fml)(TactixLibrary.expandAll andThen PropositionalTactics.prop, 0)(TactixLibrary.applyEqualities).subgoals
      if (propSubgoals.size > 1) {
        if (expandedSubgoals.size > 1) OneOf(List(Atom(fml), AllOf(propSubgoals.map(p => Atom(p.toFormula))), AllOf(expandedSubgoals.map(p => Atom(p.toFormula)))))
        else OneOf(List(Atom(fml), AllOf(propSubgoals.map(p => Atom(p.toFormula)))))
      } else if (expandedSubgoals.size > 1) {
        OneOf(List(Atom(fml), AllOf(expandedSubgoals.map(p => Atom(p.toFormula)))))
      } else Atom(fml)
    case _ => Atom(fml)
  }

  /** Strips the universal quantifiers from a formula. Assumes shape \forall x (p(x) -> q(x)) */
  @tailrec
  private def stripUniversalClosure(fml: Formula): Formula = fml match {
    case f: Imply => f
    case Forall(_, f) => stripUniversalClosure(f)
    case f => throw ConversionException("Expected shape \\forall x (p(x) -> q(x)), but got " + f.prettyString)
  }

  /** Returns a formula describing the symbolic solution of the specified differential equation system.
   * @param diffSys The differential equation system
   * @param diffArg The independent variable of the ODE, usually time
   * @param iv Names of initial values per variable, e.g., x -> x_0
   * @return The solution, if found. None otherwise.
   */
  override def odeSolve(diffSys: DifferentialProgram, diffArg: Variable,
                        iv: Predef.Map[Variable, Variable]): Option[Formula] = mODE.odeSolve(diffSys, diffArg, iv)

  override def deriveBy(term: Term, v: Variable): Term = mODE.deriveBy(term, v)

  /**
   * Returns a counterexample for the specified formula.
   * @param formula The formula.
   * @return A counterexample, if found. None otherwise.
   */
  override def findCounterExample(formula: Formula): Option[Predef.Map[NamedSymbol, Expression]] = {
    mCEX.timeout = Configuration.getInt(Configuration.Keys.CEX_SEARCH_DURATION).getOrElse(10)
    mCEX.findCounterExample(formula)
  }

  /**
    * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
    * relation is a modality-free first-order formula. The simulation starts in a state where initial holds (first-order
    * formula).
    * @param initial A first-order formula describing the initial state.
    * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
    *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
    * @param steps The length of the simulation run (i.e., number of states).
    * @param n The number of simulations (different initial states) to create.
    * @return 'n' lists (length 'steps') of simulated states.
    */
  override def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation = mSim.simulate(initial, stateRelation, steps, n)

  /**
    * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
    * relation is a modality-free first-order formula. The simulation starts in the specified initial state.
    * @param initial The initial state: concrete values .
    * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
    *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
    * @param steps The length of the simulation run (i.e., number of states).
    * @return A list (length 'steps') of simulated states.
    */
  override def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun = mSim.simulateRun(initial, stateRelation, steps)

  /*override*/ def pdeSolve(diffSys: DifferentialProgram): Iterator[Term] = mPDE.pdeSolve(diffSys)
  override def solve(equations: Formula, vars: List[Expression]): Option[Formula] = mSolve.solve(equations,vars)
  override def quotientRemainder(term: Term, div: Term, x:Variable): (Term,Term) = mAlgebra.quotientRemainder(term,div,x)
  override def groebnerBasis(polynomials: List[Term]): List[Term] = mAlgebra.groebnerBasis(polynomials)
  override def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term) = mAlgebra.polynomialReduce(polynomial, GB)
  override def simplify(expr: Expression, assumptions: List[Formula]): Expression = mSimplify.simplify(expr, assumptions)
  override def simplify(expr: Formula, assumptions: List[Formula]): Formula = mSimplify.simplify(expr, assumptions)
  override def simplify(expr: Term, assumptions: List[Formula]): Term = mSimplify.simplify(expr, assumptions)
  override def invgen(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Seq[Either[Seq[(Formula, String)],Seq[(Formula, String)]]] = mPegasus.invgen(ode, assumptions, postCond)
  override def lzzCheck(ode: ODESystem, inv: Formula): Boolean = mPegasus.lzzCheck(ode, inv)
  override def refuteODE(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Option[Map[NamedSymbol, Expression]] = mPegasus.refuteODE(ode, assumptions, postCond)
  override def genODECond(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): (List[Formula],List[Formula]) = mPegasus.genODECond(ode, assumptions, postCond)
  override def sosSolve(polynomials: List[Term], variables: List[Term], degree: Int, timeout: Option[Int]): Result = mSOSsolve.sosSolve(polynomials, variables, degree, timeout)
  override def genCLF(sys: List[ODESystem]): Option[Term] = mLyapunov.genCLF(sys)
  override def genMLF(sys: List[ODESystem], trans: List[(Int, Int, Formula)]): List[Term] = mLyapunov.genMLF(sys, trans)


  /** Restarts the MathKernel with the current configuration */
  override def restart(): Unit = link match {
    case l: JLinkMathematicaLink => l.restart()
    case l: WolframScript => l.restart()
  }

  /** @inheritdoc */
  override def cancel(): Boolean = link.cancel()

  /** @inheritdoc */
  override def isInitialized: Boolean = initialized

  /** @inheritdoc */
  override def setOperationTimeout(timeout: Int): Unit = qeMaxTimeout = timeout

  /** @inheritdoc */
  override def getOperationTimeout: Int = qeMaxTimeout

  /** @inheritdoc */
  override def getAvailableWorkers: Int = 1
}
