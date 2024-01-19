/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.ext

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.btactics.InvGenTool
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.tools.ConversionException
import edu.cmu.cs.ls.keymaerax.tools.ext.ExtMathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.install.PegasusInstaller
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.qe.{BinaryMathOpSpec, MathematicaOpSpec, NaryMathOpSpec, UnaryMathOpSpec}
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}

import scala.collection.immutable.Seq

/**
 * A continuous invariant implementation using Mathematica over the JLink interface.
 * @author Andrew Sogokon, based on QETool by Nathan Fulton and Stefan Mitsch
 */
class MathematicaInvGenTool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[Expression](link, PegasusK2MConverter, PegasusM2KConverter)
    with InvGenTool with Logging {

  private val PEGASUS_NAMESPACE = "Pegasus`"
  private val GENERICNONLINEAR_NAMESPACE = "GenericNonLinear`"
  private val GENERICLINEAR_NAMESPACE = "GenericLinear`"
  private val DIFFSATURATION_NAMESPACE = "DiffSaturation`"
  private val INVARIANTEXTRACTOR_NAMESPACE = "InvariantExtractor`"
  private val LZZ_NAMESPACE = "LZZ`"
  private val REFUTE_NAMESPACE = "Refute`"
  private val CLASSIFIER_NAMESPACE = "Classifier`"

  private def psymbol(s: String) = symbol(PEGASUS_NAMESPACE + s)
  private def gnlsymbol(s: String) = symbol(GENERICNONLINEAR_NAMESPACE + s)
  private def glsymbol(s: String) = symbol(GENERICLINEAR_NAMESPACE + s)
  private def dssymbol(s: String) = symbol(DIFFSATURATION_NAMESPACE + s)
  private def invexsymbol(s: String) = symbol(INVARIANTEXTRACTOR_NAMESPACE + s)

  private val pegasusRelativePath = PegasusInstaller.pegasusRelativeResourcePath
  private val joinedPath = fileNameJoin(list(Configuration.sanitizedPathSegments(Configuration.KEYMAERAX_HOME_PATH, pegasusRelativePath).map(string).toSeq:_*))
  private val setPathsCmd = compoundExpression(setDirectory(joinedPath), appendTo(path.op, joinedPath))

  /** @inheritdoc */
  override def invgen(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Seq[Either[Seq[(Formula, String)], Seq[(Formula, String)]]] = {
    require(postCond.isFOL, "Unable to generate invariant, expected FOL post conditions but got " + postCond.prettyString)
    timeout = -1 // reap must be outermost, so do not set tool timeout (which is automatically translated to timeconstrained), but instead use commandTimeout in timeConstrained below
    val commandTimeout = Configuration.Pegasus.invGenTimeout(-1)

    val primedVars = DifferentialHelper.getPrimedVariables(ode)
    val atomicODEs = DifferentialHelper.atomicOdes(ode)
//    val constantSlopeVars = atomicODEs.filter(_.e.isInstanceOf[Number]).map(_.xp.x)
//    val isTimeTriggered = FormulaTools.conjuncts(ode.constraint).exists({
//      //@todo most common case
//      case LessEqual(x, y) => y match {
//        case t: Term if StaticSemantics.freeVars(t).intersect(primedVars.toSet).isEmpty => constantSlopeVars.contains(x)
//        case _ => false
//      }
//      case _ => false
//    })
//
//    if (isTimeTriggered) throw new TacticInapplicableFailure("Pegasus does not yet support time-triggered systems")

    val vars = list(primedVars.map(k2m):_*)
    val vectorField = list(atomicODEs.map(o => k2m(o.e)):_*)
    val problem = list(
      k2m(assumptions.flatMap(FormulaTools.conjuncts).filter(_.isPredicateFreeFOL).reduceOption(And).getOrElse(True)),
      list(vectorField, vars, k2m(ode.constraint)),
      k2m(postCond)
    )
    logger.debug("Raw Mathematica input into Pegasus: " + problem)

    def timeoutExpr(t: Int) = if (t >= 0) int(t) else infinity

    val setOptions = applyFunc(symbol("SetOptions"))
    val options = compoundExpression(
      setOptions(psymbol("InvGen"),
        rule(psymbol("SanityCheckTimeout"), timeoutExpr(Configuration.Pegasus.sanityTimeout()))),
      setOptions(gnlsymbol("PreservedState"),
        rule(gnlsymbol("Timeout"), timeoutExpr(Configuration.Pegasus.PreservedStateHeuristic.timeout()))),
      setOptions(gnlsymbol("HeuInvariants"),
        rule(gnlsymbol("Timeout"), timeoutExpr(Configuration.Pegasus.HeuristicInvariants.timeout()))),
      setOptions(gnlsymbol("FirstIntegrals"),
        rule(gnlsymbol("Timeout"), timeoutExpr(Configuration.Pegasus.FirstIntegrals.timeout())),
        rule(gnlsymbol("Deg"), int(Configuration.Pegasus.FirstIntegrals.degree()))),
      setOptions(gnlsymbol("DbxPoly"),
        rule(gnlsymbol("Timeout"), timeoutExpr(Configuration.Pegasus.Darboux.timeout())),
        rule(gnlsymbol("MaxDeg"), int(Configuration.Pegasus.Darboux.degree())),
        rule(gnlsymbol("Staggered"), bool(Configuration.Pegasus.Darboux.staggered()))),
      setOptions(glsymbol("FirstIntegralsLin"),
        rule(glsymbol("Timeout"), timeoutExpr(Configuration.Pegasus.LinearFirstIntegrals.timeout()))),
      setOptions(glsymbol("LinearMethod"),
        rule(glsymbol("Timeout"), timeoutExpr(Configuration.Pegasus.LinearGenericMethod.timeout())),
        rule(glsymbol("RationalsOnly"), bool(Configuration.Pegasus.LinearGenericMethod.rationalsOnly())),
        rule(glsymbol("RationalPrecision"), int(Configuration.Pegasus.LinearGenericMethod.rationalPrecision())),
        rule(glsymbol("FirstIntegralDegree"), int(Configuration.Pegasus.LinearGenericMethod.firstIntegralDegree()))),
      setOptions(gnlsymbol("BarrierCert"),
        rule(gnlsymbol("Timeout"), timeoutExpr(Configuration.Pegasus.Barrier.timeout())),
        rule(gnlsymbol("Deg"), int(Configuration.Pegasus.Barrier.degree()))),
      setOptions(dssymbol("DiffSat"),
        rule(dssymbol("MinimizeCuts"), bool(Configuration.Pegasus.DiffSaturation.minimizeCuts())),
        rule(dssymbol("StrictMethodTimeouts"), bool(Configuration.Pegasus.DiffSaturation.strictMethodTimeouts())),
        rule(dssymbol("UseDependencies"), bool(Configuration.Pegasus.DiffSaturation.useDependencies()))
      ),
      setOptions(invexsymbol("DWC"),
        rule(invexsymbol("SufficiencyTimeout"), int(Configuration.Pegasus.InvariantExtractor.sufficiencyTimeout())),
        rule(invexsymbol("DWTimeout"), int(Configuration.Pegasus.InvariantExtractor.dwTimeout()))
      )
    )

    val reap = UnaryMathOpSpec(symbol("Reap"))

    val timeConstrained: BinaryMathOpSpec =
      MathematicaOpSpec.timeConstrained

    val set = BinaryMathOpSpec(symbol("Set"))
    val mIf = NaryMathOpSpec(symbol("If"))
    val part = BinaryMathOpSpec(symbol("Part"))
    val failureQ = UnaryMathOpSpec(symbol("FailureQ"))
    val length = UnaryMathOpSpec(symbol("Length"))
    val trueQ = UnaryMathOpSpec(symbol("TrueQ"))

    val pegasusMain = Configuration.Pegasus.mainFile("Pegasus.m")
    //@note quiet suppresses messages, since translated into Exception in command runner
    val command = quiet(compoundExpression(
      setPathsCmd,
      needs(string(PEGASUS_NAMESPACE), string(pegasusMain)),
      options,
      // without intermediate result extraction: applyFunc(psymbol("InvGen"))(problem)
      compoundExpression(
        set(
          symbol("reaped"),
          reap(timeConstrained(applyFunc(psymbol("InvGen"))(problem), int(commandTimeout))))
        ),
        mIf(
          trueQ(and(failureQ(part(symbol("reaped"), int(1))), greater(length(part(symbol("reaped"), int(2))), int(0)))),
          part(part(part(symbol("reaped"), int(2)), int(1)), int(-1)),
          part(symbol("reaped"), int(1))
        )
      )
    )

    try {
      val (output, result) = run(command)
      logger.debug("Generated invariant: " + result.prettyString + " from raw output " + output)
      val (invariants, flag) = PegasusM2KConverter.extractResult(result)
      assert(flag == True || flag == False, "Expected invariant/candidate flag, but got " + flag.prettyString)
      if (flag == True) Left(invariants) :: Nil else Right(invariants) :: Nil
    } catch {
      case ex: Throwable =>
        logger.warn("Pegasus invariant generator exception", ex)
        Nil
    }
  }

  /** @inheritdoc */
  override def lzzCheck(ode: ODESystem, inv: Formula): Boolean = {
    timeout = Configuration.Pegasus.invCheckTimeout(-1)

    val vars = list(DifferentialHelper.getPrimedVariables(ode).map(k2m):_*)
    val vectorField = list(DifferentialHelper.atomicOdes(ode).map(o => k2m(o.e)):_*)
    val command = compoundExpression(
      setPathsCmd,
      needs(string(LZZ_NAMESPACE), fileNameJoin(list(string("Primitives"), string("LZZ.m")))),
      applyFunc(symbol(LZZ_NAMESPACE + "InvS"))(k2m(inv), vectorField, vars, k2m(ode.constraint))
    )

    val (output, result) = runUnchecked(command.toString)
    logger.debug("LZZ check: "+ result.prettyString + " from raw output " + output)
    result match {
      case True => true
      case False => false
      case _ => throw ConversionException("Expected true/false from Pegasus call but got expression: " +
        result.prettyString)
    }
  }

  /** @inheritdoc */
  override def refuteODE(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Option[Map[NamedSymbol, Expression]] = {
    require(postCond.isFOL, "Unable to refute ODE, expected FOL post conditions but got " + postCond.prettyString)
    require(assumptions.forall(_.isFOL), "Unable to refute ODE, expected FOL assumptions but got " + assumptions)

    timeout = Configuration.Pegasus.invCheckTimeout(-1)

    val rhs = DifferentialHelper.atomicOdes(ode).map(_.e)
    // All things that need to be considered as parameters (or variables)
    val fmlvars = (assumptions :+ postCond :+ ode.constraint).flatMap(StaticSemantics.symbols)
    val trmvars = rhs.flatMap(StaticSemantics.symbols)

    val vars = (trmvars ++ fmlvars).distinct.filter({ case Function(_, _, _, _, interp) => interp.isEmpty case _ => true}).sorted
      .map({
        case f@Function(_,_,Unit,_,_) => FuncOf(f, Nothing) //for k2m conversion to work reliably on constants
        case e => e
      })

    val odeVars = list(DifferentialHelper.getPrimedVariables(ode).map(k2m):_*)
    val varsList = list(vars.map(k2m):_*)
    val vectorField = list(rhs.map(k2m):_*)

    val command = compoundExpression(
      setPathsCmd,
      needs(string(REFUTE_NAMESPACE), string("Refute.m")),
      applyFunc(symbol(REFUTE_NAMESPACE + "RefuteS"))(
        k2m(assumptions.reduceOption(And).getOrElse(True)),
        k2m(postCond),
        vectorField,
        odeVars,
        k2m(ode.constraint),
        varsList
      )
    )

    try {
      val (output, result) = runUnchecked(command.toString, CEXM2KConverter)
      logger.debug("Counterexample: " + result + " from raw output " + output)
      result match {
        case Left(cex: Formula) => cex match {
          case False =>
            logger.debug("No counterexample, Mathematica returned: " + cex.prettyString)
            None
          case _ =>
            logger.debug("Counterexample " + cex.prettyString)
            Some(FormulaTools.conjuncts(cex).map({
              case Equal(name: DifferentialSymbol, value) => name -> value
              case Equal(name: Variable, value) => name -> value
              case Equal(FuncOf(fn, _), value) => fn -> value
              case Equiv(PredOf(fn, _), value) => fn -> value
            }).toMap)
        }
        case _ =>
          logger.debug("No counterexample, Mathematica returned: " + result)
          None
      }
    } catch {
      case ex: ConversionException =>
        logger.warn("Conversion exception", ex)
        None
    }
  }

  /** @inheritdoc */
  override def genODECond(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): (List[Formula],List[Formula]) = {
    require(postCond.isFOL, "Unable to generate ODE conditions, expected FOL post conditions but got " + postCond.prettyString)
    require(assumptions.forall(_.isFOL), "Unable to generate ODE conditions, expected FOL assumptions but got " + assumptions)

    timeout = Configuration.Pegasus.invCheckTimeout(-1)

    val odeVars = list(DifferentialHelper.getPrimedVariables(ode).map(k2m):_*)
    val vectorField = list(DifferentialHelper.atomicOdes(ode).map(_.e).map(k2m):_*)
    val command = compoundExpression(
      setPathsCmd,
      needs(string(REFUTE_NAMESPACE), string("Refute.m")),
      applyFunc(symbol(REFUTE_NAMESPACE + "SeqFml"))(
        k2m(assumptions.reduceOption(And).getOrElse(True)),
        k2m(postCond),
        vectorField,
        odeVars,
        k2m(ode.constraint)
      )
    )

    val (output, result) = runUnchecked(command.toString)
    result match {
      case And(Equal(_, n: Number), And(And(And( And(i1, i2), n1), n2), n3)) =>
        assert(n.value.toInt == 5)
        (List(i1, i2), List(n1, n2, n3))
      case _ =>
        logger.warn("Incorrect pattern returned: " + output)
        (List(), List())
    }
  }

  /**
    * Returns dimension and classification of the problem defined by `ode` with assumptions `assumptions` and
    * postcondition `postCond`.
    * @param ode The differential equation system including evolution domain constraint.
    * @param assumptions Assumptions on the initial state.
    * @param postCond Postcondition
    * @return The dimension and classification of the problem.
    */
  def problemClassification(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): (Int, String, Map[String, Map[String, String]]) = {
    require(postCond.isFOL, "Unable to generate ODE conditions, expected FOL post conditions but got " + postCond.prettyString)
    require(assumptions.forall(_.isFOL), "Unable to generate ODE conditions, expected FOL assumptions but got " + assumptions)

    val vars = list(DifferentialHelper.getPrimedVariables(ode).map(k2m):_*)
    val vectorField = list(DifferentialHelper.atomicOdes(ode).map(_.e).map(k2m):_*)
    val problem = list(
      k2m(assumptions.reduceOption(And).getOrElse(True)),
      list(vectorField, vars, k2m(ode.constraint)),
      k2m(postCond)
    )

    val command = compoundExpression(
      setPathsCmd,
      needs(string(CLASSIFIER_NAMESPACE), string("NewClassifier.m")),
      applyFunc(symbol(CLASSIFIER_NAMESPACE + "ClassifyProblem"))(problem)
    )

    val (_, result) = runUnchecked(command.toString, IdentityConverter)
    val dimension :: classes :: details :: Nil = result.args().toList

    def asTuple(t: Expr): (String, String) = {
      require(rule.applies(t), "Expected Rule[String,String]")
      val key :: value :: Nil = t.args().map(_.asString).toList
      (key, value)
    }

    def asCategory(cat: Expr): (String, Map[String, String]) = {
      require(rule.applies(cat), "Expected Rule[String, {...}]")
      val key :: values :: Nil = cat.args().toList
      (key.asString, values.args().map(asTuple).toMap)
    }

    (dimension.asInt(), classes.args().head.asString, details.args().map(asCategory).toMap)
  }
}
