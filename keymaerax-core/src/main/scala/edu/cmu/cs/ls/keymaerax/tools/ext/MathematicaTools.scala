/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, FormulaTools, PosInExpr}
import edu.cmu.cs.ls.keymaerax.tools._
import edu.cmu.cs.ls.keymaerax.tools.ext.ExtMathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.ext.SimulationTool.{SimRun, SimState, Simulation}
import edu.cmu.cs.ls.keymaerax.tools.qe.{BinaryMathOpSpec, ExprFactory, K2MConverter, KeYmaeraToMathematica, M2KConverter, MathematicaNameConversion, MathematicaOpSpec, MathematicaToKeYmaera, NaryMathOpSpec, UnaryMathOpSpec}
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaConversion._
import edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec._
import edu.cmu.cs.ls.keymaerax.tools.install.PegasusInstaller
import edu.cmu.cs.ls.keymaerax.tools.qe._

import scala.collection.immutable
import scala.math.BigDecimal

object UncheckedBaseConverter {
  val CONST_FN_SUFFIX = "cnstfn"
  val CONST_PRED_SUFFIX = "cnstpred"
}

class UncheckedBaseM2KConverter extends MathematicaToKeYmaera {

  //@note unchecked, because ambiguous And==&& vs. And==Rules conversion
  override def k2m: K2MConverter[KExpr] = null
  override def apply(e: MExpr): KExpr = convert(e)

  /** Extends default converter with rule and rule list handling */
  override def convert(e: MExpr): KExpr = {
    if (isAborted(e)) {
      throw MathematicaComputationAbortedException(e.toString)
    }

    if (isTimedOut(e)) {
      throw MathematicaComputationTimedOutException(e.toString)
    }

    if (isFailed(e)) {
      throw MathematicaComputationFailedException(e.toString)
    }

    if (MathematicaOpSpec.rule.applies(e)) convertRule(e)
    else if (e.listQ() && e.args().forall(r => r.listQ() && r.args().forall(
      MathematicaOpSpec.rule.applies))) convertRuleList(e)
    // Derivatives are of the form Derivative[1][x]
    else if (e.head.args().length == 1 && e.head().args.head.integerQ() && e.head().args.head.asInt() == 1 &&
      e.head.head.symbolQ() && ExtMathematicaOpSpec.derivative.applies(e.head)) convertDerivative(e)
    else if (MathematicaOpSpec.lfalse.applies(e)) False
    else if (MathematicaOpSpec.ltrue.applies(e)) True
    else if (e.symbolQ() && MathematicaNameConversion.uncheckedUnmaskName(e.asString())._1.endsWith(UncheckedBaseConverter.CONST_FN_SUFFIX))
      MathematicaNameConversion.toKeYmaera(e) match {
        case BaseVariable(name, index, sort) => FuncOf(Function(name.substring(0, name.length - UncheckedBaseConverter.CONST_FN_SUFFIX.length), index, Unit, sort), Nothing)
      }
    else super.convert(e)
  }

  /** Converts rules and rule lists, not to be used in QE! */
  private def convertRule(e: MExpr): Formula = convert(e.args()(0)) match {
    case t: Term => Equal(t, convert(e.args()(1)).asInstanceOf[Term])
    case f: Formula => Equiv(f, convert(e.args()(1)).asInstanceOf[Formula])
    case _: Program => throw new IllegalArgumentException("There is no conversion from Mathematica to hybrid programs " + e)
  }

  private def convertRuleList(e: MExpr): Formula = {
    val convertedRules = e.args().map(_.args().map(r => convertRule(r)).reduceLeft(And))
    if (convertedRules.isEmpty) False
    else convertedRules.reduceLeft(Or)
  }

  private def convertDerivative(e: MExpr): KExpr = {
    require(e.args().length == 1, "Expected args size 1 (single differential symbol or single differential term)")
    require(e.head.args().length == 1 && e.head().args.head.integerQ() && e.head().args.head.asInt() == 1, "Expected 1 prime (e.g., v', not v'')")
    convert(e.args.head) match {
      case v: Variable => DifferentialSymbol(v)
      case t: Term => Differential(t)
    }
  }
}

class UncheckedBaseK2MConverter extends KeYmaeraToMathematica {

  //@note unchecked, because ambiguous And==&& vs. And==Rule in converse conversion
  override def m2k: M2KConverter[KExpr] = null
  override def apply(e: KExpr): MExpr = convert(e)

  override protected def convertFormula(f: Formula): MExpr = f match {
    case PredOf(Function(name, index, Unit, Bool, None), Nothing) =>
      if (name.endsWith("_")) MathematicaNameConversion.toMathematica(Variable(name.stripSuffix("_") + UncheckedBaseConverter.CONST_PRED_SUFFIX + "_", index))
      else MathematicaNameConversion.toMathematica(Variable(name + UncheckedBaseConverter.CONST_PRED_SUFFIX, index))
    case _ => super.convertFormula(f)
  }

  override protected[tools] def convertTerm(t: Term): MExpr = t match {
    case FuncOf(Function(name, index, Unit, Real, None), Nothing) =>
      if (name.endsWith("_")) MathematicaNameConversion.toMathematica(Variable(name.stripSuffix("_") + UncheckedBaseConverter.CONST_FN_SUFFIX + "_", index))
      else MathematicaNameConversion.toMathematica(Variable(name + UncheckedBaseConverter.CONST_FN_SUFFIX, index))
    case _ => super.convertTerm(t)
  }
}

object CEXK2MConverter extends K2MConverter[Either[KExpr, NamedSymbol]] {

  private val baseConverter = new UncheckedBaseK2MConverter {
    override def convert(e: KExpr): MExpr = {
      //insist on less strict input: interpreted function symbols allowed here
      insist(StaticSemantics.symbols(e).forall({ case fn@Function(_, _, _, _, Some(_)) => interpretedSymbols.exists(_._2 == fn) case _ => true }),
        "Interpreted functions must have known conversion to Mathematica")
      insist(disjointNames(StaticSemantics.symbols(e)), "Disjoint names required for Mathematica conversion")
      e match {
        case t: Term => convertTerm(t)
        case f: Formula => convertFormula(f)
        case _: Program => throw new IllegalArgumentException("There is no conversion from hybrid programs to Mathematica " + e)
        case _: Function => throw new IllegalArgumentException("There is no conversion from unapplied function symbols to Mathematica " + e)
      }
    }

    override protected[tools] def convertTerm(t: Term): MExpr = t match {
      //@note no back conversion -> no need to distinguish Differential from DifferentialSymbol
      case Differential(c) => ExtMathematicaOpSpec.primed(convert(c))
      case DifferentialSymbol(c) => ExtMathematicaOpSpec.primed(convert(c))
      case _ => super.convertTerm(t)
    }
  }

  private[tools] def convert(e: Either[KExpr, NamedSymbol]): MExpr = e match {
    case Left(expr) => baseConverter.convert(expr)
    case Right(v: Variable) => baseConverter.convert(v)
    case Right(fn@Function(_, _, Unit, Real, None)) => baseConverter.convert(FuncOf(fn, Nothing))
    case Right(fn@Function(_, _, Unit, Bool, None)) => baseConverter.convert(PredOf(fn, Nothing))
    case Right(e) => throw new IllegalArgumentException("Cannot convert " + e.prettyString)
  }

  override def m2k: M2KConverter[Either[KExpr, NamedSymbol]] = null
  override def apply(e: Either[KExpr, NamedSymbol]): MExpr = convert(e)

}

object CEXM2KConverter extends M2KConverter[Either[KExpr,NamedSymbol]] {
  private val baseConverter = new UncheckedBaseM2KConverter {
    override def apply(e: MExpr): KExpr = convert(e)

    override def convert(e: MExpr): KExpr = {
      if (ExtMathematicaOpSpec.complex.applies(e)) {
        val r :: i :: Nil = e.args().toList
        //@note not actually a complex number, encode only for the sake of reporting a counterexample
        FuncOf(Function("Complex", None, Real, Tuple(Real, Real), None), Pair(convert(r).asInstanceOf[Term], convert(i).asInstanceOf[Term]))
      } else super.convert(e)
    }

    override protected def convertAtomicTerm(e: MExpr): KExpr = {
      MathematicaNameConversion.toKeYmaera(e) match {
        case BaseVariable(name, None, _) if name == UncheckedBaseConverter.CONST_FN_SUFFIX => super.convertAtomicTerm(e)
        case BaseVariable(name, None, _) if name == UncheckedBaseConverter.CONST_PRED_SUFFIX => super.convertAtomicTerm(e)
        case BaseVariable(name, index, _) if name.endsWith(UncheckedBaseConverter.CONST_FN_SUFFIX) =>
          FuncOf(Function(name.stripSuffix(UncheckedBaseConverter.CONST_FN_SUFFIX), index, Unit, Real), Nothing)
        case BaseVariable(name, index, _) if name.endsWith(UncheckedBaseConverter.CONST_FN_SUFFIX + "_") =>
          FuncOf(Function(name.stripSuffix("_").stripSuffix(UncheckedBaseConverter.CONST_FN_SUFFIX) + "_", index, Unit, Real), Nothing)
        case BaseVariable(name, index, _) if name.endsWith(UncheckedBaseConverter.CONST_PRED_SUFFIX) =>
          PredOf(Function(name.stripSuffix(UncheckedBaseConverter.CONST_PRED_SUFFIX), index, Unit, Bool), Nothing)
        case BaseVariable(name, index, _) if name.endsWith(UncheckedBaseConverter.CONST_PRED_SUFFIX + "_") =>
          PredOf(Function(name.stripSuffix("_").stripSuffix(UncheckedBaseConverter.CONST_PRED_SUFFIX) + "_", index, Unit, Bool), Nothing)
        case _ => super.convertAtomicTerm(e)
      }
    }
  }

  override def k2m: K2MConverter[Either[KExpr, NamedSymbol]] = null
  override private[tools] def convert(e: MExpr): Either[KExpr,NamedSymbol] = try {
    Left(baseConverter.convert(e))
  } catch {
    case _: ConversionException => Left(Equal(Variable("unknown"), Variable("unknown")))
  }
  override def apply(e: MExpr): Either[KExpr,NamedSymbol] = convert(e)
}

object PlotConverter extends UncheckedBaseK2MConverter {
  override def apply(e: KExpr): MExpr = e match {
    case Imply(pre, Box(ODESystem(ode, domain), post)) =>
      val primedVars = DifferentialHelper.getPrimedVariables(ode)
      val vectorField = list(DifferentialHelper.atomicOdes(ode).map(o => apply(o.e)):_*)

      val show = NaryMathOpSpec(symbol("Show"))
      val regionPlot = NaryMathOpSpec(symbol("RegionPlot"))
      val streamPlot = NaryMathOpSpec(symbol("StreamPlot"))
      val regions = primedVars.map(v => list(apply(v), int(-5), int(5)))

      val plotPoints = rule(symbol("PlotPoints"), int(100))
      val postPlotStyle = rule(symbol("PlotStyle"), list(symbol("Red"), UnaryMathOpSpec(symbol("Opacity"))(double(0.5))))
      val prePlotStyle = rule(symbol("PlotStyle"), list(symbol("Green"), UnaryMathOpSpec(symbol("Opacity"))(double(0.5))))
      val domainPlotStyle = rule(symbol("PlotStyle"), list(symbol("Blue"), UnaryMathOpSpec(symbol("Opacity"))(double(0.5))))

      val prePlot = regionPlot((list(apply(pre)) +: (regions :+ prePlotStyle :+ plotPoints)): _*)
      val vfPlot = streamPlot((vectorField +: regions): _*)
      val domainPlot = regionPlot((list(apply(domain)) +: (regions :+ domainPlotStyle :+ plotPoints)): _*)
      val postPlot = regionPlot((list(apply(Not(post))) +: (regions :+ postPlotStyle :+ plotPoints)): _*)

      if (domain != True) show(prePlot, vfPlot, domainPlot, postPlot)
      else show(prePlot, vfPlot, postPlot)
    case _ => super.apply(e)
  }
}

object IdentityConverter extends M2KConverter[MExpr] {
  /** @inheritdoc */
  override def k2m: K2MConverter[MExpr] = null

  /** @inheritdoc */
  override private[tools] def convert(e: MExpr): MExpr = e
}

object PegasusK2MConverter extends UncheckedBaseK2MConverter {
  override protected def convertFormula(f: Formula): MExpr = f match {
    case PredOf(Function(name, index, Unit, Bool, None), Nothing) =>
      MathematicaNameConversion.toMathematica(Variable(name + UncheckedBaseConverter.CONST_PRED_SUFFIX, index))
    case _ => super.convertFormula(f)
  }

  override def convert(e: KExpr): MExpr = {
    //insist on less strict input: interpreted function symbols allowed here
    insist(StaticSemantics.symbols(e).forall({ case fn@Function(_, _, _, _, Some(_)) => interpretedSymbols.exists(_._2 == fn) case _ => true }),
      "Interpreted functions must have expected domain and sort")
    insist(disjointNames(StaticSemantics.symbols(e)), "Disjoint names required for Mathematica conversion")
    e match {
      case t: Term => convertTerm(t)
      case f: Formula => convertFormula(f)
      case _: Program => throw new IllegalArgumentException("There is no conversion from hybrid programs to Mathematica " + e)
      case _: Function => throw new IllegalArgumentException("There is no conversion from unapplied function symbols to Mathematica " + e)
    }
  }

  override protected[tools] def convertTerm(t: Term): MExpr = t match {
    //@note no back conversion -> no need to distinguish Differential from DifferentialSymbol
    case Differential(c) => ExtMathematicaOpSpec.primed(convert(c))
    case DifferentialSymbol(c) => ExtMathematicaOpSpec.primed(convert(c))
    case _ => super.convertTerm(t)
  }
}

object PegasusM2KConverter extends UncheckedBaseM2KConverter with Logging {
  private def diffSatResult: NaryMathOpSpec = new NaryMathOpSpec(com.wolfram.jlink.Expr.SYM_LIST) {
    override def applies(e: MExpr): Boolean = super.applies(e) && e.args.length == 3 &&
      MathematicaOpSpec.rule.applies(e.args()(0)) && MathematicaOpSpec.rule.applies(e.args()(1)) &&
      e.args()(0).args()(0) == symbol("ResultType") && e.args()(0).args()(1) == symbol("DiffSat")
  }

  private def trivialResult: NaryMathOpSpec = new NaryMathOpSpec(com.wolfram.jlink.Expr.SYM_LIST) {
    override def applies(e: MExpr): Boolean = super.applies(e) && e.args.length == 2 &&
      MathematicaOpSpec.rule.applies(e.args()(0)) && MathematicaOpSpec.rule.applies(e.args()(1)) &&
      e.args()(0).args()(0) == symbol("ResultType") && e.args()(0).args()(1) == symbol("Trivial")
  }

  private def errorResult: NaryMathOpSpec = new NaryMathOpSpec(com.wolfram.jlink.Expr.SYM_LIST) {
    override def applies(e: MExpr): Boolean = super.applies(e) && e.args.length == 2 &&
      MathematicaOpSpec.rule.applies(e.args()(0)) && MathematicaOpSpec.rule.applies(e.args()(1)) &&
      e.args()(0).args()(0) == symbol("ResultType") && e.args()(0).args()(1) == symbol("Error")
  }

  override def k2m: K2MConverter[KExpr] = null
  override def apply(e: MExpr): KExpr = convert(e)

  override def convert(e: MExpr): KExpr = {
    if (MathematicaOpSpec.ltrue.applies(e))   True
    else if (MathematicaOpSpec.lfalse.applies(e))  False
    else if (diffSatResult.applies(e)) convertDiffSatResult(e)
    else if (trivialResult.applies(e)) convertTrivialResult(e)
    else if (errorResult.applies(e)) convertErrorResult(e)
    else if (list.applies(e)) convertFormulaTermList(e)
    else super.convert(e)
  }

  private val LIST_LENGTH = FuncOf(Function("length", None, Real, Real), Variable("list"))

  /**
    * Encodes a differential saturation strategy result in a formula. The differential saturation strategy returns
    * results of the following shape.
    * {{{
    *   { ResultType -> DiffSat,
    *     Result -> {
    *       Invariant -> <formula>,
    *       Cuts      -> {
    *         { <formula>, Hint -> <variable> },
    *         ...
    *       },
    *       Proved -> <bool>
    *     },
    *     Meta -> {
    *       Timing -> { What -> Duration, ... }
    *     }
    *   }
    * }}}
    * We encode them in a single conjunction of the shape
    * {{{
    *   ResultType=DiffSat &
    *   ( Result <-> length(list)=3 &
    *                ( (Invariant <-> <formula>) &         // Result(0)
    *                  (Cuts <-> length(list)=<numCuts> &  // Result(1)
    *                            ( (<formula> & Hint=<variable>) &
    *                              ...
    *                            )
    *                  ) &
    *                  Proved <-> <bool>                   // Result(2)
    *                ) // end Result list
    *   ) // end Result
    * }}}
    * @param e The differential saturation strategy result.
    * @return The result encoded in a formula.
    */
  private def convertDiffSatResult(e: MExpr): Expression = {
    require(diffSatResult.applies(e), "Expected applicable Mathematica expression")

    def resultType: BinaryMathOpSpec = new BinaryMathOpSpec(symbol("Rule")) {
      override def applies(e: MExpr): Boolean =
        super.applies(e) && e.args()(0) == symbol("ResultType") && e.args()(1) == symbol("DiffSat")
    }
    def invariant: BinaryMathOpSpec = new BinaryMathOpSpec(symbol("Rule")) {
      override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("Invariant")
    }
    def cuts: BinaryMathOpSpec = new BinaryMathOpSpec(symbol("Rule")) {
      override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("Cuts") && list.applies(e.args()(1))
    }
    def hint: BinaryMathOpSpec = new BinaryMathOpSpec(symbol("Rule")) {
      override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("Hint")
    }
    def cut: NaryMathOpSpec = new NaryMathOpSpec(com.wolfram.jlink.Expr.SYM_LIST) {
      override def applies(e: MExpr): Boolean = super.applies(e) && e.args.length == 2 && hint.applies(e.args()(1))
    }
    def proved: BinaryMathOpSpec = new BinaryMathOpSpec(symbol("Rule")) {
      override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("Proved")
    }
    def result: NaryMathOpSpec = new NaryMathOpSpec(symbol("Rule")) {
      override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("Result") &&
      e.args()(1).listQ && e.args()(1).args.length == 3 &&
      invariant.applies(e.args()(1).args()(0)) && cuts.applies(e.args()(1).args()(1)) && proved.applies(e.args()(1).args()(2))
    }

    /** Converts {{{ResultType->DiffSat}}} into {{{ResultType=DiffSat}}}. */
    def convertResultType(e: MExpr): Formula = {
      require(resultType.applies(e), "Expected a rule 'ResultType -> DiffSat', but got " + e)
      Equal(Variable("ResultType"), Variable("DiffSat"))
    }
    /** Converts a result of the shape
      * {{{Result -> { Invariant -> <...>, Cuts -> <...>, Proved -> <...> } }}}
      * into
      * {{{Result <-> length(list)=3 & (Invariant <-> <...>) & (Cuts <-> <...>) & (Proved <-> <...>) }}}.
      * */
    def convertResult(e: MExpr): Formula = {
      def pred(s: String) = PredOf(Function(s, None, Unit, Bool), Nothing)

      /** Converts {{{Invariant -> <formula>}}} to {{{Invariant <-> <formula>}}}. */
      def convertInvariant(e: MExpr): Formula = {
        require(invariant.applies(e), "Expected a rule Invariant -> <formula>, but got " + e)
        convert(e.args()(1)) match {
          case f: Formula => Equiv(pred("Invariant"), f)
          case r => throw ConversionException("Unexpected content " + r + " in Invariant -> <formula>")
        }
      }

      /** Converts a hint {{{Hint-><variable>}}} into {{{Hint=<variable>}}}. */
      def convertHint(e: MExpr): Formula = {
        require(hint.applies(e), "Expected a hint of the form Hint-><hint>, but got " + e)
        convert(e.args()(1)) match {
          case v: BaseVariable => Equal(Variable("Hint"), v)
          case r => throw ConversionException("Unexpected content " + r + " in Hint -> <variable>")
        }
      }

      /** Converts a cut {{{ { <formula>, Hint-><variable> }}} into {{{ formula & Hint=<variable> }}} */
      def convertCut(e: MExpr): Formula = {
        require(cut.applies(e), "Expected a list of two elements { <formula>, Hint-><variable> }, but got " + e)
        convert(e.args()(0)) match {
          case f: Formula => And(f, convertHint(e.args()(1)))
          case r => throw ConversionException("Expected a formula but got " + r)
        }
      }

      /** Converts
        * {{{Cuts -> { { <formula>, Hint-><variable> }, ... } }}}
        * into
        * {{{Cuts <-> length(list)=n & (<formula> & Hint=<variable>) ... }}}.
        * */
      def convertCuts(e: MExpr): Formula = {
        require(cuts.applies(e), "Expected a rule Cuts -> { {<formula>, Hint-><...>}, ... }, but got " + e)
        Equiv(pred("Cuts"),
          if (e.args()(1).args.length > 0) And(Equal(LIST_LENGTH, Number(e.args()(1).args.length)), e.args()(1).args.map(convertCut).reduceLeft(And))
          else Equal(LIST_LENGTH, Number(e.args()(1).args.length))
        )
      }

      /** Converts {{{Proved-><bool>}}} to {{{Proved <-> <bool>}}}. */
      def convertProved(e: MExpr): Formula = {
        require(proved.applies(e), "Expected a rule Proved-><bool>")
        convert(e.args()(1)) match {
          case r@(True | False) => Equiv(pred("Proved"), r.asInstanceOf[Formula])
          case r => throw ConversionException("Unexpected content " + r + " in Proved-><bool>")
        }
      }

      require(result.applies(e), "Expected a result list of 3 rules: { Invariant -> <...>, Cuts -> <...>, Proved -> <...>")
      Equiv(pred("Result"), And(Equal(LIST_LENGTH, Number(3)),
        And(convertInvariant(e.args()(1).args()(0)),
          And(convertCuts(e.args()(1).args()(1)), convertProved(e.args()(1).args()(2)))
        )
      ))
    }
    logger.debug("Pegasus raw result: " + e)
    And(convertResultType(e.args()(0)), convertResult(e.args()(1)))
  }

  /**
    * Encodes a trivial result in a formula.
    * {{{
    *   { ResultType -> Trivial,
    *     Result -> Reason
    * }}}
    * We encode them in a single conjunction of the shape
    * {{{
    *   ResultType=Trivial & Result=Reason
    * }}}
    * @param e The trivial result.
    * @return The result encoded in a formula.
    */
  private def convertTrivialResult(e: MExpr): Expression = {
    assert(trivialResult.applies(e), "Expected applicable Mathematica expression")

    def resultType: BinaryMathOpSpec = new BinaryMathOpSpec(symbol("Rule")) {
      override def applies(e: MExpr): Boolean =
        super.applies(e) && e.args()(0) == symbol("ResultType") && e.args()(1) == symbol("Trivial")
    }

    def result: NaryMathOpSpec = new NaryMathOpSpec(symbol("Rule")) {
      override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("Result") && e.args()(1).symbolQ
    }

    /** Converts {{{ResultType->Trivial}}} into {{{ResultType=Trivial}}}. */
    def convertResultType(e: MExpr): Formula = {
      require(resultType.applies(e), "Expected a rule 'ResultType -> Trivial', but got " + e)
      Equal(Variable("ResultType"), Variable("Trivial"))
    }

    /** Converts Result->{ ... } */
    def convertResult(e: MExpr): Formula = {
      require(result.applies(e), "Expected Result-><...>")
      Equal(Variable("Result"), Variable(e.args()(1).asString))
    }

    And(convertResultType(e.args()(0)), convertResult(e.args()(1)))
  }

  /**
    * Converts an error result into an exception.
    * {{{
    *   { ResultType -> Error,
    *     Result -> {
    *       ErrorString -> <string>,
    *       InternalError -> <string>
    *     }
    *   }
    * }}}
    * We throw an exception.
    * @param e The error result.
    * @return Never returns, throws an exception.
    * @throws ToolExternalException always (unless inapplicable conversion)
    */
  private def convertErrorResult(e: MExpr): Expression = {
    require(errorResult.applies(e), "Expected applicable Mathematica expression")

    /** Converts Result->{ ... } */
    def convertResult(e: MExpr): Expression = {
      def errorString: NaryMathOpSpec = new NaryMathOpSpec(symbol("Rule")) {
        override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("ErrorString")
      }
      def internalError: NaryMathOpSpec = new NaryMathOpSpec(symbol("Rule")) {
        override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("InternalError")
      }
      def result: NaryMathOpSpec = new NaryMathOpSpec(symbol("Rule")) {
        override def applies(e: MExpr): Boolean = super.applies(e) && e.args()(0) == symbol("Result") &&
          e.args()(1).listQ && e.args()(1).args.length == 2 &&
          errorString.applies(e.args()(1).args()(0)) && internalError.applies(e.args()(1).args()(1))
      }

      require(result.applies(e), "Expected a result list of 2 rules: { ErrorString -> <...>, InternalError -> <...>")
      val errorMessage = e.args()(1).args()(0)
      throw new ToolExternalException(errorMessage.args()(1).asString(), null) {}
    }

    convertResult(e.args()(1))
  }

  /** Extracts the list of (invariant,hint) and a proved/candidate indicator from the Pegasus result formula
    * @see [[convertDiffSatResult]], [[convertTrivialResult]]
    */
  def extractResult(result: Expression): (immutable.Seq[(Formula, String)], Formula) = {
    def extractCuts(cuts: Formula): immutable.Seq[(Formula, String)] = cuts match {
      case And(Equal(LIST_LENGTH, Number(numCuts)), cutFmls) =>
        FormulaTools.leftConjuncts(cutFmls, numCuts.toIntExact).map({
          case And(cutFml, Equal(BaseVariable("Hint", None, _), BaseVariable(hint, None, _))) => (cutFml, hint)
          case r => throw ConversionException("Expected formula & Hint=<hint>, but got " + r.prettyString)
        })
      case Equal(LIST_LENGTH, Number(numCuts)) if numCuts == 0 => immutable.Seq.empty
      case _ => throw ConversionException("Expected length(list)=n & ..., but got " + cuts.prettyString)
    }

    result match {
      case And(Equal(BaseVariable("ResultType", None, Real), BaseVariable("DiffSat", None, Real)), result) => result match {
        case Equiv(PredOf(Function("Result", None, _, _, _), Nothing), And(Equal(LIST_LENGTH, Number(n)), resultElements)) if n.toIntExact == 3 => resultElements match {
          case And(Equiv(PredOf(Function("Invariant", None, _, _, _), Nothing), invariant),
               And(Equiv(PredOf(Function("Cuts", None, _, _, _), Nothing), cuts),
                   Equiv(PredOf(Function("Proved", None, _, _, _), Nothing), proved))) =>
            val extractedCuts = extractCuts(cuts)
            if (extractedCuts.length > 1) (extractCuts(cuts) :+ (invariant, "Unknown"), proved)
            else (extractCuts(cuts), proved) //@note invariant is identical to the single/non-existent cut
          case _ => throw ConversionException("Expected (Invariant <-> ...) & (Cuts <-> ...) & (Proved <-> ...), but got " + resultElements.prettyString)
        }
        case _ => throw ConversionException("Expected Result <-> length(list)=3 & ..., but got " + result.prettyString)
      }
      case And(Equal(BaseVariable("ResultType", None, Real), BaseVariable("Trivial", None, Real)), result) => result match {
        case Equal(BaseVariable("Result", None, Real), BaseVariable(reason, _, _)) => ((True, reason) :: Nil, True)
      }
      case _ => throw ConversionException("Expected ResultType=[DiffSat|Trivial] & ..., but got " + result.prettyString)
    }
  }

  /** Decodes the term generated by convertFormulaTermList back into a list of terms. */
  def decodeTermList(listTrm: Expression): List[Term] = {
    listTrm match {
      case Pair(l,r) =>
        l :: decodeTermList(r)
      case Nothing => List()
      case _ =>
        throw ConversionException("Expected a term list to decode but got a ill-formed expression: " + listTrm.prettyString)
    }
  }

  private def convertFormulaTermList(e: MExpr): Expression = {
    if (e.listQ) {
      val elements = e.args().map(convert)
      if (elements.nonEmpty && elements.forall(_.isInstanceOf[Formula])) {
        //@HACK first conjunct length(list)=... indicates length of list
        elements.map(_.asInstanceOf[Formula]).reduceOption(And) match {
          case Some(fmls) => And(Equal(LIST_LENGTH, Number(e.args.length)), fmls)
          case None => Equal(LIST_LENGTH, Number(e.args.length))
        }
      } else if (elements.forall(_.isInstanceOf[Term])) {
        (elements :+ Nothing).map(_.asInstanceOf[Term]).reduceRight(Pair)
      } else throw ConversionException("Pegasus converter expected either list of formulas or list of terms")
    } else throw ConversionException("Expected a list, but got " + e)
  }
}



/**
 * Mathematica counter example implementation.
  *
  * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class MathematicaCEXTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[Either[KExpr,NamedSymbol]](link, CEXK2MConverter, CEXM2KConverter) with CounterExampleTool with Logging {

  def findCounterExample(fml: Formula): Option[Map[NamedSymbol, Expression]] = {
    val cexVars = StaticSemantics.symbols(fml).filter({ case Function(_, _, _, _, interp) => interp.isEmpty case _ => true})

    if (StaticSemantics.symbols(fml).exists({ case fn@Function(_, _, _, _, Some(_)) => !MathematicaOpSpec.interpretedSymbols.exists(_._2 == fn) case _ => false})) None
    else if (cexVars.nonEmpty) {
      //@note numeric counterexamples
      val input = ExtMathematicaOpSpec.n(ExtMathematicaOpSpec.findInstance(
        k2m.convert(Left(fml match { case Imply(a, b) => And(a, Not(b)) case _ => Not(fml) })),
        MathematicaOpSpec.list(cexVars.toList.sorted.map(s => k2m.convert(Right(s))):_*),
        MathematicaOpSpec.reals.op
      ))
      run(input) match {
        case (_, Left(cex: Formula)) => cex match {
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
        case result =>
          logger.debug("No counterexample, Mathematica returned: " + result)
          None
      }
    } else {
      None
    }
  }
}

/**
  * A link to Mathematica using the JLink interface.
  *
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class MathematicaODESolverTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[KExpr](link, new UncheckedBaseK2MConverter, new UncheckedBaseM2KConverter) with ODESolverTool with DerivativeTool {

  def odeSolve(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Variable]): Option[Formula] =
    diffSol(diffArg, iv, toDiffSys(diffSys, diffArg):_*)

  /**
    * Converts a system of differential equations given as DifferentialProgram into list of x'=theta
    *
    * @param diffSys The system of differential equations
    * @param diffArg The name of the differential argument (dx/d diffArg = theta).
    * @return The differential equation system in list form.
    */
  private def toDiffSys(diffSys: DifferentialProgram, diffArg: Variable): List[(Variable, Term)] = {
    var result = List[(Variable, Term)]()
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case AtomicODE(DifferentialSymbol(x), theta) if x != diffArg => result = result :+ (x, theta); Left(None)
        case AtomicODE(DifferentialSymbol(x), _) if x == diffArg => Left(None)
        case ODESystem(_, _) => Left(None)
        case DifferentialProduct(_, _) => Left(None)
      }
    }, diffSys)
    result
  }

  /**
    * Computes the symbolic solution of a system of differential equations.
    *
    * @param diffArg The differential argument, i.e., d f(diffArg) / d diffArg.
    * @param diffSys The system of differential equations of the form x' = theta.
    * @return The solution if found; None otherwise
    */
  private def diffSol(diffArg: Variable, iv: Map[Variable, Variable], diffSys: (Variable, Term)*): Option[Formula] = {
    val primedVars = diffSys.map(_._1)
    val functionalizedTerms = diffSys.map{ case (x, theta) => ( x, functionalizeVars(theta, diffArg, primedVars:_*)) }
    val mathTerms = functionalizedTerms.map({case (x, theta) =>
      (ExtMathematicaOpSpec.dx(ExtMathematicaOpSpec.primed(k2m(x)))(k2m(diffArg)), k2m(theta))})
    val convertedDiffSys = mathTerms.map({case (x, theta) => MathematicaOpSpec.equal(x, theta)})

    val functions = diffSys.map(t => k2m(functionalizeVars(t._1, diffArg)))

    val initialValues = diffSys.map(t => k2m(
      Equal(functionalizeVars(t._1, Number(BigDecimal(0)), primedVars:_*), iv(t._1))))

    val input = ExtMathematicaOpSpec.dsolve(
      MathematicaOpSpec.list(convertedDiffSys ++ initialValues:_*),
      MathematicaOpSpec.list(functions:_*),
      k2m(diffArg)
    )

    val (_, result) = run(input)
    result match {
      case f: Formula => Some(defunctionalize(f, diffArg, primedVars.map(_.name):_*))
      case _ => None
    }
  }

  /**
    * Replaces all occurrences of variables vars in the specified term t with functions of argument arg.
    *
    * @param t The term.
    * @param arg The function argument.
    * @param vars The variables to functionalize.
    * @return The term with variables replaced by functions.
    */
  private def functionalizeVars(t: Term, arg: Term, vars: Variable*) = ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case v@BaseVariable(name, idx, sort) if vars.isEmpty || vars.contains(v) =>
          Right(FuncOf(Function(name, idx, arg.sort, sort), arg))
        case _ => Left(None)
      }
    }, t) match {
    case Some(resultTerm) => resultTerm
    case None => throw ConversionException("Unable to functionalize " + t)
  }

  /**
    * Replaces all functions with argument arg in formula f with a variable of the same name.
    *
    * @param f The formula.
    * @param arg The function argument.
    * @return The term with functions replaced by variables.
    */
  private def defunctionalize(f: Formula, arg: Term, fnNames: String*) = ExpressionTraversal.traverse(
    new ExpressionTraversalFunction {
      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case FuncOf(Function(name, idx, _, range, None), fnArg) if arg == fnArg
          && (fnNames.isEmpty || fnNames.contains(name)) => Right(Variable(name, idx, range))
        case _ => Left(None)
      }
    }, f) match {
    case Some(resultF) => resultF
    case None => throw ConversionException("Unable to defunctionalize " + f)
  }

  def deriveBy(term: Term, v: Variable): Term = {
    val mathTerm = k2m(term)
    val mathVar = k2m(v)
    val input = ExtMathematicaOpSpec.d(mathTerm, mathVar)
    val (_, result) = run(input)
    result match {
      case t: Term => t
    }
  }
}

/**
  * A link to Mathematica using the JLink interface.
  *
  * @author Andre Platzer
  */
class MathematicaPDESolverTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[KExpr](link, new UncheckedBaseK2MConverter, new DiffUncheckedM2KConverter) with PDESolverTool {

  def pdeSolve(diffSys: DifferentialProgram): Iterator[Term] = {
    val vars = DifferentialHelper.getPrimedVariables(diffSys).map(k2m).toArray
    val f = MathematicaOpSpec.symbol(DiffUncheckedM2KConverter.PREFIX + "f")
    val fall = ExprFactory.makeExpr(f, vars)
    val characteristics:List[MExpr] = DifferentialHelper.atomicOdes(diffSys).map({
      case AtomicODE(DifferentialSymbol(x),t) =>
        MathematicaOpSpec.times(k2m(t), ExtMathematicaOpSpec.d(fall, k2m(x)))
    })
    val pde = MathematicaOpSpec.equal(MathematicaOpSpec.plus(characteristics:_*), k2m(Number(0)))
    val input = ExtMathematicaOpSpec.dsolve(
      pde, fall, MathematicaOpSpec.list(vars:_*), MathematicaOpSpec.rule(
        ExtMathematicaOpSpec.generatedParameters.op,
        ExtMathematicaOpSpec.function(MathematicaOpSpec.symbol(DiffUncheckedM2KConverter.PREFIX + "C"))
      )
    )
    val (_, result) = run(input)
    result match {
        //@note List[List[Rule]] are converted to Or of And of Equal where only the right side matters.
      case r: Equal => List(r.right).iterator
      case r: And => FormulaTools.conjuncts(r).map({case Equal(_,b) => b}).iterator
      case r: Or => FormulaTools.disjuncts(r).flatMap(disj=>FormulaTools.conjuncts(disj).map{case Equal(_,b) => b}).iterator
      case r => throw ToolExecutionException("Mathematica did not solve the PDE for : " + diffSys + "\n" + r)
    }
  }
}

class MathematicaLyapunovSolverTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[KExpr](link, PegasusK2MConverter, PegasusM2KConverter) with LyapunovSolverTool {

  private val LYAPUNOV_NAMESPACE = "Lyapunov`"

  private def lsymbol(s: String): MExpr = symbol(LYAPUNOV_NAMESPACE + s)

  private val pegasusPath = PegasusInstaller.pegasusRelativeResourcePath
  private val pathsList = Configuration.sanitizedPathSegments(Configuration.KEYMAERAX_HOME_PATH, pegasusPath).map(string)
  private val joinedPath = fileNameJoin(list(pathsList:_*))
  private val setPathsCmd = compoundExpression(setDirectory(joinedPath), appendTo(path.op, joinedPath))

  /** Wraps `cmd` with the path and exception handling (suppressing). */
  private def createCommand(cmd: MExpr): MExpr = quiet(compoundExpression(
    setPathsCmd,
    needs(string(LYAPUNOV_NAMESPACE), fileNameJoin(list(pathsList :+ string("Primitives") :+ string("Lyapunov.m"):_*))),
    cmd
  ))

  /** Converts the differential equation systems `sys`. */
  private def convertODEs(sys: List[ODESystem]): MExpr = {
    list(sys.map(ode => {
      val primedVars = DifferentialHelper.getPrimedVariables(ode)
      val atomicODEs = DifferentialHelper.atomicOdes(ode)
      val vars = list(primedVars.map(k2m):_*)
      val vectorField = list(atomicODEs.map(o => k2m(o.e)):_*)
      list(vectorField, vars, k2m(ode.constraint))
    }):_*)
  }

  /** @inheritdoc */
  override def genCLF(sys: List[ODESystem]): Option[Term] = {
    val cmd = createCommand(applyFunc(lsymbol("GenCLF"))(convertODEs(sys)))
    val (_, result) = run(cmd)
    result match {
      case t: Term => flattenPairs(t).headOption
      case t => throw ConversionException("Unexpected Lyapunov Function result: " + t.prettyString) //@todo
    }
  }

  /** @inheritdoc */
  override def genMLF(sys: List[ODESystem], trans: List[(Int, Int, Formula)]): List[Term] = {
    val cmd = createCommand(applyFunc(lsymbol("GenMLF"))(
      convertODEs(sys),
      list(trans.map({ case (s, t, g) => list(int(s), int(t), k2m(g)) }):_*)
    ))
    val (_, result) = run(cmd)
    result match {
      case t: Term => flattenPairs(t)
      case t => throw ConversionException("Unexpected Lyapunov Function result: " + t.prettyString) //@todo
    }
  }

  /** Flattens the pairs in term `t` into a list of terms. */
  private def flattenPairs(t: Term): List[Term] = t match {
    case Nothing => List.empty
    case Pair(l, r) => flattenPairs(l) ++ flattenPairs(r)
    case t => List(t)
  }
}

object DiffUncheckedM2KConverter {
  val PREFIX = "xyk`"
}

/**
  * Accept n-ary arguments as for PDESolve.
  */
private class DiffUncheckedM2KConverter extends UncheckedBaseM2KConverter {

  override def convert(e: MExpr): KExpr = {
    if (e.listQ() && e.args().length == 1) {
      //HACK: convert unique Groebner basis result
      convert(e.args().head)
    } else super.convert(e)
  }

  protected override def convertAtomicTerm(e: MExpr): KExpr = interpretedSymbols.find(_._1.applies(e)) match {
    case Some((_, fn)) => convertFunction(fn, e.args())
    case None =>
      toKeYmaera(e) match {
        case fn: Function =>
          insist(!fn.interpreted, "Expected uninterpreted function symbol, but got interpreted " + fn)
          convertFunction(fn, e.args())
        case result: Variable => result
      }
  }

  private def toKeYmaera(e: MExpr): NamedSymbol = {
    if (e.head.asString().startsWith(DiffUncheckedM2KConverter.PREFIX)) {
      val name = e.head.asString().substring(DiffUncheckedM2KConverter.PREFIX.length)
      val index = None
      val fnDomain = convertFunctionDomain(e.args())
      Function(name, index, fnDomain, Real, interp = None)
    } else {
      MathematicaNameConversion.toKeYmaera(e)
    }
  }


  protected def convertFunctionDomain(args: Array[MExpr]): Sort = {
    Range(1,args.length).foldRight[Sort](Real)((_, t) => Tuple(Real,t))
  }
  protected override def convertFunction(fn: Function, args: Array[MExpr]): KExpr = {
    val arguments = args.map(convert).map(_.asInstanceOf[Term])
    FuncOf(fn, arguments.reduceRightOption[Term]((l, r) => Pair(l, r)).getOrElse(Nothing))
  }
}

/**
  * A link to Mathematica using the JLink interface.
  *
  * @author Andre Platzer
  */
class MathematicaEquationSolverTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[KExpr](link, new UncheckedBaseK2MConverter, new UncheckedBaseM2KConverter) with EquationSolverTool {

  def solve(equations: Formula, vars: List[Expression]): Option[Formula] = {
    val eqs = k2m(equations)
    val v = vars.map(k2m)

    val input = ExtMathematicaOpSpec.solve(eqs, MathematicaOpSpec.list(v:_*))
    val (_, result) = run(input)
    result match {
      case f: Formula => Some(f)
      case _ => None
    }
  }
}

/**
  * A link to Mathematica using the JLink interface.
  *
  * @author Andre Platzer
  */
class MathematicaAlgebraTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[KExpr](link, new UncheckedBaseK2MConverter, PegasusM2KConverter) with AlgebraTool {

  override def quotientRemainder(term: Term, div: Term, x:Variable): (Term,Term) = {
    val t = k2m(term)
    val d = k2m(div)
    val v = k2m(x)

    val input = ExtMathematicaOpSpec.polynomialQuotientRemainder(t, d, v)
    val (_, result) = run(input)
    result match {
      case Pair(quot,Pair(rem,Nothing)) => (quot, rem)
      case r => throw ConversionException("Unexpected output " + r + " of class " + r.getClass)
    }
  }

  override def groebnerBasis(polynomials: List[Term]): List[Term] = {
    //@note sort for stable results
    val vars = polynomials.flatMap(p => StaticSemantics.vars(p).symbols[NamedSymbol]).distinct.sorted
    val input = ExtMathematicaOpSpec.groebnerBasis(
      MathematicaOpSpec.list(polynomials.map(k2m):_*),
      MathematicaOpSpec.list(vars.map(k2m):_*),
      MathematicaOpSpec.rule(ExtMathematicaOpSpec.monomialOrder.op, ExtMathematicaOpSpec.degreeReverseLexicographic.op),
      MathematicaOpSpec.rule(ExtMathematicaOpSpec.coefficientDomain.op, ExtMathematicaOpSpec.rationals.op)
    )
    val (_, result) = run(input)
    result match {
      // turn nested back into list of terms
      case r: Term => PegasusM2KConverter.decodeTermList(r)
      case r => throw ConversionException("Unexpected output " + r + " of class " + r.getClass)
    }
  }

  override def polynomialReduce(polynomial: Term, GB: List[Term]): (List[Term], Term) = {
    //@note sort for stable results
    val vars = (polynomial::GB).flatMap(p => StaticSemantics.vars(p).symbols[NamedSymbol]).distinct.sorted
    val input = ExtMathematicaOpSpec.polynomialReduce(
      k2m(polynomial),
      MathematicaOpSpec.list(GB.map(k2m):_*),
      MathematicaOpSpec.list(vars.map(k2m):_*),
      MathematicaOpSpec.rule(ExtMathematicaOpSpec.monomialOrder.op, ExtMathematicaOpSpec.degreeReverseLexicographic.op),
      MathematicaOpSpec.rule(ExtMathematicaOpSpec.coefficientDomain.op, ExtMathematicaOpSpec.rationals.op)
    )
    val (_, result) = run(input)
    result match {
      //Mathematica returns [l,r] where l is a list, r is a singleton
      case Pair(l,Pair(r,Nothing)) => (PegasusM2KConverter.decodeTermList(l), r)
      case r => throw ConversionException("Unexpected output " + r + " of class " + r.getClass)
    }
  }
}

/**
  * A link to Mathematica using the JLink interface.
  *
  * @author Andre Platzer
  */
class MathematicaSimplificationTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[KExpr](link, new UncheckedBaseK2MConverter, new UncheckedBaseM2KConverter) with SimplificationTool {

  override def simplify(expr: Formula, assumptions: List[Formula]): Formula =
    simplify(expr.asInstanceOf[Expression], assumptions).asInstanceOf[Formula]

  override def simplify(expr: Term, assumptions: List[Formula]): Term =
    simplify(expr.asInstanceOf[Expression], assumptions).asInstanceOf[Term]

  override def simplify(expr: Expression, assumptions: List[Formula]): Expression = expr match {
    case _: AtomicTerm => expr
    case _ =>
      val ex = k2m(expr)
      val assuming = assumptions.map(k2m)

      val input = ExtMathematicaOpSpec.fullSimplify(ex, MathematicaOpSpec.list(assuming:_*))
      val (_, result) = run(input)
      result match {
        case r: Expression => r
        case _ => throw ToolExecutionException("Mathematica did not successfuly simplify: " + expr + " under assumptions " + assumptions)
      }
  }
}

object SimulationM2KConverter extends M2KConverter[Simulation] {

  //@note unchecked, because in back-translation we don't know whether end-of-world 'false' was present in original or not
  def k2m: K2MConverter[Simulation] = null
  override def apply(e: MExpr): Simulation = convert(e)

  private val m2k: M2KConverter[KExpr] = new UncheckedBaseM2KConverter

  override def convert(e: MExpr): Simulation = {
    if (e.listQ() && e.args.forall(_.listQ())) {
      val states: Array[Array[KExpr]] = e.args().map(_.args().map(m2k))
      states.map(state => {
        val endOfWorld = if (state.contains(False)) state.indexOf(False) else state.length
        state.slice(0, endOfWorld).map({
          case fml: Formula => FormulaTools.conjuncts(fml).map({
            case Equal(name: NamedSymbol, value: Number) => name -> value
            case Equal(FuncOf(fn, _), value: Number) => fn -> value
            case s => throw ConversionException("Expected state description Equal(...), but got " + s)
          }).toMap
          case s => throw ConversionException("Expected state formula, but got " + s)
        }).toList}).toList
    } else throw ConversionException("Expected list of simulation states, but got " + e)
  }
}

object SimulationK2MConverter extends K2MConverter[Simulation] {

  //@note unchecked, because don't know whether end-of-world 'false' was present in original or not
  def m2k: M2KConverter[Simulation] = null
  override def apply(e: Simulation): MExpr = convert(e)

  private val k2m: K2MConverter[KExpr] = new UncheckedBaseK2MConverter

  override def convert(e: Simulation): MExpr = {
    MathematicaOpSpec.list(
      e.map(r => MathematicaOpSpec.list(
        r.map(s => k2m(s.map{ case (n: Term, v) => Equal(n, v) }.reduceLeft(And))):_*
      )):_*
    )
  }
}

/**
  * A link to Mathematica using the JLink interface.
  *
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class MathematicaSimulationTool(override val link: MathematicaLink) extends BaseKeYmaeraMathematicaBridge[Simulation](link, SimulationK2MConverter, SimulationM2KConverter) with SimulationTool {
  private val basek2m = new UncheckedBaseK2MConverter

  def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation = {
    // init[n_] := Map[List[#]&, FindInstance[a>=..., {a, ...}, Reals, n]] as pure function
    val init =
      ExtMathematicaOpSpec.setDelayed(
        MathematicaOpSpec.symbol("kyx`init"),
        ExtMathematicaOpSpec.function(
          ExtMathematicaOpSpec.map(
            ExtMathematicaOpSpec.function(MathematicaOpSpec.list(ExtMathematicaOpSpec.placeholder)),
            ExtMathematicaOpSpec.findInstance(
              basek2m(initial),
              MathematicaOpSpec.list(StaticSemantics.symbols(initial).toList.sorted.map(basek2m):_*),
              MathematicaOpSpec.reals.op,
              ExtMathematicaOpSpec.placeholder)
          )
        )
      )
    // step[pre_] := Module[{apre=a/.pre, ...}, FindInstance[apre>=..., {a, ...}, Reals]] as pure function
    val (stepPreVars, stepPostVars) = StaticSemantics.symbols(stateRelation).filter(_.isInstanceOf[Variable]).partition(_.name.startsWith("pre"))
    val pre2post = stepPostVars.filter(_.name != "t_").map(v => Variable("pre" + v.name, v.index, v.sort) -> v).toMap[NamedSymbol, NamedSymbol]

    val stepModuleInit = stepPreVars.toList.sorted.map(s =>
      ExtMathematicaOpSpec.set(
        basek2m(s),
        ExtMathematicaOpSpec.replaceAll(
          basek2m(pre2post.getOrElse(s, throw new IllegalArgumentException("No post variable for " + s.prettyString))),
          ExtMathematicaOpSpec.placeholder
        )
      )).toArray

    val step = ExtMathematicaOpSpec.setDelayed(
        MathematicaOpSpec.symbol("kyx`step"),
        ExtMathematicaOpSpec.function(
          MathematicaOpSpec.module(
            MathematicaOpSpec.list(stepModuleInit:_*),
            ExtMathematicaOpSpec.findInstance(
              basek2m(stateRelation),
              MathematicaOpSpec.list(stepPostVars.toList.sorted.map(basek2m):_*),
              MathematicaOpSpec.reals.op
            )
          )
        )
      )
    // Map[N[NestList[step,#,steps]]&, init[n]]
    val exec =
      ExtMathematicaOpSpec.map(
        ExtMathematicaOpSpec.function(
          ExtMathematicaOpSpec.n(
            ExtMathematicaOpSpec.nestList(
              MathematicaOpSpec.symbol("kyx`step"),
              ExtMathematicaOpSpec.placeholder,
              MathematicaOpSpec.int(steps)
            )
          )
        ),
        MathematicaOpSpec.mapply(
          MathematicaOpSpec.symbol("kyx`init"),
          MathematicaOpSpec.list(MathematicaOpSpec.int(n))
        )
      )
    // initial;step;simulate
    val simulate = ExtMathematicaOpSpec.quiet(ExtMathematicaOpSpec.compoundExpression(init, step, exec))

    run(simulate)._2
  }

  /** @inheritdoc */
  override def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun = Nil
}
