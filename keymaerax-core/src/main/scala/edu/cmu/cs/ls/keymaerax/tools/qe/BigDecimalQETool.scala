package edu.cmu.cs.ls.keymaerax.tools.qe

import java.math.{MathContext, RoundingMode}

import edu.cmu.cs.ls.keymaerax.core.{And, BinaryCompositeTerm, Divide, Equal, Evidence, False, Formula, FuncOf, Function, Greater, GreaterEqual, Less, LessEqual, Minus, Neg, NotEqual, Number, Or, Pair, Plus, Power, QETool, Real, Term, Times, True, Tuple, UnaryCompositeTerm}
import edu.cmu.cs.ls.keymaerax.tools.ToolBase

import scala.collection.immutable.Map

/** (Hopefully) trustworthy and fast tool to help speed up IntervalArithmeticV2
  * 'proves' quantifier- and variable-free arithmetic formulas by evaluation with BigDecimals
 *
  * @author Fabian Immler
  */
object BigDecimalQETool extends ToolBase("BigDecimal QE Tool") with QETool {
  initialized = true

  // TODO: taken from DifferentialTactics, should perhaps be in a more central place?
  val maxF = Function("max", None, Tuple(Real, Real), Real, interpreted=true)
  val minF = Function("min", None, Tuple(Real, Real), Real, interpreted=true)

  def isNumeric(t: Term) : Boolean = t match {
    case t: BinaryCompositeTerm => isNumeric(t.left) && isNumeric(t.right)
    case t: UnaryCompositeTerm => isNumeric(t.child)
    case Number(a) => true
    case FuncOf(m, Pair(a, b)) if m == minF || m == maxF => isNumeric(a) && isNumeric(b)
    case _ => false
  }
  def eval(t: Term) : BigDecimal = t match {
    case Plus(a, b) => eval(a) + eval(b)
    case Minus(a, b) => eval(a) - eval(b)
    case Neg(a) => -eval(a)
    case Times(a, b) => eval(a) * eval(b)
    case Power(a, b) =>
      (eval(a), eval(b)) match {
        case (x, y) if y.isValidInt && y >= 1 => x pow y.toIntExact
        case (x, y) if x != 0 && y == 0 => BigDecimal(1)
        case (x, y) if x == BigDecimal(10) && y.isValidInt => BigDecimal(1).bigDecimal.scaleByPowerOfTen(y.toIntExact)
        case (x, y) => throw new IllegalArgumentException("Power " + x + " ^ " + y + " can not be computed exactly")
      }
    case Number(a) => BigDecimal(a.bigDecimal, new MathContext(0, RoundingMode.UNNECESSARY))
    case FuncOf(m, Pair(a, b)) if m == minF => eval(a) min eval(b)
    case FuncOf(m, Pair(a, b)) if m == maxF => eval(a) max eval(b)
    case Divide(a, b) => throw new IllegalArgumentException("Division is not guaranteed to be representable without error: " + t)
  }
  def eval(fml: Formula) : Boolean = fml match {
    case LessEqual(s, t) => eval(s) <= eval(t)
    case GreaterEqual(s, t) => eval(s) >= eval(t)
    case Less(s, t) => eval(s) < eval(t)
    case Greater(s, t) => eval(s) > eval(t)
    case Equal(s, t) => eval(s) == eval(t)
    case NotEqual(s, t) => eval(s) != eval(t)
    case And(f, g) => eval(f) && eval(g)
    case Or(f, g) => eval(f) || eval(g)
    case True => true
    case False => false
  }

  def qeEvidence(formula: Formula) = (if (eval(formula)) True else formula, new Evidence {
    val message = "evaluated BigDecimal numerics"
  })
  def init(config: Map[String,String]) = ()
  def restart() = ()
  def shutdown() = ()
}
