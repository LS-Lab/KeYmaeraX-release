package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import java.math.RoundingMode

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.core
import spire.math._
import edu.cmu.cs.ls.keymaerax.core._

case class UnsimpleException() extends Exception
case class ValuelessException() extends Exception
case class TestFailureException() extends Exception

object Play {
  type number = Rational
  type state = Map[Ident, number]
  val ROUNDING_SCALE = 5

  private def holds(st: state, fml: Formula): Boolean = {
    fml match {
      case Less(l, r) => eval(st, l) < eval(st, r)
      case LessEqual(l, r) => eval(st, l) <= eval(st, r)
      case Greater(l, r) => eval(st, l) > eval(st, r)
      case GreaterEqual(l, r) => eval(st, l) >= eval(st, r)
      case Equal(l, r) => eval(st, l) == eval(st, r)
      case NotEqual(l, r) => eval(st, l) != eval(st, r)
      // @TODO dangerous
      case Not(f) => !holds(st, f)
      case Or(l, r) => holds(st, l) || holds(st, r)
      case And(l, r) => holds(st, l) && holds(st, r)
      // @TODO dangerous
      case Imply (l, r) =>  holds(st, r) || !holds(st, l)
      case Equiv (l, r) =>  holds(st, r) == holds(st, l)
      case True => true
      case False => false
      case _ => throw ValuelessException()
    }
  }

  private def eval(st: state, f: Term): number = {
    f match {
      case n: core.Number => Rational(n.value)
      case Plus(l, r) => eval(st, l) + eval(st, r)
      case Times(l, r) => eval(st, l) * eval(st, r)
      case Neg(f) => - eval(st, f)
      case Divide(l, r) => eval(st, l) / eval(st, r)
      case Power(l, r: core.Number) if r.value.isValidInt =>
        val n = r.value.intValue()
        eval(st, l).pow(n)
      // @TODO: Hack. For rational roots, convert rational to algebraic, compute root, convert back
      case Power(l, Divide(num: core.Number, denom: core.Number)) if num.value.isValidInt  && denom.value.isValidInt =>
        val v = eval(st, l)
        val n = num.value.intValue()
        val d = denom.value.intValue()
        val alg = v.toAlgebraic.nroot(d).pow(n)
        Rational(alg.toBigDecimal(ROUNDING_SCALE, RoundingMode.HALF_DOWN))
      case FuncOf(f, args) if f.interpreted =>
        (f.name, args) match {
          case ("max", Pair(l, r)) => eval(st, l).max(eval(st, r))
          case ("min", Pair(l, r)) => eval(st, l).min(eval(st, r))
          case ("abs", l) => eval(st, l).abs
          case _ => throw ValuelessException()
        }
      case _ => throw ValuelessException()
    }
  }

  def apply(as: AngelStrategy, ds: DemonStrategy[number]): Unit = {
    apply(Map(), as, ds)
  }

  def apply(st: state, as: AngelStrategy, ds: DemonStrategy[number]): state = {
    as match {
      case DTest(f) =>
        if (!holds(st, f))
          throw TestFailureException()
        st
      case DAssign(x, f) =>
        val v = eval(st, f)
        ds.writeAssign(x, v)
        st.+((x -> v))
      case NDAssign(x) =>
        val v = ds.readAssign(x)
        st.+((x -> v))
      case DLoop(s) =>
        var cur = st
        while(ds.readLoop) {
          cur = apply(cur, s, ds)
        }
        cur
      case DCompose(l, r) =>
        val mid = apply(st, l, ds)
        apply(mid, r, ds)
      case DChoice(l, r) =>
        if (ds.readChoice)
          apply(st, l, ds)
        else
          apply(st, r, ds)
      case _ => throw UnsimpleException()
    }
  }
}
