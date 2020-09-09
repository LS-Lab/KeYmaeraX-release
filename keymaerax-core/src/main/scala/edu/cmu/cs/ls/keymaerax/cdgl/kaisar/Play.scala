package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import java.math.RoundingMode

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Play.{ROUNDING_SCALE, number, state}
import edu.cmu.cs.ls.keymaerax.core
import spire.math._
import edu.cmu.cs.ls.keymaerax.core._

case class UnsimpleException(nodeID: Int) extends Exception
case class ValuelessException(nodeID: Int = -1) extends Exception
case class TestFailureException(nodeID: Int) extends Exception

class Environment {
  var state: Play.state = Map()

  def contains(x: Ident): Boolean = state.contains(x)

  def set(x: Ident, v: Play.number): Unit = (state = state.+(x -> v))

  def get(x: Ident): Play.number = state(x)

  def holds(fml: Formula): Boolean = {
    fml match {
      case Less(l, r) => eval(l) < eval(r)
      case LessEqual(l, r) => eval(l) <= eval(r)
      case Greater(l, r) => eval(l) > eval(r)
      case GreaterEqual(l, r) => eval(l) >= eval(r)
      case Equal(l, r) => eval(l) == eval(r)
      case NotEqual(l, r) => eval(l) != eval(r)
      // @TODO dangerous
      case Not(f) => !holds(f)
      case Or(l, r) => holds(l) || holds(r)
      case And(l, r) => holds(l) && holds(r)
      // @TODO dangerous
      case Imply (l, r) =>  holds(r) || !holds(l)
      case Equiv (l, r) =>  holds(r) == holds(l)
      case True => true
      case False => false
      case _ => throw ValuelessException()
    }
  }

  def eval(f: Term): number = {
    f match {
      case n: core.Number => Rational(n.value)
      case Plus(l, r) => eval(l) + eval(r)
      case Minus(l, r) => eval(l) - eval(r)
      case Times(l, r) => eval(l) * eval(r)
      case Neg(f) => - eval(f)
      case Divide(l, r) => eval(l) / eval(r)
      case Power(l, r: core.Number) if r.value.isValidInt =>
        val n = r.value.intValue()
        eval(l).pow(n)
      // @TODO: Hack. For rational roots, convert rational to algebraic, compute root, convert back
      case Power(l, Divide(num: core.Number, denom: core.Number)) if num.value.isValidInt  && denom.value.isValidInt =>
        val v = eval(l)
        val n = num.value.intValue()
        val d = denom.value.intValue()
        val alg = v.toAlgebraic.nroot(d).pow(n)
        Rational(alg.toBigDecimal(ROUNDING_SCALE, RoundingMode.HALF_DOWN))
      case FuncOf(f, args) if f.interpreted =>
        (f.name, args) match {
          case ("max", Pair(l, r)) => eval(l).max(eval(r))
          case ("min", Pair(l, r)) => eval(l).min(eval(r))
          case ("abs", l) => eval(l).abs
          case _ => throw ValuelessException()
        }
      case v: Variable =>
        if (state.contains(v))
          state(v)
        else {
          println(s"Unknown value for variable $v")
          throw ValuelessException()
        }
      case _ =>
        println(s"Couldn't evaluate $f in state $state")
        throw ValuelessException()
    }
  }

}

object Play {
  type number = Rational
  type state = Map[Ident, number]
  val ROUNDING_SCALE = 5

  def apply(as: AngelStrategy, ds: DemonStrategy[number]): Environment = {
    val env = new Environment()
    // in-place updates to environment
    apply(env, as, ds)
    env
  }

  def apply(env: Environment, as: AngelStrategy, ds: DemonStrategy[number]): Unit = {
    as match {
      case DTest(f) =>
        try {
          if (!env.holds(f)) {
            println(s"""Test \"$f\" failed in state ${env.state}""")
            throw TestFailureException(as.nodeID)
          }
        } catch {
          case v: ValuelessException => throw ValuelessException(as.nodeID)
        }
      case DAssign(x, f) =>
        try {
          val v = env.eval(f)
          ds.writeAssign(as.nodeID, x, v)
          //println(s"Interpreter assigned $x -> $v")
          env.set(x, v)
        } catch {
          case v: ValuelessException => throw ValuelessException(as.nodeID)
        }
      case NDAssign(x) =>
        val v = ds.readAssign(as.nodeID, x)
        //println(s"Interpreter star-assigned $x -> $v")
        env.set(x, v)
      case DLoop(s) =>
        // in-place update
        while(ds.readLoop(as.nodeID)) {
          apply(env, s, ds)
        }
      case DCompose(children) =>
        // in-place update of env
        children.foreach(x => apply(env, x, ds))
      case DChoice(l, r) =>
        if (ds.readChoice(as.nodeID))
          apply(env, l, ds)
        else
          apply(env, r, ds)
      case _ => throw UnsimpleException(as.nodeID)
    }
  }
}
