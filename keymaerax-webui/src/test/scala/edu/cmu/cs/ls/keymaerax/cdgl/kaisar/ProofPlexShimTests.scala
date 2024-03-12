/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Test synthesizer by running synthesized code with simple shim code
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/** Test synthesized Angel strategies against handwritten do-nothing Demon strategies */
class ProofPlexShimTests extends TacticTestBase {
  val check: String => Statement = Kaisar.statementProved

  "ProofPlex Interpreter" should "execute 1D car against trivial demon" in withMathematica { _ =>
    val pf = check(SharedModels.essentialsSafeCar1D)
    val angel = SimpleStrategy(AngelStrategy(pf))
    val factory = UnknowingFactory(RatFactory)
    val env: Environment[TernaryNumber[RatNum]] = new Environment(factory)
    val demon = new EssentialsSafeCar1DShim(env)
    demon.init()
    // @TODO: Braking case test v >= B/T eventually fails after reaching destination
    a[TestFailureException] shouldBe thrownBy(new Play(factory)(env, angel, demon))
    println("Final state: " + env.state)
    val goal = env.state(Variable("d"))
    (env.state(Variable("x")) >= (goal * factory.number(Rational(0.8)))) shouldBe KnownTrue()
    (env.state(Variable("x")) <= goal) shouldBe KnownTrue()
  }

  "Simple Strategy Wrapper" should "execute 1D car against simple demon strategy" in withMathematica { _ =>
    val pf = check(SharedModels.essentialsSafeCar1D)
    val angel = SimpleStrategy(AngelStrategy(pf))
    val factory = UnknowingFactory(RatFactory)
    val env: Environment[TernaryNumber[RatNum]] = new Environment(factory)
    val demon = new WrappedDemonStrategy(new EssentialsSafeCar1DBasicStrategy(env))(env)
    demon.init()
    // @TODO: Braking case test v >= B/T eventually fails after reaching destination
    a[TestFailureException] shouldBe thrownBy(new Play(factory)(env, angel, demon))
    println("Final state: " + env.state)
    val goal = env.get(Variable("d"))
    (env.state(Variable("x")) >= (goal * factory.number(Rational(0.8)))) shouldBe KnownTrue()
    (env.state(Variable("x")) <= goal) shouldBe KnownTrue()
  }

  it should "execute 1D car with native interval type" in withMathematica { _ =>
    val pf = check(SharedModels.essentialsSafeCar1D)
    val angel = SimpleStrategy(AngelStrategy(pf))
    val factory = RatIntFactory
    val env: Environment[RatIntNum] = new Environment(factory)
    val demon = new WrappedDemonStrategy(new EssentialsSafeCar1DBasicStrategy(env))(env)
    demon.init()
    a[TestFailureException] shouldBe thrownBy(new Play(factory)(env, angel, demon))
    println("Final state: " + env.state)
    val goal = env.get(Variable("d"))
    (env.state(Variable("x")) >= (goal * factory.number(Rational(0.8)))) shouldBe KnownTrue()
    (env.state(Variable("x")) <= goal) shouldBe KnownTrue()
  }
}

class EssentialsSafeCar1DBasicStrategy[number <: Numeric[number, Ternary]](val env: Environment[number])
    extends BasicDemonStrategy[number] {
  override def init(stringArg: Option[String], intArgs: List[NodeID]): Unit = {}
  override def exit(): Unit = {}
  override def reportViolation(): Unit = {}

  var iterationsLeft: Int = 100
  val readInitState: Map[Ident, number] = Map(
    Variable("A") -> 2,
    Variable("B") -> 2,
    Variable("x") -> 0,
    Variable("v") -> 0,
    Variable("a") -> 0,
    DifferentialSymbol(Variable("x")) -> 0,
    DifferentialSymbol(Variable("v")) -> 0,
    Variable("d") -> 200,
    Variable("T") -> 1,
    Variable("t") -> 0,
    DifferentialSymbol(Variable("t")) -> 1,
  ).map({ case (k, v) => (k, env.factory.number(Rational(v))) })

  def readDemonLoop(id: NodeID): Boolean = {
    iterationsLeft = iterationsLeft - 1;
    iterationsLeft >= 0
  }

  def readDemonChoice(id: NodeID): Boolean = throw new Exception("Model does not contain demon choice")

  def readDemonAssign(id: NodeID, x: String, varIndex: Option[Int]): number = {
    // differential equation has been reduced to * assignments
    // Note: avoid failing the v >= 0 constraint
    val T = valFor(Variable("T"))
    val (xVal, vVal, aVal) = (valFor(Variable("x")), valFor(Variable("v")), valFor(Variable("a")))
    val dur: number = if (aVal >= env.factory.number(Rational(0)) == KnownTrue()) T else T.min(vVal) / -aVal
    x match {
      case "t" => dur
      case "v" => vVal + aVal * dur
      case "x" => xVal + vVal * dur + aVal * dur * dur * env.factory.number(Rational(0.5))
      case "t'" => env.factory.number(Rational(1))
      case "v'" => aVal
      case "x'" => vVal + aVal * dur
      case _ => throw new DemonException("Demon does not know how to assign variable: " + x)
    }
  }
  def writeAngelAssign(id: NodeID, x: String, varIndex: Option[Int], f: number): Unit =
    println(s"Controller updated $x -> $f (full name: ${x}_$varIndex)")
}

class EssentialsSafeCar1DShim[number <: Numeric[number, Ternary]](val env: Environment[number])
    extends DemonStrategy[number] {
  override def reportViolation(): Unit = {}
  val initValues: Map[Ident, number] = Map(
    Variable("A") -> 2,
    Variable("B") -> 2,
    Variable("x") -> 0,
    Variable("v") -> 0,
    Variable("a") -> 0,
    DifferentialSymbol(Variable("x")) -> 0,
    DifferentialSymbol(Variable("v")) -> 0,
    Variable("d") -> 200,
    Variable("T") -> 1,
    Variable("t") -> 0,
    DifferentialSymbol(Variable("t")) -> 1,
  ).map({ case (k, v) => (k, env.factory.number(Rational(v))) })

  var iterationsLeft: Int = 100

  override def readLoop(id: NodeID): Boolean = {
    iterationsLeft = iterationsLeft - 1;
    iterationsLeft >= 0
  }

  // Only choice is between accel (false) and brake (true) branches
  override def readChoice(id: NodeID): Boolean = {
    val accelFml = "((v + T*A)^2/(2*B) <= (d - (x + v*T + (A*T^2)/2)))".asFormula
    val brakeFml = "((v + T*A)^2/(2*B)  + 1 >= (d - (x + v*T + (A*T^2)/2)))".asFormula
    val (a, b) = (env.holds(accelFml), env.holds(brakeFml))
    assert((a || b) == KnownTrue())
    KnownTrue() == !a // false = accelerate, favor acceleration in case a && b
  }

  private def updated(x: Ident, v: number): number = { env.set(x, v); v }

  private def plainVar(v: Variable): Variable = {
    v match {
      case BaseVariable(name, index, sort) => Variable(name)
      case DifferentialSymbol(BaseVariable(name, index, sort)) => DifferentialSymbol(Variable(name))
    }
  }

  // in case values are accessed before initialization
  private def valFor(x: Ident): number = {
    if (env.contains(x)) env.get(x)
    else {
      val v = initValues(x)
      env.set(x, v)
      v
    }
  }

  override def readAssign(id: NodeID, xSSA: Ident): number = {
    val x = plainVar(xSSA)
    // initialization
    if (!env.contains(x)) return valFor(x)
    // differential equation has been reduced to * assignments
    // Note: avoid failing the v >= 0 constraint
    val T = valFor(Variable("T"))
    val (xVal, vVal, aVal) = (valFor(Variable("x")), valFor(Variable("v")), valFor(Variable("a")))
    val dur: number = if (KnownTrue() == aVal >= env.factory.number(Rational(0))) T else T.min(vVal) / -aVal
    x match {
      case BaseVariable("t", _, _) => updated(xSSA, dur)
      case BaseVariable("v", _, _) => updated(xSSA, vVal + aVal * dur)
      case BaseVariable("x", _, _) =>
        updated(xSSA, xVal + vVal * dur + aVal * dur * dur * env.factory.number(Rational(0.5)))
      case DifferentialSymbol(BaseVariable("t", _, _)) => updated(xSSA, env.factory.number(Rational(1)))
      case DifferentialSymbol(BaseVariable("v", _, _)) => updated(xSSA, aVal)
      case DifferentialSymbol(BaseVariable("x", _, _)) => updated(xSSA, vVal + aVal * dur)
      case _ => throw new DemonException("Demon does not know how to assign variable: " + x)
    }
  }

  override def writeAssign(id: NodeID, xSSA: Ident, f: number): Unit = {
    val x = plainVar(xSSA)
    env.set(x, f)
    println(s"Controller updated $x -> $f (full name: $xSSA)")
  }

}
