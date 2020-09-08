package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.{Integrator, RandomFormula, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.RandomParserTests
import edu.cmu.cs.ls.keymaerax.tags._
import fastparse.Parsed.{Failure, Success}
import fastparse._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._



/** Test synthesized Angel strategies against handwritten do-nothing Demon strategies */
// @TODO: variable naming conventions for current vs historical state. Make SSA always use x_i so x can be current state
class ProofPlexShimTests extends TacticTestBase {
  val check: String => Statement = Kaisar.statementProved

  "ProofPlex Interpreter" should "execute 1D car against trivial demon" in withMathematica { _ =>
    val pf = check(SharedModels.essentialsSafeCar1D)
    val angel = SimpleStrategy(AngelStrategy(pf))
    val env = new Environment()
    val demon = new EssentialsSafeCar1DShim(env)
    demon.init()
    // @TODO: Braking case test v >= B/T eventually fails after reaching destination
    a[TestFailureException] shouldBe thrownBy(Play(env, angel, demon))
    println("Final state: " + env.state)
    val goal = env.state(Variable("d"))
    (env.state(Variable("x")) >=  (goal * 0.8)) shouldBe true
    (env.state(Variable("x")) <=  goal) shouldBe true
  }
}

class EssentialsSafeCar1DShim (val env: Environment) extends DemonStrategy[Play.number] {
  val initValues: Map[Ident, Play.number] =
    Map(Variable("A") -> 2, Variable("B") -> 2, Variable("x") -> 0, Variable("v") -> 0, Variable("a") -> 0,
      DifferentialSymbol(Variable("x")) -> 0, DifferentialSymbol(Variable("v")) -> 0,
      Variable("d") -> 200, Variable("T") -> 1, Variable("t") -> 0, DifferentialSymbol(Variable("t")) -> 1)

  var iterationsLeft: Int = 100

  override def readLoop: Boolean = {
    iterationsLeft = iterationsLeft - 1;
    iterationsLeft >= 0
  }

  // Only choice is between accel (false) and brake (true) branches
  override def readChoice: Boolean = {
    val accelFml = "((v + T*A)^2/(2*B) <= (d - (x + v*T + (A*T^2)/2)))".asFormula
    val brakeFml = "((v + T*A)^2/(2*B)  + 1 >= (d - (x + v*T + (A*T^2)/2)))".asFormula
    val (a, b) = (env.holds(accelFml), env.holds(brakeFml))
    assert(a || b)
    !a // false = accelerate, favor acceleration in case a && b
  }

  private def updated(x: Ident, v: Play.number): Play.number = { env.set(x, v); v}

  private def plainVar(v: Variable): Variable = {
    v match {
      case BaseVariable(name, index, sort) => Variable(name)
      case DifferentialSymbol(BaseVariable(name, index, sort)) => DifferentialSymbol(Variable(name))
    }
  }

  // in case values are accessed before initialization
  private def valFor(x: Ident): Play.number = {
    if (env.contains(x)) env.get(x)
    else  {
      val v = initValues(x)
      env.set(x, v)
      v
    }
  }

  override def readAssign(xSSA: Ident): Play.number = {
    val x = plainVar(xSSA)
    // initialization
    if(!env.contains(x)) return valFor(x)
    // differential equation has been reduced to * assignments
    // Note: avoid failing the v >= 0 constraint
    val T = valFor(Variable("T"))
    val (xVal, vVal, aVal) = (valFor(Variable("x")), valFor(Variable("v")), valFor(Variable("a")))
    val dur: Play.number = if (aVal >= 0) T else T.min(vVal) / -aVal
    x match {
      case BaseVariable("t", _, _) => updated(xSSA, dur)
      case BaseVariable("v", _, _) => updated(xSSA, vVal + aVal * dur)
      case BaseVariable("x", _, _) => updated(xSSA, xVal + vVal * dur + aVal * dur * dur * 0.5)
      case DifferentialSymbol(BaseVariable("t", _, _)) => updated(xSSA, 1)
      case DifferentialSymbol(BaseVariable("v", _, _)) => updated(xSSA, aVal)
      case DifferentialSymbol(BaseVariable("x", _, _)) => updated(xSSA, vVal + aVal * dur)
      case _ =>
        throw new DemonException("Demon does not know how to assign variable: " + x)
    }
  }

  override def writeAssign(xSSA: Ident, f: Play.number): Unit = {
    val x = plainVar(xSSA)
    env.set(x, f)
    println(s"Controller updated $x -> $f (full name: $xSSA)")
  }

}

