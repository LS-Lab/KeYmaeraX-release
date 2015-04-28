import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.LogicalODESolver
import org.scalatest.{PrivateMethodTester, FlatSpec, Matchers}

/**
 * Created by nfulton on 4/23/15.
 */
class ODESolverTests extends FlatSpec with Matchers with PrivateMethodTester {
  //Useful values used throughout these tests.
  val x      = Variable("x", None, Real)
  val xPrime = DifferentialSymbol(x)
  val t      = Variable("t", None, Real)
  val tPrime = DifferentialSymbol(t)
  val five   = Number(5)
  val two    = Number(2)
  val one    = Number(1)
  val zero   = Number(0)

  "solutionForVariable" should "compute the correct solution for x' = 2" in {
    val program = DifferentialProduct(AtomicODE(xPrime, two), AtomicODE(tPrime, one))
    LogicalODESolver.solutionForVariable(x, program, Equal(x, zero) :: Nil) shouldBe Equal(x, Plus(Times(Number(2), t), Number(0)))
  }

  it should "compute the correct solution for x' = 2 & x = 5" in {
    val program = DifferentialProduct(ODESystem(AtomicODE(xPrime, two), Equal(x, five)), AtomicODE(tPrime, one))
    LogicalODESolver.solutionForVariable(x, program, Nil) shouldBe Equal(x, Plus(Times(Number(2), t), Number(5)))
  }
}
