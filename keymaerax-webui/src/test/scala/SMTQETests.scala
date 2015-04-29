import edu.cmu.cs.ls.keymaera.tactics.{Interpreter, Tactics}
import edu.cmu.cs.ls.keymaera.tools._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._

/**
 * Created by ran on 3/27/15.
 * @author Ran Ji
 */
class SMTQETests extends FlatSpec with Matchers with BeforeAndAfterEach {
  type KExpr = edu.cmu.cs.ls.keymaera.core.Expression
  type SExpr = SMTLib
  var z3: Z3Solver = null
  var polya: PolyaSolver = null

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.Z3Scheduler = new Interpreter(new Z3)
    Tactics.PolyaScheduler = Some(new Interpreter(new Polya))
    z3 = new Z3Solver
    polya = new PolyaSolver
  }

  override def afterEach() = {
    Tactics.PolyaScheduler.get.shutdown()
    Tactics.Z3Scheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.Z3Scheduler = null
    Tactics.KeYmaeraScheduler = null
    z3 = null
    polya = null
  }

  "QE" should "prove reals" in {
    z3.qe("3^0 < 1".asFormula) should be ("false".asFormula)
    polya.qe("3^0 < 1".asFormula) should be ("false".asFormula)
  }

  it should "prove complex qutifiers" in {
    z3.qe("\\forall x. \\forall y. \\exists z. x^2+y^2=z^2".asFormula) should be ("false".asFormula)
    polya.qe("\\forall x. \\forall y. \\exists z. x^2+y^2=z^2".asFormula) should be ("false".asFormula)
  }

  it should "prove complex" in {
    z3.qe("(x+y-z)^3 = 1 -> true".asFormula) should be("true".asFormula)
    polya.qe("(x+y-z)^3 = 1 -> true".asFormula) should be("true".asFormula)
  }

  it should "prove complex 22" in {
    z3.qe("x > 0 -> !x^2-2*x+1=0".asFormula) should be("false".asFormula)
    polya.qe("x > 0 -> !x^2-2*x+1=0".asFormula) should be("false".asFormula)
  }

  it should "prove complex 2" in {
    z3.qe("(c<1&c>=0&H>=0&g()>0&v^2<=2*g()*(H-h)&h>=0&k4_t_1=0&h_2()=h&v_2()=v&h_3=0&k4_t_4()=0&v_3=-1*k4_t_5*g()+v&0>=0&0=1/2*(-1*k4_t_5^2*g()+2*h+2*k4_t_5*v)&k4_t_5>=0&v_5=-c*(-1*k4_t_5*g()+v)->(-c*(-1*k4_t_5*g()+v))^2<=2*g()*(H-0))".asFormula) should be("true".asFormula)
    polya.qe("(c<1&c>=0&H>=0&g()>0&v^2<=2*g()*(H-h)&h>=0&k4_t_1=0&h_2()=h&v_2()=v&h_3=0&k4_t_4()=0&v_3=-1*k4_t_5*g()+v&0>=0&0=1/2*(-1*k4_t_5^2*g()+2*h+2*k4_t_5*v)&k4_t_5>=0&v_5=-c*(-1*k4_t_5*g()+v)->(-c*(-1*k4_t_5*g()+v))^2<=2*g()*(H-0))".asFormula) should be("true".asFormula)
  }

  it should "prove complex 3" in {
    z3.qe("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & k4_t_1=0 & h_2()=h & v_2()=v & h>=0 & k4_t_4()=0 & 0>=0 -> v=(0*2-1*0)/2^2*(-1*0^2*g()+2*h+2*0*v)+1/2*((-0*0^2+-1*(2*0^1*(0*0+1)))*g()+-1*0^2*0+(0*h+2*0)+((0*0+2*(0*0+1))*v+2*0*0))".asFormula) should be ("true".asFormula)
    polya.qe("c<1 & c>=0 & H>=0 & g()>0 & v^2<=2*g()*(H-h) & h>=0 & k4_t_1=0 & h_2()=h & v_2()=v & h>=0 & k4_t_4()=0 & 0>=0 -> v=(0*2-1*0)/2^2*(-1*0^2*g()+2*h+2*0*v)+1/2*((-0*0^2+-1*(2*0^1*(0*0+1)))*g()+-1*0^2*0+(0*h+2*0)+((0*0+2*(0*0+1))*v+2*0*0))".asFormula) should be ("true".asFormula)
  }

  "Simplify" should "simplify term" in {
    z3.simplify("1+x-x".asTerm) should be ("1".asTerm)
  }
}