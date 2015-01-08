import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import StringConverter._

/**
 * Tests uniform substitution.
 *
 * Created by smitsch on 1/7/15.
 * @author Stefan Mitsch
 */
class UniformSubstitutionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  private var s: Substitution = null

  override def beforeEach() = { s = new Substitution(List()) }

  private def V(s: String) = Variable(s, None, Real)

  "Free variables of x>0" should "be {x}" in {
    s.freeVariables("x>0".asFormula) should be (Set(V("x")))
  }
  // TODO similar for <, =, etc.

  "Free variables of x>0 & x>2" should "be {x}" in {
    s.freeVariables("x>0 & x>2".asFormula) should be (Set(V("x")))
  }
  // TODO similar for |, -> etc.

  // TODO why is x not bound?
  "Free variables of Exists x. x=0" should "be {x}" in {
    s.freeVariables("\\exists x. x=0".asFormula) should be (Set(V("x")))
  }
  "Free variables of Forall x. x=0" should "be {x}" in {
    s.freeVariables("\\forall x. x=0".asFormula) should be (Set(V("x")))
  }

  "Free variables of [x:=*;]x>0" should "be {x}" in {
    s.freeVariables("[x:=*;]x>0".asFormula) should be (Set(V("x")))
  }

  "Free variables of [x:=* ++ z:=x;]x>0" should "be {x}" in {
    s.freeVariables("[x:=* ++ z:=x;]x>0".asFormula) should be (Set(V("x")))
  }

  "Free variables of [x:=* ++ ?z>0;]x>0" should "be {x,z}" in {
    s.freeVariables("[x:=* ++ ?z>0;]x>0".asFormula) should be (Set(V("x"), V("z")))
  }

  "Free variables of [{x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};]x>0" should "be {x}" in {
    s.freeVariables("[{x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};]x>0".asFormula) should be (Set(V("x")))
  }

}
