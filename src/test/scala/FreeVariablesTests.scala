import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter
import StringConverter._

/**
 * Tests uniform substitution.
 *
 * Created by smitsch on 1/7/15.
 * @author Stefan Mitsch
 * @author Ran Ji
 */
class FreeVariablesTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  private var s: Substitution = null

  override def beforeEach() = { s = new Substitution(List()) }

  private def V(s: String) = Variable(s, None, Real)

  // test cases for terms

  "Free variables of -x" should "be {x}" in {
    s.freeVariables("-x".asTerm) should be (Set(V("x")))
  }

  "Free variables of x^y" should "be {x,y}" in {
    s.freeVariables("x^y".asTerm) should be (Set(V("x"),V("y")))
  }

  "Free variables of x'" should "be {x}" in {
    s.freeVariables("x'".asTerm) should be (Set(V("x")))
  }

  "Free variables of x+1" should "be {x}" in {
    s.freeVariables("x+1".asTerm) should be (Set(V("x")))
  }

  "Free variables of x+y" should "be {x, y}" in {
    s.freeVariables("x+y".asTerm) should be (Set(V("x"),V("y")))
  }

  "Free variables of x-1" should "be {x}" in {
    s.freeVariables("x-1".asTerm) should be (Set(V("x")))
  }

  "Free variables of x-y" should "be {x,y}" in {
    s.freeVariables("x-y".asTerm) should be (Set(V("x"),V("y")))
  }

  "Free variables of x*1" should "be {x}" in {
    s.freeVariables("x*1".asTerm) should be (Set(V("x")))
  }

  "Free variables of x*y" should "be {x,y}" in {
    s.freeVariables("x*y".asTerm) should be (Set(V("x"),V("y")))
  }

  "Free variables of x/1" should "be {x}" in {
    s.freeVariables("x/1".asTerm) should be (Set(V("x")))
  }

  "Free variables of x/y" should "be {x,y}" in {
    s.freeVariables("x/y".asTerm) should be (Set(V("x"),V("y")))
  }

  "Free variables of x*x+2*x*y+y*y" should "be {x,y}" in {
    s.freeVariables("x*x+2*x*y+y*y".asTerm) should be (Set(V("x"),V("y")))
  }

  "Free variables of x*y+y/(z-x)" should "be {x,y,z}" in {
    s.freeVariables("x*y+y/(z-x)".asTerm) should be (Set(V("x"),V("y"),V("z")))
  }

  "Free variables of x'*y+x*z'" should "be {x,y}" in {
    s.freeVariables("x'*y+x*z'".asTerm) should be (Set(V("x"),V("y"),V("z")))
  }

  // test cases for formulas

  "Free variables of true" should "be {}" in {
    s.freeVariables("true".asFormula) should be (Set())
  }

  "Free variables of false" should "be {}" in {
    s.freeVariables("false".asFormula) should be (Set())
  }

  "Free variables of x=1" should "be {x,y}" in {
    s.freeVariables("x=1".asFormula) should be (Set(V("x")))
  }

  "Free variables of x=y" should "be {x,y}" in {
    s.freeVariables("x=y".asFormula) should be (Set(V("x"),V("y")))
  }

  "Free variables of x!=1" should "be {x,y}" in {
    s.freeVariables("x!=1".asFormula) should be (Set(V("x")))
  }

  "Free variables of x!=y" should "be {x,y}" in {
    s.freeVariables("x!=y".asFormula) should be (Set(V("x"),V("y")))
  }

  "Free variables of x>1" should "be {x}" in {
    s.freeVariables("x>1".asFormula) should be (Set(V("x")))
  }

  "Free variables of x>y" should "be {x}" in {
    s.freeVariables("x>y".asFormula) should be (Set(V("x"),V("y")))
  }

  "Free variables of x>=1" should "be {x}" in {
    s.freeVariables("x>=1".asFormula) should be (Set(V("x")))
  }

  "Free variables of x>=y" should "be {x}" in {
    s.freeVariables("x>=y".asFormula) should be (Set(V("x"),V("y")))
  }

  "Free variables of x<1" should "be {x}" in {
    s.freeVariables("x<1".asFormula) should be (Set(V("x")))
  }

  "Free variables of x<y" should "be {x}" in {
    s.freeVariables("x<y".asFormula) should be (Set(V("x"),V("y")))
  }

  "Free variables of x<=1" should "be {x}" in {
    s.freeVariables("x<=1".asFormula) should be (Set(V("x")))
  }

  "Free variables of x<=y" should "be {x}" in {
    s.freeVariables("x<=y".asFormula) should be (Set(V("x"),V("y")))
  }

  "Free variables of !(x>x+1)" should "be {x}" in {
    s.freeVariables("!(x>x+1)".asFormula) should be (Set(V("x")))
  }

  "Free variables of x>0 & y<z" should "be {x,y,z}" in {
    s.freeVariables("x>0 & y<z".asFormula) should be (Set(V("x"),V("y"),V("z")))
  }

  "Free variables of x>0 | y<z" should "be {x,y,z}" in {
    s.freeVariables("x>0 | y<z".asFormula) should be (Set(V("x"),V("y"),V("z")))
  }

  "Free variables of x>y -> y>=z" should "be {x,y,z}" in {
    s.freeVariables("x>y -> y>=z".asFormula) should be (Set(V("x"),V("y"),V("z")))
  }

  "Free variables of x>y <-> y<z" should "be {x,y,z}" in {
    s.freeVariables("x>y <-> y<z".asFormula) should be (Set(V("x"),V("y"),V("z")))
  }

  "Free variables of Exists x. x=t" should "be {t}" in {
    s.freeVariables("\\exists x. x=t".asFormula) should be (Set(V("t")))
  }

  "Free variables of Exists x. (x=t & y=x)" should "be {t,y}" in {
    s.freeVariables("\\exists x. (x=t & y=x)".asFormula) should be (Set(V("t"),V("y")))
  }

  "Free variables of Exists x. x=t & y=x" should "be {t,x,y}" in {
    s.freeVariables("\\exists x. x=t & y=x".asFormula) should be (Set(V("t"),V("x"),V("y")))
  }

  "Free variables of Exists x. x=t | y=x" should "be {t,x,y}" in {
    s.freeVariables("\\exists x. x=t | y=x".asFormula) should be (Set(V("t"),V("x"),V("y")))
  }

  "Free variables of Exists x. x=t & y=x | x=z" should "be {t,x,y,z}" in {
    s.freeVariables("\\exists x. x=t & y=x | x=z ".asFormula) should be (Set(V("t"),V("x"),V("y"),V("z")))
  }

  "Free variables of Forall x. x=t" should "be {t}" in {
    s.freeVariables("\\forall x. x=t".asFormula) should be (Set(V("t")))
  }

  "Free variables of Forall x. (x=t & y=x)" should "be {t,y}" in {
    s.freeVariables("\\forall x. (x=t & y=x)".asFormula) should be (Set(V("t"),V("y")))
  }

  "Free variables of Forall x. x=t & y=x" should "be {t,x,y}" in {
    s.freeVariables("\\forall x. x=t & y=x".asFormula) should be (Set(V("t"),V("x"),V("y")))
  }

  "Free variables of Forall x. x=t | y=x" should "be {t,x,y}" in {
    s.freeVariables("\\forall x. x=t | y=x".asFormula) should be (Set(V("t"),V("x"),V("y")))
  }

  "Free variables of Forall x. x=t & y=x | x=z" should "be {t,x,y,z}" in {
    s.freeVariables("\\forall x. x=t & y=x | x=z ".asFormula) should be (Set(V("t"),V("x"),V("y"),V("z")))
  }

  "Free variables of Forall x. Exists y. x=y" should "be {}" in {
    s.freeVariables("\\forall x. \\exists y. x=y".asFormula) should be (Set())
  }

  // test cases for programs

  "Free variables of x:=*;" should "be {}" in {
    s.freeVariables("x:=*;".asProgram) should be (Set())
  }

  "Free variables of [x:=*;]x>0" should "be {}" in {
    s.freeVariables("[x:=*;]x>0".asFormula) should be (Set())
  }

  "Free variables of y:=x;" should "be {x}" in {
    s.freeVariables("y:=x;".asProgram) should be (Set(V("x")))
  }

  "Free variables of [y:=x;]y>0" should "be {x}" in {
    s.freeVariables("[y:=x;]y>0".asFormula) should be (Set(V("x")))
  }

  "Free variables of x:=*;y:=x;" should "be {}" in {
    s.freeVariables("x:=*;y:=x;".asProgram) should be (Set())
  }

  "Free variables of [x:=*;y:=x]y>0" should "be {}" in {
    s.freeVariables("[x:=*;y:=x]y>0".asFormula) should be (Set())
  }

  "Free variables of x:=* ++ y:=x;" should "be {x}" in {
    s.freeVariables("x:=* ++ y:=x;".asProgram) should be (Set(V("x")))
  }

  "Free variables of [x:=* ++ y:=x;]y>0" should "be {x,y}" in {
    s.freeVariables("[x:=* ++ y:=x;]y>0".asFormula) should be (Set(V("x"),V("y")))
  }

  "Free variables of [x:=* ++ ?z>0;]x>0" should "be {x,z}" in {
    s.freeVariables("[x:=* ++ ?z>0;]x>0".asFormula) should be (Set(V("x"), V("z")))
  }

  "Free variables of x:=1; x:=x+1; z:=x;" should "be {}" in {
    s.freeVariables("x:=1; x:=x+1; z:=x;".asProgram) should be (Set())
  }

  "Free variables of x:=1 ++ x:=x+1 ++ z:=x;" should "be {x}" in {
    s.freeVariables("x:=1 ++ x:=x+1 ++ z:=x;".asProgram) should be (Set(V("x")))
  }

  "Free variables of {x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};" should "be {x}" in {
    s.freeVariables("{x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram) should be (Set(V("x")))
  }

  "Free variables of {x:=1 ++ x:=x+1 ++ z:=x}*;" should "be {x}" in {
    s.freeVariables("{x:=1 ++ x:=x+1 ++ z:=x}*;".asProgram) should be (Set(V("x")))
  }


//  "Free variables of x':=a;" should "be {}" in {
//    s.freeVariables("x':=a;".asProgram) should be (Set())
//  }

// not implemented yet

//  "Free variables of [x':=*;]true" should "be {}" in {
//    s.freeVariables("[x':=*;]true".asFormula) should be (Set())
//  }
//
//  "Free variables of [x':=*;]x>0" should "be {}" in {
//    s.freeVariables("[x':=*;]x>0".asFormula) should be (Set())
//  }
//
//  "Free variables of [Forall t. x=0; x:=t+1]x>0" should "be {t}" in {
//    s.freeVariables("[\\forall t. x=0; x:=t+1]x>0".asFormula) should be (Set(V("t")))
//  }

}
