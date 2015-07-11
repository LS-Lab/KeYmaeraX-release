import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{Matchers, FlatSpec}
import testHelper.StringConverter
import StringConverter._

import scala.collection.immutable.Set

/**
 * Tests free variables
 *
 * Created by smitsch on 1/7/15.
 * @author Stefan Mitsch
 * @author Ran Ji
 */
class FreeVariablesTests extends FlatSpec with Matchers {
  private def V(s: String) = Variable(s, None, Real)

  // test cases for terms

  "Free variables of -x" should "be {x}" in {
    StaticSemantics("-x".asTerm) should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x^y" should "be {x,y}" in {
    StaticSemantics("x^y".asTerm) should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x'" should "be {x}" in {
    // assumes that x' is parsed as differential symbol
    "x'".asTerm shouldBe DifferentialSymbol(V("x"))
    StaticSemantics("x'".asTerm) should be (SetLattice(Set(DifferentialSymbol(V("x")))))
    StaticSemantics(Differential(V("x"))) should be (SetLattice(Set(V("x"), DifferentialSymbol(V("x")))))
  }

  "Free variables of x+1" should "be {x}" in {
    StaticSemantics("x+1".asTerm) should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x+y" should "be {x, y}" in {
    StaticSemantics("x+y".asTerm) should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x-1" should "be {x}" in {
    StaticSemantics("x-1".asTerm) should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x-y" should "be {x,y}" in {
    StaticSemantics("x-y".asTerm) should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x*1" should "be {x}" in {
    StaticSemantics("x*1".asTerm) should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x*y" should "be {x,y}" in {
    StaticSemantics("x*y".asTerm) should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x/1" should "be {x}" in {
    StaticSemantics("x/1".asTerm) should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x/y" should "be {x,y}" in {
    StaticSemantics("x/y".asTerm) should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x*x+2*x*y+y*y" should "be {x,y}" in {
    StaticSemantics("x*x+2*x*y+y*y".asTerm) should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x*y+y/(z-x)" should "be {x,y,z}" in {
    StaticSemantics("x*y+y/(z-x)".asTerm) should be (SetLattice(Set(V("x"),V("y"),V("z"))))
  }

  "Free variables of x'*y+x*z'" should "be {x,y}" in {
    // assumes that x' and z' are parsed as differential symbols
    "x'".asTerm shouldBe DifferentialSymbol(V("x"))
    "z'".asTerm shouldBe DifferentialSymbol(V("z"))
    StaticSemantics("x'*y+x*z'".asTerm) should be (SetLattice(Set(V("x"),V("y"),DifferentialSymbol(Variable("x", None, Real)),
      DifferentialSymbol(Variable("z", None, Real)))))
    StaticSemantics(Plus(Times(Differential(V("x")), V("y")), Times(V("x"), Differential(V("z"))))) shouldBe
      SetLattice(Set(V("x"),V("y"),V("z"),DifferentialSymbol(Variable("x", None, Real)),
        DifferentialSymbol(Variable("z", None, Real))))
  }

  // test cases for formulas

  "Free variables of true" should "be {}" in {
    StaticSemantics("true".asFormula).fv should be (SetLattice.bottom)
  }

  "Free variables of false" should "be {}" in {
    StaticSemantics("false".asFormula).fv should be (SetLattice.bottom)
  }

  "Free variables of x=1" should "be {x,y}" in {
    StaticSemantics("x=1".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x=y" should "be {x,y}" in {
    StaticSemantics("x=y".asFormula).fv should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x!=1" should "be {x,y}" in {
    StaticSemantics("x!=1".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x!=y" should "be {x,y}" in {
    StaticSemantics("x!=y".asFormula).fv should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x>1" should "be {x}" in {
    StaticSemantics("x>1".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x>y" should "be {x}" in {
    StaticSemantics("x>y".asFormula).fv should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x>=1" should "be {x}" in {
    StaticSemantics("x>=1".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x>=y" should "be {x}" in {
    StaticSemantics("x>=y".asFormula).fv should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x<1" should "be {x}" in {
    StaticSemantics("x<1".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x<y" should "be {x}" in {
    StaticSemantics("x<y".asFormula).fv should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of x<=1" should "be {x}" in {
    StaticSemantics("x<=1".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x<=y" should "be {x}" in {
    StaticSemantics("x<=y".asFormula).fv should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of !(x>x+1)" should "be {x}" in {
    StaticSemantics("!(x>x+1)".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x>0 & y<z" should "be {x,y,z}" in {
    StaticSemantics("x>0 & y<z".asFormula).fv should be (SetLattice(Set(V("x"),V("y"),V("z"))))
  }

  "Free variables of x>0 | y<z" should "be {x,y,z}" in {
    StaticSemantics("x>0 | y<z".asFormula).fv should be (SetLattice(Set(V("x"),V("y"),V("z"))))
  }

  "Free variables of x>y -> y>=z" should "be {x,y,z}" in {
    StaticSemantics("x>y -> y>=z".asFormula).fv should be (SetLattice(Set(V("x"),V("y"),V("z"))))
  }

  "Free variables of x>y <-> y<z" should "be {x,y,z}" in {
    StaticSemantics("x>y <-> y<z".asFormula).fv should be (SetLattice(Set(V("x"),V("y"),V("z"))))
  }

  "Free variables of Exists x. x=t" should "be {t}" in {
    StaticSemantics("\\exists x x=t".asFormula).fv should be (SetLattice(Set(V("t"))))
  }

  "Free variables of Exists x. (x=t & y=x)" should "be {t,y}" in {
    StaticSemantics("\\exists x (x=t & y=x)".asFormula).fv should be (SetLattice(Set(V("t"),V("y"))))
  }

  "Free variables of Exists x. x=t & y=x" should "be {t,x,y}" in {
    StaticSemantics("\\exists x x=t & y=x".asFormula).fv should be (SetLattice(Set(V("t"),V("x"),V("y"))))
  }

  "Free variables of Exists x. x=t | y=x" should "be {t,x,y}" in {
    StaticSemantics("\\exists x x=t | y=x".asFormula).fv should be (SetLattice(Set(V("t"),V("x"),V("y"))))
  }

  "Free variables of Exists x. x=t & y=x | x=z" should "be {t,x,y,z}" in {
    StaticSemantics("\\exists x x=t & y=x | x=z ".asFormula).fv should be (SetLattice(Set(V("t"),V("x"),V("y"),V("z"))))
  }

  "Free variables of Forall x. x=t" should "be {t}" in {
    StaticSemantics("\\forall x x=t".asFormula).fv should be (SetLattice(Set(V("t"))))
  }

  "Free variables of Forall x. (x=t & y=x)" should "be {t,y}" in {
    StaticSemantics("\\forall x (x=t & y=x)".asFormula).fv should be (SetLattice(Set(V("t"),V("y"))))
  }

  "Free variables of Forall x. x=t & y=x" should "be {t,x,y}" in {
    StaticSemantics("\\forall x x=t & y=x".asFormula).fv should be (SetLattice(Set(V("t"),V("x"),V("y"))))
  }

  "Free variables of Forall x. x=t | y=x" should "be {t,x,y}" in {
    StaticSemantics("\\forall x x=t | y=x".asFormula).fv should be (SetLattice(Set(V("t"),V("x"),V("y"))))
  }

  "Free variables of Forall x. x=t & y=x | x=z" should "be {t,x,y,z}" in {
    StaticSemantics("\\forall x x=t & y=x | x=z ".asFormula).fv should be (SetLattice(Set(V("t"),V("x"),V("y"),V("z"))))
  }

  "Free variables of Forall x. Exists y. x=y" should "be {}" in {
    StaticSemantics("\\forall x \\exists y x=y".asFormula).fv should be (SetLattice.bottom)
  }

  // test cases for programs

  "Free variables of x:=*;" should "be {}" in {
    StaticSemantics("x:=*;".asProgram).fv should be (SetLattice.bottom)
  }

  "Free variables of [x:=*;]x>0" should "be {}" in {
    StaticSemantics("[x:=*;]x>0".asFormula).fv should be (SetLattice.bottom)
  }

  "Free variables of y:=x;" should "be {x}" in {
    StaticSemantics("y:=x;".asProgram).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of [y:=x;]y>0" should "be {x}" in {
    StaticSemantics("[y:=x;]y>0".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of x:=*;y:=x;" should "be {}" in {
    StaticSemantics("x:=*;y:=x;".asProgram).fv should be (SetLattice.bottom)
  }

  "Free variables of [x:=*;y:=x]y>0" should "be {}" in {
    StaticSemantics("[x:=*;y:=x;]y>0".asFormula).fv should be (SetLattice.bottom)
  }

  "Free variables of x:=* ++ y:=x;" should "be {x}" in {
    StaticSemantics("x:=*; ++ y:=x;".asProgram).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of [x:=* ++ y:=x;]y>0" should "be {x,y}" in {
    StaticSemantics("[x:=*; ++ y:=x;]y>0".asFormula).fv should be (SetLattice(Set(V("x"),V("y"))))
  }

  "Free variables of [x:=* ++ ?z>0;]x>0" should "be {x,z}" in {
    StaticSemantics("[x:=*; ++ ?z>0;]x>0".asFormula).fv should be (SetLattice(Set(V("x"), V("z"))))
  }

  "Free variables of x:=1; x:=x+1; z:=x;" should "be {}" in {
    StaticSemantics("x:=1; x:=x+1; z:=x;".asProgram).fv should be (SetLattice.bottom)
  }

  "Free variables of x:=1 ++ x:=x+1 ++ z:=x;" should "be {x}" in {
    StaticSemantics("x:=1; ++ x:=x+1; ++ z:=x;".asProgram).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of {x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};" should "be {x}" in {
    StaticSemantics("{x:=1; ++ x:=x+1; ++ z:=x;}{x:=1; ++ x:=x+1; ++ z:=x;}".asProgram).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of {x:=1 ++ x:=x+1 ++ z:=x}*;" should "be {x}" in {
    StaticSemantics("{x:=1; ++ x:=x+1; ++ z:=x;}*".asProgram).fv should be (SetLattice(Set(V("x"))))
  }


  "Free variables of [x'=1;]true" should "be {x}" in {
    StaticSemantics("[{x'=1}]true".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of [{x:=x+1;}*;]true" should "be {x}" in {
    StaticSemantics("[{x:=x+1;}*]true".asFormula).fv should be (SetLattice(Set(V("x"))))
  }

  "Free variables of [x:=1;][{x:=x+1;}*;]true" should "be {}" in {
    StaticSemantics("[x:=1;][{x:=x+1;}*]true".asFormula).fv should be (SetLattice.bottom)
  }

  "Free variables of [x:=1;][x'=1;]true" should "be {}" in {
    StaticSemantics("[x:=1;][{x'=1}]true".asFormula).fv should be (SetLattice.bottom)
  }
}
