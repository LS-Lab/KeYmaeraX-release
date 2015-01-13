import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter
import scala.collection.immutable.Seq
import StringConverter._

/**
 * Created by rjcn on 09/01/15.
 * @author Ran Ji
 */

class UniformSubstitutionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  private var s: Substitution = null

  override def beforeEach() = {
    s = new Substitution(List())
  }

  // tests for basic statements

  "Uniform substitution of (x,1) |-> x=y" should "be 1=y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x=y".asFormula) should be ("1=y".asFormula)
  }

  "Uniform substitution of (x,y) |-> x=y" should "be y=y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    s.apply("x=y".asFormula) should be ("y=y".asFormula)
  }

  "Uniform substitution of (y,x+y) |-> z=x+y" should "be z=x+x+y" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("z=x+y".asFormula) should be ("z=x+(x+y)".asFormula)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> x=y" should "be y=x+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("x=y".asFormula) should be ("y=x+y".asFormula)
  }

  "Uniform substitution of (x,y) |-> (y,x+y) |-> x=y" should "be y=y+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    val s1  = new Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply(s1.apply("x=y".asFormula)) should be ("y=y+y".asFormula)
  }

  "Uniform substitution of (x,1) |-> x:=y" should "be x:=y;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x:=y;".asProgram) should be ("x:=y;".asProgram)
  }

  "Uniform substitution of (y,x+y) |-> x:=y" should "be x:=x+y;" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("x:=y;".asProgram) should be ("x:=x+y;".asProgram)
  }

  /**
   * parentheses problem a+(b+c) = a+b+c ?
   */
  "Uniform substitution of (y,x+y) |-> z:=x+y;" should "be z:=x+x+y;" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("z:=x+y;".asProgram) should be ("z:=x+(x+y);".asProgram)
  }

  /**
   * clash exception
   */
  "Uniform substitution of (y,x+y) |-> x:=y;z:=x+y;" should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    an [SubstitutionClashException] should be thrownBy(s.apply("x:=y;z:=x+y;".asProgram))
  }

  "Uniform substitution of (x,y)(y,x+y) |-> x:=y" should "be x:=x+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("x:=y;".asProgram) should be ("x:=x+y;".asProgram)
  }

  "Uniform substitution of (x,y) |-> (y,x+y) |-> x:=y" should "be x:=y+y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm)))
    val s1  = new Substitution(Seq(new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply(s1.apply("x:=y;".asProgram)) should be ("x:=y+y;".asProgram)
  }

  "Uniform substitution of (x,1) |-> x:=x+1;z:=x;" should "be x:=1+1;z:=x;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x:=x+1;z:=x;".asProgram) should be ("x:=1+1; z:=x;".asProgram)
  }

  "Uniform substitution of (x,1) |-> x:=1 ++ x:=x+1 ++ z:=x;" should "be x:=1 ++ x:=1+1 ++ z:=1;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x:=1 ++ x:=x+1 ++ z:=x".asProgram) should be ("x:=1 ++ x:=1+1 ++ z:=1;".asProgram)
  }

  "Uniform substitution of (x,1) |-> {x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};" should "be {x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("{x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram) should be ("{x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram)
  }

  "Uniform substitution of (x,1) |-> {x:=1 ++ x:=x+1 ++ z:=x}*;" should "be {x:=1 ++ x:=x+1 ++ z:=x}*" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("{x:=1 ++ x:=x+1 ++ z:=x}*".asProgram) should be ("{x:=1 ++ x:=x+1 ++ z:=x}*".asProgram)
  }

  // tests for rules

  "Uniform substitution of (x,y)(y,x+y) |-> x>y & x<=y+1 " should "be y>x+y & y<=x+y+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    s.apply("x>y & x<=y+1".asFormula) should be ("y>x+y & y<=x+y+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,y+1) |-> \\forall x. x>y" should "be forall x. x>y+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "y+1".asTerm)))
    s.apply("\\forall x. x>y".asFormula) should be ("\\forall x. x>y+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,y+1) |-> \\forall x. x>y | x<=y+1 " should "be forall x. x>y+1 | y<=y+1+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "y+1".asTerm)))
    s.apply("\\forall x. x>y | x<=y+1".asFormula) should be ("\\forall x. x>y+1 | y<=y+1+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> \\forall x. x>y | x<=y+1 " should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    an [SubstitutionClashException] should be thrownBy(s.apply("\\forall x. x>y | x<=y+1".asFormula))
  }

  "Uniform substitution of (x,y)(y,y+1) |-> \\exists x. x>y" should "be exists x. x>y+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "y+1".asTerm)))
    s.apply("\\exists x. x>y".asFormula) should be ("\\exists x. x>y+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,y+1) |-> \\exists x. x>y -> x<=y+1 " should "be exists x. x>y+1 -> y<=y+1+1" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "y+1".asTerm)))
    s.apply("\\exists x. x>y -> x<=y+1".asFormula) should be ("\\exists x. x>y+1 -> y<=y+1+1".asFormula)
  }

  "Uniform substitution of (x,y)(y,x+y) |-> \\exists x. x>y -> x<=y+1 " should "not be permitted" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "y".asTerm),new SubstitutionPair("y".asTerm, "x+y".asTerm)))
    an [SubstitutionClashException] should be thrownBy(s.apply("\\exists x. x>y -> x<=y+1".asFormula))
  }

}
