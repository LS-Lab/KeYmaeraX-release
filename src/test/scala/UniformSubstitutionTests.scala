import edu.cmu.cs.ls.keymaera.core._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter
import scala.collection.immutable.Seq
import StringConverter._

/**
 * Created by ran on 09/01/15.
 * @author Ran Ji
 */

class UniformSubstitutionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  private var s: Substitution = null

  override def beforeEach() = {
    s = new Substitution(List())
  }

  "Uniform substitution of (x,1) |-> x=y" should "be 1=y" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x=y".asFormula) should be ("1=y".asFormula)
  }

  "Uniform substitution of (x,1) |-> x:=y;" should "be x:=y;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x:=y;".asProgram) should be ("x:=y;".asProgram)
  }

  "Uniform substitution of (x,1) |-> x:=1 ++ x:=x+1 ++ z:=x;" should "be x:=1 ++ x:=1+1 ++ z:=1;" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("x:=1 ++ x:=x+1 ++ z:=x".asProgram) should be ("x:=1 ++ x:=1+1 ++ z:=1;".asProgram)
  }

  "Uniform substitution of (x,1) |-> {x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};" should "be {x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};" in {
    s = Substitution(Seq(new SubstitutionPair("x".asTerm, "1".asTerm)))
    s.apply("{x:=1 ++ x:=x+1 ++ z:=x};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram) should be ("{x:=1 ++ x:=1+1 ++ z:=1};{x:=1 ++ x:=x+1 ++ z:=x};".asProgram)
  }

}
