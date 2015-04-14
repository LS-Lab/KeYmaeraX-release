import edu.cmu.cs.ls.keymaera.tactics.{PosInExpr, SuccPosition}
import org.scalatest.{Matchers, FlatSpec}
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import testHelper.StringConverter._
import testHelper.SequentFactory.sequent

/**
 * Created by smitsch on 1/24/15.
 * @author Stefan Mitsch
 */
class TacticHelperTests extends FlatSpec with Matchers {

  "getFormula on |- x>0 at position (0, HereP)" should "return x>0" in {
    val s = sequent(Nil, Nil, "x>0".asFormula :: Nil)
    getFormula(s, new SuccPosition(0)) should be (
      "x>0".asFormula
    )
  }

  "getFormula on |- x>0 at position (0, [])" should "return x>0" in {
    val s = sequent(Nil, Nil, "x>0".asFormula :: Nil)
    getFormula(s, new SuccPosition(0, new PosInExpr(Nil))) should be (
      "x>0".asFormula
    )
  }

  "getFormula on |- [x:=2;]x>0 at position (0, [1])" should "return x>0" in {
    val s = sequent(Nil, Nil, "[x:=2;]x>0".asFormula :: Nil)
    getFormula(s, new SuccPosition(0, new PosInExpr(1 :: Nil))) should be (
      "x>0".asFormula
    )
  }

  "getFormula on |- [x:=2;]x>0 <-> x>4 at position (0, [0,1])" should "return x>0" in {
    val s = sequent(Nil, Nil, "[x:=2;]x>0 <-> x>4".asFormula :: Nil)
    getFormula(s, new SuccPosition(0, new PosInExpr(0 :: 1 :: Nil))) should be (
      "x>0".asFormula
    )
  }

  "getFormula on |- [x:=2;]x>0 <-> x>4 at position (0, [1])" should "return x>4" in {
    val s = sequent(Nil, Nil, "[x:=2;]x>0 <-> x>4".asFormula :: Nil)
    getFormula(s, new SuccPosition(0, new PosInExpr(1 :: Nil))) should be (
      "x>4".asFormula
    )
  }

  "getFormula on |- [x:=2;]x>0 <-> x>4 at position (0, [0,0])" should "return x>4" in {
    val s = sequent(Nil, Nil, "[x:=2;]x>0 <-> x>4".asFormula :: Nil)
    an [IllegalArgumentException] should be thrownBy getFormula(s, new SuccPosition(0, new PosInExpr(0 :: 0 :: Nil)))
  }

  "freshNamedSymbol in formula" should "return fresh index" in {
    freshNamedSymbol("x".asNamedSymbol, "x_2>0 | x_4<0 | z_6=5".asFormula) should be ("x_5".asNamedSymbol)
  }

  it should "return index 0 when index is None so far" in {
    freshNamedSymbol("x".asNamedSymbol, "x>5 | x=3 | x<2 | z_3=5".asFormula) should be ("x_0".asNamedSymbol)
  }

  "freshNamedSymbol in sequent" should "return fresh index when max is in succedent" in {
    val s = sequent(Nil, "x=2".asFormula :: "x_2>3".asFormula :: Nil, "x_4>5".asFormula :: Nil)
    freshNamedSymbol("x".asNamedSymbol, s) should be ("x_5".asNamedSymbol)
  }

  it should "return fresh index when max is in antecedent" in {
    val s = sequent(Nil, "x=2".asFormula :: "x_4>3".asFormula :: Nil, "x_2>5".asFormula :: Nil)
    freshNamedSymbol("x".asNamedSymbol, s) should be ("x_5".asNamedSymbol)
  }

  it should "return index 0 when index is None so far" in {
    val s = sequent(Nil, "x=2".asFormula :: "x>3".asFormula :: Nil, "x>5".asFormula :: Nil)
    freshNamedSymbol("x".asNamedSymbol, s) should be ("x_0".asNamedSymbol)
  }

  it should "return index None when variable not present" in {
    val s = sequent(Nil, "z=2".asFormula :: "y>3".asFormula :: Nil, "z>5".asFormula :: Nil)
    freshNamedSymbol("x".asNamedSymbol, s) should be ("x".asNamedSymbol)
  }
}
