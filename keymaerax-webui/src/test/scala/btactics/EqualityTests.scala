package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics._
import edu.cmu.cs.ls.keymaerax.core.Variable
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import org.scalatest.LoneElement._

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics]]
 */
class EqualityTests extends TacticTestBase {

  "eqL2R" should "rewrite x*y=0 to 0*y=0 using x=0" in {
    val result = proveBy("x=0 ==> x*y=0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0".asSequent
  }

  it should "rewrite entire formula" in {
    val result = proveBy("x=0 ==> x*y=x&x+1=1, x+1>0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0&0+1=1, x+1>0".asSequent
  }

  it should "rewrite entire formula at specified position" in {
    val result = proveBy("x=0 ==> x*y=x&x+1=1, x+1>0".asSequent, eqL2R(-1)(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0&x+1=1, x+1>0".asSequent
  }

  it should "rewrite entire term at specified position" in {
    val result = proveBy("x=0 ==> x*x*y=x, x+1>0".asSequent, eqL2R(-1)(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*0*y=x, x+1>0".asSequent
  }

  it should "rewrite only at very specified position" in {
    val result = proveBy("x=0 ==> x*y=x, x+1>0".asSequent, eqL2R(-1)(1, 0::0::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=x, x+1>0".asSequent
  }

  it should "keep positions stable" in {
    val result = proveBy("x=0 ==> x*y=0, x+1>0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0, x+1>0".asSequent
  }

  it should "rewrite complicated" in {
    val result = proveBy("x=0 ==> x*y=0 & x+3>2 | \\forall y y+x>=0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0 & 0+3>2 | \\forall y y+0>=0".asSequent
  }

  it should "rewrite complicated exhaustively" in {
    val result = proveBy("x=0 ==> x*y=0 & x+3>2 | \\forall y y+x>=0 & \\exists x x>0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0 & 0+3>2 | \\forall y y+0>=0 & \\exists x x>0".asSequent
  }

  it should "rewrite x*y=0 to 0*y=0 using 0=x" in withQE { _ =>
    val result = proveBy("0=x ==> x*y=0".asSequent,
      TactixLibrary.useAt("= commute")(-1) & eqL2R(-1)(1) & TactixLibrary.useAt("= commute")(-1))
    result.subgoals.loneElement shouldBe "0=x ==> 0*y=0".asSequent
  }

  it should "rewrite only some of the symbols when asked to" in withQE { _ =>
    val result = proveBy("y=x ==> y=2&y+y+2>y+1".asSequent, eqL2R(-1)(1, 0::0::Nil))
    result.subgoals.loneElement shouldBe "y=x ==> x=2&y+y+2>y+1".asSequent
  }

  "eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in withQE { _ =>
    val result = proveBy("0=x ==> x*y=0".asSequent, eqR2L(-1)(1))
    result.subgoals.loneElement shouldBe "0=x ==> 0*y=0".asSequent
  }

  "Exhaustive eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in {
    val result = proveBy("0=x ==> x*y=0".asSequent, exhaustiveEqR2L(-1))
    result.subgoals.loneElement shouldBe "0=x ==> 0*y=0".asSequent
  }

  "Exhaustive eqL2R" should "rewrite a single formula exhaustively" in {
    val result = proveBy("x=0 ==> x*y=0, z>2, z<x+1".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0, z>2, z<0+1".asSequent
  }

  it should "not fail when there are no applicable positions" in {
    val result = proveBy("x=0 ==> z>2".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "x=0 ==> z>2".asSequent
  }

  it should "rewrite a single formula exhaustively for a single applicable position" in {
    val result = proveBy("x=0 ==> x*y=0, z>2".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0, z>2".asSequent
  }

  it should "rewrite formulas exhaustively" in {
    val result = proveBy("x=0, z=x ==> x*y=0, z>2, z<x+1".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "x=0, z=0 ==> 0*y=0, z>2, z<0+1".asSequent
  }

  it should "rewrite formulas exhaustively everywhere" in {
    val result = proveBy("z=x, x=0 ==> x*y=0, z>2, z<x+1".asSequent, exhaustiveEqL2R(-2))
    result.subgoals.loneElement shouldBe "z=0, x=0 ==> 0*y=0, z>2, z<0+1".asSequent
  }

  it should "work even if there is only one other formula" in {
    val result = proveBy("x<5, x=0 ==> ".asSequent, exhaustiveEqL2R(-2))
    result.subgoals.loneElement shouldBe "0<5, x=0 ==> ".asSequent
  }

  it should "replace arbitary terms" in {
    val result = proveBy("a+b<5, a+b=c ==> ".asSequent, exhaustiveEqL2R(-2))
    result.subgoals.loneElement shouldBe "c<5, a+b=c ==> ".asSequent
  }

  // rewriting numbers is disallowed, because otherwise we run into endless rewriting
  it should "not rewrite numbers" in {
    a [BelleThrowable] should be thrownBy proveBy("0<5, 0=0 ==> ".asSequent, exhaustiveEqL2R(-2))
  }

  it should "not try to rewrite bound occurrences" in {
    val result = proveBy("a=1 ==> [a:=2;]a=1".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "a=1 ==> [a:=2;]a=1".asSequent
  }

  it should "rewrite multiple occurrences of a term in one shot" in {
    val result = proveBy("x+2<=x+3, x=y ==> ".asSequent, exhaustiveEqL2R(-2))
    result.subgoals.loneElement shouldBe "y+2<=y+3, x=y ==> ".asSequent
  }

  "Abbrv tactic" should "abbreviate a+b to z" in withQE { _ =>
    val result = proveBy("a+b < c".asFormula, abbrv(Variable("z"))(1, 0::Nil))
    result.subgoals.loneElement shouldBe "z = a+b ==> z < c".asSequent
  }

  it should "abbreviate min(a,b) to z" in withQE { _ =>
    val result = proveBy("min(a,b) < c".asFormula, abbrv(Variable("z"))(1, 0::Nil))
    result.subgoals.loneElement shouldBe "z = min(a,b) ==> z < c".asSequent
  }

  it should "not abbreviate in places where at least one of the arguments is bound" in withQE { _ =>
    val result = proveBy("min(a,b) < c ==> [a:=0;]min(a,b) < c".asSequent, abbrv(Variable("z"))(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "z < c, z = min(a,b) ==> [a:=0;]min(a,b) < c".asSequent
  }

  it should "abbreviate min(a,b) to z everywhere (except at bound occurrences)" in withQE { _ =>
    val result = proveBy("min(a,b) < c, x>y, 5 < min(a,b) ==> min(a,b) + 2 = 7, a<b, [b:=2;]min(a,b) < 9".asSequent,
      abbrv(Variable("z"))(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "z<c, x>y, 5<z, z = min(a,b) ==> z+2=7, a<b, [b:=2;]min(a,b)<9".asSequent
  }

  it should "abbreviate min(a,b) to z everywhere (except at bound occurrences) and pick a name automatically" in withQE { _ =>
    val result = proveBy("min(a,b) < c, x>y, 5 < min(a,b) ==> min(a,b) + 2 = 7, a<b, [b:=2;]min(a,b) < 9".asSequent,
      abbrv("min(a,b)".asTerm))
    result.subgoals.loneElement shouldBe "min_0<c, x>y, 5<min_0, min_0 = min(a,b) ==> min_0+2=7, a<b, [b:=2;]min(a,b)<9".asSequent
  }

  it should "abbreviate any argument even if not contained in the sequent and pick a name automatically" in withQE { _ =>
    val result = proveBy("x>y ==> a<b".asSequent, abbrv("c+d".asTerm))
    result.subgoals.loneElement shouldBe "x>y, x_0 = c+d ==> a<b".asSequent
  }

  "abs" should "expand abs(x) in succedent" in withQE { _ =>
    val result = proveBy("abs(x) >= 5".asFormula, abs(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x>=0&abs_0=x | x<0&abs_0=-x ==> abs_0>=5".asSequent
  }

  it should "expand abs(x) in non-top-level succedent" in withQE { _ =>
    val result = proveBy("y=2 | abs(x) >= 5".asFormula, abs(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "x>=0&abs_0=x | x<0&abs_0=-x ==> y=2 | abs_0>=5".asSequent
  }

  it should "expand abs(x) in antecedent" in withQE { _ =>
    val result = proveBy("abs(x) >= 5 ==> ".asSequent, abs(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "abs_0>=5, x>=0&abs_0=x | x<0&abs_0=-x ==> ".asSequent
  }

  "min" should "expand min(x,y) in succedent" in withQE { _ =>
    val result = proveBy("min(x,y) >= 5".asFormula, minmax(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x<=y&min_0=x | x>y&min_0=y ==> min_0>=5".asSequent
  }

  it should "expand min(x,y) in antecedent" in withQE { qeTool =>
    val result = proveBy("min(x,y) >= 5 ==> ".asSequent, minmax(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "min_0>=5, x<=y&min_0=x | x>y&min_0=y ==> ".asSequent
  }

  "max" should "expand max(x,y) in succedent" in withQE { _ =>
    val result = proveBy("max(x,y) >= 5".asFormula, minmax(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x>=y&max_0=x | x<y&max_0=y ==> max_0>=5".asSequent
  }

  it should "expand max(x,y) in antecedent" in withQE { _ =>
    val result = proveBy("max(x,y) >= 5 ==> ".asSequent, minmax(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "max_0>=5, x>=y&max_0=x | x<y&max_0=y ==> ".asSequent
  }

  "expandAll" should "expand abs everywhere" in withQE { _ =>
    val result = proveBy("abs(x-y)>0 ==> abs(a-5)>0, abs(x-y)>37".asSequent, expandAll)
    result.subgoals.loneElement shouldBe "abs_0>0, x-y>=0&abs_0=x-y|x-y < 0&abs_0=-(x-y), a-5>=0&abs_1=a-5|a-5 < 0&abs_1=-(a-5) ==> abs_1>0, abs_0>37".asSequent
  }

  it should "expand all special functions everywhere" in withQE { _ =>
    val result = proveBy("min(x,y)>0 ==> abs(a-5)>0, max(x,y)>37".asSequent, expandAll)
    result.subgoals.loneElement shouldBe "min_0>0, x<=y&min_0=x|x>y&min_0=y, a-5>=0&abs_0=a-5|a-5 < 0&abs_0=-(a-5), x>=y&max_0=x|x < y&max_0=y ==> abs_0>0, max_0>37".asSequent
  }
}
