package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics._
import edu.cmu.cs.ls.keymaerax.core.{StaticSemantics, Variable}
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

  it should "rewrite entire subformula" in {
    val result = proveBy("x=0 ==> x*y=x&(x+1=1|x-1=-1), x+1>0".asSequent, eqL2R(-1)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> x*y=x&(0+1=1|0-1=-1), x+1>0".asSequent
  }

  it should "not rewrite bound occurrences" in {
    val result = proveBy("x=0 ==> x*y=x&(x+1=1|[x:=-1;]x=-1), x+1>0".asSequent, eqL2R(-1)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> x*y=x&(0+1=1|[x:=-1;]x=-1), x+1>0".asSequent
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
      TactixLibrary.useAt(Ax.equalCommute)(-1) & eqL2R(-1)(1) & TactixLibrary.useAt(Ax.equalCommute)(-1))
    result.subgoals.loneElement shouldBe "0=x ==> 0*y=0".asSequent
  }

  it should "rewrite only some of the symbols when asked to" in withQE { _ =>
    val result = proveBy("y=x ==> y=2&y+y+2>y+1".asSequent, eqL2R(-1)(1, 0::0::Nil))
    result.subgoals.loneElement shouldBe "y=x ==> x=2&y+y+2>y+1".asSequent
  }

  it should "rewrite only free occurrences" in withQE { _ =>
    val result = proveBy("y=x ==> y=2 & \\exists y y<3".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "y=x ==> x=2 & \\exists y y<3".asSequent
  }

  it should "not fail bound occurrences" in withQE { _ =>
    val result = proveBy("y=x ==> \\exists x x>=y".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "y=x ==> \\exists x x>=y".asSequent
  }

  it should "not fail bound occurrences 2" in withQE { _ =>
    val result = proveBy("y=x ==> x>=y & \\exists x x>=y".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "y=x ==> x>=x & \\exists x x>=y".asSequent
  }

  it should "not fail bound occurrences 3" in withQE { _ =>
    val result = proveBy("y=x ==> x>=y & [x:=2;]x>=y".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "y=x ==> x>=x & [x:=2;]x>=y".asSequent
  }

  it should "not fail bound occurrences 4" in withQE { _ =>
    val result = proveBy("y=x ==> [x:=2;]x>=y".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "y=x ==> [x:=2;]x>=y".asSequent
  }

  "eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in withQE { _ =>
    val result = proveBy("0=x ==> x*y=0".asSequent, eqR2L(-1)(1))
    result.subgoals.loneElement shouldBe "0=x ==> 0*y=0".asSequent
  }

  "Exhaustive eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in {
    val result = proveBy("0=x ==> x*y=0".asSequent, exhaustiveEqR2L(-1))
    result.subgoals.loneElement shouldBe "0=x ==> 0*y=0".asSequent
  }

  it should "hide when there are no more free occurrences after rewriting" in {
    StaticSemantics.freeVars("[x:=0+1;]x>=1".asFormula)
    proveBy("0=x ==> [x:=x+1;]x>=1".asSequent, TactixLibrary.exhaustiveEqR2L(hide=true)(-1)).
      subgoals.loneElement shouldBe " ==> [x:=0+1;]x>=1".asSequent
  }

  it should "not hide when there are still free occurrences after rewriting" in {
    proveBy("0=x ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent, TactixLibrary.exhaustiveEqR2L(hide=true)(-1)).
      subgoals.loneElement shouldBe "0=x ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent
    proveBy("0=x ==> [x:=x+1; ++ y:=2;]x>=0".asSequent, TactixLibrary.exhaustiveEqR2L(hide=true)(-1)).
      subgoals.loneElement shouldBe "0=x ==> [x:=0+1; ++ y:=2;]x>=0".asSequent
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

  it should "rewrite only free occurrences" in withQE { _ =>
    val result = proveBy("y=x ==> y=2 & \\exists y y<3, \\forall y y>4, y=5".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "y=x ==> x=2 & \\exists y y<3, \\forall y y>4, x=5".asSequent
  }

  it should "hide when there are no more free occurrences after rewriting" in {
    proveBy("x=0 ==> [x:=x+1;]x>=1".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe " ==> [x:=0+1;]x>=1".asSequent
    proveBy("x=0 ==> [x:=x+1;]x>=1".asSequent, EqualityTactics.atomExhaustiveEqL2R(-1)).
      subgoals.loneElement shouldBe " ==> [x:=0+1;]x>=1".asSequent
  }

  it should "not hide when there are still free occurrences after rewriting" in {
    proveBy("x=0 ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "x=0 ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent
    proveBy("x=0 ==> [x:=x+1; ++ y:=2;]x>=0".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "x=0 ==> [x:=0+1; ++ y:=2;]x>=0".asSequent
    proveBy("x=0 ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent, EqualityTactics.atomExhaustiveEqL2R(-1)).
      subgoals.loneElement shouldBe "x=0 ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent
    proveBy("x=0 ==> [x:=x+1; ++ y:=2;]x>=0".asSequent, EqualityTactics.atomExhaustiveEqL2R(-1)).
      subgoals.loneElement shouldBe "x=0 ==> [x:=0+1; ++ y:=2;]x>=0".asSequent
  }

  it should "bound rename when right-handside names clash" in {
    proveBy("y=x ==> \\forall x x<y".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "==> \\forall x_0 x_0<x".asSequent
    proveBy("y=x ==> [x:=x+y;]x>y".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "==> [x_0:=x+x;]x_0>x".asSequent
    proveBy("y=x ==> [x:=*;]x>y".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "==> [x_0:=*;]x_0>x".asSequent
    proveBy("y=x ==> \\forall x (x<y -> \\exists x x>y)".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "==> \\forall x_0 (x_0<x -> \\exists x_1 x_1>x)".asSequent
  }

  "Apply Equalities" should "rewrite all plain equalities" in {
    proveBy("x=2, x+y>=4, y=3 ==> y-x<=1, x=2".asSequent, applyEqualities).subgoals.loneElement shouldBe "2+3>=4 ==> 3-2<=1, 2=2".asSequent
    proveBy("x=x+2, x+y>=4, y=3 ==> y-x<=1, x=2".asSequent, applyEqualities).subgoals.loneElement shouldBe "x=x+2, x+2+3>=4 ==> 3-(x+2)<=1, x+2=2".asSequent
  }

  it should "not endless rewrite equalities when LHS and RHS are the same" in {
    proveBy("x=x, x+y>=4, y=3 ==> y-x<=1, x=2".asSequent, applyEqualities).subgoals.loneElement shouldBe "x=x, x+3>=4 ==> 3-x<=1, x=2".asSequent
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
      abbrv("min(a,b)".asTerm, None))
    result.subgoals.loneElement shouldBe "min_0<c, x>y, 5<min_0, min_0 = min(a,b) ==> min_0+2=7, a<b, [b:=2;]min(a,b)<9".asSequent
  }

  it should "abbreviate any argument even if not contained in the sequent and pick a name automatically" in withQE { _ =>
    val result = proveBy("x>y ==> a<b".asSequent, abbrv("c+d".asTerm, None))
    result.subgoals.loneElement shouldBe "x>y, x_0 = c+d ==> a<b".asSequent
  }

  it should "abbreviate inside programs when free" in withQE { _ =>
    val result = proveBy("x+1>0 ==> [x:=x+1;]x>0".asSequent, abbrv("x+1".asTerm, Some("y".asVariable)))
    result.subgoals.loneElement shouldBe "y>0, y=x+1 ==> [x:=y;]x>0".asSequent
  }

  it should "not try to abbreviate inside programs when not free" in withQE { _ =>
    val result = proveBy("x+1>0 ==> [{x:=x+1;}*]x>0".asSequent, abbrv("x+1".asTerm, Some("y".asVariable)))
    result.subgoals.loneElement shouldBe "y>0, y=x+1 ==> [{x:=x+1;}*]x>0".asSequent
  }

  it should "not try to abbreviate inside programs when not free 2" in withQE { _ =>
    val result = proveBy("x+1>0 ==> [x:=x+1;x:=x+1;]x>0".asSequent, abbrv("x+1".asTerm, Some("y".asVariable)))
    result.subgoals.loneElement shouldBe "y>0, y=x+1 ==> [x:=y;x:=x+1;]x>0".asSequent
  }

  "AbbrvAt tactic" should "abbreviate in places where at least one of the arguments is bound" in withQE { _ =>
    val result = proveBy("==> [a:=0;]min(a,2) <= 2".asSequent, abbrvAt("min(a,2)".asTerm, Some("z".asVariable))(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [a:=0;]\\forall z (z=min(a,2) -> z<=2)".asSequent
  }

  it should "abbreviate according to polarity" in withQE { _ =>
    val result = proveBy("==> [a:=0;]!min(a,2) <= 2".asSequent, abbrvAt("min(a,2)".asTerm, Some("z".asVariable))(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> [a:=0;]!\\exists z (z=min(a,2) & z<=2)".asSequent
  }

  it should "work in any position" in withQE { _ =>
    val result = proveBy("==> x=4, [a:=0;]!min(a,2) <= 2, y=3".asSequent, abbrvAt("min(a,2)".asTerm, Some("z".asVariable))(2, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> x=4, [a:=0;]!\\exists z (z=min(a,2) & z<=2), y=3".asSequent
  }

  it should "work in any position in antecedent" in withQE { _ =>
    val result = proveBy("x=4, [a:=0;]!min(a,2) <= 2, y=3 ==> ".asSequent, abbrvAt("min(a,2)".asTerm, Some("z".asVariable))(-2, 1::0::Nil))
    result.subgoals.loneElement shouldBe "x=4, [a:=0;]!\\forall z (z=min(a,2) -> z<=2), y=3 ==> ".asSequent
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

  it should "expand abs(x) in context that binds x" in withQE { _ =>
    val result = proveBy("[x:=-7;]abs(x) >= 5".asFormula, abs(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=-7;](x>=0&x>=5|x < 0&-x>=5)".asSequent
  }

  it should "not abbreviate when expanding abs(x) in context that binds x" in withQE { _ =>
    // the quantifier resulting from abbreviating is not supported by dI
    val result = proveBy("[x:=-7;](abs(x) >= 5 & abs(x) <= 9)".asFormula, abs(1, 1::0::0::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=-7;]((x>=0&x>=5|x < 0&-x>=5) & abs(x) <= 9)".asSequent
  }

  it should "expand abs(x) at any position in context that binds x" in withQE { _ =>
    val result = proveBy("x=4, [x:=-7;]abs(x) >= 5, y=3 ==> ".asSequent, abs(-2, 1::0::Nil))
    result.subgoals.loneElement shouldBe "x=4, [x:=-7;](x>=0&x>=5|x < 0&-x>=5), y=3 ==> ".asSequent
  }

  it should "expand abs(x) at any position and polarity in context that binds x" in withQE { _ =>
    val result = proveBy("x=4, [x:=-7;]!abs(x) >= 5, y=3 ==> ".asSequent, abs(-2, 1::0::0::Nil))
    result.subgoals.loneElement shouldBe "x=4, [x:=-7;]!(x>=0&x>=5|x < 0&-x>=5), y=3 ==> ".asSequent
  }

  it should "expand abs(x) in equivalences in context" ignore withQE { _ =>
    //@todo not yet supported
    proveBy("==> \\forall x (abs(x)>=0 <-> (x>=0 | x<=0))".asSequent, abs(1, 0::0::0::Nil)).subgoals.loneElement shouldBe
      "==> \\forall x ( (x>=0 & x>=0 <-> (x>=0 | x<=0) ) | ( x<0 & -x>=0 <-> (x>=0 | x<=0) ) )".asSequent
  }

  "min" should "expand min(x,y) in succedent" in withQE { _ =>
    val result = proveBy("min(x,y) >= 5".asFormula, minmax(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x<=y&min_0=x | x>y&min_0=y ==> min_0>=5".asSequent
  }

  it should "expand min(x,y) in antecedent" in withQE { _ =>
    val result = proveBy("min(x,y) >= 5 ==> ".asSequent, minmax(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "min_0>=5, x<=y&min_0=x | x>y&min_0=y ==> ".asSequent
  }

  it should "expand min(x,y) in binding context" in withQE { _ =>
    val result = proveBy("[x:=2;]min(x,y) >= 2".asFormula, minmax(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=2;](x<=y&x>=2|x>y&y>=2)".asSequent
  }

  it should "expand min(x,y) in any polarity in binding context" in withQE { _ =>
    val result = proveBy("[x:=2;]!min(x,y) >= 2".asFormula, minmax(1, 1::0::0::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=2;]!(x<=y&x>=2|x>y&y>=2)".asSequent
  }

  it should "expand min(x,y) only at position" in withQE { _ =>
    val result = proveBy("[x:=2;]((min(x,y) >= 2 | y=7) & min(x,y) <= 10)".asFormula, minmax(1, 1::0::0::0::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=2;](((x<=y&x>=2|x>y&y>=2) | y=7) & min(x,y) <= 10)".asSequent
  }

  it should "be possible to combine with abbrvAt to expand min(x,y) broadly" in withQE { _ =>
    val result = proveBy("[x:=2;]((min(x,y) >= 2 | y=7) & min(x,y) <= 10)".asFormula,
      abbrvAt("min(x,y)".asTerm, None)(1, 1::Nil) & minmax(1, 1::0::0::1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=2;]\\forall min_0 (x<=y&min_0=x|x>y&min_0=y->(min_0>=2|y=7)&min_0<=10)".asSequent
  }

  it should "be possible to combine with abbrv to expand min(x,y) broadly" in withQE { _ =>
    val result = proveBy("(min(x,y) >= 2 | y=7) & min(x,y) <= 10".asFormula,
      abbrv("min(x,y)".asTerm, None) & minmax(-1, 1::Nil))
    result.subgoals.loneElement shouldBe "min_0=min_1, x<=y&min_1=x|x>y&min_1=y ==> (min_0>=2|y=7)&min_0<=10".asSequent
  }

  "max" should "expand max(x,y) in succedent" in withQE { _ =>
    val result = proveBy("max(x,y) >= 5".asFormula, minmax(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x>=y&max_0=x | x<y&max_0=y ==> max_0>=5".asSequent
  }

  it should "expand max(x,y) in antecedent" in withQE { _ =>
    val result = proveBy("max(x,y) >= 5 ==> ".asSequent, minmax(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "max_0>=5, x>=y&max_0=x | x<y&max_0=y ==> ".asSequent
  }

  it should "expand max(x,y) binding context in succedent" in withQE { _ =>
    val result = proveBy("==> [x:=2;]max(x,y) >= 2".asSequent, minmax(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=2;](x>=y&x>=2 | x<y&y>=2)".asSequent
  }

  it should "expand max(x,y) binding context in antecedent" in withQE { _ =>
    val result = proveBy("[x:=2;]max(x,y) >= 2 ==> ".asSequent, minmax(-1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "[x:=2;](x>=y&x>=2 | x<y&y>=2) ==> ".asSequent
  }

  it should "expand with a term search locator" in withQE { _ =>
    val result = proveBy("y=max(x,4) ==> y>=4".asSequent, BelleParser("minmax('L=={`max(x,4)`})"))
    result.subgoals.loneElement shouldBe "y=max_0, x>=4&max_0=x|x < 4&max_0=4 ==> y>=4".asSequent
  }

  "expandAll" should "expand abs everywhere" in withQE { _ =>
    val result = proveBy("abs(x-y)>0 ==> abs(a-5)>0, abs(x-y)>37".asSequent, expandAll)
    result.subgoals.loneElement shouldBe "abs_0>0, x-y>=0&abs_0=x-y|x-y < 0&abs_0=-(x-y), a-5>=0&abs_1=a-5|a-5 < 0&abs_1=-(a-5) ==> abs_1>0, abs_0>37".asSequent
  }

  it should "expand all special functions everywhere" in withQE { _ =>
    val result = proveBy("min(x,y)>0 ==> abs(a-5)>0, max(x,y)>37".asSequent, expandAll)
    result.subgoals.loneElement shouldBe "min_0>0, x<=y&min_0=x|x>y&min_0=y, a-5>=0&abs_0=a-5|a-5 < 0&abs_0=-(a-5), x>=y&max_0=x|x < y&max_0=y ==> abs_0>0, max_0>37".asSequent
  }

  it should "expand in context" in withQE { _ =>
    val result = proveBy("min(x,y)>0, abs(a-5)>7 ==> abs(a-5)>0, [a:=3;]abs(a-5)>=2, max(x,y)>0, [x:=4;]min(x,y)>=4".asSequent, expandAll)
    result.subgoals.loneElement shouldBe
      """min_0>0,
        |abs_0>7,
        |x<=y&min_0=x|x>y&min_0=y,
        |a-5>=0&abs_0=a-5|a-5 < 0&abs_0=-(a-5),
        |x>=y&max_0=x|x < y&max_0=y
        |==>
        |abs_0>0,
        |[a:=3;](a-5>=0&a-5>=2|a-5 < 0&-(a-5)>=2),
        |max_0>0,
        |[x:=4;](x<=y&x>=4|x>y&y>=4)
      """.stripMargin.asSequent
  }

  it should "expand anywhere in a term" in withQE { _ =>
    val result = proveBy("(x+4)/min(1,3) >= x".asFormula, expandAll)
    result.subgoals.loneElement shouldBe "1<=3 & min_0=1 | 1>3 & min_0=3 ==> (x+4)/min_0 >= x".asSequent
  }

  it should "not infinite recurse" in withQE { _ =>
    val f = "[{x'=100*x^4+y*x^3-x^2+x+c,c'=x+y+z,dbxy_'=(-(0--x)*(-- (100*x^4+y*x^3-x^2+x+c))/max(((0--x)*(0--x),-- (100*x^4+y*x^3-x^2+x+c))))*dbxy_+0&c>x&max(((0--x)*(0--x),-- (100*x^4+y*x^3-x^2+x+c)))>0}]dbxy_>0".asFormula
    proveBy(f, EqualityTactics.expandAll).subgoals.loneElement shouldBe "==> [{x'=100*x^4+y*x^3-x^2+x+c,c'=x+y+z,dbxy_'=(-(0--x)*(-- (100*x^4+y*x^3-x^2+x+c))/max(((0--x)*(0--x),-- (100*x^4+y*x^3-x^2+x+c))))*dbxy_+0&c>x&max(((0--x)*(0--x),-- (100*x^4+y*x^3-x^2+x+c)))>0}]dbxy_>0".asSequent
  }
}
