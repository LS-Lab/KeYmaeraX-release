package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics._
import edu.cmu.cs.ls.keymaerax.core.{ProverException, StaticSemantics, Variable}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.LoneElement._

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.EqualityTactics]]
 */
class EqualityTests extends TacticTestBase {

  "eqL2R" should "rewrite x*y=0 to 0*y=0 using x=0" in withTactics {
    val result = proveBy("x=0 ==> x*y=0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0".asSequent
  }

  it should "rewrite entire formula" in withTactics {
    val result = proveBy("x=0 ==> x*y=x&x+1=1, x+1>0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0&0+1=1, x+1>0".asSequent
  }

  it should "rewrite entire subformula" in withTactics {
    val result = proveBy("x=0 ==> x*y=x&(x+1=1|x-1=-1), x+1>0".asSequent, eqL2R(-1)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> x*y=x&(0+1=1|0-1=-1), x+1>0".asSequent
  }

  it should "not rewrite bound occurrences" in withTactics {
    val result = proveBy("x=0 ==> x*y=x&(x+1=1|[x:=-1;]x=-1), x+1>0".asSequent, eqL2R(-1)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> x*y=x&(0+1=1|[x:=-1;]x=-1), x+1>0".asSequent
  }

  it should "rewrite entire formula at specified position" in withTactics {
    val result = proveBy("x=0 ==> x*y=x&x+1=1, x+1>0".asSequent, eqL2R(-1)(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0&x+1=1, x+1>0".asSequent
  }

  it should "rewrite entire term at specified position" in withTactics {
    val result = proveBy("x=0 ==> x*x*y=x, x+1>0".asSequent, eqL2R(-1)(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*0*y=x, x+1>0".asSequent
  }

  it should "rewrite only at very specified position" in withTactics {
    val result = proveBy("x=0 ==> x*y=x, x+1>0".asSequent, eqL2R(-1)(1, 0::0::Nil))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=x, x+1>0".asSequent
  }

  it should "keep positions stable" in withTactics {
    val result = proveBy("x=0 ==> x*y=0, x+1>0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0, x+1>0".asSequent
  }

  it should "rewrite complicated" in withTactics {
    val result = proveBy("x=0 ==> x*y=0 & x+3>2 | \\forall y y+x>=0".asSequent, eqL2R(-1)(1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0 & 0+3>2 | \\forall y y+0>=0".asSequent
  }

  it should "rewrite complicated exhaustively" in withTactics {
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

  it should "not fail bound occurrences 5" in withQE { _ =>
    proveBy("y=x ==> [{x'=2}]x>=y".asSequent, eqL2R(-1)(1)).subgoals.loneElement shouldBe "y=x ==> [{x'=2}]x>=y".asSequent
    proveBy("x=y ==> [{x'=2}]x>=y".asSequent, eqL2R(-1)(1)).subgoals.loneElement shouldBe "x=y ==> [{x'=2}]x>=y".asSequent
  }

  it should "not try to rewrite differential symbols and differentials" in withQE { _ =>
    proveBy("y=x ==> y'=y".asSequent, eqL2R(-1)(1)).subgoals.loneElement shouldBe "y=x ==> y'=x".asSequent
    proveBy("y=x ==> (f(y))'=y".asSequent, eqL2R(-1)(1)).subgoals.loneElement shouldBe "y=x ==> (f(y))'=x".asSequent
  }

  "eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in withQE { _ =>
    val result = proveBy("0=x ==> x*y=0".asSequent, eqR2L(-1)(1))
    result.subgoals.loneElement shouldBe "0=x ==> 0*y=0".asSequent
  }

  "Exhaustive eqR2L" should "rewrite x*y=0 to 0*y=0 using 0=x" in withTactics {
    val result = proveBy("0=x ==> x*y=0".asSequent, exhaustiveEqR2L(-1))
    result.subgoals.loneElement shouldBe "0=x ==> 0*y=0".asSequent
  }

  it should "hide when there are no more free occurrences after rewriting" in withTactics {
    StaticSemantics.freeVars("[x:=0+1;]x>=1".asFormula)
    proveBy("0=x ==> [x:=x+1;]x>=1".asSequent, TactixLibrary.exhaustiveEqR2L(hide=true)(-1)).
      subgoals.loneElement shouldBe " ==> [x:=0+1;]x>=1".asSequent
  }

  it should "not hide when there are still free occurrences after rewriting" in withTactics {
    proveBy("0=x ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent, TactixLibrary.exhaustiveEqR2L(hide=true)(-1)).
      subgoals.loneElement shouldBe "0=x ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent
    proveBy("0=x ==> [x:=x+1; ++ y:=2;]x>=0".asSequent, TactixLibrary.exhaustiveEqR2L(hide=true)(-1)).
      subgoals.loneElement shouldBe "0=x ==> [x:=0+1; ++ y:=2;]x>=0".asSequent
  }

  it should "rewrite differentials" in withTactics {
    proveBy("x_0=(f(x))' ==> (f(x))'>0".asSequent, TactixLibrary.exhaustiveEqR2L(hide=true)(-1)).subgoals.
      loneElement shouldBe "==> x_0>0".asSequent
  }

  "Exhaustive eqL2R" should "rewrite a single formula exhaustively" in withTactics {
    val result = proveBy("x=0 ==> x*y=0, z>2, z<x+1".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0, z>2, z<0+1".asSequent
  }

  it should "not fail when there are no applicable positions" in withTactics {
    val result = proveBy("x=0 ==> z>2".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "x=0 ==> z>2".asSequent
  }

  it should "rewrite a single formula exhaustively for a single applicable position" in withTactics {
    val result = proveBy("x=0 ==> x*y=0, z>2".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "x=0 ==> 0*y=0, z>2".asSequent
  }

  it should "rewrite formulas exhaustively" in withTactics {
    val result = proveBy("x=0, z=x ==> x*y=0, z>2, z<x+1".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "x=0, z=0 ==> 0*y=0, z>2, z<0+1".asSequent
  }

  it should "rewrite formulas exhaustively everywhere" in withTactics {
    val result = proveBy("z=x, x=0 ==> x*y=0, z>2, z<x+1".asSequent, exhaustiveEqL2R(-2))
    result.subgoals.loneElement shouldBe "z=0, x=0 ==> 0*y=0, z>2, z<0+1".asSequent
  }

  it should "work even if there is only one other formula" in withTactics {
    val result = proveBy("x<5, x=0 ==> ".asSequent, exhaustiveEqL2R(-2))
    result.subgoals.loneElement shouldBe "0<5, x=0 ==> ".asSequent
  }

  it should "replace arbitary terms" in withTactics {
    val result = proveBy("a+b<5, a+b=c ==> ".asSequent, exhaustiveEqL2R(-2))
    result.subgoals.loneElement shouldBe "c<5, a+b=c ==> ".asSequent
  }

  // rewriting numbers is disallowed, because otherwise we run into endless rewriting
  it should "not rewrite numbers" in withTactics {
    the [IllegalArgumentException] thrownBy proveBy("0<5, 0=0 ==> ".asSequent, exhaustiveEqL2R(-2)) should have message "requirement failed: Rewriting numbers not supported"
  }

  it should "not try to rewrite bound occurrences" in withTactics {
    val result = proveBy("a=1 ==> [a:=2;]a=1".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "a=1 ==> [a:=2;]a=1".asSequent
  }

  it should "rewrite multiple occurrences of a term in one shot" in withTactics {
    val result = proveBy("x+2<=x+3, x=y ==> ".asSequent, exhaustiveEqL2R(-2))
    result.subgoals.loneElement shouldBe "y+2<=y+3, x=y ==> ".asSequent
  }

  it should "rewrite only free occurrences" in withQE { _ =>
    val result = proveBy("y=x ==> y=2 & \\exists y y<3, \\forall y y>4, y=5".asSequent, exhaustiveEqL2R(-1))
    result.subgoals.loneElement shouldBe "y=x ==> x=2 & \\exists y y<3, \\forall y y>4, x=5".asSequent
  }

  it should "hide when there are no more free occurrences after rewriting" in withTactics {
    proveBy("x=0 ==> [x:=x+1;]x>=1".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe " ==> [x:=0+1;]x>=1".asSequent
    proveBy("x=0 ==> [x:=x+1;]x>=1".asSequent, EqualityTactics.atomExhaustiveEqL2R(-1)).
      subgoals.loneElement shouldBe " ==> [x:=0+1;]x>=1".asSequent
  }

  it should "not hide when there are still free occurrences after rewriting" in withTactics {
    proveBy("x=0 ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "x=0 ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent
    proveBy("x=0 ==> [x:=x+1; ++ y:=2;]x>=0".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "x=0 ==> [x:=0+1; ++ y:=2;]x>=0".asSequent
    proveBy("x=0 ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent, EqualityTactics.atomExhaustiveEqL2R(-1)).
      subgoals.loneElement shouldBe "x=0 ==> [{x:=x+1;}*; x:=x+1;]x>=1".asSequent
    proveBy("x=0 ==> [x:=x+1; ++ y:=2;]x>=0".asSequent, EqualityTactics.atomExhaustiveEqL2R(-1)).
      subgoals.loneElement shouldBe "x=0 ==> [x:=0+1; ++ y:=2;]x>=0".asSequent
  }

  it should "bound rename when right-handside names clash" in withTactics {
    proveBy("y=x ==> \\forall x x<y".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "==> \\forall x_0 x_0<x".asSequent
    proveBy("y=x ==> [x:=x+y;]x>y".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "==> [x_0:=x+x;]x_0>x".asSequent
    proveBy("y=x ==> [x:=*;]x>y".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "==> [x_0:=*;]x_0>x".asSequent
    proveBy("y=x ==> \\forall x (x<y -> \\exists x x>y)".asSequent, TactixLibrary.exhaustiveEqL2R(hide=true)(-1)).
      subgoals.loneElement shouldBe "==> \\forall x_1 (x_1<x -> \\exists x_0 x_0>x)".asSequent
  }

  "Apply Equalities" should "rewrite all plain equalities" in withTactics {
    proveBy("x=2, x+y>=4, y=3 ==> y-x<=1, x=2".asSequent, applyEqualities).subgoals.loneElement shouldBe "2+3>=4 ==> 3-2<=1, 2=2".asSequent
    proveBy("x=x+2, x+y>=4, y=3 ==> y-x<=1, x=2".asSequent, applyEqualities).subgoals.loneElement shouldBe "x=x+2, x+2+3>=4 ==> 3-(x+2)<=1, x+2=2".asSequent
  }

  it should "not endless rewrite equalities when LHS and RHS are the same" in withTactics {
    proveBy("x=x, x+y>=4, y=3 ==> y-x<=1, x=2".asSequent, applyEqualities).subgoals.loneElement shouldBe "x=x, x+3>=4 ==> 3-x<=1, x=2".asSequent
  }

  it should "chain-rewrite" in withTactics {
    proveBy("y=z, z=0 ==> y=0".asSequent, applyEqualities).subgoals.loneElement shouldBe "==> 0=0".asSequent
    proveBy("x=y, y=z, z=0 ==> x=0".asSequent, applyEqualities).subgoals.loneElement shouldBe "==> 0=0".asSequent
    proveBy("x=y*z, y=z, z=0 ==> x=0".asSequent, applyEqualities).subgoals.loneElement shouldBe "==> 0*0=0".asSequent
  }

  it should "not rewrite verbatim occurrences even on the left-hand side of equalities in the antecedent" in withTactics {
    proveBy("x=y, x=y ==>".asSequent, applyEqualities).subgoals.loneElement shouldBe "y=y ==>".asSequent
    proveBy("x=y, x=x ==>".asSequent, applyEqualities).subgoals.loneElement shouldBe "y=y ==>".asSequent
    proveBy("x'=y, x'=x' ==>".asSequent, applyEqualities).subgoals.loneElement shouldBe "y=y ==>".asSequent
  }

  it should "not fail when rewriting creates self-rewrites" in withTactics {
    //@note rewriting x=y creates y=y which exhaustiveEqL2R rejects with IllegalArgumentException
    proveBy("y=x, x=y, x=x ==>".asSequent, applyEqualities).subgoals.loneElement shouldBe "y=y, y=y ==>".asSequent
  }

  it should "not fail when rewriting creates non-trivial left-hand sides" in withTactics {
    proveBy("x=y+1, x=z+5 ==>".asSequent, applyEqualities).subgoals.loneElement shouldBe "z+5=y+1 ==>".asSequent
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
    result.subgoals.loneElement shouldBe "min_<c, x>y, 5<min_, min_ = min(a,b) ==> min_+2=7, a<b, [b:=2;]min(a,b)<9".asSequent
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

  it should "abbreviate differentials" in withQE { _ =>
    proveBy("==> (f(x))'>0".asSequent, abbrv("(f(x))'".asTerm, None)).subgoals.loneElement shouldBe "x_0=(f(x))' ==> x_0>0".asSequent
  }

  it should "abbreviate differential symbols" in withQE { _ =>
    proveBy("==> x'>0".asSequent, abbrv("x'".asTerm, None)).subgoals.loneElement shouldBe "x_0=x' ==> x_0>0".asSequent
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
    result.subgoals.loneElement shouldBe "x>=0&abs_=x | x<0&abs_=-x ==> abs_>=5".asSequent
  }

  it should "expand abs(x) in non-top-level succedent" in withQE { _ =>
    val result = proveBy("y=2 | abs(x) >= 5".asFormula, abs(1, 1::0::Nil))
    result.subgoals.loneElement shouldBe "x>=0&abs_=x | x<0&abs_=-x ==> y=2 | abs_>=5".asSequent
  }

  it should "expand abs(x) in antecedent" in withQE { _ =>
    val result = proveBy("abs(x) >= 5 ==> ".asSequent, abs(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "abs_>=5, x>=0&abs_=x | x<0&abs_=-x ==> ".asSequent
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

  it should "find by top-level locator" in withQE { _ =>
    val s = "a=2 & five=abs(-5) ==>".asSequent
    proveBy(s, BelleParser(""" absExp('L=="a=2 & five=abs(-5)") """)).
      subgoals.loneElement shouldBe "a=2&five=abs_, -5>=0&abs_=-5 | -5 < 0&abs_=-(-5) ==>".asSequent
  }

  it should "expand nested" in withQE { _ =>
    proveBy("x <= abs(abs(x)) + abs(abs(x))".asFormula, abs(1)).subgoals.
      loneElement shouldBe "x>=0&abs_=x|x < 0&abs_=-x, abs_>=0&abs__0=abs_|abs_ < 0&abs__0=-abs_ ==> x<=abs__0+abs__0".asSequent
  }

  "min" should "expand min(x,y) in succedent" in withQE { _ =>
    val result = proveBy("min(x,y) >= 5".asFormula, minmax(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x<=y&min_=x | x>y&min_=y ==> min_>=5".asSequent
  }

  it should "expand min(x,y) in antecedent" in withQE { _ =>
    val result = proveBy("min(x,y) >= 5 ==> ".asSequent, minmax(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "min_>=5, x<=y&min_=x | x>y&min_=y ==> ".asSequent
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
    result.subgoals.loneElement shouldBe "min_=min__0, x<=y&min__0=x|x>y&min__0=y ==> (min_>=2|y=7)&min_<=10".asSequent
  }

  it should "expand exhaustively when applied to a formula" in withQE { _ =>
    proveBy("min(x,max(y,y^2)) + min(x,y^2) <= 2*max(y,y^2)".asFormula, minmax(1)).subgoals.loneElement shouldBe
      """x<=max_&min_=x|x>max_&min_=max_,
        |x<=y^2&min__0=x|x>y^2&min__0=y^2,
        |y>=y^2&max_=y|y < y^2&max_=y^2
        |==>
        |min_+min__0<=2*max_""".stripMargin.asSequent
    proveBy("min(x,max(y,z)) + min(x,y^2) <= 2*max(y,y^2)".asFormula, minmax(1)).subgoals.loneElement shouldBe
      """y>=z&max_=y|y < z&max_=z,
        |x<=max_&min_=x|x>max_&min_=max_,
        |x<=y^2&min__0=x|x>y^2&min__0=y^2,
        |y>=y^2&max__0=y|y < y^2&max__0=y^2
        |==>
        |min_+min__0<=2*max__0""".stripMargin.asSequent
  }

  it should "expand same nested" in withQE { _ =>
    proveBy("0 <= min(min(x,y), z) + min(min(x,y), z)".asFormula, minmax(1)).subgoals.
      loneElement shouldBe "x<=y&min_=x|x>y&min_=y, min_<=z&min__0=min_|min_>z&min__0=z ==> 0<=min__0+min__0".asSequent
  }

  "max" should "expand max(x,y) in succedent" in withQE { _ =>
    val result = proveBy("max(x,y) >= 5".asFormula, minmax(1, 0::Nil))
    result.subgoals.loneElement shouldBe "x>=y&max_=x | x<y&max_=y ==> max_>=5".asSequent
  }

  it should "expand max(x,y) in antecedent" in withQE { _ =>
    val result = proveBy("max(x,y) >= 5 ==> ".asSequent, minmax(-1, 0::Nil))
    result.subgoals.loneElement shouldBe "max_>=5, x>=y&max_=x | x<y&max_=y ==> ".asSequent
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
    result.subgoals.loneElement shouldBe "y=max_, x>=4&max_=x|x < 4&max_=4 ==> y>=4".asSequent
  }

  it should "find by top-level locator" in withQE { _ =>
    val s = "a=2 & five=max(0,5) ==>".asSequent
    proveBy(s, BelleParser(""" minmax('L=="a=2 & five=max(0,5)") """)).
      subgoals.loneElement shouldBe "a=2&five=max_, 0>=5&max_=0 | 0 < 5&max_=5 ==>".asSequent
  }

  "expandAll" should "expand abs everywhere" in withQE { _ =>
    val result = proveBy("abs(x-y)>0 ==> abs(a-5)>0, abs(x-y)>37".asSequent, expandAll)
    result.subgoals.loneElement shouldBe "abs_>0, x-y>=0&abs_=x-y|x-y < 0&abs_=-(x-y), a-5>=0&abs__0=a-5|a-5 < 0&abs__0=-(a-5) ==> abs__0>0, abs_>37".asSequent
  }

  it should "expand all special functions everywhere" in withQE { _ =>
    val result = proveBy("min(x,y)>0 ==> abs(a-5)>0, max(x,y)>37".asSequent, expandAll)
    result.subgoals.loneElement shouldBe "min_>0, x<=y&min_=x|x>y&min_=y, a-5>=0&abs_=a-5|a-5 < 0&abs_=-(a-5), x>=y&max_=x|x < y&max_=y ==> abs_>0, max_>37".asSequent
  }

  it should "expand in context" in withQE { _ =>
    val result = proveBy("min(x,y)>0, abs(a-5)>7 ==> abs(a-5)>0, [a:=3;]abs(a-5)>=2, max(x,y)>0, [x:=4;]min(x,y)>=4".asSequent, expandAll)
    result.subgoals.loneElement shouldBe
      """min_>0,
        |abs_>7,
        |x<=y&min_=x|x>y&min_=y,
        |a-5>=0&abs_=a-5|a-5 < 0&abs_=-(a-5),
        |x>=y&max_=x|x < y&max_=y
        |==>
        |abs_>0,
        |[a:=3;](a-5>=0&a-5>=2|a-5 < 0&-(a-5)>=2),
        |max_>0,
        |[x:=4;](x<=y&x>=4|x>y&y>=4)
      """.stripMargin.asSequent
  }

  it should "expand anywhere in a term" in withQE { _ =>
    val result = proveBy("(x+4)/min(1,3) >= x".asFormula, expandAll)
    result.subgoals.loneElement shouldBe "1<=3 & min_=1 | 1>3 & min_=3 ==> (x+4)/min_ >= x".asSequent
  }

  it should "not infinite recurse but report exception" in withQE { _ =>
    val f = "[{x'=100*x^4+y*x^3-x^2+x+c,c'=x+y+z,dbxy_'=(-(0--x)*(-- (100*x^4+y*x^3-x^2+x+c))/max(((0--x)*(0--x),-- (100*x^4+y*x^3-x^2+x+c))))*dbxy_+0&c>x&max(((0--x)*(0--x),-- (100*x^4+y*x^3-x^2+x+c)))>0}]dbxy_>0".asFormula
    (the [ProverException] thrownBy proveBy(f, expandAll)).getMessage should startWith
      "Unable to create dependent tactic 'CMonCongruence'"
  }

  it should "expand in the context of quantifiers" in withQE { _ =>
    proveBy("\\exists t_ (t>=0 & \\forall s_ (0<=s_&s_<=t_ -> !(abs(x)<abs(x+s_))))".asFormula, expandAll).subgoals.
      loneElement shouldBe "x>=0&abs_=x|x < 0&abs_=-x ==> \\exists t_ (t>=0 & \\forall s_ (0<=s_&s_<=t_->!(x+s_>=0&abs_ < x+s_|x+s_ < 0&abs_ < -(x+s_))))".asSequent
  }

  "Alpha renaming" should "rename in ODEs in succedent" in withQE { _ =>
    val result = proveBy("x=y, [{y'=y}]y>=0 ==> [{x'=x}]x>=0".asSequent, SequentCalculus.alphaRen("x".asVariable, "y".asVariable)(1))
    result.subgoals should contain theSameElementsInOrderAs List(
      "x=y, [{y'=y}]y>=0 ==> [{y'=y}]y>=0".asSequent,
      "x=y, [{y'=y}]y>=0 ==> [{x'=x}]x>=0, x=y".asSequent)
  }

  it should "rename in ODEs in antecedent" in withQE { _ =>
    val result = proveBy("y=x, [{y'=y}]y>=0 ==> [{x'=x}]x>=0".asSequent, SequentCalculus.alphaRen("y".asVariable, "x".asVariable)(-2))
    result.subgoals should contain theSameElementsInOrderAs List(
      "y=x, [{x'=x}]x>=0 ==> [{x'=x}]x>=0".asSequent,
      "y=x, [{y'=y}]y>=0 ==> [{x'=x}]x>=0, y=x".asSequent)
  }

  it should "rename quantified differential symbols" in withQE { _ =>
    proveBy("\\forall x' x'>0 ==>".asSequent, SequentCalculus.alphaRen("x".asVariable, "y".asVariable)(-1)).
      subgoals should contain theSameElementsInOrderAs List(
        "\\forall y' y'>0 ==>".asSequent,
        "\\forall x' x'>0 ==> x=y".asSequent
    )
  }

  it should "rename quantified differential symbols inside differentials" in withQE { _ =>
    proveBy("\\forall x' (f(x))'>0 ==>".asSequent, SequentCalculus.alphaRen("x".asVariable, "y".asVariable)(-1)).
      subgoals should contain theSameElementsInOrderAs List(
      "\\forall y' (f(y))'>0 ==>".asSequent,
      "\\forall x' (f(x))'>0 ==> x=y".asSequent
    )
    proveBy("\\forall x' (f(x))'>0 ==>".asSequent, SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).
      subgoals should contain theSameElementsInOrderAs List(
      "\\forall y' (f(y))'>0 ==>".asSequent,
      "\\forall x' (f(x))'>0 ==> x=y".asSequent
    )
    proveBy("x=y, \\forall x' (f(x))'>0 ==> ".asSequent, SequentCalculus.alphaRenAllBy(-1)).
      subgoals.loneElement shouldBe "x=y, \\forall y' (f(y))'>0 ==>".asSequent
  }

  "Alpha renaming all" should "rename in ODEs in succedent" in withQE { _ =>
    val result = proveBy("x=y, [{y'=y}]y>=0 ==> [{x'=x}]x>=0".asSequent, SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable))
    result.subgoals.loneElement shouldBe "x=y, [{y'=y}]y>=0 ==> [{y'=y}]y>=0".asSequent
  }

  it should "rename in ODEs in antecedent" in withQE { _ =>
    val result = proveBy("x=y, [{x'=x}]x>=0 ==> [{y'=y}]y>=0".asSequent, SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable))
    result.subgoals.loneElement shouldBe "x=y, [{y'=y}]y>=0 ==> [{y'=y}]y>=0".asSequent
  }

  it should "rename everywhere" in withQE { _ =>
    val result = proveBy("x=y, [{x'=x}]x>=0 ==> [{y'=y}]y>=0, x>=4, [z:=2;][x:=x+1;]x>=0".asSequent, SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable))
    result.subgoals.loneElement shouldBe "x=y, [{y'=y}]y>=0 ==> [{y'=y}]y>=0, y>=4, [z:=2;][y:=y+1;]y>=0".asSequent
  }

  it should "not rename in formulas with free occurrences of right-hand side" in withQE { _ =>
    val result = proveBy("x=y, [{x'=x+y}]x>=0 ==> [{y'=y}]y>=0, x>=4, [z:=2;][x:=x+1;]\\exists y y>=0".asSequent, SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable))
    //@todo want \\exists y y>=0: add another bound renaming to undo the variable flip
    //@todo want [y:=y+1;] needs fix in exhaustiveEqL2R
    result.subgoals.loneElement shouldBe "x=y, [{x'=x+y}]x>=0 ==> [{y'=y}]y>=0, y>=4, [z:=2;][y_0:=y+1;]\\exists x x>=0".asSequent
  }

  it should "cut equality" in withQE { _ =>
    proveBy("[{x'=x}]x>=0 ==> [{y'=y}]y>=0".asSequent, SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).
      subgoals should contain theSameElementsInOrderAs List(
      "[{y'=y}]y>=0 ==> [{y'=y}]y>=0".asSequent,
      "[{x'=x}]x>=0 ==> [{y'=y}]y>=0, x=y".asSequent)
    proveBy("[{x'=x}]x>=0, !x!=y ==> [{y'=y}]y>=0".asSequent, SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).
      subgoals should contain theSameElementsInOrderAs List(
      "[{y'=y}]y>=0, !y!=y ==> [{y'=y}]y>=0".asSequent,
      "[{x'=x}]x>=0, !x!=y ==> [{y'=y}]y>=0, x=y".asSequent)
    proveBy("[{x'=x}]x>=0, ==> x!=y, [{y'=y}]y>=0".asSequent, SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).
      subgoals should contain theSameElementsInOrderAs List(
      "[{y'=y}]y>=0, ==> y!=y, [{y'=y}]y>=0".asSequent,
      "[{x'=x}]x>=0, ==> x!=y, [{y'=y}]y>=0, x=y".asSequent)
  }

  it should "automate equality cut when what is mustbound" in withQE { _ =>
    proveBy("<x:=r;><{?x>1;x:=x-1;}*>x=0, x=y ==> <y:=r;><{?y>1;y:=y-1;}*>y=0".asSequent,
      SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).subgoals.
      loneElement shouldBe "<y:=r;><{?y>1;y:=y-1;}*>y=0, x=y ==> <y:=r;><{?y>1;y:=y-1;}*>y=0".asSequent
    proveBy("<x:=r;><{?x>1;x:=x-1;}*>x=0 ==> <y:=r;><{?y>1;y:=y-1;}*>y=0".asSequent,
      SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).subgoals.
      loneElement shouldBe "<y:=r;><{?y>1;y:=y-1;}*>y=0 ==> <y:=r;><{?y>1;y:=y-1;}*>y=0".asSequent
    proveBy("<x:=r;><{?x>1;x:=x-1;}*>x=0, x=r, y=r ==> <y:=r;><{?y>1;y:=y-1;}*>y=0".asSequent,
      SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).subgoals.
      loneElement shouldBe "<y:=r;><{?y>1;y:=y-1;}*>y=0, x=r, y=r ==> <y:=r;><{?y>1;y:=y-1;}*>y=0".asSequent
    proveBy("y=r, <x:=r;><{?x>1;x:=x-1;}*>x=0 ==> <{?y>1;y:=y-1;}*>y=0".asSequent,
      SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).subgoals.
      loneElement shouldBe "y=r, <y:=r;><{?y>1;y:=y-1;}*>y=0 ==> <{?y>1;y:=y-1;}*>y=0".asSequent
    proveBy("<x:=r;><{?x>1;x:=x-1;}*>x=0 ==> [y:=1+r-1;]<{?y>1;y:=y-1;}*>y=0".asSequent,
      SequentCalculus.alphaRenAll("x".asVariable, "y".asVariable)).subgoals.
      loneElement shouldBe "<y:=r;><{?y>1;y:=y-1;}*>y=0 ==> [y:=1+r-1;]<{?y>1;y:=y-1;}*>y=0".asSequent
  }
}
