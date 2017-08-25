package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import org.scalatest.Inside._
import org.scalatest.LoneElement._

/**
 * Tests automatic
 * [[edu.cmu.cs.ls.keymaerax.btactics.ToolTactics]].
 */
@UsualTest
class ToolTacticsTests extends TacticTestBase {
  "Transform" should "transform top-level" in withMathematica { _ =>
    proveBy("x>=0".asFormula, transform("x>=1".asFormula)(1)).subgoals.loneElement shouldBe "==> x>=1".asSequent
  }

  it should "transform top-level in ante" in withMathematica { _ =>
    proveBy("x>=0 ==> ".asSequent, transform("x>=-1".asFormula)(-1)).subgoals.loneElement shouldBe "x>=-1 ==> ".asSequent
  }

  it should "work with non-FO formulas present" in withMathematica { _ =>
    val result = proveBy("[a:=2;]a>=1 ==> x>=0, [b:=3;]b>1".asSequent, transform("x>=1".asFormula)(1))
    result.subgoals.loneElement shouldBe "[a:=2;]a>=1 ==> x>=1, [b:=3;]b>1".asSequent
  }

  it should "retain global facts for transformation" in withMathematica { _ =>
    val result = proveBy("c>0 ==> x/c>=0".asSequent, transform("x/c>=1".asFormula)(1))
    result.subgoals.loneElement shouldBe "c>0 ==> x/c>=1".asSequent
  }

  it should "retain all global facts for transformation" in withMathematica { _ =>
    val result = proveBy("a=0, c+a>0 ==> x/c>=0".asSequent, transform("x/c>=1".asFormula)(1))
    result.subgoals.loneElement shouldBe "a=0, c+a>0 ==> x/c>=1".asSequent
  }

  it should "retain global facts for transformation in ante" in withMathematica { _ =>
    val result = proveBy("c>0, x/c>=1 ==> ".asSequent, transform("x/c>=0".asFormula)(-2))
    result.subgoals.loneElement shouldBe "c>0, x/c>=0 ==> ".asSequent
  }

  it should "fail in the right way after all filters are unsuccessful" in withMathematica { _ =>
    the [BelleThrowable] thrownBy proveBy("z<=5 ==> ".asSequent,
      transform("z<=4".asFormula)(-1)) shouldNot have message "[Bellerophon Runtime] head of empty list"
    inside(the [BelleThrowable] thrownBy proveBy("z<=5 ==> ".asSequent, transform("z<=4".asFormula)(-1))) {
      case bt: BelleThrowable =>
        bt should have message "[Bellerophon Runtime] Tactic transform({`z<=4`},-1) may point to wrong position, found Some(z<=5) at position Fixed(-1,None,true)"
        bt.getCause should have message "[Bellerophon Runtime] Invalid transformation: z<=4"
    }
  }

  it should "work on the postcondition of a simple box property" in withMathematica { _ =>
    val result = proveBy("x>2 -> [a:=2;]x>1".asFormula, transform("x>2".asFormula)(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>2 -> [a:=2;]x>2".asSequent
  }

  it should "work on the postcondition of a box ODE" in withMathematica { _ =>
    val result = proveBy("x>2 -> [{a'=x}]x>1".asFormula, transform("x>2".asFormula)(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>2 -> [{a'=x}]x>2".asSequent
  }

  it should "work on the postcondition of a simple diamond property" in withMathematica { _ =>
    val result = proveBy("x>2 -> <a:=2;>x>1".asFormula, transform("x>2".asFormula)(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>2 -> <a:=2;>x>2".asSequent
  }

  it should "work on the postcondition of a diamond ODE" in withMathematica { _ =>
    val result = proveBy("x>2 -> <{a'=x}>x>1".asFormula, transform("x>2".asFormula)(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>2 -> <{a'=x}>x>2".asSequent
  }

  it should "work inside quantified formulas as arising in diff. solve" in withMathematica { _ =>
    val result = proveBy(
      "x=1&v=2 ==> \\exists t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->v=2)&(v*t_+x)^3>=1)".asSequent,
      transform("v=2->v=2".asFormula)(1, 0::1::0::0::1::Nil))
    result.subgoals.loneElement shouldBe "x=1&v=2 ==> \\forall t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->(v=2->v=2))&(v*t_+x)^3>=1)".asSequent
  }

  it should "cohide other formulas in succ when proving a transformation in ante" in withMathematica { _ =>
    val result = proveBy("x>0, y>0, z=x+y ==> [{x'=-x^y}]x>0".asSequent, transform("z>0".asFormula)(-3))
    result.subgoals.loneElement shouldBe "x>0, y>0, z>0 ==> [{x'=-x^y}]x>0".asSequent
  }

  it should "cohide other formulas in succ when proving a transformation in succ" in withMathematica { _ =>
    val result = proveBy("x>0, y>0 ==> [{x'=-x^y}]x>0, z>0, [{x:=x+1;}*]x>0".asSequent, transform("z>x+y".asFormula)(2))
    result.subgoals.loneElement shouldBe "x>0, y>0 ==> [{x'=-x^y}]x>0, z>x+y, [{x:=x+1;}*]x>0".asSequent
  }

  //@todo missing feature
  it should "cohide other formulas in succ when proving a transformation in negative polarity in ante" ignore withMathematica { _ =>
    val result = proveBy("x>0, y>0, z>0->a=5 ==> [{x'=-x^y}]x>0".asSequent, transform("z>x+y".asFormula)(-3, 0::Nil))
    result.subgoals.loneElement shouldBe "x>0, y>0, z>x+y->a=5 ==> [{x'=-x^y}]x>0".asSequent
  }

  //@todo missing feature
  it should "cohide other formulas in succ when proving a transformation in negative polarity in succ" ignore withMathematica { _ =>
    val result = proveBy("x>0, y>0 ==> [{x'=-x^y}]x>0, z>x+y->a=5, [{x:=x+1;}*]x>0".asSequent, transform("z>0".asFormula)(2, 0::Nil))
    result.subgoals.loneElement shouldBe "x>0, y>0 ==> [{x'=-x^y}]x>0, z>0->a=5, [{x:=x+1;}*]x>0".asSequent
  }

  "Transform in context" should "exploit equivalence" in withMathematica { _ =>
    val result = proveBy("[x:=4;]x>=v*v".asFormula, transform("x>=v^2".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=4;]x>=v^2".asSequent
  }

  it should "exploit conditional equivalence from global facts" in withMathematica { _ =>
    val result = proveBy("b>0 ==> [x:=4;]2*x*b>=v*v".asSequent, transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from unmodified global facts deeply nested" in withMathematica { _ =>
    val result = proveBy("b>0 ==> [x:=4;][v:=2;][a:=3;]2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;][v:=2;][a:=3;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from global facts retained deeply nested 2" in withMathematica { _ =>
    val result = proveBy("b>0 ==> [x:=4;][b:=2*b;][a:=3;]2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;][b:=2*b;][a:=3;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from global facts retained deeply nested 3" in withMathematica { _ =>
    val result = proveBy("b>0 ==> [x:=4;][b:=2*b;][a:=3;][{b'=a}][{b:=b+1;}*][?c=4;]2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::1::1::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;][b:=2*b;][a:=3;][{b'=a}][{b:=b+1;}*][?c=4;]x>=v^2/(2*b)".asSequent
  }

  //@todo invariant generation
  it should "exploit conditional equivalence from global facts retained deeply nested 4" ignore withMathematica { _ =>
    val result = proveBy("b>0 ==> [x:=4;][b:=2*b;][a:=3;][{a:=a+1;}*][{b'=a}][{b:=b+1;}*][?c=4;]2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::1::1::1::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;][b:=2*b;][a:=3;][{a:=a+1;}*][{b'=a}][{b:=b+1;}*][?c=4;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from global facts propositionally nested" in withMathematica { _ =>
    val result = proveBy("b>0 ==> x=4 | 2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> x=4 | x>=v^2/(2*b)".asSequent
  }

  //@todo how to prove precondition b>0 still holds in context when initial question is false already?
  it should "exploit conditional equivalence from global facts propositionally nested with false" ignore withMathematica { _ =>
    val result = proveBy("b>0 ==> false & 2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> false & x>=v^2/(2*b)".asSequent
  }

  it should "retain context in universal quantifier" in withMathematica { _ =>
    val result = proveBy("b>0 ==> \\forall x x>=0".asSequent,
      transform("y/b>0 & x*y>=0".asFormula)(1, 0::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> \\forall x (y/b>0 & x*y>=0)".asSequent
  }

  it should "retain context in existential quantifier" ignore withMathematica { _ =>
    val result = proveBy("b>0 ==> \\exists x x>=0".asSequent,
      transform("y/b>0 & x*y>=0".asFormula)(1, 0::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> \\exists x (y/b>0 & x*y>=0)".asSequent
  }

  it should "introduce new variables in results of DG" in withMathematica { _ =>
    val result = proveBy("x>0 -> \\exists y [{x'=-x,y'=1/2}]x>0".asFormula, implyR(1) & transform("x*y^2=1".asFormula)(1, 0::1::Nil))
    result.subgoals.loneElement shouldBe "x>0 ==> \\exists y [{x'=-x,y'=1/2}]x*y^2=1".asSequent
  }

  it should "retain context when introducing new variables in results of DG" ignore withMathematica { _ =>
    val result = proveBy("b>0 ==> \\exists y [{x'=2,y'=1}]x>=0".asSequent, transform("y/b>0 & x*y>=0".asFormula)(1, 0::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> \\exists y [{x'=2,y'=1}](y/b>0 & x*y>=0)".asSequent
  }

  it should "transform terms" in withMathematica { _ =>
    val result = proveBy("[x:=x/b+1+1+0;]x>0".asFormula, transform("x/b+2".asTerm)(1, 0::1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=x/b+2;]x>0".asSequent
  }

  "Edit" should "transform when special function abbrv is not used" in withMathematica { _ =>
    proveBy("x>=0".asFormula, edit("x>=1".asFormula)(1)).subgoals.loneElement shouldBe "==> x>=1".asSequent
  }

  it should "abbreviate" in withMathematica { _ =>
    proveBy("x>=2+3".asFormula, edit("x>=abbrv(2+3,y)".asFormula)(1)).subgoals.loneElement shouldBe "y=2+3 ==> x>=y".asSequent
    proveBy("2*g()*x=37".asFormula, edit("abbrv(2*g())*x=37".asFormula)(1)).subgoals.loneElement shouldBe "abbrv=2*g() ==> abbrv*x=37".asSequent
    proveBy("2*g()*x=37+4".asFormula, edit("abbrv(2*g())*x=abbrv(37+4)".asFormula)(1)).subgoals.loneElement shouldBe "abbrv=2*g(), abbrv_0=37+4 ==> abbrv*x=abbrv_0".asSequent
    proveBy("2*g()*x=37".asFormula, edit("abbrv(2*g(),foo)*x=37".asFormula)(1)).subgoals.loneElement shouldBe "foo=2*g() ==> foo*x=37".asSequent
    // does not unify
    //proveBy("2*g()*x=37".asFormula, edit("2*foo=37".asFormula)(1)).subgoals.loneElement shouldBe "foo=g()*x ==> 2*foo=37".asSequent
  }

  it should "only abbreviate if no transformations are present" in withMathematica { _ => withDatabase { db =>
    val (proofId, provable) = db.proveByWithProofId("x>=2+3", edit("x>=abbrv(2+3,y)".asFormula)(1))
    provable.subgoals.loneElement shouldBe "y=2+3 ==> x>=y".asSequent
    db.extractTactic(proofId) shouldBe BelleParser("edit({`x>=abbrv(2+3,y)`},1)")
    db.extractStepDetails(proofId, "(1,0)") shouldBe BelleParser("abbrv({`2+3`},{`y`})")
  }}

  it should "abbreviate and transform" in withMathematica { _ => withDatabase { db =>
    val (proofId, provable) = db.proveByWithProofId("2*g()*x=37+4", edit("abbrv(2*g())*x=41".asFormula)(1))
    provable.subgoals.loneElement shouldBe "abbrv=2*g() ==> abbrv*x=41".asSequent
    db.extractTactic(proofId) shouldBe BelleParser("edit({`abbrv(2*g())*x=41`},1)")
    db.extractStepDetails(proofId, "(1,0)") shouldBe BelleParser("abbrv({`2*g()`},{`abbrv`}) & transform({`abbrv*x=41`},1)")
  }}

  it should "expand abs" in withMathematica { _ =>
    proveBy("abs(x)>=0".asFormula, edit("expand(abs(x))>=1".asFormula)(1)).subgoals.loneElement shouldBe
      "x>=0&abs_0=x | x<0&abs_0=-x ==> abs_0>=1".asSequent
  }

  it should "expand min" in withMathematica { _ =>
    proveBy("min(x,y)>=0".asFormula, edit("expand(min(x,y))>=1".asFormula)(1)).subgoals.loneElement shouldBe
      "x<=y&min_0=x | x>y&min_0=y ==> min_0>=1".asSequent
  }

  it should "expand max" in withMathematica { _ =>
    proveBy("max(x,y)>=0".asFormula, edit("expand(max(x,y))>=1".asFormula)(1)).subgoals.loneElement shouldBe
      "x>=y&max_0=x | x<y&max_0=y ==> max_0>=1".asSequent
  }

  it should "abbreviate and expand" in withMathematica { _ =>
    proveBy("max(x+5*2,y)>=0".asFormula, edit("expand(max(abbrv(x+5*2,z),y))>=1".asFormula)(1)).subgoals.loneElement shouldBe
      "z=x+5*2, z>=y&max_0=z | z<y&max_0=y ==> max_0>=1".asSequent
  }

  it should "abbreviate and expand and transform" in withMathematica { _ => withDatabase { db =>
    val (proofId, provable) = db.proveByWithProofId("2*g()*abs(x)=37+4", edit("abbrv(2*g())*expand(abs(x))=41".asFormula)(1))
    provable.subgoals.loneElement shouldBe "abbrv=2*g(), x>=0&abs_0=x | x<0&abs_0=-x ==> abbrv*abs_0=41".asSequent
    db.extractTactic(proofId) shouldBe BelleParser("edit({`abbrv(2*g())*expand(abs(x))=41`},1)")
    db.extractStepDetails(proofId, "(1,0)") shouldBe BelleParser("abbrv({`2*g()`},{`abbrv`}) & absExp(1.0.1) & transform({`abbrv*abs_0=41`},1)")
  }}

  it should "abbreviate in programs" in withMathematica { _ =>
    proveBy("[x:=2+3;]x=5".asFormula, edit("[x:=abbrv(2+3,five);]x=5".asFormula)(1)).subgoals.loneElement shouldBe
      "five=2+3 ==> [x:=five;]x=5".asSequent
  }

  it should "expand multiple at once" in withMathematica { _ =>
    proveBy("abs(a)>0, abs(c)>3 ==> abs(a)>0 | abs(b)>1 | abs(c)>2".asSequent,
      edit("expand(abs(a))>0 | expand(abs(b))>1 | expand(abs(c))>2".asFormula)(1)).
      subgoals.loneElement shouldBe
      "abs_0>0, abs_2>3, a>=0 & abs_0=a | a<0 & abs_0=-a, b>=0 & abs_1=b | b<0 & abs_1=-b, c>=0 & abs_2=c | c<0 & abs_2=-c ==> abs_0>0 | abs_1>1 | abs_2>2".asSequent
  }

}
