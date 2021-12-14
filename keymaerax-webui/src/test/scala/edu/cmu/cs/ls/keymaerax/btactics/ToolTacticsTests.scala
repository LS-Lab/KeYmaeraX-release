package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleCEX, BelleThrowable}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import org.scalatest.LoneElement._

/**
 * Tests automatic
 * [[edu.cmu.cs.ls.keymaerax.btactics.ToolTactics]].
 */
@UsualTest
class ToolTacticsTests extends TacticTestBase {
  "Transform" should "transform top-level" in withQE { _ =>
    proveBy("x>=0".asFormula, transform("x>=1".asFormula)(1)).subgoals.loneElement shouldBe "==> x>=1".asSequent
  }

  it should "transform top-level in ante" in withQE { _ =>
    proveBy("x>=0 ==> ".asSequent, transform("x>=-1".asFormula)(-1)).subgoals.loneElement shouldBe "x>=-1 ==> ".asSequent
  }

  it should "work with non-FO formulas present" in withQE { _ =>
    val result = proveBy("[a:=2;]a>=1 ==> x>=0, [b:=3;]b>1".asSequent, transform("x>=1".asFormula)(1))
    result.subgoals.loneElement shouldBe "[a:=2;]a>=1 ==> x>=1, [b:=3;]b>1".asSequent
  }

  it should "retain global facts for transformation" in withQE { _ =>
    val result = proveBy("c>0 ==> x/c>=0".asSequent, transform("x/c>=1".asFormula)(1))
    result.subgoals.loneElement shouldBe "c>0 ==> x/c>=1".asSequent
  }

  it should "retain all global facts for transformation" in withQE { _ =>
    val result = proveBy("a=0, c+a>0 ==> x/c>=0".asSequent, transform("x/c>=1".asFormula)(1))
    result.subgoals.loneElement shouldBe "a=0, c+a>0 ==> x/c>=1".asSequent
  }

  it should "retain global facts for transformation in ante" in withQE { _ =>
    val result = proveBy("c>0, x/c>=1 ==> ".asSequent, transform("x/c>=0".asFormula)(-2))
    result.subgoals.loneElement shouldBe "c>0, x/c>=0 ==> ".asSequent
  }

  it should "fail in the right way after all filters are unsuccessful" in withQE { _ =>
    the [BelleThrowable] thrownBy proveBy("z<=5 ==> ".asSequent,
      transform("z<=4".asFormula)(-1)) shouldNot have message "head of empty list"
    the [BelleThrowable] thrownBy proveBy("z<=5 ==> ".asSequent, transform("z<=4".asFormula)(-1)) should
      have message "Invalid transformation: cannot transform Some(z<=5) to z<=4"
  }

  it should "fail non-critical on invalid transformation" in withQE { _ =>
    proveBy("==> x<=5".asSequent, transform("x<=6".asFormula)(1) | transform("x<=4".asFormula)(1)).subgoals.
      loneElement shouldBe "==> x<=4".asSequent
  }

  it should "work on the postcondition of a simple box property" in withQE { _ =>
    val result = proveBy("x>2 -> [a:=2;]x>1".asFormula, transform("x>2".asFormula)(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>2 -> [a:=2;]x>2".asSequent
  }

  it should "work on the postcondition of a box ODE" in withQE { _ =>
    val result = proveBy("x>2 -> [{a'=x}]x>1".asFormula, transform("x>2".asFormula)(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>2 -> [{a'=x}]x>2".asSequent
  }

  it should "work on the postcondition of a simple diamond property" in withQE { _ =>
    val result = proveBy("x>2 -> <a:=2;>x>1".asFormula, transform("x>2".asFormula)(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>2 -> <a:=2;>x>2".asSequent
  }

  it should "work on the postcondition of a diamond ODE" in withQE { _ =>
    val result = proveBy("x>2 -> <{a'=x}>x>1".asFormula, transform("x>2".asFormula)(1, 1::1::Nil))
    result.subgoals.loneElement shouldBe "==> x>2 -> <{a'=x}>x>2".asSequent
  }

  it should "work inside quantified formulas as arising in diff. solve" in withMathematica { _ =>
    val result = proveBy(
      "x=1&v=2 ==> \\exists t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->v=2)&(v*t_+x)^3>=1)".asSequent,
      transform("v=2->v=2".asFormula)(1, 0::1::0::0::1::Nil))
    result.subgoals.loneElement shouldBe "x=1&v=2 ==> \\forall t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->(v=2->v=2))&(v*t_+x)^3>=1)".asSequent
  }

  it should "cohide other formulas in succ when proving a transformation in ante" in withQE { _ =>
    val result = proveBy("x>0, y>0, z=x+y ==> [{x'=-x^y}]x>0".asSequent, transform("z>0".asFormula)(-3))
    result.subgoals.loneElement shouldBe "x>0, y>0, z>0 ==> [{x'=-x^y}]x>0".asSequent
  }

  it should "cohide other formulas in succ when proving a transformation in succ" in withQE { _ =>
    val result = proveBy("x>0, y>0 ==> [{x'=-x^y}]x>0, z>0, [{x:=x+1;}*]x>0".asSequent, transform("z>x+y".asFormula)(2))
    result.subgoals.loneElement shouldBe "x>0, y>0 ==> [{x'=-x^y}]x>0, z>x+y, [{x:=x+1;}*]x>0".asSequent
  }

  //@todo missing feature
  it should "cohide other formulas in succ when proving a transformation in negative polarity in ante" ignore withQE { _ =>
    val result = proveBy("x>0, y>0, z>0->a=5 ==> [{x'=-x^y}]x>0".asSequent, transform("z>x+y".asFormula)(-3, 0::Nil))
    result.subgoals.loneElement shouldBe "x>0, y>0, z>x+y->a=5 ==> [{x'=-x^y}]x>0".asSequent
  }

  //@todo missing feature
  it should "cohide other formulas in succ when proving a transformation in negative polarity in succ" ignore withQE { _ =>
    val result = proveBy("x>0, y>0 ==> [{x'=-x^y}]x>0, z>x+y->a=5, [{x:=x+1;}*]x>0".asSequent, transform("z>0".asFormula)(2, 0::Nil))
    result.subgoals.loneElement shouldBe "x>0, y>0 ==> [{x'=-x^y}]x>0, z>0->a=5, [{x:=x+1;}*]x>0".asSequent
  }

  it should "transform double negation" in withQE { _ =>
    proveBy("b=5 & --b>0 -> b>0".asFormula, edit("b=5 & b>0 -> b>0".asFormula)(1)).
      subgoals.loneElement shouldBe "==> b=5 & b>0 -> b>0".asSequent
    proveBy("b()=5 & --b()>0 -> b()>0".asFormula, edit("b()=5 & b()>0 -> b()>0".asFormula)(1)).
      subgoals.loneElement shouldBe "==> b()=5 & b()>0 -> b()>0".asSequent
  }

  it should "introduce universal quantifiers" in withQE { _ =>
    proveBy("\\forall y (x>0 & y>0)".asFormula, edit("\\forall x \\forall y (x>0 & y>0)".asFormula)(1)).
      subgoals.loneElement shouldBe "==> \\forall x \\forall y (x>0 & y>0)".asSequent
  }

  it should "work on a Robix example" in withMathematica { _ =>
    //@todo proves fast in Z3 4.8.4, does not complete within 20min in Z3 4.8.10
    val s = "A()>=0, b()>0, ep()>0, V()>=0, vxo^2+vyo^2<=V()^2, r!=0, abs(x_0-xo_1)>v_0^2/(2*b())+V()*v_0/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_0+V())), v_0>=0, -t*(v-A()/2*t)<=y-y_0, y-y_0<=t*(v-A()/2*t), -t*(v-A()/2*t)<=x-x_0, x-x_0<=t*(v-A()/2*t), v=v_0+A()*t, -t*V()<=yo-yo_1, yo-yo_1<=t*V(), -t*V()<=xo-xo_1, xo-xo_1<=t*V(), dx^2+dy^2=1, t>=0, t<=ep(), v>=0, v>0\n  ==>  abs(x-xo)>v^2/(2*b())+V()*v/b(), abs(y-yo)>v^2/(2*b())+V()*v/b()".asSequent
    proveBy(s, TactixLibrary.transform("abs(x_0-xo_1)>v_0^2/(2*b())+V()*v_0/b()+(A()/b()+1)*(A()/2*t^2+t*(v_0+V()))".asFormula)(-7)).subgoals.
      loneElement shouldBe "A()>=0, b()>0, ep()>0, V()>=0, vxo^2+vyo^2<=V()^2, r!=0, abs(x_0-xo_1)>v_0^2/(2*b())+V()*v_0/b()+(A()/b()+1)*(A()/2*t^2+t*(v_0+V())), v_0>=0, -t*(v-A()/2*t)<=y-y_0, y-y_0<=t*(v-A()/2*t), -t*(v-A()/2*t)<=x-x_0, x-x_0<=t*(v-A()/2*t), v=v_0+A()*t, -t*V()<=yo-yo_1, yo-yo_1<=t*V(), -t*V()<=xo-xo_1, xo-xo_1<=t*V(), dx^2+dy^2=1, t>=0, t<=ep(), v>=0, v>0\n  ==>  abs(x-xo)>v^2/(2*b())+V()*v/b(), abs(y-yo)>v^2/(2*b())+V()*v/b()".asSequent
  }

  "Transform in context" should "exploit equivalence" in withQE { _ =>
    val result = proveBy("[x:=4;]x>=v*v".asFormula, transform("x>=v^2".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=4;]x>=v^2".asSequent
  }

  it should "exploit conditional equivalence from global facts" in withQE { _ =>
    val result = proveBy("b>0 ==> [x:=4;]2*x*b>=v*v".asSequent, transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from negated global facts" in withQE { _ =>
    val result = proveBy("==> b<=0, [x:=4;]2*x*b>=v*v".asSequent, transform("x>=v^2/(2*b)".asFormula)(2, 1::Nil))
    result.subgoals.loneElement shouldBe "==> b<=0, [x:=4;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from unmodified global facts deeply nested" in withQE { _ =>
    val result = proveBy("b>0 ==> [x:=4;][v:=2;][a:=3;]2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;][v:=2;][a:=3;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from global facts retained deeply nested 2" in withQE { _ =>
    val result = proveBy("b>0 ==> [x:=4;][b:=2*b;][a:=3;]2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;][b:=2*b;][a:=3;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from global facts retained deeply nested 3" in withQE { _ =>
    val result = proveBy("b>0 ==> [x:=4;][b:=2*b;][a:=3;][{b'=a}][{b:=b+1;}*][?c=4;]2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::1::1::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;][b:=2*b;][a:=3;][{b'=a}][{b:=b+1;}*][?c=4;]x>=v^2/(2*b)".asSequent
  }

  //@todo invariant generation
  it should "exploit conditional equivalence from global facts retained deeply nested 4" ignore withQE { _ =>
    val result = proveBy("b>0 ==> [x:=4;][b:=2*b;][a:=3;][{a:=a+1;}*][{b'=a}][{b:=b+1;}*][?c=4;]2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::1::1::1::1::1::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> [x:=4;][b:=2*b;][a:=3;][{a:=a+1;}*][{b'=a}][{b:=b+1;}*][?c=4;]x>=v^2/(2*b)".asSequent
  }

  it should "exploit conditional equivalence from global facts propositionally nested" in withQE { _ =>
    val result = proveBy("b>0 ==> x=4 | 2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> x=4 | x>=v^2/(2*b)".asSequent
  }

  //@todo how to prove precondition b>0 still holds in context when initial question is false already?
  it should "exploit conditional equivalence from global facts propositionally nested with false" ignore withQE { _ =>
    val result = proveBy("b>0 ==> false & 2*x*b>=v*v".asSequent,
      transform("x>=v^2/(2*b)".asFormula)(1, 1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> false & x>=v^2/(2*b)".asSequent
  }

  it should "retain context in universal quantifier" in withQE { _ =>
    val result = proveBy("b>0 ==> \\forall x x>=0".asSequent,
      transform("y/b>0 & x*y>=0".asFormula)(1, 0::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> \\forall x (y/b>0 & x*y>=0)".asSequent
  }

  it should "retain context in existential quantifier" ignore withQE { _ =>
    val result = proveBy("b>0 ==> \\exists x x>=0".asSequent,
      transform("y/b>0 & x*y>=0".asFormula)(1, 0::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> \\exists x (y/b>0 & x*y>=0)".asSequent
  }

  it should "introduce new variables in results of DG" in withQE { _ =>
    val result = proveBy("x>0 -> \\exists y [{x'=-x,y'=1/2}]x>0".asFormula, implyR(1) & transform("x*y^2=1".asFormula)(1, 0::1::Nil))
    result.subgoals.loneElement shouldBe "x>0 ==> \\exists y [{x'=-x,y'=1/2}]x*y^2=1".asSequent
  }

  it should "retain context when introducing new variables in results of DG" ignore withQE { _ =>
    val result = proveBy("b>0 ==> \\exists y [{x'=2,y'=1}]x>=0".asSequent, transform("y/b>0 & x*y>=0".asFormula)(1, 0::1::Nil))
    result.subgoals.loneElement shouldBe "b>0 ==> \\exists y [{x'=2,y'=1}](y/b>0 & x*y>=0)".asSequent
  }

  it should "transform terms" in withQE { _ =>
    val result = proveBy("[x:=x/b+1+1+0;]x>0".asFormula, transform("x/b+2".asTerm)(1, 0::1::Nil))
    result.subgoals.loneElement shouldBe "==> [x:=x/b+2;]x>0".asSequent
  }

  //@todo missing feature
  it should "transform terms in ODEs" ignore withQE { _ =>
    val result = proveBy("x<0 -> [{x'=0*x+-5}]x<0".asFormula, transform("-5".asTerm)(1, 1::0::0::1::Nil))
    result.subgoals.loneElement shouldBe "==> x<0 -> [{x'=-5}]x<0".asSequent
  }

  "Edit" should "transform when special function abbrv is not used" in withQE { _ =>
    proveBy("x>=0".asFormula, edit("x>=1".asFormula)(1)).subgoals.loneElement shouldBe "==> x>=1".asSequent
  }

  it should "transform top-level with interpreted functions" in withQE { _ =>
    proveBy("x>5 ==> abs(x)>=0".asSequent, edit("x>=0".asFormula)(1)).subgoals.loneElement shouldBe "x>5 ==> x>=0".asSequent
    proveBy("x>5, y>2 ==> abs(x)+abs(y)+abs(x*y)>=0".asSequent, edit("x+y+x*y>=0".asFormula)(1)).subgoals.loneElement shouldBe "x>5, y>2 ==> x+y+x*y>=0".asSequent
  }

  it should "abbreviate" in withQE { _ =>
    proveBy("x>=2+3".asFormula, edit("x>=abbrv(2+3,y)".asFormula)(1)).subgoals.loneElement shouldBe "y=2+3 ==> x>=y".asSequent
    proveBy("2*g()*x=37".asFormula, edit("abbrv(2*g())*x=37".asFormula)(1)).subgoals.loneElement shouldBe "abbrv=2*g() ==> abbrv*x=37".asSequent
    proveBy("2*g()*x=37+4".asFormula, edit("abbrv(2*g())*x=abbrv(37+4)".asFormula)(1)).subgoals.loneElement shouldBe "abbrv=2*g(), abbrv_0=37+4 ==> abbrv*x=abbrv_0".asSequent
    proveBy("2*g()*x=37".asFormula, edit("abbrv(2*g(),foo)*x=37".asFormula)(1)).subgoals.loneElement shouldBe "foo=2*g() ==> foo*x=37".asSequent
    // does not unify
    //proveBy("2*g()*x=37".asFormula, edit("2*foo=37".asFormula)(1)).subgoals.loneElement shouldBe "foo=g()*x ==> 2*foo=37".asSequent
  }

  it should "only abbreviate if no transformations are present" in withQE { _ => withDatabase { db =>
    val (proofId, provable) = db.proveByWithProofId("x>=2+3", edit("x>=abbrv(2+3,y)".asFormula)(1))
    provable.subgoals.loneElement shouldBe "y=2+3 ==> x>=y".asSequent
    db.extractTactic(proofId) shouldBe BelleParser("""edit("x>=abbrv(2+3,y)",'R=="x>=2+3")""")
    db.extractStepDetails(proofId, "(1,0)") shouldBe BelleParser("""abbrv("2+3","y")""")
  }}

  it should "abbreviate and transform" in withQE { _ => withDatabase { db =>
    val (proofId, provable) = db.proveByWithProofId("2*g()*x=37+4", edit("abbrv(2*g())*x=41".asFormula)(1))
    provable.subgoals.loneElement shouldBe "abbrv=2*g() ==> abbrv*x=41".asSequent
    db.extractTactic(proofId) shouldBe BelleParser("""edit("abbrv(2*g())*x=41", 'R=="2*g()*x=37+4")""")
    db.extractStepDetails(proofId, "(1,0)") shouldBe BelleParser("""abbrv("2*g()","abbrv"); transform("41", 'R=="abbrv*x=#37+4#"); assert("abbrv*x=41", "Unexpected edit result", 'R=="abbrv*x=41")""")
  }}

  it should "expand abs" in withQE { _ =>
    proveBy("abs(x)>=0".asFormula, edit("expand(abs(x))>=1".asFormula)(1)).subgoals.loneElement shouldBe
      "x>=0&abs_=x | x<0&abs_=-x ==> abs_>=1".asSequent
  }

  it should "expand min" in withQE { _ =>
    proveBy("min(x,y)>=0".asFormula, edit("expand(min(x,y))>=1".asFormula)(1)).subgoals.loneElement shouldBe
      "x<=y&min_=x | x>y&min_=y ==> min_>=1".asSequent
  }

  it should "expand max" in withQE { _ =>
    proveBy("max(x,y)>=0".asFormula, edit("expand(max(x,y))>=1".asFormula)(1)).subgoals.loneElement shouldBe
      "x>=y&max_=x | x<y&max_=y ==> max_>=1".asSequent
  }

  it should "abbreviate and expand" in withQE { _ =>
    proveBy("max(x+5*2,y)>=0".asFormula, edit("expand(max(abbrv(x+5*2,z),y))>=1".asFormula)(1)).subgoals.loneElement shouldBe
      "z=x+5*2, z>=y&max_=z | z<y&max_=y ==> max_>=1".asSequent
  }

  it should "abbreviate and expand and transform" in withQE { _ => withDatabase { db =>
    val (proofId, provable) = db.proveByWithProofId("2*g()*abs(x)=37+4", edit("abbrv(2*g())*expand(abs(x))=41".asFormula)(1))
    provable.subgoals.loneElement shouldBe "abbrv=2*g(), x>=0&abs_=x | x<0&abs_=-x ==> abbrv*abs_=41".asSequent
    db.extractTactic(proofId) shouldBe BelleParser("""edit("abbrv(2*g())*expand(abs(x))=41", 'R=="2*g()*abs(x)=37+4")""")
    db.extractStepDetails(proofId, "(1,0)") shouldBe BelleParser("""abbrv("2*g()","abbrv") & absExp('R=="abbrv*#abs(x)#=37+4") & transform("41", 'R=="abbrv*abs_=#37+4#"); assert("abbrv*abs_=41", "Unexpected edit result", 'R=="abbrv*abs_=41")""")
  }}

  it should "abbreviate in programs" in withQE { _ =>
    proveBy("[x:=2+3;]x=5".asFormula, edit("[x:=abbrv(2+3,five);]x=5".asFormula)(1)).subgoals.loneElement shouldBe
      "five=2+3 ==> [x:=five;]x=5".asSequent
  }

  it should "expand multiple at once" in withQE { _ =>
    proveBy("abs(a)>0, abs(c)>3 ==> abs(a)>0 | abs(b)>1 | abs(c)>2".asSequent,
      edit("expand(abs(a))>0 | expand(abs(b))>1 | expand(abs(c))>2".asFormula)(1)).
      subgoals.loneElement shouldBe
      "abs_>0, abs__1>3, a>=0 & abs_=a | a<0 & abs_=-a, b>=0 & abs__0=b | b<0 & abs__0=-b, c>=0 & abs__1=c | c<0 & abs__1=-c ==> abs_>0 | abs__0>1 | abs__1>2".asSequent
  }

  it should "transform in programs" in withQE { _ =>
    val result = proveBy("x<0 -> [x:=x-1+0*z;]x<0".asFormula, edit("x<0 -> [x:=x-1;]x<0".asFormula)(1))
    result.subgoals.loneElement shouldBe "==> x<0 -> [x:=x-1;]x<0".asSequent
  }

  it should "transform postcondition of modal" in withQE { _ =>
    val result = proveBy("x<0 -> [x:=x-1;](x<0&v^2>=0)".asFormula, edit("x<0 -> [x:=x-1;]x<0".asFormula)(1))
    result.subgoals.loneElement shouldBe "==> x<0 -> [x:=x-1;]x<0".asSequent
  }

  "Use solver" should "switch to Z3" in withMathematica { _ =>
    def checkTool(name: String) = anon ((_: Sequent) => {
      ToolProvider.tools().head.name shouldBe name
      nil
    })
    proveBy("x>0 -> x>=0".asFormula,
      ToolTactics.switchSolver("Z3") & checkTool("Z3") & implyR(1) &
      ToolTactics.switchSolver("Mathematica") & checkTool("Mathematica") &
      ToolTactics.switchSolver("Mathematica") & checkTool("Mathematica") &
      master()) shouldBe 'proved
  }

  "Check for counterexample" should "not fail on uninterpreted predicates with _-suffixed names" in withMathematica { tool =>
    val s = "p__1(), x=2 ==> x>=1, q__0()".asSequent // as generated by 'using' notation
    proveBy(s, ToolTactics.assertNoCex).subgoals.loneElement shouldBe s
    a [BelleCEX] should be thrownBy proveBy("p__1(), x=2 ==> x=3, q__0()".asSequent, ToolTactics.assertNoCex)
  }
}
