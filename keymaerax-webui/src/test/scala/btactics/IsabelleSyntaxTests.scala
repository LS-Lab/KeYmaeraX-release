package btactics

import edu.cmu.cs.ls.keymaerax.btactics.IsabelleSyntax._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Created by yongkiat on 9/8/16.
  */
class IsabelleSyntaxTests extends TacticTestBase  {

  "isabelle syntax" should "re-write formulas into accepted subset" in withMathematica { qeTool =>
    val fml = "a+b <= c -> !(c>b) | a > 0 & a+5 >= 0 <-> (c = 0 -> b >= 5 & c <= 5)".asFormula
    val (f,pf) = normalise(fml)
    pf shouldBe 'proved
    f shouldBe "(a+b<=c&b < c&(a<=0|a+5 < 0)|c!=0|5<=b&c<=5)&(c=0&(b < 5|5 < c)|c < a+b|c<=b|0 < a&0<=a+5)".asFormula
  }

  "isabelle syntax" should "re-write terms into accepted subset" in withMathematica { qeTool =>
    val fml = "a-(a+b) <= a*(b-c-d)^2 & (a-b-c)!=0 | (b-(c-d))=0".asFormula
    val (f,pf) = normalise(fml)
    pf shouldBe 'proved
    f shouldBe "a+-(a+b)<=a*((b+-c+-d)*(b+-c+-d))&(0 < a+-b+-c|a+-b+-c < 0)|b+-(c+-d)=0".asFormula
  }

  "isabelle syntax" should "re-write terms under special functions" in withMathematica { qeTool =>
    val fml = "max(min(a+b,(c-d)^2+(a-b)^2),c-d) <= abs(f()-g(a-d,b-a,c-d,c-d))".asFormula
    val (f,pf) = normalise(fml)
    pf shouldBe 'proved
    //Note that the right tuple rewrite under g fails because it doesn't recurse into pairs
    f shouldBe "max((min((a+b,(c+-d)*(c+-d)+(a+-b)*(a+-b))),c+-d))<=abs(f()+-g((a+-d,(b-a,(c-d,c-d)))))".asFormula
  }

  "isabelle syntax" should "derive negation bounds" in withMathematica { qeTool =>
    val fml = "a-(x*z+y) > b-(y*z+x)".asFormula
    val (f,pf) = normalise(fml)
    val (prog,pff) = deriveFormulaProof(f)
    pf shouldBe 'proved
    pff shouldBe 'proved
    println(pff)
    println(prettyProg(prog))
  }

  "isabelle syntax" should "derive repeated addition bounds" in withMathematica { qeTool =>
    val fml = "(x+y)+z+((x+y)+z+5) <= a+b".asFormula
    val (prog,pf) = deriveFormulaProof(fml)
    pf shouldBe 'proved
    println(pf)
    println(prettyProg(prog))
  }

  "isabelle syntax" should "derive lower bounds for different forms of squares" in withMathematica { qeTool =>
    val fml = "x^2<=xopost()^2 & (a+b)^2 <= c^2 | (a+b)^2 <= (c+d)^2".asFormula
    val (f,pf) = normalise(fml)
    val (prog,pff) = deriveFormulaProof(f)
    pf shouldBe 'proved
    pff shouldBe 'proved
    println(pff)
    println(prettyProg(prog))
  }

  "isabelle syntax" should "derive ETCS essentials" in withMathematica { qeTool =>
    val uf = "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((vpost()=v&zpost()=z)&tpost()=0)&apost()=-b| m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((vpost()=v&zpost()=z)&tpost()=0)&apost()=A".asFormula
    val (f,pf) = normalise(uf)
    val (prog,pff) = deriveFormulaProof(f)
    println(prettyProg(prog))
    pf shouldBe 'proved
    pff shouldBe 'proved
  }

  "isabelle syntax" should "derive ETCS safety lemma" in withMathematica { qeTool =>
    val uf = "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&(((((vpost()=v&empost()=em)&dopost()=d)&zpost()=z)&tpost()=t)&mopost()=m)&apost()=a|((((((((vdespost()=vdes&vpost()=v)&empost()=1)&dopost()=do)&zpost()=z)&tpost()=t)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)".asFormula
    val (f,pf) = normalise(uf)
    val (prog,pff) = deriveFormulaProof(f)
    println(prettyProg(prog))
    pf shouldBe 'proved
    pff shouldBe 'proved
  }

}
