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
    val (prog, pff) = isarSyntax(fml)
    println(pff)
    println(prettyProg(prog))
    pff shouldBe 'proved
  }

  "isabelle syntax" should "derive repeated addition bounds" in withMathematica { qeTool =>
    val fml = "(x+y)+z+((x+y)+z+5) <= a+b".asFormula
    val (prog, pff) = isarSyntax(fml)
    println(pff)
    println(prettyProg(prog))
    pff shouldBe 'proved
  }

  "isabelle syntax" should "derive lower bounds for different forms of squares" in withMathematica { qeTool =>
    val fml = "x^2<=xopost()^2 & (a+b)^2 <= c^2 | (a+b)^2 <= (c+d)^2".asFormula
    val (prog, pff) = isarSyntax(fml)
    println(pff)
    println(prettyProg(prog))
    pff shouldBe 'proved
  }

  "isabelle syntax" should "derive ETCS essentials" in withMathematica { qeTool =>
    val uf = "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((vpost()=v&zpost()=z)&tpost()=0)&apost()=-b| m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((vpost()=v&zpost()=z)&tpost()=0)&apost()=A".asFormula
    val (prog, pff) = isarSyntax(uf)
    println(pff)
    println(prettyProg(prog))
    pff shouldBe 'proved
  }

  "isabelle syntax" should "derive ETCS safety lemma" in withMathematica { qeTool =>
    val uf = "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&(((((vpost()=v&empost()=em)&dopost()=d)&zpost()=z)&tpost()=t)&mopost()=m)&apost()=a|((((((((vdespost()=vdes&vpost()=v)&empost()=1)&dopost()=do)&zpost()=z)&tpost()=t)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)".asFormula
    val (f,pf) = normalise(uf)
    val (prog,pff) = deriveFormulaProof(f)
    println(prettyProg(prog))
    println(pff)
    pf shouldBe 'proved
    pff shouldBe 'proved
  }

  "isabelle syntax" should "stopsign control monitor" in withMathematica { qeTool =>
    val uf = "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((xpost()=x&vpost()=v)&apost()=A)&tpost()=0|v=0&0<=ep&((xpost()=x&vpost()=0)&apost()=0)&tpost()=0|(v>=0&0<=ep)&((xpost()=x&vpost()=v)&apost()=-b)&tpost()=0".asFormula
    val (prog, pff) = isarSyntax(uf)
    println(pff)
    println(prettyProg(prog))
    pff shouldBe 'proved
  }

  "isabelle syntax" should "stopsign with direct v control control monitor" in withMathematica { qeTool =>
    val uf = "S-x>=ep*vpost()&0<=ep&xpost()=x&tpost()=0|0<=ep&(xpost()=x&vpost()=0)&tpost()=0".asFormula
    val (prog, pff) = isarSyntax(uf)
    println(pff)
    println(prettyProg(prog))
    pff shouldBe 'proved
  }

  "isabelle syntax" should "stopsign model monitor" in withMathematica { qeTool =>
    val uf = "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((ep=0&0=tpost())&((A=0&apost()=0)&((v=0&vpost()=0)&x=xpost()|(v=vpost()&x=xpost())&v>0)|(A=apost()&A>0)&((v=0&vpost()=0)&xpost()=x|(v=vpost()&xpost()=x)&v>0))|ep>0&(((A=0&apost()=0)&((v=0&vpost()=0)&x=xpost()|(v=vpost()&xpost()=tpost()*v+x)&v>0))&((ep=tpost()|0=tpost())|0 < tpost()&tpost() < ep)|(A=apost()&A>0)&(((v=0&vpost()=A*tpost())&xpost()=1/2*A*(-1*tpost())^2+x|(vpost()=A*tpost()+v&xpost()=1/2*A*(-1*tpost())^2+tpost()*v+x)&v>0)&(ep=tpost()|0 < tpost()&tpost() < ep)|0=tpost()&((v=0&vpost()=0)&xpost()=x|(vpost()=v&xpost()=x)&v>0))))|v=0&(((0<=tpost()&ep>=tpost())&xpost()=x)&0=vpost())&apost()=0|((ep=0&0=tpost())&apost()+b=0)&((v=0&vpost()=0)&xpost()=x|(vpost()=v&xpost()=x)&v>0)|(ep>0&apost()+b=0)&(((v=b*tpost()+vpost()&b*(-1*tpost())^2+2*(-1*tpost()*v+-1*x+xpost())=0)&v>0)&((ep=tpost()&b<=ep^-1*v|0=tpost())|(tpost() < ep&0 < tpost())&b*tpost()<=v)|((0=tpost()&v=0)&vpost()=0)&2*xpost()=2*x)".asFormula
    val (f, pf) = normalise(uf)
    val (prog, pff) = deriveFormulaProof(f)
    println(prettyProg(prog))
    pf shouldBe 'proved
    pff shouldBe 'proved
  }

  "isabelle syntax" should "stopsign with direct v control model monitor" in withMathematica { qeTool =>
    val uf = "S-x>=ep*vpost()&(0<=tpost()&ep>=tpost())&xpost()=tpost()*vpost()+x|((0<=tpost()&ep>=tpost())&x=xpost())&vpost()=0".asFormula
    val (prog, pff) = isarSyntax(uf)
    println(pff)
    println(prettyProg(prog))
    pff shouldBe 'proved
  }

  "isabelle syntax" should "stopsign with direct v control model monitor with disturbance" in withMathematica { qeTool =>
    val uf = "S-x>=ep*(v+cpost()+D)&(-D<=dpost()&dpost()<=D)&((0<=tpost()&ep>=tpost())&-1*tpost()*(cpost()+dpost()+v)+xpost()=x)&v=vpost()|((((0<=tpost()&ep>=tpost())&x=xpost())&vpost()=0)&dpost()=0)&cpost()=0".asFormula
    val (prog, pff) = isarSyntax(uf)
    println(pff)
    println(prettyProg(prog))
    pff shouldBe 'proved
  }

  "isabelle syntax" should "common subformula eliminate" in withMathematica { qeTool =>
    val uf = "(P() & Q() & R() & A() | P() & A() & R() ) | A() & R()".asFormula
    println(commonFormulaProof(uf))
  }
}
