package btactics


import edu.cmu.cs.ls.keymaerax.bellerophon.{PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.IntervalArithmetic._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

import scala.collection.immutable.Nil

/**
  * Created by yongkiat on 9/8/16.
  */
class IntervalArithmeticTests extends TacticTestBase  {

  "interval arithmetic" should "re-write formulas into accepted subset" in withMathematica { qeTool =>
    val fml = "a+b <= c -> !(c>b) | a > 0 & a+5 >= 0 <-> (c = 0 -> b >= 5 & c <= 5)".asFormula
    val (f,pf) = normalise(fml)
    pf shouldBe 'proved
    f shouldBe "(a+b<=c&b < c&(a<=0|a+5 < 0)|c!=0|5<=b&c<=5)&(c=0&(b < 5|5 < c)|c < a+b|c<=b|0 < a&0<=a+5)".asFormula
  }

  "interval arithmetic" should "re-write terms into accepted subset" in withMathematica { qeTool =>
    val fml = "a-(a+b) <= a*(b-c-d)^2 & (a-b-c)<0 | (b-c-d)>0".asFormula
    val (f,pf) = normalise(fml)
    pf shouldBe 'proved
    f shouldBe "a+-(a+b)<=a*(b+-c+-d)^2&a+-b+-c < 0|0 < b+-c+-d".asFormula
  }

  "interval arithmetic" should "derive negation bounds" in withMathematica { qeTool =>
    val fml = "a-(x*z+y) > b-(y*z+x)".asFormula
    val (f,pf) = normalise(fml)
    val (prog,pff) = deriveFormulaProof(f)
    pf shouldBe 'proved
    pff shouldBe 'proved
    println(pff)
    println(prettyProg(prog))
  }

  "interval arithmetic" should "derive repeated addition bounds" in withMathematica { qeTool =>
    val fml = "(x+y)+z+((x+y)+z+5) <= a+b".asFormula
    val (prog,pf) = deriveFormulaProof(fml)
    println(pf)
    println(prettyProg(prog))
  }

  "interval arithmetic" should "derive lower bounds for different forms of squares" in withMathematica { qeTool =>
    val fml = "x^2<=xopost()^2 & (a+b)^2 <= c^2 | (a+b)^2 <= (c+d)^2".asFormula
    val (prog,pf) = deriveFormulaProof(fml)
    println(pf)
    println(prettyProg(prog))
  }

  "interval arithmetic" should "derive unchecked bounds for simple divisor" in withMathematica { qeTool =>
    val fml = "a/b <= c/d".asFormula
    val (prog,pf) = deriveFormulaProof(fml)
    println(pf)
    println(prettyProg(prog))
  }

  "interval arithmetic" should "derive checked bounds for complex divisor" in withMathematica { qeTool =>
    val fml = "(x+y)/(a+b) <= (a+b)/(x+y)".asFormula
    val (prog,pf) = deriveFormulaProof(fml)
    println(pf)
    println(prettyProg(prog))
  }

  "interval arithmetic" should "fast multiplication on known variables" in withMathematica { qeTool =>
    val fml = "a*b*c <= a*b".asFormula
    val (prog,pf) = deriveFormulaProof(fml)
    println(pf)
    println(prettyProg(prog))
  }

  "interval arithmetic" should "derive ETCS essentials" in withMathematica { qeTool =>
    val uf = "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((vpost()=v&zpost()=z)&tpost()=0)&apost()=-b| m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((vpost()=v&zpost()=z)&tpost()=0)&apost()=A".asFormula
    val (f,pf) = normalise(uf)
    val (prog,pff) = deriveFormulaProof(f)
    println(prettyProg(prog))
    pf shouldBe 'proved
    pff shouldBe 'proved
  }

  "interval arithmetic" should "derive ETCS safety lemma" in withMathematica { qeTool =>
    val uf = "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&(((((vpost()=v&empost()=em)&dopost()=d)&zpost()=z)&tpost()=t)&mopost()=m)&apost()=a|((((((((vdespost()=vdes&vpost()=v)&empost()=1)&dopost()=do)&zpost()=z)&tpost()=t)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)".asFormula
    val (f,pf) = normalise(uf)
    val (prog,pff) = deriveFormulaProof(f)
    println(prettyProg(prog))
    pf shouldBe 'proved
    pff shouldBe 'proved
  }
}
