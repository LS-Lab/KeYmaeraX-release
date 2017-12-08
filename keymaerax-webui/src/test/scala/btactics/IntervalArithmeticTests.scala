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

}
