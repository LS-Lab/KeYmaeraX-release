package btactics


import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import edu.cmu.cs.ls.keymaerax.btactics.IntervalArithmetic._

/**
  * Created by yongkiat on 9/8/16.
  */
class IntervalArithmeticTests extends TacticTestBase  {


  "interval arithmetic" should "intervalify x+y+z<=5" in withMathematica { qeTool =>
    val fml = "x+y+z<=5".asFormula
    proveBy(fml, splitGreaterEqual(1) & intervalify(1))
  }

  "interval arithmetic" should "intervalify robix fragment" in withMathematica { qeTool =>
    val fml = ("dxopost()^2+dyopost()^2<=V^2&(0<=ep&v>=0)&(((((((((xopost()=xo&yopost()=yo)&xpost()=x)&ypost()=y)&" +
      "dxpost()=dx)&dypost()=dy)&vpost()=v)&wpost()=w)&apost()=-B)&kpost()=k)").asFormula
    println(proveBy(fml, splitGreaterEqual(1) & intervalify(1)))
  }

}
