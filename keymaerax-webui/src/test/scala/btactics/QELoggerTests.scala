package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Tests for the simple QE logger
  * Only logs first order formulae
  */
class QELoggerTests extends TacticTestBase {

  "QE logger" should "log sequents and parse them back" in withMathematica { qeTool =>
     val seq = "w=-1|w=1, hp>0, rp>=0, rv>=0, a>0, maxI=max_0, 0>=w*(dhf-dhd)&max_0=0|0 < w*(dhf-dhd)&max_0=w*(dhf-dhd)\n  ==>  0<=0&0 < maxI/a&0=rv*0&0=w*a/2*0^2+dhd*0|0>=maxI/a&0=rv*0&0=dhf*0-w*maxI^2/(2*a)".asSequent
    val seq2 = "w=-1|w=1, abs_2>rp|w*h < w*0-hp, hp>0, rp>=0, rv>=0, a>0, r>=0&abs_0=r|r < 0&abs_0=-r, h>=0&abs_1=h|h < 0&abs_1=-h, r-0>=0&abs_2=r-0|r-0 < 0&abs_2=-(r-0)\n  ==>  abs_0>rp|abs_1>hp".asSequent
    clearLog()
    logSequent(seq,seq,"foo")
    logSequent(seq,seq,"bar")
    logSequent(seq,seq2,"bar")

    val ls = parseLog()
    println(ls)
    ls.keySet should contain only ("foo","bar")
    ls("foo") should contain only ((seq,seq))
    ls("bar") should contain only ((seq,seq),(seq,seq2))
  }

  "QE logger" should "log QE calls" in withMathematica { qeTool =>
    val seq = "w=-1|w=1, hp>0, rp>=0, rv>=0, a>0, maxI=max_0, 0>=w*(dhf-dhd)&max_0=0|0 < w*(dhf-dhd)&max_0=w*(dhf-dhd)\n  ==>  0<=0&0 < maxI/a&0=rv*0&0=w*a/2*0^2+dhd*0|0>=maxI/a&0=rv*0&0=dhf*0-w*maxI^2/(2*a)".asSequent

    clearLog()
    enableLogging()
    val pr = proveBy(seq,prop & OnAll(QE))
    disableLogging()
    val ls = parseLog()
    ls.keySet should contain only  ("")
    ls("").length shouldBe 48
  }

  //Timing tests
  "QE logger" should "record time to re-prove the log with QE" in withMathematica { qeTool =>
    val ls = parseLog()
    for ((k,vs) <- ls) {
      println("Replaying QE calls for: "+k)
      var time = 0L
      for ((pr,seq) <- vs) {
        val t0 = System.nanoTime()
        proveBy(seq,QE) //TODO: kill after timeout
        val t1 = System.nanoTime()
        time+=t1-t0
      }
      println("Total time (s): "+time.toDouble/1000000000.0)
    }


  }

}
