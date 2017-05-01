package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger._
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Box}
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

  "QE logger" should "keep only records with required shape" in withMathematica { qeTool =>
    val ls = parseLog()
    for ((k,vs) <- ls) {
      println(k,vs.size)
      var ctr = 0
      for ((pr,seq) <- vs) {
        if (pr.succ.length>0){
          pr.succ(0) match {
            case Box(p,f) =>
              //println(p)
              //println(f)
              ctr+=1
            case _ => ()
          }
        }
      }
      println(ctr)
    }
  }

  "QE logger" should "analyse dependencies for some examples" in withMathematica { qeTool =>
    val Some((n,pr,seq)) = parseStr("@ETCS#v_0()=v, z_0()=z, kyxtime_0()=kyxtime, v>=0&v=(-b())*(kyxtime-kyxtime_0())+v_0()\n  ==>  [{z'=v,v'=-b(),kyxtime'=1&v>=0&v=(-b())*(kyxtime-kyxtime_0())+v_0()}](z=(-b())/2*(kyxtime-kyxtime_0())^2+v_0()*(kyxtime-kyxtime_0())+z_0())'#v_0()=v, z_0()=z, kyxtime_0()=kyxtime, v>=0&v=(-b())*(kyxtime-kyxtime_0())+v_0()\n  ==>  \\forall kyxtime \\forall v (v>=0&v=(-b())*(kyxtime-kyxtime_0())+v_0()->v=(-b())/2*(2*(kyxtime-kyxtime_0())^(2-1)*(1-0))+v_0()*(1-0)+0)")
    val adjls = (pr.succ(0) match {
      case Box(a,f) =>
        DependencyAnalysis.analyseModal(a,seq)
    }).mapValues( v => v._1)
    val scc = DependencyAnalysis.scc(adjls)

    scc shouldBe List(Set("v".asVariable, "kyxtime".asVariable), Set("z".asVariable))
  }

  //Timing tests
//  "QE logger" should "record time to re-prove the log with QE" in withMathematica { qeTool =>
//    val ls = parseLog()
//    for ((k,vs) <- ls) {
//      println("Replaying QE calls for: "+k)
//      var time = 0L
//      for ((pr,seq) <- vs) {
//        val t0 = System.nanoTime()
//        proveBy(seq,QE) //TODO: kill after timeout
//        val t1 = System.nanoTime()
//        time+=t1-t0
//      }
//      println("Total time (s): "+time.toDouble/1000000000.0)
//    }
//  }


}
