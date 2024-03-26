/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.OnAll
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger._
import edu.cmu.cs.ls.keymaerax.core.{Box, Formula}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tagobjects.IgnoreInBuildTest

/** Tests for the simple QE logger Only logs first order formulae */
class QELoggerTests extends TacticTestBase {

  "QE logger" should "log sequents and parse them back" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq =
      "w=-1|w=1, hp>0, rp>=0, rv>=0, a>0, maxI=max_0, 0>=w*(dhf-dhd)&max_0=0|0 < w*(dhf-dhd)&max_0=w*(dhf-dhd)\n  ==>  0<=0&0 < maxI/a&0=rv*0&0=w*a/2*0^2+dhd*0|0>=maxI/a&0=rv*0&0=dhf*0-w*maxI^2/(2*a)"
        .asSequent
    val seq2 =
      "w=-1|w=1, abs_2>rp|w*h < w*0-hp, hp>0, rp>=0, rv>=0, a>0, r>=0&abs_0=r|r < 0&abs_0=-r, h>=0&abs_1=h|h < 0&abs_1=-h, r-0>=0&abs_2=r-0|r-0 < 0&abs_2=-(r-0)\n  ==>  abs_0>rp|abs_1>hp"
        .asSequent
    clearLog()
    logSequent(seq, seq, "foo")
    logSequent(seq, seq, "bar")
    logSequent(seq, seq2, "bar")

    val ls = parseLog()
    println(ls)
    ls.keySet should contain only ("foo", "bar")
    ls("foo") should contain only ((seq, seq))
    ls("bar") should contain only ((seq, seq), (seq, seq2))
  }

  "QE logger" should "log QE calls" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val seq =
      "w=-1|w=1, hp>0, rp>=0, rv>=0, a>0, maxI=max_0, 0>=w*(dhf-dhd)&max_0=0|0 < w*(dhf-dhd)&max_0=w*(dhf-dhd)\n  ==>  0<=0&0 < maxI/a&0=rv*0&0=w*a/2*0^2+dhd*0|0>=maxI/a&0=rv*0&0=dhf*0-w*maxI^2/(2*a)"
        .asSequent

    clearLog()
    enableLogging()
    val pr = proveBy(seq, prop & OnAll(QE))
    disableLogging()
    val ls = parseLog()
    ls.keySet should contain only ("")
    ls("").length shouldBe 48
  }

  "QE logger" should "keep only records with required shape" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val ls = parseLog()
    for ((k, vs) <- ls) {
      println(k, vs.size)
      var ctr = 0
      for ((pr, seq) <- vs) {
        if (pr.succ.length > 0) {
          pr.succ(0) match {
            case Box(p, f) =>
              // println(p)
              // println(f)
              ctr += 1
            case _ => ()
          }
        }
      }
      println(ctr)
    }
  }

  "QE logger" should "log my lab 2" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val l2 = scala.io.Source.fromFile("L2Q2.kya").mkString // Avoid committing the solution to cse repo
    enableLogging((10, "L2"))
    // Note: logger must be enabled before calling the parser, or it will parse explicit QE calls to the wrong tactic!
    val archiveL2 :: Nil = ArchiveParser.parse(l2)

    val (l2f, l2t) = (archiveL2.model.asInstanceOf[Formula], archiveL2.tactics.head._3)

    println("Proving", l2f, l2t)
    println(proveBy(l2f, l2t))

  }

  "QE logger" should "log my lab 3" taggedAs IgnoreInBuildTest in withMathematica { qeTool =>
    val l3 = scala.io.Source.fromFile("L3Q6.kya").mkString // Avoid committing the solution to cse repo
    enableLogging((10, "L3"))
    // Note: logger must be enabled before calling the parser, or it will parse explicit QE calls to the wrong tactic!
    val archiveL3 :: Nil = ArchiveParser.parse(l3)

    val (l3f, l3t) = (archiveL3.model.asInstanceOf[Formula], archiveL3.tactics.head._3)

    println("Proving", l3f, l3t)
    proveBy(l3f, l3t)
  }
}
