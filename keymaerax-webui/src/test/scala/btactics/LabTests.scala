/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon.{OnAll, TheType}
import edu.cmu.cs.ls.keymaerax.btactics.ConfigurableGenerate
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.DBAbstractionObj
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.io.Source
import scala.language.postfixOps

/**
  * Test that we can prove various homework labs from 15-424 Foundations of Cyber-Physical Systems.
  * Since we will like want to give students source code access at some point, this test loads files from
  * an arbitrary directory which can be outside the repository.
  *
  * These tests are expected to fail if the test files haven't been supplied.
  * Created by bbohrer on 1/14/16.
  */
@SlowTest
class LabTests extends TacticTestBase {
  val testDir = "keymaerax-webui/src/test/scala/btactics/labs/"

  def testLab(name:String):Unit =
    withMathematica {case mathematica =>
      val model = Source.fromFile(testDir + name).mkString
      var map = Map.empty[Expression, Formula]
      KeYmaeraXParser.setAnnotationListener({case (prog,fml) => map = map.+((prog,fml))})
      val fml = KeYmaeraXProblemParser(model)
      proveBy(fml, TactixLibrary.master(new ConfigurableGenerate[Formula](map)))
    }

  "Lab 1a" should "prove with master if file is present" in {
    testLab("lab1a.key")
  }

  "Lab 1b" should "prove with master if file is present" in {
    testLab("lab1b.key")
  }

  "Lab 1c" should "prove with master if file is present" in {
    testLab("lab1c.key")
  }

  "Lab 2a" should "prove with master if file is present" in {
    testLab("lab2a.key")
  }

  "Lab 2b" should "prove with master if file is present" in {
    testLab("lab2b.key")
  }
}
