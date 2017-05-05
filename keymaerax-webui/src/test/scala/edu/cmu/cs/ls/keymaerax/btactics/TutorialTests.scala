/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import org.scalatest.Suites

/**
  * All tutorial tests.
  * Created by smitsch on 1/27/17.
  */
@SlowTest
class TutorialTests extends Suites(
  new TutorialRegressionTester("Basic", "classpath:/examples/tutorials/basic/basic.json"),
  new TutorialRegressionTester("FM", "classpath:/examples/tutorials/fm/fm.json"),
  new TutorialRegressionTester("STTT", "classpath:/examples/tutorials/sttt/sttt.json"),
  new TutorialRegressionTester("CPSWeek", "classpath:/examples/tutorials/cpsweek/cpsweek.json"),
  new TutorialRegressionTester("FCPS17-05", "http://symbolaris.com/course/fcps17/05-dynax.kya"),
  new TutorialRegressionTester("FCPS17-07", "http://symbolaris.com/course/fcps17/07-loops.kya"),
  new TutorialRegressionTester("FCPS17-08", "http://symbolaris.com/course/fcps17/08-events.kya"),
  new TutorialRegressionTester("FCPS17-09", "http://symbolaris.com/course/fcps17/09-time.kya"),
  new TutorialRegressionTester("FCPS17-10", "http://symbolaris.com/course/fcps17/10-diffinv.kya"),
  new TutorialRegressionTester("FCPS17-11", "http://symbolaris.com/course/fcps17/11-diffcut.kya"),
  new TutorialRegressionTester("FCPS17-12", "http://symbolaris.com/course/fcps17/12-diffghost.kya"),
  new TutorialRegressionTester("FCPS17-18", "http://symbolaris.com/course/fcps17/18-gameproofs.kya"),
  new TutorialRegressionTester("FCPS-R02", "http://symbolaris.com/course/fcps17/recitation02.kya"),
  new TutorialRegressionTester("FCPS-R03", "http://symbolaris.com/course/fcps17/recitation03.kya"),
  new TutorialRegressionTester("FCPS-R04", "http://symbolaris.com/course/fcps17/recitation04.kya"),
  new TutorialRegressionTester("FCPS-R05", "http://symbolaris.com/course/fcps17/recitation05.kya"),
  new TutorialRegressionTester("FCPS-R06", "http://symbolaris.com/course/fcps17/recitation06.kya"),
  new TutorialRegressionTester("FCPS-R07", "http://symbolaris.com/course/fcps17/recitation07.kya"),
  new TutorialRegressionTester("FCPS-R08", "http://symbolaris.com/course/fcps17/recitation08.kya"),
  new TutorialRegressionTester("FCPS-R09", "http://symbolaris.com/course/fcps17/recitation09.kya"),
  new TutorialRegressionTester("FCPS-R11", "http://symbolaris.com/course/fcps17/recitation11.kya"),
  new TutorialRegressionTester("FCPS-R12", "http://symbolaris.com/course/fcps17/recitation12.kya")
)
