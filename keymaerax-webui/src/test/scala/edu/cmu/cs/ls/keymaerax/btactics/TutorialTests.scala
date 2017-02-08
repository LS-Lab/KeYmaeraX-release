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
  new TutorialRegressionTester("CPSWeek", "classpath:/examples/tutorials/cpsweek/cpsweek.json")
)