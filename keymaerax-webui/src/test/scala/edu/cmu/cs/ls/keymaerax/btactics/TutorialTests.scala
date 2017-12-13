/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import org.scalatest.Suites
import TutorialTests._

/**
  * All tutorial tests.
  * Created by smitsch on 1/27/17.
  */
@SlowTest
class TutorialTests extends Suites(
  // Tutorials
  new TutorialRegressionTester("Basic", "classpath:/examples/tutorials/basic/basic.json"),
  new TutorialRegressionTester("FM", "classpath:/examples/tutorials/fm/fm.kyx"),
  new TutorialRegressionTester("STTT", "classpath:/examples/tutorials/sttt/sttt.kyx"),
  new TutorialRegressionTester("CPSWeek", "classpath:/examples/tutorials/cpsweek/cpsweek.json"),
  // Course
  new TutorialRegressionTester("FCPS17-05", s"$COURSE17_PATH/05-dynax.kya"),
  new TutorialRegressionTester("FCPS17-07", s"$COURSE17_PATH/07-loops.kya"),
  new TutorialRegressionTester("FCPS17-08", s"$COURSE17_PATH/08-events.kya"),
  new TutorialRegressionTester("FCPS17-09", s"$COURSE17_PATH/09-time.kya"),
  new TutorialRegressionTester("FCPS17-10", s"$COURSE17_PATH/10-diffinv.kya"),
  new TutorialRegressionTester("FCPS17-11", s"$COURSE17_PATH/11-diffcut.kya"),
  new TutorialRegressionTester("FCPS17-12", s"$COURSE17_PATH/12-diffghost.kya"),
  new TutorialRegressionTester("FCPS17-18", s"$COURSE17_PATH/18-gameproofs.kya"),
  new TutorialRegressionTester("FCPS-R02", s"$COURSE17_PATH/recitation02.kya"),
  new TutorialRegressionTester("FCPS-R03", s"$COURSE17_PATH/recitation03.kya"),
  new TutorialRegressionTester("FCPS-R04", s"$COURSE17_PATH/recitation04.kya"),
  new TutorialRegressionTester("FCPS-R05", s"$COURSE17_PATH/recitation05.kya"),
  new TutorialRegressionTester("FCPS-R06", s"$COURSE17_PATH/recitation06.kya"),
  new TutorialRegressionTester("FCPS-R07", s"$COURSE17_PATH/recitation07.kya"),
  new TutorialRegressionTester("FCPS-R08", s"$COURSE17_PATH/recitation08.kya"),
  new TutorialRegressionTester("FCPS-R09", s"$COURSE17_PATH/recitation09.kya"),
  new TutorialRegressionTester("FCPS-R11", s"$COURSE17_PATH/recitation11.kya"),
  new TutorialRegressionTester("FCPS-R12", s"$COURSE17_PATH/recitation12.kya"),
  // keymaerax-projects
  new TutorialRegressionTester("Bifurcations", s"$GITHUB_PROJECTS_RAW_PATH/bifurcations/saddle-nodes/1D/combined.kya"),
  new TutorialRegressionTester("DLDS 1", s"$GITHUB_PROJECTS_RAW_PATH/dlds/dlds.kya"),
  new TutorialRegressionTester("DLDS 2", s"$GITHUB_PROJECTS_RAW_PATH/dlds/dlds-one.kya"),
  new TutorialRegressionTester("DLDS 3", s"$GITHUB_PROJECTS_RAW_PATH/dlds/parachute.kya"),
  new TutorialRegressionTester("DLDS 4", s"$GITHUB_PROJECTS_RAW_PATH/dlds/parachute-transformed.kya"),
  new TutorialRegressionTester("Games 1", s"$GITHUB_PROJECTS_RAW_PATH/games/dual-filibuster.kya"),
  new TutorialRegressionTester("Games 2", s"$GITHUB_PROJECTS_RAW_PATH/games/games.kya"),
  new TutorialRegressionTester("Games 3", s"$GITHUB_PROJECTS_RAW_PATH/games/goalie.kya"),
  new TutorialRegressionTester("Games 4", s"$GITHUB_PROJECTS_RAW_PATH/games/pusharound-cart.kya"),
  new TutorialRegressionTester("Games 5", s"$GITHUB_PROJECTS_RAW_PATH/games/WALL-E-EVE.kya"),
  new TutorialRegressionTester("Ghosts 1", s"$GITHUB_PROJECTS_RAW_PATH/ghosts_simple/example_1.kya"),
  new TutorialRegressionTester("Ghosts 2", s"$GITHUB_PROJECTS_RAW_PATH/ghosts_simple/example_2.kya"),
  new TutorialRegressionTester("Ghosts 3", s"$GITHUB_PROJECTS_RAW_PATH/ghosts_simple/example_3.kya"),
  new TutorialRegressionTester("Ghosts 4", s"$GITHUB_PROJECTS_RAW_PATH/ghosts_simple/example_4.kya"),
  new TutorialRegressionTester("ITP 1", s"$GITHUB_PROJECTS_RAW_PATH/itp17/skydiver.kya"),
  new TutorialRegressionTester("ITP 2", s"$GITHUB_PROJECTS_RAW_PATH/itp17/skydiver_abbrv.kya"),
  new TutorialRegressionTester("LICS 1", s"$GITHUB_PROJECTS_RAW_PATH/lics/bouncing-ball.kya"),
  new TutorialRegressionTester("LICS 2", s"$GITHUB_PROJECTS_RAW_PATH/lics/CurveBot.kya"),
  new TutorialRegressionTester("LICS 3", s"$GITHUB_PROJECTS_RAW_PATH/lics/damposc.kya"),
  new TutorialRegressionTester("LICS 4", s"$GITHUB_PROJECTS_RAW_PATH/lics/exp.kya"),
  new TutorialRegressionTester("LICS 5", s"$GITHUB_PROJECTS_RAW_PATH/lics/lics1-continuous-forward.kya"),
  new TutorialRegressionTester("LICS 6", s"$GITHUB_PROJECTS_RAW_PATH/lics/lics2-hybrid-forward.kya"),
  new TutorialRegressionTester("LICS 7", s"$GITHUB_PROJECTS_RAW_PATH/lics/lics4a-time-safe.kya"),
  new TutorialRegressionTester("LICS 8", s"$GITHUB_PROJECTS_RAW_PATH/lics/rotational.kya"),
  new TutorialRegressionTester("LMPC", s"$GITHUB_PROJECTS_RAW_PATH/LMPC/LMPC.kya"),
  new TutorialRegressionTester("Roundabout", s"$GITHUB_PROJECTS_RAW_PATH/roundabout/TRM-essentials.kya"),
  new TutorialRegressionTester("ACAS X", s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx.kyx"),
  new TutorialRegressionTester("Robix", s"$GITHUB_PROJECTS_RAW_PATH/ijrr/robix.kyx"),
  new TutorialRegressionTester("ETCS", s"$GITHUB_PROJECTS_RAW_PATH/etcs/etcs.kyx")
)

object TutorialTests {
  private val COURSE17_PATH = "http://symbolaris.com/course/fcps17"
  private val GITHUB_PROJECTS_RAW_PATH = "https://raw.githubusercontent.com/LS-Lab/KeYmaeraX-projects/master"
  // for testing changes in a locally cloned repository
//  private val COURSE17_PATH = "classpath:/course"
//  private val GITHUB_PROJECTS_RAW_PATH = "classpath:/keymaerax-projects"
}
