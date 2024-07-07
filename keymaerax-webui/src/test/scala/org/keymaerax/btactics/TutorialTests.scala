/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.tags.{ExtremeTest, SlowTest}
import org.scalatest.Suites
import TutorialTests._

/**
 * All tutorial tests.
 *
 * Created by smitsch on 1/27/17.
 */
@SlowTest
class TutorialTests
    extends Suites(
      // Tutorials
      new TutorialRegressionTester("Implicit Definitions", "classpath:/examples/implicitdefinitions.kyx"),
      new TutorialRegressionTester("Basic", "classpath:/examples/tutorials/basic/basictutorial.kyx"),
      new TutorialRegressionTester("FM", "classpath:/examples/tutorials/fm/fm.kyx"),
      new TutorialRegressionTester("STTT", "classpath:/examples/tutorials/sttt/sttt.kyx"),
      new TutorialRegressionTester("CPSWeek", "classpath:/examples/tutorials/cpsweek/cpsweek.kyx"),
      new TutorialRegressionTester("DLDS", "classpath:/keymaerax-projects/dlds/dlds.kya"),
      new TutorialRegressionTester("POPL", "classpath:/keymaerax-projects/popltutorial/popltutorial.kyx"),
      new TutorialRegressionTester("LFCPS", s"$GITHUB_PROJECTS_RAW_PATH/lfcps/lfcps.kyx"),
      new TutorialRegressionTester("LFCPS Tutorial", s"$GITHUB_PROJECTS_RAW_PATH/lfcps-tutorial/lfcps-tutorial.kyx"),
      // keymaerax-projects
      new TutorialRegressionTester(
        "Bifurcations",
        s"$GITHUB_PROJECTS_RAW_PATH/bifurcations/saddle-nodes/1D/combined.kya",
      ),
      new TutorialRegressionTester("DLDS 1", s"$GITHUB_PROJECTS_RAW_PATH/dlds/dlds.kya"),
      new TutorialRegressionTester("DLDS 3", s"$GITHUB_PROJECTS_RAW_PATH/dlds/parachute.kya"),
      new TutorialRegressionTester("DLDS 4", s"$GITHUB_PROJECTS_RAW_PATH/dlds/parachute-transformed.kya"),
      new TutorialRegressionTester("Games 1", s"$GITHUB_PROJECTS_RAW_PATH/games/dual-filibuster.kya"),
      new TutorialRegressionTester("Games 2", s"$GITHUB_PROJECTS_RAW_PATH/games/games.kya"),
      new TutorialRegressionTester("Games 3", s"$GITHUB_PROJECTS_RAW_PATH/games/goalie.kya"),
      new TutorialRegressionTester("Games 4", s"$GITHUB_PROJECTS_RAW_PATH/games/pusharound-cart.kya"),
      new TutorialRegressionTester("Games 5", s"$GITHUB_PROJECTS_RAW_PATH/games/WALL-E-EVE.kyx"),
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
      new TutorialRegressionTester("LMPC", s"$GITHUB_PROJECTS_RAW_PATH/LMPC/LMPC.kyx"),
    )

@ExtremeTest
class CaseStudyTests
    extends Suites(
      new CaseStudyRegressionTester("ETCS", s"$GITHUB_PROJECTS_RAW_PATH/etcs/etcs.kyx"),
      new CaseStudyRegressionTester("Roundabout", s"$GITHUB_PROJECTS_RAW_PATH/roundabout/TRM-essentials.kya"),
      new CaseStudyRegressionTester("ACAS X", s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx.kyx"),
      new CaseStudyRegressionTester("RAL", s"$GITHUB_PROJECTS_RAW_PATH/ral/relative-full.kyx"),
      new CaseStudyRegressionTester("Robix", s"$GITHUB_PROJECTS_RAW_PATH/ijrr/robix.kyx"),
      // ACAS-X games
      new CaseStudyRegressionTester(
        "ACAS X Games Bounded-Time Non-Maneuvering",
        s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx-games/Bounded-Time Safety for a Non-Maneuvering Intruder.kyx",
      ),
      new CaseStudyRegressionTester(
        "ACAS X Games Bounded-Time Vertically-Maneuvering",
        s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx-games/Bounded-Time Safety for a Vertically-Maneuvering Intruder.kyx",
      ),
      new CaseStudyRegressionTester(
        "ACAS X Games Infinite-Time Horizontally-Maneuvering",
        s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx-games/Infinite-Time Safety for a Horizontally-Maneuvering Intruder.kyx",
      ),
      new CaseStudyRegressionTester(
        "ACAS X Games Infinite-Time Non-Maneuvering",
        s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx-games/Infinite-Time Safety for a Non-Maneuvering Intruder.kyx",
      ),
      new CaseStudyRegressionTester(
        "ACAS X Games Infinite-Time Vertically-Maneuvering",
        s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx-games/Infinite-Time Safety for a Vertically-Maneuvering Intruder.kyx",
      ),
      new CaseStudyRegressionTester(
        "ACAS X Games Safeability Non-Maneuvering",
        s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx-games/Safeability for a Non-Maneuvering Intruder with Upper Bound.kyx",
      ),
      new CaseStudyRegressionTester(
        "ACAS X Games Safeability Vertically-Maneuvering",
        s"$GITHUB_PROJECTS_RAW_PATH/acasx/acasx-games/Safeability for a Vertically-Maneuvering Intruder with Upper Bound.kyx",
      ),
    )

object TutorialTests {
  val GITHUB_PROJECTS_RAW_PATH: String = "https://raw.githubusercontent.com/LS-Lab/KeYmaeraX-projects/master"
  // for testing changes in a locally cloned repository
//  val GITHUB_PROJECTS_RAW_PATH: String = "classpath:/keymaerax-projects"
}
