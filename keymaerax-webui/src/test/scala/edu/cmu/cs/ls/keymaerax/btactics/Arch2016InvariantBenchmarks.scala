/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

/**
  * These are all translated by hand from the supplementary material of
  * "Benchmarks for Non-linear Continuous System Safety Verification"
  * http://verivital.com/hyst/benchmark-nonlinear/
  * @author Nathan Fulton
  */
@SlowTest
class Arch2016InvariantBenchmarks extends TacticTestBase {
  "ahmadi_parrilo_kristic" should "prove by ODE" in withMathematica(qeTool => {
    val system = "x'=-x+x*y, y'=-y, t'=1".asDifferentialProgram
    val initially = "0.5<=x & x<=0.7 & 0<=y & y<=0.3 & t=0".asFormula
    val forbidden = "-0.8>=x & x>=-1 & -0.7>=y & y>=-1".asFormula
    val timeHorizon = "t<=9".asFormula

    val f = Imply(initially, Box(ODESystem(system, timeHorizon), Not(forbidden)))
    val t = TactixLibrary.implyR(1) & DifferentialTactics.ODE(1)

    proveBy(f,t) shouldBe 'proved
  })

  "alongi_nelson_ex_4_1_9_page_143" should "prove by ODE" in withMathematica(qeTool => {
    val system = "x'=x*z , y'=y*z , z'=-x^2-y^2 , t'=1".asDifferentialProgram
    val constraint = "x^2+y^2+z^2=1".asFormula
    val initially = "x = 1 & y = 0 & z = 0 & t=0".asFormula
    val forbidden = "x > 1 | z > 0".asFormula
    val timeHorizon = 9

    val f = Imply(initially, Box(ODESystem(system, constraint), Not(forbidden)))
    val t = TactixLibrary.implyR(1) & DifferentialTactics.ODE(1)

    proveBy(f,t) shouldBe 'proved
  })

  "keymaera_nonlinear_diffcut" should "prove by ODE" in withMathematica(qetool => {
    val system = "x'=(-3+x)^4+y^5, y'=y^2, t'=1".asDifferentialProgram
    val timeHorizon = "t<=9".asFormula
    val initially = "x^3 >= -1 & y^5 >= 0 & t=0".asFormula
    val forbidden = "1 + x < 0 | y < 0".asFormula //`+x >= 0 & y>0

    val f = Imply(initially, Box(ODESystem(system, timeHorizon), Not(forbidden)))
    val t = TactixLibrary.implyR(1) & DifferentialTactics.ODE(1)


    proveBy(f,t) shouldBe 'proved
  })


}
