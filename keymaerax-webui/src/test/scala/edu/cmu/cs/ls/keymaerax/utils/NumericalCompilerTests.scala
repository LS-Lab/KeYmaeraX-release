/*
 * *
 *   * Copyright (c) 2021 Carnegie Mellon University. CONFIDENTIAL
 *   * See LICENSE.txt for the conditions of this license.
 *
 *
 */

package edu.cmu.cs.ls.keymaerax.utils

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.parser.StringConverter.StringToStringConverter


/**
  *
  *
  * @author André Platzer
  */
class NumericalCompilerTests extends TacticTestBase {
  val integrator = new EulerIntegrationCompiler
  "Forward Euler Integration" should "work on x'=2" in {
    println(integrator("{x'=2}".asProgram))
  }

  it should "work on x'=x" in {
    println(integrator("{x'=x}".asProgram))
  }

  it should "work on x'=-x" in {
    println(integrator("{x'=-x}".asProgram))
  }

  it should "work on v'=w,w'=-v" in {
    println(integrator("{v'=w,w'=-v}".asProgram))
  }

  it should "work on v'=-w,w'=v" in {
    println(integrator("{v'=-w,w'=v}".asProgram))
  }

  it should "work on {x'=v,v'=a}" in {
    println(integrator("{x'=v,v'=a}".asProgram))
  }

  it should "work on {x'=v,v'=a,a'=j}" in {
    println(integrator("{x'=v,v'=a,a'=j}".asProgram))
  }

  it should "work on {x'=v,v'=a,a'=j&x>=0}" in {
    println(integrator("{x'=v,v'=a,a'=j&x>=0}".asProgram))
  }

  it should "work on {x'=v,v'=a,a'=j,j'=k}" in {
    println(integrator("{x'=v,v'=a,a'=j,j'=k}".asProgram))
  }

  it should "work on x'=2*x&x<=2" in {
    println(integrator("{x'=2*x&x<=2}".asProgram))
  }

  it should "work on {{a:=A;++a:=-b;}; {x'=v,v'=a}}*" in {
    println(integrator("{{a:=A;++a:=-b;}; {x'=v,v'=a}}*".asProgram))
  }

  it should "work on {{?SB(x,o);a:=A;++a:=-b;}; {x'=v,v'=a}}*" in {
    println(integrator("{{?SB(x,o);a:=A;++a:=-b;}; {x'=v,v'=a}}*".asProgram))
  }
}
