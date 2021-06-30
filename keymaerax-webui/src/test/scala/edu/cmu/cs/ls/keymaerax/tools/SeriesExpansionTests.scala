package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core.{NamedSymbol, Number, ODESystem, Term}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import smtlib.theories.Core.True

class SeriesExpansionTests extends TacticTestBase {
  "series expansion tool" should "work for a simple system" in withMathematica(tool => {
    val odes = ODESystem("{x'=y, y'=-a*x}".asDifferentialProgram, "true".asFormula)
    val ctx: Map[Term, Term] = Map({"a".asVariable -> Number(5)})
    val result = tool.seriesApproximation(odes, ctx)
    println(result)
  })

  it should "return some result when there's no relevant context." in withMathematica(tool => {
    val odes = ODESystem("{x'=y, y'=-x}".asDifferentialProgram, "true".asFormula)
    val ctx: Map[Term, Term] = Map()
    val result = tool.seriesApproximation(odes, ctx)
    println(result)
  })

  it should "return the correct result for x'=1" in withMathematica(tool => {
    val odes = ODESystem("x'=1".asDifferentialProgram, "true".asFormula)
    val ctx: Map[Term, Term] = Map()
    val result = tool.seriesApproximation(odes, ctx)

    result.get("x".asVariable) shouldBe "t + old(x)".asTerm
  })

}
