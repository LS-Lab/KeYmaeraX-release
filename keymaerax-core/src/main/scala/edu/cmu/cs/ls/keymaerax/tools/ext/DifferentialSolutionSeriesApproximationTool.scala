package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.core.{NamedSymbol, Number, ODESystem, Term, Variable}
import edu.cmu.cs.ls.keymaerax.tools.ToolInterface

trait DifferentialSolutionSeriesApproximationTool extends ToolInterface {
  /**
    *
    * @param odes The ODEs
    * @param ctx Context for any parameters in the ODEs.
    * @return upper and lower bound series approximations of each primed variable in the ODEs.
    */
  def seriesApproximation(odes: ODESystem, ctx: Map[Term, Term]): Option[Map[Variable, Term]]
}
