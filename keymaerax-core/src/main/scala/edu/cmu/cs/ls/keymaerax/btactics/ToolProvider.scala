/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider.Configuration
import edu.cmu.cs.ls.keymaerax.core.QETool
import edu.cmu.cs.ls.keymaerax.tools._


/** Central repository providing access to arithmetic tools.
  * @note Never keep references to the tools, the tool provider may decide to shutdown/switch out tools and thereby
  *       render all tool references invalid.
  * @note Do especially not keep references in singletons, the tool provider will hand out nulls until properly
  *       initialized.
  * @author Stefan Mitsch
  * @see [[edu.cmu.cs.ls.keymaerax.tools]]
  * @see [[edu.cmu.cs.ls.keymaerax.tools.ToolInterface]]
  */
object ToolProvider extends ToolProvider {

  /** Configuration options for tools. */
  type Configuration = Map[String, String]

  /* @note mutable state for switching out default tool providers, which defaults to just returning None */
  private[this] var f: ToolProvider = new NoneToolProvider()

  /** Returns the current tool provider. */
  def provider: ToolProvider = f

  /**
    * Set a new tool provider to be used from now on.
    * @param provider the tool provider to use in KeYmaera X from now on.
    */
  def setProvider(provider: ToolProvider): Unit = {
    if (provider!=this) this.f = provider else throw new IllegalArgumentException("Provide a concrete tool provider, not this repository.")
  }

  // convenience methods forwarding to the current factory

  def qeTool(name: Option[String] = None): Option[QETool] = f.qeTool(name)

  def odeTool(): Option[ODESolverTool] = f.odeTool()

  def pdeTool(): Option[PDESolverTool] = f.pdeTool()

  def simplifierTool(): Option[SimplificationTool] = f.simplifierTool()

  def solverTool(): Option[EquationSolverTool] = f.solverTool()

  def algebraTool(): Option[AlgebraTool] = f.algebraTool()

  def cexTool(): Option[CounterExampleTool] = f.cexTool()

  def simulationTool(): Option[SimulationTool] = f.simulationTool()

  def shutdown(): Unit = f.shutdown()

  def tools(): List[Tool] = f.tools()

}

/** A tool factory creates various arithmetic and simulation tools.
  * @author Stefan Mitsch
  * @see [[edu.cmu.cs.ls.keymaerax.tools.ToolInterface]]
  */
trait ToolProvider {
  /** The provided tools. */
  def tools(): List[Tool]

  /** Returns a QE tool. */
  def qeTool(name: Option[String] = None): Option[QETool]

  /** Returns an ODE tool. */
  def odeTool(): Option[ODESolverTool]

  /** Returns a PDE tool. */
  def pdeTool(): Option[PDESolverTool]

  /** Returns an equation solver tool. */
  def solverTool(): Option[EquationSolverTool]

  /** Returns an algebra tool for algebraic computations. */
  def algebraTool(): Option[AlgebraTool]

  /** Returns an arithmetic/logical simplification tool */
  def simplifierTool(): Option[SimplificationTool]

  /** Returns a counterexample tool. */
  def cexTool(): Option[CounterExampleTool]

  /** Returns a simulation tool. */
  def simulationTool(): Option[SimulationTool]

  /** Shutdown the tools provided by this provider. After shutdown, the provider hands out None only. */
  def shutdown(): Unit
}

/** A tool provider that picks appropriate special tools from the list of preferences, i.e., if multiple tools with
  * the same trait appear in `toolPreferences`, the first will be picked for that trait.
  * @author Stefan Mitsch
  */
class PreferredToolProvider[T <: Tool](val toolPreferences: List[T]) extends ToolProvider {
  require(toolPreferences != null && toolPreferences.nonEmpty && toolPreferences.forall(_.isInitialized), "Initialized tool expected")

  private[this] lazy val qe: Option[Tool with QETool] = toolPreferences.find(_.isInstanceOf[QETool]).map(_.asInstanceOf[Tool with QETool])
  private[this] lazy val ode: Option[Tool with ODESolverTool] = toolPreferences.find(_.isInstanceOf[ODESolverTool]).map(_.asInstanceOf[Tool with ODESolverTool])
  private[this] lazy val pde: Option[Tool with PDESolverTool] = toolPreferences.find(_.isInstanceOf[PDESolverTool]).map(_.asInstanceOf[Tool with PDESolverTool])
  private[this] lazy val cex: Option[Tool with CounterExampleTool] = toolPreferences.find(_.isInstanceOf[CounterExampleTool]).map(_.asInstanceOf[Tool with CounterExampleTool])
  private[this] lazy val simplifier: Option[Tool with SimplificationTool] = toolPreferences.find(_.isInstanceOf[SimplificationTool]).map(_.asInstanceOf[Tool with SimplificationTool])
  private[this] lazy val simulator: Option[Tool with SimulationTool] = toolPreferences.find(_.isInstanceOf[SimulationTool]).map(_.asInstanceOf[Tool with SimulationTool])
  private[this] lazy val solver: Option[Tool with EquationSolverTool] = toolPreferences.find(_.isInstanceOf[EquationSolverTool]).map(_.asInstanceOf[Tool with EquationSolverTool])
  private[this] lazy val algebra: Option[Tool with AlgebraTool] = toolPreferences.find(_.isInstanceOf[AlgebraTool]).map(_.asInstanceOf[Tool with AlgebraTool])

  override def tools(): List[Tool] = toolPreferences
  override def qeTool(name: Option[String] = None): Option[QETool] = ensureInitialized[Tool with QETool](name match {
    case Some(qeToolName) => toolPreferences.find(t => t.isInstanceOf[QETool] && t.name == qeToolName).map(_.asInstanceOf[Tool with QETool])
    case None => qe
  })
  override def odeTool(): Option[ODESolverTool] = ensureInitialized(ode)
  override def pdeTool(): Option[PDESolverTool] = ensureInitialized(pde)
  override def cexTool(): Option[CounterExampleTool] = ensureInitialized(cex)
  override def simplifierTool(): Option[SimplificationTool] = ensureInitialized(simplifier)
  override def simulationTool(): Option[SimulationTool] = ensureInitialized(simulator)
  override def solverTool(): Option[EquationSolverTool] = ensureInitialized(solver)
  override def algebraTool(): Option[AlgebraTool] = ensureInitialized(algebra)
  override def shutdown(): Unit = toolPreferences.foreach(_.shutdown())

  /** Ensures that the tool `t` is initialized (= not yet shutdown) before returning it; returns None for uninitialized tools. */
  private def ensureInitialized[S <: Tool](tool: Option[S]): Option[S] = tool match {
    case Some(t) if t.isInitialized => tool
    case _ => None
  }
}

/** A tool provider without tools.
  * @author Stefan Mitsch
  */
class NoneToolProvider extends ToolProvider {
  override def tools(): List[Tool] = Nil
  override def qeTool(name: Option[String] = None): Option[QETool] = None
  override def odeTool(): Option[ODESolverTool] = None
  override def pdeTool(): Option[PDESolverTool] = None
  override def simplifierTool(): Option[SimplificationTool] = None
  override def cexTool(): Option[CounterExampleTool] = None
  override def simulationTool(): Option[SimulationTool] = None
  override def solverTool(): Option[EquationSolverTool] = None
  override def algebraTool(): Option[AlgebraTool] = None
  override def shutdown(): Unit = {}
}

/** A tool provider that provides Polya as a QE tools, everything else is None.
  * @author Stefan Mitsch
  */
class PolyaToolProvider extends PreferredToolProvider({ val p = new Polya; p.init(Map()); p :: Nil }) {
  def tool(): Polya = tools().head.asInstanceOf[Polya]
}

/** A tool provider that initializes tools to Mathematica.
  * @param config The Mathematica configuration (linkName, libDir).
  * @author Stefan Mitsch
  */
class MathematicaToolProvider(config: Configuration) extends PreferredToolProvider({ val m = new Mathematica(); m.init(config); m :: Nil }) {
  def tool(): Mathematica = tools().head.asInstanceOf[Mathematica]
}

/** A tool provider that provides Z3 as QE tool and KeYmaera's own bundled diff. solution tool, everything else is None.
  * @author Stefan Mitsch
  */
class Z3ToolProvider extends PreferredToolProvider({ val z = new Z3; z.init(Map()); val ode = new IntegratorODESolverTool; ode.init(Map()); z :: ode :: Nil }) {
  def tool(): Z3 = tools().head.asInstanceOf[Z3]
}

/** A tool provider that provides all Mathematica tools, but favors Z3 for QE unless specifically asked to provide Mathematica.
  * @author Stefan Mitsch
  */
class MathematicaZ3ToolProvider(config: Configuration) extends PreferredToolProvider(
  { val m = new Mathematica(); m.init(config); val z = new Z3; z.init(Map()); z :: m :: Nil }) { }