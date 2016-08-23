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
  def setProvider(provider: ToolProvider) = {
    if (provider!=this) this.f = provider else throw new IllegalArgumentException("Provide a concrete tool provider, not this repository.")
  }

  // convenience methods forwarding to the current factory

  def qeTool(): Option[QETool] = f.qeTool()

  def odeTool(): Option[DiffSolutionTool] = f.odeTool()

  def simplifierTool(): Option[SimplificationTool] = f.simplifierTool()

  def solverTool(): Option[SolutionTool] = f.solverTool()

  def cexTool(): Option[CounterExampleTool] = f.cexTool()

  def simulationTool(): Option[SimulationTool] = f.simulationTool()

  def shutdown(): Unit = f.shutdown()

  def tools(): List[Tool] = f.tools()

}

/** A tool factory creates various arithmetic and simulation tools.
  * @author Stefan Mitsch
  */
trait ToolProvider {
  /** The provided tools. */
  def tools(): List[Tool]

  /** Returns a QE tool. */
  def qeTool(): Option[QETool]

  /** Returns an ODE tool. */
  def odeTool(): Option[DiffSolutionTool]

  /** Returns an equation solver tool. */
  def solverTool(): Option[SolutionTool]

  /** Returns an arithmetic/logical simplification tool */
  def simplifierTool(): Option[SimplificationTool]

  /** Returns a counterexample tool. */
  def cexTool(): Option[CounterExampleTool]

  /** Returns a simulation tool. */
  def simulationTool(): Option[SimulationTool]

  /** Shutdown the tools provided by this provider. After shutdown, the provider hands out null only. */
  def shutdown(): Unit
}

/** A tool provider that points all tools to a single `tool`.
  * @author Stefan Mitsch
  */
class SingleToolProvider[T <: Tool](val tool: T) extends ToolProvider {
  require(tool != null && tool.isInitialized, "Initialized tool expected")
  private[this] var theTool: T = tool

  override def tools(): List[Tool] = theTool :: Nil
  override def qeTool(): Option[QETool] = theTool  match { case t: QETool => Some(t) case _ => None }
  override def odeTool(): Option[DiffSolutionTool] = theTool  match { case t: DiffSolutionTool => Some(t) case _ => None }
  override def cexTool(): Option[CounterExampleTool] = theTool  match { case t: CounterExampleTool => Some(t) case _ => None }
  override def simplifierTool(): Option[SimplificationTool] = theTool  match { case t: SimplificationTool => Some(t) case _ => None }
  override def simulationTool(): Option[SimulationTool] = theTool  match { case t: SimulationTool => Some(t) case _ => None }
  override def solverTool(): Option[SolutionTool] = theTool match { case t: SolutionTool => Some(t) case _ => None }
  override def shutdown(): Unit = {
    if (theTool != null) {
      theTool.shutdown()
      theTool = null.asInstanceOf[T]
    }
  }
}

/** A tool provider without tools.
  * @author Stefan Mitsch
  */
class NoneToolProvider extends ToolProvider {
  override def tools(): List[Tool] = Nil
  override def qeTool(): Option[QETool] = None
  override def odeTool(): Option[DiffSolutionTool] = None
  override def simplifierTool(): Option[SimplificationTool] = None
  override def cexTool(): Option[CounterExampleTool] = None
  override def simulationTool(): Option[SimulationTool] = None
  override def solverTool(): Option[SolutionTool] = None
  override def shutdown(): Unit = {}
}

/** A tool provider that provides Polya as a QE tools, everything else is None.
  * @author Stefan Mitsch
  */
class PolyaToolProvider extends SingleToolProvider({ val p = new Polya; p.init(Map()); p }) { }

/** A tool provider that initializes tools to Mathematica.
  * @param config The Mathematica configuration (linkName, libDir).
  * @author Stefan Mitsch
  */
class MathematicaToolProvider(config: Configuration) extends SingleToolProvider({ val m = new Mathematica(); m.init(config); m }) { }

/** A tool provider that provides Z3 as QE tool, everything else is None.
  * @author Stefan Mitsch
  */
class Z3ToolProvider extends SingleToolProvider({ val z = new Z3; z.init(Map()); z }) { }
