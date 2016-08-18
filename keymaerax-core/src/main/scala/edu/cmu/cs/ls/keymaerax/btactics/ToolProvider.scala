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
object ToolProvider {

  /** Configuration options for tools. */
  type Configuration = Map[String, String]

  /* @note mutable state for switching out default tool providers, which defaults to just returning null */
  private[this] var f: ToolProvider = new NullToolProvider()

  /** Returns the current tool provider. */
  def provider: ToolProvider = f

  /**
    * Set a new tool provider to be used from now on.
    * @param provider the tool provider to use in KeYmaera X from now on.
    */
  def setProvider(provider: ToolProvider) = {f = provider}

  // convenience methods forwarding to the current factory

  /** Returns a quantifier elimination tool for real arithmetic. */
  def qeTool(): QETool = f.qeTool()

  /** Returns a differential equation solving helper tool. */
  def odeTool(): DiffSolutionTool = f.odeTool()

  /** Returns a counterexample finding helper tool. */
  def cexTool(): CounterExampleTool = f.cexTool()

  /** Returns a simulation helper tool. */
  def simulationTool(): SimulationTool = f.simulationTool()

  /** Shutdown the tools provided by the current provider. After shutdown, the provider hands out null only. */
  def shutdown(): Unit = f.shutdown()

}

/** A tool factory creates various tools.
  * @author Stefan Mitsch
  */
trait ToolProvider {
  /** The provided tools. */
  def tools(): List[Tool]

  /** Returns a QE tool. */
  def qeTool(): QETool

  /** Returns an ODE tool. */
  def odeTool(): DiffSolutionTool

  /** Returns a counterexample tool. */
  def cexTool(): CounterExampleTool

  /** Returns a simulation tool. */
  def simulationTool(): SimulationTool

  /** Shutdown the tools provided by this provider. After shutdown, the provider hands out null only. */
  def shutdown(): Unit
}

/** A tool provider that points all tools to the specified `tool`
  * @author Stefan Mitsch
  */
class SingleToolProvider[T <: Tool](val tool: T) extends ToolProvider {
  require(tool != null && tool.isInitialized, "Initialized tool expected")
  private[this] var theTool: T = tool

  override def tools(): List[Tool] = theTool :: Nil
  override def qeTool(): QETool = theTool  match { case t: QETool => t case _ => null }
  override def odeTool(): DiffSolutionTool = theTool  match { case t: DiffSolutionTool => t case _ => null }
  override def cexTool(): CounterExampleTool = theTool  match { case t: CounterExampleTool => t case _ => null }
  override def simulationTool(): SimulationTool = theTool  match { case t: SimulationTool => t case _ => null }
  override def shutdown(): Unit = {
    if (theTool != null) {
      theTool.shutdown()
      theTool = null.asInstanceOf[T]
    }
  }
}

/** A tool provider that initializes tools to null.
  * @author Stefan Mitsch
  */
class NullToolProvider extends ToolProvider {
  override def tools(): List[Tool] = Nil
  override def qeTool(): QETool = null
  override def odeTool(): DiffSolutionTool = null
  override def cexTool(): CounterExampleTool = null
  override def simulationTool(): SimulationTool = null
  override def shutdown(): Unit = {}
}

/** A tool provider that initializes QE tools to Polya, everything else to null.
  * @author Stefan Mitsch
  */
class PolyaToolProvider extends SingleToolProvider({ val p = new Polya; p.init(Map()); p }) { }

/** A tool provider that initializes tools to Mathematica.
  * @param config
  * @author Stefan Mitsch
  */
class MathematicaToolProvider(config: Configuration) extends SingleToolProvider({ val m = new Mathematica(); m.init(config); m }) { }

/** A tool provider that initializes QE tools to Z3, everything else to null.
  * @author Stefan Mitsch
  */
class Z3ToolProvider extends SingleToolProvider({ val z = new Z3; z.init(Map()); z }) { }
