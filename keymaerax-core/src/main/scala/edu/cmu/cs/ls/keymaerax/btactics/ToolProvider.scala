/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.ToolProvider.Configuration
import edu.cmu.cs.ls.keymaerax.core.QETool
import edu.cmu.cs.ls.keymaerax.tools._
import org.apache.logging.log4j.scala.Logging


/** Central repository providing access to arithmetic tools.
  * @note Never keep references to the tools, the tool provider may decide to shutdown/switch out tools and thereby
  *       render all tool references invalid.
  * @note Do especially not keep references in singletons, the tool provider will hand out nulls until properly
  *       initialized.
  * @author Stefan Mitsch
  * @see [[edu.cmu.cs.ls.keymaerax.tools]]
  * @see [[edu.cmu.cs.ls.keymaerax.tools.ToolInterface]]
  */
object ToolProvider extends ToolProvider with Logging {

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
    if (provider != this) {
      if (provider != f) f.shutdown()
      f = provider
    } else throw new IllegalArgumentException("Provide a concrete tool provider, not this repository.")
  }

  // convenience methods forwarding to the current factory

  def defaultTool(): Option[Tool] = f.defaultTool()

  def qeTool(name: Option[String] = None): Option[QETool] = f.qeTool(name)

  def invGenTool(name: Option[String] = None): Option[InvGenTool] = f.invGenTool(name)

  def odeTool(): Option[ODESolverTool] = f.odeTool()

  def pdeTool(): Option[PDESolverTool] = f.pdeTool()

  def simplifierTool(): Option[SimplificationTool] = f.simplifierTool()

  def solverTool(): Option[EquationSolverTool] = f.solverTool()

  def algebraTool(): Option[AlgebraTool] = f.algebraTool()

  def cexTool(): Option[CounterExampleTool] = f.cexTool()

  def simulationTool(): Option[SimulationTool] = f.simulationTool()

  def shutdown(): Unit = f.shutdown()

  def tools(): List[Tool] = f.tools()

  def initFallbackZ3(p: => ToolProvider, toolName: String): ToolProvider = {
    try {
      val withZ3 = new MultiToolProvider(p :: new Z3ToolProvider() :: Nil)
      if (!p.tools().forall(_.isInitialized)) {
        val msg =
          s"""Unable to connect to $toolName, switching to Z3
             |Please check your $toolName configuration in KeYmaera X->Preferences
            """.stripMargin
        logger.info(msg)
        new Z3ToolProvider
      } else withZ3
    } catch {
      case ex: Throwable =>
        val msg =
          s"""Unable to connect to $toolName, switching to Z3
             |Please check your $toolName configuration in KeYmaera X->Preferences
             |$toolName initialization failed with the error below
            """.stripMargin
        logger.warn(msg, ex)
        logger.info(s"Starting with Z3 since $toolName initialization failed")
        new Z3ToolProvider
    }
  }
}

/** A tool factory creates various arithmetic and simulation tools.
  * @author Stefan Mitsch
  * @see [[edu.cmu.cs.ls.keymaerax.tools.ToolInterface]]
  */
trait ToolProvider {
  /** The provided tools. */
  def tools(): List[Tool]

  /** Returns the default tool */
  def defaultTool(): Option[Tool]

  /** Returns the tool with `name` */
  def tool(name: String): Option[Tool] = tools().find(_.name.equalsIgnoreCase(name))

  /** Returns a QE tool. */
  def qeTool(name: Option[String] = None): Option[QETool]

  def invGenTool(name: Option[String] = None): Option[InvGenTool]

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
  private[this] lazy val invgen: Option[Tool with InvGenTool] = toolPreferences.find(_.isInstanceOf[InvGenTool]).map(_.asInstanceOf[Tool with InvGenTool])
  private[this] lazy val ode: Option[Tool with ODESolverTool] = toolPreferences.find(_.isInstanceOf[ODESolverTool]).map(_.asInstanceOf[Tool with ODESolverTool])
  private[this] lazy val pde: Option[Tool with PDESolverTool] = toolPreferences.find(_.isInstanceOf[PDESolverTool]).map(_.asInstanceOf[Tool with PDESolverTool])
  private[this] lazy val cex: Option[Tool with CounterExampleTool] = toolPreferences.find(_.isInstanceOf[CounterExampleTool]).map(_.asInstanceOf[Tool with CounterExampleTool])
  private[this] lazy val simplifier: Option[Tool with SimplificationTool] = toolPreferences.find(_.isInstanceOf[SimplificationTool]).map(_.asInstanceOf[Tool with SimplificationTool])
  private[this] lazy val simulator: Option[Tool with SimulationTool] = toolPreferences.find(_.isInstanceOf[SimulationTool]).map(_.asInstanceOf[Tool with SimulationTool])
  private[this] lazy val solver: Option[Tool with EquationSolverTool] = toolPreferences.find(_.isInstanceOf[EquationSolverTool]).map(_.asInstanceOf[Tool with EquationSolverTool])
  private[this] lazy val algebra: Option[Tool with AlgebraTool] = toolPreferences.find(_.isInstanceOf[AlgebraTool]).map(_.asInstanceOf[Tool with AlgebraTool])

  override def tools(): List[Tool] = toolPreferences
  override def defaultTool(): Option[Tool] = toolPreferences.headOption
  override def qeTool(name: Option[String] = None): Option[QETool] = ensureInitialized[Tool with QETool](name match {
    case Some(qeToolName) => toolPreferences.find(t => t.isInstanceOf[QETool] && t.name == qeToolName).map(_.asInstanceOf[Tool with QETool])
    case None => qe
  })
  override def invGenTool(name: Option[String] = None): Option[InvGenTool] = ensureInitialized[Tool with InvGenTool](name match {
    case Some(invGenToolName) => toolPreferences.find(t => t.isInstanceOf[InvGenTool] && t.name == invGenToolName).map(_.asInstanceOf[Tool with InvGenTool])
    case None => invgen
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
  override def defaultTool(): Option[Tool] = None
  override def qeTool(name: Option[String] = None): Option[QETool] = None
  override def invGenTool(name: Option[String] = None): Option[InvGenTool] = None
  override def odeTool(): Option[ODESolverTool] = None
  override def pdeTool(): Option[PDESolverTool] = None
  override def simplifierTool(): Option[SimplificationTool] = None
  override def cexTool(): Option[CounterExampleTool] = None
  override def simulationTool(): Option[SimulationTool] = None
  override def solverTool(): Option[EquationSolverTool] = None
  override def algebraTool(): Option[AlgebraTool] = None
  override def shutdown(): Unit = {}
}

/** Combines multiple tool providers. */
class MultiToolProvider(providers: List[ToolProvider]) extends PreferredToolProvider(providers.flatMap(_.tools())) {
  // wolfram tool providers know alternative names to supply named tools
  override def qeTool(name: Option[String]): Option[QETool] = providers.flatMap(_.qeTool(name)).headOption
  override def invGenTool(name: Option[String]): Option[InvGenTool] = providers.flatMap(_.invGenTool(name)).headOption
}

/** A tool provider that provides Polya as a QE tools, everything else is None.
  * @author Stefan Mitsch
  */
class PolyaToolProvider extends PreferredToolProvider({ val p = new Polya; p.init(Map()); p :: Nil }) {
  def tool(): Polya = tools().head.asInstanceOf[Polya]
}

/** Base class for Wolfram tools with alternative names. */
abstract class WolframToolProvider(tool: Tool, alternativeNames: List[String]) extends PreferredToolProvider(tool :: Nil) {
  protected def alternativeTool[T](name: Option[String], factory: Option[String] => Option[T]): Option[T] = factory(name) match {
    case None => name match {
      case Some(t) if alternativeNames.contains(t) => defaultTool().filter(_.isInstanceOf[T]).map(_.asInstanceOf[Tool with T])
      case _ => None
    }
    case t => t
  }
  override def qeTool(name: Option[String] = None): Option[QETool] = alternativeTool(name, super.qeTool)
  override def invGenTool(name: Option[String] = None): Option[InvGenTool] = alternativeTool(name, super.invGenTool)
}


/** A tool provider that initializes tools to Mathematica.
  * @param config The Mathematica configuration (linkName, libDir).
  * @author Stefan Mitsch
  */
class MathematicaToolProvider(config: Configuration) extends WolframToolProvider({ val m = new Mathematica(new JLinkMathematicaLink("Mathematica"), "Mathematica"); m.init(config); m }, "WolframEngine" :: "WolframScript" :: "M" :: Nil) {
  def tool(): Mathematica = tools().head.asInstanceOf[Mathematica]
}

/** A tool provider that initializes tools to Wolfram Engine.
  * @author Stefan Mitsch
  */
class WolframEngineToolProvider(config: Configuration) extends WolframToolProvider({ val m = new Mathematica(new JLinkMathematicaLink("WolframEngine"), "WolframEngine"); m.init(config); m }, "Mathematica" :: "WolframScript" :: "M" :: Nil) {
  def tool(): Mathematica = tools().head.asInstanceOf[Mathematica]
}

/** A tool provider that initializes tools to Wolfram Script backend.
  * @author Stefan Mitsch
  */
class WolframScriptToolProvider extends WolframToolProvider({ val m = new Mathematica(new WolframScript, "WolframScript"); m.init(Map.empty); m}, "Mathematica" :: "WolframEngine" :: "M" :: Nil) {
  def tool(): Mathematica = tools().head.asInstanceOf[Mathematica]
}

/** A tool provider that provides Z3 as QE tool and KeYmaera's own bundled diff. solution tool, everything else is None.
  * @author Stefan Mitsch
  */
class Z3ToolProvider extends PreferredToolProvider({ val z = new Z3; z.init(Map()); val ode = new IntegratorODESolverTool; ode.init(Map()); z :: ode :: Nil }) {
  def tool(): Z3 = tools().head.asInstanceOf[Z3]
}

/** A tool provider that favors Mathematica tools, but supplies Z3 when specifically asked.
  * @author Stefan Mitsch
  */
class MathematicaZ3ToolProvider(config: Configuration) extends PreferredToolProvider(
  { val m = new Mathematica(new JLinkMathematicaLink("Mathematica"), "Mathematica"); m.init(config); val z = new Z3; z.init(Map()); m :: z :: m :: Nil }) { }

/** A tool provider that provides all Mathematica tools, but favors Z3 for QE unless specifically asked to provide Mathematica.
  * @author Stefan Mitsch
  */
class Z3MathematicaToolProvider(config: Configuration) extends PreferredToolProvider(
  { val m = new Mathematica(new JLinkMathematicaLink("Mathematica"), "Mathematica"); m.init(config); val z = new Z3; z.init(Map()); z :: m :: Nil }) { }
