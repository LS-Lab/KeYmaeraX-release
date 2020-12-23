package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import java.io.File

import com.sun.jna.Native
//import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
//import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
//import edu.cmu.cs.ls.keymaerax.btactics._

//import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
//import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica
//import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import BotCommon._
//import edu.cmu.cs.ls.keymaerax.cdgl.kaisar._
//import edu.cmu.cs.ls.keymaerax.cdgl._

object MainWithProofs {
/*
  private val WOLFRAM = System.getProperty("WOLFRAM", "mathematica").toLowerCase

  class Lazy[T](f: => T) {
    private var option: Option[T] = None
    def apply(): T = option match {
      case Some(t) => t
      case None => val t = f; option = Some(t); t
    }
    def isInitialized: Boolean = option.isDefined
    def asOption: Option[T] = option
  }


  /** A tool provider that does not shut down on `shutdown`, but defers to `doShutdown`. */
  class DelayedShutdownToolProvider(p: ToolProvider) extends PreferredToolProvider(p.tools()) {
    override def init(): Boolean = p.init()
    override def shutdown(): Unit = {} // do not shut down between tests and when switching providers in ToolProvider.setProvider
    def doShutdown(): Unit = super.shutdown()
  }

  def withTemporaryConfig(tempConfig: Map[String, String])(testcode: => Any): Unit =
    Configuration.withTemporaryConfig(tempConfig)(testcode)

  //@note Initialize once per test class in beforeAll, but only if requested in a withMathematica call
  private val mathematicaProvider: Lazy[DelayedShutdownToolProvider] = new Lazy(new DelayedShutdownToolProvider(MathematicaToolProvider(ToolConfiguration.config(WOLFRAM.toLowerCase))))

  private def initQE(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    val mathLinkTcp = System.getProperty(Configuration.Keys.MATH_LINK_TCPIP, Configuration(Configuration.Keys.MATH_LINK_TCPIP)) // JVM parameter -DMATH_LINK_TCPIP=[true,false]
    val common = Map(
      Configuration.Keys.MATH_LINK_TCPIP -> mathLinkTcp,
      Configuration.Keys.QE_TOOL -> WOLFRAM)
    val uninterp = common + (Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "false")
    withTemporaryConfig(common) {
      val provider = mathematicaProvider()
      ToolProvider.setProvider(provider)
      val toolMap = Map("linkName" -> "C:\\Program Files\\Wolfram Research\\Mathematica\\SystemFiles\\Links\\JLink\\JLink.jar")
      val tool = provider.defaultTool() match {
        case Some(m: Mathematica) => m
        case _ => throw new Exception("Illegal Wolfram tool, please use one of 'Mathematica' or 'Wolfram Engine' in test setup")
      }
      KeYmaeraXTool.init(Map(
        KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName
      ))
    }
  }

  val check: String => Statement = Kaisar.statementProved
*/
  // Just for generating strategy
  def main(args: Array[String]): Unit = {
    /*
    if(args.length == 0) {
      println("Usage: ... <path_to_Kaisar_file>")
      return
    }

    val kaisarFile = scala.io.Source.fromFile(args(0), "UTF-8")
    initQE()
    println("Initialized QE")
    val pf = check(noStar1DBotModel)
    val angel =  SimpleStrategy(AngelStrategy(pf))
    println("AngelStrat:\n" + StrategyPrinter(angel))*/
  }

    // Args:  dll_name [dll_path]
  // dll_path is used for both dll loading and for printing CSV files
  // for actually running bot after generating strat
  /*def main(args: Array[String]): Unit = {
    val libName = args(0)
    // paths for loading DLL
    val fullPath =
      if (args.length > 1) {
        val dirName = args(1)
        val path = System.getProperty("jna.library.path")
        val fullPath = if(path == null) dirName else dirName + File.pathSeparator + path
        System.setProperty("jna.library.path", fullPath)
        fullPath
      } else {
        "."
      }

    initQE()
    println("Initialized QE")
    //val pf = check(noSandbox1DBotModel)
    val pf = check(noStar1DBotModel)
    val angel =  SimpleStrategy(AngelStrategy(pf))
    println("AngelStrat1:\n" + StrategyPrinter(angel))
    // So it's easy to find the strategy
    println("\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n")
    val load = FFILoader(libName)
    val lib: VeriPhyFFIs = load.Instance
    println("Loaded DLL for FFI!")
    println("native size: " + Native.LONG_SIZE)
    //val angel = StrategyParser(astratStr)
    println("AngelStrat1:\n" + StrategyPrinter(angel))
    for(speed <- testSpeeds) {
      for (simArg <- simArgs) {
        doOneBotSim(lib, angel, fullPath, simArg, speed)
      }
    }
  }*/

}
