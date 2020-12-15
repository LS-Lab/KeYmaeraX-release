//@TODO: Parse demon strategy directly so we don't need proofs here
//@TODO: copy-paste and reorganize files for minimal jar size for efficiency
package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import java.io.File

import com.sun.jna._
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.btactics.{MathematicaToolProvider, PreferredToolProvider, ToolProvider}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Ident
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import spire.math.Rational

import scala.collection.immutable.Map
import scala.io.Source

//FFI specs for VeriPhy driver functions
trait VeriPhySenselessFFIs extends Library {
  def ffiget_const(c: Array[Int], clen: Long, a: Array[Int], alen: Long): Unit
  def ffiget_ctrl(c: Array[Int], clen: Long, a: Array[Int], alen: Long): Unit
  def ffiactuate(c: Array[Int], clen: Long, a: Array[Int], alen: Long): Unit
  def ffihas_next(c: Array[Int], clen: Long, a: Array[Char], alen: Long): Unit
  def ffiviolation(c: Array[Char], clen: Long, a: Array[Int], alen: Long): Unit
}

// separate this out because GoPiGo will want to do special Python handling rather than C
trait VeriPhyFFIs extends VeriPhySenselessFFIs with Library {
  def ffiget_sensor(c: Array[Int], clen: Long, a: Array[Int], alen: Long): Unit
}


// Load DLL
case class FFILoader(libName: String) {
  def Instance: VeriPhyFFIs = Native.load(
    libName,
    classOf[VeriPhyFFIs])
}

// What sandbox action are we currently doing
trait VarMode
case object InitMode extends VarMode
case object ExtCtrlMode extends VarMode
case object ActuateMode extends VarMode
case object SenseMode extends VarMode

/** Default strategy for wrapping VeriPhy v1 style FFIs  */
class FFIBasicStrategy[number <: Numeric[number, Ternary]]
(ffis: VeriPhyFFIs,
 val constVars: List[Variable],
 val senseVars: List[Variable],
 val ctrlVars: List[Variable],
 val env: Environment[number])
  extends BasicDemonStrategy[number] {
  var varMode: VarMode = InitMode
  var staleVars: Boolean = true

  val ctrlSet: Set[Variable] = ctrlVars.toSet
  var ctrlBuf: Map[Variable, number] = Map()
  var senseBuf: Map[Variable, number] = Map()
  var extCtrlBuf: Map[Variable, number] = Map()

  def getInitState: Map[Ident, number] = {
    var vmap: Map[Ident, number] = Map()
    val inArrayC: Array[Int] = new Array(0)
    val outArrayC: Array[Int] = Array.fill[Int](constVars.length)(0)
    println("ffiget_const")

    ffis.ffiget_const(inArrayC, inArrayC.length*4, outArrayC, outArrayC.length*4)
    for ((x, i) <- constVars.zipWithIndex) {
      vmap = vmap.+(x -> env.factory.number(Rational(outArrayC(i))))
    }
    val inArrayS: Array[Int] = new Array(0)
    val outArrayS: Array[Int] = Array.fill[Int](senseVars.length)(0)
    println("ffiget_sensor")
    ffis.ffiget_sensor(inArrayS, inArrayS.length*4, outArrayS, outArrayS.length*4)
    val outList = outArrayS.toList
    for ((x, i) <- senseVars.zipWithIndex) {
      val z: Int = outList(i)
      val n = env.factory.number(Rational(z))
      senseBuf = senseBuf.+(x -> n)
      vmap = vmap.+(x -> n)
    }
    varMode = ExtCtrlMode
    vmap
  }

  val readInitState: Map[Ident, number] = getInitState

  def readDemonLoop(id: NodeID): Boolean = {
    val inArray: Array[Int] = new Array(0)
    val outArray: Array[Char] = new Array(1)
    outArray(0) = 0 // initialize output array for sake of consistency
    println("ffihas_next")
    ffis.ffihas_next(inArray, inArray.length*4, outArray, outArray.length)
    varMode = ExtCtrlMode
    outArray(0) != 0 // return whether result differs from 0
  }

  def readDemonChoice(id: NodeID): Boolean = throw new Exception ("Model does not contain demon choice")

  def readDemonAssign(id: NodeID, x: String, varIndex: Option[Int]): number = {
    println(s"readDemonAssign: $x, $varIndex")
    if (varMode == ActuateMode)
      varMode = SenseMode
    if (staleVars) {
      staleVars = false
      varMode match {
        case ExtCtrlMode =>
          extCtrlBuf = Map()
          val inVars = constVars ++ senseVars
          val inArrayEC: Array[Int] = new Array(inVars.length)
          val outArrayEC: Array[Int] = Array.fill[Int](ctrlVars.length)(0)

          for ((x,i) <- inVars.zipWithIndex) {
            val v = if (constVars.contains(x)) readInitState(x) else senseBuf(x)
            inArrayEC(i) = v.intApprox
          }

          println("ffiget_ctrl")
          ffis.ffiget_ctrl(inArrayEC, inArrayEC.length*4, outArrayEC, outArrayEC.length*4)
          for ((x,i) <- ctrlVars.zipWithIndex) {
            extCtrlBuf = extCtrlBuf.+(x -> env.factory.number(outArrayEC(i)))
          }
          extCtrlBuf(Variable(x))
        case SenseMode =>
          senseBuf = Map()
          val inArrayC: Array[Int] = new Array(0)
          val outArrayC: Array[Int] = Array.fill[Int](senseVars.length)(0)
          println("ffiget_sensor")
          ffis.ffiget_sensor(inArrayC, inArrayC.length*4, outArrayC, outArrayC.length*4)
          for ((x,i) <- senseVars.zipWithIndex) {
            senseBuf = senseBuf.+(x -> env.factory.number(outArrayC(i)))
          }
          senseBuf(Variable(x))
      }
    } else {
      varMode match {
        case ExtCtrlMode =>
          extCtrlBuf(Variable(x))
        case SenseMode =>
          senseBuf(Variable(x))
        case InitMode | _ => ???
      }
    }
  }

  override def writeAngelAssign(id: NodeID, baseVar: String, varIndex: Option[NodeID], value: number): Unit = {
    println(s"writeAngelAssign: $baseVar, $varIndex, $value")
    def toInt(n: number): Int = {
      n.intApprox
    }
    ctrlBuf = ctrlBuf.+(Variable(baseVar) -> value)
    // actuate and reset buffer if all variables have been assigned
    if ((ctrlSet -- ctrlBuf.keySet).isEmpty) {
      val inArray: Array[Int] = Array.fill[Int](ctrlVars.length)(0)
      val outArray: Array[Int] = new Array(0)
      for ((x,i) <- ctrlVars.zipWithIndex) {
        inArray(i) = toInt(ctrlBuf(x))
      }
      println("ffiactuate")
      ffis.ffiactuate(inArray, inArray.length*4, outArray, outArray.length*4)
      ctrlBuf = Map()
      staleVars = true
      varMode = ActuateMode
    }
  }
}

class GoPiGoBasicStrategy[number <: Numeric[number, Ternary]](ffis: VeriPhyFFIs, env: Environment[number])
  extends FFIBasicStrategy[number](ffis,
    List(Variable("V"), Variable("eps")), // const
    List(Variable("d"), Variable("t")),   // read
    List(Variable("v"), Variable("t")),   // assign
    env)

object BotMain {
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
      val tool = provider.defaultTool() match {
        case Some(m: Mathematica) => m
        case _ => throw new Exception("Illegal Wolfram tool, please use one of 'Mathematica' or 'Wolfram Engine' in test setup")
      }
      KeYmaeraXTool.init(Map(
        //KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> initLibrary.toString,
        KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName
      ))
    }
  }


  val check: String => Statement = Kaisar.statementProved

  val botModel: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  {?(d >= eps*V); v:=*; ?(0<=v & v<=V); ++ v:=0;}
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps);};}
      |  !brk:(inv());
      | }*
      | !(d >= 0);
      |""".stripMargin

  // Args:  dll_name [dll_path]
  def main(args: Array[String]): Unit = {
    val libName = args(0)
    // paths for loading DLL
    if (args.length > 1) {
      val dirName = args(1)
      val path = System.getProperty("jna.library.path")
      val fullPath = if(path == null) dirName else dirName + File.pathSeparator + path
      System.setProperty("jna.library.path", fullPath)
      val what = System.getProperty("jna.library.path")
      println("help:" + what)
    }

    initQE()
    println("Initialized QE")
    val pf = check(botModel)
    println("Checked proof")
    val load = FFILoader(libName)
    val lib: VeriPhyFFIs = load.Instance
    println("Loaded DLL for FFI!")
    val angel = SimpleStrategy(AngelStrategy(pf))
    val factory = UnknowingFactory(RatFactory)
    val env: Environment[TernaryNumber[RatNum]] = new Environment(factory)
    val basic = new GoPiGoBasicStrategy(lib, env)
    val demon = new WrappedDemonStrategy(basic)(env)
    demon.init()
    val interp = new Play(factory)
    println("Time to interpret")
    interp(env, angel, demon)
    println("Interp terminated normally")
    println("Final state: " + env.state)
  }
}
