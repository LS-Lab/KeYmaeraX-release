// Example how to run:
// C:\Users\bjboh\Documents\GitHub\KeYmaeraX\keymaerax-veriphy-experiments\target\scala-2.12>java -jar KeYmaeraX-VeriPhy-Experiments-assembly-4.9.2.jar  test_ffi  C:\Users\bjboh\Desktop
package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import java.io.{BufferedWriter, File, FileWriter}

import com.sun.jna._
import com.sun.jna.win32.StdCallLibrary
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
trait VeriPhySenselessFFIs extends StdCallLibrary {
  def ffiget_const(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  def ffiget_ctrl(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  def ffiactuate(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  def ffihas_next(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit  // int -> char
  def ffiviolation(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit // char -> int
  def ffiread_log(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  // c is path to output file, a is list of integers. can be called more than once
  def ffiinit(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  def ffiexit(): Unit //(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
}

// separate this out because GoPiGo will want to do special Python handling rather than C
trait VeriPhyFFIs extends VeriPhySenselessFFIs with StdCallLibrary {
  def ffiget_sensor(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
}


// Load DLL
case class FFILoader(libName: String) {
  def Instance: VeriPhyFFIs = {
    Native.load(libName, classOf[VeriPhyFFIs])
  }
}

// What sandbox action are we currently doing
trait VarMode
case object InitMode extends VarMode
case object ExtCtrlMode extends VarMode
case object ActuateMode extends VarMode
case object SenseMode extends VarMode

/** The long-term goal is to make this into a default strategy for wrapping VeriPhy v1 style FFIs,
 * but right now it's quite specific to the 1D robot simulator from the PLDI18 paper */
class FFIBasicStrategy[number <: Numeric[number, Ternary]]
(ffis: VeriPhyFFIs,
 val constVars: List[Variable],
 val senseVars: List[Variable],
 val ctrlVars: List[Variable],
 val env: Environment[number],
 val filePath: String,
 val intArgs: List[Int])
  extends BasicDemonStrategy[number] {
  var isInit = false
  val PRINT_EVENTS = true
  val DEBUG_PRINT = true

  var logWriter: BufferedWriter = null
  var varMode: VarMode = InitMode
  var staleVars: Boolean = true

  val ctrlSet: Set[Variable] = ctrlVars.toSet
  var ctrlBuf: Map[Variable, number] = Map()
  var senseBuf: Map[Variable, number] = Map()
  var extCtrlBuf: Map[Variable, number] = Map()

  // Get initial state by consulting constants and sensors
  // This gets called on creation. Initialization order is important to make sure init ffi gets called before other ffis
  def getInitState: Map[Ident, number] = {
    init(Some(filePath), intArgs)
    var vmap: Map[Ident, number] = Map()
    val inPC: Pointer = Pointer.NULL;
    val outPC: Pointer= new Memory(constVars.length*4)
    if (PRINT_EVENTS)
      println("ffiget_const: enter")
    ffis.ffiget_const(inPC, 0, outPC, constVars.length*4)
    for ((x, i) <- constVars.zipWithIndex) {
      val n = outPC.getInt(i*4)
      vmap = vmap.+(x -> env.factory.number(Rational(n)))
    }
    if (PRINT_EVENTS)
      println("ffiget_const: returned " + vmap)

    val inPS: Pointer = Pointer.NULL;
    val outPS: Pointer = new Memory(senseVars.length*4)
    if (PRINT_EVENTS)
      println("ffiget_sensor1: enter")
    ffis.ffiget_sensor(inPS, 0, outPS, senseVars.length*4)
    for ((x, i) <- senseVars.zipWithIndex) {
      val z: Int = outPS.getInt(i*4)
      val n = env.factory.number(Rational(z))
      senseBuf = senseBuf.+(x -> n)
      vmap = vmap.+(x -> n)
    }
    if (PRINT_EVENTS)
      println("ffiget_sensor1: returned " + vmap)
    varMode = ExtCtrlMode
    vmap
  }

  val readInitState: Map[Ident, number] = getInitState

  // Use FFIs to collect strings from DLL and then print them.
  // It is often recommended to have DLLs do indirect I/O by passing them to the main program.
  // It's no longer to me whether it is *strictly* necessary to do this.
  // The original reason for doing this was that the DLL was crashing when calling standard library functions,
  // but that turned out not to be specific to IO but to be a hilarious issue due to running code with Linux calling
  // conventions on Windows
  private def doIO(): Unit = {
    val BUF_SIZE = 256 * 256
    val strP: Pointer = new Memory(BUF_SIZE)
    strP.setByte(0, 0)
    val sizeP: Pointer = new Memory(8)
    var remaining = 1 // bogus init value
    var sb = new StringBuilder()
    while (remaining > 0) {
      ffis.ffiread_log(strP, BUF_SIZE, sizeP, 8)
      remaining = sizeP.getInt(0)
      var i = 0
      val most = sizeP.getInt(4)
      while (strP.getByte(i) != 0 && i < most) {
        sb = sb.append(strP.getByte(i).toChar)
        i = i + 1
      }
      val theString = sb.mkString
      logWriter.write(theString)
      logWriter.flush()
      if (DEBUG_PRINT)
        println("PRINTED STRING left:" + sizeP.getInt(0) + ", amount:" + sizeP.getInt(4) + "\n" + theString)
    }
  }

  def readDemonLoop(id: NodeID): Boolean = {
    doIO()
    val inP: Pointer = Pointer.NULL;//new Memory(0)
    val outP: Pointer = new Memory(Native.WCHAR_SIZE)
    outP.setChar(0,0)// initialize output array for sake of consistency
    if(PRINT_EVENTS)
      println("ffihas_next")
    ffis.ffihas_next(inP, 0, outP, 1)
    varMode = ExtCtrlMode
    staleVars = true
    outP.getByte(0) != 0
  }

  def readDemonChoice(id: NodeID): Boolean = {
    val lhs = env.get(Variable("d"))
    val rhs = env.get(Variable("eps")) * env.get(Variable("V"))
    if ( env.factory.number(50000) >= lhs == KnownTrue()) {
      val _ = 1 + 1
    }

    val cmp = (lhs >= rhs) == KnownTrue()
    !(cmp)
  }

  def readDemonAssign(id: NodeID, x: String, varIndex: Option[Int]): number = {
    if(PRINT_EVENTS)
      println(s"readDemonAssign: $x, $varIndex")
    if (varMode == ActuateMode)
      varMode = SenseMode
    // Do we need to ask FFIs for values? This flag is mostly used to make sure we only call FFI once to read all controllers / sensors as a block
    if (staleVars) {
      staleVars = false
      // Use mode flag to check which FFI to call because some variables are both sensed and controlled, variable name alone doesn't tell us what to do
      varMode match {
        // Do I ask external controller?
        case ExtCtrlMode =>
          extCtrlBuf = Map()
          val inVars = constVars ++ senseVars
          val inPEC: Pointer = new Memory(4*inVars.length)
          val outPEC: Pointer = new Memory(4*ctrlVars.length)

          var printArgs: Map[Variable, number] = Map()
          for ((x,i) <- inVars.zipWithIndex) {
            val v = if (constVars.contains(x)) readInitState(x) else senseBuf(x)
            printArgs = printArgs.+(x -> v)
            inPEC.setInt(4*i, v.intApprox)
          }

          if(PRINT_EVENTS)
            println("ffiget_ctrl: args " + printArgs)
          ffis.ffiget_ctrl(inPEC, 4*inVars.length, outPEC,4*ctrlVars.length)
          for ((x,i) <- ctrlVars.zipWithIndex) {
            val n = outPEC.getInt(4*i)
            extCtrlBuf = extCtrlBuf.+(x -> env.factory.number(n))
            if(ctrlVars.contains(x)) {
              ctrlBuf = ctrlBuf.+(x -> extCtrlBuf(x))
            }

          }
          if(PRINT_EVENTS)
            println("ffiget_ctrl: returned " + extCtrlBuf + ", " + Variable(x) + ", "+ extCtrlBuf(Variable(x)))
          extCtrlBuf(Variable(x))
        // Do I ask sensors?
        case SenseMode =>
          senseBuf = Map()
          val inPC: Pointer = Pointer.NULL;//new Memory(0)
          val outPC: Pointer = new Memory(senseVars.length*4)
          if(PRINT_EVENTS)
            println("ffiget_sensor: enter")
          ffis.ffiget_sensor(inPC, 0, outPC, 4*senseVars.length)
          for ((x,i) <- senseVars.zipWithIndex) {
            val n = outPC.getInt(i*4)
            senseBuf = senseBuf.+(x -> env.factory.number(n))
          }
          if(PRINT_EVENTS)
            println("ffiget_sensor: returned " + senseBuf + ", " + Variable(x) + ", " + senseBuf(Variable(x)))
          senseBuf(Variable(x))
      }
    } else {
      varMode match {
        case ExtCtrlMode =>
          println(s"read old extctrl $x: ${extCtrlBuf(Variable(x))}")
          extCtrlBuf(Variable(x))
        case SenseMode =>
          println(s"read old sense $x: ${senseBuf(Variable(x))}")
          senseBuf(Variable(x))
        case InitMode | _ => ???
      }
    }
  }

  override def writeAngelAssign(id: NodeID, baseVar: String, varIndex: Option[NodeID], value: number): Unit = {
    if(PRINT_EVENTS)
      println(s"writeAngelAssign: $baseVar, $varIndex, $value")
    def toInt(n: number): Int = {
      n.intApprox
    }
    if(ctrlSet.contains(Variable(baseVar))) { //&& !ctrlBuf.contains(Variable(baseVar))
      ctrlBuf = ctrlBuf.+(Variable(baseVar) -> value)
    }
    // @TODO: A bit of a hack to avoid calling FFI too many times, just catch the t:=0 assign at start of ODE
    val timed = baseVar == "t" && varIndex.contains(2) && value.intApprox == 0
    // actuate and reset buffer if all variables have been assigned
    if (timed) {
      val inP: Pointer = new Memory(ctrlVars.length*4)
      val outP: Pointer = Pointer.NULL;//new Memory(0)
      for ((x,i) <- ctrlVars.zipWithIndex) {
        inP.setInt(i*4,toInt(ctrlBuf(x)))
      }
      if(PRINT_EVENTS)
        println("ffiactuate:" + ctrlBuf)
      ffis.ffiactuate(inP, ctrlVars.length*4, outP, 0)
      ctrlBuf = Map()
      staleVars = true
      varMode = ActuateMode
    }
  }

  // send FFI for plant violation and read any I/O from it
  override def reportViolation(): Unit = {
    ffis.ffiviolation(Pointer.NULL, 0, Pointer.NULL, 0)
    doIO()
  }

  // tell FFIs to initialize, also initialize CSV writers
  override def init(stringArg: Option[String], intArgs: List[NodeID]): Unit = {
    if(isInit)
      return
    val str = stringArg.get
    val strP: Pointer = new Memory(str.length + 1)
    val intP: Pointer = new Memory(intArgs.length * 4)
    for((c,i) <- str.toCharArray.zipWithIndex) {
      strP.setByte(i,c.toByte)
    }
    strP.setByte(str.length, 0)
    for((n,i) <- intArgs.zipWithIndex) {
      intP.setInt(4*i, n)
    }
    if(PRINT_EVENTS)
      println(s"init:$str, $intArgs")
    ffis.ffiinit(strP, str.length, intP, intArgs.length * 4)
    if (logWriter != null) {
      logWriter.flush()
      logWriter.close()
    }
    val file = new File(str)
    logWriter = new BufferedWriter(new FileWriter(file))
    if(PRINT_EVENTS)
      println(s"initDone")
    isInit = true
  }

  // finish up IO and shut down any robots/etc on exit
  override def exit(): Unit = {
    ffis.ffiexit()
    doIO()

    if (logWriter != null) logWriter.close()

    isInit = false
    varMode = InitMode
    staleVars = true
    ctrlBuf = Map()
    senseBuf = Map()
    extCtrlBuf = Map()
  }
}

// specify the const, readable, assign variables for the robot model
class GoPiGoBasicStrategy[number <: Numeric[number, Ternary]](ffis: VeriPhyFFIs, env: Environment[number], filePath: String, intArgs: List[Int])
  extends FFIBasicStrategy[number](ffis,
    List(Variable("V"), Variable("eps")), // const
    List(Variable("d"), Variable("t")),   // read
    List(Variable("v"), Variable("t")),   // assign
    env, filePath, intArgs)

object BotMain {
  // source model for documentation
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

  // Generated from model but then modified by hand.
  // @TODO: Update with d >= 0 constraint in plant monitor
  val astratStr: String = "SCompose(" +  // 1 - paren nesting level
    "SAssignAny(eps_0),SAssignAny(v_0),SAssignAny(d_0),SAssignAny(V_0),SAssignAny(t_0)," + //1
    "STest(d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0)," +  // 1
    "SAssign(t_1,t_0),SAssign(v_1,v_0),SAssign(d_1,d_0)," +  //1
    "SLoop(" +  //2
    "SCompose(" +  //3
    "SChoice(" +  //4
      "SCompose(" + //5
        "STest(d_1>=eps_0*V_0)," +
        "SAssignAny(v_2)," +
        "STest(0<=v_2&v_2<=V_0))," + //4
      "SAssign(v_2,0))," + //3
    "SAssign(t_2,0)," + //3
    "SAssign(t_3,t_2),SAssign(d_2,d_1)," + //3
    "SAssignAny(t_3),STest(t_3>=0)," + //3
      "STest(t_3<=eps_0)," + //3
      "SAssign(t_3,t_3),SAssign(d_2,(-v_2)*t_3+d_1)," + //3
         "STest(t_3>=0 & t_3<=eps_0 & d_2>=v_2*(eps_0-t_3))," + //3
      "SAssign(t_1,t_3),SAssign(v_1,v_2),SAssign(d_1,d_2))))"

  // arguments for each test
  case class SimSpec(name: String, speedFactor: Int, obstacleSpeed: Int, actuatorOffset: Int, duration: Int, initialDistance: Int, reactionTime: Int)
  // just test one speed for debugging purposes
  val testSpeeds: List[Int] = List(100/*, 150, 200, 250*/)

  // based on tables / scripts
  val altSimArgs: List[SimSpec] = List(
    SimSpec("correct", 1, 0, 0, 13, 1000000, 220),
    SimSpec("ctrlbug", -1, 0, 0, 13, 1000000, 220),
    SimSpec("backwards", -1, -50, 0, 13, 1000000, 220),
    SimSpec("actoffsetSafe", -1, 0, -10, 13, 1000000, 220),
    SimSpec("actoffsetUnsafe", -1, 0, 10, 13, 1000000, 220),
    SimSpec("actoffsetCompensatesBackwardsObst", 1, -30, -40, 13, 1000000, 220),
    SimSpec("forwardObstCompensatesUnsafeActoffset", 1, 20, 10, 13, 1000000, 220)
  )

  // based on actual csv files I have
  val simArgs: List[SimSpec] = List(
    // commented out to focus on debugging the not-commented-out ones
    /*SimSpec("correct", 1, 0, 0, 10, 750000, 220),
    SimSpec("ctrlbug", -1, 0, 0, 10, 750000, 220),*/
    SimSpec("backwards", -1, -50, 0, 10, 750000, 220)/*,
    SimSpec("actoffsetSafe", -1, 0, -10, 10, 750000, 220),
    SimSpec("actoffsetUnsafe", -1, 0, 10, 10, 750000, 220)*/
  )

  // De one simulation and save the results to CSV
  def doOneSim(lib: VeriPhyFFIs, astrat: AngelStrategy, path: String, spec: SimSpec, speed: Int): Unit = {
    val filePath = path + File.separator + spec.name + speed + ".csv"
    val intArgs = List(spec.speedFactor*speed, spec.obstacleSpeed, spec.actuatorOffset, spec.duration, spec.initialDistance, spec.reactionTime)
    val factory = UnknowingFactory(RatFactory)
    val env: Environment[TernaryNumber[RatNum]] = new Environment(factory)
    val basic = new GoPiGoBasicStrategy(lib, env, filePath, intArgs)
    val demon = new WrappedDemonStrategy(basic)(env)
    println("Time to interpret: " + spec.name + "," + speed)
    val interp = new Play(factory)
    interp(env, astrat, demon)
    demon.exit()
    println("Final state: " + env.state)
  }

  // Args:  dll_name [dll_path]
  // dll_path is used for both dll loading and for printing CSV files
  def main(args: Array[String]): Unit = {
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

    val load = FFILoader(libName)
    val lib: VeriPhyFFIs = load.Instance
    println("Loaded DLL for FFI!")
    println("native size: " + Native.LONG_SIZE)
    println("Hmm")
    val angel = StrategyParser(astratStr)
    println("AngelStrat1:\n" + StrategyPrinter(angel))
    for(speed <- testSpeeds) {
      for (simArg <- simArgs) {
        doOneSim(lib, angel, fullPath, simArg, speed)
      }
    }
  }
}
