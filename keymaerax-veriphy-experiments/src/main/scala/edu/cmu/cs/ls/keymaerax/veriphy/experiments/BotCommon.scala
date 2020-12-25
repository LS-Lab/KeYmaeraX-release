package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import java.io.{BufferedWriter, File, FileWriter}

import com.sun.jna.{Library, Memory, Native, Pointer}
import com.sun.jna.win32.StdCallLibrary
import KaisarProof.Ident
//import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.{AngelStrategy, BasicDemonStrategy, Environment, KnownTrue, Numeric, Play, RatFactory, RatNum, Ternary, TernaryNumber, TestFailureException, UnknowingFactory, WrappedDemonStrategy}
import edu.cmu.cs.ls.keymaerax.core._
//import spire.math.Rational

import scala.collection.immutable.Map

//FFI specs for VeriPhy driver functions
trait VeriPhySenselessFFIs extends Library {
  def ffiget_const(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  def ffiget_ctrl(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  def ffiactuate(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  def ffihas_next(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit  // int -> char
  def ffifallback(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit // char -> int
  def ffiviolation(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit // char -> int
  def ffiread_log(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  // c is path to output file, a is list of integers. can be called more than once
  def ffiinit(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
  def ffiexit(): Unit //(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
}

// separate this out because GoPiGo will want to do special Python handling rather than C
trait VeriPhyFFIs extends VeriPhySenselessFFIs with Library {
  def ffiget_sensor(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit

  // Call all functions once to get any JIT compilation overhead out of the way, page into memory, etc
  // this is specialized to GoPiGo, who knows if it might crash other code
  // make sure to init again after this because it will have bogus info
  def warmStart(): Unit = {
    val initintArgs = List(1, 1, 0)
    val initstr = "foo"
    val initstrP: Pointer = new Memory(initstr.length + 1)
    val initintP: Memory = new Memory(initintArgs.length * 4)
    ffiinit(initstrP, initstr.length+1, initintP, initintArgs.length*4)
    val gisOutPC: Pointer = new Memory(2*4)
    val gisOutPS: Pointer = new Memory(2*4)
    ffiget_const(Pointer.NULL, 0, gisOutPC, 2*4)
    ffiget_sensor(Pointer.NULL, clen = 0, gisOutPS, 2*4)
    val rdainPEC: Pointer = new Memory(4*4)
    val rdaoutPEC: Pointer = new Memory(4*3)
    rdainPEC.setInt(0, 250)
    rdainPEC.setInt(4, 1000)
    rdainPEC.setInt(8, 70000)
    rdainPEC.setInt(12, 0)
    ffiget_ctrl(rdainPEC, 4*4, rdaoutPEC, 4*3)
    ffifallback(Pointer.NULL, 0, Pointer.NULL, 0)
    ffiviolation(Pointer.NULL, 0, Pointer.NULL, 0)
    val actinP = new Memory(3*4)
    actinP.setInt(0, 0)
    actinP.setInt(4, 0)
    actinP.setInt(8, 0)
    ffiactuate(actinP, 3*4, Pointer.NULL, 0)
    val rdlOutP: Pointer = new Memory(Native.WCHAR_SIZE)
    ffihas_next(Pointer.NULL, 0, rdlOutP, 1)
    val rlStrP: Pointer = new Memory(2000)
    val rlOutP: Pointer = new Memory(8)
    ffiread_log(rlStrP, 2000, rlOutP, 8)
    ffiexit()
  }
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
  val PRINT_EVENTS = false
  val DEBUG_PRINT = false

  var logWriter: BufferedWriter = null
  var varMode: VarMode = InitMode
  var staleVars: Boolean = true

  val ctrlSet: Set[Variable] = ctrlVars.toSet
  var ctrlBuf: Map[Variable, number] = Map()
  var senseBuf: Map[Variable, number] = Map()
  var extCtrlBuf: Map[Variable, number] = Map()

  // Get initial state by consulting constants and sensors
  // This gets called on creation. Initialization order is important to make sure init ffi gets called before other ffis
  val gisOutPC: Pointer = new Memory(constVars.length*4)
  val gisOutPS: Pointer = new Memory(senseVars.length*4)
  def getInitState: Map[Ident, number] = {
    init(Some(filePath), intArgs)
    var vmap: Map[Ident, number] = Map()
    val inPC: Pointer = Pointer.NULL;
    val outPC: Pointer = gisOutPC
    if (PRINT_EVENTS)
      println("ffiget_const: enter")
    ffis.ffiget_const(inPC, 0, outPC, constVars.length*4)
    for ((x, i) <- constVars.zipWithIndex) {
      val n = outPC.getInt(i*4)
      vmap = vmap.+(x -> env.factory.number(Rational(n, 1)))
    }
    if (PRINT_EVENTS)
      println("ffiget_const: returned  " + vmap)

    val inPS: Pointer = Pointer.NULL;
    val outPS: Pointer = gisOutPS //new Memory(senseVars.length*4)
    if (PRINT_EVENTS)
      println("ffiget_sensor1: enter")
    ffis.ffiget_sensor(inPS, 0, outPS, senseVars.length*4)
    for ((x, i) <- senseVars.zipWithIndex) {
      val z: Int = outPS.getInt(i*4)
      val n = env.factory.number(Rational(z, 1))
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
  val BUF_SIZE = 256 * 256
  val ioStrP: Pointer = new Memory(BUF_SIZE)
  val rlOutP: Pointer = new Memory(8)
  private def doIO(): Unit = {
    val strP: Pointer = ioStrP
    strP.setByte(0, 0)
    val sizeP: Pointer = rlOutP
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
      val before = System.currentTimeMillis()
      logWriter.write(theString)
      logWriter.flush()
      val after = System.currentTimeMillis()
      //println("LOG PRINT TIME (ms): " + (after-before))
      if (DEBUG_PRINT)
        println("PRINTED STRING left:" + sizeP.getInt(0) + ", amount:" + sizeP.getInt(4) + "\n" + theString)
    }
  }

  val rdlOutP: Pointer = new Memory(Native.WCHAR_SIZE)
  def readDemonLoop(id: NodeID): Boolean = {
    doIO()
    val inP: Pointer = Pointer.NULL;
    val outP: Pointer = rdlOutP
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
    val theV = readDemonAssign(id, "v", None)
    val rc = (theV.eq(env.factory.number(Rational(0,1))))
    val lc = lhs >= rhs
    val cmp = lc == KnownTrue()
    if(DEBUG_PRINT)
      println(s"readDemonChoice: Went right? ${!cmp} , ($lc)")
    if (!cmp && !(rc == KnownTrue())) {
      // announce that fallback was called. as of this writing, this is strictly for bookkeeping purposes.
      // Only do it if rc is false because in the other case their controller would have been safe too but we can't
      // literally use that branch because it would have a false test
      ffis.ffifallback(Pointer.NULL, 0, Pointer.NULL, 0)
    }
    !cmp
  }

  val inVars = constVars ++ senseVars
  val rdainPEC: Pointer = new Memory(4*inVars.length)
  val rdaoutPEC: Pointer = new Memory(4*ctrlVars.length)
  val smOutPC: Pointer = new Memory(senseVars.length*4)
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
          val inPEC: Pointer = rdainPEC
          val outPEC: Pointer = rdaoutPEC

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
            extCtrlBuf = extCtrlBuf.+(x -> env.factory.number(Rational(n,1)))
            if(ctrlVars.contains(x)) {
              ctrlBuf = ctrlBuf.+(x -> extCtrlBuf(x))
            }

          }
          if(PRINT_EVENTS)
            println("ffiget_ctrl: returned " + extCtrlBuf + ", " + toVar(x) + ", "+ extCtrlBuf(toVar(x)))
          extCtrlBuf(toVar(x))
        // Do I ask sensors?
        case SenseMode =>
          senseBuf = Map()
          val inPC: Pointer = Pointer.NULL;//new Memory(0)
          val outPC: Pointer = smOutPC
          if(PRINT_EVENTS)
            println("ffiget_sensor: enter")
          ffis.ffiget_sensor(inPC, 0, outPC, 4*senseVars.length)
          for ((x,i) <- senseVars.zipWithIndex) {
            val n = outPC.getInt(i*4)
            senseBuf = senseBuf.+(x -> env.factory.number(Rational(n,1)))
          }
          if(PRINT_EVENTS)
            println("ffiget_sensor: returned " + senseBuf + ", " + toVar(x) + ", " + senseBuf(toVar(x)))
          senseBuf(toVar(x))
      }
    } else {
      varMode match {
        case ExtCtrlMode =>
          if(DEBUG_PRINT)
            println(s"read old extctrl $x: ${extCtrlBuf(toVar(x))}")
          extCtrlBuf(toVar(x))
        case SenseMode =>
          if(DEBUG_PRINT)
            println(s"read old sense $x: ${senseBuf(toVar(x))}")
          senseBuf(toVar(x))
        case InitMode | _ => ???
      }
    }
  }

  private def toVar(str: String): Variable = {
    if(str.endsWith("'")) {
      DifferentialSymbol(Variable(str.dropRight(1)))
    } else {
      Variable(str)
    }
  }

  val waaInP: Pointer = new Memory(ctrlVars.length*4)
  override def writeAngelAssign(id: NodeID, baseVar: String, varIndex: Option[NodeID], value: number): Unit = {
    if(PRINT_EVENTS)
      println(s"writeAngelAssign: $baseVar, $varIndex, $value")
    def toInt(n: number): Int = {
      n.intApprox
    }
    if(ctrlSet.contains(toVar(baseVar))) {
      ctrlBuf = ctrlBuf.+(toVar(baseVar) -> value)
      extCtrlBuf = extCtrlBuf.+(toVar(baseVar) -> value)
    }
    // @TODO: A bit of a hack to avoid calling FFI too many times, just catch the t:=0 assign at start of ODE
    val timed = baseVar == "t" && varIndex.contains(2) && value.intApprox == 0
    // actuate and reset buffer if all variables have been assigned
    if (timed) {
      val inP: Pointer = waaInP
      val outP: Pointer = Pointer.NULL;//new Memory(0)
      for ((x,i) <- ctrlVars.zipWithIndex) {
        val theInt = toInt(ctrlBuf(x))
        inP.setInt(i*4,theInt)
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
    val intP: Memory = new Memory(intArgs.length * 4)
    for((c,i) <- str.toCharArray.zipWithIndex) {
      strP.setByte(i,c.toByte)
    }
    strP.setByte(str.length, 0)
    for((n,i) <- intArgs.zipWithIndex) {
      intP.setInt(4*i, n)
    }
    if (logWriter != null) {
      logWriter.flush()
      logWriter.close()
    }
    val file = new File(str)
    logWriter = new BufferedWriter(new FileWriter(file))
    if(PRINT_EVENTS)
      println(s"initDone")
    if(PRINT_EVENTS)
      println(s"init:$str, $intArgs")
    ffis.ffiinit(strP, str.length, intP, intArgs.length * 4)
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
    List(Variable("t"), Variable("v")),   // assign. in AngelSandbox, v is just an initial value
    env, filePath, intArgs)

class GoPiGoAngelSandboxStrategy[number <: Numeric[number, Ternary]](ffis: VeriPhyFFIs, env: Environment[number], filePath: String, intArgs: List[Int])
  extends FFIBasicStrategy[number](ffis,
    List(Variable("V"), Variable("eps")), // const
    List(Variable("d"), Variable("t")),   // read
    List(Variable("vCand"), Variable("t"), Variable("v")),   // assign. in AngelSandbox, v is just an initial value
    env, filePath, intArgs)

class GoPiGoTimedAngelControlStrategy[number <: Numeric[number, Ternary]](ffis: VeriPhyFFIs, env: Environment[number], filePath: String, intArgs: List[Int])
  extends FFIBasicStrategy[number](ffis,
    List(Variable("V"), Variable("eps")), // const
    List(Variable("d"), Variable("t")),   // read
    List(Variable("time"), Variable("t"), Variable("v")),   // assign. in AngelSandbox, v is just an initial value
    env, filePath, intArgs)

class GoPiGoReachAvoidStrategy[number <: Numeric[number, Ternary]](ffis: VeriPhyFFIs, env: Environment[number], filePath: String, intArgs: List[Int])
  extends FFIBasicStrategy[number](ffis,
    List(Variable("V"), Variable("eps")), // const
    List(Variable("d"), Variable("t")),   // read
    List(Variable("pos"), Variable("t"), Variable("v")),   // assign. in AngelSandbox, v is just an initial value
    env, filePath, intArgs)

object BotCommon {
  // source model
  val sandboxPLDIModel: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  {?(d >= eps*V); v:=*; ?(0<=v & v<=V); ++ v:=0;}
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps); & !(d >= v*(eps-t));};}
      |  !brk:(inv());
      | }*
      | !(d >= 0);
      |""".stripMargin

  // Generated from model but then modified by hand.
  val sandboxPLDIStratString: String = "SCompose(SAssignAny(eps_0),SAssignAny(v_0),SAssignAny(d_0),SAssignAny(V_0),SAssignAny(t_0),SCompose(STest(d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose(SAssign(t_1,t_0),SAssign(v_1,v_0),SAssign(d_1,d_0)),SLoop(SCompose(SChoice(SCompose(STest(d_1>=eps_0*V_0),SAssignAny(v_2),STest(0<=v_2&v_2<=V_0)),SAssign(v_2,0)),SAssign(t_2,0),SCompose(SAssign(t_3,t_2),SAssign(d_2,d_1)),SCompose(STest(t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny(t_3),SAssignAny(d_2),SAssignAny(t_3),STest(t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign(d_2',-v_2),SAssign(t_3',1)),SCompose(SAssign(t_1,t_3),SAssign(v_1,v_2),SAssign(d_1,d_2))))))"

  val noSandbox1DBotModel: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  switch {
      |    case (d>=eps*V) => v:=*; ?(0<=v&v<=V);
      |    case (true) => v:=0;
      |  }
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps); & !(d >= v*(eps-t));};}
      |  !brk:(inv());
      | }*
      | !(d >= 0);
      |""".stripMargin

  val noSandbox1DStratString: String = "SCompose(SAssignAny(eps_0),SAssignAny(v_0),SAssignAny(d_0),SAssignAny(V_0),SAssignAny(t_0),SCompose(STest(d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose(SAssign(t_1,t_0),SAssign(v_1,v_0),SAssign(d_1,d_0)),SLoop(SCompose(SChoice(SCompose(STest(d_1>=eps_0*V_0),SCompose(SAssignAny(v_2),STest(0<=v_2&v_2<=V_0))),SAssign(v_2,0)),SAssign(t_2,0),SCompose(SAssign(t_3,t_2),SAssign(d_2,d_1)),SCompose(STest(t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny(t_3),SAssignAny(d_2),SAssignAny(t_3),STest(t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign(d_2',-v_2),SAssign(t_3',1)),SCompose(SAssign(t_1,t_3),SAssign(v_1,v_2),SAssign(d_1,d_2))))))"

  val angelSandbox1DBotModel: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  vCand :=*;
      |  switch {
      |    case (d>=eps*V & 0 <=vCand & vCand <= V) => v:=vCand;
      |    case (true) => v:=0;
      |  }
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps); & !(d >= v*(eps-t));};}
      |  !brk:(inv());
      | }*
      | !(d >= 0);
      |""".stripMargin

  val angelSandbox1DStratString: String = "SCompose[64](SAssignAny[44](vCand_0),SAssignAny[45](eps_0),SAssignAny[46](v_0),SAssignAny[47](d_0),SAssignAny[48](V_0),SAssignAny[49](t_0),SCompose[63](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[51](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](vCand_1,vCand_0),SAssign[9](d_1,d_0)),SLoop[62](SCompose[61](SAssignAny[12](vCand_2),SChoice[57](SCompose[53](STest[52](d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0),SAssign[13](v_2,vCand_2)),SAssign[14](v_2,0)),SAssign[16](t_2,0),SCompose[58](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[59](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[60](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2))))))"
  val angelSandbox1DIDMap: String = "0|->STest[0](true)\n1|->STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0)\n2|->STest[2](true)\n3|->SAssign[3](t_1,t_0)\n4|->STest[4](true)\n5|->SAssign[5](v_1,v_0)\n6|->STest[6](true)\n7|->SAssign[7](vCand_1,vCand_0)\n8|->STest[8](true)\n9|->SAssign[9](d_1,d_0)\n10|->STest[10](true)\n11|->SCompose[11](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](vCand_1,vCand_0),SAssign[9](d_1,d_0))\n12|->SAssignAny[12](vCand_2)\n13|->SAssign[13](v_2,vCand_2)\n14|->SAssign[14](v_2,0)\n15|->ASwitch[15]((d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0, SAssign[13](v_2,vCand_2)),(true, SAssign[14](v_2,0)))\n16|->SAssign[16](t_2,0)\n17|->SAssign[17](t_3,t_2)\n18|->STest[18](true)\n19|->SAssign[19](d_2,d_1)\n20|->STest[20](true)\n21|->SCompose[21](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1))\n22|->SAssignAny[22](t_3)\n23|->SAssignAny[23](d_2)\n24|->SAssignAny[24](t_3)\n25|->SAssign[25](d_2',-v_2)\n26|->SAssign[26](t_3',1)\n27|->STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3))\n28|->STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3))\n29|->SCompose[29](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1))\n30|->STest[30](true)\n31|->SAssign[31](t_1,t_3)\n32|->STest[32](true)\n33|->SAssign[33](v_1,v_2)\n34|->STest[34](true)\n35|->SAssign[35](vCand_1,vCand_2)\n36|->STest[36](true)\n37|->SAssign[37](d_1,d_2)\n38|->STest[38](true)\n39|->SCompose[39](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2))\n40|->SCompose[40](SAssignAny[12](vCand_2),ASwitch[15]((d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0, SAssign[13](v_2,vCand_2)),(true, SAssign[14](v_2,0))),SAssign[16](t_2,0),SCompose[21](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[29](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[39](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2)))\n41|->SLoop[41](SCompose[40](SAssignAny[12](vCand_2),ASwitch[15]((d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0, SAssign[13](v_2,vCand_2)),(true, SAssign[14](v_2,0))),SAssign[16](t_2,0),SCompose[21](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[29](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[39](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2))))\n42|->STest[42](true)\n43|->SCompose[43](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[11](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](vCand_1,vCand_0),SAssign[9](d_1,d_0)),SLoop[41](SCompose[40](SAssignAny[12](vCand_2),ASwitch[15]((d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0, SAssign[13](v_2,vCand_2)),(true, SAssign[14](v_2,0))),SAssign[16](t_2,0),SCompose[21](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[29](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[39](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2)))))\n44|->SAssignAny[44](vCand_0)\n45|->SAssignAny[45](eps_0)\n46|->SAssignAny[46](v_0)\n47|->SAssignAny[47](d_0)\n48|->SAssignAny[48](V_0)\n49|->SAssignAny[49](t_0)\n50|->SCompose[50](SAssignAny[44](vCand_0),SAssignAny[45](eps_0),SAssignAny[46](v_0),SAssignAny[47](d_0),SAssignAny[48](V_0),SAssignAny[49](t_0),SCompose[43](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[11](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](vCand_1,vCand_0),SAssign[9](d_1,d_0)),SLoop[41](SCompose[40](SAssignAny[12](vCand_2),ASwitch[15]((d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0, SAssign[13](v_2,vCand_2)),(true, SAssign[14](v_2,0))),SAssign[16](t_2,0),SCompose[21](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[29](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[39](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2))))))\n51|->SCompose[51](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](vCand_1,vCand_0),SAssign[9](d_1,d_0))\n52|->STest[52](d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0)\n53|->SCompose[53](STest[52](d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0),SAssign[13](v_2,vCand_2))\n54|->STest[54](true)\n55|->ASwitch[55]((true, SAssign[14](v_2,0)))\n56|->ASwitch[56]((d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0, SAssign[13](v_2,vCand_2)),(true, SAssign[14](v_2,0)))\n57|->SChoice[57](SCompose[53](STest[52](d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0),SAssign[13](v_2,vCand_2)),SAssign[14](v_2,0))\n58|->SCompose[58](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1))\n59|->SCompose[59](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1))\n60|->SCompose[60](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2))\n61|->SCompose[61](SAssignAny[12](vCand_2),SChoice[57](SCompose[53](STest[52](d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0),SAssign[13](v_2,vCand_2)),SAssign[14](v_2,0)),SAssign[16](t_2,0),SCompose[58](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[59](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[60](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2)))\n62|->SLoop[62](SCompose[61](SAssignAny[12](vCand_2),SChoice[57](SCompose[53](STest[52](d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0),SAssign[13](v_2,vCand_2)),SAssign[14](v_2,0)),SAssign[16](t_2,0),SCompose[58](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[59](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[60](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2))))\n63|->SCompose[63](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[51](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](vCand_1,vCand_0),SAssign[9](d_1,d_0)),SLoop[62](SCompose[61](SAssignAny[12](vCand_2),SChoice[57](SCompose[53](STest[52](d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0),SAssign[13](v_2,vCand_2)),SAssign[14](v_2,0)),SAssign[16](t_2,0),SCompose[58](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[59](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[60](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2)))))\n64|->SCompose[64](SAssignAny[44](vCand_0),SAssignAny[45](eps_0),SAssignAny[46](v_0),SAssignAny[47](d_0),SAssignAny[48](V_0),SAssignAny[49](t_0),SCompose[63](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[51](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](vCand_1,vCand_0),SAssign[9](d_1,d_0)),SLoop[62](SCompose[61](SAssignAny[12](vCand_2),SChoice[57](SCompose[53](STest[52](d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0),SAssign[13](v_2,vCand_2)),SAssign[14](v_2,0)),SAssign[16](t_2,0),SCompose[58](SAssign[17](t_3,t_2),SAssign[19](d_2,d_1)),SCompose[59](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1)),SCompose[60](SAssign[31](t_1,t_3),SAssign[33](v_1,v_2),SAssign[35](vCand_1,vCand_2),SAssign[37](d_1,d_2))))))"
  val angelSandbox1DOriginMap: String = "3|->STest[4](true)\n5|->STest[6](true)\n7|->STest[8](true)\n9|->STest[10](true)\n17|->STest[18](true)\n19|->STest[20](true)\n29|->SCompose[29](STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[22](t_3),SAssignAny[23](d_2),SAssignAny[24](t_3),STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[25](d_2',-v_2),SAssign[26](t_3',1))\n31|->STest[32](true)\n33|->STest[34](true)\n35|->STest[36](true)\n37|->STest[38](true)\n57|->ASwitch[56]((d_1>=eps_0*V_0&0<=vCand_2&vCand_2<=V_0, SAssign[13](v_2,vCand_2)),(true, SAssign[14](v_2,0)))"

  val noStar1DBotModel: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  switch {
      |    case (d>=eps*V) => v:=V; ?(0<=v&v<=V);
      |    case (true) => v:=0;
      |  }
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps); & !(d >= v*(eps-t));};}
      |  !brk:(inv());
      | }*
      | !(d >= 0);
      |""".stripMargin

  val noStar1DStratString: String = "SCompose[61](SAssignAny[41](eps_0),SAssignAny[42](v_0),SAssignAny[43](d_0),SAssignAny[44](V_0),SAssignAny[45](t_0),SCompose[60](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[47](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](d_1,d_0)),SLoop[59](SCompose[58](SChoice[54](SCompose[50](STest[48](d_1>=eps_0*V_0),SCompose[49](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),SAssign[13](v_2,0)),SAssign[15](t_2,0),SCompose[55](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[56](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[57](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2))))))"
  val noStar1DIDMap: String = "0|->STest[0](true)\n1|->STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0)\n2|->STest[2](true)\n3|->SAssign[3](t_1,t_0)\n4|->STest[4](true)\n5|->SAssign[5](v_1,v_0)\n6|->STest[6](true)\n7|->SAssign[7](d_1,d_0)\n8|->STest[8](true)\n9|->SCompose[9](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](d_1,d_0))\n10|->SAssign[10](v_2,V_0)\n11|->STest[11](0<=v_2&v_2<=V_0)\n12|->SCompose[12](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))\n13|->SAssign[13](v_2,0)\n14|->ASwitch[14]((d_1>=eps_0*V_0, SCompose[12](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),(true, SAssign[13](v_2,0)))\n15|->SAssign[15](t_2,0)\n16|->SAssign[16](t_3,t_2)\n17|->STest[17](true)\n18|->SAssign[18](d_2,d_1)\n19|->STest[19](true)\n20|->SCompose[20](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1))\n21|->SAssignAny[21](t_3)\n22|->SAssignAny[22](d_2)\n23|->SAssignAny[23](t_3)\n24|->SAssign[24](d_2',-v_2)\n25|->SAssign[25](t_3',1)\n26|->STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3))\n27|->STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3))\n28|->SCompose[28](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1))\n29|->STest[29](true)\n30|->SAssign[30](t_1,t_3)\n31|->STest[31](true)\n32|->SAssign[32](v_1,v_2)\n33|->STest[33](true)\n34|->SAssign[34](d_1,d_2)\n35|->STest[35](true)\n36|->SCompose[36](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2))\n37|->SCompose[37](ASwitch[14]((d_1>=eps_0*V_0, SCompose[12](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),(true, SAssign[13](v_2,0))),SAssign[15](t_2,0),SCompose[20](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[28](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[36](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2)))\n38|->SLoop[38](SCompose[37](ASwitch[14]((d_1>=eps_0*V_0, SCompose[12](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),(true, SAssign[13](v_2,0))),SAssign[15](t_2,0),SCompose[20](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[28](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[36](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2))))\n39|->STest[39](true)\n40|->SCompose[40](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[9](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](d_1,d_0)),SLoop[38](SCompose[37](ASwitch[14]((d_1>=eps_0*V_0, SCompose[12](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),(true, SAssign[13](v_2,0))),SAssign[15](t_2,0),SCompose[20](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[28](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[36](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2)))))\n41|->SAssignAny[41](eps_0)\n42|->SAssignAny[42](v_0)\n43|->SAssignAny[43](d_0)\n44|->SAssignAny[44](V_0)\n45|->SAssignAny[45](t_0)\n46|->SCompose[46](SAssignAny[41](eps_0),SAssignAny[42](v_0),SAssignAny[43](d_0),SAssignAny[44](V_0),SAssignAny[45](t_0),SCompose[40](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[9](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](d_1,d_0)),SLoop[38](SCompose[37](ASwitch[14]((d_1>=eps_0*V_0, SCompose[12](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),(true, SAssign[13](v_2,0))),SAssign[15](t_2,0),SCompose[20](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[28](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[36](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2))))))\n47|->SCompose[47](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](d_1,d_0))\n48|->STest[48](d_1>=eps_0*V_0)\n49|->SCompose[49](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))\n50|->SCompose[50](STest[48](d_1>=eps_0*V_0),SCompose[49](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0)))\n51|->STest[51](true)\n52|->ASwitch[52]((true, SAssign[13](v_2,0)))\n53|->ASwitch[53]((d_1>=eps_0*V_0, SCompose[12](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),(true, SAssign[13](v_2,0)))\n54|->SChoice[54](SCompose[50](STest[48](d_1>=eps_0*V_0),SCompose[49](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),SAssign[13](v_2,0))\n55|->SCompose[55](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1))\n56|->SCompose[56](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1))\n57|->SCompose[57](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2))\n58|->SCompose[58](SChoice[54](SCompose[50](STest[48](d_1>=eps_0*V_0),SCompose[49](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),SAssign[13](v_2,0)),SAssign[15](t_2,0),SCompose[55](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[56](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[57](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2)))\n59|->SLoop[59](SCompose[58](SChoice[54](SCompose[50](STest[48](d_1>=eps_0*V_0),SCompose[49](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),SAssign[13](v_2,0)),SAssign[15](t_2,0),SCompose[55](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[56](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[57](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2))))\n60|->SCompose[60](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[47](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](d_1,d_0)),SLoop[59](SCompose[58](SChoice[54](SCompose[50](STest[48](d_1>=eps_0*V_0),SCompose[49](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),SAssign[13](v_2,0)),SAssign[15](t_2,0),SCompose[55](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[56](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[57](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2)))))\n61|->SCompose[61](SAssignAny[41](eps_0),SAssignAny[42](v_0),SAssignAny[43](d_0),SAssignAny[44](V_0),SAssignAny[45](t_0),SCompose[60](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[47](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](d_1,d_0)),SLoop[59](SCompose[58](SChoice[54](SCompose[50](STest[48](d_1>=eps_0*V_0),SCompose[49](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),SAssign[13](v_2,0)),SAssign[15](t_2,0),SCompose[55](SAssign[16](t_3,t_2),SAssign[18](d_2,d_1)),SCompose[56](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1)),SCompose[57](SAssign[30](t_1,t_3),SAssign[32](v_1,v_2),SAssign[34](d_1,d_2))))))"
  val noStar1DOriginMap: String = "3|->STest[4](true)\n5|->STest[6](true)\n7|->STest[8](true)\n16|->STest[17](true)\n18|->STest[19](true)\n28|->SCompose[28](STest[26](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[21](t_3),SAssignAny[22](d_2),SAssignAny[23](t_3),STest[27](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[24](d_2',-v_2),SAssign[25](t_3',1))\n30|->STest[31](true)\n32|->STest[33](true)\n34|->STest[35](true)\n54|->ASwitch[53]((d_1>=eps_0*V_0, SCompose[12](SAssign[10](v_2,V_0),STest[11](0<=v_2&v_2<=V_0))),(true, SAssign[13](v_2,0)))"

  val timedAngelControl1DModel: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | for (time := 0; ?(time <= 10000); time := (time + 600);) {
      |  switch {
      |    case (d>=eps*V) => v:=V; ?(0<=v&v<=V);
      |    case (true) => v:=0;
      |  }
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps); & !(d >= v*(eps-t));};}
      |  !brk:(inv());
      | }
      | !(d >= 0);
      |""".stripMargin
  val timedAngelControl1DStratString: String = "SCompose[70](SAssignAny[43](eps_0),SAssignAny[44](v_0),SAssignAny[45](d_0),SAssignAny[46](time_0),SAssignAny[47](V_0),SAssignAny[48](t_0),SCompose[69](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[50](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](time_1,time_0),SAssign[9](d_1,d_0)),SCompose[68](SAssign[66](time_1,0),SLoop[65](SCompose[64](STest[51](time_1<=10000),SCompose[62](SChoice[58](SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[15](v_2,0)),SAssign[17](t_2,0),SCompose[59](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[60](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[61](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),SAssign[63](time_1,time_1+600))),STest[67](!time_1<=10000))))"
  val timedAngelControl1DIDMap: String = "0|->STest[0](true)\n1|->STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0)\n2|->STest[2](true)\n3|->SAssign[3](t_1,t_0)\n4|->STest[4](true)\n5|->SAssign[5](v_1,v_0)\n6|->STest[6](true)\n7|->SAssign[7](time_1,time_0)\n8|->STest[8](true)\n9|->SAssign[9](d_1,d_0)\n10|->STest[10](true)\n11|->SCompose[11](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](time_1,time_0),SAssign[9](d_1,d_0))\n12|->SAssign[12](v_2,V_0)\n13|->STest[13](0<=v_2&v_2<=V_0)\n14|->SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))\n15|->SAssign[15](v_2,0)\n16|->ASwitch[16]((d_1>=eps_0*V_0, SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[15](v_2,0)))\n17|->SAssign[17](t_2,0)\n18|->SAssign[18](t_3,t_2)\n19|->STest[19](true)\n20|->SAssign[20](d_2,d_1)\n21|->STest[21](true)\n22|->SCompose[22](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1))\n23|->SAssignAny[23](t_3)\n24|->SAssignAny[24](d_2)\n25|->SAssignAny[25](t_3)\n26|->SAssign[26](d_2',-v_2)\n27|->SAssign[27](t_3',1)\n28|->STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3))\n29|->STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3))\n30|->SCompose[30](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1))\n31|->STest[31](true)\n32|->SAssign[32](t_1,t_3)\n33|->STest[33](true)\n34|->SAssign[34](v_1,v_2)\n35|->STest[35](true)\n36|->SAssign[36](d_1,d_2)\n37|->STest[37](true)\n38|->SCompose[38](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))\n39|->SCompose[39](ASwitch[16]((d_1>=eps_0*V_0, SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[15](v_2,0))),SAssign[17](t_2,0),SCompose[22](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[30](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[38](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2)))\n40|->AForLoop[40](time_1,0,time_1<=10000,SCompose[39](ASwitch[16]((d_1>=eps_0*V_0, SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[15](v_2,0))),SAssign[17](t_2,0),SCompose[22](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[30](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[38](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),time_1+600)\n41|->STest[41](true)\n42|->SCompose[42](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[11](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](time_1,time_0),SAssign[9](d_1,d_0)),AForLoop[40](time_1,0,time_1<=10000,SCompose[39](ASwitch[16]((d_1>=eps_0*V_0, SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[15](v_2,0))),SAssign[17](t_2,0),SCompose[22](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[30](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[38](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),time_1+600))\n43|->SAssignAny[43](eps_0)\n44|->SAssignAny[44](v_0)\n45|->SAssignAny[45](d_0)\n46|->SAssignAny[46](time_0)\n47|->SAssignAny[47](V_0)\n48|->SAssignAny[48](t_0)\n49|->SCompose[49](SAssignAny[43](eps_0),SAssignAny[44](v_0),SAssignAny[45](d_0),SAssignAny[46](time_0),SAssignAny[47](V_0),SAssignAny[48](t_0),SCompose[42](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[11](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](time_1,time_0),SAssign[9](d_1,d_0)),AForLoop[40](time_1,0,time_1<=10000,SCompose[39](ASwitch[16]((d_1>=eps_0*V_0, SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[15](v_2,0))),SAssign[17](t_2,0),SCompose[22](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[30](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[38](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),time_1+600)))\n50|->SCompose[50](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](time_1,time_0),SAssign[9](d_1,d_0))\n51|->STest[51](time_1<=10000)\n52|->STest[52](d_1>=eps_0*V_0)\n53|->SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))\n54|->SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0)))\n55|->STest[55](true)\n56|->ASwitch[56]((true, SAssign[15](v_2,0)))\n57|->ASwitch[57]((d_1>=eps_0*V_0, SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[15](v_2,0)))\n58|->SChoice[58](SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[15](v_2,0))\n59|->SCompose[59](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1))\n60|->SCompose[60](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1))\n61|->SCompose[61](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))\n62|->SCompose[62](SChoice[58](SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[15](v_2,0)),SAssign[17](t_2,0),SCompose[59](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[60](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[61](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2)))\n63|->SAssign[63](time_1,time_1+600)\n64|->SCompose[64](STest[51](time_1<=10000),SCompose[62](SChoice[58](SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[15](v_2,0)),SAssign[17](t_2,0),SCompose[59](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[60](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[61](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),SAssign[63](time_1,time_1+600))\n65|->SLoop[65](SCompose[64](STest[51](time_1<=10000),SCompose[62](SChoice[58](SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[15](v_2,0)),SAssign[17](t_2,0),SCompose[59](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[60](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[61](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),SAssign[63](time_1,time_1+600)))\n66|->SAssign[66](time_1,0)\n67|->STest[67](!time_1<=10000)\n68|->SCompose[68](SAssign[66](time_1,0),SLoop[65](SCompose[64](STest[51](time_1<=10000),SCompose[62](SChoice[58](SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[15](v_2,0)),SAssign[17](t_2,0),SCompose[59](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[60](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[61](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),SAssign[63](time_1,time_1+600))),STest[67](!time_1<=10000))\n69|->SCompose[69](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[50](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](time_1,time_0),SAssign[9](d_1,d_0)),SCompose[68](SAssign[66](time_1,0),SLoop[65](SCompose[64](STest[51](time_1<=10000),SCompose[62](SChoice[58](SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[15](v_2,0)),SAssign[17](t_2,0),SCompose[59](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[60](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[61](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),SAssign[63](time_1,time_1+600))),STest[67](!time_1<=10000)))\n70|->SCompose[70](SAssignAny[43](eps_0),SAssignAny[44](v_0),SAssignAny[45](d_0),SAssignAny[46](time_0),SAssignAny[47](V_0),SAssignAny[48](t_0),SCompose[69](STest[1](d_0>=0&V_0>=0&eps_0>=0&v_0=0&t_0=0),SCompose[50](SAssign[3](t_1,t_0),SAssign[5](v_1,v_0),SAssign[7](time_1,time_0),SAssign[9](d_1,d_0)),SCompose[68](SAssign[66](time_1,0),SLoop[65](SCompose[64](STest[51](time_1<=10000),SCompose[62](SChoice[58](SCompose[54](STest[52](d_1>=eps_0*V_0),SCompose[53](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[15](v_2,0)),SAssign[17](t_2,0),SCompose[59](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[60](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[61](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),SAssign[63](time_1,time_1+600))),STest[67](!time_1<=10000))))"
  val timedAngelControl1DOriginMap: String = "3|->STest[4](true)\n5|->STest[6](true)\n7|->STest[8](true)\n9|->STest[10](true)\n18|->STest[19](true)\n20|->STest[21](true)\n30|->SCompose[30](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1))\n32|->STest[33](true)\n34|->STest[35](true)\n36|->STest[37](true)\n58|->ASwitch[57]((d_1>=eps_0*V_0, SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[15](v_2,0)))\n65|->AForLoop[40](time_1,0,time_1<=10000,SCompose[39](ASwitch[16]((d_1>=eps_0*V_0, SCompose[14](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[15](v_2,0))),SAssign[17](t_2,0),SCompose[22](SAssign[18](t_3,t_2),SAssign[20](d_2,d_1)),SCompose[30](STest[28](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[23](t_3),SAssignAny[24](d_2),SAssignAny[25](t_3),STest[29](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[26](d_2',-v_2),SAssign[27](t_3',1)),SCompose[38](SAssign[32](t_1,t_3),SAssign[34](v_1,v_2),SAssign[36](d_1,d_2))),time_1+600)"

  val reachAvoid1DBotModel: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?inits:(d >= 0 & V > 0 & eps > 0 & v=0 & t=0);
      | !(inv());
      | init:
      | for (pos := 0;
      |    !conv:( d >= 0);
      |    ?guard:(pos <= d@init & d >= V*eps);
      |    pos := pos + V*eps/2) {
      |  switch {
      |    case (d>=eps*V) => v:=V; ?(0<=v&v<=V); !vSgn:(v>=0);
      |    case (true) => v:=0;  !vSgn:(v>=0);
      |  }
      |  {t := 0; {d' = -v, t' = 1 & ?tUp:(t <= eps); & !dLo:(d >= v*(eps-t));};}
      |  !conv:(d >= 0) using vSgn tUp dLo inits by auto;
      |  /*!brk:(inv()); */
      | }
      | !(d >= 0);
      |""".stripMargin

  val reachAvoid1DStratString: String = "SCompose[72](SAssignAny[45](eps_0),SAssignAny[46](pos_0),SAssignAny[47](v_0),SAssignAny[48](d_0),SAssignAny[49](V_0),SAssignAny[50](t_0),SCompose[71](STest[1](d_0>=0&V_0>0&eps_0>0&v_0=0&t_0=0),SCompose[52](SAssign[3](t_1,t_0),SAssign[5](pos_1,pos_0),SAssign[7](v_1,v_0),SAssign[9](d_1,d_0)),SCompose[70](SAssign[68](pos_1,0),SLoop[67](SCompose[66](STest[53](pos_1<=d_0&d_1>=V_0*eps_0),SCompose[64](SChoice[60](SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[16](v_2,0)),SAssign[19](t_2,0),SCompose[61](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[62](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[63](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),SAssign[65](pos_1,pos_1+V_0*eps_0/2))),STest[69](!(pos_1<=d_0&d_1>=V_0*eps_0)))))"
  val reachAvoid1DIDMap: String = "0|->STest[0](true)\n1|->STest[1](d_0>=0&V_0>0&eps_0>0&v_0=0&t_0=0)\n2|->STest[2](true)\n3|->SAssign[3](t_1,t_0)\n4|->STest[4](true)\n5|->SAssign[5](pos_1,pos_0)\n6|->STest[6](true)\n7|->SAssign[7](v_1,v_0)\n8|->STest[8](true)\n9|->SAssign[9](d_1,d_0)\n10|->STest[10](true)\n11|->SCompose[11](SAssign[3](t_1,t_0),SAssign[5](pos_1,pos_0),SAssign[7](v_1,v_0),SAssign[9](d_1,d_0))\n12|->SAssign[12](v_2,V_0)\n13|->STest[13](0<=v_2&v_2<=V_0)\n14|->STest[14](true)\n15|->SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))\n16|->SAssign[16](v_2,0)\n17|->STest[17](true)\n18|->ASwitch[18]((d_1>=eps_0*V_0, SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[16](v_2,0)))\n19|->SAssign[19](t_2,0)\n20|->SAssign[20](t_3,t_2)\n21|->STest[21](true)\n22|->SAssign[22](d_2,d_1)\n23|->STest[23](true)\n24|->SCompose[24](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1))\n25|->SAssignAny[25](t_3)\n26|->SAssignAny[26](d_2)\n27|->SAssignAny[27](t_3)\n28|->SAssign[28](d_2',-v_2)\n29|->SAssign[29](t_3',1)\n30|->STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3))\n31|->STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3))\n32|->SCompose[32](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1))\n33|->STest[33](true)\n34|->SAssign[34](t_1,t_3)\n35|->STest[35](true)\n36|->SAssign[36](v_1,v_2)\n37|->STest[37](true)\n38|->SAssign[38](d_1,d_2)\n39|->STest[39](true)\n40|->SCompose[40](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))\n41|->SCompose[41](ASwitch[18]((d_1>=eps_0*V_0, SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[16](v_2,0))),SAssign[19](t_2,0),SCompose[24](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[32](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[40](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2)))\n42|->AForLoop[42](pos_1,0,pos_1<=d_0&d_1>=V_0*eps_0,SCompose[41](ASwitch[18]((d_1>=eps_0*V_0, SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[16](v_2,0))),SAssign[19](t_2,0),SCompose[24](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[32](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[40](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),pos_1+V_0*eps_0/2)\n43|->STest[43](true)\n44|->SCompose[44](STest[1](d_0>=0&V_0>0&eps_0>0&v_0=0&t_0=0),SCompose[11](SAssign[3](t_1,t_0),SAssign[5](pos_1,pos_0),SAssign[7](v_1,v_0),SAssign[9](d_1,d_0)),AForLoop[42](pos_1,0,pos_1<=d_0&d_1>=V_0*eps_0,SCompose[41](ASwitch[18]((d_1>=eps_0*V_0, SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[16](v_2,0))),SAssign[19](t_2,0),SCompose[24](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[32](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[40](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),pos_1+V_0*eps_0/2))\n45|->SAssignAny[45](eps_0)\n46|->SAssignAny[46](pos_0)\n47|->SAssignAny[47](v_0)\n48|->SAssignAny[48](d_0)\n49|->SAssignAny[49](V_0)\n50|->SAssignAny[50](t_0)\n51|->SCompose[51](SAssignAny[45](eps_0),SAssignAny[46](pos_0),SAssignAny[47](v_0),SAssignAny[48](d_0),SAssignAny[49](V_0),SAssignAny[50](t_0),SCompose[44](STest[1](d_0>=0&V_0>0&eps_0>0&v_0=0&t_0=0),SCompose[11](SAssign[3](t_1,t_0),SAssign[5](pos_1,pos_0),SAssign[7](v_1,v_0),SAssign[9](d_1,d_0)),AForLoop[42](pos_1,0,pos_1<=d_0&d_1>=V_0*eps_0,SCompose[41](ASwitch[18]((d_1>=eps_0*V_0, SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[16](v_2,0))),SAssign[19](t_2,0),SCompose[24](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[32](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[40](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),pos_1+V_0*eps_0/2)))\n52|->SCompose[52](SAssign[3](t_1,t_0),SAssign[5](pos_1,pos_0),SAssign[7](v_1,v_0),SAssign[9](d_1,d_0))\n53|->STest[53](pos_1<=d_0&d_1>=V_0*eps_0)\n54|->STest[54](d_1>=eps_0*V_0)\n55|->SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))\n56|->SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0)))\n57|->STest[57](true)\n58|->ASwitch[58]((true, SAssign[16](v_2,0)))\n59|->ASwitch[59]((d_1>=eps_0*V_0, SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[16](v_2,0)))\n60|->SChoice[60](SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[16](v_2,0))\n61|->SCompose[61](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1))\n62|->SCompose[62](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1))\n63|->SCompose[63](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))\n64|->SCompose[64](SChoice[60](SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[16](v_2,0)),SAssign[19](t_2,0),SCompose[61](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[62](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[63](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2)))\n65|->SAssign[65](pos_1,pos_1+V_0*eps_0/2)\n66|->SCompose[66](STest[53](pos_1<=d_0&d_1>=V_0*eps_0),SCompose[64](SChoice[60](SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[16](v_2,0)),SAssign[19](t_2,0),SCompose[61](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[62](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[63](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),SAssign[65](pos_1,pos_1+V_0*eps_0/2))\n67|->SLoop[67](SCompose[66](STest[53](pos_1<=d_0&d_1>=V_0*eps_0),SCompose[64](SChoice[60](SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[16](v_2,0)),SAssign[19](t_2,0),SCompose[61](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[62](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[63](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),SAssign[65](pos_1,pos_1+V_0*eps_0/2)))\n68|->SAssign[68](pos_1,0)\n69|->STest[69](!(pos_1<=d_0&d_1>=V_0*eps_0))\n70|->SCompose[70](SAssign[68](pos_1,0),SLoop[67](SCompose[66](STest[53](pos_1<=d_0&d_1>=V_0*eps_0),SCompose[64](SChoice[60](SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[16](v_2,0)),SAssign[19](t_2,0),SCompose[61](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[62](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[63](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),SAssign[65](pos_1,pos_1+V_0*eps_0/2))),STest[69](!(pos_1<=d_0&d_1>=V_0*eps_0)))\n71|->SCompose[71](STest[1](d_0>=0&V_0>0&eps_0>0&v_0=0&t_0=0),SCompose[52](SAssign[3](t_1,t_0),SAssign[5](pos_1,pos_0),SAssign[7](v_1,v_0),SAssign[9](d_1,d_0)),SCompose[70](SAssign[68](pos_1,0),SLoop[67](SCompose[66](STest[53](pos_1<=d_0&d_1>=V_0*eps_0),SCompose[64](SChoice[60](SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[16](v_2,0)),SAssign[19](t_2,0),SCompose[61](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[62](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[63](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),SAssign[65](pos_1,pos_1+V_0*eps_0/2))),STest[69](!(pos_1<=d_0&d_1>=V_0*eps_0))))\n72|->SCompose[72](SAssignAny[45](eps_0),SAssignAny[46](pos_0),SAssignAny[47](v_0),SAssignAny[48](d_0),SAssignAny[49](V_0),SAssignAny[50](t_0),SCompose[71](STest[1](d_0>=0&V_0>0&eps_0>0&v_0=0&t_0=0),SCompose[52](SAssign[3](t_1,t_0),SAssign[5](pos_1,pos_0),SAssign[7](v_1,v_0),SAssign[9](d_1,d_0)),SCompose[70](SAssign[68](pos_1,0),SLoop[67](SCompose[66](STest[53](pos_1<=d_0&d_1>=V_0*eps_0),SCompose[64](SChoice[60](SCompose[56](STest[54](d_1>=eps_0*V_0),SCompose[55](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),SAssign[16](v_2,0)),SAssign[19](t_2,0),SCompose[61](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[62](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[63](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),SAssign[65](pos_1,pos_1+V_0*eps_0/2))),STest[69](!(pos_1<=d_0&d_1>=V_0*eps_0)))))"
  val reachAvoid1DOriginMap: String = "3|->STest[4](true)\n5|->STest[6](true)\n7|->STest[8](true)\n9|->STest[10](true)\n20|->STest[21](true)\n22|->STest[23](true)\n32|->SCompose[32](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1))\n34|->STest[35](true)\n36|->STest[37](true)\n38|->STest[39](true)\n60|->ASwitch[59]((d_1>=eps_0*V_0, SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[16](v_2,0)))\n67|->AForLoop[42](pos_1,0,pos_1<=d_0&d_1>=V_0*eps_0,SCompose[41](ASwitch[18]((d_1>=eps_0*V_0, SCompose[15](SAssign[12](v_2,V_0),STest[13](0<=v_2&v_2<=V_0))),(true, SAssign[16](v_2,0))),SAssign[19](t_2,0),SCompose[24](SAssign[20](t_3,t_2),SAssign[22](d_2,d_1)),SCompose[32](STest[30](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssignAny[25](t_3),SAssignAny[26](d_2),SAssignAny[27](t_3),STest[31](t_3>=0&t_3<=eps_0&d_2>=v_2*(eps_0-t_3)),SAssign[28](d_2',-v_2),SAssign[29](t_3',1)),SCompose[40](SAssign[34](t_1,t_3),SAssign[36](v_1,v_2),SAssign[38](d_1,d_2))),pos_1+V_0*eps_0/2)"


  case class StrategyBundle(stratString: String, idMapString: String, originMapString: String)

  val noStarBundle: StrategyBundle = StrategyBundle(stratString = noStar1DStratString, idMapString = noStar1DIDMap, originMapString = noStar1DOriginMap)
  val angelSandboxBundle: StrategyBundle = StrategyBundle(stratString = angelSandbox1DStratString, idMapString = angelSandbox1DIDMap, originMapString = angelSandbox1DOriginMap)
  val timedAngelControlBundle: StrategyBundle = StrategyBundle(stratString = timedAngelControl1DStratString, idMapString = timedAngelControl1DIDMap, originMapString = timedAngelControl1DOriginMap)
  val reachAvoidBundle: StrategyBundle = StrategyBundle(stratString = reachAvoid1DStratString, idMapString = reachAvoid1DIDMap, originMapString = reachAvoid1DOriginMap)

  // arguments for each test
  case class SimSpec(name: String, speedFactor: Int, obstacleSpeed: Int, actuatorOffset: Int, duration: Int, initialDistance: Int, reactionTime: Int)
  case class BotSpec(name: String, speedFactor: Int, extraMessage: String)

  val botArgs: List[BotSpec] = List(
    BotSpec("correct", 1, ""),
    BotSpec("ctrlbug", -1, ""),
    BotSpec("backwards", 1, "Move obstacle towards robot while it drives\n"),
    BotSpec("forwardObstCompensatesUnsafeActoffset", 1, "Move obstacle away from robot while it drives\n")
  )

  // just test one speed for debugging purposes
  val testSpeeds: List[Int] = List(100, 150, 200, 250)

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
    SimSpec("correct", 1, 0, 0, 10, 750000, 220),
    SimSpec("ctrlbug", -1, 0, 0, 10, 750000, 220),
    SimSpec("backwards", -1, -50, 0, 10, 750000, 220),
    SimSpec("actoffsetSafe", -1, 0, -10, 10, 750000, 220),
    SimSpec("actoffsetUnsafe", -1, 0, 10, 10, 750000, 220)
  )


  def loadBundle(sb: StrategyBundle): AngelStrategy = {
    val strat = StrategyParser(sb.stratString)
    IDCounter.clear()
    IDCounter.loadIdMap(sb.idMapString)
    IDCounter.loadOriginMap(sb.originMapString)
    strat
  }

  // De one simulation and save the results to CSV
  def doOneBotSim(lib: VeriPhyFFIs, astrat: AngelStrategy, path: String, spec: SimSpec, speed: Int): Unit = {
    val filePath = path + File.separator + spec.name + speed + ".csv"
    val intArgs = List(spec.speedFactor*speed, spec.obstacleSpeed, spec.actuatorOffset, spec.duration, spec.initialDistance, spec.reactionTime)
    val factory = UnknowingFactory(RatFactory)
    val env: Environment[TernaryNumber[RatNum]] = new Environment(factory)
    val basic = new GoPiGoTimedAngelControlStrategy(lib, env, filePath, intArgs)
    val demon = new WrappedDemonStrategy(basic)(env)
    if(true)
      println("Time to interpret: " + spec.name + "," + speed)
    val interp = new Play(factory)
    try {
      interp(env, astrat, demon)
    } catch {
      // Can swallow exception because reportViolation already did the reporting
      case tfe: TestFailureException => ()
    }
    demon.exit()
    println("Final state: " + env.state)
  }

  // De one simulation and save the results to CSV
  def doOneGoPiGo(lib: VeriPhyFFIs, astrat: AngelStrategy, path: String, spec: BotSpec, speed: Int): Unit = {
    val DURATION = 10
    val EXIT_ON_VIOLATION = 0
    val filePath = path + File.separator + spec.name + speed + ".csv"
    val intArgs = List(spec.speedFactor*speed, DURATION, EXIT_ON_VIOLATION)
    println(s"Experiment: ${spec.name} with speed $speed")
    println("Please place the robot at distance ~0.75m from the obstacle, then press Enter to continue")
    println(spec.extraMessage)
    val _ = scala.io.StdIn.readLine()
    println("Starting experiment")
    val factory = UnknowingFactory(RatFactory)
    val env: Environment[TernaryNumber[RatNum]] = new Environment(factory)
    val basic = new GoPiGoAngelSandboxStrategy(lib, env, filePath, intArgs)
    val demon = new WrappedDemonStrategy(basic)(env)
    val interp = new Play(factory)
    Play.continueOnViolation = true
    try {
      interp(env, astrat, demon)
    } catch {
      // Can swallow exception because reportViolation already did the reporting
      case tfe: TestFailureException => ()
    }
    demon.exit()
    println("Final state: " + env.state)
  }

}
