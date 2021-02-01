package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import java.io.{File, RandomAccessFile}
import java.nio._
import java.nio.channels.FileChannel

import com.sun.jna._
/*import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.veriphy.experiments.ProtocolTypes._
import edu.cmu.cs.ls.keymaerax.veriphy.experiments.BotCommon._
*/

/**
  * This *PROBABLY-WINDOWS-SPECIFIC* VeriPhy wrapper uses a bidirectional named pipe to talk to a custom fork of AirSim
  * which executes our experiments.
  * At first I'm trying blocking I/O, but could try non-blocking I/O if it doesn't work out.
  *
  * The protocol has both request and response messages for each event.
  * The events proceed in the following order:
  *
  * @TODO: Check that this order of operations is correct
  * Init - happens once. Version compatibility is checked in this step.
  * GetConst happens before main body
  * Sense happens before main body
  * The following repeats:
  * HasNext checks whether we continue the loop
  * ExtCtrl gets suggested control decisions
  * Actuate tells us the actual safe control decision
  * Sense tells us new state
  *
  */
/*object ProtocolTypes {
  val currentVersion: Int = 1
  val INT_SIZE: Int = 4
  val BOOL_SIZE: Int = 1
  val BYTE_ORDER: ByteOrder = ByteOrder.LITTLE_ENDIAN

  type scalar = RatNum
}
sealed trait MessageType { val typeId: Int }
case object InitRequestMessageType      extends MessageType { val typeId: Int  = 0 }
case object InitResponseMessageType     extends MessageType { val typeId: Int  = 1 }
case object GetConstRequestMessageType  extends MessageType { val typeId: Int  = 2 }
case object GetConstResponseMessageType extends MessageType { val typeId: Int  = 3 }
case object SenseRequestMessageType     extends MessageType { val typeId: Int  = 4 }
case object SenseResponseMessageType    extends MessageType { val typeId: Int  = 5 }
case object HasNextRequestMessageType   extends MessageType { val typeId: Int  = 6 }
case object HasNextResponseMessageType  extends MessageType { val typeId: Int  = 7 }
case object ExtCtrlRequestMessageType   extends MessageType { val typeId: Int  = 8 }
case object ExtCtrlResponseMessageType  extends MessageType { val typeId: Int  = 9 }
case object ActuateRequestMessageType   extends MessageType { val typeId: Int  = 10 }
case object ActuateResponseMessageType  extends MessageType { val typeId: Int  = 11 }

object MessageType {
  def apply(typeId: Int): MessageType = {
    val theType: MessageType =
    typeId match {
      case 0 => InitRequestMessageType
      case 1 => InitResponseMessageType
      case 2 => GetConstRequestMessageType
      case 3 => GetConstResponseMessageType
      case 4 => SenseRequestMessageType
      case 5 => SenseResponseMessageType
      case 6 => HasNextRequestMessageType
      case 7 => HasNextResponseMessageType
      case 8 => ExtCtrlRequestMessageType
      case 9 => ExtCtrlResponseMessageType
      case 10 => ActuateRequestMessageType
      case 11 => ActuateResponseMessageType
      case _ => throw new Exception("Unrecognized Message ID, make sure you're following protocol and that you and client are on same version")
    }
    assert(theType.typeId == typeId)
    theType
  }
}

sealed trait Message {
  def content: Array[Byte]
  val messageType: MessageType
  protected def intsToBytes(ints: List[Int]): Array[Byte] = {
    val contentBuffer = ByteBuffer.allocate(ints.length*INT_SIZE)
    contentBuffer.order(BYTE_ORDER);
    contentBuffer.position(0)
    for (k <- ints) {
      contentBuffer.putInt(k)
    }
    contentBuffer.array()
  }
  protected def scalarsToBytes(scalars: List[scalar]): Array[Byte] = {
    val flatted = scalars.flatMap(n => List(n.n.n.toInt, n.n.d.toInt))
    intsToBytes(flatted)
  }

  def allBytes: Array[Byte] = {
    val arr = content
    val typeId = messageType.typeId
    val size = arr.length + INT_SIZE
    val bb = ByteBuffer.allocate(size + INT_SIZE)
    bb.order(BYTE_ORDER);
    bb.putInt(size)
    bb.putInt(typeId)
    bb.put(arr)
    bb.array()
  }
  def sendTo(file: RandomAccessFile): Unit = {
    println("Sending message of type: " + this.messageType)
    val bytes = allBytes
    file.write(bytes)
  }
  def coerce[T <: Message](companion: MessageCompanion[T]): T = {
    try {
      this.asInstanceOf[T]
    } catch {
      case (_:Throwable) => throw new Exception(s"Could not coerce message $this using class ${companion.getClass.toString}")
    }
  }
}
object Message {

  private def readLittleEndianInt(file: RandomAccessFile): Int = {
    val b1 = file.readByte()
    val b2 = file.readByte()
    val b3 = file.readByte()
    val b4 = file.readByte()
    val res = b1 + (b2 << 8) + (b3 << 16) + (b4 << 24)
    res
  }
  // @TODO: set a maximum size for debugging reasons
  def blockingReadFrom(file: RandomAccessFile): Message = {
    val size = readLittleEndianInt(file)
    val typeAndContent = new Array[Byte] (size)
    val theLength = file.length()
    println("Length: " + theLength)
    val nRead = file.read(typeAndContent)
    //file.readFully(typeAndContent)
    println("Amount read: " + nRead)
    ofTypeAndContent(size, typeAndContent)
  }
  // @TODO: bytes interface -> file handle interface
  def ofTypeAndContent(declaredSize: Int, bytes: Array[Byte]): Message = {
    if (bytes.length < 4) {
      throw new Exception("Message packet expected to be at least 4 bytes of type ID after packet size header")
    }
    val bb = ByteBuffer.allocate(bytes.length)
    bb.order(BYTE_ORDER);
    bb.position(0)
    bb.put(bytes)
    bb.rewind()
    if (bytes.length != declaredSize) {
      throw new Exception("Packet does not have expected size")
    }
    val gottenInt = bb.getInt()
    val messageType = MessageType(gottenInt)
    //bb.position(INT_SIZE)
    ofContent(messageType, bytes.length - INT_SIZE, bb)
  }

  def ofContent(messageType: MessageType, bufSize: Int, contentBuffer: ByteBuffer): Message = {
    MessageCompanion.getConstructor(messageType)(bufSize,contentBuffer)
  }

}


sealed trait MessageCompanion[T <: Message] {
  //val messageType: MessageType
  def blockingReadFrom(file: RandomAccessFile): T = {
    println("Waiting for message using type: " + {this.getClass.toString})
    val msg = Message.blockingReadFrom(file)
    msg.coerce[T](this)
  }
  val constructor: ((Int, ByteBuffer) => T)
  protected def readIntArray(len: Int, buf: ByteBuffer): Array[Int] = {
    val ib = buf.asIntBuffer()
    val ints: Array[Int] = new Array[Int](len / INT_SIZE)
    val intLength = ints.length
    println("Hmm: " + intLength)
    if(intLength % 2 != 0) {
      throw new Exception("Rational array needs even number of ints")
    }
    var i = 0
    while(i < intLength) {
      ints(i) = ib.get()
      i = i + 1
    }
    ints
  }

  protected def readRatArray(len: Int, buf: ByteBuffer): Array[RatNum] = {
    val ints = readIntArray(len, buf)
    val numRats = ints.length / 2
    var i = 0
    var rats: List[scalar] = List()
    while(i < numRats) {
      rats = rats ++ List(RatNum(Rational(ints(2*i), ints(2*i + 1))))
      i = i + 1
    }
    rats.toArray
  }
}

object MessageCompanion {
  def getConstructor(messageType: MessageType): ((Int, ByteBuffer) => Message) = {
    messageType match {
      case InitRequestMessageType => InitResponseMessage.constructor
      case InitResponseMessageType =>InitResponseMessage.constructor
      case GetConstRequestMessageType => GetConstRequestMessage.constructor
      case GetConstResponseMessageType => GetConstResponseMessage.constructor
      case SenseRequestMessageType => SenseResponseMessage.constructor
      case SenseResponseMessageType => SenseResponseMessage.constructor
      case HasNextRequestMessageType => HasNextRequestMessage.constructor
      case HasNextResponseMessageType => HasNextResponseMessage.constructor
      case ExtCtrlRequestMessageType => ExtCtrlRequestMessage.constructor
      case ExtCtrlResponseMessageType => ExtCtrlResponseMessage.constructor
      case ActuateRequestMessageType => ActuateRequestMessage.constructor
      case ActuateResponseMessageType => ActuateResponseMessage.constructor
    }
  }
}

case class InitRequestMessage(protocolVersion: Int, level: AirSimLevel, controller: AirSimController) extends Message {
  override val messageType: MessageType = InitRequestMessageType
  override def content: Array[Byte] = {
    intsToBytes(List(protocolVersion, level.tag, controller.tag))
  }
}
object InitRequestMessage extends MessageCompanion[InitRequestMessage] {
  override val constructor: (Int, ByteBuffer) => InitRequestMessage = {case (len, buf) =>
    val ints = readIntArray(len, buf)
    InitRequestMessage(ints(0), AirSimLevel.all(ints(1)), AirSimController.all(ints(2)))
  }
}

case class InitResponseMessage(protocolVersion: Int, versionIsCompatible: Boolean) extends Message {
  override val messageType: MessageType = InitResponseMessageType
  override def content: Array[Byte] = {
    val contentBuffer = ByteBuffer.allocate(INT_SIZE + BOOL_SIZE)
    contentBuffer.order(BYTE_ORDER);
    contentBuffer.position(0)
    contentBuffer.putInt(protocolVersion)
    contentBuffer.put(if (versionIsCompatible) (1:Byte) else (0: Byte))
    contentBuffer.array()
  }
}
object InitResponseMessage extends MessageCompanion[InitResponseMessage] {
  override val constructor: (Int, ByteBuffer) => InitResponseMessage = {case (len, buf) =>
    val protVersion = buf.getInt()
    val versionCompat = (buf.get() == 1)
    InitResponseMessage(protVersion, versionCompat)
  }
}

case class GetConstRequestMessage(expectedVariableCount: Int) extends Message {
  override val messageType: MessageType = GetConstRequestMessageType
  override def content: Array[Byte] = {
    intsToBytes(List(expectedVariableCount))
  }
}
object GetConstRequestMessage extends MessageCompanion[GetConstRequestMessage] {
  override val constructor: (Int, ByteBuffer) => GetConstRequestMessage = {case (len, buf) =>
    GetConstRequestMessage(buf.getInt())
  }
}

case class GetConstResponseMessage(variableValueArray: Array[scalar]) extends Message {
  override val messageType: MessageType = GetConstResponseMessageType
  override def content: Array[Byte] = scalarsToBytes(variableValueArray.toList)
}
object GetConstResponseMessage extends MessageCompanion[GetConstResponseMessage] {
  override val constructor: (Int, ByteBuffer) => GetConstResponseMessage = {case (len, buf) =>
    GetConstResponseMessage(readRatArray(len, buf))
  }
}

case class SenseRequestMessage(expectedVariableCount: Int) extends Message {
  override val messageType: MessageType = SenseRequestMessageType
  override def content: Array[Byte] = {
    intsToBytes(List(expectedVariableCount))
  }
}
object SenseRequestMessage extends MessageCompanion[SenseRequestMessage] {
  override val constructor: (Int, ByteBuffer) => SenseRequestMessage = {case (len, buf) =>
    SenseRequestMessage(buf.getInt())
  }
}

case class SenseResponseMessage(variableValueArray: Array[scalar]) extends Message {
  override val messageType: MessageType = SenseResponseMessageType
  override def content: Array[Byte] = scalarsToBytes(variableValueArray.toList)
}
object SenseResponseMessage extends MessageCompanion[SenseResponseMessage] {
  override val constructor: (Int, ByteBuffer) => SenseResponseMessage = {case (len, buf) =>
    SenseResponseMessage(readRatArray(len, buf))
  }
}

case class HasNextRequestMessage() extends Message {
  override val messageType: MessageType = HasNextRequestMessageType
  override def content: Array[Byte] = Array()
}
object HasNextRequestMessage extends MessageCompanion[HasNextRequestMessage] {
  override val constructor: (Int, ByteBuffer) => HasNextRequestMessage = {case (len, buf) =>
    HasNextRequestMessage()
  }
}

case class HasNextResponseMessage(hasNext: Boolean) extends Message {
  override val messageType: MessageType = HasNextResponseMessageType
  override def content: Array[Byte] = {
    Array(if(hasNext) (1:Byte) else (0:Byte))
  }
}
object HasNextResponseMessage extends MessageCompanion[HasNextResponseMessage] {
  override val constructor: (Int, ByteBuffer) => HasNextResponseMessage = {case (len, buf) =>
    val byte = buf.get()
    HasNextResponseMessage(byte == 1)
  }
}

case class ExtCtrlRequestMessage(expectedVariableCount: Int) extends Message {
  override val messageType: MessageType = ExtCtrlRequestMessageType
  override def content: Array[Byte] = {
    intsToBytes(List(expectedVariableCount))
  }
}
object ExtCtrlRequestMessage extends MessageCompanion[ExtCtrlRequestMessage] {
  override val constructor: (Int, ByteBuffer) => ExtCtrlRequestMessage = {case (len, buf) =>
    ExtCtrlRequestMessage(buf.getInt())
  }
}

case class ExtCtrlResponseMessage(variableValueArray: Array[scalar]) extends Message {
  override val messageType: MessageType = ExtCtrlResponseMessageType
  override def content: Array[Byte] = scalarsToBytes(variableValueArray.toList)
}
object ExtCtrlResponseMessage extends MessageCompanion[ExtCtrlResponseMessage] {
  override val constructor: (Int, ByteBuffer) => ExtCtrlResponseMessage = {case (len, buf) =>
    ExtCtrlResponseMessage(readRatArray(len, buf))
  }
}

case class ActuateRequestMessage(variableValueArray: Array[scalar]) extends Message {
  override val messageType: MessageType = ActuateRequestMessageType
  override def content: Array[Byte] = scalarsToBytes(variableValueArray.toList)
}
object ActuateRequestMessage extends MessageCompanion[ActuateRequestMessage] {
  override val constructor: (Int, ByteBuffer) => ActuateRequestMessage = {case (len, buf) =>
    ActuateRequestMessage(readRatArray(len, buf))
  }
}

case class ActuateResponseMessage() extends Message {
  override val messageType: MessageType = ActuateResponseMessageType
  override def content: Array[Byte] = Array()
}
object ActuateResponseMessage extends MessageCompanion[ActuateResponseMessage] {
  override val constructor:(Int, Buffer) => ActuateResponseMessage = {case (len, buf) =>
    ActuateResponseMessage()
  }
}

// AirSim interaction isn't actually done through FFIs, it's done through interprocess communication with named pipes.
// But let's try to implement it using the same infrastructure first and see if that works or not.
object  AirSimAPI extends VeriPhyFFIs {
  //val bundle = ralVerboseBundle
  var numConsts: Int = 4
  var numSensorVars: Int = 4
  var numCtrlVars: Int = 7
  var level: AirSimLevel = AirSimLevel.all.head
  var controller: AirSimController = AirSimController.all.head

  def setSpec(airSimSpec: AirSimSpec): Unit = {
    level = airSimSpec.airSimLevel
    controller = airSimSpec.airSimController
  }

  // @TODO: Initialize better at right time because currently done too late
  def setVars(strat: AirSimVerboseStrategy[_]): Unit = {
    numConsts = 4//strat.constVars.length
    numSensorVars = 4//strat.senseVars.length
    numCtrlVars = 7//strat.ctrlVars.length
  }

  var pipe: RandomAccessFile = null;
  //val pipeChannel: FileChannel = null;

  // byte[]
  private def initPipe(): Unit = {
    if (pipe == null) {
      try { // Connect to the pipe
        pipe = new RandomAccessFile("\\\\.\\pipe\\VeriPhy", "rw")
        //pipeChannel = pipe.getChannel()
      } catch {
        case e: Exception =>
          // TODO Auto-generated catch block
          println("Connection error: " + e)
          e.printStackTrace()
      }
    }
  }

  // c is path to output file, a is list of integers. can be called more than once
  def ffiinit(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = {
    initPipe()
    val request = InitRequestMessage(ProtocolTypes.currentVersion, level, controller)
    request.sendTo(pipe)
    val response = InitResponseMessage.blockingReadFrom(pipe)
    if(!response.versionIsCompatible) {
      throw new Exception(s"Other party has incompatible protocol version: ${response.protocolVersion}")
    }
  }

  def ffiget_const(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = {
    val request = GetConstRequestMessage(numConsts)
    request.sendTo(pipe)
    val response = GetConstResponseMessage.blockingReadFrom(pipe)
    val arr = response.variableValueArray
    // @TODO: Decide int vs rat
    for((x, i) <- arr.zipWithIndex) {
      a.setInt(INT_SIZE*i*2, x.n.n.toInt)
      a.setInt(INT_SIZE*(i*2+1), x.n.d.toInt)
//      a.setInt(INT_SIZE*i, x.n.toInt)
    }
  }

  def ffiget_ctrl(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = {
    val request = ExtCtrlRequestMessage(numCtrlVars)
    request.sendTo(pipe)
    val response = ExtCtrlResponseMessage.blockingReadFrom(pipe)
    val arr = response.variableValueArray
    // @TODO: Decide int vs rat
    for((x, i) <- arr.zipWithIndex) {
      a.setInt(INT_SIZE*i*2, x.n.n.toInt)
      a.setInt(INT_SIZE*(i*2+1), x.n.d.toInt)
    }
  }

  def ffiactuate(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = {
    val actInts = c.getIntArray(0, numCtrlVars*2)//.map(n => RatNum(Rational(n, 1)))
    val arr: Array[RatNum] = new Array(numCtrlVars)
    for(i <- (0 until numCtrlVars)) {
      arr(i) = RatNum(Rational(actInts(2*i), actInts(2*i + 1)))
    }
    val request = ActuateRequestMessage(arr)
    request.sendTo(pipe)
    val _response = ActuateResponseMessage.blockingReadFrom(pipe)
  }

  def ffihas_next(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit  = { // int -> char
    val request = HasNextRequestMessage()
    request.sendTo(pipe)
    val response = HasNextResponseMessage.blockingReadFrom(pipe)
    a.setByte(0, if (response.hasNext) (1: Byte) else (0: Byte))
  }

  def ffifallback(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = { // char -> int
    () // @TODO: Needed?
  }

  def ffiviolation(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = { // char -> int
    () // @TODO: Needed?
  }

  def ffiread_log(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = {
    () // @TODO: Needed?
  }

  def ffiexit(): Unit  = { //(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit
    if(pipe != null) {
      pipe.close()
      pipe = null;
    }
  }

  def ffiget_sensor(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = {
    val request = SenseRequestMessage(numSensorVars)
    request.sendTo(pipe)
    val response = SenseResponseMessage.blockingReadFrom(pipe)
    val arr = response.variableValueArray
    // @TODO: Decide int vs rat
    for((x, i) <- arr.zipWithIndex) {
      a.setInt(INT_SIZE*i*2, x.n.n.toInt)
      a.setInt(INT_SIZE*(i*2+1), x.n.d.toInt)
//      a.setInt(INT_SIZE*i, x.n.toInt)
    }
  }
}

// separate this out because GoPiGo will want to do special Python handling rather than C
*/
object AirSimMain {
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

  private def bundleFromFile(filePath: String): StrategyBundle = {
    StrategyBundle.fromFile(filePath)

  }
*/
  // Args:  file_path
  // file_path is used for printing CSV files
  def main(args: Array[String]): Unit = {
  /*  initQE()
    println("Note: Customized AirSim must be started before this experiment is. \nThe custom AirSim version will show an UnrealEngine loading screen while waiting for us.")
    if(args.length < 2) {
      println("Usage: <exe_name> path_to_strategy_file directory_to_save_results")
      println("strategy_file should use file format from strategy extractor including ID maps separated with @ symbol")
      return
    }
    val stratPath = args(0)
    val fullPath = args(1)
    //val load = FFILoader(libName)
    val lib: VeriPhyFFIs = AirSimAPI //load.Instance
    println("Loaded DLL for FFI!")
    //println("native size: " + Native.LONG_SIZE)
    //val angel = StrategyParser(sandboxPLDIStratString)
    val bundle = bundleFromFile(stratPath)
    val angel = loadBundle(bundle)
    println("Read Angel Strategy:\n" + StrategyPrinter(angel))
    //println("Warm-starting FFI Library")
    // NB: Don't warm start because it would make protocol annoying for airsim side
    //lib.warmStart()
    //println("Warm-started FFI Library")
      val simSpec = AirSimSpec(CloverLevel, PIDHighController)
    //for (simSpec <- AirSimSpec.all) {
        doOneAirSim(lib, angel, fullPath, simSpec)
    //}*/
  }
}
