package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import java.io.{File, RandomAccessFile}
import java.nio._

import com.sun.jna._
import edu.cmu.cs.ls.keymaerax.veriphy.experiments.ProtocolTypes._
import edu.cmu.cs.ls.keymaerax.veriphy.experiments.BotCommon._


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
object ProtocolTypes {
  val currentVersion: Int = 1
  val INT_SIZE: Int = 4
  val BOOL_SIZE: Int = 1
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
    val INT_SIZE = 4
    val contentBuffer = ByteBuffer.allocate(ints.length*INT_SIZE)
    contentBuffer.position(0)
    for (k <- ints) {
      contentBuffer.putInt(k)
    }
    contentBuffer.array()
  }
  protected def scalarsToBytes(scalars: List[scalar]): Array[Byte] = {
    intsToBytes(scalars.flatMap(n => List(n.n.n.toInt, n.n.d.toInt)))
  }

  def allBytes: Array[Byte] = {
    val arr = content
    val typeId = messageType.typeId
    val size = arr.length + INT_SIZE
    val bb = ByteBuffer.allocate(size + INT_SIZE)
    bb.putInt(size)
    bb.putInt(typeId)
    bb.put(arr)
    bb.array()
  }
  def sendTo(file: RandomAccessFile): Unit = {
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
  def blockingReadFrom(file: RandomAccessFile): Message = {
    val size = file.readInt()
    val typeAndContent = new Array[Byte] (size)
    file.readFully(typeAndContent)
    ofTypeAndContent(size, typeAndContent)
  }
  // @TODO: bytes interface -> file handle interface
  def ofTypeAndContent(declaredSize: Int, bytes: Array[Byte]): Message = {
    if (bytes.length < 4) {
      throw new Exception("Message packet expected to be at least 4 bytes of type ID after packet size header")
    }
    val bb = ByteBuffer.allocate(bytes.length)
    bb.position(0)
    bb.put(bytes)
    bb.rewind()
    val INT_SIZE = 4
    if (bytes.length - INT_SIZE != declaredSize) {
      throw new Exception("Packet does not have expected size")
    }
    val messageType = MessageType(bb.getInt())
    //bb.position(INT_SIZE)
    ofContent(messageType, bytes.length - INT_SIZE, bb)
  }

  def ofContent(messageType: MessageType, bufSize: Int, contentBuffer: ByteBuffer): Message = {
    MessageCompanion.getConstructor(messageType)(bufSize,contentBuffer)
  }

}


sealed trait MessageCompanion[T <: Message] {
  def blockingReadFrom(file: RandomAccessFile): T = {
    val msg = Message.blockingReadFrom(file)
    msg.coerce[T](this)
  }
  val constructor: ((Int, ByteBuffer) => T)
  protected def readIntArray(len: Int, buf: ByteBuffer): Array[Int] = {
    val ib = buf.asIntBuffer()
    val ints: Array[Int] = Array(len / INT_SIZE)
    if(ints.length % 2 != 0) {
      throw new Exception("Actuate request needs even number of ints")
    }
    var i = 0
    while(i < len) {
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
  override val messageType: MessageType = GetConstResponseMessageType
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
object AirSimAPI extends VeriPhyFFIs {
  //val bundle = ralVerboseBundle
  var numConsts: Int = 0
  var numSensorVars: Int = 0
  var numCtrlVars: Int = 0
  var level: AirSimLevel = AirSimLevel.all.head
  var controller: AirSimController = AirSimController.all.head

  def setSpec(airSimSpec: AirSimSpec): Unit = {
    level = airSimSpec.airSimLevel
    controller = airSimSpec.airSimController
  }

  def setVars(strat: AirSimVerboseStrategy[_]): Unit = {
    numConsts = strat.constVars.length
    numSensorVars = strat.senseVars.length
    numCtrlVars = strat.ctrlVars.length
  }

  var pipe: RandomAccessFile = null;

  // byte[]
  private def initPipe(): Unit = {
    if (pipe == null) {
      try { // Connect to the pipe
        pipe = new RandomAccessFile("\\\\.\\pipe\\VeriPhy", "rw")
        pipe.close()
      } catch {
        case e: Exception =>
          // TODO Auto-generated catch block
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
      a.setInt(INT_SIZE*i, x.n.toInt)
    }
  }

  def ffiget_ctrl(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = {
    val request = ExtCtrlRequestMessage(numCtrlVars)
    request.sendTo(pipe)
    val response = ExtCtrlResponseMessage.blockingReadFrom(pipe)
    val arr = response.variableValueArray
    // @TODO: Decide int vs rat
    for((x, i) <- arr.zipWithIndex) {
      a.setInt(INT_SIZE*i, x.n.toInt)
    }
  }

  def ffiactuate(c: Pointer, clen: Int, a: Pointer, alen: Int): Unit = {
    val actVars = c.getIntArray(0, numCtrlVars).map(n => RatNum(Rational(n, 1)))
    val request = ActuateRequestMessage(actVars)
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
      a.setInt(INT_SIZE*i, x.n.toInt)
    }
  }
}

// separate this out because GoPiGo will want to do special Python handling rather than C

class AirSimMain {
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

    //val load = FFILoader(libName)
    val lib: VeriPhyFFIs = AirSimAPI //load.Instance
    println("Loaded DLL for FFI!")
    //println("native size: " + Native.LONG_SIZE)
    //val angel = StrategyParser(sandboxPLDIStratString)
    val angel = loadBundle(ralVerboseBundle)
    println("Read Angel Strategy:\n" + StrategyPrinter(angel))
    println("Warm-starting FFI Library")
    lib.warmStart()
    println("Warm-started FFI Library")
    for (simSpec <- AirSimSpec.all) {
        doOneAirSim(lib, angel, fullPath, simSpec)
    }
  }
}
