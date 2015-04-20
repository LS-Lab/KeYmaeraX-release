package testHelper

import java.io.File
import java.util.Locale
import java.util.concurrent.TimeoutException

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{PositionTactic, Tactic}

import scala.collection.immutable.Map
import scala.concurrent.duration.Duration
import scala.concurrent.{Future, Await}
import scala.concurrent.ExecutionContext.Implicits.global

/**
 * These are helper functions for writing tactic tests. Suggested use:
 *    import edu.cmu.cs.ls.keymaera.ProvabilityTestHelper.scala
 * Created by nfulton on 12/6/14.
 * @author nfulton
 * @author aplatzer
 */
class ProvabilityTestHelper(logger : String => Unit = (x:String) => ()) {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Utility Functions
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * Parses a string to an expression. Free variables may occur.
   * @param s
   * @return Some result of parse on success, or None
   */
  def parse(s:String) : Option[Expr] = new KeYmaeraParser().parseBareExpression(s)


  /**
   * Parses a string to a term. Free variables may occur.
   * @param s
   * @return Some result of parse on success, or None
   */
  def parseBareTerm(s:String) : Term = {
    parse(s) match {
      case Some(e) => e match {
        case t:Term => t
        case _ => throw new Exception("Expected to find a term but found something else: " + e.getClass())
      }
      case None => throw new Exception("Parse failed. Tried to parse: " + s)
    }
  }

  /**
   * Parses a bare program (no modality) into an expression. Free variables may occur.
   * @param s
   * @return Some result of parse on success, or None
   */
  def parseBareProgram(s : String) : Option[Program] = {
    //approach: add a modality around the bare program, parse the valid expression, extract the program.
    val result = new KeYmaeraParser().parseBareExpression("[" + s + "] 1>0");
    result match {
      case Some(BoxModality(program, formula)) => Some(program)
      case _ => None
    }
  }

  /**
   * Automatically do the projection and formula conversion. Be sure not to wrap this in an overly permissive try/catch.
   * @param s
   * @return
   */
  def parseFormula(s:String) = {
    val parseResult : Option[Expr] = parse(s);
    parseResult match {
      case Some(expr) => {
        if(expr.isInstanceOf[Formula]) {
          expr.asInstanceOf[Formula]
        }
        else {
          throw new Exception("Expected a formula but found something else.")
        }
      }
      case None => throw new Exception("Failed to parse.")
    }
  }

  /**
   *
   * @param formula
   * @return a proof node containing the formula.
   */
  def formulaToNode(formula : Formula) = {
    val sequent = new Sequent(Nil, scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(formula))
    new RootNode(sequent)
  }

  /**
   * prints out a report about the node.
   * @param node
   */
  def report(node : ProofNode) = {
    logger("REPORT")
    logger("------")
    logger("\tclosed: " + node.isClosed())
    logger("\tOpen Goals:")
    for(open <- node.openGoals()) {
      logger("\t\t" + open.sequent)
    }
    logger("------")
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Tactics
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //Begin Abbreviations

  /**
   *
   * @param tactic
   * @param rootNode
   * @return true just in case the tactic closes the rootNode.
   * @todo similar augmentations elsewhere
   */
  def tacticClosesProof(tactic : Tactic, rootNode : ProofNode):Boolean = runTactic(tactic, rootNode).isClosed()

  /**
   *
   * @param tactic
   * @param rootNode
   * @return true just in case the tactic does not apply at the node.
   */
  def tacticDoesNotApply(tactic : Tactic, rootNode : ProofNode):Boolean = !tactic.applicable(rootNode)

  /**
   *
   * @param duration
   * @param tactic
   * @param rootNode
   * @return true iff tactic finishes in duration.
   */
  def tacticFinishesAndClosesProof(duration: Duration, tactic : Tactic, rootNode : ProofNode):Boolean = runTacticWithTimeoutDuration(duration, tactic, rootNode) match {
    case Some(pn) => pn.isClosed()
    case None    => false
  }

  /**
   *
   * @param timeoutMs
   * @param tactic
   * @param rootNode
   * @return true iff tactic finishes in timeoutMs milliseconds
   */
  def tacticFinishesAndClosesProof(timeoutMs : Long, tactic : Tactic, rootNode : ProofNode):Boolean =
    tacticFinishesAndClosesProof(Duration(timeoutMs, "millis"), tactic, rootNode)

  /**
   * Converts a position tactic to a tactic by finding an applicable position. Use with care; you might want to find the
   * position yourself using the location tactics in the TacticsLibrary.
   * @param positionTactic
   * @return tactic at an applicable position, or ?
   */
  def positionTacticToTactic(positionTactic : PositionTactic):Tactic = {
    TacticLibrary.locateSuccAnte(positionTactic)
  }

  //Begin Substance.
  /**
   * Runs tactic at rootNode, and then blocks while the tactic runs.
   * @param tactic
   * @param rootNode
   * @param mustApply If true, an exception is thrown if the tactic does not apply. Default: false.
   * @return the rootNode after tactic application completes.
   */
  def runTactic(tactic : Tactic, rootNode : ProofNode, mustApply:Boolean=false):ProofNode = {
    if(!tactic.applicable(rootNode)) {
      throw new Exception("Called a tactic an an inapplicable node! Details: runTactic was called on tactic " + tactic.name + ", but is not applicable on the node")
    }

    //Dispatching the tactic.
    logger("Dispatching tactic " + tactic.name)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))

//    logger("beginning wait sequence for " + tactic.name)
//    tactic.synchronized {
//      tactic.registerCompletionEventListener(_ => tactic.synchronized(tactic.notifyAll));
//      tactic.wait();
//      tactic.unregister;
//    }

//    logger("Ending wait sequence for " + tactic.name)
    logger("Proof is closed: " + rootNode.isClosed())
    if(!rootNode.isClosed()) {
      rootNode.openGoals().map(x => logger("Open Goal: " + x.sequent.toString()))
    }

    if (false && rootNode.isClosed()) {
      // test that a Provable proving proofNode can be constructed
      assert(rootNode.isProved(), "A correct ProofNode.isClosed should imply ProofNode.isProveD()")
      assert(rootNode.provableWitness.isProved, "A correct ProofNode.isClosed should imply its provableWitness isProved")
      assert(rootNode.provableWitness.proved == rootNode.sequent, "A correct provableWitness construction proves the original goal")
    }

    rootNode
  }

  /**
   *
   * @param timeoutMs Milliseconds.
   * @param tactic @see runTactic
   * @param rootNode @see runTactic
   * @param mustApply @see runTactic
   * @return Some[node] if the tactic finishes in time, where node is the rootNode passed in.
   *         If the tactic does not end in time, returns None.
   */
  def runTacticWithTimeout(timeoutMs : Long, tactic : Tactic, rootNode : ProofNode,
                           mustApply:Boolean=false) : Option[ProofNode] = {
    val future = Future { runTactic(tactic, rootNode, mustApply) }
    eliminateFutureOrTimeout(future, Duration(timeoutMs, "millis"))
  }

  /**
   * Exactly like runTacticWithTimeout, but accepts a duration.
   * @param duration A duration.
   * @param tactic @see runTactic
   * @param rootNode @see runTactic
   * @param mustApply @see runTactic
   * @return Some[node] if the tactic finishes in time, where node is the rootNode passed in.
   *         If the tactic does not end in time, returns None.
   */
  def runTacticWithTimeoutDuration(duration : Duration, tactic : Tactic, rootNode : ProofNode,
                                   mustApply:Boolean=false) : Option[ProofNode] = {
    val future = Future { runTactic(tactic, rootNode, mustApply) }
    eliminateFutureOrTimeout(future, duration)
  }

  def runTacticForFiveSeconds(tactic:Tactic, rootNode:ProofNode) = runTacticWithTimeout(5000, tactic, rootNode, true)

  /**
   *
   * @param x
   * @param timeout
   * @tparam T
   * @return Some(result of x) if x completes within the duration, or None if not.
   *         Any exception which is not a TimeoutException is propagated.
   */
  private def eliminateFutureOrTimeout[T](x : Future[T], timeout : Duration) : Option[T] = {
    try {
      val result : T = Await.result(x, timeout)
      Some(result)
    }
    catch {
      case e : TimeoutException => None
      case e : Exception => throw e
    }
  }

  def mathematicaConfig : Map[String, String] = {
    var linkNamePath : String = ""
    var libDirPath : String = ""
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    val osArch = System.getProperty("os.arch")
    if(osName.contains("mac")) {
      val linkNamePathMac = "/Applications/Mathematica.app/Contents/MacOS/MathKernel"
      if(new java.io.File(linkNamePathMac).exists())
        linkNamePath = linkNamePathMac
      if(osArch.contains("64")) {
        val libDirPathMac64MmtcNew = "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64"
        val libDirPathMac64MmtcOld = "/Applications/Mathematica.app/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64"
        if(new java.io.File(libDirPathMac64MmtcNew).exists()) {
          libDirPath = libDirPathMac64MmtcNew
        } else if(new java.io.File(libDirPathMac64MmtcOld).exists()) {
          libDirPath = libDirPathMac64MmtcOld
        }
      } else {
        val libDirPathMac32MmtcNew = "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86"
        val libDirPathMac32MmtcOld = "/Applications/Mathematica.app/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86"
        if(new java.io.File(libDirPathMac32MmtcNew).exists()) {
          libDirPath = libDirPathMac32MmtcNew
        } else if(new java.io.File(libDirPathMac32MmtcOld).exists()) {
          libDirPath = libDirPathMac32MmtcOld
        }
      }
    } else if(osName.contains("windows")) {
      val linkNamePathWindows = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\MathKernel.exe"
      if(new java.io.File(linkNamePathWindows).exists())
        linkNamePath = linkNamePathWindows
      if(osArch.contains("64")) {
        val libDirPathWindows64 = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows-x86-64"
        if(new java.io.File(libDirPathWindows64).exists())
          libDirPath = libDirPathWindows64
      } else {
        val libDirPathWindows32 = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows"
        if(new java.io.File(libDirPathWindows32).exists())
          libDirPath = libDirPathWindows32
      }
    } else if(osName.contains("linux")) {
      val linkNamePathLinuxMmtc10 = "/usr/local/Wolfram/Mathematica/10.0/Executables/MathKernel"
      val linkNamePathLinuxMmtc9 = "/usr/local/Wolfram/Mathematica/9.0/Executables/MathKernel"
      if(new java.io.File(linkNamePathLinuxMmtc10).exists()) {
        linkNamePath = linkNamePathLinuxMmtc10
        if(osArch.contains("64")) {
          val libDirPathLinux64Mmtc10 = "/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64"
          if(new java.io.File(libDirPathLinux64Mmtc10).exists())
            libDirPath = libDirPathLinux64Mmtc10
        } else {
          val libDirPathLinux32Mmtc10 = "/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux"
          if(new java.io.File(libDirPathLinux32Mmtc10).exists())
            libDirPath = libDirPathLinux32Mmtc10
        }
      } else if(new java.io.File(linkNamePathLinuxMmtc9).exists()) {
        linkNamePath = linkNamePathLinuxMmtc9
        if(osArch.contains("64")) {
          val libDirPathLinux64Mmtc9 = "/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64"
          if(new java.io.File(libDirPathLinux64Mmtc9).exists())
            libDirPath = libDirPathLinux64Mmtc9
        } else {
          val libDirPathLinux32Mmtc9 = "/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux"
          if(new java.io.File(libDirPathLinux32Mmtc9).exists())
            libDirPath = libDirPathLinux32Mmtc9
        }
      }
    }
    if(linkNamePath == "")
      throw new Exception("Could not find the path to MathKernel on your " + osName)
    if(libDirPath == "")
      throw new Exception("Could not find the path to J/Link Native Library on your " + osName)
    Map("linkName" -> linkNamePath, "libDir" -> libDirPath)
  }
}
