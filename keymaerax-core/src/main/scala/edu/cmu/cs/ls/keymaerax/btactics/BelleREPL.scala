package edu.cmu.cs.ls.keymaerax.btactics

import java.io.PrintWriter

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.{NoProofTermProvable, ProvableSig}
import scala.util.control.Breaks._

import scala.util.Try

/** Credit for Eval class to https://gist.github.com/xuwei-k/9ba39fe22f120cb098f4 */
private object Eval {
  import scala.reflect.runtime.currentMirror
  import scala.tools.reflect.ToolBox
  import java.io.File
  import edu.cmu.cs.ls.keymaerax.bellerophon._
  import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
  val toolbox = currentMirror.mkToolBox()

  def apply[A](string: String): A = {
    val tree = toolbox.parse(tacticImports+string)
    toolbox.eval(tree).asInstanceOf[A]
  }

  def fromFile[A](file: File): A =
    apply(scala.io.Source.fromFile(file).mkString(""))

  def fromFileName[A](file: String): A =
    fromFile(new File(file))

  private val tacticImports =
    """
      |import edu.cmu.cs.ls.keymaerax.bellerophon._;
      |import edu.cmu.cs.ls.keymaerax.btactics._;
      |import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._;
      |import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._;
      |import edu.cmu.cs.ls.keymaerax.parser.StringConverter._;
      |
    """.stripMargin


  def tactic(tac:String):BelleExpr = {
    apply[BelleExpr](tac)
  }
}
/**
  * Created by bbohrer on 12/19/16.
  *
  */
class BelleREPL (val concl:Formula, val initTactic:Option[String], val initScala:Option[String], val defaultKytOutput:Option[String], val defaultScalaOutput:Option[String]){

  private final val DEFAULT_NSTEPS:Int = 10
  private abstract class Command
  private case class Quit(filename:String, sname:Option[String]) extends Command
  private case class Tactic( source:String) extends Command
  private case class Usage() extends Command
  private case class Head(n:Int, verbose:Boolean) extends Command
  private case class Tail(n:Int, verbose:Boolean) extends Command
  private case class PrintTactic() extends Command
  private case class RewindTo(n:Int) extends Command
  private case class RewindBy(n:Int) extends Command
  private case class EvalScala(code:String) extends Command

  private class REPLParseException(err:String) extends Exception

  def interpret(e:BelleExpr, pr:Provable):ProvableSig = {
    SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
      case BelleProvable(result,_) => result
    }
  }

  val initProvable = Provable.startProof(concl)
  /* All belle exprs run so far and snapshots of proof state before each tactic was run */
  var hist:List[(Provable, String)] =
    initTactic match {
      case None => Nil
      case Some(e) => List((initProvable, e))
    }

  var scalaState:String = initScala.getOrElse("")
  var state:Provable =
    initTactic match {
      case None => initProvable
      case Some(e) => interpret(Eval.tactic(scalaState + e), initProvable).underlyingProvable
    }

  def ignore[A](a:Any,b:A):A = b

  def fullTactic:String = {
    hist.map(_._2).foldLeft("nil")((acc,e) => e + " &\n " + acc)
  }

  def fullScala:String = {
    scalaState
  }

  def acquireOutputFile:(String,Option[String]) = {
    Console.println("You have finished proving the formula:")
    Console.println(PrettyPrinter(concl))
    Console.println("The following tactic proves the formula:")
    Console.println(fullTactic)
    val kytOut =
      defaultKytOutput match {
        case None =>
          Console.println("Please enter a filename in which to save the resulting tactic:")
          scala.io.StdIn.readLine()
        case Some(default) =>
          Console.println("Please enter a filename in which to save the resulting tactic (default: overwrite input file " + defaultKytOutput + "):")
          val out = scala.io.StdIn.readLine()
          if (out == "") default else out
      }
    val scalaOut:Option[String] =
      defaultScalaOutput match {
        case None =>
          Console.println("Please enter a filename in which to save the associated Scala definitions:")
          val out = scala.io.StdIn.readLine()
          if (out == "") defaultScalaOutput else Some(out)
        case Some(default) =>
          Console.println("Please enter a filename in which to save the associated Scala definitions (default: overwrite input file " + defaultScalaOutput + "):")
          val out = scala.io.StdIn.readLine()
          if (out == "") defaultScalaOutput else Some(out)
      }
    (kytOut, scalaOut)
  }

  def saveTo(kytFilename:String, scalaFilename:Option[String]):Unit = {
    val kpw = new PrintWriter(kytFilename)
    kpw.write(fullTactic)
    kpw.close()
    scalaFilename.foreach(name => {
      val spw = new PrintWriter(name)
      spw.write(fullScala)
      spw.close()})
  }

  def printSteps(msg:String, steps:List[(Provable,String)], verbose:Boolean):Unit = {
    Console.println(msg)
    val iSteps:List[((Provable,String),Int)] = steps.zipWithIndex
    iSteps.foreach { case ((pr, e), i) =>
      val displayI = i + 1
      Console.println(displayI + " " + e)
      if(verbose)
        Console.println(pr.prettyString)
    }
  }
  def rewindby(n:Int):Boolean = {
    if (n <= 0)
      false
    else {
      val hds = hist.take(n)
      val tls = hist.drop(n)
      state = hds.last._1
      hist = tls
      false
    }
  }

  def saveIfDone(pr:Provable):Boolean = {
    if(pr.isProved) {
      val (kout,sout) = acquireOutputFile
      saveTo(kout,sout)
      true
    }
    else {
      false
    }
  }

  def interp(cmd:Command):Boolean = {
    cmd match {
      case Quit(filename, sname) =>
        saveTo(filename, sname)
        true
      case Tactic(s) =>
        val e = Eval.tactic(scalaState + s)
        val newState = interpret(e, state).underlyingProvable
        hist = (state, s)::hist
        state = newState
        saveIfDone(newState)
      case Tail(n, verbose) =>
        printSteps("Most recent " + n + " steps:", hist.take(n), verbose)
        false
      case Head(n, verbose) =>
        printSteps("First " + n + " steps:", hist.reverse.take(n), verbose)
        false
      case Usage() =>
        Console.println("Type '?' to view this help")
        Console.println("Type 'quit' to save current progress and quit")
        Console.println("Type 'head [n] [-v]' to view first n steps (default: " + DEFAULT_NSTEPS + ")")
        Console.println("Type 'tail [n] [-v]' to view last n steps (default: " + DEFAULT_NSTEPS + ")")
        Console.println("Type 'tactic' to view a tactic for the proof so far")
        Console.println("Type 'rewindBy n' or 'rb n' to rewind by n steps")
        Console.println("Type 'rewindTo n' or 'rt n' to rewind to step n")
        Console.println("To enter Scala definitions, type 'scala' on a line by itself, then write the definitions, then a blank line when done.)")
        Console.println("Anything else will be interpreted as a Bellerophon tactic")
        false
      case PrintTactic() =>
        Console.println("Current tactic:")
        Console.println(fullTactic)
        false
      case RewindBy(n) =>
        rewindby(n)
      case RewindTo(n) =>
        rewindby(hist.length - n)
      case EvalScala(code) =>
        scalaState = scalaState  + code + "\n"
        Eval(scalaState)
        false

    }
  }

  private def parse(str:String):Command = {
    val split =  str.split(" ").map(_.toLowerCase)
    if(str.startsWith("quit")) {
      if(split.length <= 1 || !split(1).endsWith(".kyt"))
        throw new REPLParseException ("Quit command must specify .kyt file to save tactic in")
      else if (split.length == 1)
        Quit(split(1), None)
      else Quit(split(1), Some(split(2)))
    } else if (str.startsWith("?")) {
      Usage()
    } else if (str.startsWith("head")) {
      val maybeInt = Try (split(1).toInt).toOption
      val verbose = split.contains("-v") || split.contains("--verbose")
      val nsteps =
        if (split.length <= 1 || maybeInt.isEmpty)
          DEFAULT_NSTEPS
        else
          maybeInt.get
      Head(nsteps, verbose)
    } else if (str.startsWith("tail")) {
      val verbose = split.contains("-v") || split.contains("--verbose")
      val nsteps =
        if (split.length <= 1 || Try (split(1).toInt).toOption.isEmpty) {
          DEFAULT_NSTEPS
        } else {
          Try(split(1).toInt).toOption.get
        }
      Tail(nsteps, verbose)
    } else if (str.startsWith("tactic")) {
      PrintTactic()
    } else if (str.startsWith("rb") || str.startsWith("rewindby")) {
      if(split.length <= 1 || Try (split(1).toInt).toOption.isEmpty)
        throw new REPLParseException ("rewindBy command must take integer argument")
      RewindBy(Try (split(1).toInt).toOption.get)
    } else if (str.startsWith("rt") || str.startsWith("rewindto")) {
      if(split.length <= 1 || Try (split(1).toInt).toOption.isEmpty)
        throw new REPLParseException ("rewindTo command must take integer argument")
      RewindTo(Try (split(1).toInt).toOption.get)
    } else if(str.startsWith("scala")) {
      var allText = ""
      var nextLine = ""
      do {
        nextLine = scala.io.StdIn.readLine()
        allText = allText + nextLine
      } while(nextLine != "")
      EvalScala(allText)
    } else {
      Tactic(str)
    }
  }

  def printState(pr:Provable):Unit = {
    Console.println("Proof state:")
    Console.println(state.prettyString)
    Console.print(">")
  }

  def run():Unit = {
    var line:String = null
    if(saveIfDone(state)) {
      Console.println("Initial tactic proved model. Goodbye!")
      return
    }
    Console.println("Bellerophon REPL started. Type ? for usage info")
    while (ignore(ignore(printState(state), line = scala.io.StdIn.readLine()),  line != null)) {
      breakable {
        val parsed =
          try { parse(line) }
          catch {
            case e:Exception =>
              Console.println("Exception while parsing following line:")
              Console.println(line)
              Console.println("Exception: " + e)
              break()
          }
        val done =
          try { interp(parsed) }
          catch {
            case e:Exception =>
              Console.println("Exception while executing following line:")
              Console.println(parsed)
              Console.println("Exception: " + e)
              break()
          }
        if (done)
          return
      }
    }
  }
}
