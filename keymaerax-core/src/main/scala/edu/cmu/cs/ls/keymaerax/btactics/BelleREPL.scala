package edu.cmu.cs.ls.keymaerax.btactics

import java.io.PrintWriter

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.{NoProofTermProvable, ProvableSig}
import scala.util.control.Breaks._

import scala.util.Try


/**
  * Created by bbohrer on 12/19/16.
  *
  * @TODO Make input tactic optional
  */
class BelleREPL (val concl:Formula, val initTactic:BelleExpr, val defaultOutput:String){
  private final val DEFAULT_NSTEPS:Int = 10
  private abstract class Command
  private case class Quit(filename:String) extends Command
  private case class Tactic(e:BelleExpr) extends Command
  private case class Usage() extends Command
  private case class Head(n:Int, verbose:Boolean) extends Command
  private case class Tail(n:Int, verbose:Boolean) extends Command

  private class REPLParseException(err:String) extends Exception

  def interpret(e:BelleExpr, pr:Provable):ProvableSig = {
    SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
      case BelleProvable(result,_) => result
    }
  }

  val initProvable = Provable.startProof(concl)
  /* All belle exprs run so far and snapshots of proof state before each tactic was run */
  var hist:List[(Provable, BelleExpr)] = List((initProvable, initTactic))
  var state:Provable = interpret(initTactic, initProvable).underlyingProvable

  def ignore[A](a:Any,b:A):A = b

  def fullTactic:String = {
    val tac:BelleExpr = hist.map(_._2).foldLeft(TactixLibrary.nil)((acc,e) => e&acc)
    BellePrettyPrinter(tac)
  }

  def acquireOutputFile:String = {
    Console.println("You have finished proving the formula:")
    Console.println(PrettyPrinter(concl))
    Console.println("The following tactic proves the formula:")
    Console.println(fullTactic)
    Console.println("Please enter a filename in which to save the resulting tactic (default: overwrite input file " + defaultOutput + "):")
    val out = scala.io.StdIn.readLine()
    if (out == "") defaultOutput else out
  }

  def saveTo(filename:String):Unit = {
    val pw = new PrintWriter(filename)
    pw.write(fullTactic)
    pw.close()
  }

  def printSteps(msg:String, steps:List[(Provable,BelleExpr)], verbose:Boolean):Unit = {
    Console.println(msg)
    val iSteps:List[((Provable,BelleExpr),Int)] = steps.zipWithIndex
    iSteps.foreach { case ((pr, e), i) =>
      val displayI = i + 1
      Console.println(displayI + " " + BellePrettyPrinter(e))
      if(verbose)
        Console.println(pr.prettyString)
    }
  }

  def interp(cmd:Command):Boolean = {
    cmd match {
      case Quit(filename) =>
        saveTo(filename)
        true
      case Tactic(e) =>
        val newState = interpret(e, state).underlyingProvable
        hist = (state, e)::hist
        state = newState
        if(newState.isProved) {
          val out = acquireOutputFile
          saveTo(out)
          true
        }
        else {
          false
        }
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
        Console.println("Anything else will be interpreted as a Bellerophon tactic")
        false
    }
  }

  private def parse(str:String):Command = {
    val split = str.split(" ")
    if(str.startsWith("quit")) {
      if(split.length <= 1 || !split(1).endsWith(".kyt"))
        throw new REPLParseException ("Quit command must specify .kyt file to save tactic in")
      Quit(split(1))
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
      val maybeInt = Try (split(1).toInt).toOption
      val verbose = split.contains("-v") || split.contains("--verbose")
      val nsteps =
        if (split.length <= 1 || maybeInt.isEmpty)
          DEFAULT_NSTEPS
        else
          maybeInt.get
      Tail(nsteps, verbose)
    } else {
      Tactic(BelleParser(str))
    }
  }

  def run():Unit = {
    var line:String = null
    Console.println("Bellerophon REPL started. Type ? for usage info")
    Console.println("Initial proof state:")
    Console.println(state.prettyString)
    while (ignore(line = scala.io.StdIn.readLine(),  line != null)) {
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
        else {
          Console.println("Current proof state:")
          Console.println(state.prettyString)
        }
      }
    }
  }
}
