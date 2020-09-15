package edu.cmu.cs.ls.keymaerax.cli

import java.io.PrintWriter

import edu.cmu.cs.ls.keymaerax.bellerophon.SaturateTactic
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.{OptionMap, exit}
import edu.cmu.cs.ls.keymaerax.codegen.{CGenerator, CMonitorGenerator}
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Box, Compose, Formula, Imply, Loop, StaticSemantics, Test}
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.ParsedArchiveEntry

import scala.compat.Platform
import scala.reflect.io.File

/** Code generator command-line interface. */
object CodeGen {
  /** Code generator.
    * @param options Options to steer the code generator:
    *                - 'in (mandatory) input archive file, can be of the form file.kyx#entry
    *                - 'out (optional) output file (default: 'in.c)
    *                - 'vars (optional)
    *                - 'interval (optional) Whether to use interval arithmetic or floating point arithmetic (default: interval)
    *                - 'quantitative (optional) Whether to generate a quantitative or boolean monitor (default: true)
    * @param usage Usage information to print on wrong usage. */
  def codegen(options: OptionMap, usage: String): Unit = {
    require(options.contains('in), usage)

    val inputFileName = options('in).toString
    val inputFile =
      if (inputFileName.contains("#")) File(inputFileName.substring(0, inputFileName.lastIndexOf("#")))
      else File(inputFileName)

    val inputFormulas = ArchiveParser.parseFromFile(inputFileName)
    var outputFile = inputFile.changeExtension("c")
    if (options.contains('out)) outputFile = File(options('out).toString)

    val vars: Option[Set[BaseVariable]] =
      if (options.contains('vars)) Some(options('vars).asInstanceOf[Array[BaseVariable]].toSet)
      else None

    val interval = options.getOrElse('interval, true).asInstanceOf[Boolean]
    val head = EvidencePrinter.stampHead(options)
    val quantitative = options.getOrElse('quantitative, false).asInstanceOf[Boolean]
    val written = inputFormulas.map(e => {
      val outputFileName =
        if (inputFormulas.size <= 1) outputFile.toString()
        else {
          val ext = outputFile.extension
          outputFile.addExtension(e.name.replaceAll("\\s", "_")).addExtension(ext).toString()
        }
      if (quantitative) codegenQuantitative(e, outputFileName, head, vars, quantitative.toString)
      else codegen(e, interval, outputFileName, head, vars)
      outputFileName
    })
    println("Generated\n  " + written.mkString("\n  "))
  }

  def codegen(entry: ParsedArchiveEntry, interval: Boolean, outputFileName: String, head: String,
              vars: Option[Set[BaseVariable]]): Unit = {
    if (interval) {
      //@todo check that when assuming the output formula as an additional untrusted lemma, the Provable isProved.
      System.err.println("Cannot yet augment compiled code with interval arithmetic to guard against floating-point roundoff errors\n(use -nointerval instead)")

      println("Interval arithmetic: unfinished")
      System.err.println("Interval arithmetic: unfinished")
      //@todo wipe out output file PrintWriter above has already emptied the output file
      //@todo pw.close()
      exit(-1)
      // TODO what to to when proof cannot be checked?
    } else {
      println("Interval arithmetic: Skipped interval arithmetic generation\n(use -interval to guard against floating-point roundoff errors)")
    }

    val inputFormula = entry.model.asInstanceOf[Formula]

    //@note codegen in C format only regardless of file extension
    val theVars = vars match {
      case Some(v) => v
      case None => StaticSemantics.vars(inputFormula).symbols.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])
    }

    val codegenStart = Platform.currentTime
    //@todo input variables (nondeterministically assigned in original program)
    val output = (new CGenerator(new CMonitorGenerator()))(inputFormula, theVars, Set(), outputFileName)
    Console.println("[codegen time " + (Platform.currentTime - codegenStart) + "ms]")
    val pw = new PrintWriter(outputFileName)
    pw.write(head)
    pw.write("/* @evidence: print of CGenerator of input */\n\n")
    pw.write(output._1 + "\n" + output._2)
    pw.close()
  }

  def codegenQuantitative(entry: ParsedArchiveEntry, outputFileName: String, head: String,
                          vars: Option[Set[BaseVariable]], kind: String): Unit = {
    import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
    val (monitorFml: Formula, monitorStateVars: Set[BaseVariable]) =
      if (entry.model.asInstanceOf[Formula].isFOL) {
        val stateVars = vars match {
          case Some(v) => v
          case None => StaticSemantics.vars(entry.model).symbols.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])
        }
        (entry.model.asInstanceOf[Formula], stateVars)
      } else {
        val model@Imply(_, Box(Loop(Compose(prg, _)), _)) = entry.model

        val nonlinearModelApprox = ModelPlex.createNonlinearModelApprox(entry.name, entry.tactics.head._3)(model)
        val Imply(init, Box(Loop(Compose(
        ctrl,
        plant@Compose(x0Ghosts, Compose(Test(x0EvolDomain), Compose(nondetPlant, Test(evolDomain)))))), safe)) = nonlinearModelApprox._1

        val monitorStateVars = vars match {
          case Some(v) => v.toSeq
          case None => kind match {
            case "model" => StaticSemantics.boundVars(nonlinearModelApprox._1).symbols.toSeq
            case "ctrl" => StaticSemantics.boundVars(ctrl).symbols.toSeq
            case "plant" => StaticSemantics.boundVars(plant).symbols.toSeq
          }
        }

        val (monitorInput, assumptions) = kind match {
          case "model" => ModelPlex.createMonitorSpecificationConjecture(nonlinearModelApprox._1, monitorStateVars: _*)
          case "ctrl" => ModelPlex.createMonitorSpecificationConjecture(Imply(init, Box(Loop(ctrl), safe)), monitorStateVars: _*)
          case "plant" => ModelPlex.createMonitorSpecificationConjecture(Imply(init, Box(Loop(plant), safe)), monitorStateVars: _*)
        }

        val simplifier = SimplifierV3.simpTac(taxs = SimplifierV3.composeIndex(
          SimplifierV3.groundEqualityIndex, SimplifierV3.defaultTaxs))
        val monitorTactic = DebuggingTactics.print("Deriving Monitor") &
          ModelPlex.controllerMonitorByChase(1) &
          DebuggingTactics.print("Chased") &
          SaturateTactic(ModelPlex.optimizationOneWithSearch(ToolProvider.simplifierTool(), assumptions)(1)) &
          DebuggingTactics.print("Quantifiers instantiated") &
          simplifier(1) & DebuggingTactics.print("Monitor Result")

        val monitorResult = TactixLibrary.proveBy(monitorInput, monitorTactic)
        val monitorFml = monitorResult.subgoals.head.succ.head
        (monitorFml, monitorStateVars.toSet)
      }

    val reassociatedMonitorFml = FormulaTools.reassociate(monitorFml)
    //proveBy(Equiv(modelMonitorFml, reassociatedCtrlMonitorFml), TactixLibrary.prop)
    val monitorProg = TactixLibrary.proveBy(reassociatedMonitorFml, ModelPlex.chaseToTests(combineTests=false)(1)*2).subgoals.head.succ.head
    val inputs = CGenerator.getInputs(monitorProg)
    val monitorCode = (new CGenerator(new CMonitorGenerator()))(monitorProg, monitorStateVars, inputs, "Monitor")

    val pw = new PrintWriter(outputFileName)
    pw.write(head)
    pw.write("/* @evidence: print of CGenerator of input */\n\n")
    pw.write(monitorCode._1 + "\n" + monitorCode._2)
    pw.close()
  }
}
