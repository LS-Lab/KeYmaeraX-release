/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.PrintProgressListener
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX._
import edu.cmu.cs.ls.keymaerax.cli.{CodeGen, EvidencePrinter, Options, Usage}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.{
  DBTools,
  DbProofTree,
  LabelledTraceToTacticConverter,
  TempDBTools,
  VerbatimTraceToTacticConverter,
  VerboseTraceToTacticConverter,
}
import edu.cmu.cs.ls.keymaerax.info.Version
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.pt.{HOLConverter, IsabelleConverter, ProvableSig, TermProvable}
import edu.cmu.cs.ls.keymaerax.scalatactic.ScalaTacticCompiler
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.apache.commons.lang3.StringUtils

import java.io.PrintWriter
import scala.annotation.tailrec
import scala.collection.immutable.{List, Nil}
import scala.reflect.io.File
import scala.util.Random

/**
 * Command-line interface launcher for [[http://keymaeraX.org/ KeYmaera X]], the aXiomatic Tactical Theorem Prover for
 * Hybrid Systems and Hybrid Games.
 *
 *   - `[[edu.cmu.cs.ls.keymaerax.core]]` - KeYmaera X kernel, proof certificates, main data structures
 *   - `[[edu.cmu.cs.ls.keymaerax.btactics]]` - Tactic language library
 *   - `[[edu.cmu.cs.ls.keymaerax.bellerophon]]` - Bellerophon tactic language and tactic interpreter
 *
 * @author
 *   Stefan Mitsch
 * @author
 *   Andre Platzer
 * @author
 *   Ran Ji
 * @author
 *   Brandon Bohrer
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In
 *   Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]].
 *   Springer, 2018.
 * @see
 *   Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Volp and Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_36 KeYmaera X: An axiomatic tactical theorem prover for hybrid systems]].
 *   In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015.
 *   [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in
 *   Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.launcher.Main]]
 */
object KeYmaeraX {

  /** Names of actions that full KeYmaera X supports. */
  object Modes {
    val CODEGEN: String = edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.Modes.CODEGEN
    val MODELPLEX: String = edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.Modes.MODELPLEX
    val PROVE: String = edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.Modes.PROVE
    val REPL: String = edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.Modes.REPL
    val CONVERT: String = edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.Modes.CONVERT
    val SETUP: String = edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.Modes.SETUP
    val UI: String = "ui"
    val modes: Set[String] = Set(CODEGEN, CONVERT, MODELPLEX, PROVE, REPL, UI, SETUP)
  }

  /** Usage -help information. */
  val usage: String = Usage.fullUsage

  private def launched(): Unit = {
    LAUNCH = true
    // println("Launching KeYmaera X")
  }
  var LAUNCH: Boolean = false

  /**
   * main function to start KeYmaera X from command line. Other entry points exist but this one is best for command line
   * interfaces.
   */
  def main(args: Array[String]): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    if (args.length > 0 && List("-help", "--help", "-h", "-?").contains(args(0))) {
      println(help)
      exit(1)
    }
    println(s"KeYmaera X Prover $Version")
    println("Use option -help for usage and license information")
    // @note 'commandLine to preserve evidence of what generated the output; default mode: UI
    val options = nextOption(Options(commandLine = Some(args.mkString(" ")), mode = Some(Modes.UI)), args.toList)

    try {
      // @todo allow multiple passes by filter architecture: -prove bla.key -tactic bla.scal -modelplex -codegen
      options.mode match {
        case Some(Modes.CODEGEN) =>
          val toolConfig =
            if (options.quantitative.isDefined) {
              configFromFile(Tools.MATHEMATICA) // @note quantitative ModelPlex uses Mathematica to simplify formulas
            } else { configFromFile("z3") }
          initializeProver(combineConfigs(options.toOptionMap, toolConfig), usage)
          CodeGen.codegen(options.toOptionMap, usage)
        case Some(Modes.MODELPLEX) =>
          initializeProver(combineConfigs(options.toOptionMap, configFromFile("z3")), usage)
          modelplex(options.toOptionMap)
        case Some(Modes.REPL) =>
          initializeProver(combineConfigs(options.toOptionMap, configFromFile("z3")), usage)
          repl(options.toOptionMap)
        case Some(Modes.UI) => launchUI(args) // @note prover initialized in web UI launcher
        case Some(Modes.CONVERT) => options.conversion match {
            case Some("verboseTactics") | Some("verbatimTactics") =>
              initializeProver(combineConfigs(options.toOptionMap, configFromFile("z3")), usage)
              convertTactics(options.toOptionMap, usage)
            case _ => runCommand(options, usage)
          }

        case _ => runCommand(options, usage)
      }
    } finally { shutdownProver() }
  }

  /** Statistics about size of prover kernel. */
  def stats: String = { "    with " + Provable.rules.size + " axiomatic rules and " + Provable.axiom.size + " axioms" }

  /** KeYmaera X -help string. */
  def help: String = stats + "\n" + usage

  private def configFromFile(defaultTool: String): OptionMap = {
    Configuration.getString(Configuration.Keys.QE_TOOL).getOrElse(defaultTool).toLowerCase() match {
      case Tools.MATHEMATICA => Map(Symbol("tool") -> Tools.MATHEMATICA) ++
          ToolConfiguration.mathematicaConfig(Map.empty).map({ case (k, v) => Symbol(k) -> v })
      case Tools.WOLFRAMENGINE => Map(Symbol("tool") -> Tools.WOLFRAMENGINE) ++
          ToolConfiguration.wolframEngineConfig(Map.empty).map({ case (k, v) => Symbol(k) -> v })
      case Tools.Z3 => Map(Symbol("tool") -> Tools.Z3) ++
          ToolConfiguration.z3Config(Map.empty).map({ case (k, v) => Symbol(k) -> v })
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
  }

  private def makeVariables(varNames: Array[String]): Array[BaseVariable] = {
    varNames.map(vn =>
      Parser.parser(vn) match {
        case v: BaseVariable => v
        case v => throw new IllegalArgumentException("String " + v + " is not a valid variable name")
      }
    )
  }

  @tailrec
  def nextOption(map: Options, list: List[String]): Options = {
    list match {
      case Nil => map
      case "-help" :: _ => println(usage); exit(1)
      // actions
      case "-sandbox" :: tail => nextOption(map.copy(sandbox = Some(true)), tail)
      case "-modelplex" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-"))
          nextOption(map.copy(mode = Some(Modes.MODELPLEX), in = Some(value)), tail)
        else { Usage.optionErrorReporter("-modelPlex", usage); exit(1) }
      case "-isar" :: tail => nextOption(map.copy(isar = Some(true)), tail)
      case "-codegen" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-"))
          nextOption(map.copy(mode = Some(Modes.CODEGEN), in = Some(value)), tail)
        else { Usage.optionErrorReporter("-codegen", usage); exit(1) }
      case "-quantitative" :: tail => nextOption(map.copy(quantitative = Some(true)), tail)
      case "-repl" :: model :: tactic_and_scala_and_tail =>
        val posArgs = tactic_and_scala_and_tail.takeWhile(x => !x.startsWith("-"))
        val restArgs = tactic_and_scala_and_tail.dropWhile(x => !x.startsWith("-"))
        val newMap = posArgs match {
          case Nil => map
          case tactic :: Nil => map.copy(tactic = Some(tactic))
          case tactic :: scaladefs :: _ => map.copy(tactic = Some(tactic), scaladefs = Some(scaladefs))
        }
        if (model.nonEmpty && !model.toString.startsWith("-"))
          nextOption(newMap.copy(mode = Some(Modes.REPL), model = Some(model)), restArgs)
        else { Usage.optionErrorReporter("-repl", usage); exit(1) }
      case "-ui" :: tail => /*launchUI(tail.toArray);*/ nextOption(map.copy(mode = Some(Modes.UI)), tail)
      // action options
      case "-out" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-")) nextOption(map.copy(out = Some(value)), tail)
        else { Usage.optionErrorReporter("-out", usage); exit(1) }
      case "-fallback" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-")) nextOption(map.copy(fallback = Some(value)), tail)
        else { Usage.optionErrorReporter("-fallback", usage); exit(1) }
      case "-vars" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-"))
          nextOption(map.copy(vars = Some(makeVariables(value.split(",")))), tail)
        else { Usage.optionErrorReporter("-vars", usage); exit(1) }
      case "-monitor" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-")) nextOption(map.copy(monitor = Some(Symbol(value))), tail)
        else { Usage.optionErrorReporter("-monitor", usage); exit(1) }
      case "-interactive" :: tail => nextOption(map.copy(interactive = Some(true)), tail)
      // aditional options
      case "-interval" :: tail => require(map.interval.isEmpty); nextOption(map.copy(interval = Some(true)), tail)
      case "-nointerval" :: tail => require(map.interval.isEmpty); nextOption(map.copy(interval = Some(false)), tail)
      case "-dnf" :: tail => require(map.dnf.isEmpty); nextOption(map.copy(dnf = Some(true)), tail)
      // global options
      case "-launch" :: tail => launched(); nextOption(map, tail)
      case "-timeout" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-")) nextOption(map.copy(timeout = Some(value.toLong)), tail)
        else { Usage.optionErrorReporter("-timeout", usage); exit(1) }
      case _ =>
        val (options, unprocessedArgs) = edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.nextOption(map, list, usage)
        if (unprocessedArgs == list) {
          Usage.optionErrorReporter(unprocessedArgs.head, usage)
          exit(1)
        } else nextOption(options, unprocessedArgs)
    }
  }

  /**
   * ModelPlex monitor synthesis for the given input files
   * {{{KeYmaeraXPrettyPrinter(ModelPlex(vars)(KeYmaeraXProblemParser(input))}}}
   *
   * @param options
   *   in describes input file name, vars describes the list of variables, out describes the output file name.
   */
  def modelplex(options: OptionMap): Unit = {
    // @TODO remove option, hol config no longer necessary
    if (options.contains(Symbol("ptOut"))) {
      // @TODO: Actual produce proof terms here, right now this option is overloaded to produce hol config instead
      ProvableSig.PROOF_TERMS_ENABLED = false
    } else { ProvableSig.PROOF_TERMS_ENABLED = false }
    require(options.contains(Symbol("in")), usage)

    val in = options(Symbol("in")).toString
    val inputEntry = ArchiveParser.parseFromFile(in).head
    val inputModel = inputEntry.defs.exhaustiveSubst(inputEntry.model.asInstanceOf[Formula])

    val verifyOption: Option[ProvableSig => Unit] =
      if (options.getOrElse(Symbol("verify"), false).asInstanceOf[Boolean]) {
        Some({
          case ptp: TermProvable =>
            val conv = new IsabelleConverter(ptp.pt)
            val source = conv.sexp
            val pwPt = new PrintWriter(options(Symbol("ptOut")).asInstanceOf[String] + ".pt")
            pwPt.write(source)
            pwPt.close()
          case _: ProvableSig => ()
        })
      } else Some { case _ => () }
    // val isarOption = options.getOrElse('isar,false).asInstanceOf[Boolean]

    val inputFileName = in.split('#')(0).dropRight(4)

    val outputFileName =
      if (options.contains(Symbol("out"))) options(Symbol("out")).toString else inputFileName + ".kym"

    val kind =
      if (options.contains(Symbol("sandbox"))) Symbol("sandbox")
      else if (options.contains(Symbol("monitor"))) options(Symbol("monitor")).asInstanceOf[Symbol]
      else Symbol("model")

    if (options.contains(Symbol("sandbox"))) {
      val fallback = options.get(Symbol("fallback")) match {
        case Some(fallbackPrgString: String) => fallbackPrgString.asProgram
        case _ => inputEntry.model match {
            case Imply(_, Box(Loop(Compose(ctrl, _)), _)) => ctrl
            case Imply(_, Box(Compose(ctrl, _), _)) => ctrl
            case _ => throw new IllegalArgumentException(
                "Unable to extract fallback from input model. Please provide fallback program with option -fallback."
              )
          }
      }

      // check safety proof
      println(s"Checking safety proof ${inputEntry.name}...")
      assert(
        TactixLibrary.proveBy(inputEntry.model.asInstanceOf[Formula], inputEntry.tactics.head._3).isProved,
        s"Sandbox synthesis requires a provably safe input model, but ${inputEntry.name} is not proved.",
      )
      println(s"Done checking safety proof ${inputEntry.name}")

      println("Synthesizing sandbox and safety proof...")
      val ((sandbox, sbTactic), lemmas) = ModelPlex.createSandbox(
        inputEntry.name,
        inputEntry.tactics.head._3,
        Some(fallback),
        kind = Symbol("ctrl"),
        checkProvable = None,
        synthesizeProofs = false,
        defs = inputEntry.defs,
      )(inputModel)
      println("Done synthesizing sandbox and safety proof")

      val db = new TempDBTools(Nil)

      val lemmaEntries = lemmas.map({ case (name, fml, tactic) =>
        val serializableTactic = db.extractSerializableTactic(fml, tactic)
        ParsedArchiveEntry(
          name,
          "lemma",
          "",
          "",
          Declaration(Map.empty),
          fml,
          (name + " Proof", BellePrettyPrinter(serializableTactic), serializableTactic) :: Nil,
          Nil,
          Map.empty,
        )
      })
      // check and store lemmas
      lemmaEntries.foreach(entry => {
        println(s"Checking sandbox lemma ${entry.name}...")
        val lemmaProof = TactixLibrary.proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3)
        assert(lemmaProof.isProved, s"Aborting sandbox synthesis: sandbox lemma ${entry.name} was not provable.")
        println(s"Done checking sandbox lemma ${entry.name}")
        val lemmaName = "user" + File.separator + entry.name
        if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
        val evidence = Lemma.requiredEvidence(
          lemmaProof,
          ToolEvidence(List("tool" -> "KeYmaera X", "model" -> entry.fileContent, "tactic" -> entry.tactics.head._2)) ::
            Nil,
        )
        LemmaDBFactory.lemmaDB.add(new Lemma(lemmaProof, evidence, Some(lemmaName)))
      })

      val serializableTactic = db.extractSerializableTactic(sandbox, sbTactic)
      val sandboxEntry = ParsedArchiveEntry(
        inputEntry.name + " Sandbox",
        "theorem",
        "",
        "",
        Declaration(Map.empty),
        sandbox,
        (inputEntry.name + " Sandbox Proof", BellePrettyPrinter(serializableTactic), serializableTactic) :: Nil,
        Nil,
        Map.empty,
      )
      // check sandbox proof
      println("Checking sandbox safety...")
      assert(
        TactixLibrary.proveBy(sandboxEntry.model.asInstanceOf[Formula], sandboxEntry.tactics.head._3).isProved,
        "Aborting sandbox synthesis: sandbox safety was not derivable from input model safety proof.",
      )
      println("Done checking sandbox safety")

      val archive = (lemmaEntries :+ sandboxEntry)
        .map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))(_))
        .mkString("\n\n")
      val pw = new PrintWriter(outputFileName)
      pw.write(archive)
      pw.close()
      println(s"Sandbox synthesis successful: $outputFileName")
    } else if (options.contains(Symbol("vars"))) {
      val result =
        ModelPlex(options(Symbol("vars")).asInstanceOf[Array[Variable]].toList, kind, verifyOption)(inputModel)
      printModelplexResult(inputModel, result, outputFileName, options)
    } else {
      val result = ModelPlex(inputModel, kind, verifyOption)
      printModelplexResult(inputModel, result, outputFileName, options)
    }
  }

  private def printModelplexResult(model: Formula, fml: Formula, outputFileName: String, options: OptionMap): Unit = {
    val output = PrettyPrinter(fml)
    val reparse = Parser(output)
    assert(reparse == fml, "parse of print is identity")
    val pw = new PrintWriter(outputFileName)
    pw.write(EvidencePrinter.stampHead(options))
    pw.write("/* @evidence: parse of print of ModelPlex proof output */\n\n")
    pw.write(
      "/************************************\n * Generated by KeYmaera X ModelPlex\n ************************************/\n\n"
    )
    pw.write(
      "/**\n * @param variables are for the state before the controller run\n * @param post() function symbols are for the state after the controller run\n * @param other function symbols are constant\n */\n\n"
    )
    pw.write(output)
    pw.close()

    options.get(Symbol("ptOut")) match {
      case Some(path: String) =>
        val pwHOL = new PrintWriter(outputFileName + ".holconfiggen")
        // @TODO: Robustify
        val Imply(init, Box(Compose(Test(bounds), Loop(Compose(ctrl, plant))), safe)) = model
        val consts = StaticSemantics.signature(model)
        pwHOL.write(
          HOLConverter
            .configFile(consts, options(Symbol("vars")).asInstanceOf[Array[Variable]].toList, bounds, init, fml)
        )
        pwHOL.close()

      case None => ()
    }
  }

  def repl(options: OptionMap): Unit = {
    require(options.contains(Symbol("model")), usage)
    val modelFileNameDotKyx = options(Symbol("model")).toString
    val tacticFileNameDotKyt = options.get(Symbol("tactic")).map(_.toString)
    val scaladefsFilename = options.get(Symbol("scaladefs")).map(_.toString)
    assert(
      modelFileNameDotKyx.endsWith(".kyx"),
      "\n[Error] Wrong model file name " + modelFileNameDotKyx +
        " used for -repl! Should. Please use: -repl MODEL.kyx TACTIC.kyt",
    )
    tacticFileNameDotKyt.foreach(name =>
      assert(
        name.endsWith(".kyt"),
        "\n[Error] Wrong tactic file name " + tacticFileNameDotKyt +
          " used for -repl! Should. Please use: -repl MODEL.kyx TACTIC.kyt",
      )
    )
    val modelInput = {
      val source = scala.io.Source.fromFile(modelFileNameDotKyx, edu.cmu.cs.ls.keymaerax.core.ENCODING)
      try source.mkString
      finally source.close()
    }
    val tacticInput = tacticFileNameDotKyt.map(path => {
      val source = scala.io.Source.fromFile(path, edu.cmu.cs.ls.keymaerax.core.ENCODING)
      try source.mkString
      finally source.close()
    })
    val defsInput = scaladefsFilename.map(path => {
      val source = scala.io.Source.fromFile(path, edu.cmu.cs.ls.keymaerax.core.ENCODING)
      try source.mkString
      finally source.close()
    })
    val inputFormula: Formula = ArchiveParser.parseAsFormula(modelInput)
    new BelleREPL(inputFormula, tacticInput, defsInput, tacticFileNameDotKyt, scaladefsFilename).run()
  }

  /** Launch the web user interface */
  def launchUI(args: Array[String]): Unit = {
    val augmentedArgs =
      if (args.map(_.stripPrefix("-")).intersect(Modes.modes.toList).isEmpty) ("-" + Modes.UI) +: args else args
    if (LAUNCH) Main.main("-launch" +: augmentedArgs) else Main.main(augmentedArgs)
  }

  /**
   * Executes all entries in `options('in)` to convert their tactics into `options('conversion)` format. Prints the
   * result to `options('out)`.
   */
  def convertTactics(options: OptionMap, usage: String): Unit = {
    require(
      options.contains(Symbol("in")) && options.contains(Symbol("out")) && options.contains(Symbol("conversion")),
      usage,
    )

    val kyxFile = options(Symbol("in")).toString
    val how = options(Symbol("conversion")).toString

    val src = scala.io.Source.fromFile(kyxFile.split("#")(0))
    val fileContent =
      try { src.mkString }
      finally { src.close() }
    val archiveContent = ArchiveParser.parseFromFile(kyxFile)

    def convertTactic(e: ParsedArchiveEntry, how: String): ParsedArchiveEntry = e.copy(tactics =
      e.tactics
        .map({ case (name, tactic, t) =>
          tactic.trim.stripPrefix("expandAllDefs").trim.stripPrefix(";").trim match {
            case "auto" | "autoClose" | "master" => (name, tactic, t) // @todo record and export automated steps
            case _ =>
              println("==== Entry " + e.name + ": running tactic " + name + " for conversion")
              val additionalListeners = new PrintProgressListener(t, Nil) :: Nil
              val tempDB = new TempDBTools(additionalListeners)
              val proofId = tempDB.createProof(e.fileContent, e.name, name)
              val interpreter = SpoonFeedingInterpreter(
                proofId,
                -1,
                tempDB.db.createProof,
                e.defs,
                DBTools.listener(tempDB.db, additionalListeners = additionalListeners),
                ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
                0,
                strict = false,
                convertPending = false,
                recordInternal = false,
              )
              BelleInterpreter.setInterpreter(interpreter)
              BelleInterpreter(t, BelleProvable.plain(ProvableSig.startProof(e.model.asInstanceOf[Formula], e.defs)))
              val tree = DbProofTree(tempDB.db, proofId.toString)
              val converter = how match {
                case "verboseTactics" => new VerboseTraceToTacticConverter(tree.info.defs(tempDB.db))
                case "labelledTactics" => new LabelledTraceToTacticConverter(tree.info.defs(tempDB.db))
                case "verbatimTactics" => new VerbatimTraceToTacticConverter(tree.info.defs(tempDB.db))
                case "succinctTactics" => ??? // @todo a succinct tactic converter that prints with index positions
              }
              val (converted, _) = tree.tacticString(converter)
              println("==== Done tactic " + name)
              (name, converted, t)
          }
        })
    )

    val convertedContent = archiveContent
      .map(e => e -> convertTactic(e, how))
      .foldLeft(fileContent)({ case (content, (orig, conv)) =>
        val entryOnwards = content.substring(content.indexOf(orig.name))
        val entryOnwardsConverted = orig
          .tactics
          .map(_._2)
          .zip(conv.tactics.map(_._2))
          .foldLeft(entryOnwards)({ case (fc, (ot, ct)) => StringUtils.replaceOnce(fc, ot, ct) })
        content.replace(entryOnwards, entryOnwardsConverted)
      })

    val outFile = options(Symbol("out")).toString
    val pw = new PrintWriter(outFile)
    pw.write(convertedContent)
    pw.close()
  }

  // helpers

  /** Print brief information about all open goals in the proof tree under node */
  def printOpenGoals(node: ProvableSig): Unit = node.subgoals.foreach(g => printNode(g))

  def printNode(node: Sequent): Unit = node.toString + "\n"

  private val interactiveUsage = "Type a tactic command to apply to the current goal.\n" +
    "skip - ignore the current goal for now and skip to the next goal.\n" + "goals - list all open goals.\n" +
    "goal i - switch to goal number i\n" + "exit - quit the prover (or hit Ctrl-C any time).\n" +
    "help - will display this usage information.\n" +
    "Tactics will be reported back when a branch closes but may need cleanup.\n"

  /** KeYmaera C: A simple interactive command-line prover */
  @deprecated("Use web UI instead")
  private def interactiveProver(root: ProvableSig): ProvableSig = {
    val commands = io.Source.stdin.getLines()
    println(
      "KeYmaera X Interactive Command-line Prover\n" +
        "If you are looking for the more convenient web user interface,\nrestart with option -ui\n\n"
    )
    println(interactiveUsage)

    while (!root.isProved) {
      assert(root.subgoals.nonEmpty, "proofs that are not closed must have open goals")
      println("Open Goals: " + root.subgoals.size)
      var node = root.subgoals.head
      var current = root
      // println("=== " + node.tacticInfo.infos.getOrElse("branchLabel", "<none>") + " ===\n")
      var tacticLog = ""
      assert(!current.isProved, "open goals are not closed")
      while (!current.isProved) {
        printNode(node)
        System.out.flush()
        commands.next().trim match {
          case "" =>
          case "help" => println(interactiveUsage)
          case "exit" => exit(5)
          case "goals" =>
            val open = root.subgoals
            (1 to open.length).foreach(g => { println("Goal " + g); printNode(open(g - 1)) })
          case it if it.startsWith("goal ") =>
            try {
              val g = it.substring("goal ".length).toInt
              if (1 <= g && g <= root.subgoals.size) node = root.subgoals(g - 1) else println("No such goal: " + g)
            } catch { case e: NumberFormatException => println(e) }
          case "skip" =>
            if (root.subgoals.size >= 2) {
              // @todo skip to the next goal somewhere on the right of node, not to a random goal
              // @todo track this level skipping by closing and opening parentheses in the log
              var nextGoal = new Random().nextInt(root.subgoals.length)
              assert(0 <= nextGoal && nextGoal < root.subgoals.size, "random in range")
              node =
                if (root.subgoals(nextGoal) != node) root.subgoals(nextGoal)
                else {
                  val otherGoals = root.subgoals diff List(node)
                  assert(
                    otherGoals.length == root.subgoals.length - 1,
                    "removing one open goal decreases open goal count by 1",
                  )
                  nextGoal = new Random().nextInt(otherGoals.length)
                  assert(0 <= nextGoal && nextGoal < otherGoals.size, "random in range")
                  otherGoals(nextGoal)
                }
            } else { println("No other open goals to skip to") }
          case command: String =>
            // @note security issue since executing arbitrary input unsanitized
            val tacticGenerator = new ScalaTacticCompiler()
              .compile(tacticParsePrefix + command + tacticParseSuffix)
              .head
              .newInstance()
              .asInstanceOf[() => BelleExpr]
            val tactic = tacticGenerator()
            tacticLog += "& " + command + "\n"
            current = TactixLibrary.proveBy(node, tactic)
            // walk to the next open subgoal
            // continue walking if it has leaves
            while (!current.isProved && current.subgoals.nonEmpty) node = current.subgoals.head
          // @todo make sure to walk to siblings ultimately
        }
      }
      assert(current.isProved)
//      println("=== " + node.tacticInfo.infos.getOrElse("branchLabel", "<none>") + " === CLOSED")
      println(tacticLog)
    }
    root
  }

  // @todo import namespace of the user tactic *object* passed in -tactic
  private val tacticParsePrefix = """
                                    |import edu.cmu.cs.ls.keymaerax.bellerophon._
                                    |import edu.cmu.cs.ls.keymaerax.btactics._
                                    |import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
                                    |import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
                                    |import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
                                    |class InteractiveLocalTactic extends (() => BelleExpr) {
                                    |  def apply(): BelleExpr = {
                                    |
    """.stripMargin

  private val tacticParseSuffix = """
                                    |  }
                                    |}
    """.stripMargin
}
