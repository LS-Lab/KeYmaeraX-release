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
import edu.cmu.cs.ls.keymaerax.cli.{CodeGen, Command, EvidencePrinter, Options, Usage}
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
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.apache.commons.lang3.StringUtils

import java.io.PrintWriter
import scala.annotation.tailrec
import scala.collection.immutable.{List, Nil}
import scala.reflect.io.File

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
    val options = nextOption(Options(commandLine = Some(args.mkString(" "))), args.toList)

    try { runCommand(options, usage) }
    finally { shutdownProver() }
  }

  def runCommand(options: Options, usage: String): Unit = options.command match {
    case Some(Command.Codegen) =>
      // Quantitative ModelPlex uses Mathematica to simplify formulas
      val tool = if (options.quantitative.isDefined) Tools.MATHEMATICA else "z3"
      val toolConfig = toolConfigFromFile(tool)
      initializeProver(combineToolConfigs(options.toToolConfig, toolConfig), usage)
      CodeGen.codegen(options, usage)
    case Some(Command.Modelplex) =>
      initializeProver(combineToolConfigs(options.toToolConfig, toolConfigFromFile("z3")), usage)
      modelplex(options)
    case Some(Command.Repl) =>
      initializeProver(combineToolConfigs(options.toToolConfig, toolConfigFromFile("z3")), usage)
      repl(options)
    case Some(Command.Convert)
        if options.conversion.contains("verboseTactics") || options.conversion.contains("verbatimTactics") =>
      initializeProver(combineToolConfigs(options.toToolConfig, toolConfigFromFile("z3")), usage)
      convertTactics(options, usage)
    case _ => edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.runCommand(options, usage)
  }

  /** Statistics about size of prover kernel. */
  def stats: String = { "    with " + Provable.rules.size + " axiomatic rules and " + Provable.axiom.size + " axioms" }

  /** KeYmaera X -help string. */
  def help: String = stats + "\n" + usage

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
      // actions
      case "-sandbox" :: tail => nextOption(map.copy(sandbox = Some(true)), tail)
      case "-modelplex" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-"))
          nextOption(map.copy(command = Some(Command.Modelplex), in = Some(value)), tail)
        else { Usage.optionErrorReporter("-modelPlex", usage); exit(1) }
      case "-isar" :: tail => nextOption(map.copy(isar = Some(true)), tail)
      case "-codegen" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-"))
          nextOption(map.copy(command = Some(Command.Codegen), in = Some(value)), tail)
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
          nextOption(newMap.copy(command = Some(Command.Repl), model = Some(model)), restArgs)
        else { Usage.optionErrorReporter("-repl", usage); exit(1) }
      case "-ui" :: tail => nextOption(map.copy(command = Some(Command.Ui)), tail)
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
      case "-verify" :: tail => require(map.verify.isEmpty); nextOption(map.copy(verify = Some(true)), tail)
      case "-open" :: value :: tail =>
        if (value.nonEmpty && !value.startsWith("-")) nextOption(map.copy(open = Some(value)), tail)
        else { Usage.optionErrorReporter("-open", usage); exit(1) }
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
  def modelplex(options: Options): Unit = {
    // @TODO remove option, hol config no longer necessary
    if (options.ptOut.isDefined) {
      // @TODO: Actual produce proof terms here, right now this option is overloaded to produce hol config instead
      ProvableSig.PROOF_TERMS_ENABLED = false
    } else { ProvableSig.PROOF_TERMS_ENABLED = false }
    require(options.in.isDefined, usage)

    val in = options.in.get
    val inputEntry = ArchiveParser.parseFromFile(in).head
    val inputModel = inputEntry.defs.exhaustiveSubst(inputEntry.model.asInstanceOf[Formula])

    val verifyOption: Option[ProvableSig => Unit] =
      if (options.verify.getOrElse(false)) {
        Some({
          case ptp: TermProvable =>
            val conv = new IsabelleConverter(ptp.pt)
            val source = conv.sexp
            val pwPt = new PrintWriter(options.ptOut.get + ".pt")
            pwPt.write(source)
            pwPt.close()
          case _: ProvableSig => ()
        })
      } else Some(_ => ())
    // val isarOption = options.getOrElse('isar,false).asInstanceOf[Boolean]

    val inputFileName = in.split('#')(0).dropRight(4)

    val outputFileName = options.out.getOrElse(inputFileName + ".kym")

    val kind =
      if (options.sandbox.isDefined) Symbol("sandbox")
      else if (options.monitor.isDefined) options.monitor.get
      else Symbol("model")

    if (options.sandbox.isDefined) {
      val fallback = options.fallback match {
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
    } else if (options.vars.isDefined) {
      val result = ModelPlex(options.vars.get.toList, kind, verifyOption)(inputModel)
      printModelplexResult(inputModel, result, outputFileName, options)
    } else {
      val result = ModelPlex(inputModel, kind, verifyOption)
      printModelplexResult(inputModel, result, outputFileName, options)
    }
  }

  private def printModelplexResult(model: Formula, fml: Formula, outputFileName: String, options: Options): Unit = {
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

    options.ptOut match {
      case Some(path: String) =>
        val pwHOL = new PrintWriter(outputFileName + ".holconfiggen")
        // @TODO: Robustify
        val Imply(init, Box(Compose(Test(bounds), Loop(Compose(ctrl, plant))), safe)) = model
        val consts = StaticSemantics.signature(model)
        pwHOL.write(HOLConverter.configFile(consts, options.vars.get.toList, bounds, init, fml))
        pwHOL.close()

      case None => ()
    }
  }

  def repl(options: Options): Unit = {
    require(options.model.isDefined, usage)
    val modelFileNameDotKyx = options.model.get
    val tacticFileNameDotKyt = options.tactic
    val scaladefsFilename = options.scaladefs
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

  /**
   * Executes all entries in `options('in)` to convert their tactics into `options('conversion)` format. Prints the
   * result to `options('out)`.
   */
  def convertTactics(options: Options, usage: String): Unit = {
    require(options.in.isDefined && options.out.isDefined && options.conversion.isDefined, usage)

    val kyxFile = options.in.get
    val how = options.conversion.get

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

    val outFile = options.out.get
    val pw = new PrintWriter(outFile)
    pw.write(convertedContent)
    pw.close()
  }
}
