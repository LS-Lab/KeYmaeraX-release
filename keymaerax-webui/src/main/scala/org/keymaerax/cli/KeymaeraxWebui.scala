/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.keymaerax.bellerophon.IOListeners.PrintProgressListener
import org.keymaerax.bellerophon._
import org.keymaerax.bellerophon.parser.BellePrettyPrinter
import org.keymaerax.btactics._
import org.keymaerax.core._
import org.keymaerax.hydra.{
  DBTools,
  DbProofTree,
  LabelledTraceToTacticConverter,
  TempDBTools,
  VerbatimTraceToTacticConverter,
  VerboseTraceToTacticConverter,
}
import org.keymaerax.info.TechnicalName
import org.keymaerax.lemma.{Lemma, LemmaDBFactory}
import org.keymaerax.parser.StringConverter._
import org.keymaerax.parser._
import org.keymaerax.pt.{HOLConverter, IsabelleConverter, ProvableSig, TermProvable}
import org.keymaerax.tools.{ToolEvidence, ToolName}
import org.keymaerax.{Configuration, FileConfiguration}
import org.apache.commons.lang3.StringUtils

import java.io.PrintWriter
import scala.collection.immutable.{List, Nil}
import scala.concurrent.Await
import scala.concurrent.duration.Duration
import scala.reflect.io.File

/** Command-line interface for the KeYmaera X webui jar. */
object KeymaeraxWebui {
  def main(args: Array[String]): Unit = {
    val options = Options.parseArgs(s"$TechnicalName-webui", args)
    if (!options.launch) Relauncher.relaunchOrExit(args)

    Configuration.setConfiguration(FileConfiguration)
    GlobalLockChecks.acquireGlobalLockFileOrExit(graphical = true)

    try {
      KeymaeraxCore.initializeConfig(options)
      runCommand(options)
    } finally { KeymaeraxCore.shutdownProver() }
  }

  def runCommand(options: Options): Unit = options.command match {
    case Some(cmd: Command.Codegen) =>
      // Quantitative ModelPlex uses Mathematica to simplify formulas
      val tool = if (cmd.quantitative) ToolName.Mathematica else ToolName.Z3
      val toolConfig = KeymaeraxCore.toolConfigFromFile(tool)
      val vars = cmd.vars.map(makeVariables(_).toSet)
      KeymaeraxCore.initializeProver(KeymaeraxCore.combineToolConfigs(options.toToolConfig, toolConfig))
      CodeGen.codegen(
        in = cmd.in,
        out = cmd.out,
        quantitative = cmd.quantitative,
        interval = cmd.interval,
        vars = vars,
        args = options.args,
      )
    case Some(cmd: Command.Modelplex) =>
      KeymaeraxCore.initializeProver(
        KeymaeraxCore.combineToolConfigs(options.toToolConfig, KeymaeraxCore.toolConfigFromFile(ToolName.Z3))
      )
      modelplex(
        in = cmd.in,
        out = cmd.out,
        ptOut = cmd.ptOut,
        vars = cmd.vars,
        verify = cmd.verify,
        sandbox = cmd.sandbox,
        monitor = cmd.monitor,
        fallback = cmd.fallback,
        args = options.args,
      )
    case Some(cmd: Command.Repl) =>
      KeymaeraxCore.initializeProver(
        KeymaeraxCore.combineToolConfigs(options.toToolConfig, KeymaeraxCore.toolConfigFromFile(ToolName.Z3))
      )
      repl(model = cmd.model, tactic = cmd.tactic, scaladefs = cmd.scaladefs)
    // TODO Turn this into separate webui-only command (maybe named "convertTactics")
    case Some(cmd: Command.ConvertTactics) =>
      if (cmd.out.isEmpty) options.printUsageAndExitWithError()
      KeymaeraxCore.initializeProver(
        KeymaeraxCore.combineToolConfigs(options.toToolConfig, KeymaeraxCore.toolConfigFromFile(ToolName.Z3))
      )
      convertTactics(in = cmd.in, out = cmd.out, conversion = cmd.conversion)
    case Some(Command.Ui) =>
      LoadingDialogFactory()
      DatabaseChecks.exitIfDeprecated()
      LoadingDialogFactory().addToStatus(15, Some("Checking lemma caches..."))
      LemmaCacheChecks.clearCacheIfDeprecated()
      LoadingDialogFactory().addToStatus(10, Some("Checking port..."))
      PortChecks.ensureWebuiPortCanBeBoundOrExit()
      Await.result(org.keymaerax.hydra.NonSSLBoot.run(options), Duration.Inf)
    case _ => org.keymaerax.cli.KeymaeraxCore.runCommand(options)
  }

  private def makeVariables(varNames: Seq[String]): Seq[BaseVariable] = {
    varNames.map(vn =>
      Parser.parser(vn) match {
        case v: BaseVariable => v
        case v => throw new IllegalArgumentException("String " + v + " is not a valid variable name")
      }
    )
  }

  /**
   * ModelPlex monitor synthesis for the given input files
   * {{{KeYmaeraXPrettyPrinter(ModelPlex(vars)(KeYmaeraXProblemParser(input))}}}
   *
   * @param in
   *   Input file
   * @param out
   *   Output file
   * @param vars
   *   The list of variables
   */
  def modelplex(
      in: String,
      out: Option[String],
      ptOut: Option[String],
      vars: Option[Seq[String]],
      verify: Boolean,
      sandbox: Boolean,
      monitor: Option[ModelPlexKind.Value],
      fallback: Option[String],
      args: Seq[String],
  ): Unit = {
    // @TODO remove option, hol config no longer necessary
    if (ptOut.isDefined) {
      // @TODO: Actual produce proof terms here, right now this option is overloaded to produce hol config instead
      ProvableSig.PROOF_TERMS_ENABLED = false
    } else { ProvableSig.PROOF_TERMS_ENABLED = false }

    val inputEntry = ArchiveParser.parseFromFile(in).head
    val inputModel = inputEntry.defs.exhaustiveSubst(inputEntry.model.asInstanceOf[Formula])

    val verifyOption: Option[ProvableSig => Unit] =
      if (verify) {
        Some({
          case ptp: TermProvable =>
            val conv = new IsabelleConverter(ptp.pt)
            val source = conv.sexp
            val pwPt = new PrintWriter(ptOut.get + ".pt")
            pwPt.write(source)
            pwPt.close()
          case _: ProvableSig => ()
        })
      } else Some(_ => ())
    // val isarOption = options.getOrElse('isar,false).asInstanceOf[Boolean]

    val inputFileName = in.split('#')(0).dropRight(4)

    val outputFileName = out.getOrElse(inputFileName + ".kym")

    if (sandbox) {
      val fallbackProgram = fallback match {
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
        Some(fallbackProgram),
        kind = ModelPlexKind.Ctrl,
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
    } else if (vars.isDefined) {
      val parsedVars = makeVariables(vars.get).toList
      val kind = monitor.getOrElse(ModelPlexKind.Model)
      val result = ModelPlex(parsedVars, kind, verifyOption)(inputModel)
      printModelplexResult(inputModel, result, outputFileName, ptOut, vars = vars, args = args)
    } else {
      val kind = monitor.getOrElse(ModelPlexKind.Model)
      val result = ModelPlex(inputModel, kind, verifyOption)
      printModelplexResult(inputModel, result, outputFileName, ptOut, vars = vars, args = args)
    }
  }

  private def printModelplexResult(
      model: Formula,
      fml: Formula,
      outputFileName: String,
      ptOut: Option[String],
      vars: Option[Seq[String]],
      args: Seq[String],
  ): Unit = {
    val output = PrettyPrinter(fml)
    val reparse = Parser(output)
    assert(reparse == fml, "parse of print is identity")
    val pw = new PrintWriter(outputFileName)
    pw.write(EvidencePrinter.stampHead(args))
    pw.write("/* @evidence: parse of print of ModelPlex proof output */\n\n")
    pw.write(
      "/************************************\n * Generated by KeYmaera X ModelPlex\n ************************************/\n\n"
    )
    pw.write(
      "/**\n * @param variables are for the state before the controller run\n * @param post() function symbols are for the state after the controller run\n * @param other function symbols are constant\n */\n\n"
    )
    pw.write(output)
    pw.close()

    ptOut match {
      case Some(path: String) =>
        val pwHOL = new PrintWriter(outputFileName + ".holconfiggen")
        // @TODO: Robustify
        val Imply(init, Box(Compose(Test(bounds), Loop(Compose(ctrl, plant))), safe)) = model
        val consts = StaticSemantics.signature(model)
        val parsedVars = makeVariables(vars.get).toList
        pwHOL.write(HOLConverter.configFile(consts, parsedVars, bounds, init, fml))
        pwHOL.close()

      case None => ()
    }
  }

  def repl(model: String, tactic: Option[String], scaladefs: Option[String]): Unit = {
    val modelFileNameDotKyx = model
    val tacticFileNameDotKyt = tactic
    val scaladefsFilename = scaladefs
    assert(
      modelFileNameDotKyx.endsWith(".kyx"),
      "\n[Error] Wrong model file name " + modelFileNameDotKyx +
        " used for -repl! Should. Please use: -repl MODEL.kyx TACTIC.kyt",
    )
    tacticFileNameDotKyt.foreach(name =>
      assert(
        name.endsWith(".kyt"),
        "\n[Error] Wrong tactic file name " + name + " used for -repl! Should. Please use: -repl MODEL.kyx TACTIC.kyt",
      )
    )
    val modelInput = {
      val source = scala.io.Source.fromFile(modelFileNameDotKyx, org.keymaerax.core.ENCODING)
      try source.mkString
      finally source.close()
    }
    val tacticInput = tacticFileNameDotKyt.map(path => {
      val source = scala.io.Source.fromFile(path, org.keymaerax.core.ENCODING)
      try source.mkString
      finally source.close()
    })
    val defsInput = scaladefsFilename.map(path => {
      val source = scala.io.Source.fromFile(path, org.keymaerax.core.ENCODING)
      try source.mkString
      finally source.close()
    })
    val inputFormula: Formula = ArchiveParser.parseAsFormula(modelInput)
    new BelleREPL(inputFormula, tacticInput, defsInput, tacticFileNameDotKyt, scaladefsFilename).run()
  }

  /**
   * Executes all entries in the input file to convert their tactics into `options('conversion)` format. Prints the
   * result to the output file.
   *
   * @param in
   *   Input file
   * @param out
   *   Output file
   */
  def convertTactics(in: String, out: String, conversion: TacticConversion.Value): Unit = {
    val src = scala.io.Source.fromFile(in.split("#")(0))
    val fileContent =
      try { src.mkString }
      finally { src.close() }
    val archiveContent = ArchiveParser.parseFromFile(in)

    def convertTactic(e: ParsedArchiveEntry): ParsedArchiveEntry = e.copy(tactics =
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
              val converter = conversion match {
                case TacticConversion.Verbose => new VerboseTraceToTacticConverter(tree.info.defs(tempDB.db))
                case TacticConversion.Labelled => new LabelledTraceToTacticConverter(tree.info.defs(tempDB.db))
                case TacticConversion.Verbatim => new VerbatimTraceToTacticConverter(tree.info.defs(tempDB.db))
                // TODO A succinct tactic converter that prints with index positions
              }
              val (converted, _) = tree.tacticString(converter)
              println("==== Done tactic " + name)
              (name, converted, t)
          }
        })
    )

    val convertedContent = archiveContent
      .map(e => e -> convertTactic(e))
      .foldLeft(fileContent)({ case (content, (orig, conv)) =>
        val entryOnwards = content.substring(content.indexOf(orig.name))
        val entryOnwardsConverted = orig
          .tactics
          .map(_._2)
          .zip(conv.tactics.map(_._2))
          .foldLeft(entryOnwards)({ case (fc, (ot, ct)) => StringUtils.replaceOnce(fc, ot, ct) })
        content.replace(entryOnwards, entryOnwardsConverted)
      })

    val pw = new PrintWriter(out)
    pw.write(convertedContent)
    pw.close()
  }
}
