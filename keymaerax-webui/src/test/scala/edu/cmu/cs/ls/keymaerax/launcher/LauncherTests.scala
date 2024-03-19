/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.{
  ArchiveParser,
  KeYmaeraXArchivePrinter,
  KeYmaeraXExtendedLemmaParser,
  PrettierPrintFormatProvider,
}
import edu.cmu.cs.ls.keymaerax.tagobjects.SlowTest
import edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaeraXTool, ToolEvidence}
import org.scalatest.LoneElement._
import testHelper.KeYmaeraXTestTags.TodoTest

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import scala.collection.immutable._

@IgnoreInBuildTest
class LauncherTests extends TacticTestBase {

  "Launcher" should "prove the bouncing ball from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath

    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    exitVal shouldBe 0
    output should include("PROVED")

    val actualFileContent = {
      val source = scala.io.Source.fromFile(outputFileName)
      try source.mkString
      finally source.close()
    }
    val expectedProof = {
      val source = scala
        .io
        .Source
        .fromFile("keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyp")
      try source.mkString
      finally source.close()
    }
    // @note actual file content contains evidence comments: temporary file name in comments changes on every test run
    actualFileContent should include(expectedProof)
  }

  it should "prove the bouncing ball with conjecture option from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val conjectureFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-notac.kyx"
    val conjecture = ArchiveParser.parseFromFile(conjectureFileName).head

    val (output, _, exitVal) =
      runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    exitVal shouldBe 0
    output should include("PROVED")

    val exported = {
      val source = scala.io.Source.fromFile(outputFileName)
      val input =
        try source.mkString
        finally source.close()
      KeYmaeraXExtendedLemmaParser(input)
    }
    exported._2.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(conjecture.expandedModel.asInstanceOf[Formula]))
    val ("tool", "KeYmaera X") :: ("model", model) :: ("tactic", tactic) :: ("proof", proof) :: Nil = exported
      ._3
      .loneElement
      .asInstanceOf[ToolEvidence]
      .info
    ArchiveParser.parser(model).loneElement.expandedModel shouldBe conjecture.expandedModel
    tactic shouldBe "master"
    proof shouldBe empty // proof term not exported
  }

  it should "not prove the bouncing ball without tactic from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-niltac.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-niltac", ".kyp").getAbsolutePath
    val conjectureFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-notac.kyx"

    val (output, _, exitVal) =
      runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    exitVal shouldBe 255
    output should include("UNFINISHED")

    new File(outputFileName) should not(exist)
  }

  it should "prove multiple bouncing ball entries with matching conjectures from command line" in withZ3 { _ =>
    val sourceFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val inputFile = File.createTempFile("bouncing-ball-tout", ".kyx")
    val inputFileName = inputFile.getAbsolutePath
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val conjectureFileName = File.createTempFile("bouncing-ball-notac", ".kyx").getAbsolutePath

    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "false",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName,
    ))
    val sourceEntries = List
      .fill(3)(ArchiveParser.parseFromFile(sourceFileName).head)
      .zipWithIndex
      .map({ case (e, i) => e.copy(name = e.name + i) })
    val conjectureEntries = sourceEntries.map(_.copy(tactics = Nil))
    Files.write(
      Paths.get(inputFileName),
      sourceEntries
        .map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments = true))
        .mkString("\n")
        .getBytes(StandardCharsets.UTF_8),
    )
    Files.write(
      Paths.get(conjectureFileName),
      conjectureEntries
        .map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80)))
        .mkString("\n")
        .getBytes(StandardCharsets.UTF_8),
    )

    val (output, _, exitVal) =
      runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    exitVal shouldBe 0
    sourceEntries.foreach(e => output should include("PROVED " + e.name))

    val outputFileNames = sourceEntries.map(e =>
      outputFileName.stripSuffix(".kyp") + "-" + inputFile.getName + "-" + e.name.replaceAll("\\W", "_") + ".kyp"
    )
    val conjectures = ArchiveParser.parseFromFile(conjectureFileName)
    outputFileNames
      .zipWithIndex
      .foreach({ case (o, i) =>
        val exported = {
          val source = scala.io.Source.fromFile(o)
          val input =
            try source.mkString
            finally source.close()
          KeYmaeraXExtendedLemmaParser(input)
        }
        val conjecture = conjectures(i)
        exported._2.conclusion shouldBe
          Sequent(IndexedSeq(), IndexedSeq(conjecture.expandedModel.asInstanceOf[Formula]))
        val ("tool", "KeYmaera X") :: ("model", model) :: ("tactic", tactic) :: ("proof", proof) :: Nil =
          exported._3.loneElement.asInstanceOf[ToolEvidence].info
        val entry = ArchiveParser.parser(model).loneElement
        entry.name shouldBe conjecture.name
        entry.expandedModel shouldBe conjecture.expandedModel
        tactic shouldBe "master()"
        proof shouldBe empty // proof term not exported
      })
  }

  it should "complain about non-matching conjectures from command line" in withZ3 { _ =>
    val sourceFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val inputFile = File.createTempFile("bouncing-ball-tout", ".kyx")
    val inputFileName = inputFile.getAbsolutePath
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val conjectureFileName = File.createTempFile("bouncing-ball-notac", ".kyx").getAbsolutePath

    val sourceEntries = List
      .fill(3)(ArchiveParser.parseFromFile(sourceFileName).head)
      .zipWithIndex
      .map({ case (e, i) => e.copy(name = e.name + i) })
    val conjectureEntries = sourceEntries.map(_.copy(tactics = Nil)).take(2)
    Files.write(
      Paths.get(inputFileName),
      sourceEntries
        .map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments = true))
        .mkString("\n")
        .getBytes(StandardCharsets.UTF_8),
    )
    Files.write(
      Paths.get(conjectureFileName),
      conjectureEntries
        .map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80)))
        .mkString("\n")
        .getBytes(StandardCharsets.UTF_8),
    )

    val (_, errors, exitVal) =
      runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    exitVal shouldBe 1
    errors should include("Conjectures and archives must agree on names, but got diff Bouncing Ball2")

    val outputFileContents = {
      val source = scala.io.Source.fromFile(outputFileName)
      try source.mkString
      finally source.close()
    }
    outputFileContents shouldBe empty

    val outputFileNames = sourceEntries.map(e =>
      outputFileName.stripSuffix(".kyp") + "-" + inputFile.getName + "-" + e.name.replaceAll("\\W", "_") + ".kyp"
    )
    outputFileNames.foreach(new File(_) should not(exist))
  }

  it should "complain about non-matching conjecture names from command line" in withZ3 { _ =>
    val sourceFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val inputFile = File.createTempFile("bouncing-ball-tout", ".kyx")
    val inputFileName = inputFile.getAbsolutePath
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val conjectureFileName = File.createTempFile("bouncing-ball-notac", ".kyx").getAbsolutePath

    val sourceEntries = List
      .fill(3)(ArchiveParser.parseFromFile(sourceFileName).head)
      .zipWithIndex
      .map({ case (e, i) => e.copy(name = e.name + i) })
    val conjectureEntries = sourceEntries.map(e => e.copy(name = e.name + "Mismatch", tactics = Nil))
    Files.write(
      Paths.get(inputFileName),
      sourceEntries
        .map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments = true))
        .mkString("\n")
        .getBytes(StandardCharsets.UTF_8),
    )
    Files.write(
      Paths.get(conjectureFileName),
      conjectureEntries
        .map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80)))
        .mkString("\n")
        .getBytes(StandardCharsets.UTF_8),
    )

    val (_, errors, exitVal) =
      runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    exitVal shouldBe 1
    errors should
      include("Conjectures and archives must agree on names, but got diff Bouncing Ball0,Bouncing Ball1,Bouncing Ball2")

    val outputFileContents = {
      val source = scala.io.Source.fromFile(outputFileName)
      try source.mkString
      finally source.close()
    }
    outputFileContents shouldBe empty

    val outputFileNames = sourceEntries.map(e =>
      outputFileName.stripSuffix(".kyp") + "-" + inputFile.getName + "-" + e.name.replaceAll("\\W", "_") + ".kyp"
    )
    outputFileNames.foreach(new File(_) should not(exist))
  }

  it should "prove with wildcards from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/*.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX("-tool", "Mathematica", "-prove", inputFileName, "-out", outputFileName)
    exitVal shouldBe 255 // @note -1 since unfinished entries
    // JDK 11 requires explicit StringOps due to Scala bug:  https://github.com/scala/bug/issues/11125
    val proofStatOutputs = (output: StringOps).linesIterator.toList.takeRight(4)
    proofStatOutputs(0) should startWith("PROVED")
    proofStatOutputs(1) should startWith("UNFINISHED")
    proofStatOutputs(2) should startWith("UNFINISHED (CEX)")
    proofStatOutputs(3) should startWith("PROVED")

    val (outputZ3, _, exitValZ3) = runKeYmaeraX("-tool", "Z3", "-prove", inputFileName, "-out", outputFileName)
    exitValZ3 shouldBe 254 // Z3 throws an exception on bouncing-ball-cex.kyx (failed)
    val proofStatOutputsZ3 = (outputZ3: StringOps).linesIterator.toList.takeRight(4)
    proofStatOutputsZ3(0) should startWith("PROVED")
    proofStatOutputsZ3(1) should startWith("UNFINISHED")
    proofStatOutputsZ3(2) should startWith("FAILED")
    proofStatOutputsZ3(3) should startWith("PROVED")
  }

  it should "FEATURE_REQUEST: prove entries without tactics with auto" taggedAs (TodoTest, SlowTest) ignore {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-notac.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    exitVal shouldBe 0
    output should include("PROVED")

    val outputFileContents = {
      val source = scala.io.Source.fromFile(outputFileName)
      try source.mkString
      finally source.close()
    }
    outputFileContents should include("tactic \"\"\"\"auto\"\"\"\"")
  }

  it should "report entries with tactic nil as unfinished" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-niltac.kyx"
    val outputFile = File.createTempFile("bouncing-ball-tout", ".kyp")
    val outputFileName = outputFile.getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    exitVal shouldBe 255 // @note -1
    output should include("UNFINISHED")
    outputFile should not(exist)
  }

  it should "report disproved entries" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-cex.kyx"
    val outputFile = File.createTempFile("bouncing-ball-cex", ".kyp")
    val outputFileName = outputFile.getAbsolutePath

    val (output, _, exitVal) = runKeYmaeraX("-tool", "Mathematica", "-prove", inputFileName, "-out", outputFileName)
    exitVal shouldBe 255 // @note -1 since unfinished entry
    output should include("UNFINISHED (CEX)")
    outputFile should not(exist)

    val (outputZ3, _, exitValZ3) = runKeYmaeraX("-tool", "Z3", "-prove", inputFileName, "-out", outputFileName)
    exitValZ3 shouldBe 254 // @note Z3 fails to prove
    outputZ3 should include("FAILED")
    outputFile should not(exist)
  }

  it should "have usage information, formatted to 80 characters width" in {
    val usage = KeYmaeraX.usage
    (usage: StringOps).linesIterator.foreach(l => withClue(l) { l.length should be <= 80 })
  }

  it should "report a parsable model with exit value 0" in {
    val (output, _, exitVal) =
      runKeYmaeraX("-parse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx")
    exitVal shouldBe 0
    output should include("Parsed file successfully")
  }

  it should "report a parser error with exit value -1" in {
    val (output, _, exitVal) = runKeYmaeraX(
      "-parse",
      "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-parseerror.key",
    )
    exitVal shouldBe 255 // @note: -1
    output should include("Failed to parse file")
  }

  it should "report a parsable tactic with exit value 0" in {
    val (output, _, exitVal) =
      runKeYmaeraX("-bparse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyt")
    exitVal shouldBe 0
    output should include("Parsed file successfully")
  }

  it should "report a tactic parse error with exit value -1" in {
    val (output, _, exitVal) = runKeYmaeraX(
      "-bparse",
      "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-parseerror.kyt",
    )
    exitVal shouldBe 255 // @note: -1
    output should include("Failed to parse file")
  }

  it should "report successful proof with exit value 0" in {
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX(
      "-prove",
      "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx",
      "-tactic",
      "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyt",
      "-out",
      outputFileName,
    )
    exitVal shouldBe 0
    output should include("duration=")

    val actualFileContent = {
      val source = scala.io.Source.fromFile(outputFileName)
      try source.mkString
      finally source.close()
    }
    val expectedProof = {
      val source = scala
        .io
        .Source
        .fromFile("keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyp")
      try source.mkString
      finally source.close()
    }
    // @note actual file content contains evidence comments: temporary file name in comments changes on every test run
    actualFileContent should include(expectedProof)
  }

  it should "report non-closed proof with exit value -1" in {
    val outputFile = File.createTempFile("bouncing-ball-tout", ".kyp")
    val outputFileName = outputFile.getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX(
      "-prove",
      "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx",
      "-tactic",
      "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-incomplete.kyt",
      "-out",
      outputFileName,
    )
    exitVal shouldBe 255 // @note: -1
    output should include("UNFINISHED")
    outputFile should not(exist)
  }

  private def runKeYmaeraX(args: String*): (String, String, Int) = {
    val sep = System.getProperty("file.separator")
    val classpath = System.getProperty("java.class.path")
    val path = System.getProperty("java.home") + sep + "bin" + sep + "java"
    val pbArgs: List[String] =
      (path :: "-cp" :: classpath :: "edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX" :: Nil) ++ args
    val processBuilder = new ProcessBuilder(pbArgs: _*)
    val process = processBuilder.start()
    val exitVal = process.waitFor()
    val output = scala.io.Source.fromInputStream(process.getInputStream).getLines().mkString("\n")
    val errors = scala.io.Source.fromInputStream(process.getErrorStream).getLines().mkString("\n")
    print(output)
    Console.err.print(errors)
    (output, errors, exitVal)
  }
}
