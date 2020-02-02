package edu.cmu.cs.ls.keymaerax.launcher

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}

import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Sequent}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXArchivePrinter, KeYmaeraXExtendedLemmaParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import resource._
import testHelper.KeYmaeraXTestTags.{SlowTest, TodoTest}

import scala.collection.immutable._
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import org.scalatest.LoneElement._

class LauncherTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  "Launcher" should "prove the bouncing ball from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath

    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    output should include ("PROVED")
    exitVal shouldBe 0

    val actualFileContent = managed(scala.io.Source.fromFile(outputFileName)).apply(_.mkString)
    val expectedProof = managed(scala.io.Source.fromFile("keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyp")).apply(_.mkString)
    //@note actual file content contains evidence comments: temporary file name in comments changes on every test run
    actualFileContent should include (expectedProof)
  }

  it should "prove the bouncing ball with conjecture option from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val conjectureFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-notac.kyx"
    val conjecture = KeYmaeraXArchiveParser.parseFromFile(conjectureFileName).head

    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    output should include ("PROVED")
    exitVal shouldBe 0

    val exported = KeYmaeraXExtendedLemmaParser(managed(scala.io.Source.fromFile(outputFileName)).apply(_.mkString))
    exported._2.loneElement shouldBe Sequent(IndexedSeq(), IndexedSeq(conjecture.expandedModel.asInstanceOf[Formula]))
    val ("tool", "KeYmaera X") :: ("model", model) :: ("tactic", tactic) :: ("proof", proof) :: Nil =
      exported._3.loneElement.asInstanceOf[ToolEvidence].info
    KeYmaeraXArchiveParser(model).loneElement.expandedModel shouldBe conjecture.expandedModel
    tactic shouldBe "master"
    proof shouldBe empty // proof term not exported
  }

  it should "not prove the bouncing ball without tactic from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-niltac.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-niltac", ".kyp").getAbsolutePath
    val conjectureFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-notac.kyx"

    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    output should include ("UNFINISHED")
    exitVal shouldBe 255

    new File(outputFileName) should not (exist)
  }

  it should "prove multiple bouncing ball entries with matching conjectures from command line" in {
    val sourceFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val inputFile = File.createTempFile("bouncing-ball-tout", ".kyx")
    val inputFileName = inputFile.getAbsolutePath
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val conjectureFileName = File.createTempFile("bouncing-ball-notac", ".kyx").getAbsolutePath

    val sourceEntries = List.fill(3)(KeYmaeraXArchiveParser.parseFromFile(sourceFileName).head).zipWithIndex.map({
      case (e, i) => e.copy(name = e.name + i)
    })
    val conjectureEntries = sourceEntries.map(_.copy(tactics = Nil))
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    Files.write(Paths.get(inputFileName), sourceEntries.map(new KeYmaeraXArchivePrinter(withComments = true)).mkString("\n").getBytes(StandardCharsets.UTF_8))
    Files.write(Paths.get(conjectureFileName), conjectureEntries.map(new KeYmaeraXArchivePrinter).mkString("\n").getBytes(StandardCharsets.UTF_8))

    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    sourceEntries.foreach(e => output should include ("PROVED " + e.name))
    exitVal shouldBe 0

    val outputFileNames = sourceEntries.map(e => outputFileName.stripSuffix(".kyp") +
      "-" + inputFile.getName + "-" + e.name.replaceAll("\\W", "_") + ".kyp")
    val conjectures = KeYmaeraXArchiveParser.parseFromFile(conjectureFileName)
    outputFileNames.zipWithIndex.foreach({ case (o, i) =>
      val exported = KeYmaeraXExtendedLemmaParser(managed(scala.io.Source.fromFile(o)).apply(_.mkString))
      val conjecture = conjectures(i)
      exported._2.loneElement shouldBe Sequent(IndexedSeq(), IndexedSeq(conjecture.expandedModel.asInstanceOf[Formula]))
      val ("tool", "KeYmaera X") :: ("model", model) :: ("tactic", tactic) :: ("proof", proof) :: Nil =
        exported._3.loneElement.asInstanceOf[ToolEvidence].info
      val entry = KeYmaeraXArchiveParser(model).loneElement
      entry.name shouldBe conjecture.name
      entry.expandedModel shouldBe conjecture.expandedModel
      tactic shouldBe "master"
      proof shouldBe empty // proof term not exported
    })
  }

  it should "complain about non-matching conjectures from command line" in {
    val sourceFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val inputFile = File.createTempFile("bouncing-ball-tout", ".kyx")
    val inputFileName = inputFile.getAbsolutePath
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val conjectureFileName = File.createTempFile("bouncing-ball-notac", ".kyx").getAbsolutePath

    val sourceEntries = List.fill(3)(KeYmaeraXArchiveParser.parseFromFile(sourceFileName).head).zipWithIndex.map({
      case (e, i) => e.copy(name = e.name + i)
    })
    val conjectureEntries = sourceEntries.map(_.copy(tactics = Nil)).take(2)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    Files.write(Paths.get(inputFileName), sourceEntries.map(new KeYmaeraXArchivePrinter(withComments = true)).mkString("\n").getBytes(StandardCharsets.UTF_8))
    Files.write(Paths.get(conjectureFileName), conjectureEntries.map(new KeYmaeraXArchivePrinter).mkString("\n").getBytes(StandardCharsets.UTF_8))

    val (output, errors, exitVal) = runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    errors should include ("Conjectures and archives must agree on names, but got diff Bouncing Ball2")
    exitVal shouldBe 1

    val outputFileNames = sourceEntries.map(e => outputFileName.stripSuffix(".kyp") +
      "-" + inputFile.getName + "-" + e.name.replaceAll("\\W", "_") + ".kyp")
    managed(scala.io.Source.fromFile(outputFileName)).apply(_.mkString) shouldBe empty
    outputFileNames.foreach(new File(_) should not (exist))
  }

  it should "complain about non-matching conjecture names from command line" in {
    val sourceFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val inputFile = File.createTempFile("bouncing-ball-tout", ".kyx")
    val inputFileName = inputFile.getAbsolutePath
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val conjectureFileName = File.createTempFile("bouncing-ball-notac", ".kyx").getAbsolutePath

    val sourceEntries = List.fill(3)(KeYmaeraXArchiveParser.parseFromFile(sourceFileName).head).zipWithIndex.map({
      case (e, i) => e.copy(name = e.name + i)
    })
    val conjectureEntries = sourceEntries.map(e => e.copy(name = e.name + "Mismatch", tactics = Nil))
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    Files.write(Paths.get(inputFileName), sourceEntries.map(new KeYmaeraXArchivePrinter(withComments = true)).mkString("\n").getBytes(StandardCharsets.UTF_8))
    Files.write(Paths.get(conjectureFileName), conjectureEntries.map(new KeYmaeraXArchivePrinter).mkString("\n").getBytes(StandardCharsets.UTF_8))

    val (_, errors, exitVal) = runKeYmaeraX("-prove", inputFileName, "-conjecture", conjectureFileName, "-out", outputFileName)
    errors should include ("Conjectures and archives must agree on names, but got diff Bouncing Ball0,Bouncing Ball1,Bouncing Ball2")
    exitVal shouldBe 1

    val outputFileNames = sourceEntries.map(e => outputFileName.stripSuffix(".kyp") +
      "-" + inputFile.getName + "-" + e.name.replaceAll("\\W", "_") + ".kyp")
    managed(scala.io.Source.fromFile(outputFileName)).apply(_.mkString) shouldBe empty
    outputFileNames.foreach(new File(_) should not (exist))
  }

  it should "prove with wildcards from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/*.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    val proofStatOutputs = output.lines.toList.takeRight(4)
    proofStatOutputs(0) should startWith ("PROVED")
    proofStatOutputs(1) should startWith ("UNFINISHED")
    proofStatOutputs(2) should startWith ("DISPROVED")
    proofStatOutputs(3) should startWith ("PROVED")
    exitVal shouldBe 254 //@note -2 since one entry disproved
  }

  it should "FEATURE_REQUEST: prove entries without tactics with auto" taggedAs (TodoTest, SlowTest) ignore {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-notac.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    output should include ("PROVED")
    exitVal shouldBe 0
    managed(scala.io.Source.fromFile(outputFileName)).apply(_.mkString) should include ("tactic \"\"\"\"auto\"\"\"\"")
  }

  it should "report entries with tactic nil as unfinished" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-niltac.kyx"
    val outputFile = File.createTempFile("bouncing-ball-tout", ".kyp")
    val outputFileName = outputFile.getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    output should include ("UNFINISHED")
    exitVal shouldBe 255 //@note -1
    outputFile should not (exist)
  }

  it should "report disproved entries" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-cex.kyx"
    val outputFile = File.createTempFile("bouncing-ball-cex", ".kyp")
    val outputFileName = outputFile.getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    output should include ("DISPROVED")
    exitVal shouldBe 254 //@note -2
    outputFile should not (exist)
  }

  it should "have usage information, formatted to 80 characters width" in {
    val usage = KeYmaeraX.usage
    usage.lines.foreach(l => withClue(l) { l.length should be <= 80 })
  }

  it should "report a parsable model with exit value 0" in {
    val (output, _, exitVal) = runKeYmaeraX("-parse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx")
    output should include ("Parsed file successfully")
    exitVal shouldBe 0
  }

  it should "report a parser error with exit value -1" in {
    val (output, _, exitVal) = runKeYmaeraX("-parse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-parseerror.key")
    output should include ("Failed to parse file")
    exitVal shouldBe 255 //@note: -1
  }

  it should "report a parsable tactic with exit value 0" in {
    val (output, _, exitVal) = runKeYmaeraX("-bparse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyt")
    output should include ("Parsed file successfully")
    exitVal shouldBe 0
  }

  it should "report a tactic parse error with exit value -1" in {
    val (output, _, exitVal) = runKeYmaeraX("-bparse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-parseerror.kyt")
    output should include ("Failed to parse file")
    exitVal shouldBe 255 //@note: -1
  }

  it should "report successful proof with exit value 0" in {
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX(
      "-prove", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx",
      "-tactic", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyt",
      "-out", outputFileName)
    output should include ("duration=")
    exitVal shouldBe 0

    val actualFileContent = managed(scala.io.Source.fromFile(outputFileName)).apply(_.mkString)
    val expectedProof = managed(scala.io.Source.fromFile("keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyp")).apply(_.mkString)
    //@note actual file content contains evidence comments: temporary file name in comments changes on every test run
    actualFileContent should include (expectedProof)
  }

  it should "report non-closed proof with exit value -1" in {
    val outputFile = File.createTempFile("bouncing-ball-tout", ".kyp")
    val outputFileName = outputFile.getAbsolutePath
    val (output, _, exitVal) = runKeYmaeraX(
      "-prove", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx",
      "-tactic", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-incomplete.kyt",
      "-out", outputFileName)
    output should include ("UNFINISHED")
    exitVal shouldBe 255 //@note: -1
    outputFile should not (exist)
  }

  private def runKeYmaeraX(args: String*): (String, String, Int) = {
    val sep        = System.getProperty("file.separator")
    val classpath  = System.getProperty("java.class.path")
    val path       = System.getProperty("java.home") + sep + "bin" + sep + "java"
    val pbArgs: List[String] = (path :: "-cp" :: classpath :: "edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX" :: Nil) ++ args
    val processBuilder = new ProcessBuilder(pbArgs:_*)
    val process = processBuilder.start()
    val exitVal = process.waitFor()
    val output = scala.io.Source.fromInputStream(process.getInputStream).getLines().mkString("\n")
    val errors = scala.io.Source.fromInputStream(process.getErrorStream).getLines().mkString("\n")
    print(output)
    (output, errors, exitVal)
  }
}
