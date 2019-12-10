package edu.cmu.cs.ls.keymaerax.launcher

import java.io.File

import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import resource._
import testHelper.KeYmaeraXTestTags.{SlowTest, TodoTest}

class LauncherTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  "Launcher" should "prove the bouncing ball from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath

    val (output, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    output should include ("PROVED")
    exitVal shouldBe 0

    val actualFileContent = managed(scala.io.Source.fromFile(outputFileName)).apply(_.mkString)
    val expectedProof = managed(scala.io.Source.fromFile("keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyp")).apply(_.mkString)
    //@note actual file content contains evidence comments: temporary file name in comments changes on every test run
    actualFileContent should include (expectedProof)
  }

  it should "prove with wildcards from command line" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/*.kyx"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
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
    val (output, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    output should include ("PROVED")
    exitVal shouldBe 0
    managed(scala.io.Source.fromFile(outputFileName)).apply(_.mkString) should include ("tactic \"\"\"\"auto\"\"\"\"")
  }

  it should "report entries with tactic nil as unfinished" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-niltac.kyx"
    val outputFile = File.createTempFile("bouncing-ball-tout", ".kyp")
    val outputFileName = outputFile.getAbsolutePath
    val (output, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    output should include ("UNFINISHED")
    exitVal shouldBe 255 //@note -1
    outputFile should not (exist)
  }

  it should "report disproved entries" in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-cex.kyx"
    val outputFile = File.createTempFile("bouncing-ball-cex", ".kyp")
    val outputFileName = outputFile.getAbsolutePath
    val (output, exitVal) = runKeYmaeraX("-prove", inputFileName, "-out", outputFileName)
    output should include ("DISPROVED")
    exitVal shouldBe 254 //@note -2
    outputFile should not (exist)
  }

  it should "have usage information, formatted to 80 characters width" in {
    val usage = KeYmaeraX.usage
    usage.lines.foreach(l => withClue(l) { l.length should be <= 80 })
  }

  it should "report a parsable model with exit value 0" in {
    val (output, exitVal) = runKeYmaeraX("-parse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx")
    output should include ("Parsed file successfully")
    exitVal shouldBe 0
  }

  it should "report a parser error with exit value -1" in {
    val (output, exitVal) = runKeYmaeraX("-parse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-parseerror.key")
    output should include ("Failed to parse file")
    exitVal shouldBe 255 //@note: -1
  }

  it should "report a parsable tactic with exit value 0" in {
    val (output, exitVal) = runKeYmaeraX("-bparse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyt")
    output should include ("Parsed file successfully")
    exitVal shouldBe 0
  }

  it should "report a tactic parse error with exit value -1" in {
    val (output, exitVal) = runKeYmaeraX("-bparse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-parseerror.kyt")
    output should include ("Failed to parse file")
    exitVal shouldBe 255 //@note: -1
  }

  it should "report successful proof with exit value 0" in {
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, exitVal) = runKeYmaeraX(
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
    val (output, exitVal) = runKeYmaeraX(
      "-prove", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx",
      "-tactic", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-incomplete.kyt",
      "-out", outputFileName)
    output should include ("UNFINISHED")
    exitVal shouldBe 255 //@note: -1
    outputFile should not (exist)
  }

  private def runKeYmaeraX(args: String*): (String, Int) = {
    val sep        = System.getProperty("file.separator")
    val classpath  = System.getProperty("java.class.path")
    val path       = System.getProperty("java.home") + sep + "bin" + sep + "java"
    val pbArgs: List[String] = (path :: "-cp" :: classpath :: "edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX" :: Nil) ++ args
    val processBuilder = new ProcessBuilder(pbArgs:_*)
    val process = processBuilder.start()
    val exitVal = process.waitFor()
    val output = scala.io.Source.fromInputStream(process.getInputStream).getLines().mkString("\n")
    (output, exitVal)
  }
}
