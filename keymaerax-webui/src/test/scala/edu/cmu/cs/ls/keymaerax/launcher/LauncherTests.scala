package edu.cmu.cs.ls.keymaerax.launcher

import java.io.File

import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

@SlowTest
class LauncherTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  "Launcher" should "prove the bouncing ball from command line with scala tactic" taggedAs IgnoreInBuildTest in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.key"
    val tacticFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/BouncingBallTacticGenerator.scala"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath

    KeYmaeraX.main(Array("-prove", inputFileName, "-tactic", tacticFileName, "-out", outputFileName))

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    val expectedProof = scala.io.Source.fromFile("keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyx.proof").mkString
    //@note actual file content contains evidence comments: temporary file name in comments changes on every test run
    actualFileContent should include (expectedProof)
  }

  it should "prove the bouncing ball from command line with kyt tactic" taggedAs IgnoreInBuildTest in {
    val inputFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.key"
    val tacticFileName = "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyt"
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath

    KeYmaeraX.main(Array("-prove", inputFileName, "-tactic", tacticFileName, "-out", outputFileName))

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    val expectedProof = scala.io.Source.fromFile("keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyp").mkString
    //@note actual file content contains evidence comments: temporary file name in comments changes on every test run
    actualFileContent should include (expectedProof)
  }

  it should "have usage information, formatted to 80 characters width" in {
    val usage = KeYmaeraX.usage
    usage.lines.foreach(l => withClue(l) { l.length should be <= 80 })
  }

  "Launcher process" should "report a parsable model with exit value 0" taggedAs IgnoreInBuildTest in {
    val (output, exitVal) = runKeYmaeraX("-parse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.key")
    output should include ("Parsed file successfully")
    exitVal shouldBe 0
  }

  it should "report a parser error with exit value -1" taggedAs IgnoreInBuildTest in {
    val (output, exitVal) = runKeYmaeraX("-parse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-parseerror.key")
    output should include ("Failed to parse file")
    exitVal shouldBe 255 //@note: -1
  }

  it should "report a parsable tactic with exit value 0" taggedAs IgnoreInBuildTest in {
    val (output, exitVal) = runKeYmaeraX("-bparse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyt")
    output should include ("Parsed file successfully")
    exitVal shouldBe 0
  }

  it should "report a tactic parse error with exit value -1" taggedAs IgnoreInBuildTest in {
    val (output, exitVal) = runKeYmaeraX("-bparse", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-parseerror.kyt")
    output should include ("Failed to parse file")
    exitVal shouldBe 255 //@note: -1
  }

  it should "report successful proof with exit value 0" taggedAs IgnoreInBuildTest in {
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, exitVal) = runKeYmaeraX(
      "-prove", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.key",
      "-tactic", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyt",
      "-out", outputFileName)
    output should include ("[proof time ")
    exitVal shouldBe 0

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    val expectedProof = scala.io.Source.fromFile("keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.kyp").mkString
    //@note actual file content contains evidence comments: temporary file name in comments changes on every test run
    actualFileContent should include (expectedProof)
  }

  it should "report non-closed proof with exit value -1" taggedAs IgnoreInBuildTest in {
    val outputFileName = File.createTempFile("bouncing-ball-tout", ".kyp").getAbsolutePath
    val (output, exitVal) = runKeYmaeraX(
      "-prove", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout.key",
      "-tactic", "keymaerax-webui/src/test/resources/examples/simple/bouncing-ball/bouncing-ball-tout-incomplete.kyt",
      "-out", outputFileName)
    output should include ("""==================================
                             |Tactic did not finish the proof    open goals: 1
                             |==================================""".stripMargin)
    exitVal shouldBe 255 //@note: -1
    scala.io.Source.fromFile(outputFileName).mkString shouldBe ""
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
