/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.codegen

import java.io.{File, FileWriter}
import org.scalatest.Matchers._

/**
  * Tools for testing code generation.
  * @author Stefan Mitsch
  */
object CodeGenTestTools {

  /** Augments ModelPlex monitor `code` with a sample main method calling the monitor (for compilation purposes). */
  def augmentMonitorMain(code: String): String = {
    s"""$code
       |
       |int main(int argc, char** argv) {
       |  state current;
       |  parameters params;
       |  while (true) monitor(current, params);
       |  return 0;
       |}
       |
       |""".stripMargin
  }

  /** Compiles `code` with g++. */
  def compileCpp(code: String): Unit = {
    val file = File.createTempFile("kyxcode", ".cpp")
    val f = new FileWriter(file)
    f.write(code)
    f.flush()
    f.close()
    val cmd = s"g++ ${file.getAbsolutePath}"
    val p = Runtime.getRuntime.exec(cmd)
    withClue(scala.io.Source.fromInputStream(p.getErrorStream).mkString) { p.waitFor() shouldBe 0 }
  }

}
