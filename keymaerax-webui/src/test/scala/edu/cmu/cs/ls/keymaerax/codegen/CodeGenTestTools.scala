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
       |state ctrl(state curr, parameters params) { return curr; }
       |state fallback(state curr, parameters params) { return curr; }
       |
       |int main() {
       |  state current = { 0 }; /* compound literal initialization requires gcc -Wno-missing-field-initializers */
       |  parameters params = { 0 };
       |  while (true) monitoredCtrl(current, params, &ctrl, &fallback);
       |  return 0;
       |}
       |
       |""".stripMargin
  }

  /** Compiles `code` with gcc and returns the path to the compiled result (temporary). */
  def compileCpp(code: String): String = {
    val file = File.createTempFile("kyxcode", ".c")
    val f = new FileWriter(file)
    f.write(code)
    f.flush()
    f.close()
    val compiledFile = file.getAbsolutePath.stripSuffix(".c") + ".o"
    val cmd = s"gcc -Wall -Wextra -Werror -Wno-unused-parameter -Wno-missing-field-initializers -std=c99 -pedantic ${file.getAbsolutePath} -o $compiledFile"
    val p = Runtime.getRuntime.exec(cmd, null, file.getParentFile.getAbsoluteFile)
    withClue(scala.io.Source.fromInputStream(p.getErrorStream).mkString) { p.waitFor() shouldBe 0 }
    compiledFile
  }

}
