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
  def augmentMonitorMain(code: String, hasParams: Boolean, hasInputs: Boolean): String = {
    val (defineParams, paramsArg) = if (hasParams) ("parameters params = { 0 };", "&params") else ("", "(const parameters* const)0")
    val (defineInputs, inputsArg) = if (hasInputs) ("input in = { 0 };", "&in") else ("", "(const input* const)0")

    s"""$code
       |
       |state ctrl(state curr, const parameters* const params, const input* const in) { return curr; }
       |state fallback(state curr, const parameters* const params, const input* const in) { return curr; }
       |
       |int main() {
       |  state current = { 0 }; /* compound literal initialization requires gcc -Wno-missing-field-initializers */
       |  $defineParams
       |  $defineInputs
       |  while (true) monitoredCtrl(current, $paramsArg, $inputsArg, &ctrl, &fallback);
       |  return 0;
       |}
       |
       |""".stripMargin
  }

  /** Compiles `code` with gcc and returns the path to the compiled result (temporary). */
  def compileC(code: String): String = {
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
