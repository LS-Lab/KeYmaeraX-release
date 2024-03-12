/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.ext

import com.wolfram.jlink.KernelLink
import edu.cmu.cs.ls.keymaerax.tools.qe.{JLinkMathematicaCommandRunner, MathematicaQETool}

/** Asynchronous bridge to [[edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaQETool]]. */
class MathematicaQEToolBridge[T](override val link: MathematicaLink)
    extends BaseKeYmaeraMathematicaBridge[T](link, null, null) {

  /** Extracts the kernel link from `link`. */
  private def kernelLink: KernelLink = link match { case j: JLinkMathematicaLink => j.ml }

  /** Returns the synchronous QE tool. */
  def qeTool: MathematicaQETool = {
    // @note need to create fresh every time since kernel link may have restarted
    val runner = new JLinkMathematicaCommandRunner(kernelLink)
    runner.timeout = timeout
    runner.memoryLimit = memoryLimit
    new MathematicaQETool(runner)
  }

  /** Runs the command `cmd` asynchronously. */
  def run(cmd: MathematicaQETool => T): T = link.run(() => cmd(qeTool), mathematicaExecutor)
}
