/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Package- and argument-less shortcut for direct launcher.
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX]]
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.launcher.Main]]
 */
object KeYmaeraX {
  def main(args: Array[String]): Unit = {
    // bypass prelauncher with its JVM restart by passing -launch, but still show UI splash
    edu.cmu.cs.ls.keymaerax.launcher.Main.main(Array("-launch") ++ args)
  }
}
