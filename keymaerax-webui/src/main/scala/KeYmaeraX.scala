/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

/**
  * Package- and argument-less shortcut.
  */
object KeYmaeraX {
  def main (args: Array[String]): Unit = {
    edu.cmu.cs.ls.keymaerax.launcher.Main.main(args ++ ("-launch" :: "-ui" :: Nil))
  }
}
