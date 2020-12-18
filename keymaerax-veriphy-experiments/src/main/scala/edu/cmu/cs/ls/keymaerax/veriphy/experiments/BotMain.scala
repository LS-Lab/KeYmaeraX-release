// Example how to run:
// C:\Users\bjboh\Documents\GitHub\KeYmaeraX\keymaerax-veriphy-experiments\target\scala-2.12>java -jar KeYmaeraX-VeriPhy-Experiments-assembly-4.9.2.jar  test_ffi  C:\Users\bjboh\Desktop
package edu.cmu.cs.ls.keymaerax.veriphy.experiments

import java.io.File
import com.sun.jna._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar._

import BotCommon._

object BotMain {

  // Args:  dll_name [dll_path]
  // dll_path is used for both dll loading and for printing CSV files
  def main(args: Array[String]): Unit = {
    val libName = args(0)
    // paths for loading DLL
    val fullPath =
      if (args.length > 1) {
        val dirName = args(1)
        val path = System.getProperty("jna.library.path")
        val fullPath = if(path == null) dirName else dirName + File.pathSeparator + path
        System.setProperty("jna.library.path", fullPath)
        fullPath
      } else {
        "."
      }

    val load = FFILoader(libName)
    val lib: VeriPhyFFIs = load.Instance
    println("Loaded DLL for FFI!")
    println("native size: " + Native.LONG_SIZE)
    val angel = StrategyParser(astratStr)
    println("AngelStrat1:\n" + StrategyPrinter(angel))
    for(speed <- testSpeeds) {
      for (simArg <- simArgs) {
        doOneSim(lib, angel, fullPath, simArg, speed)
      }
    }
  }
}
