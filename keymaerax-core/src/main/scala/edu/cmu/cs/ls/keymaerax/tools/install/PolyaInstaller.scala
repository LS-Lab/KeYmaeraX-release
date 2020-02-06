/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.install

import java.io.{File, FileOutputStream, InputStream}
import java.nio.channels.Channels
import java.util.Locale

import edu.cmu.cs.ls.keymaerax.Configuration
import org.apache.logging.log4j.scala.Logging

/**
  * Installs and/or updates the Polya binary in the KeYmaera X directory.
  */
object PolyaInstaller extends Logging {

  /** Get the absolute path to Polya jar */
  val polyaPath: String = {
    val polyaTempDir = Configuration.path(Configuration.Keys.POLYA_PATH)
    if (!new File(polyaTempDir).exists) new File(polyaTempDir).mkdirs
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)

    // so far only for MacOS and Linux
    //@todo: support for other OS
    if (new File(polyaTempDir + "polya").exists()) {
      polyaTempDir + "polya"
    } else {
      val osArch = System.getProperty("os.arch")
      var resource: InputStream = null
      if (osName.contains("mac")) {
        if (osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/polya/mac64/polya")
        }
      } else if (osName.contains("linux")) {
        if (osArch.contains("64")) {
          resource = this.getClass.getResourceAsStream("/polya/ubuntu64/polya")
        }
      } else {
        throw new Exception("Polya solver is currently not supported in your operating system.")
      }
      if (resource == null)
        //@note points to a release error
        throw new Exception("Unable to find Polya in classpath jar bundle: " + System.getProperty("user.dir"))

      val polyaSource = Channels.newChannel(resource)
      val polyaTemp = new File(polyaTempDir, "polya")
      // Get a stream to the script in the resources dir
      val polyaDest = new FileOutputStream(polyaTemp)
      // Copy file to temporary directory
      polyaDest.getChannel.transferFrom(polyaSource, 0, Long.MaxValue)
      val polyaAbsPath = polyaTemp.getAbsolutePath
      //@note this is a non-windows solution but there's no windows version currently
      Runtime.getRuntime.exec("chmod u+x " + polyaAbsPath)
      polyaSource.close()
      polyaDest.close()
      assert(new File(polyaAbsPath).exists(), "Polya has been unpacked successfully")
      polyaAbsPath
    }
  }

}
