/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.install

import java.io.{File, FileOutputStream}
import java.nio.channels.Channels

import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}

/**
  * Installs SOSsolve in the KeYmaera X directory, imitating [[PegasusInstaller]]
  */
object SOSsolveInstaller extends Logging {

  /** The path to the installed SOSsolve. */
  val sossolveRelativeResourcePath: String = {
    val absolutePath = copyToDisk()
    val relativePath = Configuration.SOSsolve.relativePath
    assert(absolutePath == Configuration.sanitizedPath(Configuration.KEYMAERAX_HOME_PATH, relativePath), "Unexpected absolute/relative path")
    File.separator + relativePath
  }

  /** Copies SOSsolve to the disk. Returns the path to the SOSsolve installation. */
  def copyToDisk(): String = {
    // copy SOSsolve Mathematica notebooks
    val sossolveDir = Configuration.SOSsolve.absolutePath
    if (!new File(sossolveDir).exists) new File(sossolveDir).mkdirs

    val sossolveResourcePath = "/SOSsolve/"
    val sossolveResourceNames =
        "sossolve.wl" ::
        "NDConvexHull.wl" ::
        Nil

    sossolveResourceNames.foreach(n => {
      val sossolveDestPath = sossolveDir + File.separator + n
      if (!new File(sossolveDestPath).getParentFile.exists) new File(sossolveDestPath).getParentFile.mkdirs
      val sossolveDest = new FileOutputStream(sossolveDestPath)
      val sossolveSrc = Channels.newChannel(getClass.getResourceAsStream(sossolveResourcePath + n))
      sossolveDest.getChannel.transferFrom(sossolveSrc, 0, Long.MaxValue)
    })
    val sossolveAbsPaths = sossolveResourceNames.map(sossolveDir + File.separator + _.replace("/", File.separator))
    assert(sossolveAbsPaths.forall(new File(_).exists()), "Missing SOSsolve files")
    sossolveDir
  }

}
