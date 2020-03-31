/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.install

import java.io.{File, FileOutputStream}
import java.nio.channels.Channels

import edu.cmu.cs.ls.keymaerax.Configuration
import org.apache.logging.log4j.scala.Logging

/**
  * Installs Pegasus in the KeYmaera X directory.
  */
object PegasusInstaller extends Logging {

  /** The path to the installed Pegasus. */
  val pegasusRelativeResourcePath: String = {
    val absolutePath = copyToDisk()
    val relativePath = Configuration.Pegasus.path
    assert(absolutePath == System.getProperty("user.home") + File.separator + relativePath, "Unexpected absolute/relative path")
    File.separator + relativePath
  }

  /** Copies Pegasus to the disk. Returns the path to the Pegasus installation. */
  def copyToDisk(): String = {
    // copy Pegasus Mathematica notebooks
    val pegasusDir = Configuration.path(Configuration.Keys.Pegasus.PATH)
    if (!new File(pegasusDir).exists) new File(pegasusDir).mkdirs

    val pegasusResourcePath = "/Pegasus/"
    val pegasusResourceNames =
        "Primitives/BarrierCertificates.m" ::
        "Primitives/ConicAbstractions.m" ::
        "Primitives/DarbouxPolynomials.m" ::
        "Primitives/Dependency.m" ::
        "Primitives/DiscreteAbstraction.m" ::
        "Primitives/FirstIntegrals.m" ::
        "Primitives/LinearAlgebraicInvariants.m" ::
        "Primitives/LZZ.m" ::
        "Primitives/PreservedState.m" ::
        "Primitives/Primitives.m" ::
        "Primitives/QualAbsPolynomials.m" ::
        "Primitives/TransitionRelation.m" ::
        "Strategies/DarbouxDDC.m" ::
        "Strategies/DiffSaturation.m" ::
        "Strategies/Format.m" ::
        "Strategies/Generic.m" ::
        "Strategies/GenericNonLinear.m" ::
        "Strategies/Helper.m" ::
        "Strategies/InvariantExtractor.m" ::
        "Strategies/GenericLinear.m" ::
        "Strategies/OneDimensional.m" ::
        "Classifier.m" ::
        "Pegasus.m" ::
        "Refute.m" ::
        Nil

    pegasusResourceNames.foreach(n => {
      val pegasusDestPath = pegasusDir + File.separator + n
      if (!new File(pegasusDestPath).getParentFile.exists) new File(pegasusDestPath).getParentFile.mkdirs
      val pegasusDest = new FileOutputStream(pegasusDestPath)
      val pegasusSrc = Channels.newChannel(getClass.getResourceAsStream(pegasusResourcePath + n))
      pegasusDest.getChannel.transferFrom(pegasusSrc, 0, Long.MaxValue)
    })
    val pegasusAbsPaths = pegasusResourceNames.map(n => pegasusDir + File.separator + n)
    assert(pegasusAbsPaths.forall(new File(_).exists()), "Missing Pegasus files")
    pegasusDir
  }

}
