/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.install

import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}

import java.io.{File, FileOutputStream}
import java.nio.channels.Channels

/** Installs Pegasus in the KeYmaera X directory. */
object PegasusInstaller extends Logging {

  /** The path to the installed Pegasus. */
  val pegasusRelativeResourcePath: String = {
    val absolutePath = copyToDisk()
    val relativePath = Configuration.Pegasus.relativePath
    assert(
      absolutePath == Configuration.sanitizedPath(Configuration.KEYMAERAX_HOME_PATH, relativePath),
      "Unexpected absolute/relative path",
    )
    relativePath
  }

  /** Copies Pegasus to the disk. Returns the path to the Pegasus installation. */
  def copyToDisk(): String = {
    // copy Pegasus Mathematica notebooks
    val pegasusDir = Configuration.Pegasus.absolutePath
    if (!new File(pegasusDir).exists) new File(pegasusDir).mkdirs

    val pegasusResourcePath = "/Pegasus/"
    val pegasusResourceNames = List(
      "Primitives/BarrierCertificates.m",
      "Primitives/ConicAbstractions.m",
      "Primitives/DarbouxPolynomials.m",
      "Primitives/Dependency.m",
      "Primitives/DiscreteAbstraction.m",
      "Primitives/FirstIntegrals.m",
      "Primitives/LinearAlgebraicInvariants.m",
      "Primitives/Lyapunov.m",
      "Primitives/LZZ.m",
      "Primitives/PreservedState.m",
      "Primitives/Primitives.m",
      "Primitives/QualAbsPolynomials.m",
      "Primitives/TransitionRelation.m",
      "Strategies/DarbouxDDC.m",
      "Strategies/DiffSaturation.m",
      "Strategies/Format.m",
      "Strategies/DiffDivConquer.m",
      "Strategies/GenericNonLinear.m",
      "Strategies/Helper.m",
      "Strategies/InvariantExtractor.m",
      "Strategies/GenericLinear.m",
      "Strategies/OneDimensional.m",
      "Classifier.m",
      "NewClassifier.m",
      "Pegasus.m",
      "Refute.m",
    )

    pegasusResourceNames.foreach(n => {
      val pegasusDestPath = pegasusDir + File.separator + n
      if (!new File(pegasusDestPath).getParentFile.exists) new File(pegasusDestPath).getParentFile.mkdirs
      val pegasusDest = new FileOutputStream(pegasusDestPath)
      val pegasusSrc = Channels.newChannel(getClass.getResourceAsStream(pegasusResourcePath + n))
      pegasusDest.getChannel.transferFrom(pegasusSrc, 0, Long.MaxValue)
    })
    val pegasusAbsPaths = pegasusResourceNames.map(pegasusDir + File.separator + _.replace("/", File.separator))
    assert(pegasusAbsPaths.forall(new File(_).exists()), "Missing Pegasus files")
    pegasusDir
  }

}
