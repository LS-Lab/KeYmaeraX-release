/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.{JSResponse, LocalhostOnlyRequest, Response}

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.collection.immutable.List
import scala.io.Source

class HotkeysRequest extends LocalhostOnlyRequest {
  override def resultingResponses(): List[Response] = {
    val f = new File(Configuration.KEYMAERAX_HOME_PATH + File.separator + "hotkeys.js")
    if (!f.exists) {
      val s = Source.fromURL("https://raw.githubusercontent.com/samysweb/KeymaeraX-Hotkeys/main/keymaerax-hotkeys.js")
      try {
        f.createNewFile()
        Files.write(f.toPath, s.mkString.getBytes(StandardCharsets.UTF_8))
      } finally {
        s.close
      }
    }
    val hotkeys = Source.fromFile(f)
    try {
      List(JSResponse(hotkeys.mkString))
    } finally {
      hotkeys.close
    }
  }
}