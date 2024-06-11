/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.{JSResponse, LocalhostOnlyRequest, Response}

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.io.Source

class HotkeysRequest extends LocalhostOnlyRequest {
  override def resultingResponse(): Response = {
    val f = new File(Configuration.KEYMAERAX_HOME_PATH + File.separator + "hotkeys.js")
    if (!f.exists) {
      val s = Source.fromURL("https://raw.githubusercontent.com/samysweb/KeymaeraX-Hotkeys/main/keymaerax-hotkeys.js")
      try {
        f.createNewFile()
        Files.write(f.toPath, s.mkString.getBytes(StandardCharsets.UTF_8))
      } finally { s.close }
    }
    val hotkeys = Source.fromFile(f)
    try { JSResponse(hotkeys.mkString) }
    finally { hotkeys.close }
  }
}
