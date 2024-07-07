/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.Configuration
import org.keymaerax.hydra.SQLite.SQLiteDB
import org.keymaerax.hydra.responses.configuration.ExtractDatabaseResponse
import org.keymaerax.hydra.{
  ConfigurationPOJO,
  ErrorResponse,
  HyDRAServerConfig,
  LocalhostOnlyRequest,
  RegisteredOnlyRequest,
  Response,
}

import java.io.{File, FileInputStream, FileOutputStream}
import java.text.SimpleDateFormat
import java.util.Calendar
import scala.collection.immutable.Map

class ExtractDatabaseRequest() extends LocalhostOnlyRequest with RegisteredOnlyRequest {
  override def resultingResponse(): Response = {
    if (HyDRAServerConfig.isHosted) new ErrorResponse("Cannot extract the database on a hosted instance of KeYmaera X")
    else {
      val productionDatabase = org.keymaerax.hydra.SQLite.ProdDB
      productionDatabase.syncDatabase()

      val today = Calendar.getInstance().getTime
      val fmt = new SimpleDateFormat("MDY")

      val extractionPath = Configuration.KEYMAERAX_HOME_PATH + File.separator + s"extracted_${fmt.format(today)}.sqlite"
      val dbPath = productionDatabase.dblocation

      val src = new File(dbPath)
      val dest = new File(extractionPath)
      new FileOutputStream(dest).getChannel.transferFrom(new FileInputStream(src).getChannel, 0, Long.MaxValue)

      // @todo Maybe instead do this in the production database and then have a catch all that undoes it.
      // That way we don't have to sync twice. Actually, I'm also not sure if this sync is necessary or not...
      val extractedDatabase = new SQLiteDB(extractionPath)
      extractedDatabase.updateConfiguration(new ConfigurationPOJO("extractedflag", Map("extracted" -> "true")))
      extractedDatabase.syncDatabase()

      new ExtractDatabaseResponse(extractionPath)
    }
  }
}
