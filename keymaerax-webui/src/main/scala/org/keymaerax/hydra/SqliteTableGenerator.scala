/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra

import org.keymaerax.{Configuration, FileConfiguration}
import slick.codegen.SourceCodeGenerator
import slick.jdbc.SQLiteProfile
import slick.model.Model

import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration

/**
 * Generates database interaction code (Tables.scala) based on the schema in ~/.keymaerax/keymaerax.sqlite
 *
 * See also:
 *   - https://scala-slick.org/doc/3.2.3/code-generation.html#customization
 *   - https://github.com/slick/slick/blob/v3.2.3/doc/code/CodeGenerator.scala#L36-L71
 *
 * @author
 *   nfulton
 * @author
 *   Joscha Mennicken
 */
object SqliteTableGenerator {

  /**
   * Works around a bug in Slick which causes its code generator to not mark auto-incremented columns as such. Since the
   * row id (named _ID) is auto-incremented (or technically allocated uniquely in a way which usually coincides with
   * auto-incrementing) we can safely say that column should always be auto-increment.
   */
  def FixedCodeGenerator(model: Model): SourceCodeGenerator = new SourceCodeGenerator(model) {
    override def Table = new Table(_) {
      override def Column = new Column(_) {
        /* Slick's code generator tries very hard to prevent us from just saying the column is auto-increment (the
         * autoInc method is final), so instead we look through the generated code for the column options and add an
         * AutoInc option.
         *
         * This is admittedly cryptic and hacky. If you are confused, read the Tables.scala file output by the
         * generator. */
        override def code = {
          if (name == "_Id") { super.code.replaceFirst("O.PrimaryKey", "O.PrimaryKey, O.AutoInc") }
          else { super.code }
        }

        // Yet another hack:
        // The current slick codegen version interprets BOOLEAN columns as having the type Int.
        // However, the code expects the two BOOLEAN columns to have the type String.
        // This restores the previous behaviour so old databases containing string values
        // like "true" and "false" are not broken.
        override def rawType =
          if (name == "userexecuted" || name == "childrenrecorded") { "String" }
          else { super.rawType }
      }
    }
  }

  def main(args: Array[String]): Unit = {
    Configuration.setConfiguration(FileConfiguration)

    // Make sure the SQLite driver is loaded
    Class.forName("org.sqlite.JDBC")

    // Open database
    val loc = Configuration.path(Configuration.Keys.DB_PATH)
    val db = SQLiteProfile.api.Database.forURL("jdbc:sqlite:" + loc)

    try {
      // Fetch data model
      val modelFuture = db.run(SQLiteProfile.createModel())
      val model = Await.result(modelFuture, atMost = Duration.Inf)

      FixedCodeGenerator(model).writeToFile(
        "slick.jdbc.SQLiteProfile",
        "keymaerax-webui/src/main/scala/",
        "org.keymaerax.hydra",
        "Tables",
        "Tables.scala",
      )
    } finally { db.close() }
  }
}
