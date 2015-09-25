/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import java.io.File

/**
 * Created by nfulton on 4/13/15.
 */
    object SqliteTableGenerator {
  //@todo was: System.getProperty("user.home") + "/keymaerax.sqlite3" which is inconsistent with DbAbstractionObj.dblocation
      val loc = System.getProperty("user.home") + File.separator +
        ".keymaerax" + File.separator + "keymaerax.sqlite"
      def main(args : Array[String]) : Unit =
        scala.slick.codegen.SourceCodeGenerator.main(
          Array("scala.slick.driver.SQLiteDriver", "org.sqlite.JDBC", "jdbc:sqlite:" + loc, "src/main/scala/edu/cmu/cs/ls/keymaerax/hydra", "")
        )
    }
