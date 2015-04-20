package edu.cmu.cs.ls.keymaera.hydra

/**
 * Created by nfulton on 4/13/15.
 */
    object SqliteTableGenerator {
      val loc = System.getProperty("user.home") + "/keymaerax.sqlite3"
      def main(args : Array[String]) : Unit =
        scala.slick.codegen.SourceCodeGenerator.main(
          Array("scala.slick.driver.SQLiteDriver", "org.sqlite.JDBC", "jdbc:sqlite:" + loc, "src/main/scala/edu/cmu/cs/ls/keymaera/hydra", "")
        )
    }
