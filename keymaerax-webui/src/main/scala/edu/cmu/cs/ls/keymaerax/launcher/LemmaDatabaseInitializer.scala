package edu.cmu.cs.ls.keymaerax.launcher

import java.io.{FileOutputStream, File}
import java.nio.channels.Channels
import java.nio.file.{Paths, Files}
import java.util.zip.{ZipFile}



/**
 * @todo enforce requirement that this code is only ever used from a .JAR.
 * Created by nfulton on 9/15/15.
 */
object LemmaDatabaseInitializer {
  val ZIP_FILE_LOCATION: String = 
    System.getProperty("user.home") +
    File.separator +
    ".keymaerax" +
    File.separator +
    "cache" +
    File.separator +
    "lemmadb" +
    File.separator +
    "lemmadb.zip"

  val LEMMA_DB_PATH =
    System.getProperty("user.home") +
    File.separator +
    ".keymaerax" +
    File.separator +
    "cache" +
    File.separator +
    "lemmadb"

  /** initializes the lemmas database from a ZIP file contained in a JAR */
  def initializeFromJAR = {
    // Create the user's cache if it does not already exist.
    if(!new File(LEMMA_DB_PATH).exists) new File(LEMMA_DB_PATH).mkdirs

    val lemmasZipFile = copyZipFromJar(LEMMA_DB_PATH)
    unzipTo(lemmasZipFile, LEMMA_DB_PATH)
    Files.delete(Paths.get(ZIP_FILE_LOCATION))
  }

  /** Copies a ZIP file out of a JAR and to the user's cache/lemmadb directory  */
  private def copyZipFromJar(lemmaPath : String): ZipFile = {
    // Copy the .zip file into the user's lemmadb.
    val resource = this.getClass.getResourceAsStream("/lemmadb.zip")
    val lemmas = Channels.newChannel(resource)
    new FileOutputStream(ZIP_FILE_LOCATION).getChannel.transferFrom(lemmas, 0, Long.MaxValue)

    if(new File(ZIP_FILE_LOCATION).exists())
      println("Successfully copied ZIP file to " + ZIP_FILE_LOCATION)
    else
      throw new Exception("Failed to copy the lemmas database ZIP file")

    new ZipFile(ZIP_FILE_LOCATION)
  }

  /**
   * Copies all files in `zip` into the directory located at `destinationPathPrefix`.
   * Skips files that already exist in the destination.
   */
  private def unzipTo(zip : ZipFile, destinationPathPrefix : String) = {
    val entries = zip.entries()
    while(entries.hasMoreElements) {
      val nextFile = entries.nextElement()
      val is = zip.getInputStream(nextFile)

      val outputFileLocation: String = LEMMA_DB_PATH   + File.separator + nextFile.getName
      val outputFile: File = new File(outputFileLocation)
      val outputPath = Paths.get(outputFileLocation)

      //only copy the file if it doesn't already exist.
      if(!outputFile.exists()) {
        println("[Lemma DB Initializer] Copying a file from the ZIP file (" + nextFile.getName + ") to " + outputFileLocation)
        Files.copy(is, outputPath)
      }
      else {
        println("[Lemma DB Initializer] Skipping " + nextFile.getName + " because it already exists in the lemma database")
      }
    }
  }
}
