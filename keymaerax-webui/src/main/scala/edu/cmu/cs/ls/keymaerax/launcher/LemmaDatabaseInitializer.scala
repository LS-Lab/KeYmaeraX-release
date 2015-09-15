package edu.cmu.cs.ls.keymaerax.launcher

import java.io.{OutputStreamWriter, FileOutputStream, File}
import java.nio.channels.Channels
import java.nio.file.{Paths, Files}
import java.util.zip.{ZipOutputStream, ZipEntry, ZipFile, ZipInputStream}



/**
 * @todo enforce requirement that this code is only ever used from a .JAR.
 * Created by nfulton on 9/15/15.
 */
object LemmaDatabaseInitializer {
  val ZIP_FILE_LOCATION: String = 
    System.getProperty("user.home") + File.separator + ".keymaerax/cache/lemmadb/lemmadb.zip"

  /** initializes the lemmas database from a ZIP file contained in a JAR */
  def initializeFromJAR = {
    // Create the user's cache if it does not already exist.
    val lemmaDbPath = System.getProperty("user.home") + File.separator + ".keymaerax/cache/lemmadb"
    if(!new File(lemmaDbPath).exists) new File(lemmaDbPath).mkdirs

    val lemmasZipFile = copyZipFromJar(lemmaDbPath)
    copyfilesFromZip(lemmasZipFile, lemmaDbPath)
    Files.delete(Paths.get(ZIP_FILE_LOCATION))
  }

  /** Copies a ZIP file out of a JAR and to the user's cache/lemmadb directory  */
  private def copyZipFromJar(lemmaPath : String): ZipFile = {
    // Copy the .zip file into the user's lemmadb.
    val lemmas = Channels.newChannel(this.getClass.getResourceAsStream("/resources/lemmadb.zip"))
    new FileOutputStream(lemmaPath).getChannel.transferFrom(lemmas, 0, Long.MaxValue)
    new ZipFile(ZIP_FILE_LOCATION)
  }

  /**
   * Copies all files in `zip` into the directory located at `destinationPathPrefix`
   */
  private def copyfilesFromZip(zip : ZipFile, destinationPathPrefix : String) = {
    val entries = zip.entries()
    while(entries.hasMoreElements) {
      val nextFile = entries.nextElement()
      val is = zip.getInputStream(nextFile)
      val outputLocation = Paths.get(zip + File.separator + nextFile.getName)
      println("Copying " + nextFile.getName + " to " + outputLocation)
      Files.copy(is, outputLocation)
    }
  }
}
