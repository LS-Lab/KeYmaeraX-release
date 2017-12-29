/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax

import java.io.{File, PrintWriter}
import java.nio.file.{Files, Paths}

import org.apache.commons.configuration2.PropertiesConfiguration

/** The KeYmaera X configuration. */
object Configuration {
  /** Configuration keys */
  object Keys {
    val DB_PATH = "DB_PATH"
    val DEBUG = "DEBUG"
    val GUEST_USER = "GUEST_USER"
    val HOST = "HOST"
    val IS_HOSTED = "IS_HOSTED"
    val JKS = "JKS"
    val MATHEMATICA_LINK_NAME = "MATHEMATICA_LINK_NAME"
    val MATHEMATICA_JLINK_LIB_DIR = "MATHEMATICA_JLINK_LIB_DIR"
    val MATH_LINK_TCPIP = "MATH_LINK_TCPIP"
    val LAX = "LAX"
    val LEMMA_COMPATIBILITY = "LEMMA_COMPATIBILITY"
    val LEMMA_CACHE_PATH = "LEMMA_CACHE_PATH"
    val LOG_ALL_FO = "LOG_ALL_FO"
    val LOG_QE = "LOG_QE"
    val LOG_QE_DURATION = "LOG_QE_DURATION"
    val LOG_QE_STDOUT = "LOG_QE_STDOUT"
    val POLYA_PATH = "POLYA_PATH"
    val PORT = "PORT"
    val PROOF_TERM = "PROOF_TERM"
    val QE_LOG_PATH = "QE_LOG_PATH"
    val QE_TOOL = "QE_TOOL"
    val SMT_CACHE_PATH = "SMT_CACHE_PATH"
    val TEST_DB_PATH = "TEST_DB_PATH"
    val Z3_PATH = "Z3_PATH"
  }

  private val KEYMAERAX_HOME: String = System.getProperty("KEYMAERAX_HOME", ".keymaerax")
  val KEYMAERAX_HOME_PATH: String = System.getProperty("user.home") + File.separator + KEYMAERAX_HOME

  private val CONFIG_PATH: String = System.getProperty("CONFIG_PATH",
    KEYMAERAX_HOME_PATH + File.separator + "keymaerax.conf")
  private val DEFAULT_CONFIG_PATH: String = "/default.conf"

  //@note initializes the home directory
  {
    new File(KEYMAERAX_HOME_PATH).mkdirs()
  }

  /** Reads the configuration (initializes from bundled default configuration if necessary). */
  private val config = {
    val config = new PropertiesConfiguration()
    if (!Files.exists(Paths.get(CONFIG_PATH))) {
      config.read(scala.io.Source.fromInputStream(getClass.getResourceAsStream(DEFAULT_CONFIG_PATH)).reader)
      config.write(new PrintWriter(new File(CONFIG_PATH)))
    } else config.read(scala.io.Source.fromFile(CONFIG_PATH).reader)
    config
  }

  /** Indicates whether or not the configuration contains the `key`. */
  def contains(key: String): Boolean = config.containsKey(key)

  /** Returns the value of `key`. */
  def apply(key: String): String = config.getString(key)

  /** Returns the value of `key` or None, if not present. */
  def getOption(key: String): Option[String] = if (contains(key)) Some(apply(key)) else None

  /** Returns the configuration entry `key` as an absolute path with file separators. */
  def path(key: String): String = {
    val p = config.getString(key).replaceAllLiterally("/", File.separator)
    if (p.startsWith(File.separator)) p
    else System.getProperty("user.home") + File.separator + p
  }

  /** Sets the `value` of `key` and stores the configuration file (unless !`saveToFile`). */
  def set(key: String, value: String, saveToFile: Boolean = true): Unit = {
    config.setProperty(key, value)
    if (saveToFile) config.write(new PrintWriter(new File(CONFIG_PATH)))
  }
}
