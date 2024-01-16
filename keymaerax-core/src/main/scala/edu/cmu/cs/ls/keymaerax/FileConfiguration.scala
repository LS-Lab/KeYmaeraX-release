/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax

import java.io.{File, PrintWriter, StringReader}
import java.nio.file.{Files, Paths}

import org.apache.commons.configuration2.PropertiesConfiguration

import scala.collection.JavaConverters._

/** The KeYmaera X configuration.
  * The purpose of this object is to have a central place for system configuration options of KeYmaera X.
  * @see [[edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX]] */
object FileConfiguration extends Configuration {
  /** The default KeYmaera X directory name in the user's home directory, if environment variable [[KEYMAERAX_HOME_PATH]] is not set. */
  private val DEFAULT_KEYMAERAX_DIR_NAME: String = ".keymaerax"

  /** The user's home directory for the storage of KeYmaera X configuration and model and proof database files */
  override val KEYMAERAX_HOME_PATH: String = {
    System.getenv("KEYMAERAX_HOME") match {
      case null => System.getProperty("user.home") + File.separator + DEFAULT_KEYMAERAX_DIR_NAME
      case h => h
    }
  }

  private val CONFIG_PATH: String = System.getProperty("CONFIG_PATH", KEYMAERAX_HOME_PATH + File.separator + "keymaerax.conf")
  private val DEFAULT_CONFIG_PATH: String = "/default.conf"

  //@note initializes the home directory
  {
    new File(KEYMAERAX_HOME_PATH).mkdirs()
  }

  /** Reads the configuration (initializes from bundled default configuration if necessary). */
  private val config = {
    val config = new PropertiesConfiguration()
    if (!Files.exists(Paths.get(CONFIG_PATH))) {
      config.read(scala.io.Source.fromInputStream(getClass.getResourceAsStream(DEFAULT_CONFIG_PATH)).reader())
      config.write(new PrintWriter(new File(CONFIG_PATH)))
    } else config.read(scala.io.Source.fromFile(CONFIG_PATH).reader())
    updateConfig(config)
  }

  /** Prints the configuration to `writer`. */
  override def printConfig(writer: PrintWriter): Unit= config.write(writer)

  /** Overwrites the configuration with `content`. */
  override def overwrite(content: String): Unit = {
    val config = new PropertiesConfiguration()
    config.read(new StringReader(content))
    config.write(new PrintWriter(new File(CONFIG_PATH)))
  }

  /** Indicates whether or not the configuration contains the `key`. */
  override def contains(key: String): Boolean = config.containsKey(key)

  /** Returns the value of `key`. */
  override def apply(key: String): String = config.getString(key)

  /** Returns the value of `key` or None, if not present. */
  private def safeGet[T](key: String, getter: String => Any): Option[T] = if (contains(key)) Some(getter(key).asInstanceOf[T]) else None
  /** Returns the value of `key` as Boolean or None, if not present. */
  override def getBoolean(key: String): Option[Boolean] = safeGet(key, config.getBoolean)
  /** Returns the value of `key` as String or None, if not present. */
  override def getString(key: String): Option[String] = safeGet(key, config.getString)
  /** Returns the value of `key` as Int or None, if not present. */
  override def getInt(key: String): Option[Int] = safeGet(key, config.getInt)
  /** Returns the value of `key` as Long or None, if not present. */
  override def getLong(key: String): Option[Long] = safeGet(key, config.getLong)
  /** Returns the value of `key` as Float or None, if not present. */
  override def getFloat(key: String): Option[Float] = safeGet(key, config.getFloat)
  /** Returns the value of `key` as Double or None, if not present. */
  override def getDouble(key: String): Option[Double] = safeGet(key, config.getDouble)
  /** Returns the value of `key` as BigInt or None, if not present. */
  override def getBigInteger(key: String): Option[BigInt] = safeGet(key, config.getBigInteger)
  /** Returns the value of `key` as BigDecimal or None, if not present. */
  override def getBigDecimal(key: String): Option[BigDecimal] = safeGet(key, config.getBigDecimal)
  /** @inheritdoc */
  override def getList(key: String): List[String] = getString(key).map(_.split(",").toList).getOrElse(Nil)
  /** @inheritdoc */
  override def getMap(key: String): Map[String, String] = {
    getList(key).map(entry => {
      val k :: v :: Nil = entry.split("->").toList
      k.trim -> v.trim.stripPrefix("->").trim
    }).toMap
  }

  /** Returns the configuration entry `key` as an absolute path with file separators. */
  override def path(key: String): String = {
    val p = config.getString(key).replaceAllLiterally("/", File.separator)
    if (p.startsWith(File.separator)) p
    else Configuration.sanitizedPath(Configuration.KEYMAERAX_HOME_PATH, p)
  }

  override def relativePath(key: String): String = apply(key).replaceAllLiterally("/", File.separator)

  /** Sets the `value` of `key` and stores the configuration file (unless !`saveToFile`). */
  override def set(key: String, value: String, saveToFile: Boolean = true): Unit = {
    config.setProperty(key, value)
    if (saveToFile) config.write(new PrintWriter(new File(CONFIG_PATH)))
  }

  /** Removes a configuration element and stores the configuration file (unless !`saveToFile`). */
  override def remove(key: String, saveToFile: Boolean = true): Unit = {
    config.clearProperty(key)
    if (saveToFile) config.write(new PrintWriter(new File(CONFIG_PATH)))
  }

  private def updateConfig(config: PropertiesConfiguration): PropertiesConfiguration = {
    val default = new PropertiesConfiguration()
    default.read(scala.io.Source.fromInputStream(getClass.getResourceAsStream(DEFAULT_CONFIG_PATH)).reader())
    val missing = default.getKeys().asScala.toSet -- config.getKeys().asScala.toSet
    if (missing.nonEmpty) {
      missing.foreach(m => config.setProperty(m, default.getString(m)))
      if (missing.contains(Configuration.Keys.USE_DEFAULT_USER) && missing.contains(Configuration.Keys.DEFAULT_USER)) {
        // update from a version without default login functionality -> set USE_DEFAULT_USER = "ask"
        config.setProperty(Configuration.Keys.USE_DEFAULT_USER, "ask")
      }
      config.write(new PrintWriter(new File(CONFIG_PATH)))
    }
    config
  }
}
