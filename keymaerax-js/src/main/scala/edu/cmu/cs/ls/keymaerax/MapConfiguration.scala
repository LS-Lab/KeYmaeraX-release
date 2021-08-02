package edu.cmu.cs.ls.keymaerax

import java.io.PrintWriter

/** The KeYmaera X configuration.
  * The purpose of this object is to have a central place for system configuration options of KeYmaera X.
  *
  * @see [[edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX]] */
object MapConfiguration extends Configuration {
  /** The user's home directory for the storage of KeYmaera X configuration and model and proof database files */
  override val KEYMAERAX_HOME_PATH: String = ""

  /** Prints the configuration to `writer`. */
  override def printConfig(writer: PrintWriter): Unit = {}

  /** Overwrites the configuration with `content`. */
  override def overwrite(content: String): Unit = {}

  /** The hard-coded configuration. */
  private val config = Map(
    "LAX" -> "true",
    "DEBUG" -> "false",
    "PARSER" -> "KeYmaeraXParser"
  )

  /** Indicates whether or not the configuration contains the `key`. */
  override def contains(key: String): Boolean = config.contains(key)

  /** Returns the value of `key`. */
  override def apply(key: String): String = config(key)

  /** Returns the value of `key` as Boolean or None, if not present. */
  override def getBoolean(key: String): Option[Boolean] = config.get(key).map(_.toBoolean)

  /** Returns the value of `key` as String or None, if not present. */
  override def getString(key: String): Option[String] = config.get(key)

  /** Returns the value of `key` as Int or None, if not present. */
  override def getInt(key: String): Option[Int] = config.get(key).map(_.toInt)

  /** Returns the value of `key` as Long or None, if not present. */
  override def getLong(key: String): Option[Long] = config.get(key).map(_.toLong)

  /** Returns the value of `key` as Float or None, if not present. */
  override def getFloat(key: String): Option[Float] = config.get(key).map(_.toFloat)

  /** Returns the value of `key` as Double or None, if not present. */
  override def getDouble(key: String): Option[Double] = config.get(key).map(_.toDouble)

  /** Returns the value of `key` as BigInt or None, if not present. */
  override def getBigInteger(key: String): Option[BigInt] = config.get(key).map(BigInt.apply)

  /** Returns the value of `key` as BigDecimal or None, if not present. */
  override def getBigDecimal(key: String): Option[BigDecimal] = config.get(key).map(BigDecimal.apply)
  /** Returns the value of key as a `List`. */
  override def getList(key: String): List[String] = getString(key).map(_.split(",").toList).getOrElse(Nil)
  /** Returns the value of `key` as a Map. */
  override def getMap(key: String): Map[String, String] = {
    getList(key).map(entry => {
      val k :: v :: Nil = entry.split("->").toList
      k.trim -> v.trim.stripPrefix("->").trim
    }).toMap
  }

  /** Returns the configuration entry `key` as an absolute path with file separators. */
  override def path(key: String): String = config(key)

  override def relativePath(key: String): String = config(key)

  /** Sets the `value` of `key` and stores the configuration file (unless !`saveToFile`). */
  override def set(key: String, value: String, saveToFile: Boolean = true): Unit = {}

  /** Removes a configuration element and stores the configuration file (unless !`saveToFile`). */
  override def remove(key: String, saveToFile: Boolean = true): Unit = {}
}
