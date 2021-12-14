/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax

import java.io.PrintWriter
import scala.collection.mutable

/** Temporary in-memory system configuration that is not saved to a file. */
object MapConfiguration extends MapConfiguration(mutable.Map.empty)

/** Temporary in-memory system configuration that is not saved to a file. */
case class MapConfiguration(config: mutable.Map[String, String]) extends Configuration {

  /** @inheritdoc */
  override val KEYMAERAX_HOME_PATH: String = ""

  /** @inheritdoc */
  override def printConfig(writer: PrintWriter): Unit = {}

  /** @inheritdoc */
  override def overwrite(content: String): Unit = {}

  /** @inheritdoc */
  override def contains(key: String): Boolean = config.contains(key)

  /** @inheritdoc */
  override def apply(key: String): String = config(key)

  /** @inheritdoc */
  override def getBoolean(key: String): Option[Boolean] = config.get(key).map(_.toBoolean)

  /** @inheritdoc */
  override def getString(key: String): Option[String] = config.get(key)

  /** @inheritdoc */
  override def getInt(key: String): Option[Int] = config.get(key).map(_.toInt)

  /** @inheritdoc */
  override def getLong(key: String): Option[Long] = config.get(key).map(_.toLong)

  /** @inheritdoc */
  override def getFloat(key: String): Option[Float] = config.get(key).map(_.toFloat)

  /** @inheritdoc */
  override def getDouble(key: String): Option[Double] = config.get(key).map(_.toDouble)

  /** @inheritdoc */
  override def getBigInteger(key: String): Option[BigInt] = config.get(key).map(BigInt.apply)

  /** @inheritdoc */
  override def getBigDecimal(key: String): Option[BigDecimal] = config.get(key).map(BigDecimal.apply)
  /** @inheritdoc */
  override def getList(key: String): List[String] = getString(key).map(_.split(",").toList).getOrElse(Nil)
  /** @inheritdoc */
  override def getMap(key: String): Map[String, String] = {
    getList(key).map(entry => {
      val k :: v :: Nil = entry.split("->").toList
      k.trim -> v.trim.stripPrefix("->").trim
    }).toMap
  }

  /** @inheritdoc */
  override def path(key: String): String = config(key)

  /** @inheritdoc */
  override def relativePath(key: String): String = config(key)

  /** @inheritdoc */
  override def set(key: String, value: String, saveToFile: Boolean = true): Unit = { config(key) = value }

  /** @inheritdoc */
  override def remove(key: String, saveToFile: Boolean = true): Unit = { config.remove(key) }
}
