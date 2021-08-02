/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax

import java.io.PrintWriter
import scala.collection.immutable.Map

/** The KeYmaera X configuration.
  * The purpose of this object is to have a central place for system configuration options of KeYmaera X.
  * @see [[edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX]] */
trait Configuration {

  /** Configuration keys */
  object Keys {
    val DB_PATH = "DB_PATH"
    val DEBUG = "DEBUG"
    val GUEST_USER = "GUEST_USER"
    val HOST = "HOST"
    val IS_HOSTED = "IS_HOSTED"
    val DEFAULT_USER = "DEFAULT_USER"
    val USE_DEFAULT_USER = "USE_DEFAULT_USER"
    val JKS = "JKS"
    val MATHEMATICA_LINK_NAME = "MATHEMATICA_LINK_NAME"
    val MATHEMATICA_JLINK_LIB_DIR = "MATHEMATICA_JLINK_LIB_DIR"
    val MATH_LINK_TCPIP = "MATH_LINK_TCPIP"
    val MATHEMATICA_PARALLEL_QE = "MATHEMATICA_PARALLEL_QE"
    val WOLFRAMENGINE_LINK_NAME = "WOLFRAMENGINE_LINK_NAME"
    val WOLFRAMENGINE_JLINK_LIB_DIR = "WOLFRAMENGINE_JLINK_LIB_DIR"
    val WOLFRAMENGINE_TCPIP = "WOLFRAMENGINE_TCPIP"
    val LAX = "LAX"
    val PARSER = "PARSER"
    val LEMMA_COMPATIBILITY = "LEMMA_COMPATIBILITY"
    val LEMMA_CACHE_PATH = "LEMMA_CACHE_PATH"
    val LOG_ALL_FO = "LOG_ALL_FO"
    val LOG_QE = "LOG_QE"
    val LOG_QE_DURATION = "LOG_QE_DURATION"
    val LOG_QE_STDOUT = "LOG_QE_STDOUT"
    val PORT = "PORT"
    val PROOF_TERM = "PROOF_TERM"
    val QE_LOG_PATH = "QE_LOG_PATH"
    val SOSSOLVE_LOG_PATH = "SOSSOLVE_LOG_PATH"
    val SOSSOLVE_LOG_INPUT = "SOSSOLVE_LOG_INPUT"
    val SOSSOLVE_LOG_TIMEOUT = "SOSSOLVE_LOG_TIMEOUT"
    val SOSSOLVE_VARIABLE_ORDERING = "SOSSOLVE_VARIABLE_ORDERING"
    val QE_TOOL = "QE_TOOL"
    val CEX_SEARCH_DURATION = "CEX_SEARCH_DURATION"
    val MATHEMATICA_QE_METHOD = "QE_METHOD"
    val MATHEMATICA_QE_OPTIONS = "QE_OPTIONS"
    val SMT_CACHE_PATH = "SMT_CACHE_PATH"
    val TEST_DB_PATH = "TEST_DB_PATH"
    val Z3_PATH = "Z3_PATH"
    val QE_TIMEOUT_INITIAL = "QE_TIMEOUT_INITIAL"
    val QE_TIMEOUT_CEX = "QE_TIMEOUT_CEX"
    val QE_TIMEOUT_MAX = "QE_TIMEOUT_MAX"
    val QE_ALLOW_INTERPRETED_FNS = "QE_ALLOW_INTERPRETED_FNS"
    val JLINK_USE_EXPR_INTERFACE = "JLINK_USE_EXPR_INTERFACE"
    val ODE_TIMEOUT_FINALQE = "ODE_TIMEOUT_FINALQE"
    val ODE_USE_NILPOTENT_SOLVE = "ODE_USE_NILPOTENT_SOLVE"
    val TACTIC_AUTO_EXPAND_DEFS_COMPATIBILITY = "TACTIC_AUTO_EXPAND_DEFS_COMPATIBILITY"

    object SOSsolve {
      val PATH = "SOSSOLVE_PATH"
      val MAIN_FILE = "SOSSOLVE_MAIN_FILE"
    }

    object Pegasus {
      val PATH = "PEGASUS_PATH"
      val MAIN_FILE = "PEGASUS_MAIN_FILE"
      val INVGEN_TIMEOUT = "PEGASUS_INVGEN_TIMEOUT"
      val INVCHECK_TIMEOUT = "PEGASUS_INVCHECK_TIMEOUT"
      val SANITY_TIMEOUT = "PEGASUS_SANITY_TIMEOUT"

      object DiffSaturation {
        val MINIMIZE_CUTS = "PEGASUS_DIFFSAT_MINIMIZE_CUTS"
        val STRICT_METHOD_TIMEOUTS = "PEGASUS_DIFFSAT_STRICT_METHOD_TIMEOUTS"
        val USE_DEPENDENCIES = "USE_DEPENDENCIES"
      }

      object PreservedStateHeuristic {
        val TIMEOUT = "PEGASUS_PRESERVEDSTATE_TIMEOUT"
      }

      object HeuristicInvariants {
        val TIMEOUT = "PEGASUS_HEURISTICS_TIMEOUT"
      }

      object FirstIntegrals {
        val TIMEOUT = "PEGASUS_FIRSTINTEGRALS_TIMEOUT"
        val DEGREE = "PEGASUS_FIRSTINTEGRALS_DEGREE"
      }

      object LinearFirstIntegrals {
        val TIMEOUT = "PEGASUS_LINEAR_FIRSTINTEGRALS_TIMEOUT"
      }

      object LinearGenericMethod {
        val TIMEOUT = "PEGASUS_LINEAR_GENERIC_TIMEOUT"
        val RATIONALS_ONLY = "PEGASUS_LINEAR_RATIONALS_ONLY"
        val RATIONAL_PRECISION = "PEGASUS_LINEAR_RATIONAL_PRECISION"
        val FIRST_INTEGRAL_DEGREE = "PEGASUS_LINEAR_FI_DEGREE"
      }

      object Darboux {
        val TIMEOUT = "PEGASUS_DARBOUX_TIMEOUT"
        val DEGREE = "PEGASUS_DARBOUX_DEGREE"
        val STAGGERED = "PEGASUS_DARBOUX_STAGGERED"
      }

      object Barrier {
        val TIMEOUT = "PEGASUS_BARRIER_TIMEOUT"
        val DEGREE = "PEGASUS_BARRIER_DEGREE"
      }

      object InvariantExtractor {
        val TIMEOUT = "PEGASUS_INVARIANTEXTRACTOR_TIMEOUT"
        val SUFFICIENCY_TIMEOUT = "PEGASUS_INVARIANTEXTRACTOR_SUFFICIENCY_TIMEOUT"
        val DW_TIMEOUT = "PEGASUS_INVARIANTEXTRACTOR_DW_TIMEOUT"
      }

    }

    val MATHEMATICA_MEMORY_LIMIT = "MATHEMATICA_MEMORY_LIMIT"
  }

  /** The user's home directory for the storage of KeYmaera X configuration and model and proof database files */
  def KEYMAERAX_HOME_PATH: String

  /** Prints the configuration to `writer`. */
  def printConfig(writer: PrintWriter): Unit

  /** Overwrites the configuration with `content`. */
  def overwrite(content: String): Unit

  /** Indicates whether or not the configuration contains the `key`. */
  def contains(key: String): Boolean

  /** Returns the configuration entry `key` as an absolute path with file separators. */
  def path(key: String): String

  /** Returns the configuration entry `key` as a relative path with file separators. */
  def relativePath(key: String): String

  /** Sets the `value` of `key` and stores the configuration file (unless !`saveToFile`). */
  def set(key: String, value: String, saveToFile: Boolean = true): Unit

  /** Removes a configuration element and stores the configuration file (unless !`saveToFile`). */
  def remove(key: String, saveToFile: Boolean = true): Unit

  /** Returns the value of `key`. */
  def apply(key: String): String

  /** Returns the value of `key` as Boolean or None, if not present. */
  def getBoolean(key: String): Option[Boolean]
  /** Returns the value of `key` as String or None, if not present. */
  def getString(key: String): Option[String]
  /** Returns the value of `key` as Int or None, if not present. */
  def getInt(key: String): Option[Int]
  /** Returns the value of `key` as Long or None, if not present. */
  def getLong(key: String): Option[Long]
  /** Returns the value of `key` as Float or None, if not present. */
  def getFloat(key: String): Option[Float]
  /** Returns the value of `key` as Double or None, if not present. */
  def getDouble(key: String): Option[Double]
  /** Returns the value of `key` as BigInt or None, if not present. */
  def getBigInteger(key: String): Option[BigInt]
  /** Returns the value of `key` as BigDecimal or None, if not present. */
  def getBigDecimal(key: String): Option[BigDecimal]
  /** Returns the value of key as a `List`. */
  def getList(key: String): List[String]
  /** Returns the value of `key` as a Map. */
  def getMap(key: String): Map[String, String]
}

object Configuration extends Configuration {
  private[this] var conf: Configuration = _

  override def KEYMAERAX_HOME_PATH: String = conf.KEYMAERAX_HOME_PATH

  def setConfiguration(config: Configuration): Unit = { conf = config }

  override def printConfig(writer: PrintWriter): Unit = conf.printConfig(writer)

  override def overwrite(content: String): Unit = conf.overwrite(content)

  override def contains(key: String): Boolean = conf.contains(key)

  override def remove(key: String, saveToFile: Boolean): Unit = conf.remove(key, saveToFile)

  override def path(key: String): String = conf.path(key)

  override def relativePath(key: String): String = conf.relativePath(key)

  override def set(key: String, value: String, saveToFile: Boolean): Unit = conf.set(key, value, saveToFile)

  override def apply(key: String): String = conf(key)

  override def getBoolean(key: String): Option[Boolean] = conf.getBoolean(key)

  override def getString(key: String): Option[String] = conf.getString(key)

  override def getInt(key: String): Option[Int] = conf.getInt(key)

  override def getLong(key: String): Option[Long] = conf.getLong(key)

  override def getFloat(key: String): Option[Float] = conf.getFloat(key)

  override def getDouble(key: String): Option[Double] = conf.getDouble(key)

  override def getBigInteger(key: String): Option[BigInt] = conf.getBigInteger(key)

  override def getBigDecimal(key: String): Option[BigDecimal] = conf.getBigDecimal(key)

  override def getList(key: String): List[String] = conf.getList(key)

  override def getMap(key: String): Map[String, String] = conf.getMap(key)

  /** Executes `code` with a temporary configuration that gets reset after execution. */
  def withTemporaryConfig[T](tempConfig: Map[String, String])(code: => T): T = {
    val origConfig = tempConfig.keys.map(k => k -> Configuration.getString(k))
    try {
      tempConfig.foreach({ case (k, v) => Configuration.set(k, v, saveToFile = false) })
      code
    } finally {
      origConfig.foreach({
        case (k, None) => Configuration.remove(k, saveToFile = false)
        case (k, Some(v)) => Configuration.set(k, v, saveToFile = false)
      })
    }
  }

  //<editor-fold desc="Configuration access shortcuts>

  /** Pegasus configuration access shortcuts. */
  object Pegasus {
    def relativePath: String = Configuration.relativePath(Configuration.Keys.Pegasus.PATH)
    def absolutePath: String = path(Configuration.Keys.Pegasus.PATH)
    def mainFile(default: String): String = getString(Configuration.Keys.Pegasus.MAIN_FILE).getOrElse(default)
    def invGenTimeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.INVGEN_TIMEOUT).getOrElse(default)
    def invCheckTimeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.INVCHECK_TIMEOUT).getOrElse(default)
    def sanityTimeout(default: Int = 0): Int = getInt(Configuration.Keys.Pegasus.SANITY_TIMEOUT).getOrElse(default)
    object DiffSaturation {
      def minimizeCuts(default: Boolean = true): Boolean = getBoolean(Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS).getOrElse(default)
      def strictMethodTimeouts(default: Boolean = false): Boolean = getBoolean(Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS).getOrElse(default)
      def useDependencies(default: Boolean = false): Boolean = getBoolean(Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES).getOrElse(default)
    }
    object PreservedStateHeuristic {
      def timeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT).getOrElse(default)
    }
    object HeuristicInvariants {
      def timeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT).getOrElse(default)
    }
    object FirstIntegrals {
      def timeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT).getOrElse(default)
      def degree(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.FirstIntegrals.DEGREE).getOrElse(default)
    }
    object LinearFirstIntegrals {
      def timeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT).getOrElse(default)
    }
    object LinearGenericMethod {
      def timeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT).getOrElse(default)
      def rationalsOnly(default: Boolean = false): Boolean = getBoolean(Configuration.Keys.Pegasus.LinearGenericMethod.RATIONALS_ONLY).getOrElse(default)
      def rationalPrecision(default: Int = 10): Int = getInt(Configuration.Keys.Pegasus.LinearGenericMethod.RATIONAL_PRECISION).getOrElse(default)
      def firstIntegralDegree(default: Int = 2): Int = getInt(Configuration.Keys.Pegasus.LinearGenericMethod.FIRST_INTEGRAL_DEGREE).getOrElse(default)
    }
    object Darboux {
      def timeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.Darboux.TIMEOUT).getOrElse(default)
      def degree(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.Darboux.DEGREE).getOrElse(default)
      def staggered(default: Boolean = false): Boolean = getBoolean(Configuration.Keys.Pegasus.Darboux.STAGGERED).getOrElse(default)
    }
    object Barrier {
      def timeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.Barrier.TIMEOUT).getOrElse(default)
      def degree(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.Barrier.DEGREE).getOrElse(default)
    }
    object InvariantExtractor {
      def timeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.InvariantExtractor.TIMEOUT).getOrElse(default)
      def sufficiencyTimeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT).getOrElse(default)
      def dwTimeout(default: Int = -1): Int = getInt(Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT).getOrElse(default)
    }
  }

  /** SOSsolve configuration access shortcuts. */
  object SOSsolve {
    def relativePath: String = Configuration.relativePath(Configuration.Keys.SOSsolve.PATH)
    def absolutePath: String = path(Configuration.Keys.SOSsolve.PATH)
    def mainFile(default: String): String = getString(Configuration.Keys.SOSsolve.MAIN_FILE).getOrElse(default)
  }

  //</editor-fold>
}
