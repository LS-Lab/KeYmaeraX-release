/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Option management for Kaisar.
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

/** Language of option specifications */
sealed trait OptionSpec

/** When tracing is enabled, every proof statement is printed as it is checked, with line numbers */
case class Trace(opt: Boolean) extends OptionSpec

/** When arith debug, every formula checked in a proof search is printed */
case class DebugArith(opt: Boolean) extends OptionSpec

/**
 * If tracing is also enabled, enabling time will print the cumulative runtime at each line, to allow macro-scale
 * performance measurements. The timestamp resets each time this option is enabled, even if it is already on.
 */
case class Time(opt: Boolean) extends OptionSpec

/** Set option status and implement functionality of specific options */
object ProofOptions {
  var proofText: Option[String] = None
  val allNames: Set[String] = Set("trace", "time", "debugArith")
  var branchCount: Int = 0
  var branchBound: Int = 1

  var trace: Boolean = false
  var debugArith: Boolean = false
  // If Some(ts), ts is the time, in milliseconds,
  private var time: Option[Long] = None
  def timeEnabled: Boolean = time.nonEmpty

  /** Maintain timestamp for time printing */
  def updateTime(): String = {
    val nowMillis = System.currentTimeMillis()
    val thenMillis = time.getOrElse(nowMillis)
    if (time.isEmpty) time = Some(nowMillis)
    val diff = nowMillis - thenMillis
    val secs = diff.toDouble / 1000.0
    secs.toString
  }

  /** Update the value of a setting */
  def update(id: OptionSpec): Unit = {
    id match {
      case DebugArith(opt) => debugArith = opt
      case Trace(opt) => trace = opt
      case Time(opt) => if (opt) updateTime() else (time = None)
    }
  }

  private def parseBool(str: String): Option[Boolean] =
    if (str == "true") Some(true) else if (str == "false") Some(false) else None

  /** Parse option statements written in Kaisar proofs */
  def tryParse(option: String): Option[OptionSpec] = {
    option.split("=").toList match {
      case ("time" :: optArg :: Nil) => parseBool(optArg).map(b => (Time(b)))
      case ("trace" :: optArg :: Nil) => parseBool(optArg).map(b => (Trace(b)))
      case ("debugArith" :: optArg :: Nil) => parseBool(optArg).map(b => (DebugArith(b)))
      case _ => None
    }
  }

  /**
   * Pretty-print estimated or real branch counts of atomic proof steps. This is used to help estimate if the proof goal
   * is too complex for automation
   */
  def countBranches(estimated: Boolean = false): Unit = {
    val tag = if (estimated) "Branches (estimated): " else "Branches: "
    if (trace && branchCount >= branchBound) println(s"$tag$branchCount")
    branchCount = 0
  }
}
