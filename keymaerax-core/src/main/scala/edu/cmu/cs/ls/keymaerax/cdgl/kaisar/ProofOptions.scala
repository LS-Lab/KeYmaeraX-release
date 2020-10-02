package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

sealed trait OptionSpec
case class Trace(opt: Boolean) extends OptionSpec
case class Time(opt: Boolean) extends OptionSpec

object ProofOptions {
  var proofText: Option[String] = None
  val allNames: Set[String] = Set("trace", "time")
  var branchCount: Int = 0
  var branchBound: Int = 1

  var trace: Boolean = false
  // If Some(ts), ts is the time, in milliseconds,
  private var time: Option[Long] = None
  def timeEnabled: Boolean = time.nonEmpty
  def updateTime(): String = {
    val nowMillis = System.currentTimeMillis()
    val thenMillis = time.getOrElse(nowMillis)
    if(time.isEmpty) time = Some(nowMillis)
    val diff = nowMillis - thenMillis
    val secs = diff.toDouble / 1000.0
    secs.toString
  }

  def update(id: OptionSpec): Unit = {
    id match {
      case Trace(opt) => trace = opt
      case Time(opt) =>
        if (opt)
          updateTime()
        else
          (time = None)
    }
  }

  private def parseBool(str: String): Option[Boolean] = if(str == "true") Some(true) else if (str == "false") Some(false) else None

  def tryParse(option: String): Option[OptionSpec] = {
    option.split("=").toList match {
      case ("time" :: optArg :: Nil) =>
        parseBool(optArg).map(b => (Time(b)))
      case ("trace" :: optArg :: Nil) =>
        parseBool(optArg).map(b => (Trace(b)))
      case _ => None
    }
  }

  def countBranches(): Unit = {
    if (trace && branchCount >= branchBound)
      println(s"Branches: $branchCount")
    branchCount = 0
  }
}
