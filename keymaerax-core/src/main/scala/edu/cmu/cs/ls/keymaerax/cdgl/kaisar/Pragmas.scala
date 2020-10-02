package edu.cmu.cs.ls.keymaerax.cdgl.kaisar


sealed trait PragmaSpec {}
case class OptionPragma(optionSpec: OptionSpec) extends PragmaSpec

object Pragmas {
  val allNames = Set("option")
  private def tryParse(pragmaName: String, pragmaArg: String): Option[PragmaSpec] = {
    pragmaName match {
      case "option" => ProofOptions.tryParse(pragmaArg).map(OptionPragma)
      case _ => None
    }
  }

  def canParse(pragmaName: String, pragmaArg: String): Boolean = tryParse(pragmaName, pragmaArg).isDefined
  def parse(pragmaName: String, pragmaArg: String): PragmaSpec = tryParse(pragmaName, pragmaArg).get

  def update(pr: PragmaSpec): Unit = {
    pr match {
      case OptionPragma(optionSpec) => ProofOptions.update(optionSpec)
    }
  }

  def listen(kc: Context, s: Statement): Unit = {
    val time = if (ProofOptions.timeEnabled) Some(ProofOptions.updateTime()) else None
    (time, ProofOptions.trace) match {
      case (Some(timeStr), false) => println("Time: " + timeStr)
      case (None, false) => ()
      case (_, true) =>
        val lineCol = s.location.flatMap(loc => ProofOptions.proofText.map(str => KaisarProgramParser.prettyIndex(loc, str)))
        val lcStr = lineCol.getOrElse("")
        val timeStr = time.map(str => s" ($str s)").getOrElse("")
        println(s"$lcStr$timeStr: ${PrettyPrinter.short(s)}")
    }
  }
}
