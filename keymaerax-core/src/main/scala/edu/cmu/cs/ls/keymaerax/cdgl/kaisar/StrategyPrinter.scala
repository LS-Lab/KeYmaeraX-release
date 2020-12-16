package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

object StrategyPrinter {
  def apply(as: AngelStrategy): String = {
    as match {
      case STest(f) => s"STest(${f.prettyString})"
      case SAssign(x, f) => s"SAssign(${x.prettyString},${f.prettyString})"
      case SAssignAny(x) => s"SAssignAny(${x.prettyString})"
      case SLoop(s) => s"SLoop(${apply(s)})"
      case SCompose(children) => s"SCompose(${children.map(apply).mkString(",")})"
      case SChoice(l, r) => s"SChoice(${apply(l)},${apply(r)})"
      case SODE(ode) => s"SODE(${ode.prettyString})"
      case ALoop(conv, body) => s"ALoop(${conv.prettyString},${apply(body)})"
      case ASwitch(branches) => s"ASwitch(${branches.map({case (fml, as) => s"(${fml.prettyString}, ${apply(as)})"}).mkString(",")})"
      case AODE(ode, dur) => s"AODE(${ode.prettyString},${dur.prettyString})"
    }
  }
}
