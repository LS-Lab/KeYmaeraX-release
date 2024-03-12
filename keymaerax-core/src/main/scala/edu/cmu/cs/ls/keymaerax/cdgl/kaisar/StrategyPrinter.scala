/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

object StrategyPrinter {
  def apply(as: AngelStrategy): String = {
    as match {
      case STest(f) => s"STest[${as.nodeID}](${f.prettyString})"
      case SAssign(x, f) => s"SAssign[${as.nodeID}](${x.prettyString},${f.prettyString})"
      case SAssignAny(x) => s"SAssignAny[${as.nodeID}](${x.prettyString})"
      case SLoop(s) => s"SLoop[${as.nodeID}](${apply(s)})"
      case SCompose(children) => s"SCompose[${as.nodeID}](${children.map(apply).mkString(",")})"
      case SChoice(l, r) => s"SChoice[${as.nodeID}](${apply(l)},${apply(r)})"
      case SODE(ode) => s"SODE[${as.nodeID}](${ode.prettyString})"
      case AForLoop(idx, idx0, conv, body, idxup, guardEpsilon) =>
        val guardStr = guardEpsilon.map(f => "," + f.prettyString).getOrElse("")
        s"AForLoop[${as.nodeID}](${idx.prettyString},${idx0.prettyString},${conv.prettyString},${apply(body)},${idxup
            .prettyString}${guardStr})"
      case ALoop(conv, body) => s"ALoop[${as.nodeID}](${conv.prettyString},${apply(body)})"
      case ASwitch(branches) =>
        s"ASwitch[${as.nodeID}](${branches.map({ case (fml, as) => s"(${fml.prettyString}, ${apply(as)})" }).mkString(",")})"
      case AODE(ode, dur) => s"AODE[${as.nodeID}](${ode.prettyString},${dur.prettyString})"
    }
  }
}
