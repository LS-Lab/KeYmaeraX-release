package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.core._

object PrettyPrinter {
  def short(s: Statement): String = {
    s match {
      case Assume(pat, f) =>
        val patStr = pat match {case Nothing => "" case f => s"$f:"}
        s"?$patStr($f)"
      case Assert(pat, f, m) =>
        val patStr = pat match {case Nothing => "" case f => s"$f:"}
        s"!$patStr($f) ..."
      case Modify(ids, mods) => mods.map({case (x, None) => s"$x:=*;" case (x, Some(f)) => s"$x:=$f;"}).mkString(" ")
      case Label(st, snapshot) => s"$st:"
      case Note(x, proof, annotation) => s"note $x = ..."
      case LetSym(f, args, e) => s"let $f(${args.mkString(", ")}) = ..."
      case Match(pat, e) => s"match ($pat) = $e"
      case Switch(scrutinee, pats) => s"switch ($scrutinee) { ... }"
      case BoxChoice(left, right) => s"... ++ ..."
      case While(x, j, s) => s"while($x:$j) { ... }"
      case For(metX, metF, metIncr, guard, conv, body) => s"for($metX := $metF; $guard; $metX := $metIncr) { ... }"
      case BoxLoop(s, ih) => s"{...}*"
      case Ghost(s) =>  s"/++ ++/"
      case InverseGhost(s) => s"/-- --/"
      case Phi(asgns) => s"φ(...)"
      case ProveODE(ds, dc) =>
      val bound = ds.allAtoms.map(aodes => aodes.dp.xp.prettyString).map(x => s"$x = ...")
      s"{${bound.mkString(", ")} & ... }"
      case _ => ""
    }
  }
}
