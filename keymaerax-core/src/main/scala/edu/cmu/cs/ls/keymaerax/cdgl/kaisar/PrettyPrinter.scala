/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{Ident, LabelDef}
import edu.cmu.cs.ls.keymaerax.core._

object PrettyPrinter {
  def short(s: Statement): String = {
    s match {
      case Assume(pat, f) =>
        val patStr = pat match {
          case Nothing => ""
          case f => s"$f:"
        }
        s"?$patStr($f)"
      case Assert(pat, f, m) =>
        val patStr = pat match {
          case Nothing => ""
          case f => s"$f:"
        }
        s"!$patStr($f) ..."
      case Modify(ids, mods) => mods
          .map({
            case (x, None) => s"$x:=*;"
            case (x, Some(f)) => s"$x:=$f;"
          })
          .mkString(" ")
      case Label(st, snapshot) => s"$st:"
      case Note(x, proof, annotation) => s"note $x = ..."
      case LetSym(f, args, e) => s"let $f(${args.mkString(", ")}) = ..."
      case Match(pat, e) => s"match ($pat) = $e"
      case Switch(scrutinee, pats) => s"switch ($scrutinee) { ... }"
      case BoxChoice(left, right) => s"... ++ ..."
      case While(x, j, s) => s"while($x:$j) { ... }"
      case For(metX, metF, metIncr, guard, conv, body, eps) => s"for($metX := $metF; $guard; $metX := $metIncr) { ... }"
      case BoxLoop(s, ih) => s"{...}*"
      case Ghost(s) => s"/++ ++/"
      case InverseGhost(s) => s"/-- --/"
      case Phi(asgns) => s"φ(...)"
      case ProveODE(ds, dc) =>
        val bound = ds.allAtoms.map(aodes => aodes.dp.xp.prettyString).map(x => s"$x = ...")
        s"{${bound.mkString(", ")} & ... }"
      case Comment(str) => "/* " + str + "*/"
      case _ => ""
    }
  }

  private def ofPatInner(pat: Term): String = {
    pat match {
      case Nothing => ""
      case Pair(l, r) => ofPatInner(l) + "," + ofPatInner(r)
      case bv: Variable => bv.name
    }
  }

  private def ofPat(pat: Term): String = {
    pat match {
      case Nothing => ""
      case bv: Variable => s"${bv.name}:"
      case pat => s"${ofPatInner(pat)}:"
    }
  }

  private def ofFml(f: Formula): String = { "(" + f.prettyString + ")" }

  private def ofProofTerm(term: ProofTerm): String = {
    term match {
      case ProofVar(x) => x.name
      case ProgramVar(x) => x.name
      case ProgramAssignments(x, onlySSA) => x.name + ":="
      case ProofInstance(e) => "\"" + e.prettyString + "\""
      case ProofApp(m, n) => "(" + ofProofTerm(m) + " " + ofProofTerm(n) + ")"
    }
  }

  private def ofSelector(sel: Selector): String = {
    sel match {
      case ForwardSelector(forward) => ofProofTerm(forward)
      case PatternSelector(e) => "\"" + e.prettyString + "\""
      case DefaultSelector => "..."
      case DefaultAssignmentSelector => "..:=.."
    }
  }

  private def ofMethod(method: Method, topLevel: Boolean = false): String = {
    method match {
      case RCF() => " by rcf"
      case Auto() => " by auto"
      case Prop() => " by prop"
      case Solution() => " by solution"
      case Hypothesis() => " by hypothesis"
      case DiffInduction() => " by induction"
      case Exhaustive() => " by exhaustion"
      case ByProof(proof) => "proof \n" + proof.map(full).mkString + " end\n"
      case GuardDone(delta) => s" by guard(${delta})"
      case Using(use, method) => s" using ${use.map(ofSelector).mkString(" ")} ${ofMethod(method)}"
    }
  }

  def ofLabelDef(labelDef: LabelDef): String = {
    if (labelDef.args.isEmpty) labelDef.label + ":\n" else labelDef.label + "(" + labelDef.args.mkString(",") + "):"
  }

  def ofMod(mod: (Variable, Option[Term]), full: Boolean): String = {
    (mod, full) match {
      case ((x, None), true) => s"$x:=*;\n"
      case ((x, None), false) => s"$x:=*;"
      case ((x, Some(f)), true) => s"$x:=${f.prettyString};\n"
      case ((x, Some(f)), false) => s"$x:=${f.prettyString};"
    }
  }

  private def varsPat(idents: List[Ident]): String = {
    idents match {
      case Nil => ""
      case id :: Nil => id.name
      case ids => "(" + ids.map(_.name).mkString(",") + ")"
    }
  }

  private def ofBranch(br: (Term, Formula, Statement)): String = {
    br match {
      case (Nothing, f, s) => s"case (${f.prettyString}) => ${full(s)}"
      case (pat, f, s) => s"case ${ofPat(pat)}(${f.prettyString}) => ${full(s)}"
    }
  }

  private def ofDiffStatement(dc: DiffStatement): String = {
    dc match {
      case AtomicODEStatement(dp, Nothing) => dp.prettyString
      case AtomicODEStatement(dp, v: Variable) => v.name + ": " + dp.prettyString
      case DiffProductStatement(l, r) => ofDiffStatement(l) + ", " + ofDiffStatement(r)
      case DiffGhostStatement(ds) => "/++ " + ofDiffStatement(ds) + " ++/"
      case InverseDiffGhostStatement(ds) => "/-- " + ofDiffStatement(ds) + " --/"
    }
  }

  private def ofDomainStatement(dc: DomainStatement): String = {
    dc match {
      case da: DomAssert => full(Assert(da.x, da.f, da.child))
      case da: DomAssume => full(Assume(da.x, da.f))
      case DomWeak(dc) => "/-- " + ofDomainStatement(dc) + " --/"
      case DomModify(Nothing, x, f) => x.name + " := " + f.prettyString + ";\n"
      case DomModify(v: Variable, x, f) => "?" + v.name + ":(" + x.name + " := " + f.prettyString + ");\n"
      case DomAnd(l, r) => ofDomainStatement(l) + "& " + ofDomainStatement(r)
    }
  }

  private def ofODE(ds: DiffStatement, dc: DomainStatement): String = {
    dc match {
      case DomAssume(Nothing, True) => "{" + ofDiffStatement(ds) + "};\n"
      case _ => "{" + ofDiffStatement(ds) + "& " + ofDomainStatement(dc) + "};"
    }
  }

  def full(s: Statement): String = {
    s match {
      case Assume(pat, f) => "?" + ofPat(pat) + ofFml(f) + ";\n"
      case Assert(pat, f, m) => "!" + ofPat(pat) + ofFml(f) + ofMethod(m, topLevel = true) + ";\n"
      case Label(st, snapshot) => ofLabelDef(st)
      case Modify(ids, mods) => ids match {
          case Nil => mods.map(mod => ofMod(mod, full = true)).mkString
          case ids => "?" + varsPat(ids) + ":(" + mods.map(mod => ofMod(mod, full = false)).mkString + ");"
        }
      case Note(x, proof, annotation) => "note  " + x.name + " " + ofProofTerm(proof) + ";"
      case LetSym(f, args, e) => (args, e) match {
          case (Nil, _: Term) => "let " + f + " = " + e.prettyString + ";\n"
          case (Nil, _: Formula) => "let " + f + " <-> " + e.prettyString + ";\n"
          case (Nil, _: Program) => "let " + f + " ::= " + e.prettyString + ";\n"
          case (_, _: Term) => "let " + f + "(" + args.map(_.name).mkString(", ") + ") = " + e.prettyString + ";\n"
          case (_, _: Formula) => "let " + f + "(" + args.map(_.name).mkString(", ") + ") <-> " + e.prettyString + ";\n"

        }
      case Match(pat, e) => s"match (${pat.prettyString}) = ${e.prettyString};"
      case Block(ss) => "{" + ss.map(full).mkString + "}"
      case For(metX, met0, metIncr, conv, guard, body, guardDelta) =>
        val convStr = conv.map(full).getOrElse("")
        s"for(${metX}:=${met0}; $convStr${full(guard)}$metX:=${metIncr.prettyString}){\n" + full(body) + "}"
      case While(x, j, s) => s"while(${ofPat(x)}${ofFml(j)}){\n${full(s)}}"
      case Switch(scrutinee, pats) => "switch " + scrutinee.map(s => "(" + ofSelector(s) + ")").getOrElse("") + "{\n" +
          pats.map(ofBranch).mkString + "}\n"
      case ProveODE(ds, dc) => ofODE(ds, dc)
      case BoxChoice(left, right) => "{" + full(left) + " ++ " + full(right) + "}"
      case BoxLoop(s, ih) => s"{\n${full(s)}}*\n"
      case Ghost(s) => "/++ " + full(s) + " ++/"
      case InverseGhost(s) => "/-- " + full(s) + " --/"
      case Comment(str) => "/* " + str + "*/"
      case Phi(ss) => full(ss)
      case Triv() => ""
    }
  }
}
