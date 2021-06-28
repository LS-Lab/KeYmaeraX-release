/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr

/**
  * Prints a KeYmaera X archive.
  *
  * Format example:
  * {{{
  *   ArchiveEntry "Entry 1".
  *     Functions. ... End.
  *     ProgramVariables. ... End.
  *     Problem. ... End.
  *     Tactic "Proof 1". ... End.
  *     Tactic "Proof 2". ... End.
  *   End.
  *   Lemma "Entry 2". ... End.
  * }}}
  *
  * Created by smitsch on 01/04/18.
  */
class KeYmaeraXArchivePrinter(prettierPrinter: Expression => FormatProvider, withComments: Boolean = false) extends (ParsedArchiveEntry => String) {
  import KeYmaeraXArchivePrinter._

  /** Prints the `entry`. */
  def apply(entry: ParsedArchiveEntry): String = {
    val head = entry.kind match {
      case "lemma" => LEMMA_BEGIN
      case "theorem" => THEOREM_BEGIN
      case "exercise" => EXERCISE_BEGIN
      case _ => ARCHIVE_ENTRY_BEGIN
    }

    val symbols = StaticSemantics.symbols(entry.model)

    val varsBlock = printVarsBlock(symbols)

    val printedTactics = entry.tactics.map({
      case (tname, t, _) => s"""$TACTIC_BEGIN "$tname"\n$t\n$END_BLOCK"""
    }).mkString("\n\n")

    val defsBlock = printDefsBlock(entry.defs, symbols)

    val printed = print(head, entry.name, defsBlock, varsBlock, prettierPrinter(entry.model).print(entry.model.prettyString), printedTactics)

    val finalPrint = if (withComments) {
      assert(ArchiveParser(printed).map(_.model) == ArchiveParser(entry.problemContent).map(_.model),
        "Expected printed entry and stored problem content to reparse to same model")

      """(Theorem|Lemma|ArchiveEntry|Exercise)[^"]*"[^"]*"""".r.findFirstIn(entry.problemContent) match {
        case Some(header) =>
          s"""${entry.problemContent.replaceAllLiterally(header, head + " \"" + entry.name + "\"").stripSuffix(END_BLOCK).trim()}
             #
             #$printedTactics
             #
             #$END_BLOCK""".stripMargin('#')
        case None if entry.problemContent.contains(PROBLEM_BLOCK.img) =>
          s"""$head "${entry.name}"
             #${entry.problemContent}
             #
             #$printedTactics
             #
             #$END_BLOCK""".stripMargin('#')
        case None if !entry.problemContent.contains(PROBLEM_BLOCK.img) =>
          // entry was imported from formula. augment header and blocks but print plain formula content.
          s"""$head "${entry.name}"
             #$defsBlock
             #$varsBlock
             #
             #Problem
             #  ${entry.problemContent}
             #$END_BLOCK
             #
             #$printedTactics
             #
             #$END_BLOCK""".stripMargin('#')
      }
    } else printed

    "/* Exported from KeYmaera X v" + VERSION + " */\n\n" + finalPrint
  }


}

object KeYmaeraXArchivePrinter {
  private val ARCHIVE_ENTRY_BEGIN: String = "ArchiveEntry"
  private val LEMMA_BEGIN: String = "Lemma"
  private val THEOREM_BEGIN: String = "Theorem"
  private val TACTIC_BEGIN: String = "Tactic"
  private val EXERCISE_BEGIN: String = "Exercise"
  private val END_BLOCK: String = "End."

  def printName(name: String, idx: Option[Int]): String = name + (idx match {
    case Some(i) => "_" + i
    case None => ""
  })

  def printSort(sort: Sort): String = sort match {
    case Real => "Real"
    case Bool => "Bool"
    case Trafo => "HP"
    case Tuple(l, r) => "(" + printSort(l) + "," + printSort(r) + ")"
    case _ => throw new IllegalArgumentException("Sort " + sort + " not supported as sort of declaration; please use one of [Real, Bool, HP].")
  }

  /** Prints the sort of term `arg` as a function domain with named arguments (argument names from variables in term `arg`).
    * Term must be one of [Nothing, BaseVariable, (nested) Pair of BaseVariable]. */
  def printDomain(arg: Term): String = arg match {
    case v: BaseVariable => v.sort match {
      case Real =>  "Real " + v.prettyString
      case _ => throw new IllegalArgumentException("Sort " + v.sort + " not supported for variables")
    }
    case Nothing => ""
    case Pair(l, r) => printDomain(l) + "," + printDomain(r)
    case _ => throw new IllegalArgumentException("Sort " + arg.prettyString + " not supported as domain of declaration; please use of of [Nothing, BaseVariable, Pair]")
  }

  def printDef(domain: Sort, interpretation: Option[Expression]): String = interpretation match {
    case Some(i) =>
      val (op, parens) = domain match {
        case Real => ("=", "("::")"::Nil)
        case Bool => ("<->", "("::")"::Nil)
        case Trafo => ("::=", "{"::"}"::Nil)
      }
      s" $op ${parens(0)} ${i.prettyString} ${parens(1)}"
    case None => ""
  }

  /** Creates a term that fits `domain`, using `name` to name arguments with start index `i` (incremented). */
  private def createArg(domain: Sort, name: String, i: Int = 0): (Term, Int) = domain match {
    case Unit => (Nothing, i)
    case Real => (BaseVariable(name, Some(i)), i+1)
    case Tuple(l, r) =>
      val (ls, li) = createArg(l, name, i)
      val (rs, ri) = createArg(r, name, li)
      (Pair(ls, rs), ri)
    case _ => throw new IllegalArgumentException("Sort " + domain + " not supported as domain of declaration; please use one of [Unit, Real, Tuple]")
  }

  /** Prints the domain of `fn` with argument names created from base name `name`. */
  def printDomain(fn: Function, name: String): String = printDomain(createArg(fn.domain, name)._1)
  /** Prints the `domain` with argument names created from base name `name`. */
  def printDomain(domain: Sort, name: String): String = printDomain(createArg(domain, name)._1)

  /** Prints a `Definitions` block, excluding base variables occurring in `symbols`. */
  def printDefsBlock(decl: Declaration, symbols: Set[NamedSymbol]): String = {
    val defs = decl.decls.filter(_._2.domain.isDefined)

    val printedDecls = symbols.filter(s => !defs.keySet.contains(Name(s.name, s.index))).map({
      case Function(name, idx, domain, sort, _) =>
        if (!decl.decls.contains(Name(name, idx)) && !InterpretedSymbols.byName.contains((name, idx))) {
          s"  ${printSort(sort)} ${printName(name, idx)}(${printSort(domain)});"
        } else ""
      case _ => "" // either printedDefs or printedVars
    }).filter(_.nonEmpty).mkString("\n")

    def nameDots(e: Expression, name: String): Expression = {
      val dots = StaticSemantics.symbols(e).filter(_.isInstanceOf[DotTerm])
      assert(dots.map(_.index).map(_.getOrElse(0)).size == dots.size, "Interpretation uses both . and ._0")
      dots.foldLeft(e)({ case (e, d) => e.replaceAll(d, Variable(name, Some(d.index.getOrElse(0)))) })
    }

    val printedDefs = defs.map({
      case (Name(name, idx), Signature(domain, codomain, _, interpretation, _)) =>
        val printedDomain = codomain match {
          case Trafo => "" //@todo program arguments not yet supported
          case _ => "(" + printDomain(domain.getOrElse(Unit), "x") + ")"
        }
        s"  ${printSort(codomain)} ${printName(name, idx)}$printedDomain${printDef(codomain, interpretation.map(nameDots(_, "x")))};"
      case _ => ""
    }).filter(_.nonEmpty)

    if (printedDecls.nonEmpty || printedDefs.nonEmpty) "Definitions\n" +
      printedDecls + (if (printedDecls.nonEmpty && printedDefs.nonEmpty) "\n" else "") +
      printedDefs.mkString("\n") + "\n" + END_BLOCK + "\n"
    else ""
  }

  def printVarsBlock(symbols: Set[NamedSymbol]): String = {
    val printedVars = symbols.map({
      case v: BaseVariable => "  " + printSort(v.sort) + " " + printName(v.name, v.index) + ";"
      case _ => "" // see [[printDefsBlock]]
    }).filter(_.nonEmpty)
    if (printedVars.nonEmpty) "ProgramVariables\n" + printedVars.mkString("\n") + "\n" + END_BLOCK
    else ""
  }

  def print(head: String, name: String, defsBlock: String, varsBlock: String, model: String, tacticsBlock: String): String = {
    s"""$head "$name"
       #$defsBlock
       #$varsBlock
       #
       #Problem
       #  $model
       #$END_BLOCK
       #
       #$tacticsBlock
       #$END_BLOCK""".stripMargin('#')
  }
}

class KeYmaeraXLegacyArchivePrinter(withComments: Boolean = false) extends (ParsedArchiveEntry => String) {
  private val ARCHIVE_ENTRY_BEGIN: String = "ArchiveEntry"
  private val LEMMA_BEGIN: String = "Lemma"
  private val THEOREM_BEGIN: String = "Theorem"
  private val TACTIC_BEGIN: String = "Tactic"
  private val EXERCISE_BEGIN: String = "Exercise"
  private val END_BLOCK: String = "End."

  private val printer = new KeYmaeraXPrecedencePrinter {
    override protected def pp(q: PosInExpr, term: Term): String = term match {
      case DotTerm(sort, idx) => "." +
        (idx match { case None => "" case Some(i) => "_" + i }) +
        (sort match { case Tuple(_, _) => sort.toString case _ => "" })
      case _ => super.pp(q, term)
    }
  }

  /** Prints the `entry`. */
  def apply(entry: ParsedArchiveEntry): String = {
    val head = entry.kind match {
      case "lemma" => LEMMA_BEGIN
      case "theorem" => THEOREM_BEGIN
      case "exercise" => EXERCISE_BEGIN
      case _ => ARCHIVE_ENTRY_BEGIN
    }

    def printName(name: String, idx: Option[Int]): String = name + (idx match {
      case Some(i) => "_" + i
      case None => ""
    })

    def printSort(domain: Sort): String = domain match {
      case Real => "R"
      case Bool => "B"
      case Trafo => "HP"
      case Unit => ""
      case Tuple(l, r) => printSort(l) + "," + printSort(r)
    }

    def printDef(domain: Sort, interpretation: Option[Expression]): String = interpretation match {
      case Some(i) =>
        val (op, parens) = domain match {
          case Real => ("=", "("::")"::Nil)
          case Bool => ("<->", "("::")"::Nil)
          case Trafo => ("::=", "{"::"}"::Nil)
        }
        s" $op ${parens(0)} ${i.prettyString} ${parens(1)}"
      case None => ""
    }

    val pp = PrettyPrinter.printer
    PrettyPrinter.setPrinter(printer)

    try {
      val symbols = StaticSemantics.symbols(entry.model)

      val defs = entry.defs.decls.filter(_._2.domain.isDefined)

      val printedDecls = symbols.filter(s => !defs.keySet.contains(Name(s.name, s.index))).map({
        case Function(name, idx, domain, sort, _) if !entry.defs.decls.contains(Name(name, idx)) =>
          s"  ${printSort(sort)} ${printName(name, idx)}(${printSort(domain)})."
        case _ => "" // either printedDefs or printedVars
      }).filter(_.nonEmpty).mkString("\n")

      val printedDefs = defs.map({
        case (Name(name, idx), Signature(_, codomain, _, interpretation, _)) if codomain == Trafo =>
          s"  ${printSort(codomain)} ${printName(name, idx)} ${printDef(codomain, interpretation)}."
        case (Name(name, idx), Signature(domain, codomain, _, interpretation, _)) if codomain != Trafo =>
          s"  ${printSort(codomain)} ${printName(name, idx)}(${printSort(domain.getOrElse(Unit))})${printDef(codomain, interpretation)}."
        case _ => ""
      }).filter(_.nonEmpty)

      val printedVars = symbols.map({
        case v: BaseVariable => "  " + printSort(v.sort) + " " + printName(v.name, v.index) + "."
        case _ => "" // see printDecls and printDefs above
      }).filter(_.nonEmpty).mkString("\n")

      val printedTactics = entry.tactics.map({
        case (tname, t, _) =>
          s"""$TACTIC_BEGIN "$tname".\n$t\n$END_BLOCK"""
      }).mkString("\n\n")

      val defsBlock =
        if (printedDecls.nonEmpty || printedDefs.nonEmpty) "Definitions.\n" +
          printedDecls + (if (printedDecls.nonEmpty && printedDefs.nonEmpty) "\n" else "") +
          printedDefs.mkString("\n") + "\n" + END_BLOCK + "\n"
        else ""

      val printed = s"""$head "${entry.name}".
                       #$defsBlock
                       #ProgramVariables.
                       #$printedVars
                       #$END_BLOCK
                       #
                       #Problem.
                       #  ${entry.model.prettyString}
                       #$END_BLOCK
                       #
                       #$printedTactics
                       #$END_BLOCK""".stripMargin('#')

      if (withComments) {
        assert(ArchiveParser.parser(printed).map(_.model) == ArchiveParser.parser(entry.problemContent).map(_.model),
          "Expected printed entry and stored problem content to reparse to same model")

        """(Theorem|Lemma|ArchiveEntry|Exercise)[^"]*"[^"]*"""".r.findFirstIn(entry.problemContent) match {
          case Some(_) =>
            s"""${entry.problemContent.stripSuffix(END_BLOCK).trim()}
               #$printedTactics
               #$END_BLOCK""".stripMargin('#')
          case None if entry.problemContent.contains(PROBLEM_BLOCK.img) =>
            s"""$head "${entry.name}"
               #${entry.problemContent}
               #$printedTactics
               #$END_BLOCK""".stripMargin('#')
          case None if !entry.problemContent.contains(PROBLEM_BLOCK.img) =>
            // entry was imported from formula. augment header and blocks but print plain formula content.
            s"""$head "${entry.name}"
               #$defsBlock
               #ProgramVariables.
               #$printedVars
               #$END_BLOCK
               #
               #Problem.
               #  ${entry.problemContent}
               #$END_BLOCK
               #
               #$printedTactics
               #$END_BLOCK""".stripMargin('#')
        }
      } else printed
    } finally {
      PrettyPrinter.setPrinter(pp)
    }
  }
}
