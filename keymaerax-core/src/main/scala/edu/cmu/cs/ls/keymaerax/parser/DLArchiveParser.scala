/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import fastparse._
import JavaWhitespace._
import edu.cmu.cs.ls.keymaerax.parser.DLParser.parseException
import KeYmaeraXArchiveParser.{Declaration, ParsedArchiveEntry, parseProblem}
import edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable._

/**
  * Parse a differential dynamic logic archive file string to a list of archive entries.
  * Splits a KeYmaera X archive into its parts and forwards to respective problem/tactic parsers. An archive contains
  * at least one entry combining a model in the .kyx format and possibly a (partial) proof tactic.
  *
  * Format example:
  * {{{
  *   ArchiveEntry "Entry 1".
  *     Description "optional description text".
  *     ProgramVariables ... End.
  *     Definitions ... End.
  *     Problem ... End.
  *     Tactic "Proof 1" ... End.
  *     Tactic "Proof 2" ... End.
  *   End.
  *
  *   ArchiveEntry "Entry 2". ... End.
  * }}}
  *
  * @author Andre Platzer
  * @see [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
  */
object DLArchiveParser extends (String => List[ParsedArchiveEntry]) {
  import DLParser.{formula, term, program, ident, baseVariable}
  import DLAxiomParser.string

  /**
    * Parse an archive file string into a list of archive entries.
    * @param input The contents of the archive file.
    * @return A list of archive entries occurring in the string.
    */
  def apply(input: String) : List[ParsedArchiveEntry] = archiveParser(input)
  def parse(input: String) : List[ParsedArchiveEntry] = archiveParser(input)

  //@todo definitions elaboration to replace arguments by dots and do type analysis

  /** Tries parsing as a problem first. If it fails due to a missing Problem block, tries parsing as a plain formula. */
  def parseAsProblemOrFormula(input: String): Formula = problemOrFormulaParser(input)

  val archiveParser: String => List[ParsedArchiveEntry] = input => fastparse.parse(input, archiveEntries(_)) match {
    case Parsed.Success(value, index) => (if (value.length==1)
      List(value.head.withProblemContent(input.trim))
    else
      value).map(e => e.withFileContent(input.trim))
    case f: Parsed.Failure => throw parseException(f) //@todo? .inContext(input)
  }

  private val problemOrFormulaParser: String => Formula = input => fastparse.parse(input, problemOrFormula(_)) match {
    case Parsed.Success(value, index) => value
    case f: Parsed.Failure => throw parseException(f) //@todo? .inContext(input)
  }

  // implementation

  def sort[_: P]: P[Sort] = P( ("Real" | "Bool" | "HP").! ).map({case "Real" => Real case "Bool" => Bool case "HP" => Trafo})

  /** parse a label */
  def label[_: P]: P[String] = {
    import NoWhitespace._
    P( (CharIn("a-zA-Z") ~~ CharIn("a-zA-Z0-9_").rep).! )
  }


  /** Convenience: Parse a single problem or a single formula */
  def problemOrFormula[_: P]: P[Formula] = P( Start ~ (problem | formula) ~ End )



  /** Parse a list of archive entries */
  def archiveEntries[_: P]: P[List[ParsedArchiveEntry]] = P( Start ~ archiveEntry.rep(1) ~ End ).map(_.toList)

  /** Parse a single archive entry. */
  def archiveEntry[_: P]: P[ParsedArchiveEntry] = P( ("ArchiveEntry" | "Lemma" | "Theorem" | "Exercise").!.
    map({case "Exercise"=>"exercise" case "Lemma" => "lemma" case _=>"theorem"}) ~
    (label ~ ":").? ~ string ~
    metaInfo ~
    allDeclarations ~
    problem ~
    tactic.? ~
    metaInfo ~
    ("End.".!.map(s=>None) | "End" ~ label.map(s=>Some(s)) ~ ".")).map(
    {case (kind, label, name, meta, decl, prob, moremeta, endlabel) =>
      if (endlabel.isDefined && endlabel != label) throw ParseException("end label is optional but should be the same as the start label: " + label + " is not " + endlabel)
      ParsedArchiveEntry(
        name = name,
        kind = kind,
        fileContent = "???",
        problemContent = "???",
        defs = decl,
        model = prob,
        tactics = Nil,
        //@todo check that there are no contradictory facts in the meta and moremeta
        info = (if (label.isDefined) Map("id"->label.get) else Map.empty) ++ meta ++ moremeta
      )}
  )

  /** meta information */
  def metaInfo[_: P]: P[Map[String,String]] = P(
    description.? ~
    title.? ~
    link.?
  ).map({case (desc, title, link) =>
    (if (desc.isDefined) Map("Description"->desc.get) else Map.empty) ++
      (if (title.isDefined) Map("Title"->title.get) else Map.empty) ++
      (if (link.isDefined) Map("Link"->link.get) else Map.empty)})

  /** Functions and ProgramVariables block in any order */
  def allDeclarations[_: P]: P[Declaration] = P(
    NoCut(declarations ~ functions).map(p=>p._1++p._2) |
    NoCut(functions.? ~ declarations.?).
      map({case (Some(a), Some(b)) => a++b case (None, Some(b)) => b case (Some(a), None) => a case (None, None) => Declaration(Map.empty, Map.empty)})
  )

  /** `Description "text".` parsed. */
  def description[_: P]: P[String] = P("Description" ~/ string ~ "." )

  /** `Title "text".` parsed. */
  def title[_: P]: P[String] = P("Title" ~/ string ~ "." )

  /** `Link "text".` parsed. */
  def link[_: P]: P[String] = P("Link" ~/ string ~ "." )

  /** `Functions declOrDef End.` parsed. */
  def functions[_: P]: P[Declaration] = P("Definitions" ~/ declOrDef.rep ~ "End." ).
    map(list => Declaration(list.toMap, Map.empty))
//      list.filter({case (id,sig) => sig._3.isEmpty}).toMap,
//      list.filter({case (id,sig) => sig._3.isDefined}).toMap)

  /** Name is alphanumeric name and index. */
  type Name = (String, Option[Int])
  /** Signature is a domain sort, codomain sort, expression used as "interpretation", location that starts the declaration. */
  type Signature = (Option[Sort], Sort, Option[Expression], Location)

  /** `sort name(sort1 arg1, sorg2 arg2);` declaration or
    * `sort name(sort1 arg1, sorg2 arg2) = term;` function definition or
    * `Bool name(sort1 arg1, sorg2 arg2) <-> formula;` predicate definition or
    * `HP name ::= program;` program definition. */
  def declOrDef[_: P]: P[(Name,Signature)] = P(
    NoCut(progDef)
    | NoCut(declPart ~ ";")
    | NoCut(declPart ~ "=" ~ term ~ ";").map({case (id, sig, e) => (id, (sig._1, sig._2, Some(e), sig._4))})
    | NoCut(declPart ~ "<->" ~ formula ~ ";").map({case (id, sig, f) => (id, (sig._1, sig._2, Some(f), sig._4))})
  )

  /** `sort name(sort1 arg1, sorg2 arg2)` declaration part */
  def declPart[_: P]: P[(Name,Signature)] = P(
    sort ~/ ident ~~ (
      ("(" ~ (sort ~ ident.?).rep(sep=","./) ~ ")").
        map(xs => xs.map(_._1).toList.reduceRightOption(Tuple).getOrElse(core.Unit))
      | "".!.map(_ => core.Unit)
    )
  ).map({case (ty,n,args) => (n, (Some(args), ty, None, UnknownLocation))})

  /** `HP name ::= program;` program definition. */
  def progDef[_: P]: P[(Name,Signature)] = P( "HP" ~/ ident ~/ "::=" ~/ program ~ ";" ).
    map({case (s,idx,p) => ((s,idx),(None, Trafo, Some(p), UnknownLocation))})

  /** `ProgramVariables declarationsOrDefinitions End.` parsed. */
  def declarations[_: P]: P[Declaration] = P ("ProgramVariables" ~/
    //@todo retain location information
    //@todo how to ensure there is some whitespace between sort and baseVariable?
    (sort ~ ident ~ ("," ~ ident).rep ~ ";").map({case (ty,x,xs) => (xs.+:(x)).toList.map(v=>v->ty)})
      .rep.map(xs => Declaration(xs.flatten.map(x=>x._1->(None,x._2,None,UnknownLocation)).toMap, Map.empty))
    ~ "End." )

  /** `Problem  formula  End.` parsed. */
  def problem[_: P]: P[Formula] = P("Problem" ~/ formula ~ "End." )

  //@todo tactic.rep needs tactic parser or skip ahead to End. and ask BelleParser.
  def tactic[_: P]: P[Unit] = P( "Tactic" ~ "End.")
}
