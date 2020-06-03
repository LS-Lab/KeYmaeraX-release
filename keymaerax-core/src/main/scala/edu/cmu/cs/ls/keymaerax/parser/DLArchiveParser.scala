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
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.DLBelleParser
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

  /** Which formula/term/program parser this archive parser uses. */
  val expParser = DLParser

  /**
    * Parse an archive file string into a list of archive entries.
    * @param input The contents of the archive file.
    * @return A list of archive entries occurring in the string.
    * @see [[parse()]]
    */
  def apply(input: String) : List[ParsedArchiveEntry] = parse(input)
  /** Parse an archive file string into a list of archive entries, same as [[apply()]] */
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
  def archiveEntries[_: P]: P[List[ParsedArchiveEntry]] = P( Start ~
    sharedDefinitions.? ~
    archiveEntry.rep(1) ~
    End).map({case (shared,entries) => entries.toList})
  //@todo add sharedDefinition to all entries

  /** Parse a single archive entry. */
  def archiveEntry[_: P]: P[ParsedArchiveEntry] = P( ("ArchiveEntry" | "Lemma" | "Theorem" | "Exercise").!.
    map({case "Exercise"=>"exercise" case "Lemma" => "lemma" case _=>"theorem"}) ~~ blank ~
    (label ~ ":").? ~ string ~
    metaInfo ~
    allDeclarations ~
    problem ~
    tacticProof.? ~
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
    NoCut(programVariables ~ definitions).map(p=>p._1++p._2) |
    (definitions.? ~ programVariables.?).
      map({case (a,b) => optjoin(a,b).getOrElse(Declaration(Map.empty))})
  )

  private def optjoin(a: Option[Declaration], b: Option[Declaration]): Option[Declaration] = a match {
    case None => b
    case Some(d) => b match {
      case None => a
        //@todo complain about conflicting declarations
      case Some(e) => Some(d++e)
    }
  }

  /** `Description "text".` parsed. */
  def description[_: P]: P[String] = P("Description" ~~ blank~/ string ~ "." )

  /** `Title "text".` parsed. */
  def title[_: P]: P[String] = P("Title" ~~ blank~/ string ~ "." )

  /** `Link "text".` parsed. */
  def link[_: P]: P[String] = P("Link" ~~ blank~/ string ~ "." )

  /** `SharedDefinitions declOrDef End.` parsed. */
  def sharedDefinitions[_: P]: P[Declaration] = P("SharedDefinitions" ~~ blank ~/ declOrDef.rep ~ "End." ).
    map(list => Declaration(list.flatten.toMap))

  /** `Definitions declOrDef End.` parsed. */
  def definitions[_: P]: P[Declaration] = P("Definitions" ~~ blank ~/ declOrDef.rep ~ "End." ).
    map(list => Declaration(list.flatten.toMap))
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
  def declOrDef[_: P]: P[List[(Name,Signature)]] = P(
    NoCut(progDef).map(p => p::Nil)
    | NoCut(declPartList ~ ";")
    | NoCut(declPart ~ "=" ~ term ~ ";").map({case (id, sig, e) => (id, (sig._1, sig._2, Some(e), sig._4))::Nil})
    | NoCut(declPart ~ "<->" ~ formula ~ ";").map({case (id, sig, f) => (id, (sig._1, sig._2, Some(f), sig._4))::Nil})
  )

  /** `sort name(sort1 arg1, sorg2 arg2)` single declaration part.*/
  def declPart[_: P]: P[(Name,Signature)] = P(
    sort ~~ blank ~~/ ident ~~ (
      ("(" ~ (sort ~~ (blank ~ ident).?).rep(sep=","./) ~ ")").
        map(xs => xs.map(_._1).toList.reduceRightOption(Tuple).getOrElse(core.Unit))
      | "".!.map(_ => core.Unit)
    )
  ).map({case (ty,n,args) => (n, (Some(args), ty, None, UnknownLocation))})

  /** `sort nameA(sort1A arg1A, sorg2A arg2A), nameB(sort1B arg1B)` list declaration part.*/
  def declPartList[_: P]: P[List[(Name,Signature)]] = P(
    sort ~~ blank ~~/ (ident ~~ (
      ("(" ~ (sort ~~ (blank ~ ident).?).rep(sep=","./) ~ ")").
        map(xs => xs.map(_._1).toList.reduceRightOption(Tuple).getOrElse(core.Unit))
        | "".!.map(_ => core.Unit)
      )).rep(sep=","./)
  ).map({case (ty,decllist) => decllist.map({case (n,idx,args) => ((n,idx), (Some(args), ty, None, UnknownLocation))}).toList})

  /** `HP name ::= program;` program definition. */
  def progDef[_: P]: P[(Name,Signature)] = P(
    "HP" ~~ blank ~ ident ~ "::=" ~ ("{" ~ (NoCut(program) | odeprogram) ~ "}" /*| NoCut(program)*/) ~ ";".?
  ).map({case (s,idx,p) => ((s,idx),(None, Trafo, Some(p), UnknownLocation))})

  /** `ProgramVariables Real x; Real y,z; End.` parsed. */
  def programVariables[_: P]: P[Declaration] = P ("ProgramVariables" ~~ blank ~/
    //@todo retain location information
    //@todo how to ensure there is some whitespace between sort and baseVariable?
    (sort ~ ident ~ ("," ~ ident).rep ~ ";").map({case (ty,x,xs) => (xs.+:(x)).toList.map(v=>v->ty)})
      .rep.map(xs => Declaration(xs.flatten.map(x=>x._1->(None,x._2,None,UnknownLocation)).toMap))
    ~ "End." )

  /** `Problem  formula  End.` parsed. */
  def problem[_: P]: P[Formula] = P("Problem" ~~ blank ~/ formula ~ "End." )

  //@todo tactic needs tactic parser or skip ahead to End. and ask BelleParser.
  def tacticProof[_: P]: P[Unit] = P( "Tactic" ~~ blank ~ string.? ~ tactic ~/ "End.")


  // externals

  /** Explicit nonempty whitespace terminal from [[expParser]]. */
  def blank[_:P]: P[Unit] = expParser.blank

  /** parse a number literal from [[expParser]] */
  def number[_: P]: P[Number] = expParser.number
  /** parse an identifier from [[expParser]] */
  def ident[_: P]: P[(String,Option[Int])] = expParser.ident
  def string[_: P]: P[String] = expParser.string

  def baseVariable[_: P]: P[BaseVariable] = expParser.baseVariable

  /** term: Parses a dL term from [[expParser]]. */
  def term[_: P]: P[Term] = expParser.term

  /** formula: Parses a dL formula from [[expParser]]. */
  def formula[_: P]: P[Formula] = expParser.formula

  /** program: Parses a dL program from [[expParser]]. */
  def program[_: P]: P[Program] = expParser.program

  /** odeprogram: Parses an ode system from [[expParser]]. */
  def odeprogram[_: P]: P[Program] = expParser.odeprogram

  def tactic[_: P]: P[BelleExpr] = DLBelleParser.tactic
}
