/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import fastparse._
import JavaWhitespace._
import edu.cmu.cs.ls.keymaerax.parser.DLParser.parseException
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.DLTacticParser
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import edu.cmu.cs.ls.keymaerax.parser.ODEToInterpreted.FromProgramException

import scala.collection.immutable._

/**
  * Parse a differential dynamic logic archive file string to a list of archive entries.
  * Splits a KeYmaera X archive into its parts and forwards to respective problem/tactic parsers. An archive contains
  * at least one entry combining a model in the `.kyx` format and possibly a (partial) proof tactic.
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
  * @see [[KeYmaeraXArchiveParser]]
  */
class DLArchiveParser(tacticParser: DLTacticParser) extends ArchiveParser {

  /** Which formula/term/program parser this archive parser uses. */
  private val expParser = DLParser

  /**
    * Parse an archive file string into a list of archive entries.
    * @param input The contents of the archive file.
    * @return A list of archive entries occurring in the string.
    * @see [[parse()]]
    */
  def apply(input: String) : List[ParsedArchiveEntry] = parse(input)
  /** Parse an archive file string into a list of archive entries, same as [[apply()]] */
  def parse(input: String) : List[ParsedArchiveEntry] = archiveParser(input)

  override def parse(input: String, parseTactics: Boolean): List[ParsedArchiveEntry] = parse(input)

  /** Tries parsing as a problem first. If it fails due to a missing Problem block, tries parsing as a plain formula. */
  override def parseAsFormula(input: String): Formula = problemOrFormulaParser(input)

  override def parseFromFile(file: String): List[ParsedArchiveEntry] = ???

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

  def sort[_: P]: P[Sort] = P( ("Real" | "Bool" | "HP" | "HG").! ).
    map({case "Real" => Real case "Bool" => Bool case "HP" => Trafo case "HG" => Trafo})

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
    {case (kind, label, name, meta, decl, prob, tac, moremeta, endlabel) =>
      if (endlabel.isDefined && endlabel != label) throw ParseException("end label is optional but should be the same as the start label: " + label + " is not " + endlabel)
      // definitions elaboration to replace arguments by dots and do type analysis
      ArchiveParser.elaborate(ParsedArchiveEntry(
        name = name,
        kind = kind,
        fileContent = "???",
        problemContent = "???",
        defs = decl,
        model = prob,
        tactics = if (tac.isEmpty) Nil else List((tac.get._1.getOrElse("<undefined>"),"<source???>",tac.get._2)),
        annotations = Nil, //@todo fill annotations
        //@todo check that there are no contradictory facts in the meta and moremeta
        info = (if (label.isDefined) Map("id"->label.get) else Map.empty) ++ meta ++ moremeta
      ))}
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
    (programVariables | definitions).rep.map(_.reduceOption(_++_).getOrElse(Declaration(Map())))
  )

  /** `Description "text".` parsed. */
  def description[_: P]: P[String] = P("Description" ~~ blank ~/ string ~ "." )

  /** `Title "text".` parsed. */
  def title[_: P]: P[String] = P("Title" ~~ blank ~/ string ~ "." )

  /** `Link "text".` parsed. */
  def link[_: P]: P[String] = P("Link" ~~ blank ~/ string ~ "." )

  /** `SharedDefinitions declOrDef End.` parsed. */
  def sharedDefinitions[_: P]: P[Declaration] = P(
    "SharedDefinitions" ~~ blank ~/
      DLParserUtils.repFold(Declaration(Map.empty))(curDecls =>
        declOrDef(curDecls).map(newDecls => curDecls ++ Declaration(newDecls.toMap))
      ) ~ "End."
  )

  /** `Definitions declOrDef End.` parsed. */
  def definitions[_: P]: P[Declaration] = P(
    "Definitions" ~~ blank ~/
      DLParserUtils.repFold(Declaration(Map.empty))(curDecls =>
        declOrDef(curDecls).map(newDecls => curDecls ++ Declaration(newDecls.toMap))
      ) ~ "End."
  )

  /** `implicit Real name1(Real arg1, Real arg2), name2(Real arg1, Real arg2) '= {initConds; ode};` ODE function definition or
    * `sort name(sort1 arg1, sorg2 arg2);` declaration or
    * `sort name(sort1 arg1, sorg2 arg2) = term;` function definition or
    * `Bool name(sort1 arg1, sorg2 arg2) <-> formula;` predicate definition or
    * `HP name ::= program;` program definition. */
  def declOrDef[_: P](curDecls: Declaration): P[List[(Name, Signature)]] = P(
      implicitDef(curDecls) ~ ";"
    | progDef.map(p => p::Nil)
    | declPartList.flatMap(decls =>
        Pass(decls) ~ ";"./
        | (decls match {
          case (id,sig)::Nil =>
            ("="./ ~ term ~ ";").map(e => (id, sig.copy(interpretation = Some(e)))::Nil) |
            ("<->" ~ formula ~ ";").map(f => (id, sig.copy(interpretation = Some(f)))::Nil)
          case _ => Fail
        })
    )
  )

  private def namedTupleDo(ty1: Sort, n1: Option[Name], ty2: Sort, n2: Option[List[(Name, Sort)]]): (Sort, Option[List[(Name, Sort)]]) =
    (Tuple(ty1,ty2),
      n2 match {
        case Some(args) => Some((n1.getOrElse(throw ParseException("Either all or no arguments of function/predicate declarations should have names")),ty1) :: args)
        case None => if (n1.isEmpty) None else throw ParseException("Either all or no arguments of function/predicate declarations should have names")
      }
      )
  private def namedTuple(args: ((Sort, Option[Name]), (Sort, Option[List[(Name, Sort)]]))): (Sort, Option[List[(Name, Sort)]]) =
    namedTupleDo(args._1._1, args._1._2, args._2._1, args._2._2)
//  private def namedTuple(ty1: Sort, n1: Option[(String, Option[Int])], args: (Sort, Option[List[((String, Option[Int]), Sort)]])): (Sort, Option[List[(Name, Sort)]]) =
//    namedTupleDo(ty1, n1, args._1, args._2)
  private def namedArgs(ty1: Sort, n1: Option[Name], acc: Option[List[(Name, Sort)]]): Option[List[(Name, Sort)]] =
  n1 match {
    case Some(name) => Some((name,ty1) :: acc.getOrElse(Nil))
    case None => if (acc.isEmpty) None else throw ParseException("Either all or no arguments of function/predicate declarations should have names")
  }

  /** `name(sort1 arg1, sorg2 arg2)` declaration part.
   * Input sort is the (codomain) sort */
  def declPart[_: P](ty: Sort) : P[(Name,Signature)] = P(
    ident ~~ ("(" ~/ (sort ~~ (blank ~ ident).?).rep(sep = ","./) ~ ")"./).?
  ).map({
    case (n, idx, argList) =>
      val args = argList.map(xs => (xs.map(_._1).reduceRightOption(Tuple).getOrElse(Unit)
          , xs.zipWithIndex.foldRight(Nil: List[(Name, Sort)]) { case (((sort, name), i), acc) =>
          (Name.tupled(name.getOrElse(("_default", Some(i)))), sort) :: acc
        })).getOrElse(Unit, List())
      (Name(n, idx), Signature(Some(args._1), ty, Some(args._2), None, UnknownLocation))
  })

  /** `sort nameA(sort1A arg1A, sorg2A arg2A), nameB(sort1B arg1B)` list declaration part.*/
  def declPartList[_: P]: P[List[(Name,Signature)]] = P(
    (sort ~~ blank ~/ Pass).flatMap(sort =>
      declPart(sort).rep(sep=","./).
        map(_.toList)
    )
  )

  /** `HP name ::= {program};` | `HG name ::= {program};` program definition. */
    //@todo better return type with ProgramConst/SystemConst instead of Name
  def progDef[_: P]: P[(Name,Signature)] = P(
    ("HP" | "HG") ~~ blank ~/ ident ~ "::=" ~ "{" ~/ (NoCut(program) | odeprogram) ~ "}" ~ ";".?
  ).map({case (s,idx,p) => (Name(s,idx), Signature(Some(Unit), Trafo, None, Some(p), UnknownLocation))})

  /** `ProgramVariables Real x; Real y,z; End.` parsed. */
  def programVariables[_: P]: P[Declaration] = P ("ProgramVariables" ~~ blank ~/
    //@todo retain location information
    //@todo how to ensure there is some whitespace between sort and baseVariable?
    (sort ~ ident ~ ("," ~ ident).rep ~ ";").map({case (ty,x,xs) => (xs.+:(x)).toList.map(v=>v->ty)})
      .rep.map(xs => Declaration(xs.flatten.map(x=>Name(x._1._1, x._1._2)->Signature(None,x._2,None,None,UnknownLocation)).toMap))
    ~ "End." )

  /** implicit ...
   *
   *  implicit Real sin(Real t), cos(Real t) '=
   *    {sin:=0; cos:=1; t:=0; {t'=1, sin'=cos, cos'=-sin}};
   *
   *  implicit Real xsq(Real t) '=
   *    {{xsq:=0; t:=0;}; {xsq'=2t,t'=1}};
   *
   *  implicit Real abs(Real x) = y <->
   *    x < 0 & y = -x | x >= 0 & y = x;
   *
   *  Note that implicitly defined functions can be given directly
   *  via the f<<interp>>(...) syntax, but the syntax here avoids
   *  the need for writing out interpretations with dot terms, and
   *  introduces a substitution for the uninterpreted function at
   *  the elaboration phase.
   */
  def implicitDef[_: P](curDecls: Declaration): P[List[(Name,Signature)]] =
    P("implicit" ~~ blank ~/ (
      // This syntax was removed in favor of syntactic restriction to ODE implicit defs
      // implicitDefInterp.map(List(_)) |
      implicitDefODE(curDecls)
    ))

  def implicitDefODE[_: P](curDecls: Declaration): P[List[(Name,Signature)]] = P(
    (declPartList ~ "'=" ~/ "{" ~ program ~ "}")
      .map{case (sigs, preProg) =>
        if (sigs.exists(s => s._2.domain != Some(Real) || s._2.codomain != Real))
          throw ParseException("Implicit ODE declarations can only declare real-valued " +
            "functions of a single real variable.")

        val (t,Real) = sigs.head._2.arguments.get.head
        if (sigs.exists(_._2.arguments.get.head._1 != t))
          throw ParseException("Implicit ODE declarations should all use the same " +
            "time argument.")

        val nameSet = sigs.map(_._1).toSet

        if (nameSet.size != sigs.size)
          throw ParseException("Tried declaring same function twice in an implicit ODE definition")

        // Hack: expand prior declarations in the program, to allow programs containing prior
        // definitions in block
        val prog = curDecls.expandFull(preProg)

        val interpFuncs = try {
          ODEToInterpreted.fromProgram(prog,Variable(t.name,t.index))
        } catch {
          case FromProgramException(s) => throw ParseException("Failed to parse implicit definition by ODE: " + s)
        }

        interpFuncs.map{f =>
          if (!nameSet.contains(Name(f.name, f.index)))
            throw ParseException("ODE variable missing from implicit declaration")

          Name(f.name, f.index) -> Signature(
              domain = Some(Real), codomain = Real, arguments = Some(List((t,Real))),
              interpretation = Some(FuncOf(f, Variable(t.name, t.index, Real))),
              loc = UnknownLocation
          )
        }.toList
      }
  )

  /* Commented out because this syntax was removed in favor of syntactic
   * restriction to ODE implicit defs
   */
  /*
  def implicitDefInterp[_: P]: P[(Name,Signature)] = P(
    (declPart ~ "=" ~ ident ~ "<->" ~ formula)
      .map{case (Name(fnName, fnNameNum), sig @ Signature(Some(argSort), Real, Some(vars), None, loc), res, form) =>
        val formAfterSubstitutions = vars.zipWithIndex.foldLeft (
          // Replace res with DotTerm(0)
          form.replaceFree(
            BaseVariable(res._1,res._2,Real),
            DotTerm(idx=Some(0))
          )) { case (acc,(x,i)) =>
          // Replace x with DotTerm(i+1)
          acc.replaceFree(
            BaseVariable(x._1.name,x._1.index,x._2),
            DotTerm(idx = Some(i+1))
          )
        }

        val func = Function(fnName, fnNameNum, argSort, Real, interp = Some(formAfterSubstitutions))

        Name(fnName, fnNameNum) -> sig.copy(interpretation = Some(FuncOf(func,
            vars.map({case(name,sort)=> Variable(name.name, name.index, sort)})
                .reduceRightOption(Pair).getOrElse(Nothing)))
        )
      }
  )
  */

  /** `Problem  formula  End.` parsed. */
  def problem[_: P]: P[Formula] = P("Problem" ~~ blank ~/ formula ~ "End." )

  //@todo tactic needs tactic parser or skip ahead to End. and ask BelleParser.
  def tacticProof[_: P]: P[(Option[String],BelleExpr)] = P( "Tactic" ~~ blank ~/ string.? ~ tactic ~ "End.")


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
  def odeprogram[_: P]: P[ODESystem] = expParser.odeprogram

  def tactic[_: P]: P[BelleExpr] = tacticParser.tactic
}
