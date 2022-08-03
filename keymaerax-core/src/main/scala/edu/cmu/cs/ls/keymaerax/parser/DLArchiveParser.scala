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
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{DLTacticParser, TacticParser}
import edu.cmu.cs.ls.keymaerax.parser.ODEToInterpreted.FromProgramException

import scala.collection.immutable._
import scala.collection.mutable.ListBuffer

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

  /** @inheritdoc */
  override def exprParser: Parser = expParser

  /** @inheritdoc */
  override def tacticParser: TacticParser = tacticParser

  val archiveParser: String => List[ParsedArchiveEntry] = input => fastparse.parse(ParserHelper.checkUnicode(ParserHelper.removeBOM(input)), archiveEntries(_)) match {
    case Parsed.Success(value, index) =>
      if (value.length==1)
        List(value.head.withProblemContent(input.trim))
      else
        value
    case f: Parsed.Failure => throw parseException(f) //@todo? .inContext(input)
  }

  private val problemOrFormulaParser: String => Formula = input => fastparse.parse(ParserHelper.checkUnicode(ParserHelper.removeBOM(input)), problemOrFormula(_)) match {
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
  def problemOrFormula[_: P]: P[Formula] = P( Start ~ (problem.map(_._1) | formula) ~ End )



  /** Parse a list of archive entries */
  def archiveEntries[_: P]: P[List[ParsedArchiveEntry]] =
    for {
      shared <- Start ~ DLParserUtils.captureWithValue(sharedDefinitions).?
      entries <- DLParserUtils.captureWithValue(archiveEntry(shared.map(_._1))).rep(1) ~ End
    } yield entries.map({ case (entry, content) =>
      entry.withFileContent(shared.map(_._2).getOrElse("") + content)
    }).toList

  /** Parse a single archive entry without source. */
  def archiveEntryNoSource[_: P](shared: Option[Declaration]): P[ParsedArchiveEntry] = {
    val al = Parser.parser.annotationListener
    val annotations = ListBuffer.empty[(Program, Formula)]
    Parser.parser.setAnnotationListener((p: Program, f: Formula) => annotations.append((p, f)))
    try {
      (archiveStart ~~/ blank ~ (label ~ ":").? ~ string ~
        metaInfo ~
      (for {
        archiveDecls <- allDeclarations
        rest <- problem ~ /* todo refactor to pass definitions to problem parser to check along the way instead of elaborating after */
          tacticProof(shared.map(_ ++ archiveDecls).getOrElse(archiveDecls)).rep
      } yield (archiveDecls, rest))
        ~ metaInfo ~
        ("End" ~ label.? ~ ".")
      ).flatMapX({ case (kind, label, name, meta, (decl, (prob, probString, tacs)), moremeta, endlabel) =>
        if (endlabel.isDefined && endlabel != label)
          Fail.opaque("end label: " + endlabel + " is optional but should be the same as the start label: " + label)
        else {
          val usedShared = shared.map(d => Declaration(ArchiveParser.defsUsedIn(d, prob +: annotations.map(_._2).toList, Set.empty)))
          val result = // definitions elaboration to replace arguments by dots and do type analysis
            ArchiveParser.elaborate(ParsedArchiveEntry(
              name = name,
              kind = kind,
              fileContent = "<undefined>",
              problemContent = probString.trim,
              defs = usedShared.map(_ ++ decl).getOrElse(decl),
              model = prob,
              tactics = tacs.map({ case (tn, (t, ts)) => (tn.getOrElse("<undefined>"), ts.trim, t) }).toList,
              annotations = annotations.toList,
              //@todo check that there are no contradictory facts in the meta and moremeta
              info = (if (label.isDefined) Map("id" -> label.get) else Map.empty) ++ meta ++ moremeta
            ))
          result.annotations.foreach({ case (p: Program, f: Formula) => al(p, f) })
          Pass(result)
        }
      })
    } finally {
      Parser.parser.setAnnotationListener(al)
    }
  }

  /** Parses a single archive entry */
  def archiveEntry[_: P](shared: Option[Declaration]): P[ParsedArchiveEntry] = DLParserUtils.captureWithValue(archiveEntryNoSource(shared)).map({
    case (e, s) => e.copy(fileContent = s.trim)
  })

  def archiveStart[_: P]: P[String] = P(
    ("ArchiveEntry" | "Lemma" | "Theorem" | "Exercise").!./.
      map({case "Exercise"=>"exercise" case "Lemma" => "lemma" case _=>"theorem"})
  )

  /** meta information */
  def metaInfo[_: P]: P[Map[String,String]] = P(
    DLParserUtils.repFold(Map.empty[String,String])(acc =>
      (metaInfoKey ~~/ blank ~ string ~ ".").
        flatMap{case (key, value) =>
          if (acc.contains(key))
            Fail.opaque(s"MetaInfo key $key appears twice")
          else
            Pass(acc + (key -> value))
        })
  )
  def metaInfoKey[_: P]: P[String] = P(
    ("Description" | "Title" | "Link" | "Author" | "See" | "Illustration" | "Citation").!
  )

  /** Functions and ProgramVariables block in any order */
  def allDeclarations[_: P]: P[Declaration] = {
    DLParserUtils.repFold(Declaration(Map.empty))(curDecls => programVariables(curDecls) | definitions(curDecls))
  }

  /** Merges `newDecls` into `curDecls`, but checks that no duplicate symbol names occur. */
  private def uniqueDecls(curDecls: Declaration, newDecls: List[(Name, Signature)])(implicit ctx: P[_]) = {
    val nn = newDecls.map(_._1)
    //@todo Fail messages show up in Expected and Hint
    nn.diff(nn.distinct) match {
      case Nil =>
        val ix = curDecls.decls.keySet.intersect(nn.toSet)
        if (ix.isEmpty) Pass(curDecls ++ Declaration(newDecls.toMap))
        else Fail.opaque("Unique name (" + ix.map(_.prettyString).mkString(",") + " not unique)")
      case d => Fail.opaque("Unique name (" + d.map(_.prettyString).mkString(",") + " not unique)")
    }
  }

  /** `SharedDefinitions declOrDef End.` parsed. */
  def sharedDefinitions[_: P]: P[Declaration] = P(
    "SharedDefinitions" ~~/ blank ~
      DLParserUtils.repFold(Declaration(Map.empty))(curDecls => declOrDef(curDecls).flatMap(uniqueDecls(curDecls, _))
      ) ~ "End."
  )

  /** `Definitions declOrDef End.` parsed. */
  def definitions[_: P](curDecls: Declaration): P[Declaration] = P(
    "Definitions" ~~/ blank ~
      DLParserUtils.repFold(curDecls)(curDecls => declOrDef(curDecls).flatMap(uniqueDecls(curDecls, _))
      ) ~ "End."
  )

  /** `implicit Real name1(Real arg1, Real arg2), name2(Real arg1, Real arg2) '= {initConds; ode};` ODE function definition or
    * `sort name(sort1 arg1, sorg2 arg2);` declaration or
    * `sort name(sort1 arg1, sorg2 arg2) = term;` function definition or
    * `Bool name(sort1 arg1, sorg2 arg2) <-> formula;` predicate definition or
    * `HP name ::= program;` program definition. */
  def declOrDef[_: P](curDecls: Declaration): P[List[(Name, Signature)]] = (
      implicitDef(curDecls) ~ ";"
    | progDef.map(p => p::Nil)
    | declPartList.flatMap(decls =>
        Pass(decls) ~ ";"./
        | (decls match {
          case (id,sig)::Nil =>
            ("="./ ~ term(true) ~ ";").map(e => (id, sig.copy(interpretation = Some(e)))::Nil) |
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
  def declPart[_: P](ty: Sort) : P[(Name,Signature)] = (
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
  def declPartList[_: P]: P[List[(Name,Signature)]] = (
    (sort ~~ blank ~/ Pass).flatMap(sort =>
      declPart(sort).rep(sep=","./).
        map(_.toList)
    )
  )

  /** `HP name ::= {program};` | `HG name ::= {program};` program definition. */
    //@todo better return type with ProgramConst/SystemConst instead of Name
  def progDef[_: P]: P[(Name,Signature)] = P(
    ("HP" | "HG") ~~ blank ~/ ident ~ "::=" ~ "{" ~/ (NoCut(program) | odeprogram) ~ "}" ~ ";"
  ).map({case (s,idx,p) => (Name(s,idx), Signature(Some(Unit), Trafo, None, Some(p), UnknownLocation))})

  /** `ProgramVariables Real x; Real y,z; End.` parsed. */
  def programVariables[_: P](curDecls: Declaration): P[Declaration] = P ("ProgramVariables" ~~ blank ~/
    //@todo retain location information
    //@todo how to ensure there is some whitespace between sort and baseVariable?
    (sort ~/ ident ~ (","./ ~ ident).rep ~ ";").map({ case (ty, x, xs) => (x +: xs).toList.map(_ -> ty) }).rep.flatMap(xs => {
      val ns = xs.flatten.map(x=>Name(x._1._1, x._1._2)->Signature(None,x._2,None,None,UnknownLocation))
      val n = ns.map(_._1)
      if (n.size == n.distinct.size) uniqueDecls(curDecls, ns.toList)
      else Fail.opaque("Unique name (" + n.diff(n.distinct).map(_.prettyString).mkString(",") + " not unique)")
    })
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

  def implicitDefODE[_: P](curDecls: Declaration): P[List[(Name,Signature)]] = (
    (declPartList ~ "=" ~/ "{" ~ program ~ "}")
      .flatMap{case (sigs, preProg) =>
        if (sigs.exists(s => !s._2.domain.contains(Real) || s._2.codomain != Real))
          return Fail.opaque("Implicit ODE declarations can only declare real-valued " +
            "functions of a single real variable.")

        val (t,Real) = sigs.head._2.arguments.get.head
        if (sigs.exists(_._2.arguments.get.head._1 != t))
          return Fail.opaque("Implicit ODE declarations should all use the same " +
            "time argument.")

        val nameSet = sigs.map(_._1).toSet

        if (nameSet.size != sigs.size)
          return Fail.opaque("Tried declaring same function twice in an implicit ODE definition")

        // Hack: expand prior declarations in the program, to allow programs containing prior
        // definitions in block
        val prog = curDecls.expandFull(preProg)

        val interpFuncs = try {
          ODEToInterpreted.fromProgram(prog,Variable(t.name,t.index))
        } catch {
          case FromProgramException(s) => return Fail.opaque("Failed to parse implicit definition by ODE: " + s)
        }

        if (interpFuncs.exists(f => !nameSet.contains(Name(f.name, f.index))))
          return Fail.opaque("ODE variable missing from implicit declaration")

        val redef = InterpretedSymbols.builtin.intersect(interpFuncs)
        if (redef.nonEmpty)
          return Fail.opaque("Not redefining builtin symbols (" + redef.map(f => Name(f.name, f.index).prettyString).mkString(",") + " redefined)")

        Pass(interpFuncs.map{f =>
          Name(f.name, f.index) -> Signature(
            domain = Some(Real), codomain = Real, arguments = Some(List((t,Real))),
            interpretation = Some(FuncOf(f, Variable(t.name, t.index, Real))),
            loc = UnknownLocation)
        }.toList)
      }
  )

  /* Commented out because this syntax was removed in favor of syntactic
   * restriction to ODE implicit defs
   */
  /*
  def implicitDefInterp[_: P]: P[(Name,Signature)] = (
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
  def problem[_: P]: P[(Formula,String)] = P("Problem" ~~ blank ~/ DLParserUtils.captureWithValue(formula) ~ "End." )

  def tacticProof[_: P](defs: Declaration): P[(Option[String],(BelleExpr,String))] = P( "Tactic" ~~ blank ~/ string.? ~ DLParserUtils.captureWithValue(tactic(defs)) ~ "End.")


  // externals

  /** Explicit nonempty whitespace terminal from [[expParser]]. */
  def blank[_:P]: P[Unit] = expParser.blank

  /** parse a number literal from [[expParser]] */
  def number[_: P]: P[Number] = expParser.numberLiteral
  /** parse an identifier from [[expParser]] */
  def ident[_: P]: P[(String,Option[Int])] = expParser.ident
  def string[_: P]: P[String] = expParser.string

  def baseVariable[_: P]: P[BaseVariable] = expParser.baseVariable

  /** term: Parses a dL term from [[expParser]]. */
  def term[_: P](doAmbigCuts: Boolean): P[Term] = expParser.term(doAmbigCuts)

  /** formula: Parses a dL formula from [[expParser]]. */
  def formula[_: P]: P[Formula] = expParser.formula

  /** program: Parses a dL program from [[expParser]]. */
  def program[_: P]: P[Program] = expParser.program

  /** odeprogram: Parses an ode system from [[expParser]]. */
  def odeprogram[_: P]: P[ODESystem] = expParser.odeprogram

  def tactic[_: P](defs: Declaration): P[BelleExpr] = {
    tacticParser.setDefs(defs)
    tacticParser.setDefTactics(Map.empty)
    tacticParser.tactic
  }
}
