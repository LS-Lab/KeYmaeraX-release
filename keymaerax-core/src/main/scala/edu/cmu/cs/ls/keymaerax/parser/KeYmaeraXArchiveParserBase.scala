/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr, StaticSemanticsTools}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser.{declarationsOf, elaborate}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.ParseState
import edu.cmu.cs.ls.keymaerax.parser.ODEToInterpreted.FromProgramException

import scala.annotation.tailrec
import scala.collection.immutable.{List, StringOps}
import scala.collection.mutable.ListBuffer

/**
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
  *   ArchiveEntry "Entry 2". ... End.
  * }}}
  *
  * @author Stefan Mitsch
  * @see [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
  * @see [[DLArchiveParser]]
  */
abstract class KeYmaeraXArchiveParserBase extends ArchiveParser {

  private[parser] trait ArchiveItem extends OtherItem

  /** Internal entry content collected by the parser, to be converted to a ParsedArchiveEntry in post-processing. */
  private[parser] case class ArchiveEntry(name: String, kind: String, loc: Location,
                                          inheritedDefinitions: List[Definition],
                                          definitions: List[Definition],
                                          vars: List[Definition],
                                          problem: Either[Formula,List[Token]],
                                          annotations: List[Annotation],
                                          tactics: List[Tactic],
                                          info: Map[String, String]) extends ArchiveItem {
    def inheritDefs(defs: List[Definition]): ArchiveEntry = {
      ArchiveEntry(name, kind, loc, inheritedDefinitions ++ defs, definitions, vars, problem, annotations, tactics, info)
    }

    lazy val allDefs: List[Definition] = (problem match {
      case Left(fml) =>
        @tailrec
        def transitiveNames(from: List[Definition], visited: Set[String], unvisited: Set[String]): Set[String] = {
          val nextToVisit = (unvisited -- visited).flatMap(s => from.filter(_.indexedName == s)).map(_.symbols)
          if (nextToVisit.isEmpty) visited
          else if (nextToVisit.exists(_.isEmpty)) from.map(_.indexedName).toSet //@note entry is an exercise
          else transitiveNames(from, visited ++ unvisited, nextToVisit.flatMap(_.get).map(_.toString))
        }

        val defSymbols = definitions.map(_.symbols)
        if (defSymbols.exists(_.isEmpty)) {
          //@note one of the entry definitions is an exercise: we don't know yet which of the shared definitions might be used, so return all
          inheritedDefinitions
        } else {
          val used = StaticSemantics.symbols(fml) ++ defSymbols.flatMap(_.get).toSet
          val transitiveUsedNames = transitiveNames(inheritedDefinitions, Set.empty, used.map(_.toString))
          val transitiveUsed = inheritedDefinitions.filter(d => transitiveUsedNames.contains(d.indexedName))
          if (transitiveUsed.exists(_.symbols.isEmpty)) {
            //@note at least one exercise definition is used in entry, return all definitions
            inheritedDefinitions
          } else {
            //@note none of the exercise definitions is used, filter out the ones that do not fit program variables
            // nor the must-bound variables of the problem, e.g., could have formula \forall x [inc;]x>=old(x)
            val problemVars = problem match {
              case Left(fml) =>
                val mbv = StaticSemantics.boundVars(fml) -- StaticSemantics.freeVars(fml)
                if (mbv.isInfinite) Set.empty
                else mbv.toSet
              case Right(_) => Set.empty
            }
            val varNames = vars.map(_.indexedName) ++ problemVars.filter(_.isInstanceOf[BaseVariable]).map(_.prettyString)
            val definedNames = inheritedDefinitions.map(_.indexedName) //@note are still variables here but will be elaborated later
            val (useOnlyDefSymbols, useUndefSymbols) = inheritedDefinitions.filterNot(_.symbols.isEmpty).partition({
              case d: FuncPredDef => (d.freeVars.toSet[Variable].filter(_.isInstanceOf[BaseVariable]).map(_.prettyString) -- varNames -- definedNames).isEmpty
              case d: ProgramDef => (d.symbols.get.filter(_.isInstanceOf[BaseVariable]).map(_.prettyString) -- varNames -- definedNames).isEmpty
            })
            val report = useUndefSymbols.filter(transitiveUsed.contains)
            if (report.nonEmpty) throw ParseException("Definition " + report.head.indexedName + " uses undefined symbols " +
              (report.head.symbols.get.filter(_.isInstanceOf[BaseVariable]).map(_.prettyString) -- varNames -- definedNames).mkString(","), report.head.loc)
            useOnlyDefSymbols
          }
        }
      case _ => inheritedDefinitions //@note entry formula is an exercise
    }) ++ definitions ++ vars

    def allAnnotations: List[Annotation] = annotations ++ definitions.flatMap({ case ProgramDef(_, _, _, annotations, _) => annotations case _ => Nil })
  }
  private[parser] case class ArchiveEntries(entries: List[ArchiveEntry]) extends ArchiveItem {
    def inheritDefs(defs: List[Definition]): ArchiveEntries = ArchiveEntries(entries.map(_.inheritDefs(defs)))
  }

  private[parser] abstract class Definition(val name: String, val index: Option[Int],
                                            val definition: Either[Option[Expression], List[Token]],
                                            val loc: Location) extends ArchiveItem {
    def extendLocation(end: Location): Definition

    /** Prints the indexed name. */
    def indexedName: String = name + index.map("_" + _).getOrElse("")

    /** Returns the symbols used in the definition; None for exercises since not yet fully known. */
    def symbols: Option[Set[NamedSymbol]] = definition match {
      case Left(Some(e)) => Some(StaticSemantics.symbols(e))
      case Left(None) => Some(Set.empty)
      case Right(_) => None
    }

    /** Returns the free variables of the definition. */
    def freeVars: SetLattice[Variable] = definition match {
      case Left(Some(e)) => StaticSemantics.freeVars(e)
      case Left(None) => SetLattice.bottom
      case Right(_) => SetLattice.allVars //@note definition is an exercise, do not yet know which variables may occur
    }
  }
  private[parser] case class ImplicitFuncFam(funcs: List[FuncPredDef]) extends ArchiveItem
  private[parser] case class FuncPredDef(override val name: String, override val index: Option[Int], sort: Sort,
                                         signature: List[NamedSymbol],
                                         override val definition: Either[Option[Expression], List[Token]],
                                         override val loc: Location) extends Definition(name, index, definition, loc) {
    override def extendLocation(end: Location): Definition = FuncPredDef(name, index, sort, signature, definition, loc.spanTo(end))
    override def freeVars: SetLattice[Variable] = super.freeVars -- signature.filterNot(_.isInstanceOf[DotTerm]).map(_.asInstanceOf[Variable])
  }

  private[parser] case class ProgramDef(override val name: String, override val index: Option[Int],
                                        override val definition: Either[Option[Program], List[Token]],
                                        annotations: List[Annotation], override val loc: Location) extends Definition(name, index, definition, loc) {
    override def extendLocation(end: Location): Definition = ProgramDef(name, index, definition, annotations, loc.spanTo(end))
  }
  private[parser] case class VarDef(override val name: String, override val index: Option[Int],
                                    override val loc: Location) extends Definition(name, index, Left(None), loc) {
    override def extendLocation(end: Location): Definition = VarDef(name, index, loc.spanTo(end))
  }
  private[parser] case class Definitions(defs: List[Definition], vars: List[Definition]) extends ArchiveItem
  private[parser] case class Annotation(element: Expression, annotation: Expression) extends ArchiveItem
  private[parser] case class Problem(fml: Either[Formula,List[Token]], annotations: List[Annotation]) extends ArchiveItem
  private[parser] case class Tactic(name: String, tacticText: String, blockLoc: Location, belleExprLoc: Location) extends ArchiveItem
  private[parser] case class Tactics(tactics: List[Tactic]) extends ArchiveItem
  private[parser] case class MetaInfo(info: Map[String, String]) extends ArchiveItem
  private[parser] case class Accept(entries: List[ArchiveEntry]) extends FinalItem

  private[parser] case class MetaInfoKey(key: String) extends ArchiveItem {
    assert(MetaInfoKey.KEYS.contains(key), "Invalid meta info key '" + key + "'; must be one of " + MetaInfoKey.KEYS.mkString(", "))
  }
  private[parser] object MetaInfoKey {
    val KEYS: List[String] = "Link" :: "Citation" :: "Title" :: "Description" :: "Author" :: "See" :: "Illustration" :: Nil
  }

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  def apply(input: String): List[ParsedArchiveEntry] = parse(input)
  /** Parse the input string in the concrete syntax as a differential dynamic logic expression.
    * Skips parsing tactics if `parseTactics` is false. Requires KeYmaeraXPrettyPrinter setup if `parseTactics` is true. */
  def parse(input: String, parseTactics: Boolean = true): List[ParsedArchiveEntry] = {
    val stripped = ParserHelper.removeBOM(input).replaceAllLiterally("\t","  ")
    val tokenStream = KeYmaeraXLexer.inMode(stripped, ProblemFileMode)
    try {
      parse(tokenStream, stripped, parseTactics).map(e =>
        if (e.defs.decls.isEmpty) elaborate(e.copy(defs = declarationsOf(e.model))) else e)
    } catch {
      //@note backwards compatibility with formula-only problem contents of old databases
      case ex: ParseException if ex.expect == "ArchiveEntry|Theorem|Lemma|Exercise" =>
        val content = Parser(input)
        val decls = declarationsOf(content)
        val name = "New Entry"
        val symbols = StaticSemantics.symbols(content)
        val defsBlock = KeYmaeraXArchivePrinter.printDefsBlock(decls, symbols)
        val varsBlock = KeYmaeraXArchivePrinter.printVarsBlock(symbols)
        val fileContent = KeYmaeraXArchivePrinter.print("ArchiveEntry", name, defsBlock, varsBlock, input, "")
        val problemContent = fileContent
        ParsedArchiveEntry(name, "theorem", fileContent, problemContent, decls, content, Nil, Nil, Map.empty) :: Nil
      case e: ParseException => throw e.inInput(stripped, Some(tokenStream))
    }
  }

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  /** Parses the input token stream (lexed from `text`); skips tactic parsing if parseTactics is false. */
  def parse(input: TokenStream, text: String, parseTactics: Boolean): List[ParsedArchiveEntry] = {
    require(input.last.tok == EOF, "token streams have to end in " + EOF)
    require(!text.contains('\t'), "Tabs in input not supported, please replace with spaces")

    parseLoop(ParseState(Bottom, input), text).stack match {
      case Bottom :+ Accept(entries) => entries.map(convert(_, text, parseTactics)).map(elaborate)
      case _ :+ Error(msg, loc, st) => throw ParseException(msg, loc, "<unknown>", "<unknown>", "", st)
      case _ => throw new AssertionError("Parser terminated with unexpected stack")
    }
  }

  /** Repeatedly perform parseStep until a final parser item is produced. */
  @tailrec
  private def parseLoop(st: ParseState, text: String): ParseState = st.stack match {
    case _ :+ (_: FinalItem) => st
    case _ => parseLoop(parseStep(st, text), text)
  }

  private def parseStep(st: ParseState, text: String): ParseState = {
    val ParseState(s, input@((nextTok@Token(la, currLoc)) :: rest)) = st

    def isReal(t: Terminal) = t == IDENT("R", None) || t == IDENT("Real", None)
    def isBool(t: Terminal) = t == IDENT("B", None) || t == IDENT("Bool", None)
    def isProgram(t: Terminal) = t == IDENT("HP", None)

    //@note This table of LR Parser matches needs an entry for every prefix substring of the grammar.
    s match {
      // shared definitions
      case r :+ (begin@Token(SHARED_DEFINITIONS_BEGIN, _)) =>
        reduce(st, 0, Bottom :+ Definitions(Nil, Nil) :+ Token(DEFINITIONS_BLOCK, UnknownLocation), r :+ begin)
      case r :+ (begin@Token(SHARED_DEFINITIONS_BEGIN, _)) :+ (defs@Definitions(_, _)) :+ (defsBlock@Token(DEFINITIONS_BLOCK, _)) if la == PERIOD || la == SEMI =>
        reduce(shift(st), 1, Bottom, r :+ begin :+ defs :+ defsBlock)

      // start entry
      case r :+ (begin@Token(ARCHIVE_ENTRY_BEGIN(_), _)) => la match {
        case _: DOUBLE_QUOTES_STRING => reduce(shift(st), 0, Bottom :+ MetaInfo(Map.empty), r :+ begin :+ input.head)
        case _: IDENT => shift(st)
        case _ => throw ParseException("Missing archive name", st, nextTok, "\"<string>\"")
      }
      case r :+ (begin@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ Token(entryId@IDENT(_, _), idLoc) => la match {
        case COLON => shift(st)
        case nextSegment: IDENT => reduce(shift(st), 2, Bottom :+ Token(IDENT(entryId.img + nextSegment.img, None), idLoc.spanTo(currLoc)), r :+ begin)
        case _ => throw ParseException("Missing entry ID separator", st, Expected.ExpectTerminal(COLON) :: Nil)
      }
      case _ :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(IDENT(_, _), _) :+ Token(COLON, _) => la match {
        case _: DOUBLE_QUOTES_STRING => shift(st)
        case _ => throw ParseException("Missing entry title", st, Expected.ExpectTerminal(DOUBLE_QUOTES_STRING("<string>")) :: Nil)
      }
      case r :+ (begin@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ Token(IDENT(entryId, entryIdx), _) :+ Token(COLON, _) :+ (name@Token(_: DOUBLE_QUOTES_STRING, _)) =>
        reduce(st, 3, Bottom :+ name :+ MetaInfo(Map("id" -> (entryId+entryIdx.getOrElse("")))), r :+ begin)
      case r :+ (begin@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(_: DOUBLE_QUOTES_STRING, _)) :+ (info@MetaInfo(_)) if la == PERIOD || la == SEMI =>
        reduce(shift(st), 1, Bottom, r :+ begin :+ name :+ info)
      // finish entry
      case r@(_ :+ (tok@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+
        Definitions(_, _) :+ Problem(_, _) :+ Tactics(_)) => la match {
        case END_BLOCK => shift(st)
        case TACTIC_BLOCK => shift(st)
        case IDENT(key, None) if MetaInfoKey.KEYS.contains(key) => reduce(shift(st), 1, Bottom :+ MetaInfoKey(key), r)
        case _ => throw ParseException.imbalancedErrorHere(tok + /*" from " + tok.loc +*/ " has no matching " + END_BLOCK.img+PERIOD.img, unmatched=tok, END_BLOCK.img+PERIOD.img, st,
          hint="Every entry (including ArchiveEntry, Problem, Lemma, Theorem, and Exercise)" +  " needs its own " + END_BLOCK.img+PERIOD.img + " delimiter.")
      }
      case r :+ Token(ARCHIVE_ENTRY_BEGIN(kind), startLoc) :+ Token(DOUBLE_QUOTES_STRING(name), _) :+ MetaInfo(info) :+ Definitions(defs, vars) :+
        Problem(problem, annotations) :+ Tactics(tactics) :+ Token(END_BLOCK, _) => la match {
        case PERIOD => reduce(shift(st), 8, Bottom :+ ArchiveEntry(name, kind, startLoc.spanTo(currLoc.end), Nil, defs, vars, problem, annotations, tactics, info), r)
        case _: IDENT => shift(st)
        case _ => throw ParseException("Missing " + PERIOD.img + " after " + END_BLOCK.img + " delimiter", st, Expected.ExpectTerminal(PERIOD) :: Nil)
      }
      case r :+ (archiveBegin@Token(ARCHIVE_ENTRY_BEGIN(kind), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(entryName), _)) :+ (info@MetaInfo(_)) :+ (defs@Definitions(_, _)) :+
        (problem@Problem(_, _)) :+ (tactics@Tactics(_)) :+ (archiveEnd@Token(END_BLOCK, _)) :+ Token(entryId@IDENT(_, _), idLoc) => la match {
        case PERIOD if info.info.contains("id") && info.info("id") == entryId.img => reduce(st, 1, Bottom, r :+ archiveBegin :+ name :+ info :+ defs :+ problem :+ tactics :+ archiveEnd)
        case PERIOD if !info.info.contains("id") => throw ParseException("Archive entry ends with undefined ID " + entryId.img + "; define ID at entry start with " + kind + " " + entryId.img + " : \""  + entryName + "\"", idLoc)
        case PERIOD if info.info("id") != entryId.img => throw ParseException("Archive entry ends with ID " + entryId.img + " but entry start defined " + info.info("id"), idLoc)
        case nextSegment: IDENT => reduce(shift(st), 2, Bottom :+ Token(IDENT(entryId.img + nextSegment.img, None), idLoc.spanTo(currLoc)), r :+ archiveBegin :+ name :+ info :+ defs :+ problem :+ tactics :+ archiveEnd)
        case _ => throw ParseException("Missing entry ID separator", st, Expected.ExpectTerminal(COLON) :: Nil)
      }

      // collect entries
      case r :+ (lentry: ArchiveEntry) :+ (rentry: ArchiveEntry) =>
        reduce(st, 2, Bottom :+ ArchiveEntries(lentry :: rentry :: Nil), r)
      case r :+ ArchiveEntries(lentries) :+ (rentry: ArchiveEntry) =>
        reduce(st, 2, Bottom :+ ArchiveEntries(lentries :+ rentry), r)

      // metainfo (at any position inside entries)
      case r :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ MetaInfoKey(_) => la match {
        case DOUBLE_QUOTES_STRING(_) => shift(st)
        case _ => throw ParseException("Invalid meta info value", st, Expected.ExpectTerminal(DOUBLE_QUOTES_STRING("")) :: Nil)
      }
      case r :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ Definitions(_, _) :+ MetaInfoKey(_) => la match {
        case DOUBLE_QUOTES_STRING(_) => shift(st)
        case _ => throw ParseException("Invalid meta info value", st, Expected.ExpectTerminal(DOUBLE_QUOTES_STRING("")) :: Nil)
      }
      case r :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ Definitions(_, _) :+ Problem(_, _) :+ MetaInfoKey(_) => la match {
        case DOUBLE_QUOTES_STRING(_) => shift(st)
        case _ => throw ParseException("Invalid meta info value", st, Expected.ExpectTerminal(DOUBLE_QUOTES_STRING("")) :: Nil)
      }
      case r :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ Definitions(_, _) :+ Problem(_, _) :+ Tactics(_) :+ MetaInfoKey(_) => la match {
        case DOUBLE_QUOTES_STRING(_) => shift(st)
        case _ => throw ParseException("Invalid meta info value", st, Expected.ExpectTerminal(DOUBLE_QUOTES_STRING("")) :: Nil)
      }
      case r :+ (entry@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) :+ MetaInfo(info) :+ MetaInfoKey(infoKey) :+ Token(DOUBLE_QUOTES_STRING(infoValue), _) => la match {
        case PERIOD | SEMI => reduce(shift(st), 4, Bottom :+ MetaInfo(info ++ Map(infoKey -> infoValue)), r :+ entry :+ name)
        case _ => throw ParseException("Missing meta info delimiter", st, Expected.ExpectTerminal(PERIOD) :: Expected.ExpectTerminal(SEMI) :: Nil)
      }
      case r :+ (entry@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) :+ MetaInfo(info) :+ (defs@Definitions(_, _)) :+ MetaInfoKey(infoKey) :+ Token(DOUBLE_QUOTES_STRING(infoValue), _) => la match {
        case PERIOD | SEMI => reduce(shift(st), 5, Bottom :+ MetaInfo(info ++ Map(infoKey -> infoValue)) :+ defs, r :+ entry :+ name)
        case _ => throw ParseException("Missing meta info delimiter", st, Expected.ExpectTerminal(PERIOD) :: Expected.ExpectTerminal(SEMI) :: Nil)
      }
      case r :+ (entry@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) :+ MetaInfo(info) :+ (defs@Definitions(_, _)) :+ (problem@Problem(_, _)) :+ MetaInfoKey(infoKey) :+ Token(DOUBLE_QUOTES_STRING(infoValue), _) => la match {
        case PERIOD | SEMI => reduce(shift(st), 6, Bottom :+ MetaInfo(info ++ Map(infoKey -> infoValue)) :+ defs :+ problem, r :+ entry :+ name)
        case _ => throw ParseException("Missing meta info delimiter", st, Expected.ExpectTerminal(PERIOD) :: Expected.ExpectTerminal(SEMI) :: Nil)
      }
      case r :+ (entry@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) :+ MetaInfo(info) :+ (defs@Definitions(_, _)) :+ (problem@Problem(_, _)) :+ (tactics@Tactics(_)) :+ MetaInfoKey(infoKey) :+ Token(DOUBLE_QUOTES_STRING(infoValue), _) => la match {
        case PERIOD | SEMI => reduce(shift(st), 7, Bottom :+ MetaInfo(info ++ Map(infoKey -> infoValue)) :+ defs :+ problem :+ tactics, r :+ entry :+ name)
        case _ => throw ParseException("Missing meta info delimiter", st, Expected.ExpectTerminal(PERIOD) :: Expected.ExpectTerminal(SEMI) :: Nil)
      }

      // entry components: optional meta info, definitions, program variables before mandatory problem
      case r :+ (entry@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) :+ (info@MetaInfo(_)) => la match {
        case IDENT(key, None) if MetaInfoKey.KEYS.contains(key) => reduce(shift(st), 1, Bottom :+ MetaInfoKey(key), r :+ entry :+ name :+ info)
        case DEFINITIONS_BLOCK | FUNCTIONS_BLOCK => shift(st)
        case PROGRAM_VARIABLES_BLOCK => shift(st)
        case PROBLEM_BLOCK if !rest.exists(t => t.tok == DEFINITIONS_BLOCK || t.tok == FUNCTIONS_BLOCK || t.tok == PROGRAM_VARIABLES_BLOCK) =>
          reduce(st, 0, Bottom :+ Definitions(Nil, Nil), r :+ entry :+ name :+ info)
        case PROBLEM_BLOCK if rest.exists(t => t.tok == DEFINITIONS_BLOCK || t.tok == FUNCTIONS_BLOCK || t.tok == PROGRAM_VARIABLES_BLOCK) =>
          throw ParseException("Misplaced definitions/program variables: expected before problem", st, nextTok,
            rest.find(t => t.tok == DEFINITIONS_BLOCK || t.tok == FUNCTIONS_BLOCK || t.tok == PROGRAM_VARIABLES_BLOCK).get.tok.img)
        case TACTIC_BLOCK if !rest.exists(_.tok == PROBLEM_BLOCK) => throw ParseException("Missing problem block", st, nextTok, PROBLEM_BLOCK.img)
        case TACTIC_BLOCK if  rest.exists(_.tok == PROBLEM_BLOCK) => throw ParseException("Misplaced problem block: problem expected before tactics", st, nextTok, PROBLEM_BLOCK.img)
        case IDENT(key, _) => throw ParseException("Invalid meta info key '" + key + "'", st, nextTok, MetaInfoKey.KEYS.mkString(","))
        case _ => throw ParseException("Invalid meta info key " + la, st, nextTok, MetaInfoKey.KEYS.mkString(","))
      }

      // definitions
      case _ :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ Definitions(_, _) if la == DEFINITIONS_BLOCK || la == FUNCTIONS_BLOCK => shift(st)
      case r :+ (entry@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) :+ (info@MetaInfo(_)) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) =>
        reduce(st, 1, Bottom :+ Definitions(Nil, Nil) :+ defsBlock, r :+ entry :+ name :+ info)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) => la match {
        case PERIOD => reduce(shift(st), 1, Bottom, r :+ defs :+ defsBlock)
        case END_BLOCK => shift(st)
        case IMPLICIT => reduce(shift(st), 1, Bottom :+ ImplicitFuncFam(Nil), r :+ defs :+ defsBlock)
        case _ if isReal(la) || isBool(la) || isProgram(la) => shift(st)
        case _ => throw ParseException("Unexpected definition", st,
          Expected.ExpectTerminal(END_BLOCK) ::
            Expected.ExpectTerminal(IMPLICIT) ::
            Expected.ExpectTerminal(IDENT("Real")) ::
            Expected.ExpectTerminal(IDENT("Bool")) ::
            Expected.ExpectTerminal(IDENT("HP")) :: Nil)
      }
      case r :+ (defs: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ Token(END_BLOCK, _) => la match {
        case PERIOD => reduce(shift(st), 3, Bottom, r :+ defs)
        case _ => throw ParseException("Missing definitions delimiter", st, Expected.ExpectTerminal(PERIOD) :: Nil)
      }
      // Start: Implicit ODE function definition
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: ImplicitFuncFam) =>
        la match {
          case _ if isReal(la) => shift(st)
          case _ => throw ParseException("Unexpected sort for implicit function", st,
            Expected.ExpectTerminal(IDENT("Real")) :: Nil)
        }
      case r @ (_ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: ImplicitFuncFam)) :+ Token(sort,_) if isReal(sort) =>
        la match {
          case _: IDENT => shift(st)
          case _ => throw ParseException("Expected identifier for function", st, Nil)
        }
      case r :+ (defs: Definitions) :+ (defsBlock @ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (iff: ImplicitFuncFam) :+ Token(sort,startLoc) :+ Token(IDENT(name, index),endLoc) if isReal(sort) =>
        la match {
          case LPAREN =>
            (defs.defs ++ defs.vars).find(d => d.name == name && d.index == index) match {
              case Some(d) => throw ParseException.duplicateSymbolError(name, index, endLoc, d.loc)
              case None => reduce(st, 2, Bottom :+ FuncPredDef(name, index, Real, Nil, Left(None), startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock :+ iff)
            }
          case _ => throw ParseException("Implicit definitions must be functions", st,
            Expected.ExpectTerminal(LPAREN) :: Nil)
        }
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: ImplicitFuncFam) :+ (_: FuncPredDef) if la == LPAREN =>
        shift(st)
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: ImplicitFuncFam) :+ (_: FuncPredDef) :+ Token(LPAREN, _) =>
        la match {
          case RPAREN => shift(st)
          case x if isReal(x) => shift(st)
          case _ => throw ParseException("Unexpected token", st,
            Expected.ExpectTerminal(RPAREN) ::
              Expected.ExpectTerminal(IDENT("Real")) :: Nil)
        }
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: ImplicitFuncFam) :+ (_: FuncPredDef) :+ Token(LPAREN, _) :+ Token(sort, _) if isReal(sort) =>
        la match {
          case _: IDENT => shift(st)
          case _ => throw ParseException("Expected identifier for function argument", st, Nil)
        }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (iff: ImplicitFuncFam) :+ (next: FuncPredDef) :+ (lpar@Token(LPAREN, _)) :+ Token(sort, _) :+ Token(IDENT(name, index), endLoc) if isReal(sort) =>
        la match {
          case COMMA => shift(st)
          case _ =>
            reduce(st, 4, Bottom :+ FuncPredDef(next.name, next.index, next.sort, next.signature :+ Variable(name, index), next.definition, next.loc.spanTo(endLoc.end)) :+ lpar,
              r :+ defs :+ defsBlock :+ iff)
        }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (iff: ImplicitFuncFam) :+ (next: FuncPredDef) :+ (lpar@Token(LPAREN, _)) :+ Token(sort, _) :+ Token(IDENT(name, index), _) :+ Token(COMMA, endLoc) if isReal(sort) =>
        reduce(st, 5, Bottom :+ FuncPredDef(next.name, next.index, next.sort, next.signature :+ Variable(name, index), next.definition, next.loc.spanTo(endLoc.end)) :+ lpar,
          r :+ defs :+ defsBlock :+ iff)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (iff: ImplicitFuncFam) :+ (next: FuncPredDef) :+ Token(LPAREN, _) :+ Token(RPAREN, endLoc) =>
        reduce(st, 3, Bottom :+ next.extendLocation(endLoc.end), r :+ defs :+ defsBlock :+ iff)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ ImplicitFuncFam(fns) :+ (next: FuncPredDef) =>
        la match {
          case COMMA =>
            reduce(shift(st), 3, Bottom :+ ImplicitFuncFam(next :: fns) :+ Token(IDENT("Real")), r :+ defs :+ defsBlock)
          case PRIME =>
            shift(st)
          case _ => throw ParseException("Unexpected token", st, Nil)
        }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ ImplicitFuncFam(fns) :+ (next: FuncPredDef) :+ Token(PRIME, _) =>
        la match {
          case EQ =>
            val (term: Either[Option[Program], List[Token]], endLoc, remainder) = parseDefinition(rest, text, KeYmaeraXParser.programTokenParser)
            val prog: Program = term match {
              case Left(Some(prog)) => prog
              case _ => throw ParseException("Expected a program of the form {initial condition}; {differentials}", st, Nil)
            }

            val sigs = (next :: fns).reverse

            sigs.foreach(s =>
              if (InterpretedSymbols.byName.contains((s.name, s.index)))
                throw ParseException("Re-definition of interpreted symbol " + s.name + " not allowed; please use a different name for your definition.",
                  s.loc.spanTo(endLoc), s.name, "A name != " + s.name)
            )

            if (sigs.exists(_.signature.size != 1))
              throw ParseException("Implicit ODE declarations must be functions of one variable.")

            val t = next.signature.head

            if (sigs.exists(_.signature.head != t))
              throw ParseException("Implicit ODE declarations must be functions of one variable.")

            val nameSet = sigs.map(s => Name(s.name, s.index)).toSet

            if (nameSet.size != sigs.size)
              throw ParseException("Tried declaring same function twice in an implicit ODE definition")

            val interpFuncs = try {
              ODEToInterpreted.fromProgram(prog,Variable(t.name,t.index))
            } catch {
              case FromProgramException(s) =>
                throw ParseException("Failed to interpret implicit definition by ODE: " + s, st, Nil)
            }

            val funcDefs = sigs.map{s =>
              val f = interpFuncs.find(f => f.name == s.name && f.index == s.index) match {
                case Some(f) => f
                case None =>
                  throw ParseException("Symbol " + s.name + " not defined by supplied ODE", s.loc.spanTo(endLoc))
              }
              s.copy(definition = Left(Some(FuncOf(f, Variable(t.name, t.index)))))
            }

            val st2 = ParseState(r :+ Definitions(defs.defs ++ funcDefs, defs.vars) :+ defsBlock, remainder)

            remainder match {
              case Token(SEMI,_) :: _ => reduce(shift(st2), 1, Bottom, r :+ Definitions(defs.defs ++ funcDefs, defs.vars) :+ defsBlock)
              case _ => throw ParseException("Expected semicolon after implicit definition", st2,
                Expected.ExpectTerminal(SEMI) :: Nil)
            }
          case _ => throw ParseException("Unexpected token in function definition", st, Expected.ExpectTerminal(EQ) :: Nil)
        }
      // End: Implicit ODE function definition
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ Token(sort, _) if (isReal(sort) || isBool(sort) || isProgram(sort)) && la.isInstanceOf[IDENT] => shift(st)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isReal(sort) =>
        (defs.defs ++ defs.vars).find(d => d.name == name && d.index == index) match {
          case Some(d) => throw ParseException.duplicateSymbolError(name, index, endLoc, d.loc)
          case None => reduce(st, 2, Bottom :+ FuncPredDef(name, index, Real, Nil, Left(None), startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)
        }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isBool(sort) =>
        (defs.defs ++ defs.vars).find(d => d.name == name && d.index == index) match {
          case Some(d) => throw ParseException.duplicateSymbolError(name, index, endLoc, d.loc)
          case None => reduce(st, 2, Bottom :+ FuncPredDef(name, index, Bool, Nil, Left(None), startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)
        }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isProgram(sort) =>
        (defs.defs ++ defs.vars).find(d => d.name == name && d.index == index) match {
          case Some(d) => throw ParseException.duplicateSymbolError(name, index, endLoc, d.loc)
          case None => reduce(st, 2, Bottom :+ ProgramDef(name, index, Left(None), Nil, startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)
        }
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: FuncPredDef) if la == LPAREN => shift(st)
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: FuncPredDef) :+ Token(LPAREN, _) if isReal(la) => shift(st)
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: FuncPredDef) :+ Token(LPAREN, _) :+ Token(sort, _) if isReal(sort) && la.isInstanceOf[IDENT] => shift(st)
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: FuncPredDef) :+ Token(LPAREN, _) :+ Token(sort, _) :+ Token(IDENT(_, _), _) if isReal(sort) && la == COMMA => shift(st)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) :+ (lpar@Token(LPAREN, _)) :+ Token(sort, _) :+ Token(IDENT(name, index), endLoc) if isReal(sort) && la != COMMA =>
        reduce(st, 4, Bottom :+ FuncPredDef(next.name, next.index, next.sort, next.signature :+ Variable(name, index), next.definition, next.loc.spanTo(endLoc.end)) :+ lpar, r :+ defs :+ defsBlock)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) :+ (lpar@Token(LPAREN, _)) :+ Token(sort, _) :+ Token(IDENT(name, index), _) :+ Token(COMMA, endLoc) if isReal(sort) =>
        reduce(st, 5, Bottom :+ FuncPredDef(next.name, next.index, next.sort, next.signature :+ Variable(name, index), next.definition, next.loc.spanTo(endLoc.end)) :+ lpar, r :+ defs :+ defsBlock)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) :+ (lpar@Token(LPAREN, _)) :+ Token(sort, _) if isReal(sort) && la == COMMA => shift(st)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) :+ (lpar@Token(LPAREN, _)) :+ Token(sort, endLoc) if isReal(sort) && la != COMMA =>
        reduce(st, 3, Bottom :+ FuncPredDef(next.name, next.index, next.sort, next.signature :+ DotTerm(Real, Some(next.signature.size)), next.definition, next.loc.spanTo(endLoc.end)) :+ lpar, r :+ defs :+ defsBlock)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) :+ (lpar@Token(LPAREN, _)) :+ Token(sort, _) :+ Token(COMMA, endLoc) if isReal(sort) =>
        reduce(st, 4, Bottom :+ FuncPredDef(next.name, next.index, next.sort, next.signature :+ DotTerm(Real, Some(next.signature.size)), next.definition, next.loc.spanTo(endLoc.end)) :+ lpar, r :+ defs :+ defsBlock)
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ (_: FuncPredDef) :+ Token(LPAREN, _) if la == RPAREN => shift(st)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) :+ Token(LPAREN, _) :+ Token(RPAREN, endLoc) =>
        reduce(st, 3, Bottom :+ next.extendLocation(endLoc.end), r :+ defs :+ defsBlock)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) if next.sort == Bool => la match {
        case EQUIV =>
          val (pred: Either[Option[Formula], List[Token]], endLoc, remainder) = parseDefinition(rest, text, KeYmaeraXParser.formulaTokenParser)
          if (InterpretedSymbols.byName.contains((next.name, next.index))) throw ParseException("Re-definition of interpreted symbol " + next.name + " not allowed; please use a different name for your definition.", next.loc.spanTo(endLoc), next.name, "A name != " + next.name)
          else ParseState(r :+ defs :+ defsBlock :+ FuncPredDef(next.name, next.index, next.sort, next.signature, pred, next.loc.spanTo(endLoc)), remainder)
        case SEMI | PERIOD => shift(st)
        case COMMA => ParseState(r :+ defs :+ defsBlock :+ next, Token(SEMI, currLoc) +: Token(IDENT("Bool"), currLoc) +: rest)
        case EQ => throw ParseException("Predicate must be defined by equivalence", st, nextTok, EQUIV.img)
        case _ => throw ParseException("Unexpected token in predicate definition", st, nextTok, EQUIV.img)
      }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) if next.sort == Real => la match {
        case EQ =>
          val (term: Either[Option[Term], List[Token]], endLoc, remainder) = parseDefinition(rest, text, KeYmaeraXParser.termTokenParser)
          if (InterpretedSymbols.byName.contains((next.name, next.index))) throw ParseException("Re-definition of interpreted symbol " + next.name + " not allowed; please use a different name for your definition.", next.loc.spanTo(endLoc), next.name, "A name != " + next.name)
          else ParseState(r :+ defs :+ defsBlock :+ FuncPredDef(next.name, next.index, next.sort, next.signature, term, next.loc.spanTo(endLoc)), remainder)
        case SEMI | PERIOD => shift(st)
        case COMMA => ParseState(r :+ defs :+ defsBlock :+ next, Token(SEMI, currLoc) +: Token(IDENT("Real"), currLoc) +: rest)
        case EQUIV => throw ParseException("Function must be defined by equality", st, nextTok, EQ.img)
        case _ => throw ParseException("Unexpected token in function definition", st, Expected.ExpectTerminal(EQ) :: Expected.ExpectTerminal(SEMI) :: Nil)
      }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (nextDef: Definition) :+ Token(SEMI | PERIOD, endLoc) =>
        reduce(st, 4, Bottom :+ Definitions(defs.defs :+ nextDef.extendLocation(endLoc.end), defs.vars) :+ defsBlock, r)

      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: ProgramDef) => la match {
        case PRG_DEF =>
          val parser = KeYmaeraXParser
          val annotationListener = parser.annotationListener
          val annotations = new ListBuffer[Annotation]()
          parser.setAnnotationListener((prg, fml) => annotations += Annotation(prg, fml))
          try {
            if (rest.head.tok != LBRACE) throw ParseException("Missing program definition start delimiter", rest.head.loc, rest.head.tok.toString, LBRACE.img, "", "", null)
            var openParens = 0
            val (Token(LBRACE, _) :: prgDefBlock, defEnd) = rest.span(t => {
              if (t.tok == LBRACE) openParens += 1 else if (t.tok == RBRACE) openParens -= 1; openParens > 0
            })
            if (defEnd.isEmpty) throw ParseException.imbalancedError("Unmatched opening brace in program definition", rest.head, RBRACE.img, ParseState(Bottom :+ rest.head, rest.tail))
            val (rbrace@Token(RBRACE, endLoc)) :: remainder = defEnd
            val program: Either[Option[Program], List[Token]] = try {
              if (!prgDefBlock.exists(_.tok == EXERCISE_PLACEHOLDER)) {
                try {
                  Left(Some(KeYmaeraXParser.programTokenParser(prgDefBlock :+ Token(EOF, endLoc))))
                } catch {
                  case ex: AssertionError if ex.getMessage.startsWith("assumption failed: binary operator expected for UnitOpSpec(PSEUDO$") =>
                    // might be an ODESystem without braces
                    Left(Some(KeYmaeraXParser.programTokenParser(Token(LBRACE) +: prgDefBlock :+ Token(RBRACE) :+ Token(EOF, endLoc))))
                  case ex: ParseException if ex.msg == "ODE without {}" =>
                    // ODE without braces
                    Left(Some(KeYmaeraXParser.programTokenParser(Token(LBRACE) +: prgDefBlock :+ Token(RBRACE) :+ Token(EOF, endLoc))))
                }
              } else {
                Right(prgDefBlock :+ Token(EOF, endLoc))
              }
            } catch {
              case ex: ParseException =>
                val (loc, found) = ex.loc match {
                  case UnknownLocation =>
                    val defLoc = prgDefBlock.head.loc.spanTo(endLoc)
                    (defLoc, slice(text, defLoc))
                  case _ if ex.found != EOF.description => (ex.loc, ex.found)
                  case _ if ex.found == EOF.description => (ex.loc, rbrace.description)
                }
                throw new ParseException(ex.msg, loc, found, ex.expect, ex.after, ex.state, ex)
            }
            ParseState(r :+ defs :+ defsBlock :+ ProgramDef(next.name, next.index, program, annotations.toList, next.loc.spanTo(endLoc.end)), remainder)
          } finally {
            parser.setAnnotationListener(annotationListener)
          }
        case SEMI | PERIOD => shift(st)
        case EQUIV | EQ => throw ParseException("Program must be defined by " + PRG_DEF.img, st, nextTok, PRG_DEF.img)
        case _ => throw ParseException("Unexpected token in program definition", st, Expected.ExpectTerminal(PRG_DEF) :: Expected.ExpectTerminal(SEMI) :: Nil)
      }

      // optional program variables (after optional definitions block)
      case r :+ (entry@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) :+ (info@MetaInfo(_)) :+ (varsBlock@Token(PROGRAM_VARIABLES_BLOCK, _)) =>
        reduce(st, 1, Bottom :+ Definitions(Nil, Nil) :+ varsBlock, r :+ entry :+ name :+ info)
      case _ :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ Definitions(_, _) if la == PROGRAM_VARIABLES_BLOCK => shift(st)
      case r :+ (varsBlock@Token(PROGRAM_VARIABLES_BLOCK, _)) => la match {
        case PERIOD => reduce(shift(st), 1, Bottom, r :+ varsBlock)
        case END_BLOCK => shift(st)
        case _ if isReal(la) => shift(st)
        case _ if isBool(la) || isProgram(la) => throw ParseException("Predicate and program definitions only allowed in Definitions block", st, nextTok, "Real")
        case _ => throw ParseException("Unexpected program variable definition", st,
          Expected.ExpectTerminal(END_BLOCK) ::
            Expected.ExpectTerminal(IDENT("Real")) :: Nil)
      }
      case r :+ Token(PROGRAM_VARIABLES_BLOCK, _) :+ Token(END_BLOCK, _) => la match {
        case PERIOD => reduce(shift(st), 3, Bottom, r)
        case _ => throw ParseException("Missing program variables delimiter", st, Expected.ExpectTerminal(END_BLOCK) :: Nil)
      }
      case _ :+ Token(PROGRAM_VARIABLES_BLOCK, _) :+ Token(sort, _) if isReal(sort) => la match {
        case _: IDENT => shift(st)
        case _ => throw ParseException("Missing identifier", st, Expected.ExpectTerminal(IDENT("<string>")) :: Nil)
      }
      case r :+ (defs: Definitions) :+ (varsBlock@Token(PROGRAM_VARIABLES_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), identLoc) if isReal(sort) => la match {
        case SEMI | PERIOD =>
          (defs.defs ++ defs.vars).find(d => d.name == name && d.index == index) match {
            case Some(d) => throw ParseException.duplicateSymbolError(name, index, identLoc, d.loc)
            case None => reduce(shift(st), 5, Bottom :+ Definitions(defs.defs, defs.vars :+ VarDef(name, index, startLoc)) :+ varsBlock, r)
          }
        case COMMA if isReal(rest.head.tok) => throw ParseException("Unexpected declaration delimiter", st, Expected.ExpectTerminal(SEMI) :: Nil)
        case COMMA =>
          (defs.defs ++ defs.vars).find(d => d.name == name && d.index == index) match {
            case Some(d) => throw ParseException.duplicateSymbolError(name, index, identLoc, d.loc)
            case None => reduce(shift(st), 5, Bottom :+ Definitions(defs.defs, defs.vars :+ VarDef(name, index, startLoc)) :+ varsBlock :+ Token(sort, startLoc), r)
          }
        case LPAREN => throw ParseException("Function definition only allowed in Definitions block", st, Expected.ExpectTerminal(SEMI) :: Expected.ExpectTerminal(COMMA) :: Nil)
        case _ if isReal(la) || isBool(la) || isProgram(la) =>
          throw ParseException("Missing variable declaration delimiter", st, Expected.ExpectTerminal(SEMI) :: Nil)
        case _ => throw ParseException("Unexpected token in ProgramVariables block", st, Expected.ExpectTerminal(SEMI) :: Expected.ExpectTerminal(COMMA) :: Nil)
      }
      case r :+ (defs: Definitions) :+ (varsBlock@Token(PROGRAM_VARIABLES_BLOCK, _)) :+ (real@Token(sort, startLoc)) :+ Token(IDENT(name, index), _) if isReal(sort) && la == COMMA =>
        reduce(shift(st), 2, Bottom :+ Definitions(defs.defs, defs.vars :+ VarDef(name, index, startLoc)) :+ varsBlock :+ real, r)

      // problem
      case r@(_ :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ Definitions(_, _)) => la match {
        case PROBLEM_BLOCK =>
          val parser = KeYmaeraXParser
          val annotationListener = parser.annotationListener
          val annotations = new ListBuffer[Annotation]()
          parser.setAnnotationListener((prg, fml) => annotations += Annotation(prg, fml))
          try {
            if (!st.input.exists(_.tok == END_BLOCK)) throw ParseException("Missing problem delimiter", st, st.input.last, END_BLOCK.img)
            val (problemBlock, Token(END_BLOCK, endLoc) :: remainder) = st.input.span(_.tok != END_BLOCK) match {
              case (Token(PROBLEM_BLOCK, _) :: Token(PERIOD, _) :: pb, (endBlock@Token(END_BLOCK, _)) :: Token(PERIOD, _) :: r) => (pb, endBlock +: r)
              case (Token(PROBLEM_BLOCK, _) :: pb, (endBlock@Token(END_BLOCK, _)) :: Token(PERIOD, _) :: r) => (pb, endBlock +: r)
              case (Token(PROBLEM_BLOCK, _) :: pb, (endBlock@Token(END_BLOCK, _)) :: r) => throw ParseException("Missing " + PERIOD.img + " after delimiter " + END_BLOCK.img, r.head.loc, r.head.description, Expected.ExpectTerminal(PERIOD).toString, endBlock.toString, st.toString)
              case (Token(PROBLEM_BLOCK, _) :: _, r) => throw ParseException("Missing problem delimiter", r.last.loc, r.last.toString, END_BLOCK.img + PERIOD.img, "", st.toString)
            }
            problemBlock.find(_.tok == TACTIC_BLOCK) match {
              case Some(t) => throw ParseException("Missing problem delimiter", st, t, END_BLOCK.img)
              case None => // problem seems correctly ended
            }
            if (problemBlock.exists(_.tok == EXERCISE_PLACEHOLDER)) {
              ParseState(st.stack :+ Problem(Right(problemBlock :+ Token(EOF, endLoc)), annotations.toList) :+ Tactics(Nil), remainder)
            } else {
              val problem: Formula = parser.formulaTokenParser(problemBlock :+ Token(EOF, endLoc))
              ParseState(st.stack :+ Problem(Left(problem), annotations.toList) :+ Tactics(Nil), remainder)
            }
          } finally {
            parser.setAnnotationListener(annotationListener)
          }
        case IDENT(key, None) if MetaInfoKey.KEYS.contains(key) => reduce(shift(st), 1, Bottom :+ MetaInfoKey(key), r)
        case _ if !rest.exists(_.tok == PROBLEM_BLOCK) => throw ParseException("Missing problem block", st, nextTok, PROBLEM_BLOCK.img)
        case _ if  rest.exists(_.tok == PROBLEM_BLOCK) => throw ParseException("Misplaced problem block: problem expected before tactics", st, nextTok, PROBLEM_BLOCK.img)
      }

      // tactic
      case _ :+ Tactics(_) :+ Token(TACTIC_BLOCK, _) if la.isInstanceOf[DOUBLE_QUOTES_STRING] => shift(st)
      case r :+ (tactics@Tactics(_)) :+ (tacticBlock@Token(TACTIC_BLOCK, _)) if la == PERIOD =>
        reduce(shift(st), 1, Bottom :+ Token(DOUBLE_QUOTES_STRING("<undefined>"), currLoc), r :+ tactics :+ tacticBlock)
      case r :+ (tactics@Tactics(_)) :+ (tacticBlock@Token(TACTIC_BLOCK, _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) if la == PERIOD || la == SEMI =>
        reduce(shift(st), 1, Bottom, r :+ tactics :+ tacticBlock :+ name)
      case r :+ (tactics@Tactics(_)) :+ Token(TACTIC_BLOCK, blockLoc) :+ Token(DOUBLE_QUOTES_STRING(name), nameLoc) =>
        //@note slice and parse later with BelleParser (needs converted definitions)
        //@todo reimplement BelleLexer/BelleParser
        val (belleExprBlock, remainder) = input.span(_.tok != END_BLOCK)
        val blockEndLoc = remainder match {
          case Token(END_BLOCK, _) :: Token(PERIOD, endLoc) :: _ => endLoc
          case Token(END_BLOCK, endLoc) :: _ => endLoc
        }
        val tacticText = slice(text, nameLoc.end.spanTo(belleExprBlock.last.loc.end)).stripPrefix("\"").stripPrefix(".").trim
        ParseState(r :+ tactics :+ Tactic(name, tacticText, blockLoc.spanTo(blockEndLoc), currLoc), remainder)
      case r :+ (tactics@Tactics(_)) :+ (tactic@Tactic(_, _, _, _)) if la == END_BLOCK => shift(st)
      case r :+ (tactics@Tactics(_)) :+ (tactic@Tactic(_, _, _, _)) :+ Token(END_BLOCK, _) =>
        reduce(shift(st), 4, Bottom :+ Tactics(tactics.tactics :+ tactic), r)

      // small stack cases
      case Bottom :+ ArchiveEntries(t) =>
        if (la != EOF) shift(st)
        else accept(st, t)

      case Bottom :+ (e: ArchiveEntry) =>
        if (la != EOF) shift(st)
        else accept(st, e :: Nil)

      case Bottom :+ Token(SHARED_DEFINITIONS_BEGIN, _) :+ Definitions(defs, _) :+ (entries@ArchiveEntries(_)) =>
        if (la != EOF) shift(st)
        else {
          val inheritedEntries@ArchiveEntries(t) = entries.inheritDefs(defs)
          accept(reduce(st, 3, Bottom :+ inheritedEntries, Bottom), t)
        }

      case Bottom :+ Token(SHARED_DEFINITIONS_BEGIN, _) :+ Definitions(defs, _) :+ (e: ArchiveEntry) =>
        if (la != EOF) shift(st)
        else {
          val f = e.inheritDefs(defs)
          accept(reduce(st, 3, Bottom :+ f, Bottom), f :: Nil)
        }

      case Bottom :+ Token(SHARED_DEFINITIONS_BEGIN, _) :+ Definitions(_, _) if la.isInstanceOf[ARCHIVE_ENTRY_BEGIN] => shift(st)

      case Bottom => la match {
        case ARCHIVE_ENTRY_BEGIN(_) => shift(st)
        case SHARED_DEFINITIONS_BEGIN => shift(st)
        case DEFINITIONS_BLOCK | FUNCTIONS_BLOCK | PROGRAM_VARIABLES_BLOCK | PROBLEM_BLOCK =>
          rest.find({ case Token(ARCHIVE_ENTRY_BEGIN(_), _) => true case _ => false }) match {
            case Some(Token(ARCHIVE_ENTRY_BEGIN(kind), loc)) => throw ParseException("Archives that start with an anonymous entry may not contain any other entries, but found " + kind, loc)
            case None =>
              val (tokens, eof) = input.splitAt(input.size - 1)
              ParseState(
                Bottom :+ Token(ARCHIVE_ENTRY_BEGIN("ArchiveEntry"), UnknownLocation) :+ Token(DOUBLE_QUOTES_STRING("<undefined>"), UnknownLocation) :+ MetaInfo(Map.empty),
                (tokens :+ Token(END_BLOCK, UnknownLocation) :+ Token(PERIOD, UnknownLocation)) ++ eof)
          }
        case EOF => throw ParseException("Empty input is not a well-formed archive ", st, "ArchiveEntry|Theorem|Lemma|Exercise")
        case _ => throw ParseException("Unexpected archive start ", st, "ArchiveEntry|Theorem|Lemma|Exercise")
      }

      case _ => throw ParseException("Unexpected archive content", st)
    }
  }

  /** Shift to put the next input token la on the parser stack s. */
  private def shift(st: ParseState): ParseState = {
    val ParseState(s, (la :: rest)) = st
    require(la.tok != EOF, "Cannot shift past end of file")
    ParseState(s :+ la, rest)
  }

  /**
    * Reduce the parser stack by reducing the consuming many items from the stack to the reduced item.
    *
    * @param remainder Redundant parameter, merely for correctness checking.
    */
  private def reduce(st: ParseState, consuming: Int, reduced: Stack[Item], remainder: Stack[Item]): ParseState = {
    val ParseState(s, input) = st
    ParseState(s.drop(consuming) ++ reduced, input)
  } ensures(r => r.stack.drop(reduced.length) == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  /** Accept the given parser result. */
  private def accept(st: ParseState, result: List[ArchiveEntry]): ParseState = {
    val ParseState(s, input) = st
    require(input.length == 1 && input.head.tok == EOF, "Can only accept after all input has been read.\nRemaining input: " + input)
    require(s.length == 1, "Can only accept with one single result on the stack.\nRemaining stack: " + s)
    ParseState(Bottom :+ Accept(result), input)
  }

  /** Elaborates problem, annotations, and annotations in definitions in the `entry` according to the entry-specific
    * and inherited definitions listed in `entry`. */
  def elaborateEntry(entry: ArchiveEntry): ArchiveEntry = {
    val (definitions, elaboratables) = elaborateDefinitions(entry)

    entry.copy(
      inheritedDefinitions = Nil,
      definitions = definitions.map(elaborateWithDots),
      //@note replaces all literal occurrences of variable uses with functions and relies on earlier check
      //      that input does not mix variable and function use of the same symbol.
      problem = entry.problem match {
        case Left(problem) => Left(problem.elaborateToFunctions(elaboratables).asInstanceOf[Formula])
        case r => r
      },
      annotations = elaborateAnnotations(entry.annotations, elaboratables)
      //@note do not elaborate to function symbols etc. in tactics (postponed until tactic execution)
    )
  }

  /** Elaborates to functions in annotations.
    * @param annotations the annotations to elaborate
    * @param elaboratables lists functions to elaborate to
    * @throws ParseException if annotations are not formulas, not attached to programs, or type analysis of annotations fails
    * */
  private def elaborateAnnotations(annotations: List[Annotation], elaboratables: Set[NamedSymbol]): List[Annotation] = {
    annotations.map({
      case Annotation(e: Program, a: Formula) =>
        val substPrg = e.elaborateToFunctions(elaboratables)
        val substFml = a.elaborateToFunctions(elaboratables)
        Annotation(substPrg, substFml)
      case Annotation(_: Program, a) => throw ParseException("Annotation must be formula, but got " + a.prettyString, UnknownLocation)
      case Annotation(e, _) => throw ParseException("Annotation on programs only, but was on " + e.prettyString, UnknownLocation)
    })
  }

  /** Elaborates argument names in `d`'s interpretation with dots. */
  private def elaborateWithDots(d: Definition): Definition = d match {
    case FuncPredDef(name, index, sort, signature, Left(interpretation), loc) =>
      // backwards compatible dots
      val dotTerms =
        if (signature.size == 1) signature.map(v => v -> DotTerm(v.sort, None))
        else signature.zipWithIndex.map({ case (v, i) => v -> DotTerm(v.sort, Some(i)) })
      val dottedInterpretation = interpretation.map(d => dotTerms.foldRight(d)({ case ((v, dot), dotted) =>
        v match {
          case vv: Variable => dotted.replaceFree(vv, dot)
          case _ => dotted
        }
      }))
      FuncPredDef(name, index, sort, signature, Left(dottedInterpretation), loc)
    case _ => d // nothing to do in variables, programs etc.
  }

  def convert(entry: ArchiveEntry, text: String, parseTactics: Boolean): ParsedArchiveEntry = {
    //@todo report multiple duplicate symbols
    val duplicateDefs = entry.definitions.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateDefs.nonEmpty) throw ParseException("Duplicate symbol '" + duplicateDefs.head._1._1 + "'", duplicateDefs.head._2.last.loc)
    val duplicateVars = entry.vars.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateVars.nonEmpty) throw ParseException("Duplicate variable '" + duplicateVars.head._1._1 + "'", duplicateVars.head._2.last.loc)

    val duplicateInheritedDefs = entry.inheritedDefinitions.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateInheritedDefs.nonEmpty) throw ParseException("Duplicate symbol '" + duplicateInheritedDefs.head._1._1 + "'", duplicateInheritedDefs.head._2.last.loc)

    val illegalOverride = entry.definitions.filter(e => entry.inheritedDefinitions.exists(_.name == e.name))
    if (illegalOverride.nonEmpty) throw ParseException("Symbol '" + illegalOverride.head.name + "' overrides inherited definition; must declare override", illegalOverride.head.loc)

    val definitions = entry.allDefs.map(convert).reduceOption(_++_).getOrElse(Declaration(Map.empty))

    val annotations = entry.annotations ++ (entry.definitions ++ entry.inheritedDefinitions).flatMap(extractAnnotations)

    val (problemText, entryText) = createStandaloneEntryText(entry, text)

    entry.problem match {
      case Left(problem) =>
        // check whether constants are bound anywhere (quantifiers, program/system consts etc.)
        val fullyExpanded = try {
          definitions.expandFull(problem)
        } catch {
          case ex: AssertionError => throw ParseException(ex.getMessage, ex)
        }
        ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
            case v: Variable if definitions.decls.exists({ case (Name(n, i), Signature(d, s, _, _, _)) => d.isDefined && v.name == n && v.index == i && v.sort == s }) =>
              val bv = StaticSemanticsTools.boundAt(fullyExpanded, p)
              if (bv.contains(v)) {
                // isInfinite case should never occur because expandFull elaborates first;
                // but just in case: bound in a programconst, hint that [a;]x>=0 can be fixed with [a;]x()>=0
                if (bv.isInfinite) throw ParseException(
                  "Symbol " + v.prettyString + " occurs in variable syntax but is declared constant; please use " +
                    v.prettyString + "() explicitly.", UnknownLocation)
                // otherwise it's explicitly bound either in quantifier or program, encourage to rename
                else throw ParseException(
                  "Symbol " + v.prettyString + " is bound but is declared constant; please use a different name in the quantifier/program binding " +
                    v.prettyString, UnknownLocation)
              }
              else Left(None)
            case _ => Left(None)
          }
        }, fullyExpanded)

        val tactics =
          if (parseTactics) {
            //@note tactics hard to elaborate later (expandAllDefs must use elaborated symbols to not have substitution clashes)
            val elaboratedDefinitions = elaborateDefinitions(entry)._1.map(convert).reduceOption(_++_).getOrElse(Declaration(Map.empty))
            entry.tactics.map(convert(_, elaboratedDefinitions))
          } else entry.tactics.map(t => (t.name, t.tacticText, convert(Tactic("nil", "nil", UnknownLocation, UnknownLocation), Declaration(Map.empty))._3))

        val entryKinds = Map("ArchiveEntry"->"theorem", "Theorem"->"theorem", "Lemma"->"lemma", "Exercise"->"exercise")

        // double-check that the extracted problem text still parses
        val tokens = KeYmaeraXLexer.inMode(problemText, ProblemFileMode)
        val reparse = try {
          parseLoop(ParseState(Bottom, tokens), text).stack
        } catch {
          case _: ParseException => throw ParseException("Even though archive parses, extracted problem does not parse (try reformatting):\n" + problemText, UnknownLocation)
        }
        reparse match {
          case Bottom :+ Accept(entries) if entries.size == 1 =>
            if (entries.head.problem != entry.problem) throw ParseException("Even though archive parses, extracted problem does not match archive entry:\n" + problemText, UnknownLocation)
          case Bottom :+ Accept(entries) if entries.size != 1 => throw ParseException("Even though archive parses, extracted problem artifact results in unexpected number of problems (expected 1 but got " + entries.size + "): \n" + entries.mkString("\n"), UnknownLocation)
          case _ :+ Error(msg, loc, st) => throw ParseException("Even though archive parses, extracted problem artifact does not parse: " + msg, loc, "<unknown>", "<unknown>", "", st)
          case _ => throw new AssertionError("Even though archive parses, extracted problem artifact does not parse: Parser terminated with unexpected stack")
        }

        ParsedArchiveEntry(entry.name, entryKinds(entry.kind), entryText.trim(), problemText.trim(), definitions, problem, tactics, annotations.map(convert), entry.info)
      case Right(_) =>
        ParsedArchiveEntry(entry.name, "exercise", entryText.trim(), problemText.trim(), definitions, False, Nil, annotations.map(convert), entry.info)
    }
  }

  /** Merges definitions explicitly mentioned in `entry.definitions` and those inherited from other entries
    * listed in `entry.inheritedDefinitions` into function-elaborated definitions.
    * @param entry The entry information collected in the parse step.
    * @return The elaborated definitions and the symbols that can be elaborated to.
    * @throws ParseException if duplicate definitions or illegal overrides are detected.
    */
  private def elaborateDefinitions(entry: ArchiveEntry): (List[Definition], Set[NamedSymbol]) = {
    //@todo report multiple duplicate symbols
    val duplicateDefs = entry.definitions.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateDefs.nonEmpty) throw ParseException("Duplicate symbol '" + duplicateDefs.head._1._1 + "'", duplicateDefs.head._2.last.loc)
    val duplicateVars = entry.vars.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateVars.nonEmpty) throw ParseException("Duplicate variable '" + duplicateVars.head._1._1 + "'", duplicateVars.head._2.last.loc)

    val duplicateInheritedDefs = entry.inheritedDefinitions.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateInheritedDefs.nonEmpty) throw ParseException("Duplicate symbol '" + duplicateInheritedDefs.head._1._1 + "'", duplicateInheritedDefs.head._2.last.loc)

    val illegalOverride = entry.definitions.filter(e => entry.inheritedDefinitions.exists(_.name == e.name))
    if (illegalOverride.nonEmpty) throw ParseException("Symbol '" + illegalOverride.head.name + "' overrides inherited definition; must declare override", illegalOverride.head.loc)

    val elaboratables: Set[NamedSymbol] = entry.allDefs.flatMap({
      case FuncPredDef(name, index, sort, Nil, Left(None), _) => Some(Function(name, index, Unit, sort))
      case _ => None
    }).toSet
    val elaboratedDefinitions = entry.allDefs.map({
      case f@FuncPredDef(_, _, _, signature, Left(interpretation), _) => f.copy(
        definition = Left(interpretation.map(_.elaborateToFunctions(
          elaboratables.filter(e => !signature.exists(s => e.name == s.name && e.index == s.index))))))
      case p@ProgramDef(_, _, Left(interpretation), annotations, _) => p.copy(
        definition = Left(interpretation.map(_.elaborateToFunctions(elaboratables).asInstanceOf[Program])),
        annotations = elaborateAnnotations(annotations, elaboratables)
      )
      case d => d
    })

    (elaboratedDefinitions, elaboratables)
  }

  private def createStandaloneEntryText(entry: ArchiveEntry, text: String): (String, String) = {
    val usedSharedDefs = entry.inheritedDefinitions.filter(entry.allDefs.contains)
    val sharedDefsText = if (usedSharedDefs.nonEmpty) {
      "SharedDefinitions\n" +
        usedSharedDefs.map(d => "  " + slice(text, d.loc)).mkString("\n") +
        "\nEnd.\n"
    } else ""

    val entryText = sharedDefsText + (if (entry.loc.begin.line > 0) slice(text, entry.loc) else text)
    val problemText = sharedDefsText + (
      if (entry.loc.begin.line > 0) {
        val tacticStripped = slice(text, entry.loc, entry.tactics.map(_.blockLoc)).trim()
        if (tacticStripped.trim().endsWith("End.")) {
          tacticStripped.trim().stripSuffix("End.").trim() + "\nEnd."
        } else tacticStripped
      } else text)
    (problemText, entryText)
  }

  private def convert(d: Definition): Declaration = d match {
    case FuncPredDef(name, index, sort, signature, Left(definition), loc) =>
      Declaration(Map(Name(name, index) -> Signature(Some(toSort(signature)), sort, Some(signature.map(s => (Name(s.name, s.index), s.sort))), definition, loc)))
    case FuncPredDef(name, index, sort, signature, Right(_), loc) =>
      Declaration(Map(Name(name, index) -> Signature(Some(toSort(signature)), sort, Some(signature.map(s => (Name(s.name, s.index), s.sort))), None, loc)))
    case ProgramDef(name, index, Left(definition), _, loc) =>
      Declaration(Map(Name(name, index) -> Signature(Some(Unit), Trafo, None, definition, loc)))
    case ProgramDef(name, index, Right(_), _, loc) =>
      Declaration(Map(Name(name, index) -> Signature(Some(Unit), Trafo, None, None, loc)))
    case VarDef(name, index, loc) =>
      Declaration(Map(Name(name, index) -> Signature(None, Real, None, None, loc)))
  }

  private def extractAnnotations(d: Definition): List[Annotation] = d match {
    case ProgramDef(_, _, _, annotations, _) => annotations
    case _: FuncPredDef => Nil
    case _: VarDef => Nil
  }

  private def toSort(signature: List[NamedSymbol]): Sort = {
    if (signature.isEmpty) Unit
    else signature.tail.foldRight[Sort](signature.head.sort)({ case (v, s) => Tuple(v.sort, s) })
  }

  private def convert(a: Annotation): (Expression, Expression) = (a.element, a.annotation)

  protected def convert(t: Tactic, defs: Declaration): (String, String, BelleExpr)

  private def slice(text: String, loc: Location): String = {
    val lines = (text: StringOps).lines.slice(loc.begin.line - 1, loc.end.line).toList
    if (loc.end.line > loc.begin.line) {
      val header = lines.head.drop(loc.begin.column - 1)
      val footer = lines.last.take(loc.end.column)
      (header +: lines.tail.dropRight(1) :+ footer).mkString("\n")
    } else {
      val result = lines.head.take(loc.end.column)
      result.drop(loc.begin.column - 1)
    }
  }

  @tailrec
  private def slice(text: String, loc: Location, except: List[Location]): String = {
    if (except.isEmpty) slice(text, loc)
    else slice(
      slice(text, Region(1, 1, 1, 1).spanTo(except.last.begin)).dropRight(1) + slice(text, except.last.end.spanTo(loc.end)).drop(1),
      loc, except.dropRight(1))
  }

  /** Parses definition tokens `defTokens` with `parser` (using `text` to produce error messages). Returns the parsed
    * expression, the end location of the definition, and the remainder tokens after the definition. */
  private def parseDefinition[T <: Expression](defTokens: List[Token], text: String, parser: List[Token] => T): (Either[Option[T], List[Token]], Location, List[Token]) = {
    val (defBlock: List[Token], remainder: List[Token]) = sliceDefinition(defTokens, parser)
    val resultExpression = try {
      if (!defBlock.exists(_.tok == EXERCISE_PLACEHOLDER)) {
        Left(Some(parser(defBlock :+ Token(EOF, remainder.head.loc))))
      } else {
        Right(defBlock :+ Token(EOF, remainder.head.loc))
      }
    } catch {
      case ex: ParseException =>
        val (loc, found) = ex.loc match {
          case UnknownLocation =>
            val defLoc = defBlock.head.loc.spanTo(defBlock.last.loc.end)
            (defLoc, slice(text, defLoc))
          case _ if ex.found != EOF.description => (ex.loc, ex.found)
          case _ if ex.found == EOF.description => (ex.loc, remainder.head.description)
        }
        throw new ParseException(ex.msg, loc, found, ex.expect, ex.after, ex.state, ex)
    }
    (resultExpression, defBlock.last.loc.end, remainder)
  }

  /** Runs `parser` on `rest` to find the longest parseable expression, with fallback for exercises enclosed in () or ending in a single ;.
    * Returns the tokens of the longest parseable expression and the remaining tokens after that. */
  private def sliceDefinition[T <: Expression](rest: List[Token], parser: List[Token] => T): (List[Token], List[Token]) = {
    try {
      parser(rest)
      throw ParseException("Missing ';' at definition end", rest.last.loc, rest.last.tok.img, SEMI.img)
    } catch {
      case ex: ParseException => rest.find({
        case Token(_, tl) => tl == ex.loc
      }) match {
        case Some(errorToken) =>
          val (parsedOk: List[Token], remainder: List[Token]) = rest.splitAt(rest.indexOf(errorToken))
          if (errorToken.tok == EXERCISE_PLACEHOLDER) {
            // exercise must be either enclosed in () or contain exactly 1 ; (at the very end)
            if (rest.head.tok == LPAREN) {
              var openParens = 0
              val (Token(LPAREN, _) :: funcDefBlock, defEnd) = rest.span(t => { if (t.tok == LPAREN) openParens += 1 else if (t.tok == RPAREN) openParens -= 1; openParens > 0})
              if (defEnd.isEmpty) throw ParseException.imbalancedError("Unmatched opening parenthesis in function definition", rest.head, RPAREN.img, ParseState(Bottom :+ rest.head, rest.tail))
              val (rparen@Token(RPAREN, _)) :: remainder = defEnd
              (funcDefBlock, remainder)
            } else {
              val (funcDefBlock, remainder) = rest.span(_.tok != SEMI)
              (funcDefBlock, remainder)
            }
          } else if (errorToken.tok == SEMI || errorToken.tok == PERIOD) {
            (parsedOk, remainder)
          } else {
            val lastSemiIdx = parsedOk.lastIndexWhere(t => t.tok == SEMI || t.tok == PERIOD)
            if (lastSemiIdx >= 0) {
              val (funcDefBlock, nextDefStart) = parsedOk.splitAt(lastSemiIdx)
              (funcDefBlock, nextDefStart ++ remainder)
            } else throw ex.copy(msg = "Unexpected token in definition", expect = ex.expect.replaceAllLiterally("<EOF>", SEMI.img))
          }
        case None => throw ex
      }
    }
  }

}
