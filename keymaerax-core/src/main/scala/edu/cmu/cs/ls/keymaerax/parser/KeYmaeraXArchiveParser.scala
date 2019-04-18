/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import java.io.InputStream

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, DefExpression, DefTactic, PosInExpr}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser.{BelleToken, DefScope}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleLexer, BelleParser}
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.{ExpressionTraversal, Idioms, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.ParseState

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

/**
  * Splits a KeYmaera X archive into its parts and forwards to respective problem/tactic parsers. An archive contains
  * at least one entry combining a model in the .kyx format and a (partial) proof tactic in .kyt format.
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
  */
object KeYmaeraXArchiveParser {
  /** The entry name, kyx file content (model), definitions, parsed model, and parsed named tactics. */
  case class ParsedArchiveEntry(name: String, kind: String, fileContent: String, problemContent: String,
                                defs: Declaration,
                                model: Expression, tactics: List[(String, String, BelleExpr)],
                                info: Map[String, String])

  /** Name is alphanumeric name and index. */
  type Name = (String, Option[Int])
  /** Signature is a domain sort, codomain sort, expression used as "interpretation", location that starts the declaration. */
  type Signature = (Option[Sort], Sort, Option[Expression], Location)
  /** A parsed declaration, which assigns a signature to names */
  case class Declaration(decls: Map[Name, Signature]) {
    /** The declarations as substitution pair. */
    lazy val substs: List[SubstitutionPair] = decls.filter(_._2._3.isDefined).
      map((declAsSubstitutionPair _).tupled).toList

    /** Declared names and signatures as functions. */
    lazy val asFunctions: List[Function] = decls.map({ case ((name, idx), (domain, codomain, _, _)) =>
      Function(name, idx, domain.getOrElse(Unit), codomain) }).toList

    /** Applies substitutions per `substs` exhaustively to expression-like `arg`. */
    def exhaustiveSubst[T <: Expression](arg: T): T = elaborateToFunctions(arg) match {
      case e: Expression =>
        def exhaustiveSubst(f: Expression): Expression = {
          val fs = try {
            USubst(substs)(f)
          } catch {
            case ex: SubstitutionClashException =>
              throw ParseException("Definition " + ex.e + " must declare arguments " + ex.clashes, ex)
          }
          if (fs != f) exhaustiveSubst(fs) else fs
        }
        exhaustiveSubst(e).asInstanceOf[T]
      case e => e
    }

    /** Joins two declarations. */
    def ++(other: Declaration): Declaration = Declaration(decls ++ other.decls)

    /** Finds the definition with `name` and index `idx`. */
    def find(name: String, idx: Option[Int] = None): Option[Signature] = decls.get(name -> idx)

    /** Turns a function declaration (with defined body) into a substitution pair. */
    private def declAsSubstitutionPair(name: Name, signature: Signature): SubstitutionPair = {
      assert(signature._3.isDefined, "Substitution only for defined functions")

      /** Converts sort `s` into nested pairs of DotTerms. Returns the nested dots and the next unused dot index. */
      def toDots(s: Sort, idx: Int): (Term, Int) = s match {
        case Real => (DotTerm(s, Some(idx)), idx+1)
        case Tuple(l, r) =>
          val (lDots, lNextIdx) = toDots(l, idx)
          val (rDots, rNextIdx) = toDots(r, lNextIdx)
          (Pair(lDots, rDots), rNextIdx)
      }

      /** Returns the dots used in expression `e`. */
      def dotsOf(e: Expression): Set[DotTerm] = {
        val dots = scala.collection.mutable.Set[DotTerm]()
        val traverseFn = new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, t: Term): Either[Option[StopTraversal], Term] = t match {
            case d: DotTerm => dots += d; Left(None)
            case _ => Left(None)
          }
        }
        e match {
          case t: Term => ExpressionTraversal.traverse(traverseFn, t)
          case f: Formula => ExpressionTraversal.traverse(traverseFn, f)
          case p: Program => ExpressionTraversal.traverse(traverseFn, p)
        }
        dots.toSet
      }

      val (arg, sig) = signature._1 match {
        case Some(Unit) => (Nothing, Unit)
        case Some(s@Tuple(_, _)) => (toDots(s, 0)._1, s)
        case Some(s) => (DotTerm(s), s)
        case None => (Nothing, Unit)
      }
      val what = signature._2 match {
        case Real => FuncOf(Function(name._1, name._2, sig, signature._2), arg)
        case Bool => PredOf(Function(name._1, name._2, sig, signature._2), arg)
        case Trafo =>
          assert(name._2.isEmpty, "Expected no index in program const name, but got " + name._2)
          assert(signature._1.getOrElse(Unit) == Unit, "Expected domain Unit in program const signature, but got " + signature._1)
          ProgramConst(name._1)
      }
      val repl = elaborateToFunctions(signature._3.get)

      val undeclaredDots = dotsOf(repl) -- dotsOf(arg)
      if (undeclaredDots.nonEmpty) throw ParseException(
        "Function/predicate " + what.prettyString + " defined using undeclared " + undeclaredDots.map(_.prettyString).mkString(","),
        UnknownLocation)

      SubstitutionPair(what, repl)
    }

    /** Elaborates variable uses of declared functions. */
    private def elaborateToFunctions[T <: Expression](expr: T): T = {
      val freeVars = StaticSemantics.freeVars(expr)
      if (freeVars.isInfinite) {
        //@note program constant occurs
        expr
      } else {
        val elaboratables = StaticSemantics.freeVars(expr).toSet[Variable].filter({
          case BaseVariable(name, i, _) => decls.contains((name, i)) && decls((name, i))._1.contains(Unit)
          case _ => false
        })
        elaboratables.foldLeft(expr)((e, v) =>
          SubstitutionHelper.replaceFree(e)(v, FuncOf(Function(v.name, v.index, Unit, v.sort), Nothing)))
      }
    }
  }

  /** Returns all the quantified variables in an expression. Used in [[typeAnalysis()]] */
  private def quantifiedVars(expr : Expression) = {
    val quantifiedVariables : scala.collection.mutable.Set[NamedSymbol] = scala.collection.mutable.Set()

    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = {
        //Add all quantified variables to the quantifiedVariables set.
        e match {
          case Forall(xs, _) => xs.foreach(v => quantifiedVariables += v)
          case Exists(xs, _) => xs.foreach(v => quantifiedVariables += v)
          case _ =>
        }
        Left(None)
      }
    }, expr.asInstanceOf[Formula])

    quantifiedVariables
  }

  /**
    * Type analysis of expression according to the given type declarations decls
    * @param name the entry name
    * @param d the type declarations known from the context
    * @param expr the expression parsed
    * @throws [[edu.cmu.cs.ls.keymaerax.parser.ParseException]] if the type analysis fails.
    */
  def typeAnalysis(name: String, d: Declaration, expr: Expression): Boolean = {
    StaticSemantics.symbols(expr).forall({
      case f: Function =>
        val (declaredDomain, declaredSort, _, loc: Location) = d.decls.get((f.name,f.index)) match {
          case Some(decl) => decl
          case None => throw ParseException.typeError(name + ": undefined function symbol", f, f.sort + "", UnknownLocation,
            "Make sure to declare all variables in ProgramVariable and all symbols in Definitions block.")
        }
        if (f.sort != declaredSort) throw ParseException.typeDeclError(s"$name: ${f.prettyString} declared with sort $declaredSort but used where sort ${f.sort} was expected.", declaredSort + " function", f.sort + "", loc)
        else if (!declaredDomain.contains(f.domain)) {
          (f.domain, declaredDomain) match {
            case (_, Some(r)) => throw ParseException.typeDeclError(s"$name: ${f.prettyString} declared with domain $r but used where domain ${f.domain} was expected.", r + "", f.domain + "", loc)
            case (_, None) => throw ParseException.typeDeclError(s"$name: ${f.prettyString} declared as a variable of sort ${f.sort} but used as a function with arguments.", "no arguments", "function with arguments", loc)
            //The other cases can't happen -- we know f is a function so we know it has a domain.
          }
        }
        else true
      case DifferentialSymbol(v) => d.decls.contains(v.name, v.index) //@note hence it is checked as variable already
      case x: Variable if quantifiedVars(expr).contains(x) => true //Allow all undeclared variables if they are at some point bound by a \forall or \exists. @todo this is an approximation. Should only allow quantifier bindings...
      case x: Variable =>
        val (declaredSort, declLoc) = d.decls.get((x.name,x.index)) match {
          case Some((None,sort, _, loc)) => (sort, loc)
          case Some((Some(domain), sort, _, loc)) => throw ParseException.typeDeclError(s"$name: ${x.name} was declared as a function but must be a variable when it is assigned to or has a differential equation.", domain + "->" + sort + " Function", "Variable of sort Real", loc)
          case None => throw ParseException.typeDeclGuessError(name +": undefined symbol " + x + " with index " + x.index, "undefined symbol", x, UnknownLocation,
            "Make sure to declare all variables in ProgramVariable and all symbols in Definitions block.")
        }
        if (x.sort != declaredSort) throw ParseException.typeDeclGuessError(s"$name: ${x.prettyString} declared with sort $declaredSort but used where a ${x.sort} was expected.", declaredSort + "", x, declLoc)
        x.sort == declaredSort
      case _: UnitPredicational => true //@note needs not be declared
      case _: UnitFunctional => true //@note needs not be declared
      case _: DotTerm => true //@note needs not be declared
      case _ => false
    })
  }

  private[parser] trait ArchiveItem extends OtherItem

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
  }
  private[parser] case class ArchiveEntries(entries: List[ArchiveEntry]) extends ArchiveItem {
    def inheritDefs(defs: List[Definition]): ArchiveEntries = ArchiveEntries(entries.map(_.inheritDefs(defs)))
  }

  private[parser] abstract class Definition(val name: String, val index: Option[Int],
                                            val definition: Either[Option[Expression], List[Token]],
                                            val loc: Location) extends ArchiveItem {
    def extendLocation(end: Location): Definition
  }
  private[parser] case class FuncPredDef(override val name: String, override val index: Option[Int], sort: Sort,
                                         signature: List[NamedSymbol],
                                         override val definition: Either[Option[Expression], List[Token]],
                                         override val loc: Location) extends Definition(name, index, definition, loc) {
    override def extendLocation(end: Location): Definition = FuncPredDef(name, index, sort, signature, definition, loc.spanTo(end))
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
    val KEYS: List[String] = "Link" :: "Citation" :: "Title" :: "Description" :: "Author" :: "See" :: Nil
  }

  private[parser] object BuiltinDefinitions {
    val defs: Declaration =
      (FuncPredDef("abs", None, Real, DotTerm(Real, None) :: Nil, Left(None), UnknownLocation) ::
       FuncPredDef("min", None, Real, DotTerm(Real, Some(0)) :: DotTerm(Real, Some(1)) :: Nil, Left(None), UnknownLocation) ::
       FuncPredDef("max", None, Real, DotTerm(Real, Some(0)) :: DotTerm(Real, Some(1)) :: Nil, Left(None), UnknownLocation) ::
       Nil).map(convert).reduce(_++_)
  }

  private[parser] object BuiltinAnnotationDefinitions {
    val defs: Declaration =
      (FuncPredDef("old", None, Real, DotTerm(Real, None) :: Nil, Left(None), UnknownLocation) ::
       Nil).map(convert).reduce(_++_)
  }

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  def apply(input: String): List[ParsedArchiveEntry] = parse(input)
  /** Parse the input string in the concrete syntax as a differential dynamic logic expression.
    * Skips parsing tactics if `parseTactics` is false. Requires KeYmaeraXPrettyPrinter setup if `parseTactics` is true. */
  def parse(input: String, parseTactics: Boolean = true): List[ParsedArchiveEntry] = {
    val stripped = ParserHelper.removeBOM(input).replaceAllLiterally("\t","  ")
    val tokenStream = KeYmaeraXLexer.inMode(stripped, ProblemFileMode)
    try {
      parse(tokenStream, stripped, parseTactics)
    } catch {
      case e: ParseException if e.msg.startsWith("Unexpected archive start") =>
        // cannot parse as archive, try parse plain formula
        try {
          val fml = KeYmaeraXParser(input).asInstanceOf[Formula]
          ParsedArchiveEntry("<undefined>", "theorem", stripped, stripped, declarationsOf(fml), fml, Nil, Map.empty) :: Nil
        } catch {
          // cannot parse as plain formula either, throw original exception
          case _: Throwable => throw e.inInput(stripped, Some(tokenStream))
        }
      case e: ParseException => throw e.inInput(stripped, Some(tokenStream))
    }
  }

  /** Tries parsing as a problem first. If it fails due to a missing Problem block, tries parsing as a plain formula. */
  def parseAsProblemOrFormula(input: String): Formula = parseProblem(input, parseTactics=false).model.asInstanceOf[Formula]
  def parseAsProblemOrFormula(in: InputStream): Formula = parseAsProblemOrFormula(io.Source.fromInputStream(in).mkString)

  /** Parses a single entry. */
  def parseProblem(input: String, parseTactics: Boolean = true): ParsedArchiveEntry = {
    val entries = parse(input, parseTactics)
    if (entries.size == 1) entries.head
    else throw ParseException("Expected a single entry, but got " + entries.size, UnknownLocation)
  }

  /** Parses an archive from the source at path `file`. Use file#entry to refer to a specific entry in the file. */
  def parseFromFile(file: String): List[ParsedArchiveEntry] = {
    file.split('#').toList match {
      case fileName :: Nil =>
        val input = scala.io.Source.fromFile(fileName).mkString
        KeYmaeraXArchiveParser.parse(input)
      case fileName :: entryName :: Nil =>
        val input = scala.io.Source.fromFile(fileName).mkString
        KeYmaeraXArchiveParser.getEntry(entryName, input).
          getOrElse(throw new IllegalArgumentException("Unknown archive entry " + entryName)) :: Nil
    }
  }

  /** Reads a specific entry from the archive. */
  def getEntry(name: String, content: String): Option[ParsedArchiveEntry] = parse(content).find(_.name == name)

  /** Indicates whether or not the model represents an exercise. */
  def isExercise(model: String): Boolean = model.contains("__________")

  /** Lexer's token stream with first token at head. */
  type TokenStream = List[Token]

  /** Parses the input token stream (lexed from `text`); skips tactic parsing if parseTactics is false. */
  private[parser] def parse(input: TokenStream, text: String, parseTactics: Boolean): List[ParsedArchiveEntry] = {
    require(input.last.tok == EOF, "token streams have to end in " + EOF)
    require(!text.contains('\t'), "Tabs in input not supported, please replace with spaces")

    parseLoop(ParseState(Bottom, input), text).stack match {
      case Bottom :+ Accept(entries) => entries.map(convert(_, text, parseTactics))
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
      case r :+ (tok@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+
          Definitions(_, _) :+ Problem(_, _) :+ Tactics(_) => la match {
        case END_BLOCK => shift(st)
        case TACTIC_BLOCK => shift(st)
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

      // metainfo
      case r :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ MetaInfoKey(_) => la match {
        case DOUBLE_QUOTES_STRING(_) => shift(st)
        case _ => throw ParseException("Invalid meta info value", st, Expected.ExpectTerminal(DOUBLE_QUOTES_STRING("")) :: Nil)
      }
      case r :+ (entry@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) :+ MetaInfo(info) :+ MetaInfoKey(infoKey) :+ Token(DOUBLE_QUOTES_STRING(infoValue), _) => la match {
        case PERIOD | SEMI => reduce(shift(st), 4, Bottom :+ MetaInfo(info ++ Map(infoKey -> infoValue)), r :+ entry :+ name)
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
        case _ if isReal(la) || isBool(la) || isProgram(la) => shift(st)
        case _ => throw ParseException("Unexpected definition", st, 
          Expected.ExpectTerminal(END_BLOCK) :: 
          Expected.ExpectTerminal(IDENT("Real")) ::
          Expected.ExpectTerminal(IDENT("Bool")) ::
          Expected.ExpectTerminal(IDENT("HP")) :: Nil)
      }
      case r :+ (defs: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ Token(END_BLOCK, _) => la match {
        case PERIOD => reduce(shift(st), 3, Bottom, r :+ defs)
        case _ => throw ParseException("Missing definitions delimiter", st, Expected.ExpectTerminal(PERIOD) :: Nil)
      }
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ Token(sort, _) if (isReal(sort) || isBool(sort) || isProgram(sort)) && la.isInstanceOf[IDENT] => shift(st)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isReal(sort) =>
        reduce(st, 2, Bottom :+ FuncPredDef(name, index, Real, Nil, Left(None), startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isBool(sort) =>
        reduce(st, 2, Bottom :+ FuncPredDef(name, index, Bool, Nil, Left(None), startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isProgram(sort) =>
        reduce(st, 2, Bottom :+ ProgramDef(name, index, Left(None), Nil, startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)

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
          val (predDefBlock, endDef, remainder, endLoc) =
            if (rest.head.tok == LPAREN) {
              var openParens = 0
              val (Token(LPAREN, _) :: predDefBlock, defEnd) = rest.span(t => { if (t.tok == LPAREN) openParens += 1 else if (t.tok == RPAREN) openParens -= 1; openParens > 0})
              if (defEnd.isEmpty) throw ParseException.imbalancedError("Unmatched opening parenthesis in predicate definition", rest.head, RPAREN.img, ParseState(Bottom :+ rest.head, rest.tail))
              val (rparen@Token(RPAREN, endLoc)) :: remainder = defEnd
              (predDefBlock, rparen, remainder, endLoc.end)
            } else {
              val (predDefBlock, remainder) = rest.span(_.tok != SEMI)
              (predDefBlock, remainder.head, remainder, predDefBlock.last.loc.end)
            }
          val pred: Either[Option[Formula], List[Token]] = try {
            if (!predDefBlock.exists(_.tok == EXERCISE_PLACEHOLDER)) {
              Left(Some(KeYmaeraXParser.formulaTokenParser(predDefBlock :+ Token(EOF, remainder.head.loc))))
            } else {
              Right(predDefBlock :+ Token(EOF, remainder.head.loc))
            }
          } catch {
            case ex: ParseException =>
              val (loc, found) = ex.loc match {
                case UnknownLocation =>
                  val defLoc = predDefBlock.head.loc.spanTo(endLoc)
                  (defLoc, slice(text, defLoc))
                case _ if ex.found != EOF.description => (ex.loc, ex.found)
                case _ if ex.found == EOF.description => (ex.loc, endDef.description)
              }
              throw new ParseException(ex.msg, loc, found, ex.expect, ex.after, ex.state, ex)
          }
          ParseState(r :+ defs :+ defsBlock :+ FuncPredDef(next.name, next.index, next.sort, next.signature, pred, next.loc.spanTo(endLoc)), remainder)
        case SEMI | PERIOD => shift(st)
        case EQ => throw ParseException("Predicate must be defined by equivalence", st, nextTok, EQUIV.img)
        case _ => throw ParseException("Unexpected token in predicate definition", st, nextTok, EQUIV.img)
      }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) if next.sort == Real => la match {
        case EQ =>
          val (funcDefBlock, endDef, remainder, endLoc) =
            if (rest.head.tok == LPAREN) {
              var openParens = 0
              val (Token(LPAREN, _) :: funcDefBlock, defEnd) = rest.span(t => { if (t.tok == LPAREN) openParens += 1 else if (t.tok == RPAREN) openParens -= 1; openParens > 0})
              if (defEnd.isEmpty) throw ParseException.imbalancedError("Unmatched opening parenthesis in function definition", rest.head, RPAREN.img, ParseState(Bottom :+ rest.head, rest.tail))
              val (rparen@Token(RPAREN, endLoc)) :: remainder = defEnd
              (funcDefBlock, rparen, remainder, endLoc.end)
            } else {
              val (funcDefBlock, remainder) = rest.span(_.tok != SEMI)
              (funcDefBlock, remainder.head, remainder, funcDefBlock.last.loc.end)
            }
          val term: Either[Option[Term], List[Token]] = try {
            if (!funcDefBlock.exists(_.tok == EXERCISE_PLACEHOLDER)) {
              Left(Some(KeYmaeraXParser.termTokenParser(funcDefBlock :+ Token(EOF, remainder.head.loc))))
            } else {
              Right(funcDefBlock :+ Token(EOF, remainder.head.loc))
            }
          } catch {
            case ex: ParseException =>
              val (loc, found) = ex.loc match {
                case UnknownLocation =>
                  val defLoc = funcDefBlock.head.loc.spanTo(endLoc)
                  (defLoc, slice(text, defLoc))
                case _ if ex.found != EOF.description => (ex.loc, ex.found)
                case _ if ex.found == EOF.description => (ex.loc, endDef.description)
              }
              throw new ParseException(ex.msg, loc, found, ex.expect, ex.after, ex.state, ex)
          }
          ParseState(r :+ defs :+ defsBlock :+ FuncPredDef(next.name, next.index, next.sort, next.signature, term, next.loc.spanTo(endLoc)), remainder)
        case SEMI | PERIOD => shift(st)
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
                Left(Some(KeYmaeraXParser.programTokenParser(prgDefBlock :+ Token(EOF, endLoc))))
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
      case r :+ (defs: Definitions) :+ (varsBlock@Token(PROGRAM_VARIABLES_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), _) if isReal(sort) => la match {
        case SEMI | PERIOD =>
          reduce(shift(st), 5, Bottom :+ Definitions(defs.defs, defs.vars :+ VarDef(name, index, startLoc)) :+ varsBlock, r)
        case COMMA if isReal(rest.head.tok) => throw ParseException("Unexpected declaration delimiter", st, Expected.ExpectTerminal(SEMI) :: Nil)
        case COMMA =>
          reduce(shift(st), 5, Bottom :+ Definitions(defs.defs, defs.vars :+ VarDef(name, index, startLoc)) :+ varsBlock :+ Token(sort, startLoc), r)
        case LPAREN => throw ParseException("Function definition only allowed in Definitions block", st, Expected.ExpectTerminal(SEMI) :: Expected.ExpectTerminal(COMMA) :: Nil)
        case _ if isReal(la) || isBool(la) || isProgram(la) =>
          throw ParseException("Missing variable declaration delimiter", st, Expected.ExpectTerminal(SEMI) :: Nil)
        case _ => throw ParseException("Unexpected token in ProgramVariables block", st, Expected.ExpectTerminal(SEMI) :: Expected.ExpectTerminal(COMMA) :: Nil)
      }
      case r :+ (defs: Definitions) :+ (varsBlock@Token(PROGRAM_VARIABLES_BLOCK, _)) :+ (real@Token(sort, startLoc)) :+ Token(IDENT(name, index), _) if isReal(sort) && la == COMMA =>
        reduce(shift(st), 2, Bottom :+ Definitions(defs.defs, defs.vars :+ VarDef(name, index, startLoc)) :+ varsBlock :+ real, r)

      // problem
      case _ :+ Token(ARCHIVE_ENTRY_BEGIN(_), _) :+ Token(DOUBLE_QUOTES_STRING(_), _) :+ MetaInfo(_) :+ Definitions(_, _) => la match {
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
  } ensuring(r => r.stack.drop(reduced.length) == remainder, "Expected remainder stack after consuming the indicated number of stack items.")

  /** Accept the given parser result. */
  private def accept(st: ParseState, result: List[ArchiveEntry]): ParseState = {
    val ParseState(s, input) = st
    require(input.length == 1 && input.head.tok == EOF, "Can only accept after all input has been read.\nRemaining input: " + input)
    require(s.length == 1, "Can only accept with one single result on the stack.\nRemaining stack: " + s)
    ParseState(Bottom :+ Accept(result), input)
  }

  /** Postprocesses parse results. */
  private def convert(entry: ArchiveEntry, text: String, parseTactics: Boolean): ParsedArchiveEntry = {
    //@todo report multiple duplicate symbols
    val duplicateDefs = entry.definitions.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateDefs.nonEmpty) throw ParseException("Duplicate symbol '" + duplicateDefs.head._1._1 + "'", duplicateDefs.head._2.last.loc)
    val duplicateVars = entry.vars.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateVars.nonEmpty) throw ParseException("Duplicate variable '" + duplicateVars.head._1._1 + "'", duplicateVars.head._2.last.loc)

    val duplicateInheritedDefs = entry.inheritedDefinitions.groupBy(d => (d.name, d.index)).filter({case (_, defs) => defs.size > 1})
    if (duplicateInheritedDefs.nonEmpty) throw ParseException("Duplicate symbol '" + duplicateInheritedDefs.head._1._1 + "'", duplicateInheritedDefs.head._2.last.loc)

    val illegalOverride = entry.definitions.filter(e => entry.inheritedDefinitions.exists(_.name == e.name))
    if (illegalOverride.nonEmpty) throw ParseException("Symbol '" + illegalOverride.head.name + "' overrides inherited definition; must declare override", illegalOverride.head.loc)

    val definitions = ((entry.inheritedDefinitions ++ entry.definitions).map(convert) ++ entry.vars.map(convert)).reduceOption(_++_).getOrElse(Declaration(Map.empty))

    val sharedDefsText = if (entry.inheritedDefinitions.nonEmpty) {
      "SharedDefinitions\n" +
        entry.inheritedDefinitions.map(d => slice(text, d.loc)).mkString("\n") +
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

    entry.problem match {
      case Left(problem) =>
        KeYmaeraXParser.semanticAnalysis(problem) match {
          case None =>
          case Some(error) => throw ParseException("Semantic analysis error\n" + error, problem)
        }

        val elaborated = definitions.exhaustiveSubst(problem)
        typeAnalysis(entry.name, definitions ++ BuiltinDefinitions.defs, elaborated) //throws ParseExceptions.

        // check that definitions and use match
        val symbols = StaticSemantics.symbols(problem) ++ definitions.substs.flatMap(s => StaticSemantics.symbols(s.repl))
        val defSymbols = definitions.substs.map(_.what)
        val mismatches = defSymbols.map({
          case n: NamedSymbol => symbols.find(u => u.name == n.name && u.index == n.index && u.kind != n.kind).map(n -> _)
          case _ => None
        }).filter(_.isDefined).map(_.get)
        if (mismatches.nonEmpty) {
          val mismatchDescription = mismatches.map({ case (defSym, sym) =>
            "Symbol '" + defSym.prettyString + "' defined as " + defSym.kind +
              ", but used as " + sym.kind + " in " + sym.prettyString}).mkString("\n")
          val found = mismatches.map({ case (_, sym) => sym.prettyString}).mkString(", ")
          val expected = mismatches.map({ case (defSym, _) => defSym.prettyString }).mkString(", ")
          throw new ParseException("All definitions and uses must match, but found the following mismatches:\n" +
            mismatchDescription, UnknownLocation, found, expected, "", "")
        }

        // collect annotations
        val defAnnotations = (entry.inheritedDefinitions ++ entry.definitions).flatMap({ case ProgramDef(_, _, _, annotations, _) => annotations case _ => Nil })

        // report annotations
        (defAnnotations ++ entry.annotations).foreach({
          case Annotation(e: Program, a: Formula) =>
            val substPrg = definitions.exhaustiveSubst(e)
            val substFml = definitions.exhaustiveSubst(a)
            typeAnalysis(entry.name, definitions ++ BuiltinDefinitions.defs ++ BuiltinAnnotationDefinitions.defs, substFml)
            KeYmaeraXParser.annotationListener(substPrg, substFml)
          case Annotation(_: Program, a) => throw ParseException("Annotation must be formula, but got " + a.prettyString, UnknownLocation)
          case Annotation(e, _) => throw ParseException("Annotation on programs only, but was on " + e.prettyString, UnknownLocation)
        })

        val tactics =
          if (parseTactics) entry.tactics.map(convert(_, definitions))
          else entry.tactics.map(t => (t.name, t.tacticText, Idioms.nil))

        //@todo "Exercise"->"exercise"???
        val entryKinds = Map("ArchiveEntry"->"theorem", "Theorem"->"theorem", "Lemma"->"lemma", "Exercise"->"theorem")

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

        ParsedArchiveEntry(entry.name, entryKinds(entry.kind), entryText.trim(), problemText.trim(), definitions, elaborated, tactics, entry.info)
      case Right(_) =>
        ParsedArchiveEntry(entry.name, "exercise", entryText.trim(), problemText.trim(), definitions, False, Nil, entry.info)
    }
  }

  private def convert(d: Definition): Declaration = d match {
    case FuncPredDef(name, index, sort, signature, Left(definition), loc) =>
      // backwards compatible dots
      val dotTerms =
        if (signature.size == 1) signature.map(v => v -> DotTerm(v.sort, None))
        else signature.zipWithIndex.map({ case (v, i) => v -> DotTerm(v.sort, Some(i)) })
      val dottedDef = definition.map(d => dotTerms.foldRight(d)({ case ((v, dot), dotted) =>
        v match {
          case vv: Variable => dotted.replaceFree(vv, dot)
          case _ => dotted
        }
      }))
      Declaration(Map((name, index) -> (Some(toSort(signature)), sort, dottedDef, loc)))
    case FuncPredDef(name, index, sort, signature, Right(_), loc) =>
      Declaration(Map((name, index) -> (Some(toSort(signature)), sort, None, loc)))
    case ProgramDef(name, index, Left(definition), _, loc) =>
      Declaration(Map((name, index) -> (Some(Unit), Trafo, definition, loc)))
    case ProgramDef(name, index, Right(_), _, loc) =>
      Declaration(Map((name, index) -> (Some(Unit), Trafo, None, loc)))
    case VarDef(name, index, loc) =>
      Declaration(Map((name, index) -> (None, Real, None, loc)))
  }

  private def toSort(signature: List[NamedSymbol]): Sort = {
    if (signature.isEmpty) Unit
    else signature.tail.foldRight[Sort](signature.head.sort)({ case (v, s) => Tuple(v.sort, s) })
  }

  private def convert(t: Tactic, defs: Declaration): (String, String, BelleExpr) = {
    val tokens = BelleLexer(t.tacticText).map(tok => BelleToken(tok.terminal, shiftLoc(tok.location, t.belleExprLoc)))

    val tactic = BelleParser.parseTokenStream(tokens,
      DefScope[String, DefTactic](), DefScope[Expression, DefExpression](), None, defs)

    (t.name, t.tacticText, tactic)
  }

  private def slice(text: String, loc: Location): String = {
    val lines = text.lines.slice(loc.begin.line - 1, loc.end.line).toList
    if (loc.end.line > loc.begin.line) {
      val header = lines.head.drop(loc.begin.column - 1)
      val footer = lines.last.take(loc.end.column)
      (header +: lines.tail.dropRight(1) :+ footer).mkString("\n")
    } else {
      val result = lines.head.take(loc.end.column)
      result.drop(loc.begin.column - 1)
    }
  }

  private def slice(text: String, loc: Location, except: List[Location]): String = {
    if (except.isEmpty) slice(text, loc)
    else slice(
      slice(text, Region(1, 1, 1, 1).spanTo(except.last.begin)).dropRight(1) + slice(text, except.last.end.spanTo(loc.end)).drop(1),
      loc, except.dropRight(1))
  }

  private def declarationsOf(parsedContent: Expression): Declaration = {
    val symbols = StaticSemantics.symbols(parsedContent)
    val fnDecls = symbols.filter(_.isInstanceOf[Function]).map(_.asInstanceOf[Function]).map(fn =>
      (fn.name, fn.index) -> (Some(fn.domain), fn.sort, None, UnknownLocation)
    ).toMap[(String, Option[Int]),(Option[Sort], Sort, Option[Expression], Location)]
    val varDecls = symbols.filter(_.isInstanceOf[BaseVariable]).map(v =>
      (v.name, v.index) -> (None, v.sort, None, UnknownLocation)
    ).toMap[(String, Option[Int]),(Option[Sort], Sort, Option[Expression], Location)]
    Declaration(fnDecls ++ varDecls)
  }
  
  private def shiftLoc(loc: Location, offset: Location): Location = {
    if (loc.line <= 1) loc match {
      case Region(l, c, el, ec) if el == l =>
        Region(l + offset.line - 1, c + offset.column - 1, el + offset.line -1, ec + offset.column - 1)
      case Region(l, c, el, ec) if el > l =>
        Region(l + offset.line - 1, c + offset.column - 1, el + offset.line -1, ec)
      case SuffixRegion(l, c) => SuffixRegion(l + offset.line - 1, c + offset.column - 1)
      case l => l.addLines(offset.line - 1) //
    } else {
      loc.addLines(offset.line - 1)
    }
  }

}
