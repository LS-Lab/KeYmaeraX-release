/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

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
  *     Functions. ... End.
  *     ProgramVariables. ... End.
  *     Problem. ... End.
  *     Tactic "Proof 1". ... End.
  *     Tactic "Proof 2". ... End.
  *   End.
  *   ArchiveEntry "Entry 2". ... End.
  * }}}
  *
  * Created by smitsch on 12/29/16.
  */
object KeYmaeraXArchiveParser {
  /** The entry name, kyx file content (model), parsed model, and parsed name+tactic. */
  case class ParsedArchiveEntry(name: String, kind: String, fileContent: String,
                                defs: Declaration,
                                model: Expression, tactics: List[(String, String, BelleExpr)],
                                info: Map[String, String])

  /** Name is alphanumeric name and index. */
  type Name = (String, Option[Int])
  /** Signature is domain sort, codomain sort, "interpretation", token that starts the declaration. */
  type Signature = (Option[Sort], Sort, Option[Expression], Location)
  /** A declaration */
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
          val fs = USubst(substs)(f)
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
          case BaseVariable(name, i, _) => decls.contains((name, i)) && decls((name, i))._1 == Some(Unit)
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
    * @param d the type declarations known from the context
    * @param expr the expression parsed
    * @throws [[edu.cmu.cs.ls.keymaerax.parser.ParseException]] if the type analysis fails.
    */
  def typeAnalysis(d: Declaration, expr: Expression): Boolean = {
    StaticSemantics.symbols(expr).forall({
      case f:Function =>
        val (declaredDomain,declaredSort, interpretation, loc) = d.decls.get((f.name,f.index)) match {
          case Some(decl) => decl
          case None => throw ParseException("type analysis" + ": " + "undefined symbol " + f, f)
        }
        if(f.sort != declaredSort) throw ParseException(s"type analysis: ${f.prettyString} declared with sort $declaredSort but used where sort ${f.sort} was expected.", loc)
        else if (f.domain != declaredDomain.get) {
          (f.domain, declaredDomain) match {
            case (l, Some(r)) => throw ParseException(s"type analysis: ${f.prettyString} declared with domain $r but used where domain ${f.domain} was expected.", loc)
            case (l, None) => throw ParseException(s"type analysis: ${f.prettyString} declared as a non-function but used as a function.", loc)
            //The other cases can't happen -- we know f is a function so we know it has a domain.
          }
        }
        else true
      case x: Variable if quantifiedVars(expr).contains(x) => true //Allow all undeclared variables if they are at some point bound by a \forall or \exists. @todo this is an approximation. Should only allow quantifier bindings...
      case x: Variable =>
        val (declaredSort, declLoc) = d.decls.get((x.name,x.index)) match {
          case Some((None,sort, _, loc)) => (sort, loc)
          case Some((Some(domain), sort, _, loc)) => throw ParseException(s"Type analysis: ${x.name} was declared as a function but used as a non-function.", loc)
          case None => throw ParseException("type analysis" + ": " + "undefined symbol " + x + " with index " + x.index, x)
        }
        if (x.sort != declaredSort) throw ParseException(s"type analysis: ${x.prettyString} declared with sort $declaredSort but used where a ${x.sort} was expected.", declLoc)
        x.sort == declaredSort
      case _: UnitPredicational => true //@note needs not be declared
      case _: UnitFunctional => true //@note needs not be declared
      case _: DotTerm => true //@note needs not be declared
      case DifferentialSymbol(v) => d.decls.contains(v.name, v.index) //@note hence it is checked as variable already
      case _ => false
    })
  }

  private[parser] trait ArchiveItem extends OtherItem

  private[parser] case class ArchiveEntry(name: String, kind: String, loc: Location,
                                          inheritedDefinitions: List[Definition],
                                          definitions: List[Definition],
                                          vars: List[Definition],
                                          problem: Formula,
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

  private[parser] abstract class Definition(val name: String, val index: Option[Int], val definition: Option[Expression], val loc: Location) extends ArchiveItem {
    def extendLocation(end: Location): Definition
  }
  private[parser] case class FuncPredDef(override val name: String, override val index: Option[Int], sort: Sort, signature: List[NamedSymbol], override val definition: Option[Expression], override val loc: Location) extends Definition(name, index, definition, loc) {
    override def extendLocation(end: Location): Definition = FuncPredDef(name, index, sort, signature, definition, loc.spanTo(end))
  }
  private[parser] case class ProgramDef(override val name: String, override val index: Option[Int], override val definition: Option[Program], annotations: List[Annotation], override val loc: Location) extends Definition(name, index, definition, loc) {
    override def extendLocation(end: Location): Definition = ProgramDef(name, index, definition, annotations, loc.spanTo(end))
  }
  private[parser] case class VarDef(override val name: String, override val index: Option[Int], override val loc: Location) extends Definition(name, index, None, loc) {
    override def extendLocation(end: Location): Definition = VarDef(name, index, loc.spanTo(end))
  }
  private[parser] case class Definitions(defs: List[Definition], vars: List[Definition]) extends ArchiveItem
  private[parser] case class Annotation(element: Expression, annotation: Expression) extends ArchiveItem
  private[parser] case class Problem(fml: Formula, annotations: List[Annotation]) extends ArchiveItem
  private[parser] case class Tactic(name: String, tacticText: String, begin: Location) extends ArchiveItem
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
      (FuncPredDef("abs", None, Real, DotTerm(Real, None) :: Nil, None, UnknownLocation) ::
       FuncPredDef("min", None, Real, DotTerm(Real, Some(0)) :: DotTerm(Real, Some(1)) :: Nil, None, UnknownLocation) ::
       FuncPredDef("max", None, Real, DotTerm(Real, Some(0)) :: DotTerm(Real, Some(1)) :: Nil, None, UnknownLocation) ::
       Nil).map(convert).reduce(_++_)
  }

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  def apply(input: String): List[ParsedArchiveEntry] = parse(input)
  /** Parse the input string in the concrete syntax as a differential dynamic logic expression.
    * Skips parsing tactics if `parseTactics` is false. Requires KeYmaeraXPrettyPrinter setup if `parseTactics` is true. */
  def parse(input: String, parseTactics: Boolean = true): List[ParsedArchiveEntry] = {
    val stripped = ParserHelper.removeBOM(input)
    val tokenStream = KeYmaeraXLexer.inMode(stripped, ProblemFileMode)
    try {
      parse(tokenStream, stripped, parseTactics)
    } catch {
      case e: ParseException => throw e.inInput(stripped, Some(tokenStream))
    }
  }

  /** Tries parsing as a problem first. If it fails due to a missing Problem block, tries parsing as a plain formula. */
  def parseAsProblemOrFormula(input: String): Formula = {
    try {
      parseProblem(input, parseTactics=false).model.asInstanceOf[Formula]
    } catch {
      case ex: ParseException if ex.msg == "Problem. block expected" =>
        KeYmaeraXParser(input).asInstanceOf[Formula]
    }
  }

  /** Parses a single entry. */
  def parseProblem(input: String, parseTactics: Boolean = true): ParsedArchiveEntry = {
    val entries = parse(input)
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
        case _ => throw ParseException("Missing archive name", st, nextTok, "\"<string>\"")
      }
      case r :+ (begin@Token(ARCHIVE_ENTRY_BEGIN(_), _)) :+ (name@Token(_: DOUBLE_QUOTES_STRING, _)) :+ (info@MetaInfo(_)) if info.info.isEmpty && (la == PERIOD || la == SEMI) =>
        reduce(shift(st), 1, Bottom, r :+ begin :+ name :+ info)
      // finish entry
      case r :+ Token(ARCHIVE_ENTRY_BEGIN(kind), startLoc) :+ Token(DOUBLE_QUOTES_STRING(name), _) :+ MetaInfo(info) :+ Definitions(defs, vars) :+
          Problem(problem, annotations) :+ Tactics(tactics) => la match {
        case END_BLOCK => reduce(shift(st), 7, Bottom :+ ArchiveEntry(name, kind, startLoc.spanTo(currLoc.end), Nil, defs, vars, problem, annotations, tactics, info), r)
        case TACTIC_BLOCK => shift(st)
        case _ => throw ParseException("Missing entry delimiter", st, nextTok, END_BLOCK.img)
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
        case END_BLOCK => reduce(shift(st), 2, Bottom, r :+ defs)
        case _ if isReal(la) || isBool(la) || isProgram(la) => shift(st)
        case _ => throw ParseException("Missing definitions delimiter", st, nextTok, END_BLOCK.img)
      }
      case _ :+ (_: Definitions) :+ Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _) :+ Token(sort, _) if (isReal(sort) || isBool(sort) || isProgram(sort)) && la.isInstanceOf[IDENT] => shift(st)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isReal(sort) =>
        reduce(st, 2, Bottom :+ FuncPredDef(name, index, Real, Nil, None, startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isBool(sort) =>
        reduce(st, 2, Bottom :+ FuncPredDef(name, index, Bool, Nil, None, startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), endLoc) if isProgram(sort) =>
        reduce(st, 2, Bottom :+ ProgramDef(name, index, None, Nil, startLoc.spanTo(endLoc.end)), r :+ defs :+ defsBlock)

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
          val (predDefBlock, remainder, endLoc) =
            if (rest.head.tok == LPAREN) {
              var openParens = 0
              if (!rest.exists(_.tok == RPAREN)) throw ParseException.imbalancedError("Unmatched predicate definition delimiter", rest.head, RPAREN.img, ParseState(Bottom :+ rest.head, rest.tail))
              val (Token(LPAREN, _) :: predDefBlock, Token(RPAREN, endLoc) :: remainder) = rest.span(t => { if (t.tok == LPAREN) openParens += 1 else if (t.tok == RPAREN) openParens -= 1; openParens > 0})
              (predDefBlock, remainder, endLoc.end)
            } else {
              val (predDefBlock, remainder) = rest.span(_.tok != SEMI)
              (predDefBlock, remainder, predDefBlock.last.loc.end)
            }
          val pred: Formula = try {
            KeYmaeraXParser.formulaTokenParser(predDefBlock :+ Token(EOF, remainder.head.loc))
          } catch {
            case ex: ParseException =>
              val loc = predDefBlock.head.loc.spanTo(endLoc)
              throw new ParseException("Predicate definition expects a Formula", loc, slice(text, loc.begin, loc.end), FormulaKind.toString, la.img, "", ex)
          }
          ParseState(r :+ defs :+ defsBlock :+ FuncPredDef(next.name, next.index, next.sort, next.signature, Some(pred), next.loc.spanTo(endLoc)), remainder)
        case SEMI | PERIOD => shift(st)
        case EQ => throw ParseException("Predicate must be defined by equivalence", st, nextTok, EQUIV.img)
        case _ => throw ParseException("Unexpected token in predicate definition", st, nextTok, EQUIV.img)
      }
      case r :+ (defs: Definitions) :+ (defsBlock@Token(DEFINITIONS_BLOCK | FUNCTIONS_BLOCK, _)) :+ (next: FuncPredDef) if next.sort == Real => la match {
        case EQ =>
          val (funcDefBlock, remainder, endLoc) =
            if (rest.head.tok == LPAREN) {
              var openParens = 0
              if (!rest.exists(_.tok == RPAREN)) throw ParseException.imbalancedError("Unmatched function definition delimiter", rest.head, RPAREN.img, ParseState(Bottom :+ rest.head, rest.tail))
              val (Token(LPAREN, _) :: funcDefBlock, Token(RPAREN, endLoc) :: remainder) = rest.span(t => { if (t.tok == LPAREN) openParens += 1 else if (t.tok == RPAREN) openParens -= 1; openParens > 0})
              (funcDefBlock, remainder, endLoc.end)
            } else {
              val (funcDefBlock, remainder) = rest.span(_.tok != SEMI)
              (funcDefBlock, remainder, funcDefBlock.last.loc.end)
            }
          val term: Term = try {
            KeYmaeraXParser.termTokenParser(funcDefBlock :+ Token(EOF, remainder.head.loc))
          } catch {
            case ex: ParseException =>
              val loc = funcDefBlock.head.loc.spanTo(endLoc)
              throw new ParseException("Function definition expects a Term", loc, slice(text, loc.begin, loc.end), TermKind.toString, la.img, "", ex)
          }
          ParseState(r :+ defs :+ defsBlock :+ FuncPredDef(next.name, next.index, next.sort, next.signature, Some(term), next.loc.spanTo(endLoc)), remainder)
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
          if (rest.head.tok != LBRACE) throw ParseException("Missing program definition start delimiter", rest.head.loc, rest.head.tok.toString, LBRACE.img, "", "", null)
          if (!rest.exists(_.tok == RBRACE)) throw ParseException.imbalancedError("Unmatched program definition delimiter", rest.head, RBRACE.img, ParseState(Bottom :+ rest.head, rest.tail))
          var openParens = 0
          val (Token(LBRACE, _) :: prgDefBlock, Token(RBRACE, endLoc) :: remainder) =
            rest.span(t => { if (t.tok == LBRACE) openParens += 1 else if (t.tok == RBRACE) openParens -= 1; openParens > 0})
          val program: Program = try {
            KeYmaeraXParser.programTokenParser(prgDefBlock :+ Token(EOF, endLoc))
          } catch {
            case ex: ParseException =>
              val loc = prgDefBlock.head.loc.spanTo(endLoc)
              throw new ParseException("Program definition expects a Program", loc, slice(text, loc.begin, loc.end), ProgramKind.toString, la.img, "", ex)
          }
          parser.setAnnotationListener(annotationListener)
          ParseState(r :+ defs :+ defsBlock :+ ProgramDef(next.name, next.index, Some(program), annotations.toList, next.loc.spanTo(endLoc.end)), remainder)
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
        case END_BLOCK => reduce(shift(st), 2, Bottom, r)
        case _ if isReal(la) => shift(st)
        case _ if isBool(la) || isProgram(la) => throw ParseException("Predicate and program definitions only allowed in Definitions block", st, nextTok, "Real")
        case _ => throw ParseException("Missing program variables delimiter", st, nextTok, END_BLOCK.img)
      }
      case _ :+ Token(PROGRAM_VARIABLES_BLOCK, _) :+ Token(sort, _) if isReal(sort) && la.isInstanceOf[IDENT] => shift(st)
      case r :+ (defs: Definitions) :+ (varsBlock@Token(PROGRAM_VARIABLES_BLOCK, _)) :+ Token(sort, startLoc) :+ Token(IDENT(name, index), _) if isReal(sort) => la match {
        case SEMI | PERIOD =>
          reduce(shift(st), 5, Bottom :+ Definitions(defs.defs, defs.vars :+ VarDef(name, index, startLoc)) :+ varsBlock, r)
        case LPAREN => throw ParseException("Function definition only allowed in Definitions block", st, nextTok, SEMI.img + " or " + COMMA.img)
        case _ => throw ParseException("Unexpected token in ProgramVariables block", st, nextTok, SEMI.img + " or " + COMMA.img)
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
          if (!st.input.exists(_.tok == END_BLOCK)) throw ParseException("Missing problem delimiter", st, st.input.last, END_BLOCK.img)
          val (problemBlock, Token(END_BLOCK, endLoc) :: remainder) = st.input.span(_.tok != END_BLOCK) match {
            case (Token(PROBLEM_BLOCK, _) :: Token(PERIOD, _) :: pb, r) => (pb, r)
            case (Token(PROBLEM_BLOCK, _) :: pb, r) => (pb, r)
          }
          problemBlock.find(_.tok == TACTIC_BLOCK) match {
            case Some(t) => throw ParseException("Missing problem delimiter", st, t, END_BLOCK.img)
            case None => // problem seems correctly ended
          }
          val problem: Formula = parser.formulaTokenParser(problemBlock :+ Token(EOF, endLoc))
          parser.setAnnotationListener(annotationListener)
          ParseState(st.stack :+ Problem(problem, annotations.toList) :+ Tactics(Nil), remainder)
        case _ if !rest.exists(_.tok == PROBLEM_BLOCK) => throw ParseException("Missing problem block", st, nextTok, PROBLEM_BLOCK.img)
        case _ if  rest.exists(_.tok == PROBLEM_BLOCK) => throw ParseException("Misplaced problem block: problem expected before tactics", st, nextTok, PROBLEM_BLOCK.img)
      }

      // tactic
      case _ :+ Tactics(_) :+ Token(TACTIC_BLOCK, _) if la.isInstanceOf[DOUBLE_QUOTES_STRING] => shift(st)
      case r :+ (tactics@Tactics(_)) :+ (tacticBlock@Token(TACTIC_BLOCK, _)) if la == PERIOD =>
        reduce(shift(st), 1, Bottom :+ Token(DOUBLE_QUOTES_STRING("Unnamed"), currLoc), r :+ tactics :+ tacticBlock)
      case r :+ (tactics@Tactics(_)) :+ (tacticBlock@Token(TACTIC_BLOCK, _)) :+ (name@Token(DOUBLE_QUOTES_STRING(_), _)) if la == PERIOD || la == SEMI =>
        reduce(shift(st), 1, Bottom, r :+ tactics :+ tacticBlock :+ name)
      case r :+ (tactics@Tactics(_)) :+ Token(TACTIC_BLOCK, _) :+ Token(DOUBLE_QUOTES_STRING(name), _) =>
        //@note slice and parse later with BelleParser (needs converted definitions)
        //@todo reimplement BelleLexer/BelleParser
        val (tacticBlock, remainder) = input.span(_.tok != END_BLOCK)
        val tacticText = slice(text, tacticBlock.head.loc.begin, tacticBlock.last.loc.end)
        ParseState(r :+ tactics :+ Tactic(name, tacticText, currLoc), remainder)
      case r :+ (tactics@Tactics(_)) :+ (tactic@Tactic(_, _, _)) if la == END_BLOCK =>
        reduce(shift(st), 3, Bottom :+ Tactics(tactics.tactics :+ tactic), r)

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
                Bottom :+ Token(ARCHIVE_ENTRY_BEGIN("ArchiveEntry"), UnknownLocation) :+ Token(DOUBLE_QUOTES_STRING("Unnamed"), UnknownLocation) :+ MetaInfo(Map.empty),
                (tokens :+ Token(END_BLOCK, UnknownLocation)) ++ eof)
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
    KeYmaeraXParser.semanticAnalysis(entry.problem) match {
      case None =>
      case Some(error) => throw ParseException("Semantic analysis error\n" + error, entry.problem)
    }

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
    val elaborated = definitions.exhaustiveSubst(entry.problem)
    typeAnalysis(definitions ++ BuiltinDefinitions.defs, elaborated) //throws ParseExceptions.

    // collect annotations
    val defAnnotations = (entry.inheritedDefinitions ++ entry.definitions).flatMap({ case ProgramDef(_, _, _, annotations, _) => annotations case _ => Nil })

    // report annotations
    (defAnnotations ++ entry.annotations).foreach({
      case Annotation(e: Program, a: Formula) => KeYmaeraXParser.annotationListener(definitions.exhaustiveSubst(e), definitions.exhaustiveSubst(a))
      case Annotation(_: Program, a) => throw ParseException("Annotation must be formula, but got " + a.prettyString, UnknownLocation)
      case Annotation(e, _) => throw ParseException("Annotation on programs only, but was on " + e.prettyString, UnknownLocation)
    })

    val tactics =
      if (parseTactics) entry.tactics.map(convert(_, definitions))
      else entry.tactics.map(t => (t.name, t.tacticText, Idioms.nil))

    val sharedDefsText = if (entry.inheritedDefinitions.nonEmpty) {
      "SharedDefinitions.\n" +
      entry.inheritedDefinitions.map(d => slice(text, d.loc.begin, d.loc.end)).mkString("\n") +
      "\nEnd.\n"
    } else ""

    val entryText = sharedDefsText + (if (entry.loc.begin.line > 0) slice(text, entry.loc.begin, entry.loc.end) else text)

    val entryKinds = Map("ArchiveEntry"->"theorem", "Theorem"->"theorem", "Lemma"->"lemma", "Exercise"->"theorem")

    ParsedArchiveEntry(entry.name, entryKinds(entry.kind), entryText, definitions, elaborated, tactics, entry.info)
  }

  private def convert(d: Definition): Declaration = d match {
    case FuncPredDef(name, index, sort, signature, definition, loc) =>
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
    case ProgramDef(name, index, definition, _, loc) =>
      Declaration(Map((name, index) -> (Some(Unit), Trafo, definition, loc)))
    case VarDef(name, index, loc) =>
      Declaration(Map((name, index) -> (None, Real, None, loc)))
  }

  private def toSort(signature: List[NamedSymbol]): Sort = {
    if (signature.isEmpty) Unit
    else signature.tail.foldRight[Sort](signature.head.sort)({ case (v, s) => Tuple(v.sort, s) })
  }

  private def convert(t: Tactic, defs: Declaration): (String, String, BelleExpr) = {
    val tokens = BelleLexer(t.tacticText)
    tokens.map(t => BelleToken(t.terminal, t.location.addLines(t.location.line)))

    val tactic = BelleParser.parseTokenStream(tokens,
      DefScope[String, DefTactic](), DefScope[Expression, DefExpression](), None, defs)

    (t.name, t.tacticText, tactic)
  }

  private def slice(text: String, begin: Location, end: Location): String = {
    val lines = text.lines.slice(begin.line - 1, end.line).toList
    if (end.line > begin.line) {
      val header = lines.head.drop(begin.column - 1)
      val footer = lines.last.take(end.column)
      (header +: lines.tail.dropRight(1) :+ footer).mkString("\n")
    } else {
      val result = lines.head.take(end.column)
      result.drop(begin.column - 1)
    }
  }

}
