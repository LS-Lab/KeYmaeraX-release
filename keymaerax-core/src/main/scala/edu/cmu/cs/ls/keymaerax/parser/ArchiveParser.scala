package edu.cmu.cs.ls.keymaerax.parser

import java.io.InputStream

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core.{Bool, DotTerm, Expression, Formula, FuncOf, Function, NamedSymbol, Nothing, PredOf, Program, ProgramConst, Real, Sort, StaticSemantics, SubstitutionClashException, SubstitutionPair, SystemConst, Term, Trafo, Tuple, USubst, Unit, Variable}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{DependencyAnalysis, ExpressionTraversal, FormulaTools, PosInExpr}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser.{Name, Signature}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser.parse

import scala.collection.immutable.List

/** A parsed declaration, which assigns a signature to names. */
case class Declaration(decls: Map[Name, Signature]) {
  /** The declarations as topologically sorted substitution pairs. */
  lazy val substs: List[SubstitutionPair] = topSort(decls.filter(_._2._4.isDefined).map({
    case (name, (domain, sort, argNames, interpretation, loc)) =>
      // elaborate to functions for topSort (topSort uses signature)
      (name, (domain, sort, argNames, interpretation.map(elaborateToFunctions), loc))
  })).map((declAsSubstitutionPair _).tupled)

  /** Declared names and signatures as [[NamedSymbol]]. */
  lazy val asNamedSymbols: List[NamedSymbol] = decls.map({ case ((name, idx), (domain, sort, _, _, _)) => sort match {
    case Real | Bool if domain.isEmpty => Variable(name, idx, sort)
    case Real | Bool if domain.isDefined => Function(name, idx, domain.get, sort)
    case Trafo => assert(idx.isEmpty, "Program constants are not allowed to have an index, but got " + name + "_" + idx); ProgramConst(name)
  }}).toList

  /** Topologically sorts the names in `decls`. */
  private def topSort(decls: Map[Name, Signature]): List[(Name, Signature)] = {
    val sortedNames = DependencyAnalysis.dfs[Name](decls.map({ case (name, (_, _, _, repl, _)) =>
      name -> repl.map(StaticSemantics.signature).map(_.map(ns => (ns.name, ns.index))).getOrElse(Set.empty) }))
    decls.toList.sortBy(s => sortedNames.indexOf(s._1))
  }

  /** Joins two declarations. */
  def ++(other: Declaration): Declaration = Declaration(decls ++ other.decls)

  /** Finds the definition with `name` and index `idx`. */
  def find(name: String, idx: Option[Int] = None): Option[Signature] = decls.get(name -> idx)

  /** Applies substitutions per `substs` exhaustively to expression-like `arg`. */
  def exhaustiveSubst[T <: Expression](arg: T): T = try {
    elaborateToFunctions(arg.exhaustiveSubst(USubst(substs))).asInstanceOf[T]
  } catch {
    case ex: SubstitutionClashException =>
      throw ParseException("Definition " + ex.context + " as " + ex.e + " must declare arguments " + ex.clashes, ex)
  }

  /** Elaborates variable uses of declared functions. */
  //@todo need to look into concrete programs that implement program constants when elaborating
  def elaborateToFunctions[T <: Expression](expr: T): T = expr.elaborateToFunctions(asNamedSymbols.toSet).asInstanceOf[T]

  /** Elaborates program constants to system constants if their definition is dual-free. */
  def elaborateToSystemConsts(expr: Formula): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case ProgramConst(name, space) =>
          decls.find(_._1._1 == name).flatMap(_._2._4) match {
            case Some(prg: Program) =>
              if (FormulaTools.dualFree(prg)) Right(SystemConst(name, space))
              else Left(None)
            case Some(_) => Left(None) // symbol is not defined as a program (typeAnalysis error will be raised later)
            case None => Left(None) // undefined symbol (could be program or game)
          }
        case _ => Left(None)
      }
    }, expr) match {
      case Some(f) => f
      case None => ???
    }
  }

  /** Elaborates all declarations to dots. */
  def elaborateWithDots: Declaration = Declaration(decls.map(d => elaborateWithDots(d._1, d._2)))

  /** Elaborates the interpretation in `signature` to dots. */
  private def elaborateWithDots(name: Name, signature: Signature): (Name, Signature) = signature._4 match {
    case None => (name, signature)
    case Some(interpretation) => signature._3 match {
      case None => (name, signature)
      case Some(argNames) =>
        val arg = signature._1 match {
          case Some(Unit) => Nothing
          case Some(s: Tuple) => s.toDots(0)._1
          case Some(s) => DotTerm(s)
          case None => Nothing
        }

        // backwards compatible dots
        val dotTerms =
          if (argNames.size == 1) argNames.map(v => v -> DotTerm(v._2, None))
          else argNames.zipWithIndex.map({ case (v, i) => v -> DotTerm(v._2, Some(i)) })
        val dottedInterpretation = dotTerms.foldRight(interpretation)({ case ((((name, index), sort), dot), dotted) =>
          // signature may contain DotTerms because of anonymous arguments
          if (name != DotTerm().name) dotted.replaceFree(Variable(name, index, sort), dot)
          else dotted
        })

        val undeclaredDots = dotsOf(dottedInterpretation) -- dotsOf(arg)
        if (undeclaredDots.nonEmpty) throw ParseException(
          "Function/predicate " + name._1 + name._2.map("_" + _).getOrElse("") + "(" +
            argNames.map(an => (if (an._1._1 != DotTerm().name) an._1._1 else "•") + an._1._2.map("_" + _).getOrElse("")).mkString(",") + ")" +
            " defined using undeclared " + undeclaredDots.map(_.prettyString).mkString(","),
          UnknownLocation)
        (name, (signature._1, signature._2, signature._3, Some(dottedInterpretation), signature._5))
    }
  }

  /** Returns the dots used in expression `e`. */
  private def dotsOf(e: Expression): Set[DotTerm] = {
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

  /** Turns a function declaration (with defined body) into a substitution pair. */
  private def declAsSubstitutionPair(name: Name, signature: Signature): SubstitutionPair = {
    require(signature._4.isDefined, "Substitution only for defined functions")
    val (_, (domain, sort, _, Some(interpretation), loc)) = elaborateWithDots(name, signature)

    val (arg, sig) = domain match {
      case Some(Unit) => (Nothing, Unit)
      case Some(s: Tuple) => (s.toDots(0)._1, s)
      case Some(s) => (DotTerm(s), s)
      case None => (Nothing, Unit)
    }
    val what = sort match {
      case Real => FuncOf(Function(name._1, name._2, sig, signature._2), arg)
      case Bool => PredOf(Function(name._1, name._2, sig, signature._2), arg)
      case Trafo =>
        assert(name._2.isEmpty, "Expected no index in program const name, but got " + name._2)
        assert(signature._1.getOrElse(Unit) == Unit, "Expected domain Unit in program const signature, but got " + signature._1)
        interpretation match {
          case prg: Program =>
            if (FormulaTools.dualFree(prg)) SystemConst(name._1)
            else ProgramConst(name._1)
          case e => throw ParseException("Definition of " + name._1 + " is not a program, but a " + e.kind, loc)
        }
    }
    val repl = elaborateToFunctions(interpretation) match {
      case r@FuncOf(fn: Function, c) =>
        if (what.sort == fn.sort) r
        else PredOf(Function(fn.name, fn.index, fn.domain, what.sort), c)
      case p@PredOf(fn: Function, c) =>
        if (what.sort == fn.sort) p
        else FuncOf(Function(fn.name, fn.index, fn.domain, what.sort), c)
      case r => r
    }

    val undeclaredDots = dotsOf(repl) -- dotsOf(arg)
    if (undeclaredDots.nonEmpty) throw ParseException(
      "Function/predicate " + what.prettyString + " defined using undeclared " + undeclaredDots.map(_.prettyString).mkString(","),
      UnknownLocation)

    SubstitutionPair(what, repl)
  }
}

/** The entry name, kyx file content (model), definitions, parsed model, and parsed named tactics. */
case class ParsedArchiveEntry(name: String, kind: String, fileContent: String, problemContent: String,
                              defs: Declaration,
                              model: Expression,
                              tactics: List[(String, String, BelleExpr)],
                              annotations: List[(Expression, Expression)],
                              info: Map[String, String]) {
  /** True if this entry is an exercise, false otherwise. */
  def isExercise: Boolean = kind=="exercise"
  /** The model with all definitions expanded. */
  def expandedModel: Expression = defs.exhaustiveSubst(model)
  /** Return an archive with modified problem contents, otherwise identical./ */
  def withProblemContent(newProblemContent: String): ParsedArchiveEntry =
    ParsedArchiveEntry(name, kind, fileContent, newProblemContent, defs, model, tactics, annotations, info)
  /** Return an archive with modified file contents, otherwise identical./ */
  def withFileContent(newFileContent: String): ParsedArchiveEntry =
    ParsedArchiveEntry(name, kind, newFileContent, problemContent, defs, model, tactics, annotations, info)
}

trait ArchiveParser extends (String => List[ParsedArchiveEntry]) {
  def parse(input: String, parseTactics: Boolean = true): List[ParsedArchiveEntry]
  def parseFromFile(file: String): List[ParsedArchiveEntry]

  /** Returns the first entry in `input` as formula. */
  def parseAsFormula(input: String): Formula = parse(input, parseTactics=false).head.model.asInstanceOf[Formula]

  /** Returns the first entry in `in` as formula. */
  def parseAsFormula(in: InputStream): Formula = parseAsFormula(io.Source.fromInputStream(in).mkString)

  /** Reads a specific entry from the archive. */
  def getEntry(name: String, content: String): Option[ParsedArchiveEntry] = parse(content).find(_.name == name)

  /** Parses a single entry. */
  def parseProblem(input: String, parseTactics: Boolean = true): ParsedArchiveEntry = {
    val entries = parse(input, parseTactics)
    if (entries.size == 1) entries.head
    else throw ParseException("Expected a single entry, but got " + entries.size, UnknownLocation)
  }

  /** Indicates whether or not the model represents an exercise. */
  def isExercise(model: String): Boolean = model.contains("__________")
}

object ArchiveParser extends ArchiveParser {
  /** Name is alphanumeric name and index. */
  type Name = (String, Option[Int])
  /** Signature is a domain sort, codomain sort, argument names, expression used as "interpretation", location that starts the declaration. */
  type Signature = (Option[Sort], Sort, Option[List[(Name, Sort)]], Option[Expression], Location)
  /** Input signature as defined in the input file ([[Signature]] is extracted from it). */
  type InputSignature = (List[NamedSymbol], Option[Expression])

  /* @note mutable state for switching out the default parser. */
  private[this] var p: ArchiveParser = Configuration.get[String](Configuration.Keys.PARSER) match {
    case Some("KeYmaeraXParser") | None => KeYmaeraXArchiveParser
    case Some("DLParser") => DLArchiveParser
  }

  /** The parser that is presently used per default. */
  def parser: ArchiveParser = p

  /** Set a new parser. */
  def setParser(parser: ArchiveParser): Unit = { p = parser }

  /** Parses `input`. */
  override def apply(input: String): List[ParsedArchiveEntry] = parser(input)

  override def parse(input: String, parseTactics: Boolean): List[ParsedArchiveEntry] = parser.parse(input, parseTactics)

  override def parseFromFile(file: String): List[ParsedArchiveEntry] = parser.parseFromFile(file)
}