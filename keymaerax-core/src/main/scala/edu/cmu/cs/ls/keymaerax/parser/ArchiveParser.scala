package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.TacticParser

import java.io.InputStream
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, ProverSetupException}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{DependencyAnalysis, ExpressionTraversal, FormulaTools, PosInExpr}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._

import scala.collection.immutable.List
import scala.collection.mutable.ListBuffer

/** Name is alphanumeric name and index. */
case class Name(name: String, index: Option[Int] = None) {
  def prettyString: String = name + index.map("_" + _).getOrElse("")
}
/** Signature is a domain sort, codomain sort, argument names, expression used as interpretation, location that starts the declaration.
  * The signature of a function/predicate/program symbol.
  * @param domain the source domain required as an argument (if any).
  * @param codomain the resulting target domain.
  * @param arguments the list of named arguments (and their sorts which are compatible with `domain`).
  * @param interpretation uninterpreted symbol if None, or the interpretation of interpreted symbols.
  * @param loc the location in the model archive file where this was declared.
  */
//@todo check whether domain sort is compatible with sorts of arguments
case class Signature(domain: Option[Sort], codomain: Sort, arguments: Option[List[(Name, Sort)]],
                     interpretation: Option[Expression], loc: Location)

/** A parsed declaration, which assigns a signature to names.
  * This is the central data structure remembering which name belongs to which function/predicate/program symbol declaration
  * of a model in an archive.
  */
case class Declaration(decls: Map[Name, Signature]) {
  /** The declarations as topologically sorted substitution pairs. */
  lazy val substs: List[SubstitutionPair] = Declaration.topSort(decls.filter(_._2.interpretation match {
    case Some(ns: NamedSymbol) => !ReservedSymbols.reserved.contains(ns)
    case i => i.isDefined
  }).map({
    case (name, sig@Signature(_, _, args, interpretation, _)) =>
      // except named arguments and dots, elaborate all symbols to functions for topSort because topSort uses signature
      val taboo = args.map(_.filter({ case (Name("\\cdot", _), _) => false case _ => true }).
        map({ case (Name(n, i), sort) => Function(n, i, Unit, sort) }).toSet).getOrElse(Set.empty)
      (name, sig.copy(interpretation = interpretation.map(i => elaborateToSystemConsts(elaborateToFunctions(i, taboo)))))
  })).map((declAsSubstitutionPair _).tupled)

  /** The subset of substs for implicitly defined functions. */
  lazy val isubsts: List[SubstitutionPair] = substs.filter(f =>
    f.repl match {
      case FuncOf(e,_) => e.interpreted && e.domain == Real
      case _ => false
    }
  )

  /** Returns the substitutions reachable transitively from symbols `s`. */
  def transitiveSubstsFrom(e: Expression): List[SubstitutionPair] = {
    val s = StaticSemantics.symbols(e).filterNot(_.isInstanceOf[DotTerm])
    val expand = substs.filter(sp => StaticSemantics.symbols(sp.what).intersect(s).nonEmpty)
    val also = expand.flatMap(sp => transitiveSubstsFrom(sp.repl) )
    Declaration.topSort(also ++ expand)
  }

  /** Substitution applying all definitions non-recursively (i.e., one level of substitution). */
  lazy val subst: USubst = USubst(substs)

  /** Declared names and signatures as [[NamedSymbol]]. */
  lazy val asNamedSymbols: List[NamedSymbol] = {
    Declaration.topSort(decls).reverseMap(decl => Declaration.asNamedSymbol(decl._1,
      decl._2.copy(interpretation = decl._2.interpretation.map(elaborateToSystemConsts))))
  }

  /** Joins two declarations. */
  def ++(other: Declaration): Declaration = {
    val keyClashes = decls.keySet.intersect(other.decls.keySet).flatMap(n => {
      if (decls(n) == other.decls(n)) None
      else (decls(n), other.decls(n)) match {
        case (Signature(td, ts, ta, ti, _), Signature(od, os, oa, oi, _)) if td != od || ts != os || ta.size != oa.size || ti != oi => Some(n)
        case _ => None
      }
    })
    require(keyClashes.isEmpty, "Expected unique definitions, but got contradictory definitions for names " + keyClashes.map(_.prettyString).mkString(","))
    Declaration(decls ++ other.decls)
  }

  /** Definitions projected to names. */
  def project(names: Set[Name]): Declaration = Declaration(decls.filter({ case (n, _) => names.contains(n) }))

  /** Finds the definition with `name` and index `idx`. */
  def find(name: String, idx: Option[Int] = None): Option[Signature] = decls.get(Name(name, idx))

  /** True if a definition with `name` and `idx` is contained in this set. */
  def contains(name: String, idx: Option[Int]): Boolean = decls.contains(Name(name, idx))
  /** True if a definition with name and index per named symbol `n` is contained in this set. */
  def contains(n: NamedSymbol): Boolean = contains(n.name, n.index)

  /** Applies substitutions per `substs` exhaustively to expression-like `arg`. */
  def exhaustiveSubst[T <: Expression](arg: T): T = try {
    elaborateToFunctions(arg.exhaustiveSubst(USubst(substs))).asInstanceOf[T]
  } catch {
    case ex: SubstitutionClashException =>
      throw ParseException("Definition " + ex.context + " as " + ex.e + " must declare arguments " + ex.clashes, ex)
  }
  /** Applies substitutions per `substs` exhaustively to sequent `s`. */
  def exhaustiveSubst(s: Sequent): Sequent = Sequent(s.ante.map(exhaustiveSubst[Formula]), s.succ.map(exhaustiveSubst[Formula]))

  /** Applies implicit definition substitutions to expression-like `arg`. */
  def implicitSubst[T <: Expression](arg: T): T = try {
    USubst(isubsts).apply(arg).asInstanceOf[T]
  } catch {
    case ex: SubstitutionClashException =>
      throw ParseException("Definition " + ex.context + " as " + ex.e + " must declare arguments " + ex.clashes, ex)
  }

  /** Expands all symbols in expression `arg` fully. */
  def expandFull[T <: Expression](arg: T): T = try {
    exhaustiveSubst(elaborateToFunctions(elaborateToSystemConsts(arg)))
  } catch {
    case ex: SubstitutionClashException =>
      throw ParseException("Definition " + ex.context + " as " + ex.e + " must declare arguments " + ex.clashes, ex)
  }

  /** Elaborates variable uses of declared functions, except those listed in taboo. */
  //@todo need to look into concrete programs that implement program constants when elaborating
  def elaborateToFunctions[T <: Expression](expr: T, taboo: Set[Function] = Set.empty): T = try {
    expr.elaborateToFunctions(asNamedSymbols.toSet ++ InterpretedSymbols.builtin.toSet -- taboo).asInstanceOf[T]
  } catch {
    case ex: AssertionError => throw ParseException("Unable to elaborate to function symbols: " + ex.getMessage, ex)
  }

  /** Elaborates program constants to system constants if their definition is dual-free. */
  def elaborateToSystemConsts[T <: Expression](expr: T): T = {
    val elaborator = new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case ProgramConst(name, space) =>
          decls.find(_._1.name == name).flatMap(_._2.interpretation) match {
            case Some(prg: Program) =>
              if (FormulaTools.dualFree(prg)) Right(SystemConst(name, space))
              else Left(None)
            case Some(_) => Left(None) // symbol is not defined as a program (typeAnalysis error will be raised later)
            case None => Left(None) // undefined symbol (could be program or game)
          }
        case _ => Left(None)
      }
    }

    expr match {
      case f: Formula => ExpressionTraversal.traverse(elaborator, f).get.asInstanceOf[T]
      case t: Term => ExpressionTraversal.traverse(elaborator, t).get.asInstanceOf[T]
      case p: Program => ExpressionTraversal.traverse(elaborator, p).get.asInstanceOf[T]
    }
  }

  /** Elaborates all declarations to dots. */
  def elaborateWithDots: Declaration = Declaration(decls.map(d => elaborateWithDots(d._1, d._2)))

  /** Elaborates the interpretation in `signature` to dots. */
  private def elaborateWithDots(name: Name, signature: Signature): (Name, Signature) = signature.interpretation match {
    case None => (name, signature)
    case Some(interpretation) => signature.arguments match {
      case None => (name, signature)
      case Some((Name(Nothing.name, Nothing.index), Unit) :: Nil) => (name, signature)
      case Some(argNames) =>
        val arg = signature.domain match {
          case Some(Unit) => Nothing
          case Some(s: Tuple) => s.toDots(0)._1
          case Some(s) => DotTerm(s)
          case None => Nothing
        }

        // backwards compatible dots
        val dotTerms =
          if (argNames.size == 1) argNames.map(v => v -> DotTerm(v._2, None))
          else argNames.zipWithIndex.map({ case (v, i) => v -> DotTerm(v._2, Some(i)) })
        val dottedInterpretation = dotTerms.foldRight(interpretation)({ case (((Name(name, index), sort), dot), dotted) =>
          // signature may contain DotTerms because of anonymous arguments
          if (name != DotTerm().name) dotted.replaceFree(Variable(name, index, sort), dot).replaceFree(Differential(Variable(name, index, sort)), Differential(dot))
          else dotted
        })

        val undeclaredDots = dotsOf(dottedInterpretation) -- dotsOf(arg)
        if (undeclaredDots.nonEmpty) throw ParseException(
          "Function/predicate " + name.name + name.index.map("_" + _).getOrElse("") + "(" +
            argNames.map(an => (if (an._1.name != DotTerm().name) an._1.name else ".") + an._1.index.map("_" + _).getOrElse("")).mkString(",") + ")" +
            " defined using undeclared " + undeclaredDots.map(_.prettyString).mkString(","),
          UnknownLocation)
        (name, signature.copy(interpretation = Some(dottedInterpretation)))
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
      case _ => throw ParseException("Unknown expression " + e.prettyString + " of kind " + e.kind +
        " encountered when dotifying", UnknownLocation)
    }
    dots.toSet
  }

  /** Turns a function declaration (with defined body) into a substitution pair. */
  private def declAsSubstitutionPair(name: Name, signature: Signature): SubstitutionPair = {
    require(signature.interpretation.isDefined, "Substitution only for defined functions")
    val (_, Signature(domain, sort, _, Some(interpretation), loc)) = elaborateWithDots(name, signature)

    val (arg, sig) = domain match {
      case Some(Unit) => (Nothing, Unit)
      case Some(s: Tuple) => (s.toDots(0)._1, s)
      case Some(s) => (DotTerm(s), s)
      case None => (Nothing, Unit)
    }
    val what = sort match {
      case Real => FuncOf(Function(name.name, name.index, sig, signature.codomain), arg)
      case Bool => PredOf(Function(name.name, name.index, sig, signature.codomain), arg)
      case Trafo =>
        assert(name.index.isEmpty, "Expected no index in program const name, but got " + name.index)
        assert(signature.domain.getOrElse(Unit) == Unit, "Expected domain Unit in program const signature, but got " + signature.domain)
        interpretation match {
          case prg: Program =>
            if (FormulaTools.dualFree(prg)) SystemConst(name.name)
            else ProgramConst(name.name)
          case e => throw ParseException("Definition of " + name.name + " is not a program, but a " + e.kind, loc)
        }
      case _ => throw ParseException("Unknown sort " + sort + " encountered when converting definition to substitution pair", loc)
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

object Declaration {
  /** Converts name `n` with signature `s` to a named symbol. */
  def asNamedSymbol(n: Name, s: Signature): NamedSymbol = (n, s) match {
    case (Name(name, idx), Signature(domain, sort, _, rhs, _)) => sort match {
      case Real | Bool =>
        if (domain.isEmpty) Variable(name, idx, sort)
        else Function(name, idx, domain.get, sort)
      case Trafo =>
        assert(idx.isEmpty, "Program/system constants are not allowed to have an index, but got " + name + "_" + idx)
        rhs match {
          case Some(p: Program) if FormulaTools.dualFree(p) => SystemConst(name)
          case _ => ProgramConst(name)
        }
    }
  }

  /** Converts a list of substitution pairs `s` into a declaration. */
  def fromSubst(s: List[SubstitutionPair]): Declaration = {
    def argsFromExpr(t: Expression): Option[List[(Name, Sort)]] = {
      val symbols = StaticSemantics.symbols(t)
      if (symbols.isEmpty) None
      else Some(StaticSemantics.symbols(t).map(s => Name(s.name, s.index) -> s.sort).toList)
    }
    Declaration(s.map({
      case SubstitutionPair(af: ApplicationOf, r) =>
        Name(af.func.name, af.func.index) -> Signature(Some(af.func.domain), af.func.sort, argsFromExpr(af.child), Some(r), UnknownLocation)
      case SubstitutionPair(s: SystemConst, r) =>
        Name(s.name, s.index) -> Signature(Some(Unit), s.sort, None, Some(r), UnknownLocation)
      case SubstitutionPair(s: ProgramConst, r) =>
        Name(s.name, s.index) -> Signature(Some(Unit), s.sort, None, Some(r), UnknownLocation)
    }).toMap)
  }

  /** Topologically sorts the names in `decls`. */
  def topSort(decls: Map[Name, Signature]): List[(Name, Signature)] = {
    val adjacencyMap = decls.map({ case (name, Signature(_, _, _, repl, _)) =>
      name -> repl.map(StaticSemantics.signature).map(_.map(ns => Name(ns.name, ns.index))).getOrElse(Set.empty) })
    val sortedNames = DependencyAnalysis.dfs[Name](adjacencyMap).reverse
    decls.toList.sortBy(s => sortedNames.indexOf(s._1))
  }

  def topSort(substs: List[SubstitutionPair]): List[SubstitutionPair] = {
    def namesOf(e: Expression): Set[Name] = StaticSemantics.signature(e).filterNot(_.isInstanceOf[DotTerm]).map(ns => Name(ns.name, ns.index))
    def uniqueNameOf(e: Expression): Name = {
      val names = namesOf(e)
      assert(names.size == 1)
      names.head
    }
    val adjacencyMap = substs.map({ case SubstitutionPair(what, repl) => uniqueNameOf(what) -> namesOf(repl) }).toMap
    val sortedNames = DependencyAnalysis.dfs[Name](adjacencyMap).reverse
    substs.sortBy({ case SubstitutionPair(what, _) => sortedNames.indexOf(uniqueNameOf(what)) })
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
  /** The model as sequent. */
  def sequent: Sequent = Sequent(
    scala.collection.immutable.IndexedSeq(),
    scala.collection.immutable.IndexedSeq(model.asInstanceOf[Formula]))
  /** Return an archive with modified problem contents, otherwise identical./ */
  def withProblemContent(newProblemContent: String): ParsedArchiveEntry = copy(problemContent = newProblemContent)
  /** Return an archive with modified file contents, otherwise identical./ */
  def withFileContent(newFileContent: String): ParsedArchiveEntry = copy(fileContent = newFileContent)
}

trait ArchiveParser extends (String => List[ParsedArchiveEntry]) {
  final override def apply(input: String): List[ParsedArchiveEntry] = parse(input)
  final def parse(input: String): List[ParsedArchiveEntry] = parse(input, parseTactics=true)
  final def parse(input: String, parseTactics: Boolean): List[ParsedArchiveEntry] = {
    val result = doParse(input, parseTactics).map(e =>
      if (e.defs.decls.isEmpty) ArchiveParser.elaborate(e.copy(defs = ArchiveParser.declarationsOf(e.model)))
      else ArchiveParser.elaborate(e)
    )
    result.foreach(_.annotations.foreach({ case (p: Program, f: Formula) => Parser.parser.annotationListener(p, f) }))
    result
  }
  protected def doParse(input: String, parseTactics: Boolean): List[ParsedArchiveEntry]
  /** Parses an archive from the source at path `file`. Use file#entry to refer to a specific entry in the file. */
  def parseFromFile(file: String): List[ParsedArchiveEntry] = {
    file.split('#').toList match {
      case fileName :: Nil =>
        val src = scala.io.Source.fromFile(fileName, edu.cmu.cs.ls.keymaerax.core.ENCODING)
        try {
          parse(src.mkString)
        } finally {
          src.close()
        }
      case fileName :: entryName :: Nil =>
        val src = scala.io.Source.fromFile(fileName, edu.cmu.cs.ls.keymaerax.core.ENCODING)
        try {
          getEntry(entryName, src.mkString).
            getOrElse(throw new IllegalArgumentException("Unknown archive entry " + entryName)) :: Nil
        } finally {
          src.close()
        }
    }
  }

  /** Returns the first entry in `input` as formula. */
  def parseAsFormula(input: String): Formula = parse(input, parseTactics=false).head.model.asInstanceOf[Formula]

  /** Returns the first entry in `input` as a formula with all definitions fully expanded. */
  def parseAsExpandedFormula(input: String): Formula = parse(input, parseTactics=false).head match {
    case ParsedArchiveEntry(_, _, _, _, defs, model, _, _, _) => defs.expandFull(model.asInstanceOf[Formula])
  }

  /** Returns the first entry in `in` as formula. */
  def parseAsFormula(in: InputStream): Formula = parseAsFormula(io.Source.fromInputStream(in).mkString)

  /** Reads a specific entry from the archive. */
  def getEntry(name: String, content: String, parseTactics: Boolean = true): Option[ParsedArchiveEntry] =
    parse(content, parseTactics).find(_.name == name)

  /** Parses a single entry. */
  def parseProblem(input: String, parseTactics: Boolean = true): ParsedArchiveEntry = {
    val entries = parse(input, parseTactics)
    if (entries.size == 1) entries.head
    else throw ParseException("Expected a single entry, but got " + entries.size, UnknownLocation)
  }

  /** Indicates whether or not the model represents an exercise. */
  def isExercise(model: String): Boolean = model.contains("__________")

  /** The expression parser used in this archive parser. */
  def exprParser: Parser

  /** The tactic parser used in this archive parser. */
  def tacticParser: TacticParser
}

object ArchiveParser extends ArchiveParser {
  /* @note mutable state for switching out the default parser. */
  private[this] var p: ArchiveParser = _

  /** The parser that is presently used per default. */
  def parser: ArchiveParser = {
    if (p != null) p
    else throw new ProverSetupException("No archive parser set. Please check the command line during startup for error messages.")
  }

  /** Set a new parser. */
  def setParser(parser: ArchiveParser): Unit = { p = parser }

  /** @inheritdoc */
  override protected def doParse(input: String, parseTactics: Boolean): List[ParsedArchiveEntry] = parser.doParse(input, parseTactics)

  /** @inheritdoc */
  override def parseFromFile(file: String): List[ParsedArchiveEntry] = parser.parseFromFile(file)

  /** @inheritdoc */
  override def exprParser: Parser = parser.exprParser

  /** @inheritdoc */
  override def tacticParser: TacticParser = parser.tacticParser

  private[parser] object BuiltinDefinitions {
    val defs: Declaration =
      InterpretedSymbols.builtin.map( f => {
        require(f.interpreted, "InterpretedSymbols should be interpreted but got: "+f)
        val dots = (1 to f.realDomainDim.get).map(i => (Name("\\cdot", Some(i)), Real : Sort)).toList

        Declaration(
          Map(Name(f.name, None) -> Signature(Some(f.domain), f.sort, Some(dots), f.interp, UnknownLocation))
        )
      }
      ).reduce(_ ++ _)
  }

  private[parser] object BuiltinAnnotationDefinitions {
    val defs: Declaration =
      Declaration(Map(Name("old", None) -> Signature(Some(Real), Real, Some(List((Name("\\cdot", None), Real))), None, UnknownLocation)))
  }

  /** Returns all symbols of `e` minus the explicitly quantified symbols (want to treat \forall x differently from [x:=...;]). */
  private def baseSymbols(e: Expression): Set[NamedSymbol] =
    (StaticSemantics.symbols(e) -- (e match {
      case _: Term => Set.empty // include all term symbols
      case f: Formula =>
        // exclude universally/existentially quantified symbols
        val quantifiedSymbols = scala.collection.mutable.Set.empty[Variable]
        ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
            case q: Quantified =>
              quantifiedSymbols ++= q.vars
              Left(None)
            case _ => Left(None)
          }
        }, f)
        val fv = StaticSemantics.freeVars(f)
        if (fv.isInfinite) Set.empty
        else quantifiedSymbols -- fv.toSet
      case _: Program => Set.empty // include all program symbols //@todo test with quantified formulas ?\exists y p(y)
      case _ => throw ParseException("Unknown expression " + e.prettyString + " of kind " + e.kind + " encountered when computing free base symbols", UnknownLocation)
    })).map({ case DifferentialSymbol(v) => v case s => s })

  /** All symbols (transitively) used from `e`, except explicitly quantified symbols. */
  def defsUsedIn(defs: Declaration, e: List[Expression], taboo: Set[Name]): Map[Name, Signature] = {
    val syms = e.flatMap(baseSymbols).map(s => Name(s.name, s.index)).toSet -- taboo
    defs.decls.flatMap({
      case e@(name, Signature(_, _, args, int, _)) =>
        //@note implicit definitions have not only args but also bind their own name
        if (syms.contains(name)) int.map(i => defsUsedIn(defs, List(i), taboo ++ args.map(_.map(_._1)).getOrElse(List.empty) + name)).getOrElse(Map.empty) + e
        else Map.empty[Name, Signature]
      case _ => Map.empty[Name, Signature]
    })
  }

  /** Elaborates variable uses of nullary function symbols in `entry` and its definitions/annotations, performs
    * DotTerm abstraction in entry definitions, and semantic/type analysis of the results. */
  def elaborate(entry: ParsedArchiveEntry): ParsedArchiveEntry = {
    val defsWithDotArgs = entry.defs.decls.filter({
      case (_, Signature(_, _, Some(args), _, _)) => args.exists(_._1.name == "\\cdot")
      case (_, Signature(_, _, None, _, _)) => false
    })
    if (defsWithDotArgs.nonEmpty) {
      val (name, Signature(_, _, _, _, loc)) = defsWithDotArgs.head
      throw ParseException("Definition " + name.prettyString + " uses unsupported anonymous (dot) arguments; please use named arguments (e.g., Real x) instead", loc)
    }

    val elaboratedDefs = elaborateDefs(entry.defs)

    val uses = elaboratedDefs.decls.map({
      case (name, Signature(_, _, args, int, loc)) => name -> ((args match {
        case Some(args) => int.map(baseSymbols(_).filterNot(n => args.contains((Name(n.name, n.index), n.sort))))
        case None => int.map(baseSymbols)
      }).getOrElse(Set.empty).groupBy(n => Name(n.name, n.index)), loc)
    })
    val inconsistentUses = uses.filter(_._2._1.exists(_._2.size > 1))
    if (inconsistentUses.nonEmpty) {
      val (name, (symbols, loc)) = inconsistentUses.head
      throw ParseException("Definition " + name.prettyString +
        " uses same name for " + symbols.map(_._2.map(_.fullString).mkString(" vs. ")), loc)
    }
    val locallyConsistentUses = uses.map({ case (k, (v, loc)) => k -> (v.map(_._2.head).toSet, loc) })

    val undeclaredUses = locallyConsistentUses.
      map({ case (n, (symbols, loc)) => n ->
        (symbols.
          filterNot(_.isInstanceOf[DotTerm]).
          filter(s => !elaboratedDefs.decls.contains(Name(s.name, s.index))).
          filterNot(ReservedSymbols.reserved.contains).
          filterNot(InterpretedSymbols.builtin.contains).
          filterNot(TacticReservedSymbols.symbols.contains), loc) }).
      filter({ case (_, (s, _)) => s.nonEmpty })
    if (undeclaredUses.nonEmpty) {
      val (name, (symbols, loc)) = undeclaredUses.head
      throw ParseException("Definition " + name.prettyString + " uses undefined symbol(s) " +
        symbols.toList.sortBy(_.name).map(_.prettyString).mkString(",") + ". Please add arguments or define as functions/predicates/programs", loc)
    }

    val inconsistentWithDecls = locallyConsistentUses.
      map({ case (k, (used, loc)) => k -> (used.map(n => n -> elaboratedDefs.decls.get(Name(n.name, n.index))), loc) }).
      filter({ case (_, (symbols, _)) => symbols.exists({ case (use, decl) => decl.exists({
        case Signature(domain, sort, _, _, _) => use match {
          case fn: Function => fn.sort != sort || !domain.contains(fn.domain)
          case _ => false
        }
      }) }) })
    if (inconsistentWithDecls.nonEmpty) {
      val (name, (symbols, loc)) = inconsistentWithDecls.head
      throw ParseException("Definition " + name.prettyString +
        " uses " + symbols.map({ case (s, d) => s.fullString + " inconsistent with definition " +
        s.prettyString + d.map(s => ":" + s.domain.map(_ + "->").getOrElse("") + s.codomain).getOrElse("") }), loc)
    }

    // elaborate model and check
    val elaboratedModel = try {
      elaboratedDefs.implicitSubst(elaboratedDefs.elaborateToSystemConsts(elaboratedDefs.elaborateToFunctions(entry.model)))
    } catch {
      case ex: AssertionError => throw ParseException(ex.getMessage, ex)
    }
    val fullyExpandedModel = try {
      elaboratedDefs.exhaustiveSubst(elaboratedModel)
    } catch {
      case ex: AssertionError => throw ParseException(ex.getMessage, ex)
    }
    Parser.semanticAnalysis(fullyExpandedModel).toList match {
      case Nil =>
      case ambiguous =>
        val msg =
          "semantics: Expect unique names_index that identify a unique type." +
            "\nambiguous: " + ambiguous.map(_.fullString).mkString(" and ")
        throw ParseException("Semantic analysis error\n" + msg, UnknownLocation,
          ambiguous.map(_.fullString).mkString(" and "), "unambiguous type")
    }
    //@note bare formula input without any definitions uses default meaning of symbols
    if (elaboratedDefs.decls.nonEmpty) typeAnalysis(entry.name, entry.defs ++ BuiltinDefinitions.defs, elaboratedModel) //throws ParseExceptions.
    checkUseDefMatch(elaboratedModel, elaboratedDefs)

    // analyze and report annotations
    val elaboratedAnnotations = elaborateAnnotations(entry.annotations, elaboratedDefs)
    elaboratedAnnotations.distinct.foreach({
      case (e: Program, a: Formula) =>
        if (elaboratedDefs.decls.nonEmpty) typeAnalysis(entry.name, elaboratedDefs ++ BuiltinDefinitions.defs ++ BuiltinAnnotationDefinitions.defs, a)
        else typeAnalysis(entry.name, declarationsOf(entry.model) ++ BuiltinDefinitions.defs ++ BuiltinAnnotationDefinitions.defs, a)
      case (_: Program, a) => throw ParseException("Unsupported annotation " + a.prettyString + " of kind " + a.kind +
        " encountered, please provide a formula", UnknownLocation)
      case (e, a) => throw ParseException("Annotation " + a.prettyString + " on " + e.prettyString + " of kind " +
        e.kind + " not supported, please annotate programs only", UnknownLocation)
    })

    entry.copy(
      model = elaboratedModel,
      defs = elaboratedDefs.elaborateWithDots,
      annotations = elaboratedAnnotations
    )
  }

  /** Checks that uses in `problem` match the declarations.
    * @throws [[ParseException]] on use-def mismatch.
    */
  private def checkUseDefMatch(problem: Expression, defs: Declaration): Unit = {
    // check that definitions and use match
    val symbols = StaticSemantics.symbols(problem) ++ defs.substs.flatMap(s => StaticSemantics.symbols(s.repl))
    val defSymbols = defs.substs.map(_.what)
    val mismatches = defSymbols.map({
      case n: NamedSymbol => symbols.find(u => u.name == n.name && u.index == n.index && u.kind != n.kind).map(n -> _)
      case _ => None
    }).filter(_.isDefined).map(_.get)
    if (mismatches.nonEmpty) {
      val mismatchDescription = mismatches.map({ case (defSym, sym) =>
        "Symbol '" + defSym.prettyString + "' defined as " + defSym.kind +
          ", but used as " + sym.kind + " in " + sym.prettyString
      }).mkString("\n")
      val found = mismatches.map({ case (_, sym) => sym.prettyString }).mkString(", ")
      val expected = mismatches.map({ case (defSym, _) => defSym.prettyString }).mkString(", ")
      throw new ParseException("All definitions and uses must match, but found the following mismatches:\n" +
        mismatchDescription, UnknownLocation, found, expected, "", "")
    }
  }


  /** Elaborates to functions in annotations.
    * @param annotations the annotations to elaborate
    * @param defs lists functions to elaborate to
    * @throws [[ParseException]] if annotations are not formulas, not attached to programs, or type analysis of annotations fails
    * */
  private def elaborateAnnotations(annotations: List[(Expression, Expression)], defs: Declaration): List[(Expression, Expression)] = {
    annotations.map({
      case (e: Program, a: Formula) =>
        val substPrg = defs.elaborateToSystemConsts(defs.elaborateToFunctions(e))
        val substFml = defs.elaborateToSystemConsts(defs.elaborateToFunctions(a))
        (substPrg, substFml)
      case (_: Program, a) => throw ParseException("Annotation must be formula, but got " + a.prettyString, UnknownLocation)
      case (e, _) => throw ParseException("Annotation on programs only, but was on " + e.prettyString, UnknownLocation)
    })
  }


  /** Expands definitions in annotations to create fully expanded annotations. */
  private def expandAnnotations(annotations: List[(Expression, Expression)], defs: Declaration): List[(Expression, Expression)] = {
    annotations.map({
      case (e: Program, a: Formula) =>
        val substPrg = defs.exhaustiveSubst(defs.elaborateToFunctions(e))
        val substFml = defs.exhaustiveSubst(defs.elaborateToFunctions(a))
        (substPrg, substFml)
      case (_: Program, a) => throw ParseException("Annotation must be formula, but got " + a.prettyString, UnknownLocation)
      case (e, _) => throw ParseException("Annotation on programs only, but was on " + e.prettyString, UnknownLocation)
    })
  }

  /** Extracts declarations per static semantics of the expression `parsedContent`. */
  def declarationsOf(parsedContent: Expression, filter: Option[Set[NamedSymbol]] = None): Declaration = {
    def makeArgsList(args: Term): List[(Name, Sort)] = args match {
      case Pair(l, r) => makeArgsList(l) ++ makeArgsList(r)
      case FuncOf(n, _) => List(Name(n.name, n.index) -> n.sort)
      case n: NamedSymbol => List(Name(n.name, n.index) -> n.sort)
      case _ => List() //@note unable to guess argument name from general terms x+y
    }

    val collectedArgs = scala.collection.mutable.Map.empty[NamedSymbol, List[(Name, Sort)]]
    def collect(fn: Function, args: Term): Unit = {
      InterpretedSymbols.byName.get((fn.name, fn.index)) match {
        case None =>
          if (filter.isEmpty || filter.get.contains(fn)) {
            if (!collectedArgs.contains(fn)) collectedArgs(fn) = makeArgsList(args)
            else assert(collectedArgs(fn) == makeArgsList(args), "Expected consistent arguments to " + fn.prettyString +
              " everywhere, but found " + collectedArgs(fn).mkString(",") + " vs. " + makeArgsList(args).mkString(","))
          }
        case Some(_) => // nothing to do, builtin interpreted symbols do not need to be declared
      }
    }

    ExpressionTraversal.traverseExpr(new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case FuncOf(fn, args) =>
          collect(fn, args)
          Left(None)
        case _ => Left(None)
      }
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case PredOf(fn, args) =>
          collect(fn, args)
          Left(None)
        case _ => Left(None)
      }
    }, parsedContent)

    val symbols = StaticSemantics.symbols(parsedContent)
    val fnDecls = symbols.filterNot(InterpretedSymbols.builtin.contains).filter(_.isInstanceOf[Function]).map(_.asInstanceOf[Function]).map(fn =>
      Name(fn.name, fn.index) -> Signature(Some(fn.domain), fn.sort, collectedArgs.get(fn), None, UnknownLocation)
    ).toMap
    val varDecls = symbols.filter(_.isInstanceOf[BaseVariable]).map(v =>
      Name(v.name, v.index) -> Signature(None, v.sort, None, None, UnknownLocation)
    ).toMap
    Declaration(fnDecls ++ varDecls)
  }

  /** Elaborates variables to function symbols and program constants to system constants in definitions `defs`. */
  def elaborateDefs(defs: Declaration): Declaration = {
    def taboos(signature: List[(Name, Sort)]): Set[Function] = signature.
      filter({ case (Name(name, _), _) => name != "\\cdot" }).
      map({ case(Name(name, idx), sort) => Function(name, idx, Unit, sort) }).toSet

    val inconsistentDecls = defs.decls.
      map({ case (n, Signature(_, _, _, i, loc)) =>
        (n, loc) -> i.map(baseSymbols(_).groupBy(n => Name(n.name, n.index))).getOrElse(Map.empty) }).
      filter({ case (_, symbols) => symbols.exists(_._2.size > 1) })
    if (inconsistentDecls.nonEmpty) {
      val loc = if (inconsistentDecls.size == 1) inconsistentDecls.head._1._2 else UnknownLocation
      throw ParseException(inconsistentDecls.map({ case ((name, loc), symbols) => "Definition " + name.prettyString + " at " + loc +
        " uses names inconsistently\n" + symbols.map({ case (_, s) => "  " + s.map(_.fullString).mkString(" vs. ") }).mkString("\n") }).mkString("\n"), loc)
    }

    def elaborateToDifferentials(e: Expression): Expression = {
      val ds = StaticSemantics.symbols(e).filter(_.isInstanceOf[DifferentialSymbol]).map(_.asInstanceOf[DifferentialSymbol])
      ds.foldLeft(e)({ case (e, n) => e.replaceFree(n, Differential(n.x)) })
    }

    val elab = ListBuffer.empty[(Name, Signature)]
    val remainder = scala.collection.mutable.Map(defs.decls.toSeq:_*)
    defs.copy(decls = Declaration.topSort(defs.decls).map({ case (name, sig@Signature(_, sort, argNames, interpretation, loc)) =>
      val r = (name, sig.copy(interpretation = interpretation.map(i => {
        //@note use already elaborated symbols instead of original symbols
        val d = Declaration(elab.toMap ++ remainder)
        val elaborated = d.elaborateToSystemConsts(d.elaborateToFunctions(elaborateToDifferentials(i), taboos(argNames.getOrElse(Nil))))
        if (elaborated.sort != sort) throw ParseException("Definition " + name.prettyString + " does not fit declared sort " + sort + "; right-hand side is of sort " + elaborated.sort, loc)
        elaborated
      })))
      elab += r
      remainder.remove(name)
      r
    }).toMap)
  }

  /**
    * Type analysis of expression according to the given type declarations decls
    * @param name the entry name (for error messages)
    * @param d the type declarations known from the context (e.g., as parsed from the Definitions and ProgramVariables block of an entry)
    * @param expr the expression to analyze
    * @throws [[edu.cmu.cs.ls.keymaerax.parser.ParseException]] if the type analysis fails.
    */
  def typeAnalysis(name: String, d: Declaration, expr: Expression): Boolean = {
    StaticSemantics.symbols(expr).filterNot(TacticReservedSymbols.symbols.contains(_)).filterNot(InterpretedSymbols.builtin.contains(_)).forall({
      case f: Function =>
        val Signature(declaredDomain, declaredSort, _, _, loc: Location) = d.decls.get(Name(f.name,f.index)) match {
          case Some(decl) => decl
          case None => throw ParseException.typeError(name + ": undefined function symbol", f, f.sort + "", UnknownLocation,
            "Make sure to declare all variables in ProgramVariables and all symbols in Definitions block.")
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
      case DifferentialSymbol(v) => d.decls.contains(Name(v.name, v.index)) //@note hence it is checked as variable already
      case x: Variable =>
        if (quantifiedVars(expr).contains(x)) true //Allow all undeclared variables if they are at some point bound by a \forall or \exists. @todo this is an approximation. Should only allow quantifier bindings...
        else {
          val (declaredSort, declLoc) = d.decls.get(Name(x.name, x.index)) match {
            case Some(Signature(None, sort, _, _, loc)) => (sort, loc)
            case Some(Signature(Some(domain), sort, _, _, loc)) =>
              throw ParseException.typeDeclError(s"$name: ${x.name} was declared as a function but must be a variable when it is assigned to or has a differential equation.",
                x.prettyString + ": " + domain + "->" + sort + " Function", "Real " + x.prettyString, loc)
            case None => throw ParseException.typeDeclGuessError(name + ": undefined symbol " + x.prettyString,
              "undefined symbol " + x.prettyString, "Real " + x.prettyString, UnknownLocation,
              "Add \"Real " + x.prettyString + ";\" to the ProgramVariables block")
          }
          if (x.sort != declaredSort) throw ParseException.typeDeclGuessError(s"$name: ${x.prettyString} declared with sort $declaredSort but used where a ${x.sort} was expected.",
            declaredSort + x.prettyString, x.sort + " " + x.prettyString, declLoc)
          x.sort == declaredSort
        }
      case _: UnitPredicational => true //@note needs not be declared
      case _: UnitFunctional => true //@note needs not be declared
      case _: DotTerm => true //@note needs not be declared
      case _ => false
    })
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
}