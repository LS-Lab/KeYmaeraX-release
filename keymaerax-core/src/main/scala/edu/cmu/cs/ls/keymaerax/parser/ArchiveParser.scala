/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

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

/**
 * Signature is a domain sort, codomain sort, argument names, expression used as interpretation, location that starts
 * the declaration. The signature of a function/predicate/program symbol.
 * @param domain
 *   the source domain required as an argument (if any).
 * @param codomain
 *   the resulting target domain.
 * @param arguments
 *   the list of named arguments (and their sorts which are compatible with `domain`).
 * @param interpretation
 *   Left(implicitly) defined interpreted symbol, or uninterpreted symbol if Right(None), or Right(explicitly) defined
 *   interpreted symbols.
 * @param loc
 *   the location in the model archive file where this was declared.
 */
//@todo check whether domain sort is compatible with sorts of arguments
case class Signature(
    domain: Option[Sort],
    codomain: Sort,
    arguments: Option[List[(Name, Sort)]],
    interpretation: Either[Formula, Option[Expression]],
    loc: Location,
)

object Signature {
  def variable(loc: Location = UnknownLocation): Signature = Signature(None, Real, None, Right(None), loc)
  def const(loc: Location = UnknownLocation): Signature =
    Signature(Some(Unit), Real, Some(List.empty), Right(None), loc)
}

/**
 * A parsed declaration, which assigns a signature to names. This is the central data structure remembering which name
 * belongs to which function/predicate/program symbol declaration of a model in an archive.
 */
case class Declaration(decls: Map[Name, Signature]) {

  /** The declarations as topologically sorted substitution pairs. */
  lazy val substs: List[SubstitutionPair] = Declaration
    .topSort(
      decls
        .filter(_._2.interpretation match {
          case Right(Some(ns: NamedSymbol)) => !ReservedSymbols.reserved.contains(ns)
          case Right(i) => i.isDefined
          // implicitly defined interpreted symbols are not substitutions
//    case _ => false
          case Left(_) => true
        })
        .map({ case (name, sig @ Signature(_, _, args, interpretation, _)) =>
          // except named arguments and dots, elaborate all symbols to functions for topSort because topSort uses signature
          val taboo = args
            .map(
              _.filter({
                  case (Name("\\cdot", _), _) => false
                  case _ => true
                })
                .map({ case (Name(n, i), sort) => Function(n, i, Unit, sort) })
                .toSet
            )
            .getOrElse(Set.empty)
          (
            name,
            sig.copy(interpretation =
              interpretation.map(_.map(e => elaborateToSystemConsts(elaborateToFunctions(e, taboo))))
            ),
          )
        })
    )
    .map((declAsSubstitutionPair _).tupled)

  /** The subset of substs for implicitly defined functions (have what.name == repl.name and repl.interpreted). */
  lazy val isubsts: List[SubstitutionPair] = substs.filter({ case SubstitutionPair(what, repl) =>
    (what, repl) match {
      case (FuncOf(e, _), FuncOf(f, _)) =>
        // @note filter out definitions that just forward implicitly defined functions, e.g., Real f(x,y) = min(x,y);
        e.name == f.name && e.index == f.index && e.domain == f.domain && e.sort == f.sort && f.interpreted
      case _ => false
    }
  })

  /** Returns the substitutions reachable transitively from symbols `s`. */
  def transitiveSubstsFrom(e: Expression): List[SubstitutionPair] = {
    val s = StaticSemantics.symbols(e).filterNot(_.isInstanceOf[DotTerm])
    val expand = substs.filter(sp => StaticSemantics.symbols(sp.what).intersect(s).nonEmpty)
    val also = expand.flatMap(sp => transitiveSubstsFrom(sp.repl))
    Declaration.topSort(also ++ expand)
  }

  /** Substitution applying all definitions non-recursively (i.e., one level of substitution). */
  lazy val subst: USubst = USubst(substs)

  /** Declared names and signatures as [[NamedSymbol]]. */
  lazy val asNamedSymbols: List[NamedSymbol] = {
    Declaration
      .topSort(decls)
      .reverseIterator
      .map(decl =>
        Declaration.asNamedSymbol(
          decl._1,
          decl
            ._2
            .copy(interpretation = decl._2.interpretation match {
              case Left(f) => Left(elaborateToSystemConsts(f))
              case Right(e) => Right(e.map(elaborateToSystemConsts))
            }),
        )
      )
      .toList
  }

  /** Joins two declarations. */
  def ++(other: Declaration): Declaration = {
    val keyClashes = decls
      .keySet
      .intersect(other.decls.keySet)
      .flatMap(n => {
        if (decls(n) == other.decls(n)) None
        else (decls(n), other.decls(n)) match {
          case (Signature(td, ts, ta, ti, _), Signature(od, os, oa, oi, _))
              if td != od || ts != os || ta.size != oa.size || ti != oi => Some(n)
          case _ => None
        }
      })
    require(
      keyClashes.isEmpty,
      "Expected unique definitions, but got contradictory definitions for names " +
        keyClashes.map(_.prettyString).mkString(","),
    )
    Declaration(decls ++ other.decls)
  }

  /** Adds the elements of `other` that are not contained in this declaration. */
  def addNew(other: Declaration): Declaration = {
    this ++ Declaration(other.decls.filterNot({ case (n, _) => decls.contains(n) }))
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
  def exhaustiveSubst[T <: Expression](arg: T): T =
    try { elaborateToFunctions(arg.exhaustiveSubst(USubst(substs))).asInstanceOf[T] }
    catch {
      case ex: SubstitutionClashException =>
        throw ParseException("Definition " + ex.context + " as " + ex.e + " must declare arguments " + ex.clashes, ex)
    }

  /** Applies substitutions per `substs` exhaustively to sequent `s`. */
  def exhaustiveSubst(s: Sequent): Sequent =
    Sequent(s.ante.map(exhaustiveSubst[Formula]), s.succ.map(exhaustiveSubst[Formula]))

  /** Applies implicit definition substitutions to expression-like `arg`. */
  def implicitSubst[T <: Expression](arg: T): T = arg match {
    case _: Function => arg // @note no substitutions on unapplied functions
    case _ =>
      try { if (isubsts.nonEmpty) USubst(isubsts)(arg).asInstanceOf[T] else arg }
      catch {
        case ex: SubstitutionClashException =>
          throw ParseException("Definition " + ex.context + " as " + ex.e + " must declare arguments " + ex.clashes, ex)
      }
  }

  /** Applies implicit definition substitutions to sequent `s`. */
  def implicitSubst(s: Sequent): Sequent = if (isubsts.nonEmpty) USubst(isubsts)(s) else s

  /** Expands all symbols in expression `arg` fully. */
  def expandFull[T <: Expression](arg: T): T =
    try { exhaustiveSubst(implicitSubst(elaborateToFunctions(elaborateToSystemConsts(arg)))) }
    catch {
      case ex: SubstitutionClashException =>
        throw ParseException("Definition " + ex.context + " as " + ex.e + " must declare arguments " + ex.clashes, ex)
    }

  /** Elaborates the expression `expr` fully (functions, constants, builtin/imported functions), but does not expand. */
  def elaborateFull[T <: Expression](expr: T): T = implicitSubst(elaborateToSystemConsts(elaborateToFunctions(expr)))

  /**
   * Elaborates variable uses of declared functions, except those listed in taboo. Also elaborates [[FuncOf]] to
   * [[PredOf]] per sort in `decls`.
   */
  // @todo need to look into concrete programs that implement program constants when elaborating
  def elaborateToFunctions[T <: Expression](expr: T, taboo: Set[Function] = Set.empty): T =
    try { expr.elaborateToFunctions(asNamedSymbols.toSet -- taboo).asInstanceOf[T] }
    catch {
      case ex: ElaborationError => (BuiltinSymbols.all.asNamedSymbols.toSet -- taboo)
          .find(n => n.name == ex.v.name && n.index == ex.v.index) match {
          case Some(f) => throw ParseException(
              "Name " + ex.v + " has builtin meaning as an interpreted function " + f.prettyString +
                ", so cannot be used as a variable",
              ex,
            )
          case None => throw ParseException("Unable to elaborate to function symbols: " + ex.getMessage, ex)
        }
    }

  /** Elaborates program constants to system constants if their definition is dual-free. */
  def elaborateToSystemConsts[T <: Expression](expr: T): T = {
    val elaborator = new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case ProgramConst(name, space) => decls.find(_._1.name == name).map(_._2.interpretation) match {
            case Some(Right(Some(prg: Program))) =>
              if (FormulaTools.dualFree(prg)) Right(SystemConst(name, space)) else Left(None)
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
  def elaborateWithDots: Declaration = Declaration(decls.map(d => Declaration.elaborateWithDots(d._1, d._2)))

  /** Turns a function declaration (with defined body) into a substitution pair. */
  private def declAsSubstitutionPair(name: Name, signature: Signature): SubstitutionPair = {
    // @todo Function interpretation would also need to keep track of differentiable yes/no
    // require(signature.interpretation.isRight && signature.interpretation.right.get.isDefined, "Substitution only for defined functions")
    // val (_, Signature(domain, sort, args, Right(Some(interpretation)), loc)) = Declaration.elaborateWithDots(name, signature)

    // Transforms list `args` of dotted name into a term with DotTerm
    def dotArg(domain: Sort, args: Option[List[(Name, Sort)]]): Term = domain match {
      case Unit => Nothing
      case s: Tuple =>
        assert(args.nonEmpty && args.get.size > 1)
        val idxs = args.get.map(_._1.index.get)
        val dotTerm = s.toDots(idxs)._1
        assert(s.toDots(idxs)._2.isEmpty)
        assert(Declaration.dotsOf(dotTerm).map(_.index.get) == idxs.toSet)
        dotTerm
      case Real =>
        assert(args.nonEmpty && args.get.size == 1)
        DotTerm(Real, args.get.head._1.index)
    }

    val (domain, sort, args, interpretation, loc) = Declaration.elaborateWithDots(name, signature) match {
      case (_, Signature(domain, sort, args, Right(Some(interpretation)), loc)) =>
        (domain.getOrElse(Unit), sort, args, interpretation, loc)
      case (Name(n, i), Signature(domain, sort, args, Left(interpretation), loc)) =>
        val dottedArg = dotArg(domain.getOrElse(Unit), args)
        (
          domain.getOrElse(Unit),
          sort,
          args,
          FuncOf(Function(n, i, domain.getOrElse(Unit), sort, Some(interpretation)), dottedArg),
          loc,
        )
    }

    val dottedArg = dotArg(domain, args)
    val what = sort match {
      case Real => FuncOf(Function(name.name, name.index, domain, signature.codomain), dottedArg)
      case Bool => PredOf(Function(name.name, name.index, domain, signature.codomain), dottedArg)
      case Trafo =>
        assert(name.index.isEmpty, "Expected no index in program const name, but got " + name.index)
        assert(
          signature.domain.getOrElse(Unit) == Unit,
          "Expected domain Unit in program const signature, but got " + signature.domain,
        )
        interpretation match {
          case prg: Program => if (FormulaTools.dualFree(prg)) SystemConst(name.name) else ProgramConst(name.name)
          case e => throw ParseException("Definition of " + name.name + " is not a program, but a " + e.kind, loc)
        }
      case _ => throw ParseException(
          "Unknown sort " + sort + " encountered when converting definition to substitution pair",
          loc,
        )
    }
    val repl = elaborateToFunctions(interpretation) match {
      case r @ FuncOf(fn: Function, c) =>
        if (what.sort == fn.sort) r else PredOf(Function(fn.name, fn.index, fn.domain, what.sort), c)
      case p @ PredOf(fn: Function, c) =>
        if (what.sort == fn.sort) p else FuncOf(Function(fn.name, fn.index, fn.domain, what.sort), c)
      case r => r
    }

    // @note ._0 is output of interpreted functions
    val undeclaredDots = Declaration.dotsOf(repl) /*- DotTerm(Real, Some(0))*/ -- Declaration.dotsOf(dottedArg)
    if (undeclaredDots.nonEmpty) {
      val undeclaredDotsStr = undeclaredDots.map(_.prettyString).mkString(",")
      throw ParseException(
        s"Function/predicate ${what.prettyString} uses undeclared dot(s) $undeclaredDotsStr",
        UnknownLocation,
      )
    }

    SubstitutionPair(what, repl)
  }

  /**
   * All symbols of this declaration used (transitively) from `e`, except when explicitly quantified symbols or `taboo`.
   */
  def project(e: List[Expression], taboo: Set[Name] = Set.empty): Declaration = {
    val syms = e.flatMap(_.baseSymbols).map(s => Name(s.name, s.index)).toSet -- taboo
    Declaration(decls.flatMap({
      case e @ (name, Signature(_, _, args, Left(int), _)) =>
        if (syms.contains(name)) project(List(int), taboo ++ args.map(_.map(_._1)).getOrElse(List.empty)).decls + e
        else Map.empty[Name, Signature]
      case e @ (name, Signature(_, _, args, Right(int), _)) =>
        // @note implicit definitions have not only args but also bind their own name
        // Otherwise, the resulting Declaration will have a duplicate signature for `name`
        if (syms.contains(name)) int
          .map(i => project(List(i), taboo ++ args.map(_.map(_._1)).getOrElse(List.empty) + name))
          .getOrElse(Declaration(Map.empty))
          .decls + e
        else Map.empty[Name, Signature]
      case _ => Map.empty[Name, Signature]
    }))
  }
}

object Declaration {

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
      case _ => throw ParseException(
          "Unknown expression " + e.prettyString + " of kind " + e.kind + " encountered when dotifying",
          UnknownLocation,
        )
    }
    dots.toSet
  }

  /** Elaborates the argument and the interpretation in `signature` to dots. */
  def elaborateWithDots(name: Name, signature: Signature): (Name, Signature) = signature.interpretation match {
    case Right(None) => (name, signature)
    case interpretation => signature.arguments match {
        case None => (name, signature)
        case Some((Name(Nothing.name, Nothing.index), Unit) :: Nil) => (name, signature)
        // If the signature is already written with anonymous arguments (i.e. dots), no elaboration is required
        case Some(argNames) if argNames.forall({ case (n, _) => n.name == DotTerm().name }) => (name, signature)
        case Some(argNames) =>
          // Having a mix of anonymous and concrete arguments is not handled, and probably bad practice anyway
          assert(argNames.forall({ case (n, _) => n.name != DotTerm().name }))
          val interpDots = interpretation match {
            case Right(Some(fn @ FuncOf(Function(_, _, _, _, Some(i)), _))) =>
              (StaticSemantics.symbols(fn) ++ StaticSemantics.symbols(i)).filter(_.isInstanceOf[DotTerm])
            case Right(Some(e)) => StaticSemantics.symbols(e).filter(_.isInstanceOf[DotTerm])
            case Left(e) => StaticSemantics.symbols(e).filter(_.isInstanceOf[DotTerm])
            case _ => Set.empty
          }

          def nextDotI(dots: Set[_ <: NamedSymbol]): Int =
            if (dots.nonEmpty) dots.maxBy(_.index).index.map(_ + 1).getOrElse(0) else 0

          val dotTerms = argNames
            .zipWithIndex
            .map({ case (v, i) => v -> DotTerm(v._2, Some(i + nextDotI(interpDots))) })
          val dottedArg = dotTerms.map({ case ((_, s), d) => (Name(d.name, d.index), s) })
          val dottedInterpretation = dotTerms.foldRight(interpretation)({
            case (((Name(name, index), sort), dot), dotted) => dotted match {
                case Left(f) => Left(
                    f.replaceFree(Variable(name, index, sort), dot)
                      .replaceFree(Differential(Variable(name, index, sort)), Differential(dot))
                  )
                case Right(e) => Right(e.map(
                    _.replaceFree(Variable(name, index, sort), dot)
                      .replaceFree(Differential(Variable(name, index, sort)), Differential(dot))
                  ))
              }
          })
          (name, signature.copy(arguments = Some(dottedArg), interpretation = dottedInterpretation))
      }
  }

  /** Converts name `n` with signature `s` to a named symbol. */
  def asNamedSymbol(n: Name, s: Signature): NamedSymbol = (n, s) match {
    case (n @ Name(name, idx), s @ Signature(domain, sort, args, interp, _)) => sort match {
        case Real | Bool =>
          if (domain.isEmpty) Variable(name, idx, sort)
          else elaborateWithDots(n, s)._2.interpretation match {
            case Right(Some(f: Formula)) =>
              if (sort == Real) Function(name, idx, domain.get, sort, Some(f))
              else
                Function(
                  name,
                  idx,
                  domain.get,
                  sort,
                ) // @note predicate with a substitution definition (not interpreted)
            case Right(Some(FuncOf(fn, _))) if fn.name == n.name && fn.index == n.index => fn
            case Right(Some(_: Term)) => Function(name, idx, domain.get, sort)
            // Function(name, idx, domain.get, sort, Some(Equal(DotTerm(Real, Some(0)), t)))
            case Right(None) => Function(name, idx, domain.get, sort)
            case Left(f) => Function(name, idx, domain.get, sort, Some(f))
          }
        case Trafo =>
          assert(idx.isEmpty, "Program/system constants are not allowed to have an index, but got " + name + "_" + idx)
          interp match {
            case Right(Some(p: Program)) if FormulaTools.dualFree(p) => SystemConst(name)
            case Right(_) => ProgramConst(name)
          }
      }
  }

  /** Converts a list of substitution pairs `s` into a declaration, using the argument names of definitions in `ref`. */
  def fromSubst(s: List[SubstitutionPair], ref: Declaration): Declaration = {
    def argsFromExpr(t: Expression): Option[List[(Name, Sort)]] = {
      val symbols = StaticSemantics.symbols(t)
      if (symbols.isEmpty) None else Some(StaticSemantics.symbols(t).map(s => Name(s.name, s.index) -> s.sort).toList)
    }
    Declaration(
      s.map({
          case SubstitutionPair(af: ApplicationOf, r) =>
            val (args, interp) = argsFromExpr(af.child) match {
              case None => (None, Some(r))
              case Some(a) => ref.decls.get(Name(af.func.name, af.func.index)) match {
                  case Some(refSig) => refSig.arguments match {
                      case None => (Some(a), Some(r))
                      case Some(ra) =>
                        val foo = a
                          .zip(ra)
                          .foldLeft(r)({
                            case (e, ((Name(wn, wi), ws), (Name(rn, ri), rs))) if rs == ws =>
                              e.replaceFree(
                                if (wn == DotTerm().name) DotTerm(ws, wi) else Variable(wn, wi),
                                Variable(rn, ri),
                              )
                            case (e, _) => e
                          })
                        (Some(ra), Some(foo))
                    }
                  case None => (Some(a), Some(r))
                }
            }
            Name(af.func.name, af.func.index) ->
              Signature(Some(af.func.domain), af.func.sort, args, Right(interp), UnknownLocation)
          case SubstitutionPair(s: AtomicProgram with NamedSymbol, r) => Name(s.name, s.index) ->
              Signature(Some(Unit), s.sort, None, Right(Some(r)), UnknownLocation)
        })
        .toMap
    )
  }

  /** Topologically sorts the names in `decls`. */
  def topSort(decls: Map[Name, Signature]): List[(Name, Signature)] = {
    val adjacencyMap = decls.map({
      case (name, Signature(_, _, _, Right(interp), _)) => name ->
          interp.map(StaticSemantics.signature).map(_.map(ns => Name(ns.name, ns.index))).getOrElse(Set.empty)
      case (name, Signature(_, _, _, Left(interp), _)) => name ->
          StaticSemantics.signature(interp).map(ns => Name(ns.name, ns.index))
    })
    val sortedNames = DependencyAnalysis.dfs[Name](adjacencyMap).reverse
    decls.toList.sortBy(s => sortedNames.indexOf(s._1))
  }

  def topSort(substs: List[SubstitutionPair]): List[SubstitutionPair] = {
    def namesOf(e: Expression): Set[Name] = StaticSemantics
      .signature(e)
      .filterNot(_.isInstanceOf[DotTerm])
      .map(ns => Name(ns.name, ns.index))
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
case class ParsedArchiveEntry(
    name: String,
    kind: String,
    fileContent: String,
    problemContent: String,
    defs: Declaration,
    model: Expression,
    tactics: List[(String, String, BelleExpr)],
    annotations: List[(Expression, Expression)],
    info: Map[String, String],
) {

  /** True if this entry is an exercise, false otherwise. */
  def isExercise: Boolean = kind == "exercise"

  /** The model with all definitions expanded. */
  def expandedModel: Expression = defs.exhaustiveSubst(model)

  /** The model as sequent. */
  def sequent: Sequent =
    Sequent(scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(model.asInstanceOf[Formula]))

  /** Return an archive with modified problem contents, otherwise identical./ */
  def withProblemContent(newProblemContent: String): ParsedArchiveEntry = copy(problemContent = newProblemContent)

  /** Return an archive with modified file contents, otherwise identical./ */
  def withFileContent(newFileContent: String): ParsedArchiveEntry = copy(fileContent = newFileContent)
}

trait ArchiveParser extends (String => List[ParsedArchiveEntry]) {
  final override def apply(input: String): List[ParsedArchiveEntry] = parse(input)
  final def parse(input: String): List[ParsedArchiveEntry] = parse(input, parseTactics = true)
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
        try { parse(src.mkString) }
        finally { src.close() }
      case fileName :: entryName :: Nil =>
        val src = scala.io.Source.fromFile(fileName, edu.cmu.cs.ls.keymaerax.core.ENCODING)
        try {
          getEntry(entryName, src.mkString)
            .getOrElse(throw new IllegalArgumentException("Unknown archive entry " + entryName)) :: Nil
        } finally { src.close() }
    }
  }

  /** Returns the first entry in `input` as formula. */
  def parseAsFormula(input: String): Formula = parse(input, parseTactics = false).head.model.asInstanceOf[Formula]

  /** Returns the first entry in `input` as a formula with all definitions fully expanded. */
  def parseAsExpandedFormula(input: String): Formula = parse(input, parseTactics = false).head match {
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

  /** A parser for definitions package files. */
  def definitionsPackageParser: String => Declaration
}

object ArchiveParser extends ArchiveParser {
  /* @note mutable state for switching out the default parser. */
  private[this] var p: ArchiveParser = _

  /** The parser that is presently used per default. */
  def parser: ArchiveParser = {
    if (p != null) p
    else throw new ProverSetupException(
      "No archive parser set. Please check the command line during startup for error messages."
    )
  }

  /** Set a new parser. */
  def setParser(parser: ArchiveParser): Unit = { p = parser }

  /** @inheritdoc */
  override protected def doParse(input: String, parseTactics: Boolean): List[ParsedArchiveEntry] = parser
    .doParse(input, parseTactics)

  /** @inheritdoc */
  override def parseFromFile(file: String): List[ParsedArchiveEntry] = parser.parseFromFile(file)

  /** @inheritdoc */
  override def exprParser: Parser = parser.exprParser

  /** @inheritdoc */
  override def tacticParser: TacticParser = parser.tacticParser

  /** @inheritdoc */
  override def definitionsPackageParser: String => Declaration = parser.definitionsPackageParser

  private[parser] object BuiltinAnnotationDefinitions {
    val defs: Declaration = Declaration(Map(
      Name("old", None) ->
        Signature(Some(Real), Real, Some(List((Name("\\cdot", None), Real))), Right(None), UnknownLocation)
    ))
  }

  /**
   * Elaborates variable uses of nullary function symbols in `entry` and its definitions/annotations, performs DotTerm
   * abstraction in entry definitions, and semantic/type analysis of the results.
   */
  def elaborate(entry: ParsedArchiveEntry): ParsedArchiveEntry = {
    val defsWithDotArgs = entry
      .defs
      .decls
      .filter({
        case (_, Signature(_, _, Some(args), _, _)) => args.exists(_._1.name == "\\cdot")
        case (_, Signature(_, _, None, _, _)) => false
      })
    if (defsWithDotArgs.nonEmpty) {
      val (name, Signature(_, _, _, _, loc)) = defsWithDotArgs.head
      throw ParseException(
        "Definition " + name.prettyString +
          " uses unsupported anonymous (dot) arguments; please use named arguments (e.g., Real x) instead",
        loc,
      )
    }

    val elaboratedDefs = elaborateDefs(entry.defs)

    val uses: Map[Name, (Map[Name, Set[NamedSymbol]], Location)] = elaboratedDefs
      .decls
      .map({
        case (name, Signature(_, _, _, Left(_), loc)) => name -> (Map.empty[Name, Set[NamedSymbol]], loc)
        case (name, Signature(_, _, args, Right(int), loc)) => name ->
            (
              (args match {
                case Some(args) => int.map(_.baseSymbols.filterNot(n => args.contains((Name(n.name, n.index), n.sort))))
                case None => int.map(_.baseSymbols)
              }).getOrElse(Set.empty).groupBy(n => Name(n.name, n.index)),
              loc,
            )
      })
    val inconsistentUses = uses.filter(_._2._1.exists(_._2.size > 1))
    if (inconsistentUses.nonEmpty) {
      val (name, (symbols, loc)) = inconsistentUses.head
      throw ParseException(
        "Definition " + name.prettyString + " uses same name for " +
          symbols.map(_._2.map(_.fullString).mkString(" vs. ")),
        loc,
      )
    }
    val locallyConsistentUses = uses.map({ case (k, (v, loc)) => k -> (v.map(_._2.head).toSet, loc) })

    val undeclaredUses = locallyConsistentUses
      .map({ case (n, (symbols, loc)) =>
        n ->
          (
            symbols
              .filterNot(_.isInstanceOf[DotTerm])
              .filter(s => !elaboratedDefs.decls.contains(Name(s.name, s.index)))
              .filterNot(ReservedSymbols.reserved.contains)
              .filterNot(TacticReservedSymbols.symbols.contains),
            loc,
          )
      })
      .filter({ case (_, (s, _)) => s.nonEmpty })
    if (undeclaredUses.nonEmpty) {
      val (name, (symbols, loc)) = undeclaredUses.head
      throw ParseException(
        "Definition " + name.prettyString + " uses undefined symbol(s) " +
          symbols.toList.sortBy(_.name).map(_.prettyString).mkString(",") +
          ". Please add arguments or define as functions/predicates/programs",
        loc,
      )
    }

    val inconsistentWithDecls = locallyConsistentUses
      .map({ case (k, (used, loc)) => k -> (used.map(n => n -> elaboratedDefs.decls.get(Name(n.name, n.index))), loc) })
      .filter({ case (_, (symbols, _)) =>
        symbols.exists({ case (use, decl) =>
          decl.exists({ case Signature(domain, sort, _, _, _) =>
            use match {
              case fn: Function => fn.sort != sort || !domain.contains(fn.domain)
              case _ => false
            }
          })
        })
      })
    if (inconsistentWithDecls.nonEmpty) {
      val (name, (symbols, loc)) = inconsistentWithDecls.head
      throw ParseException(
        "Definition " + name.prettyString + " uses " + symbols.map({ case (s, d) =>
          s.fullString + " inconsistent with definition " + s.prettyString +
            d.map(s => ":" + s.domain.map(s => s"$s->").getOrElse("") + s.codomain).getOrElse("")
        }),
        loc,
      )
    }

    // elaborate model and check
    val elaboratedModel =
      try {
        elaboratedDefs
          .implicitSubst(elaboratedDefs.elaborateToSystemConsts(elaboratedDefs.elaborateToFunctions(entry.model)))
      } catch { case ex: AssertionError => throw ParseException(ex.getMessage, ex) }
    val fullyExpandedModel =
      try { elaboratedDefs.exhaustiveSubst(elaboratedModel) }
      catch { case ex: AssertionError => throw ParseException(ex.getMessage, ex) }
    Parser.semanticAnalysis(fullyExpandedModel).toList match {
      case Nil =>
      case ambiguous =>
        val msg = "semantics: Expect unique names_index that identify a unique type." + "\nambiguous: " +
          ambiguous.map(_.fullString).mkString(" and ")
        throw ParseException(
          "Semantic analysis error\n" + msg,
          UnknownLocation,
          ambiguous.map(_.fullString).mkString(" and "),
          "unambiguous type",
        )
    }
    // @note bare formula input without any definitions uses default meaning of variables and constant symbols
    if (
      elaboratedDefs.decls.nonEmpty ||
      StaticSemantics
        .symbols(elaboratedModel)
        .exists({
          case Function(_, _, domain, _, _) => domain != Unit
          case _ => false
        })
    ) {
      typeAnalysis(entry.name, entry.defs, elaboratedModel) // may throw ParseException
    }

    checkUseDefMatch(elaboratedModel, elaboratedDefs)

    // analyze and report annotations
    val elaboratedAnnotations = elaborateAnnotations(entry.annotations, elaboratedDefs)
    elaboratedAnnotations
      .distinct
      .foreach({
        case (e: Program, a: Formula) =>
          if (elaboratedDefs.decls.nonEmpty)
            typeAnalysis(entry.name, elaboratedDefs ++ BuiltinAnnotationDefinitions.defs, a)
          else typeAnalysis(entry.name, declarationsOf(entry.model) ++ BuiltinAnnotationDefinitions.defs, a)
        case (_: Program, a) => throw ParseException(
            "Unsupported annotation " + a.prettyString + " of kind " + a.kind +
              " encountered, please provide a formula",
            UnknownLocation,
          )
        case (e, a) => throw ParseException(
            "Annotation " + a.prettyString + " on " + e.prettyString + " of kind " + e.kind +
              " not supported, please annotate programs only",
            UnknownLocation,
          )
      })

    entry.copy(model = elaboratedModel, defs = elaboratedDefs, annotations = elaboratedAnnotations)
  }

  /**
   * Checks that uses in `problem` match the declarations.
   * @throws [[ParseException]]
   *   on use-def mismatch.
   */
  private def checkUseDefMatch(problem: Expression, defs: Declaration): Unit = {
    // check that definitions and use match
    val symbols = StaticSemantics.symbols(problem) ++ defs.substs.flatMap(s => StaticSemantics.symbols(s.repl))
    val defSymbols = defs.substs.map(_.what)
    val mismatches = defSymbols
      .map({
        case n: NamedSymbol => symbols.find(u => u.name == n.name && u.index == n.index && u.kind != n.kind).map(n -> _)
        case _ => None
      })
      .filter(_.isDefined)
      .map(_.get)
    if (mismatches.nonEmpty) {
      val mismatchDescription = mismatches
        .map({ case (defSym, sym) =>
          "Symbol '" + defSym.prettyString + "' defined as " + defSym.kind + ", but used as " + sym.kind + " in " +
            sym.prettyString
        })
        .mkString("\n")
      val found = mismatches.map({ case (_, sym) => sym.prettyString }).mkString(", ")
      val expected = mismatches.map({ case (defSym, _) => defSym.prettyString }).mkString(", ")
      throw new ParseException(
        "All definitions and uses must match, but found the following mismatches:\n" + mismatchDescription,
        UnknownLocation,
        found,
        expected,
        "",
        "",
      )
    }
  }

  /**
   * Elaborates to functions in annotations.
   * @param annotations
   *   the annotations to elaborate
   * @param defs
   *   lists functions to elaborate to
   * @throws [[ParseException]]
   *   if annotations are not formulas, not attached to programs, or type analysis of annotations fails
   */
  private def elaborateAnnotations(
      annotations: List[(Expression, Expression)],
      defs: Declaration,
  ): List[(Expression, Expression)] = {
    annotations.map({
      case (e: Program, a: Formula) =>
        val substPrg = defs.elaborateToSystemConsts(defs.elaborateToFunctions(e))
        val substFml = defs.elaborateToSystemConsts(defs.elaborateToFunctions(a))
        (substPrg, substFml)
      case (_: Program, a) =>
        throw ParseException("Annotation must be formula, but got " + a.prettyString, UnknownLocation)
      case (e, _) => throw ParseException("Annotation on programs only, but was on " + e.prettyString, UnknownLocation)
    })
  }

  /** Expands definitions in annotations to create fully expanded annotations. */
  private def expandAnnotations(
      annotations: List[(Expression, Expression)],
      defs: Declaration,
  ): List[(Expression, Expression)] = {
    annotations.map({
      case (e: Program, a: Formula) =>
        val substPrg = defs.exhaustiveSubst(defs.elaborateToFunctions(e))
        val substFml = defs.exhaustiveSubst(defs.elaborateToFunctions(a))
        (substPrg, substFml)
      case (_: Program, a) =>
        throw ParseException("Annotation must be formula, but got " + a.prettyString, UnknownLocation)
      case (e, _) => throw ParseException("Annotation on programs only, but was on " + e.prettyString, UnknownLocation)
    })
  }

  /** Extracts declarations per static semantics of the expression `parsedContent`. */
  def declarationsOf(parsedContent: Expression, filter: Option[Set[NamedSymbol]] = None): Declaration = {
    def makeArgsList(args: Term): Option[List[(Name, Sort)]] = args match {
      case Pair(l, r) => (makeArgsList(l), makeArgsList(r)) match {
          case (Some(la), Some(ra)) => Some(la ++ ra)
          case (la @ Some(_), None) => la
          case (None, ra @ Some(_)) => ra
          case _ => None
        }
      case FuncOf(n, _) => Some(List(Name(n.name, n.index) -> n.sort))
      case n: NamedSymbol => Some(List(Name(n.name, n.index) -> n.sort))
      case _ => None // @note unable to guess argument name from general terms x+y
    }

    val collectedArgs = scala.collection.mutable.Map.empty[NamedSymbol, List[(Name, Sort)]]
    val symbols = StaticSemantics.symbols(parsedContent)
    val fnDecls = symbols
      .filter(_.isInstanceOf[Function])
      .map(_.asInstanceOf[Function])
      .filter(_.domain == Unit)
      . // @note allow undeclared constants, but not actual functions (still: Pi, E?)
      map(fn =>
        Name(fn.name, fn.index) ->
          Signature(Some(fn.domain), fn.sort, collectedArgs.get(fn), Right(None), UnknownLocation)
      )
      .toMap
    val varDecls = symbols
      .filter(_.isInstanceOf[BaseVariable])
      .map(v => Name(v.name, v.index) -> Signature(None, v.sort, None, Right(None), UnknownLocation))
      .toMap
    Declaration(fnDecls ++ varDecls)
  }

  /** Elaborates variables to function symbols and program constants to system constants in definitions `defs`. */
  def elaborateDefs(defs: Declaration): Declaration = {
    def taboos(signature: List[(Name, Sort)]): Set[Function] = signature
      .filter({ case (Name(name, _), _) => name != "\\cdot" })
      .map({ case (Name(name, idx), sort) => Function(name, idx, Unit, sort) })
      .toSet

    val inconsistentDecls = defs
      .decls
      .map({
        case (n, Signature(_, _, _, Right(interp), loc)) => (n, loc) ->
            interp.map(_.baseSymbols.groupBy(n => Name(n.name, n.index))).getOrElse(Map.empty)
        case (n, Signature(_, _, _, Left(interp), loc)) => (n, loc) ->
            interp.baseSymbols.groupBy(n => Name(n.name, n.index))
      })
      .filter({ case (_, symbols) => symbols.exists(_._2.size > 1) })
    if (inconsistentDecls.nonEmpty) {
      val loc = if (inconsistentDecls.size == 1) inconsistentDecls.head._1._2 else UnknownLocation
      throw ParseException(
        inconsistentDecls
          .map({ case ((name, loc), symbols) =>
            "Definition " + name.prettyString + " at " + loc + " uses names inconsistently\n" +
              symbols.map({ case (_, s) => "  " + s.map(_.fullString).mkString(" vs. ") }).mkString("\n")
          })
          .mkString("\n"),
        loc,
      )
    }

    def elaborateToDifferentials(e: Expression): Expression = {
      val ds = StaticSemantics
        .symbols(e)
        .filter(_.isInstanceOf[DifferentialSymbol])
        .map(_.asInstanceOf[DifferentialSymbol])
      ds.foldLeft(e)({ case (e, n) => e.replaceFree(n, Differential(n.x)) })
    }

    val elab = ListBuffer.empty[(Name, Signature)]
    val remainder = scala.collection.mutable.Map(defs.decls.toSeq: _*)
    defs.copy(decls =
      Declaration
        .topSort(defs.decls)
        .map({
          case (name, sig @ Signature(_, _, _, Left(_), _)) => (name, sig)
          case (name, sig @ Signature(_, sort, argNames, Right(interpretation), loc)) =>
            val r = (
              name,
              sig.copy(interpretation = Right(interpretation.map(i => {
                // @note use already elaborated symbols instead of original symbols
                val d = Declaration(elab.toMap ++ remainder)
                val elaborated = d.elaborateToSystemConsts(
                  d.elaborateToFunctions(elaborateToDifferentials(i), taboos(argNames.getOrElse(Nil)))
                )
                if (elaborated.sort != sort) throw ParseException(
                  "Definition " + name.prettyString + " does not fit declared sort " + sort +
                    "; right-hand side is of sort " + elaborated.sort,
                  loc,
                )
                elaborated
              }))),
            )
            elab += r
            remainder.remove(name)
            r
        })
        .toMap
    )
  }

  /**
   * Type analysis of expression according to the given type declarations decls
   * @param name
   *   the entry name (for error messages)
   * @param d
   *   the type declarations known from the context (e.g., as parsed from the Definitions and ProgramVariables block of
   *   an entry)
   * @param expr
   *   the expression to analyze
   * @throws [[edu.cmu.cs.ls.keymaerax.parser.ParseException]]
   *   if the type analysis fails.
   */
  def typeAnalysis(name: String, d: Declaration, expr: Expression): Boolean = {
    StaticSemantics
      .symbols(expr)
      .filterNot(TacticReservedSymbols.symbols.contains(_))
      .forall({
        case f: Function =>
          val Signature(declaredDomain, declaredSort, _, _, loc: Location) = d.decls.get(Name(f.name, f.index)) match {
            case Some(decl) => decl
            case None => throw ParseException.typeError(
                name + ": undefined function symbol",
                f,
                f.sort.toString,
                UnknownLocation,
                "Make sure to declare all variables in ProgramVariables and all symbols in Definitions block.",
              )
          }
          if (f.sort != declaredSort) throw ParseException.typeDeclError(
            s"$name: ${f.prettyString} declared with sort $declaredSort but used where sort ${f.sort} was expected.",
            s"$declaredSort function",
            f.sort.toString,
            loc,
          )
          else if (!declaredDomain.contains(f.domain)) {
            (f.domain, declaredDomain) match {
              case (_, Some(r)) => throw ParseException.typeDeclError(
                  s"$name: ${f.prettyString} declared with domain $r but used where domain ${f.domain} was expected.",
                  r.toString,
                  f.domain.toString,
                  loc,
                )
              case (_, None) => throw ParseException.typeDeclError(
                  s"$name: ${f.prettyString} declared as a variable of sort ${f.sort} but used as a function with arguments.",
                  "no arguments",
                  "function with arguments",
                  loc,
                )
              // The other cases can't happen -- we know f is a function so we know it has a domain.
            }
          } else true
        case DifferentialSymbol(v) =>
          d.decls.contains(Name(v.name, v.index)) // @note hence it is checked as variable already
        case x: Variable =>
          if (quantifiedVars(expr).contains(x))
            true // Allow all undeclared variables if they are at some point bound by a \forall or \exists. @todo this is an approximation. Should only allow quantifier bindings...
          else {
            val (declaredSort, declLoc) = d.decls.get(Name(x.name, x.index)) match {
              case Some(Signature(None, sort, _, _, loc)) => (sort, loc)
              case Some(Signature(Some(domain), sort, _, _, loc)) => throw ParseException.typeDeclError(
                  s"$name: ${x.name} was declared as a function but must be a variable when it is assigned to or has a differential equation.",
                  x.prettyString + ": " + domain + "->" + sort + " Function",
                  "Real " + x.prettyString,
                  loc,
                )
              case None => throw ParseException.typeDeclGuessError(
                  name + ": undefined symbol " + x.prettyString,
                  "undefined symbol " + x.prettyString,
                  "Real " + x.prettyString,
                  UnknownLocation,
                  "Add \"Real " + x.prettyString + ";\" to the ProgramVariables block",
                )
            }
            if (x.sort != declaredSort) throw ParseException.typeDeclGuessError(
              s"$name: ${x.prettyString} declared with sort $declaredSort but used where a ${x.sort} was expected.",
              s"$declaredSort${x.prettyString}",
              s"${x.sort} ${x.prettyString}",
              declLoc,
            )
            x.sort == declaredSort
          }
        case _: UnitPredicational => true // @note needs not be declared
        case _: UnitFunctional => true // @note needs not be declared
        case _: DotTerm => true // @note needs not be declared
        case _ => false
      })
  }

  /** Returns all the quantified variables in an expression. Used in [[typeAnalysis()]] */
  private def quantifiedVars(expr: Expression) = {
    val quantifiedVariables: scala.collection.mutable.Set[NamedSymbol] = scala.collection.mutable.Set()

    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = {
          // Add all quantified variables to the quantifiedVariables set.
          e match {
            case Forall(xs, _) => xs.foreach(v => quantifiedVariables += v)
            case Exists(xs, _) => xs.foreach(v => quantifiedVariables += v)
            case _ =>
          }
          Left(None)
        }
      },
      expr.asInstanceOf[Formula],
    )

    quantifiedVariables
  }
}
