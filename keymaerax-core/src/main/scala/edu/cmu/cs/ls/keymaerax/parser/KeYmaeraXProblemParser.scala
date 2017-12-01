/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PosInExpr}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.{ExpressionTraversal, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}

import scala.annotation.tailrec
import scala.util.Try

/**
 * Parses `.kyx` KeYmaera X problem files.
 * @todo check sorts
 * @author Nathan Fulton
 * Created by nfulton on 6/12/15.
 */
object KeYmaeraXProblemParser {
  type Declaration = KeYmaeraXDeclarationsParser.Declaration

  /** Indicates whether or not the model represents an exercise. */
  def isExercise(model: String): Boolean = model.contains("__________")

  /** Convenience wrapper to get formula only. */
  def apply(inputWithPossibleBOM : String): Formula = parseProblem(inputWithPossibleBOM)._2

  /** Parse a problem file to its declarations and problem formula. */
  def parseProblem(inputWithPossibleBOM : String): (Declaration, Formula) = {
    val input = ParserHelper.removeBOM(inputWithPossibleBOM)
    try {
      firstUnacceptableCharacter(input) match {
        case Some(pair) => throw ParseException(s"Input string contains non-ASCII character ${pair._2}", pair._1)
        case None =>
          val lexResult = KeYmaeraXLexer.inMode(input, ProblemFileMode)
          if(KeYmaeraXParser.PARSER_DEBUGGING) println(lexResult) //@note Useful to change this to true if you're modifying the parser or chasing down a bug.
          parseProblem(lexResult)
      }
    } catch {
      case e: ParseException => throw e.inInput(input)
    }
  }

  /** Tries parsing as a problem first. If it fails due to a missing Problem block, tries parsing as a plain formula. */
  def parseAsProblemOrFormula(input : String): Formula = {
    try {
      val (d, fml) = KeYmaeraXProblemParser.parseProblem(input)
      d.exhaustiveSubst(fml)
    } catch {
      case ex: ParseException if ex.msg == "Problem. block expected" =>
        KeYmaeraXParser(input).asInstanceOf[Formula]
    }
  }

  /** //almost always the line number where the Problem section begins. (see todo) */
  private def problemLineOffset(input: String) =
    input.split("\n")
      .zipWithIndex
      .find(s => s._1.contains("Problem."))
      .getOrElse(throw new Exception("All problem files should contain a Problem. declaration."))
      ._2 + 2 //+1 because lines start at 1, and +1 again because the problem starts on the line after the Problem. declaration. @todo that second +1 is not always true.

  /** Parses a file of the form Problem. ... End. Solution. ... End. */
  def parseProblemAndTactic(input: String): (Formula, BelleExpr) = try {
    firstUnacceptableCharacter(input) match {
      case Some(pair) => throw ParseException(s"Input string contains non-ASCII character ${pair._2}", pair._1)
      case None => {
        val parts = input.split("Solution.")
        assert(parts.length == 2, "Expected a problem file followed by a single ``Solution`` section.")
        val (problem, tactic) = (parts(0), parts(1))

        assert(tactic.trim.endsWith("End."), "``Solution.`` does not have a closing ``End.``")

        val belleExpr = BelleParser(tactic.trim.dropRight("End.".length))
        val formula = apply(problem)

        (formula, belleExpr)
      }
    }
  }
  catch {case e: ParseException => throw e.inInput(input)} //@todo properly offset Belle parse exceptions...

  /** Non-unicode characters that are allowed in KeYmaera X input files.
    * Should correspond to the unicode that's printed in the web UI. */
  val allowedUnicodeChars : Set[Char] = Set[Char](
    '≤',
    '≥',
    '∧',
    '∨',
    '≠',
    '∀',
    '∃',
    '→',
    '↔',
    '←'
  )

  /** Returns the location and value of the first non-ASCII character in a string that is not in [[allowedUnicodeChars]] */
  def firstUnacceptableCharacter(s : String) : Option[(Location, Char)] = {
    val pattern = """([^\p{ASCII}])""".r
    val nonAsciiChars = pattern.findAllIn(s).matchData.map(_.group(0).toCharArray.last).toList

    //Some unicode is allowed! Find only the unicode that is not allwed.
    val disallowedChars = nonAsciiChars.filter(!allowedUnicodeChars.contains(_))

    if(disallowedChars.nonEmpty) {
      val nonAsciiCharacter : Char = {
        if(disallowedChars.nonEmpty) disallowedChars.head
        else throw new Exception("Expected at least one match but matchData.hasNext returned false when matches.nonEmpty was true!")
      }
      val prefix = s.split(nonAsciiCharacter).head
      val lines = prefix.split("\n")
      val lineNumber = lines.length
      val columnNumber = lines.last.length + 1
      Some(new Region(lineNumber, columnNumber, lineNumber, columnNumber), nonAsciiCharacter)
    }
    else {
      //@todo change this assertion: assert(s.matches("\\A\\p{ASCII}*\\z"))
      None
    }
  }

  protected def parseProblem(tokens: List[Token]):  (Declaration, Formula) = {
    val parser = KeYmaeraXParser
    val (d, remainingTokens) = KeYmaeraXDeclarationsParser(tokens)
    checkInput(remainingTokens.nonEmpty, "Problem. block expected", UnknownLocation, "kyx problem input problem block")
    checkInput(remainingTokens.head.tok.equals(PROBLEM_BLOCK), "Problem. block expected", remainingTokens.head.loc, "kyx reading problem block")

    if(d.decls.keySet.nonEmpty && remainingTokens.head.loc.line <= 1)
      println("WARNING: There were declarations in this file but the non-declaration portion of the file starts at line 0 or line 1. There may be off-by-n errors in location messages.")

    val (theProblem, eof) = remainingTokens.span(x => !x.tok.equals(END_BLOCK))
    checkInput(eof.length == 2 && eof.head.tok.equals(END_BLOCK),
      "Expected Problem block to end with 'End.' but found " + eof,
      if (eof.nonEmpty) eof.last.loc else theProblem.last.loc, "kyx problem end block parser")
    checkInput(eof.length == 2 && eof.last.tok.equals(EOF),
      "Expected Problem block to be last in file, but found " + eof,
      if (eof.nonEmpty) eof.last.loc else theProblem.last.loc, "kyx problem end block parser")

    //@note redirect annotation listener to elaborate products
    val annotationListener = parser.annotationListener
    parser.setAnnotationListener((prg, fml) => {
      // make annotations compatible with parse result: add () and expand function declarations
      annotationListener(d.exhaustiveSubst(prg), d.exhaustiveSubst(fml))
    })

    val problem : Formula = parser.parse(theProblem.tail :+ Token(EOF, UnknownLocation)) match {
      case f : Formula => f
      case expr : Expression => throw ParseException("problem block" + ":" + "Expected problem to parse to a Formula", expr)
    }

    parser.setAnnotationListener(annotationListener)

    parser.semanticAnalysis(problem) match {
      case None =>
      case Some(error) => throw ParseException("Semantic analysis error\n" + error, problem)
    }

    val elaborated = d.exhaustiveSubst(problem)

    KeYmaeraXDeclarationsParser.typeAnalysis(d, elaborated) //throws ParseExceptions.

    (d, elaborated)
  }
}

/**
 * Parses the declarations in .kyx and .alp files.
 */
object KeYmaeraXDeclarationsParser {
  /** Name is alphanumeric name and index. */
  type Name = (String, Option[Int])
  /** Signature is domain sort, codomain sort, "interpretation", token that starts the declaration. */
  type Signature = (Option[Sort], Sort, Option[Expression], Token)
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
    private def declAsSubstitutionPair(name: KeYmaeraXDeclarationsParser.Name, signature: KeYmaeraXDeclarationsParser.Signature): SubstitutionPair = {
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

  /**
   *
   * @param tokens The tokens to parse
   * @return A pair containing:
   *          _1: A mapping from variable name/index pairs to variable sorts, where the sort is a triple:
   *              _1: (Optionally) the domain sort of a function
   *              _2: The sort of a ProgramVariable, or the codomain sort of a function.
    *             _3: The token that starts the declaration.
   *          _2: The list of remaining tokens.
   */
  def apply(tokens : List[Token]) : (Declaration, List[Token]) =
    parseDeclarations(tokens)

  /** Parses declarations in Functions/Definitions/ProgramVariables/Variables blocks. */
  def parseDeclarations(tokens: List[Token]): (Declaration, List[Token]) = {
    if (tokens.head.tok == PROGRAM_VARIABLES_BLOCK) {
      val (programVariables, remainder) = processProgramVariables(tokens)
      val (functions, finalRemainder) = processDefinitions(remainder)
      (programVariables ++ functions, finalRemainder)
    } else if (tokens.head.tok == FUNCTIONS_BLOCK || tokens.head.tok == DEFINITIONS_BLOCK) {
      val (functions, remainder) = processDefinitions(tokens)
      val (programVariables, finalRemainder) = processProgramVariables(remainder)
      (programVariables ++ functions, finalRemainder)
    } else if (tokens.head.tok == VARIABLES_BLOCK) {
      processVariables(tokens)
    } else {
      (Declaration(Map()), tokens)
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
        val (declaredDomain,declaredSort, interpretation, declarationToken) = d.decls.get((f.name,f.index)) match {
          case Some(decl) => decl
          case None => throw ParseException("type analysis" + ": " + "undefined symbol " + f, f)
        }
        if(f.sort != declaredSort) throw ParseException(s"type analysis: ${f.prettyString} declared with sort $declaredSort but used where sort ${f.sort} was expected.", declarationToken.loc)
        else if (f.domain != declaredDomain.get) {
          (f.domain, declaredDomain) match {
            case (l, Some(r)) => throw ParseException(s"type analysis: ${f.prettyString} declared with domain $r but used where domain ${f.domain} was expected.", declarationToken.loc)
            case (l, None) => throw ParseException(s"type analysis: ${f.prettyString} declared as a non-function but used as a function.", declarationToken.loc)
            //The other cases can't happen -- we know f is a function so we know it has a domain.
          }
        }
        else true
      case x : Variable if quantifiedVars(expr).contains(x) => true //Allow all undeclared variables if they are at some point bound by a \forall or \exists. @todo this is an approximation. Should only allow quantifier bindings...
      case x: Variable =>
        val (declaredSort, declarationToken) = d.decls.get((x.name,x.index)) match {
          case Some((None,sort, _, token)) => (sort, token)
          case Some((Some(domain), sort, _, token)) => throw ParseException(s"Type analysis: ${x.name} was declared as a function but used as a non-function.", token.loc)
          case None => throw ParseException("type analysis" + ": " + "undefined symbol " + x + " with index " + x.index, x)
        }
        if (x.sort != declaredSort) throw ParseException(s"type analysis: ${x.prettyString} declared with sort $declaredSort but used where a ${x.sort} was expected.", declarationToken.loc)
        x.sort == declaredSort
      case _: UnitPredicational => true //@note needs not be declared
      case _: UnitFunctional => true //@note needs not be declared
      case _: DotTerm => true //@note needs not be declared
      case DifferentialSymbol(v) => d.decls.contains(v.name, v.index) //@note hence it is checked as variable already
      case _ => false
    })
  }


  /**
   *
   * @param tokens Tokens in the parsed file.
   * @return A pair:
   *          _1: The list of Named Symbols.
   *          _2: The remainder of the file.
   */
  def processProgramVariables(tokens : List[Token]): (Declaration, List[Token]) = {
    if (tokens.head.tok.equals(PROGRAM_VARIABLES_BLOCK)) {
      val(progVarsSection, remainder) = tokens.span(x => !x.tok.equals(END_BLOCK))
        val progVarsTokens = progVarsSection.tail
        (processDeclarations(progVarsTokens, Declaration(Map())), remainder.tail)
    } else (Declaration(Map()), tokens)

  }

  /** Parses the declarations in a Functions/Definitions block. */
  private def processDefinitions(tokens: List[Token]): (Declaration, List[Token]) = {
    if (tokens.head.tok == FUNCTIONS_BLOCK || tokens.head.tok == DEFINITIONS_BLOCK) {
      val(funSymbolsTokens, remainder) = tokens.span(_.tok != END_BLOCK)
      val funSymbolsSection = funSymbolsTokens.tail
      (Declaration(processDeclarations(funSymbolsSection, Declaration(Map())).decls.map({
        case d@(i, (domain, sort, interpretation, token)) => domain match {
          case None => (i, (Some(Unit), sort, interpretation, token)) //@note allow A() declared without parentheses
          case Some(_) => d
        }
      })), remainder.tail)
    } else (Declaration(Map()), tokens)
  }

  def processVariables(tokens: List[Token]) : (Declaration, List[Token]) = {
    if(tokens.head.tok.equals(VARIABLES_BLOCK)) {
      val(funSymbolsTokens, remainder) = tokens.span(x => !x.tok.equals(END_BLOCK))
      val funSymbolsSection = funSymbolsTokens.tail
      (processDeclarations(funSymbolsSection, Declaration(Map())), remainder.tail)
    }
    else (Declaration(Map()), tokens)
  }


  /*
   *                                              parseFunctionDomainSort
   *                                 ++=========================================++
   *                                 ||                  +-------------+        ||
   *                                 ||                 \/             |        ||
   * InitS --> SortS ---> NameS ---> || OpenParenS ---> ArgSortS ---> CommaS    ||
   *                        |        ||   |                            |        ||
   *                        |        ||   |                            \/       ||
   *                        |        ||   +---------------------- > CloseParen  ||
   *                        |        ++=========================================++
   *                        \/                                         |
   *                     PeriodS <-------------------------------------+
   *
   * And if the machine halts in a non-PeriodS state then it errors.
   */
  private def parseDeclaration(ts : List[Token]) : ((Name, Signature), List[Token]) = {
    val sortToken = ts.head
    val sort = parseSort(sortToken, sortToken)

    val nameToken = ts.tail.head
    val nameTerminal : IDENT = ts.tail.head.tok match {
      case i : IDENT => i
      case x => throw new Exception("Expected an identifier but found " + x.getClass.getCanonicalName)
    }

    val afterName = ts.tail.tail //skip over IDENT and REAL/BOOL tokens.
    if (afterName.head.tok == LPAREN) {
      val (fnDef, remainder) = splitDef(ts, RPAREN)
      checkInput(fnDef.last.tok == PERIOD,
        "Expected declaration to end with . but found " + fnDef.last, fnDef.last.loc, "Reading a declaration")
      val (domainSort, domainSortRemainder) = parseFunctionDomainSort(fnDef.tail.tail, nameToken)
      val interpretation = parseInterpretation(sort, domainSortRemainder, nameToken)
      (( (nameTerminal.name, nameTerminal.index), (Some(domainSort), sort, interpretation, nameToken)), remainder)
    } else if (afterName.head.tok == PRG_DEF) {
      val (fnDef, remainder) = splitDef(ts, RBRACE)
      checkInput(fnDef.last.tok == PERIOD,
        "Expected declaration to end with . but found " + fnDef.last, fnDef.last.loc, "Reading a declaration")
      val interpretation = parseInterpretation(sort, fnDef.tail.tail, nameToken)
      (( (nameTerminal.name, nameTerminal.index), (None, sort, interpretation, nameToken)), remainder)
    } else if (afterName.head.tok == PERIOD) {
      (( (nameTerminal.name, nameTerminal.index) , (None, sort, None, nameToken) ), afterName.tail)
    } else {
      throw new ParseException("Variable declarations should end with a period.", afterName.head.loc, afterName.head.tok.img, ".", "", "declaration parse")
    }
  }

  /**
   *
   * @param tokens A list of tokens that begins like: (R|B, ...).
    *@param of A meaningful token representing the thing whose type is being parsed.
   * @return A pair:
   *          _1: The sort of the entire function,
   *          _2: The reamining tokens.
   */
  private def parseFunctionDomainSort(tokens: List[Token], of: Token): (Sort, List[Token]) = {
    // Parse the domain sort.
    checkInput(tokens.length > 1, "domain sort expected in declaration", if (tokens.isEmpty) UnknownLocation else tokens.head.loc, "parsing function domain sort")
    checkInput(tokens.head.tok.equals(LPAREN), "function argument parentheses expected", tokens.head.loc, "parsing function domain sorts")

    def spanSorts(tokens: List[Token]): (List[Token], List[Token]) = {
      var n = 1
      tokens.tail.span(_.tok match { case LPAREN => n=n+1; true case RPAREN => n=n-1; n>0 case _ => true })
    }

    val splitAtRparen = spanSorts(tokens)
    val domainElements = splitAtRparen._1

    checkInput(splitAtRparen._2.head.tok.equals(RPAREN),
      "unmatched LPAREN at end of function declaration. Intead, found: " + splitAtRparen._2.head, splitAtRparen._2.head.loc, "parsing function domain sorts")
    val remainder = splitAtRparen._2.tail

    def dottify(body: List[Token], id: IDENT, nextDot: DOT): (List[Token], DOT) = {
      val nextIdx = nextDot.index match {
        case Some(i) => i+1
        case None => 0
      }
      (body.map(t => if (t.tok==id) Token(nextDot, t.loc) else t), DOT(Some(nextIdx)))
    }

    def toSort(tokens: List[Token], body: List[Token], nextDot: DOT): (Sort, List[Token], DOT) = tokens match {
      case Nil => (Unit, body, nextDot)
      case Token(COMMA, _)::tail => toSort(tail, body, nextDot)
      case Token(LPAREN, _)::_ =>
        val (nestedSort, sortRemainder) = spanSorts(tokens)
        assert(sortRemainder.head.tok == RPAREN, "Expected a closing parenthesis, but got " + sortRemainder.head.tok)
        if (sortRemainder.tail.isEmpty) {
          toSort(nestedSort, body, nextDot)
        } else {
          val (s1, b1, d1) = toSort(nestedSort, body, nextDot)
          val (s2, b2, d2) = toSort(sortRemainder.tail, b1, d1)
          (Tuple(s1, s2), b2, d2)
        }
      case (st@Token(_, _))::Token(id: IDENT, _)::tail if tail.nonEmpty =>
        val s1 = parseSort(st, of)
        val (b1, d1) = dottify(body, id, nextDot)
        val (s2, b2, d2) = toSort(tail, b1, d1)
        (Tuple(s1, s2), b2, d2)
      case (st@Token(_, _))::Token(id: IDENT, _)::Nil =>
        val s1 = parseSort(st, of)
        val (b1, d1) = dottify(body, id, nextDot)
        (s1, b1, d1)
      case (st@Token(_, _))::tail if tail.nonEmpty =>
        val s1 = parseSort(st, of)
        val (s2, b2, d2) = toSort(tail, body, nextDot)
        (Tuple(s1, s2), b2, d2)
      case (st@Token(_, _))::Nil => (parseSort(st, of), body, nextDot)
    }

    //@note backwards compatibility with f(R) = (. + 2).
    toSort(domainElements, remainder, DOT(Some(0))) match {
      case (Real, body, _) if body.forall(_.tok match {
        case DOT(Some(0)) => true
        case DOT(_) => false
        case _ => true
      }) => (Real, body.map(x => x.tok match {
        case DOT(Some(0)) => Token(DOT(), x.loc)
        case _ => x
      }))
      case (s, b, _) => (s, b)
    }
  }

  /**
    *
    * @param tokens A list of tokens that begins like: (R|B, ...).
    * @param of A meaningful token representing the thing whose type is being parsed.
    * @return A pair:
    *          _1: The interpretation,
    *          _2: The reamining tokens.
    */
  private def parseInterpretation(sort: Sort, tokens: List[Token], of: Token): Option[Expression] = {
    /** Reads and parses a definition ending in `defDelim`PERIOD, and returns the remaining tokens after the definition. */
    def parseDef(tokens: List[Token], defDelim: Terminal): Option[Expression] = {
      val definition = tokens.dropRight(1) //splitDef(tokens, defDelim)
      val expr = KeYmaeraXParser.parse(definition :+ Token(EOF))
      if (expr.sort != sort) throw new ParseException("Definition sort does not match declaration",
        tokens.head.loc.spanTo(tokens.last.loc), "<" + expr.sort + ">", "<" + sort + ">", "", "parsing function interpretation")
      else Some(expr)
    }

    (sort, tokens.head.tok) match {
      case (Real|Trafo, EQUIV) => throw new ParseException("Operator and sort mismatch", tokens.head.loc, EQUIV.img + " <" + EQUIV + ">", EQ.img + " <" + EQ + ">", "", "parsing function interpretation")
      case (Bool|Trafo, EQ)    => throw new ParseException("Operator and sort mismatch", tokens.head.loc, EQ.img + " <" + EQ + ">", EQUIV.img + " <" + EQUIV + ">", "", "parsing function interpretation")
      case (_, EQUIV | EQ) => parseDef(tokens.tail, RPAREN)
      case (_, PRG_DEF) => parseDef(tokens.tail, RBRACE)
      case _ => None
    }
  }

  /** Splits a token stream at said definition delimiter followed by PERIOD. */
  private def splitDef(tokens: List[Token], defDelim: Terminal): (List[Token], List[Token]) = {
    val decl = tokens.sliding(2).toList.span({case Token(delim, _)::Token(PERIOD, _)::Nil => delim != defDelim case _ => true})
    if (decl._2.isEmpty) throw new ParseException("Non-delimited definition",
      tokens.head.loc.spanTo(decl._1.last.last.loc), decl._1.last.last.toString, ")", "", "parsing interpretation")
    val (definition, remainder) = (decl._1.map(_.head) :+ decl._2.head.head, decl._2.map(_.last))
    checkInput(remainder.head.tok == PERIOD,
      "Non-delimited definition. Found: " + remainder.head, tokens.head.loc.spanTo(remainder.head.loc), "parsing interpretation")
    (definition :+ remainder.head, remainder.tail)
  }

  private def parseSort(sortToken : Token, of: Token) : Sort = sortToken.tok match {
    case edu.cmu.cs.ls.keymaerax.parser.IDENT("R", _) => edu.cmu.cs.ls.keymaerax.core.Real
    case edu.cmu.cs.ls.keymaerax.parser.IDENT("HP", _) => edu.cmu.cs.ls.keymaerax.core.Trafo
    case edu.cmu.cs.ls.keymaerax.parser.IDENT("P", _) => edu.cmu.cs.ls.keymaerax.core.Trafo
    //@todo do we need a cont. trafo sort to do well-formedness checking?
    case edu.cmu.cs.ls.keymaerax.parser.IDENT("CP", _) => edu.cmu.cs.ls.keymaerax.core.Trafo
    case edu.cmu.cs.ls.keymaerax.parser.IDENT("F", _) => edu.cmu.cs.ls.keymaerax.core.Bool
    case edu.cmu.cs.ls.keymaerax.parser.IDENT("B", _) => edu.cmu.cs.ls.keymaerax.core.Bool
    case edu.cmu.cs.ls.keymaerax.parser.IDENT("T", _) => edu.cmu.cs.ls.keymaerax.core.Real
    case edu.cmu.cs.ls.keymaerax.parser.ANYTHING => edu.cmu.cs.ls.keymaerax.core.Real //Anything extends RTerm
    case edu.cmu.cs.ls.keymaerax.parser.TERM => edu.cmu.cs.ls.keymaerax.core.Real //@todo deprecated -- should be handled by T identifier.
    case edu.cmu.cs.ls.keymaerax.parser.PROGRAM => edu.cmu.cs.ls.keymaerax.core.Trafo //@todo
    case edu.cmu.cs.ls.keymaerax.parser.CP => edu.cmu.cs.ls.keymaerax.core.Trafo //@todo
    case edu.cmu.cs.ls.keymaerax.parser.MFORMULA => edu.cmu.cs.ls.keymaerax.core.Bool //@todo
    case edu.cmu.cs.ls.keymaerax.parser.TEST => edu.cmu.cs.ls.keymaerax.core.Bool //@todo this is getting stupid
    case _ => throw ParseException(s"Error in type declaration statement for ${identTerminalToString(of.tok)}" + ": " + "Expected a sort but found " + sortToken.toString, of.loc)
  }

  /** Turns an IDENT into a string for the sake of error messages only. This is probably replicated in the parser. */
  private def identTerminalToString(terminal: Terminal) = terminal match {
    case i : IDENT => i.name + {i.index match {case Some(x) => "_x" case None => ""}}
    case _ => throw new Exception(s"Expected an IDENT terminal but found $terminal")
  }

  /**
   * Takes a list of tokens and produces a mapping form names to signatures (domain, codomain, interpretation).
   * @param ts A list of tokens
   * @param accumulated The declarations accumulated so far.
   * @return Declarations [[Declaration]], i.e., a map from [[Name]] to [[Signature]].
   */
  @tailrec
  private def processDeclarations(ts: List[Token], accumulated: Declaration): Declaration =
    if (ts.nonEmpty) {
      //@note redirect annotation listener to elaborate products depending on declarations so far
      val annotationListener = KeYmaeraXParser.annotationListener
      KeYmaeraXParser.setAnnotationListener((prg, fml) =>
        annotationListener(accumulated.exhaustiveSubst(prg), accumulated.exhaustiveSubst(fml)))
      val (nextDecl, remainders) = parseDeclaration(ts)
      KeYmaeraXParser.setAnnotationListener(annotationListener)
      if (accumulated.decls.contains(nextDecl._1)) {
        val name = nextDecl._1._2 match {
          case Some(i) => nextDecl._1._1 + "_" + i
          case None => nextDecl._1._1
        }
        throw new ParseException("Duplicate symbol '" + name + "'",
          UnknownLocation, "", "", "", "")
      }
      processDeclarations(remainders, Declaration(accumulated.decls.updated(nextDecl._1, nextDecl._2)))
    } else accumulated
}
