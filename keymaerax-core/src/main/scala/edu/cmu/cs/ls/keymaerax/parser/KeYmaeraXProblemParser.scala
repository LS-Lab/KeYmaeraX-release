/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PosInExpr}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.core._

import scala.annotation.tailrec

/**
 * Parses `.kyx` KeYmaera X problem files.
 * @todo check sorts
 * @author Nathan Fulton
 * Created by nfulton on 6/12/15.
 */
object KeYmaeraXProblemParser {
  def apply(inputWithPossibleBOM : String): Formula = {
    val input = ParserHelper.removeBOM(inputWithPossibleBOM)
    try {
      firstNonASCIICharacter(input) match {
        case Some(pair) => throw ParseException(s"Input string contains non-ASCII character ${pair._2}", pair._1)
        case None => parseProblem(KeYmaeraXLexer.inMode(input, ProblemFileMode), input)._2
      }
    }
    catch {
      case e: ParseException => throw e.inInput(input)
    }
  }

  /** Tries parsing as a formula first. If that fails, tries parsing as a problem file. */
  def parseAsProblemOrFormula(input : String): Formula = {
    val result = try { Some(KeYmaeraXParser(input).asInstanceOf[Formula]) } catch { case e: Throwable => None }
    result match {
      case Some(formula) => formula
      case None => KeYmaeraXProblemParser(input)
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
    firstNonASCIICharacter(input) match {
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

  /** Returns the location and value of the first non-ASCII character in a string. */
  def firstNonASCIICharacter(s : String) : Option[(Location, Char)] = {
    val pattern = """([^\p{ASCII}])""".r
    val matches = pattern.findAllIn(s).matchData

    if(matches.nonEmpty) {
      val nonAsciiCharacter : Char = {
        if(matches.hasNext) matches.next().group(0).toCharArray.last
        else throw new Exception("Expected at least one match but matchData.hasNext returned false when matches.nonEmpty was true!")
      }
      val prefix = s.split(nonAsciiCharacter).head
      val lines = prefix.split("\n")
      val lineNumber = lines.length
      val columnNumber = lines.last.length + 1
      Some(new Region(lineNumber, columnNumber, lineNumber, columnNumber), nonAsciiCharacter)
    }
    else {
      assert(s.matches("\\A\\p{ASCII}*\\z"))
      None
    }
  }

  protected def parseProblem(tokens: List[Token], input: String) :  (Map[(String, Option[Int]), (Option[Sort], Sort)], Formula) = {
    val parser = KeYmaeraXParser
    val (decls, remainingTokens) = KeYmaeraXDeclarationsParser(tokens)
    checkInput(remainingTokens.nonEmpty, "Problem. block expected", UnknownLocation, "kyx problem input problem block")
    checkInput(remainingTokens.head.tok.equals(PROBLEM_BLOCK), "Problem. block expected", remainingTokens.head.loc, "kyx reading problem block")

    if(decls.keySet.nonEmpty && remainingTokens.head.loc.line <= 1)
      println("WARNING: There were declarations in this file but the non-declaration portion of the file starts at line 0 or line 1. There may be off-by-n errors in location messages.")

    val (theProblem, eof) = remainingTokens.span(x => !x.tok.equals(END_BLOCK))
    checkInput(eof.length == 2 && eof.head.tok.equals(END_BLOCK),
      "Expected Problem block to end with 'End.' but found " + eof,
      if (eof.nonEmpty) eof.last.loc else theProblem.last.loc, "kyx problem end block parser")
    checkInput(eof.length == 2 && eof.last.tok.equals(EOF),
      "Expected Problem block to be last in file, but found " + eof,
      if (eof.nonEmpty) eof.last.loc else theProblem.last.loc, "kyx problem end block parser")

    val parseResult : Expression = try {
      parser.parse(theProblem.tail :+ Token(EOF, UnknownLocation))
    } catch{
      case e : ParseException => throw ParseException(e.msg, e.loc.addLines(problemLineOffset(input)), e.found, e.expect, e.after, e.state, e.cause)
    }

    val problem = parseResult match {
      case f : Formula => f
      case expr : Expression => throw ParseException("problem block" + ":" + "Expected problem to parse to a Formula", expr)
    }

    parser.semanticAnalysis(problem) match {
      case None =>
      case Some(error) => throw ParseException("Semantic analysis error\n" + error, problem)
    }

    KeYmaeraXDeclarationsParser.typeAnalysis(decls, problem) //throws ParseExceptions.

    val declsWithoutStartToks = decls.mapValues(v => (v._1, v._2))
    (declsWithoutStartToks, problem)
  }
}

/**
 * Parses the declarations in .kyx and .alp files.
 */
object KeYmaeraXDeclarationsParser {
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
  def apply(tokens : List[Token]) : (Map[(String, Option[Int]), (Option[Sort], Sort, Token)], List[Token]) =
    parseDeclarations(tokens)

  def parseDeclarations(tokens: List[Token]): (Map[(String, Option[Int]), (Option[Sort], Sort, Token)], List[Token]) = {
    if(tokens.head.tok.equals(PROGRAM_VARIABLES_BLOCK)) {
      val (programVariables, remainder) = processProgramVariables(tokens)
      val (functions, finalRemainder) = processFunctionSymbols(remainder)
      (programVariables ++ functions, finalRemainder)
    }
    else if(tokens.head.tok.equals(FUNCTIONS_BLOCK)) {
      val (functions, remainder) = processFunctionSymbols(tokens)
      val (programVariables, finalRemainder) = processProgramVariables(remainder)
      (programVariables ++ functions, finalRemainder)
    }
    else if(tokens.head.tok.equals(VARIABLES_BLOCK)) {
      processVariables(tokens)
    }
    else {
      (Map(), tokens)
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
   * @param decls the type declarations known from the context
   * @param expr the expression parsed
   * @throws [[edu.cmu.cs.ls.keymaerax.parser.ParseException]] if the type analysis fails.
   */
  def typeAnalysis(decls: Map[(String, Option[Int]), (Option[Sort], Sort, Token)], expr: Expression): Boolean = {
    StaticSemantics.symbols(expr).forall({
      case f:Function =>
        val (declaredDomain,declaredSort, declarationToken) = decls.get((f.name,f.index)) match {
          case Some(d) => d
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
        val (declaredSort, declarationToken) = decls.get((x.name,x.index)) match {
          case Some((None,sort,token)) => (sort, token)
          case Some((Some(domain), sort, token)) => throw ParseException(s"Type analysis: ${x.name} was declared as a function but used as a non-function.", token.loc)
          case None => throw ParseException("type analysis" + ": " + "undefined symbol " + x + " with index " + x.index, x)
        }
        if (x.sort != declaredSort) throw ParseException(s"type analysis: ${x.prettyString} declared with sort $declaredSort but used where a ${x.sort} was expected.", declarationToken.loc)
        x.sort == declaredSort
      case _: UnitPredicational => true //@note needs not be declared
      case _: UnitFunctional => true //@note needs not be declared
      case _: DotTerm => true //@note needs not be declared
      case DifferentialSymbol(v) => decls.contains(v.name, v.index) //@note hence it is checked as variable already
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
  def processProgramVariables(tokens : List[Token]): (Map[(String, Option[Int]), (Option[Sort], Sort, Token)], List[Token]) = {
    if(tokens.head.tok.equals(PROGRAM_VARIABLES_BLOCK)) {
      val(progVarsSection, remainder) = tokens.span(x => !x.tok.equals(END_BLOCK))
        val progVarsTokens = progVarsSection.tail
        (processDeclarations(progVarsTokens, Map()), remainder.tail)
    }
    else (Map(), tokens)

  }

  def processFunctionSymbols(tokens: List[Token]) : (Map[(String, Option[Int]), (Option[Sort], Sort, Token)], List[Token]) = {
    if(tokens.head.tok.equals(FUNCTIONS_BLOCK)) {
      val(funSymbolsTokens, remainder) = tokens.span(x => !x.tok.equals(END_BLOCK))
      val funSymbolsSection = funSymbolsTokens.tail
      (processDeclarations(funSymbolsSection, Map()), remainder.tail)
    }
    else (Map[(String, Option[Int]), (Option[Sort], Sort, Token)](), tokens)
  }

  def processVariables(tokens: List[Token]) : (Map[(String, Option[Int]), (Option[Sort], Sort, Token)], List[Token]) = {
    if(tokens.head.tok.equals(VARIABLES_BLOCK)) {
      val(funSymbolsTokens, remainder) = tokens.span(x => !x.tok.equals(END_BLOCK))
      val funSymbolsSection = funSymbolsTokens.tail
      (processDeclarations(funSymbolsSection, Map()), remainder.tail)
    }
    else (Map(), tokens)
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
  private def parseDeclaration(ts : List[Token]) : (((String, Option[Int]), (Option[Sort], Sort, Token)), List[Token]) = {
    val sortToken = ts.head
    val sort = parseSort(sortToken, sortToken)

    val nameToken = ts.tail.head
    val nameTerminal : IDENT = ts.tail.head.tok match {
      case i : IDENT => i
      case x => throw new Exception("Expected an identifier but found " + x.getClass().getCanonicalName())
    }

    val afterName = ts.tail.tail //skip over IDENT and REAL/BOOL tokens.
    if(afterName.head.tok.equals(LPAREN)) {
      val (domainSort, remainder) = parseFunctionDomainSort(afterName, nameToken)

      checkInput(remainder.last.tok.equals(PERIOD),
        "Expected declaration to end with . but found " + remainder.last, remainder.last.loc, "Reading a declaration")

      (( (nameTerminal.name, nameTerminal.index), (Some(domainSort), sort, nameToken)), remainder.tail)
    }
    else if(afterName.head.tok.equals(PERIOD)) {
      (( (nameTerminal.name, nameTerminal.index) , (None, sort, nameToken) ), afterName.tail)
    }
    else {
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
  private def parseFunctionDomainSort(tokens : List[Token], of: Token) : (Sort, List[Token]) = {
    // Parse the domain sort.
    checkInput(tokens.length > 1, "domain sort expected in declaration", if (tokens.isEmpty) UnknownLocation else tokens.head.loc, "parsing function domain sort")
    checkInput(tokens.head.tok.equals(LPAREN), "function argument parentheses expected", tokens.head.loc, "parsing function domain sorts")

    val splitAtRparen = tokens.tail.span(x => !x.tok.equals(RPAREN))
    val domainElements = splitAtRparen._1

    checkInput(splitAtRparen._2.head.tok.equals(RPAREN),
      "unmatched LPAREN at end of function declaration. Intead, found: " + splitAtRparen._2.head, splitAtRparen._2.head.loc, "parsing function domain sorts")
    val remainder = splitAtRparen._2.tail

    val domain = domainElements.foldLeft(List[Sort]())((list: List[Sort], token: Token) =>
      if(token.tok.equals(COMMA)) list
      else list :+ parseSort(token, of)) //@todo clean up code and also support explicit association e.g. F((B, R), B)

    if(domain.isEmpty) {
      (Unit, remainder)
    }
    else {
      val fstArgSort = domain.head
      val domainSort = domain.tail.foldRight(fstArgSort)( (next, tuple) => Tuple(next, tuple) )
      (domainSort, remainder)
    }
  }

  private def parseSort(sortToken : Token, of: Token) : Sort = sortToken.tok match {
    case edu.cmu.cs.ls.keymaerax.parser.IDENT("R", _) => edu.cmu.cs.ls.keymaerax.core.Real
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
    case _ => throw new Exception(s"Expected an IDENT terminal but found ${terminal}")
  }

  private def isSort(terminal: Terminal) = terminal match {
    case REAL => true
    case BOOL => true
    case _    => false
  }

  /**
   * Takes a list of tokens and produces a mapping form names to sorts.
   * @param ts A list of tokens
   * @return A map from variable names and indices to a pair of:
   *          _1: The (optional) domain sort (if this is a function declaration
   *          _2: The sort of the variable, or the codomain sort of a function.
   */
  @tailrec
  private def processDeclarations(ts: List[Token],
                                  sortDeclarations: Map[(String, Option[Int]), (Option[Sort], Sort, Token)]) : Map[(String, Option[Int]), (Option[Sort], Sort, Token)] =
    if(ts.nonEmpty) {
      val (nextDecl, remainders) = parseDeclaration(ts)
      processDeclarations(remainders, sortDeclarations.updated(nextDecl._1, nextDecl._2))
    }
    else {
      sortDeclarations
    }

}