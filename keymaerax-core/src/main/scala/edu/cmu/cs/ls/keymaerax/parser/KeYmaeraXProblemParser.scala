/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

import scala.annotation.tailrec

/**
 * Parses .kyx files.
 * @todo check sorts
 * Created by nfulton on 6/12/15.
 */
object KeYmaeraXProblemParser {
  def apply(input : String): Formula = try { parseProblem(KeYmaeraXLexer.inMode(input, ProblemFileMode()))._2 }
  catch {case e: ParseException => throw e.inContext(input)}

  def parseProblem(tokens: List[Token]) :  (Map[(String, Option[Int]), (Option[Sort], Sort)], Formula) = {
    val parser = KeYmaeraXParser
    val (decls, remainingTokens) = KeYmaeraXDeclarationsParser(tokens)
    checkInput(remainingTokens.nonEmpty, "Problem. block expected", UnknownLocation, "kyx problem input problem block")
    checkInput(remainingTokens.head.tok.equals(PROBLEM_BLOCK), "Problem. block expected", remainingTokens.head.loc, "kyx reading problem block")

    val (theProblem, eof) = remainingTokens.span(x => !x.tok.equals(END_BLOCK))
    checkInput(eof.length == 2 && eof.head.tok.equals(END_BLOCK) && eof.last.tok.equals(EOF),
      "Expected .kyx file to end with .<EOF> but found " + eof, eof.last.loc, "kyx problem end block parser")

    val problem : Formula = parser.parse(theProblem.tail :+ Token(EOF, UnknownLocation)) match {
      case f : Formula => f
      case expr : Expression => throw new ParseException("Expected problem to parse to a Formula, but found " + expr, UnknownLocation, "problem block")
    }

    parser.semanticAnalysis(problem) match {
      case None =>
      case Some(error) => throw new ParseException("Semantic analysis error", UnknownLocation, "parsed: " + parser.printer.stringify(problem) + "\n" + error)
    }

    require(KeYmaeraXDeclarationsParser.typeAnalysis(decls, problem), "type analysis")
    (decls, problem)
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
   *          _1: A mapping from variable name/index pairs to variable sorts, where the sort is a pair:
   *              _1: (Optionally) the domain sort of a function
   *              _2: The sort of a ProgramVariable, or the codomain sort of a function.
   *          _2: The list of remaining tokens.
   */
  def apply(tokens : List[Token]) : (Map[(String, Option[Int]), (Option[Sort], Sort)], List[Token]) =
    parseDeclarations(tokens)

  def parseDeclarations(tokens: List[Token]): (Map[(String, Option[Int]), (Option[Sort], Sort)], List[Token]) = {
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

  /**
   * Type analysis of expression according to the given type declarations decls
   * @param decls the type declarations known from the context
   * @param expr the expression parsed
   * @return whether expr conforms to the types declared in decls.
   */
  def typeAnalysis(decls: Map[(String, Option[Int]), (Option[Sort], Sort)], expr: Expression): Boolean = {
    StaticSemantics.signature(expr).forall(f => f match {
      case f:Function =>
        val (domain,sort) = decls.get((f.name,f.index)) match {
          case Some(d) => d
          case None => throw new ParseException("undefined symbol " + f, UnknownLocation, "type analysis")
        }
        f.sort == sort && (domain match {
          case Some(d) => f.domain == d
          case None => throw new ParseException(f.name + " is declared as non-function, but used as function", UnknownLocation, "type analysis")
        })
      case _ => true
    }) &&
    StaticSemantics.vars(expr).toSymbolSet.forall(x => x match {
      case x: Variable =>
        val sort = decls.get((x.name,x.index)) match {
          case Some((None,d)) => d
          case None => throw new ParseException("undefined symbol " + x + " with index " + x.index, UnknownLocation, "type analysis")
        }
        x.sort == sort
      case _ => true
    })
  }


  /**
   *
   * @param tokens Tokens in the parsed file.
   * @return A pair:
   *          _1: The list of Named Symbols.
   *          _2: The remainder of the file.
   */
  def processProgramVariables(tokens : List[Token]): (Map[(String, Option[Int]), (Option[Sort], Sort)], List[Token]) = {
    if(tokens.head.tok.equals(PROGRAM_VARIABLES_BLOCK)) {
      val(progVarsSection, remainder) = tokens.span(x => !x.tok.equals(END_BLOCK))
        val progVarsTokens = progVarsSection.tail
        (processDeclarations(progVarsTokens, Map()), remainder.tail)
    }
    else (Map(), tokens)

  }

  def processFunctionSymbols(tokens: List[Token]) : (Map[(String, Option[Int]), (Option[Sort], Sort)], List[Token]) = {
    if(tokens.head.tok.equals(FUNCTIONS_BLOCK)) {
      val(funSymbolsTokens, remainder) = tokens.span(x => !x.tok.equals(END_BLOCK))
      val funSymbolsSection = funSymbolsTokens.tail
      (processDeclarations(funSymbolsSection, Map()), remainder.tail)
    }
    else (Map(), tokens)
  }

  def processVariables(tokens: List[Token]) : (Map[(String, Option[Int]), (Option[Sort], Sort)], List[Token]) = {
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
  private def parseDeclaration(ts : List[Token]) : (((String, Option[Int]), (Option[Sort], Sort)), List[Token]) = {
    val sortToken = ts.head
    val sort = parseSort(sortToken)

    val nameToken : IDENT = ts.tail.head.tok match {
      case i : IDENT => i
      case x => throw new Exception("Expected identifier token (IDENT) but found " + x.getClass().getCanonicalName())
    }

    val afterName = ts.tail.tail //skip over IDENT and REAL/BOOL tokens.
    if(afterName.head.tok.equals(LPAREN)) {
      val (domainSort, remainder) = parseFunctionDomainSort(afterName)

      checkInput(remainder.last.tok.equals(PERIOD),
        "Expected declaration to end with . but found " + remainder.last, remainder.last.loc, "Reading a declaration")

      (( (nameToken.name, nameToken.index), (Some(domainSort), sort)), remainder.tail)
    }
    else if(afterName.head.tok.equals(PERIOD)) {
      (( (nameToken.name, nameToken.index) , (None, sort) ), afterName.tail)
    }
    else {
      throw new ParseException("Expected complete declaration but could not find terminating period", afterName.head.loc, "declaration parse")
    }
  }

  /**
   *
   * @param tokens A list of tokens that begins like: (R|B, ...).
   * @return A pair:
   *          _1: The sort of the entire function,
   *          _2: The reamining tokens.
   */
  private def parseFunctionDomainSort(tokens : List[Token]) : (Sort, List[Token]) = {
    // Parse the domain sort.
    checkInput(tokens.length > 1, "domain sort expected in declaration", if (tokens.isEmpty) UnknownLocation else tokens.head.loc, "parsing function domain sort")
    checkInput(tokens.head.tok.equals(LPAREN), "function argument parentheses expected", tokens.head.loc, "parsing function domain sorts")

    val splitAtRparen = tokens.tail.span(x => !x.tok.equals(RPAREN))
    val domainElements = splitAtRparen._1

    checkInput(splitAtRparen._2.head.tok.equals(RPAREN),
      "unmatched LPAREN at end of function declaration. Intead, found: " + splitAtRparen._2.head, splitAtRparen._2.head.loc, "parsing function domain sorts")
    val remainder = splitAtRparen._2.tail

    val domain = domainElements.foldLeft(List[Sort]())((list, token) =>
      if(token.tok.equals(COMMA)) list
      else list :+ parseSort(token))

    if(domain.isEmpty) {
      (Unit, remainder)
    }
    else {
      val fstArgSort = domain.head
      val domainSort = domain.tail.foldLeft(fstArgSort)( (tuple, next) => Tuple(tuple, next) )
      (domainSort, remainder)
    }
  }

  private def parseSort(sortToken : Token) : Sort = sortToken.tok match {
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
    case _ => throw new ParseException("Expected sort token but found " + sortToken, sortToken.loc, "parse sort")
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
                                  sortDeclarations: Map[(String, Option[Int]), (Option[Sort], Sort)]) : Map[(String, Option[Int]), (Option[Sort], Sort)] =
    if(ts.nonEmpty) {
      val (nextDecl, remainders) = parseDeclaration(ts)
      processDeclarations(remainders, sortDeclarations.updated(nextDecl._1, nextDecl._2))
    }
    else {
      sortDeclarations
    }

}