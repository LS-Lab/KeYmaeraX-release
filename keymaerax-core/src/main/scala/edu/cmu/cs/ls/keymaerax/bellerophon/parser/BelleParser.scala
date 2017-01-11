package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Term, Variable}
import edu.cmu.cs.ls.keymaerax.parser._
import BelleLexer.TokenStream

/**
  * The Bellerophon parser
  *
  * @author Nathan Fulton
  */
object BelleParser extends (String => BelleExpr) {
  private var invariantGenerator : Option[Generator.Generator[Formula]] = None
  private var DEBUG = false

  override def apply(s: String): BelleExpr = parseWithInvGen(s, None)

  def parseWithInvGen(s: String, g:Option[Generator.Generator[Formula]] = None): BelleExpr =
    KeYmaeraXProblemParser.firstNonASCIICharacter(s) match {
      case Some((loc, char)) => throw ParseException(s"Found a non-ASCII character when parsing tactic: ${char}", loc, "<unknown>", "<unknown>", "", "")
      case None => {
        invariantGenerator = g;
        parseTokenStream(BelleLexer(s))
      }
    }

  /** Runs the parser with debug mode turned on. */
  def debug(s: String) = {
    DEBUG = true
    apply(s)
    DEBUG = false
  }

  //region The LL Parser

  case class ParserState(stack: Stack[BelleItem], input: TokenStream) {
    def topString = stack.take(5).fold("")((s, e) => s + " " + e)

    def location = input.headOption match {
      case Some(theHead) => theHead.location
      case None => if(stack.length == 0) UnknownLocation else stack.top.defaultLocation()
    }
  }

  def parseTokenStream(toks: TokenStream): BelleExpr = {
    val result = parseLoop(ParserState(Bottom, toks))
    result.stack match {
      case Bottom :+ BelleAccept(e) => e
      case context :+ (BelleErrorItem(msg,loc,st)) => throw ParseException(msg, loc, "<unknown>", "<unknown>", "", st) //@todo not sure why I need the extra () around ErrorList.
      case _ => throw new AssertionError(s"Parser terminated with unexpected stack ${result.stack}")
    }
  }

  //@tailrec
  private def parseLoop(st: ParserState) : ParserState = {
    if(DEBUG) println(s"Current state: ${st}")

    st.stack match {
      case _ :+ (result : FinalBelleItem) => st
      case _ => parseLoop(parseStep(st))
    }
  }

  private def parseStep(st: ParserState) : ParserState = {
    val stack : Stack[BelleItem] = st.stack

    stack match {
      //@note This is a hack to support "blah & <(blahs)" in addition to "blah <(blahs)" without copying all of branch cases.
      //@todo Diable support for e<(e) entirely.
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(SEQ_COMBINATOR, seqCombinatorLoc) :+ BelleToken(BRANCH_COMBINATOR, branchCombinatorLoc) =>
        ParserState(
          r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(BRANCH_COMBINATOR, branchCombinatorLoc),
          st.input
        )

      //region Seq combinator
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(SEQ_COMBINATOR, combatinorLoc) =>
        st.input.headOption match {
          case Some(BelleToken(OPEN_PAREN, oParenLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(IDENT(name), identLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(BRANCH_COMBINATOR, branchCombinatorLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(OPTIONAL, optCombinatorLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(DONE, doneLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(_) => throw ParseException("A combinator should be followed by a full tactic expression", st)
          case None => throw ParseException("Tactic script cannot end with a combinator", combatinorLoc)
        }
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(SEQ_COMBINATOR, combatinorLoc) :+ ParsedBelleExpr(right, rightLoc) =>
        st.input.headOption match {
          case Some(BelleToken(SEQ_COMBINATOR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(KLEENE_STAR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(N_TIMES(_), _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(SATURATE, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case _ => ParserState(r :+ ParsedBelleExpr(left & right, leftLoc.spanTo(rightLoc)), st.input)
        }
      //endregion

      //region Either combinator
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(EITHER_COMBINATOR, combatinorLoc) => st.input.headOption match {
        case Some(BelleToken(OPEN_PAREN, oParenLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(BelleToken(IDENT(name), identLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(BelleToken(PARTIAL, partialLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(BelleToken(OPTIONAL, optCombinatorLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(_) => throw ParseException("A combinator should be followed by a full tactic expression", st)
        case None => throw ParseException("Tactic script cannot end with a combinator", combatinorLoc)
      }
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(EITHER_COMBINATOR, combatinorLoc) :+ ParsedBelleExpr(right, rightLoc) =>
        st.input.headOption match {
          case Some(BelleToken(EITHER_COMBINATOR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(KLEENE_STAR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(N_TIMES(_), _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(SATURATE, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(SEQ_COMBINATOR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case _ => {
            val parsedExpr = left | right
            parsedExpr.setLocation(combatinorLoc)
            ParserState(r :+ ParsedBelleExpr(parsedExpr, leftLoc.spanTo(rightLoc)), st.input)
          }
        }
      //endregion

      //region Branch combinator
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(BRANCH_COMBINATOR, combinatorLoc) => st.input.headOption match {
        case Some(BelleToken(OPEN_PAREN, oParenLoc)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(_) => throw ParseException("A branching combinator should be followed by an open paren", st)
        case None => throw ParseException("Tactic script cannot end with a combinator", combinatorLoc)
      }
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(BRANCH_COMBINATOR, combinatorLoc) :+ ParsedBelleExprList(branchTactics) => {
        assert(branchTactics.length > 0)
        val parsedExpr = left <(branchTactics.map(_.expr):_*)
        parsedExpr.setLocation(combinatorLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, leftLoc.spanTo(branchTactics.last.loc)), st.input)
      }
      //Allow doStuff<() for partial tacics that just leave all branches open. Useful for interactive tactic development.
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(BRANCH_COMBINATOR, combinatorLoc) :+ BelleToken(OPEN_PAREN, oParenLoc) :+ BelleToken(CLOSE_PAREN, cParenLoc) => {
        val parsedExpr = left <(Seq():_*)
        parsedExpr.setLocation(combinatorLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, leftLoc.spanTo(cParenLoc)), st.input)
      }
      //Also allow branching tactic that mention only a single branch. Although I'm not even quite sure we should allow this?
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(BRANCH_COMBINATOR, combinatorLoc) :+ BelleToken(OPEN_PAREN, oParenLoc) :+ ParsedBelleExpr(expr, exprLoc) :+ BelleToken(CLOSE_PAREN, cParenLoc) => {
        val parsedExpr = left <(Seq(expr):_*)
        parsedExpr.setLocation(combinatorLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, leftLoc.spanTo(cParenLoc)), st.input)
      }

      //Lists passed into the branch combinator
      case r :+ ParsedBelleExpr(e, eLoc) :+ BelleToken(COMMA, commaLoc) => st.input.headOption match {
        case Some(inputHead) =>
          if(hasOpenParen(st)) ParserState(st.stack :+ inputHead, st.input.tail)
          else throw ParseException("Comma-separated lists of expressions need to be surrounded by parentheses.", commaLoc)
        case None => throw ParseException("Tactics cannot end with a comma.", commaLoc)
      }

      /*
       * The next three cases fold a paren-delimited, comma-separated list of ParsedBelleExpr's into one ParsedBelleExprList:
       *
       * <(e1,...,ek,em,en) =>          by case 1
       * <(e1,...,ek,es     =>          by case 2
       * <(e1,...,es        => ... =>   by case 2
       * <(e1,es            =>          by case 2
       * <(es               =>          by case 3
       * <es                            Which is then handled by the BRANCH_COMBINATOR case.
       *
       * @todo still not sure about this. What about
       *    <((e1,e2,e3)) =>
       *    <((e1,es)     =>
       *    <((es)        =>
       *    error: paren mismatch!
       * But I think this is OK because branches should always have exactly one paren. I.e.
       *    (e)           well-formed
       *    <((e,e))      NOT well-formed.
       *    <((e))        NOT well-formed because a branch tactic should always contain more than one child...
       */
      case r :+ ParsedBelleExpr(em, emLoc) :+ BelleToken(COMMA, commaLoc) :+ ParsedBelleExpr(en, enLoc) :+ BelleToken(CLOSE_PAREN, closeParenLoc) => {
        val es = ParsedBelleExprList(Seq(ParsedBelleExpr(em, emLoc), ParsedBelleExpr(en, enLoc)))
        ParserState(r :+ es, st.input)
      }
      case r :+ ParsedBelleExpr(ek, ekLoc) :+ BelleToken(COMMA, commaLoc) :+ ParsedBelleExprList(es) => {
        val newList = ParsedBelleExprList(ParsedBelleExpr(ek, ekLoc) +: es)
        ParserState(r :+ newList, st.input)
      }
      case r :+ BelleToken(OPEN_PAREN, oParenLoc) :+ ParsedBelleExprList(es) => {
        ParserState(r :+ ParsedBelleExprList(es), st.input)
      }

      //endregion

      //region OnAll combinator
      case r :+ BelleToken(IDENT(name), loc) if name == ON_ALL.img => st.input match {
        case BelleToken(OPEN_PAREN, oParenLoc) :: tail =>
          //@note find matching closing parenthesis, parse inner expr, then continue with remainder
          var openParens = 1
          val (inner, BelleToken(CLOSE_PAREN, cParenLoc) :: remainder) = tail.span({
            case BelleToken(OPEN_PAREN, _) => openParens = openParens + 1; openParens > 0
            case BelleToken(CLOSE_PAREN, _) => openParens = openParens - 1; openParens > 0
            case _ => openParens > 0
          } )
          val innerExpr = parseTokenStream(inner)
          ParserState(r :+ ParsedBelleExpr(OnAll(innerExpr), loc.spanTo(cParenLoc)), remainder)
      }
      //endregion

      //region ? combinator
      case r :+ BelleToken(OPTIONAL, loc) => st.input match {
        case BelleToken(OPEN_PAREN, oParenLoc) :: tail =>
          //@note find matching closing parenthesis, parse inner expr, then continue with remainder
          var openParens = 1
          val (inner, BelleToken(CLOSE_PAREN, cParenLoc) :: remainder) = tail.span({
            case BelleToken(OPEN_PAREN, _) => openParens = openParens + 1; openParens > 0
            case BelleToken(CLOSE_PAREN, _) => openParens = openParens - 1; openParens > 0
            case _ => openParens > 0
          } )
          val innerExpr = parseTokenStream(inner)
          ParserState(r :+ ParsedBelleExpr(Idioms.?(innerExpr), loc.spanTo(cParenLoc)), remainder)
      }
      //endregion

      //region Stars and Repitition
      case r :+ ParsedBelleExpr(expr, loc) :+ BelleToken(KLEENE_STAR, starLoc) => {
        val parsedExpr = SaturateTactic(expr)
        parsedExpr.setLocation(starLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, loc.spanTo(starLoc)), st.input)
      }


      case r :+ ParsedBelleExpr(expr, loc) :+ BelleToken(N_TIMES(n), ntimesloc) => {
        val parsedExpr = RepeatTactic(expr, n)
        parsedExpr.setLocation(ntimesloc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, loc.spanTo(ntimesloc)), st.input)
      }

      case r :+ ParsedBelleExpr(expr, loc) :+ BelleToken(SATURATE, satloc) => {
        val paredExpr = SeqTactic(expr, SaturateTactic(expr))
        paredExpr.setLocation(satloc)
        ParserState(r :+ ParsedBelleExpr(paredExpr, loc.spanTo(satloc)), st.input)
      }

      //endregion

      //region partial

      //Suffix case.
      case r :+ ParsedBelleExpr(expr, exprLoc) :+ BelleToken(PARTIAL, partialLoc) => {
        val parsedExpr = expr.partial
        parsedExpr.setLocation(partialLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, exprLoc.spanTo(partialLoc)), st.input)
      }

      case r :+ BelleToken(PARTIAL, partialLoc) => st.input.headOption match {
        case None => throw ParseException("Found bare use of partial keyword", st)
        case Some(BelleToken(OPEN_PAREN, opnParenLoc)) =>  ParserState(st.stack :+ st.input.head, st.input.tail)
        case _ => throw ParseException("Unrecognized token stream", st)
      }

      case r :+ BelleToken(PARTIAL, partialLoc) :+ ParsedBelleExpr(expr, exprLoc) => {
        val parsedExpr = expr.partial
        parsedExpr.setLocation(partialLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, partialLoc.spanTo(exprLoc)), st.input)
      }
      //endregion

      //region done

      case r :+ BelleToken(DONE, doneLoc) => {
        val parsedExpr = TactixLibrary.done
        parsedExpr.setLocation(doneLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, doneLoc), st.input)
      }

      //endregion

      //region built-in tactics
      case r :+ BelleToken(IDENT(name), identLoc) =>
        try {
          if(!isOpenParen(st.input)) {
            val parsedExpr = constructTactic(name, None, identLoc)
            ParserState(r :+ ParsedBelleExpr(parsedExpr, identLoc), st.input)
          }
          else {
            val (args, remainder) = parseArgumentList(name, st.input)

            //Do our best at computing the entire range of positions that is encompassed by the tactic application.
            val endLoc = remainder match {
              case hd :: tl => hd.location
              case _ => st.input.last.location
            }
            val spanLoc = if(endLoc.end.column != -1) identLoc.spanTo(endLoc) else identLoc

            val parsedExpr = constructTactic(name, Some(args), identLoc)
            parsedExpr.setLocation(identLoc)
            ParserState(r :+ ParsedBelleExpr(parsedExpr, spanLoc), remainder)
          }
        }
        catch {
          case e : ClassCastException => throw ParseException(s"Could not convert tactic ${name} because the arguments passed to it were of incorrect type", e)
        }
      //endregion

      //region Parentheses around single expressions (parens around lists of expressions is covered in the branch combinator case.)
      case r :+ BelleToken(OPEN_PAREN, openParenLoc) => st.input.headOption match {
        case Some(head) => ParserState(st.stack :+ head, st.input.tail)
        case None => throw ParseException("Tactic cannot end with an open-paren.", openParenLoc)
      }

      //A single expression surrounded by parens. Different case from the list of expressions as is used as an argument to the Branch combinator.
      case r :+ BelleToken(OPEN_PAREN, openParenLoc) :+ expr :+ BelleToken(CLOSE_PAREN, closeParenLoc) =>
        if(isParsedExpression(expr)) ParserState(r :+ expr, st.input)
        else throw ParseException(s"Expected item surrounded by parentheses to be a parsable expression", closeParenLoc)
      //endregion

      case r :+ BelleToken(EOF, eofLoc) =>
        if(st.input.isEmpty) ParserState(r, st.input)
        else throw ParseException("Internal parser error: did not expect to find EOF while input stream is unempty.", UnknownLocation)

      case Bottom =>
        if(st.input.isEmpty) throw ParseException("Empty inputs are not parsable.", UnknownLocation)//ParserState(stack :+ FinalItem(), Nil) //Disallow empty inputs.
        else if(isCombinator(st.input.head)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isIdent(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isOpenParen(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isProofStateToken(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else throw ParseException("Bellerophon programs should start with identifiers, open parens, or partials.", st.input.head.location)

      case r :+ ParsedBelleExpr(e, loc) => st.input.headOption match {
        case Some(head) => ParserState(st.stack :+ st.input.head, st.input.tail)
        case None =>
          if(r == Bottom) ParserState(Bottom :+ BelleAccept(e), Nil)
          else throw ParseException(s"Cannot continue parsing because detected an infinite loop with stack ${st.topString}", st)
      }

      case _ => throw ParseException(s"Unrecognized token stream: ${st.topString}", st)
    }
  }

  //endregion

  //region Recognizers (i.e., predicates over the input stream that determine whether the stream matches some pattern)

  private def isIdent(toks : TokenStream) = toks match {
    case BelleToken(IDENT(_), _) :: _ => true
    case _ => false
  }

  private def isParsedExpression(item: BelleItem) = item match {
    case accepted : BelleAccept => true
    case expr : ParsedBelleExpr => true
    case _ => false
  }

  private def isOpenParen(toks : TokenStream) = toks match {
    case BelleToken(OPEN_PAREN, _) :: _ => true
    case _ => false
  }

  private def isCombinator(tok: BelleToken) = tok.terminal match {
    case SEQ_COMBINATOR => true
    case EITHER_COMBINATOR => true
    case BRANCH_COMBINATOR => true
    case KLEENE_STAR => true
    case SATURATE => true
    case OPTIONAL => true
    case _ => false
  }

  private def isProofStateToken(toks: TokenStream) = toks.headOption match {
    case Some(BelleToken(PARTIAL, _)) => true
    case Some(BelleToken(DONE, _)) => true
    case _ => false
  }


  //endregion

  //region Constructors (i.e., functions that construct [[BelleExpr]] and other accepted values from partially parsed inputs.

  /** Constructs a tactic using the reflective expression builder. */
  private def constructTactic(name: String, args : Option[List[TacticArg]], location: Location) : BelleExpr = {
    // Converts List[Either[Expression, Pos]] to List[Either[Seq[Expression], Pos]] by makikng a bunch of one-tuples.
    val newArgs = args match {
      case None => Nil
      case Some(argList) => argList.map(_ match {
        case Left(expression) => Left(Seq(expression))
        case Right(pl) => Right(pl)
      })
    }

    try {
      ReflectiveExpressionBuilder(name, newArgs, invariantGenerator)
    } catch {
      case e: ReflectiveExpressionBuilderExn => throw ParseException(e.getMessage + s" Encountered while parsing $name", location, e)
    }
  }

  /**
    * Consolidates all successive expression arguments into a single list.
    *
    * Example: 1=1,2=2,'L becomes (1=1,2=2),'L
    * Example: 1=1, 'L, 2=2 stays the smame.
    *
    * Could be used e.g. for diffInd type things to pass a list of formulas to a tactic without actually adding lists of formulas to the grammar.
    */
  @deprecated("This method implicitly converts a list of formula arguments to a single argument that is a list of formulas. This is necessary for ArgList tactics; i.e. tactics that take lists of formulas as arguments. These tactics that take lists of formulas as arguments are temporarily deprecated until they can be fully supported. Even then, we probably want explicit syntax for differentiating between a list of formula arguments and a list of formulas as an argument.", "4.2b1")
  private def consolidatedExpressions(args : Option[List[TacticArg]]) = args match {
      case None => Nil
      case Some(argList) => argList
        .foldLeft[List[Either[Seq[Expression], PositionLocator]]](Nil)((newArgs, arg) => {
        if(newArgs.length == 0) arg match {
          case Left(e) => newArgs :+ Left(Seq(e))
          case Right(pl) => newArgs :+ Right(pl)
        }
        else (newArgs.last, arg) match {
          case (_, Right(pl)) => newArgs :+ Right(pl)
          case (Right(pl), Left(expression)) => newArgs :+ Left(Seq(expression))
          case (Left(consolidatedExprs), Left(nextExpr)) => newArgs.dropRight(1) :+ Left(consolidatedExprs :+ nextExpr)
        }
      })
    }

  @deprecated("Replaced with a stack traversal.", "4.2b1")
  /** @todo Delete this code after testing that the common tactics did not break with new approach. */
  private def reduceExpressionList(st: ParserState) = {
    val list = st.stack.toList.reverse.span(_ match {
      case BelleToken(OPEN_PAREN, _) => false
      case _ => true
    })._2

    val remainingStack = st.stack.drop(list.length)

    //Remove the leading ( and trailing ) from the list.
    assert(list.headOption match {
      case Some(BelleToken(OPEN_PAREN, _)) => true
      case _ => false
    }, "First element of list should be a OPEN_PAREN")
    assert(list.last match {
      case BelleToken(CLOSE_PAREN, _) => true
      case _ => false
    }, "Last element of list should be a CLOSE_PAREN")
    val commaSepExprs = list.tail.dropRight(1)

    val onlyExprs = commaSepExprs.filter(x => x match {
      case BelleToken(COMMA, _) => false
      case e : ParsedBelleExpr => true
      case _ => {assert(false, s"Comma-separated expression list should only commas expressions and ParsedBelleExprs, but found ${x}"); ???}
     }).map(_.asInstanceOf[ParsedBelleExpr])

    val newItem = ParsedBelleExprList(onlyExprs)

    ParserState(remainingStack :+ newItem, st.input)
  }

  //endregion

  //region Ad-hoc Argument List Parser

  type TacticArg = Either[Expression, PositionLocator]

  /**
    * An ad-hoc parser for argument lists.
    *
    * @param input A TokenStream containing: arg :: "," :: arg :: "," :: arg :: "," :: ... :: ")" :: remainder
    * @return Parsed arguments and the remainder token string.
    */
  private def parseArgumentList(codeName: String, input: TokenStream) : (List[TacticArg], TokenStream) = input match {
    case BelleToken(OPEN_PAREN, oParenLoc) +: rest => {
      val (argList, closeParenAndRemainder) = rest.span(tok => tok.terminal != CLOSE_PAREN)

      //Ensure we actually found a close-paren and then compute the remainder.
      if (closeParenAndRemainder.isEmpty)
        throw ParseException("Expected argument list but could not find closing parenthesis.", input.head.location)
      assert(closeParenAndRemainder.head.terminal == CLOSE_PAREN)
      val remainder = closeParenAndRemainder.tail

      //Parse all the arguments.
      var nonPosArgCount = 0 //Tracks the number of non-positional arguments that have already been processed.

      def arguments(al: List[BelleToken]): List[TacticArg] = al match {
        case Nil => Nil
        case (tok@BelleToken(_: EXPRESSION, loc))::tail =>
          assert(DerivationInfo.hasCodeName(codeName), s"DerivationInfo should contain code name $codeName because it is called with expression arguments.")
          assert(nonPosArgCount < DerivationInfo(codeName).inputs.length, s"Too many expr arguments were passed to $codeName (Expected ${DerivationInfo(codeName).inputs.length} but found at least ${nonPosArgCount+1})")
          val theArg = parseArgumentToken(Some(DerivationInfo(codeName).inputs(nonPosArgCount)))(tok, loc)
          nonPosArgCount = nonPosArgCount + 1
          theArg +: arguments(tail)
        case BelleToken(SEARCH_SUCCEDENT, _)::BelleToken(matchKind, _)::BelleToken(expr: EXPRESSION, loc)::tail =>
          Right(Find.FindR(0, Some(expr.expression), exact=matchKind==EXACT_MATCH)) +: arguments(tail)
        case BelleToken(SEARCH_ANTECEDENT, _)::BelleToken(matchKind, _)::BelleToken(expr: EXPRESSION, loc)::tail =>
          Right(Find.FindL(0, Some(expr.expression), exact=matchKind==EXACT_MATCH)) +: arguments(tail)
        case BelleToken(SEARCH_EVERYWHERE, _)::BelleToken(matchKind, _)::BelleToken(expr: EXPRESSION, loc)::tail =>
          Right(new Find(0, Some(expr.expression), AntePosition(1), exact = matchKind==EXACT_MATCH)) +: arguments(tail)
        case tok::tail => parseArgumentToken(None)(tok, UnknownLocation) +: arguments(tail)
      }

      (arguments(removeCommas(argList, commaExpected=false)), remainder)
    }
  }

  /** Takes a COMMA-delimited list of arguments and extracts only the argument tokens.
    *
    * @see parseArgumentList */
  private def removeCommas(toks: TokenStream, commaExpected: Boolean) : List[BelleToken] = toks match {
    case BelleToken(COMMA, commaPos) :: Nil => throw ParseException("Expected argument but found none", commaPos)
    case BelleToken(COMMA, commaPos) :: r =>
      if(commaExpected) removeCommas(r, !commaExpected)
      else throw ParseException(s"Expected argument but found comma.", commaPos)
    case arg :: r => arg.terminal match {
      case terminal: TACTIC_ARGUMENT => arg +: removeCommas(r, !commaExpected)
      case _ =>
        assert(!isArgument(toks.head), "Inexhautive pattern matching in removeCommas.")
        throw ParseException(s"Expected tactic argument but found ${arg.terminal.img}", arg.location)
    }
    case Nil => Nil
  }

  /**
    *
    * @param expectedType The expected type of the argument..
    * @param tok The argument token that's currently being processed.
    * @return The argument corresponding to the current token.
    */
  private def parseArgumentToken(expectedType: Option[ArgInfo])(tok : BelleToken, loc: Location) : TacticArg = tok.terminal match {
    case terminal : TACTIC_ARGUMENT => terminal match {
      case ABSOLUTE_POSITION(posString) => Right(parseAbsolutePosition(posString, tok.location))
      case LAST_ANTECEDENT              => Right(LastAnte(0)) //@todo 0?
      case LAST_SUCCEDENT               => Right(LastSucc(0)) //@todo 0?
      case SEARCH_ANTECEDENT            => Right(Find.FindL(0, None)) //@todo 0?
      case SEARCH_SUCCEDENT             => Right(Find.FindR(0, None)) //@todo 0?
      case SEARCH_EVERYWHERE            => Right(new Find(0, None, AntePosition(1), exact = true)) //@todo 0?
      case tok : EXPRESSION       => {
        //@todo allow lists here as well. For now any consecutive list of formula arguments is parsed as a Seq[Formula]. See constructTactic.
        import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
        //Use the parsed result if it matches the expected type. Otherwise re-parse using a grammar-specific parser.
        assert(expectedType.nonEmpty, "When parsing an EXPRESSION argument an expectedType should be specified.")
        expectedType.get match {
          case ty:FormulaArg if tok.expression.isInstanceOf[Formula] => Left(tok.expression)
          case ty:FormulaArg => try {
            Left(tok.undelimitedExprString.asFormula)
          } catch {
            case exn: ParseException => throw ParseException(s"Could not parse ${tok.exprString} as a Formula, but a formula was expected. Error: $exn", loc, exn)
          }
          case ty:TermArg if tok.expression.isInstanceOf[Term] => Left(tok.expression)
          case ty:TermArg => try {
            Left(tok.undelimitedExprString.asTerm)
          } catch {
            case exn: ParseException => throw ParseException(s"Could not parse ${tok.exprString} as a Variable, but a term was expected. Error: $exn", loc, exn)
          }
          case ty:VariableArg if tok.expression.isInstanceOf[Variable] => Left(tok.expression)
          case ty:VariableArg => try {
            Left(tok.undelimitedExprString.asVariable)
          } catch {
            case exn: ParseException => throw ParseException(s"Could not parse ${tok.exprString} as a Variable, but a Variable was expected. Error: $exn", loc, exn)
          }
        }
      }
      case tok : EXPRESSION       => Left(tok.expression) //@todo allow lists here as well. For now any consecutive list of formula arguments is parsed as a Seq[Formula]. See constructTactic.
      case _ => throw ParseException(s"Expected a tactic argument (Belle Expression or position locator) but found ${terminal.img}", tok.location)
    }
    case _ => throw ParseException("Encountered non-tactic-argument terminal when trying to parse a tactic argument", tok.location)
  }

  /** Parses a string of the form int.int.int.int to a Bellerophon position.
    * Public because this is a useful utility function.
    *
    * @see [[parseArgumentToken]] */
  def parseAbsolutePosition(s : String, location: Location) : PositionLocator = {
    if(!s.contains(".")) Fixed(Position(parseInt(s, location)))
    else {
      val subPositionStrings = s.split('.')
      val subPositions = subPositionStrings.tail.map(x => parseInt(x, location, nonZero=false))
      Fixed(Position(parseInt(subPositionStrings.head, location), subPositions.toList))
    }
  }

  /** Parses s to a non-zero integer or else throws a ParseException pointing to location.
    *
    * @see [[parseAbsolutePosition]] */
  private def parseInt(s: String, location: Location, nonZero: Boolean = true) =
    try {
      val pos = Integer.parseInt(s)
      if (nonZero && pos == 0) throw ParseException("0 is not a valid absolute (sub)position -- must be (-inf, -1] \\cup [1, inf)", location)
      else pos
    }
    catch {
      case e : NumberFormatException => throw ParseException("Could not parse absolute position a (sequence of) integer(s)", location)
    }

  /** Argument tokens are positions and escaped expressions. */
  private def isArgument(tok: BelleToken) = tok.terminal match {
    case ABSOLUTE_POSITION(_) => true
    case SEARCH_ANTECEDENT    => true
    case SEARCH_SUCCEDENT     => true
    case SEARCH_EVERYWHERE    => true
    case EXPRESSION(_)        => true
    case _                    => false
  }

  /** Returns true if there's a currently open unmatched open paren. */
  private def hasOpenParen(st: ParserState) = {
    val reversedStack = st.stack.toList.zipWithIndex.reverse
    val lastOpenParen = reversedStack.find(_._1 match {
      case BelleToken(OPEN_PAREN, _) => true
      case _ => false
    })
    val lastCloseParen = reversedStack.find(_._1 match {
      case BelleToken(CLOSE_PAREN, _) => true
      case _ => false
    })

    (lastOpenParen, lastCloseParen) match {
      case (Some(open), Some(closed)) => open._2 > closed._2
      case (Some(open), None) => true
      case (None, _) => false
    }
  }

  //endregion

  //region Items processed/generated by the Bellerophon Parser

  private[parser] trait BelleItem {
    def defaultLocation() = this match {
      case BelleToken(x,l) => l
      case ParsedBelleExpr(x,l) => l
      case ParsedBelleExprList(xs) => xs match {
        case hd :: Nil => xs.head.loc
        case hd :: read => xs.head.loc.spanTo(xs.last.loc)
        case Nil => UnknownLocation
      }
      case ParsedPosition(x,l) => l
      case BelleAccept(e) => UnknownLocation
      case BelleErrorItem(msg, loc, st) => loc
    }
  }
  private trait FinalBelleItem
  private[parser] case class BelleToken(terminal: BelleTerminal, location: Location) extends BelleItem
  private case class ParsedBelleExpr(expr: BelleExpr, loc: Location) extends BelleItem
  private case class ParsedBelleExprList(exprs: Seq[ParsedBelleExpr]) extends BelleItem
  private case class ParsedPosition(pos: Position, loc: Location) extends BelleItem
  private case class BelleAccept(e: BelleExpr) extends BelleItem with FinalBelleItem
  private case class BelleErrorItem(msg: String, loc: Location, state: String) extends BelleItem with FinalBelleItem

  //endregion
}
