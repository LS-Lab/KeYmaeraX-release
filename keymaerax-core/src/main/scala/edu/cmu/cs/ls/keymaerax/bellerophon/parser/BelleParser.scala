package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import BelleLexer.TokenStream
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXDeclarationsParser.Declaration
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser.Declaration

/**
  * The Bellerophon parser
  *
  * @author Nathan Fulton
  */
object BelleParser extends (String => BelleExpr) {
  private var invariantGenerator : Option[Generator.Generator[Expression]] = None
  private var definitions: Declaration = Declaration(Map())
  private var DEBUG = false

  private case class DefScope[K, V](defs: scala.collection.mutable.Map[K, V] = scala.collection.mutable.Map.empty[K, V],
                                    parent: Option[DefScope[K, V]] = None) {
    def get(key: K): Option[V] = defs.get(key) match {
      case Some(e) => Some(e)
      case None => parent match {
        case Some(parentScope) => parentScope.get(key)
        case None => None
      }
    }
  }

  override def apply(s: String): BelleExpr = parseWithInvGen(s, None)

  def parseWithInvGen(s: String, g: Option[Generator.Generator[Expression]] = None,
                      defs: Declaration = Declaration(Map())): BelleExpr =
    KeYmaeraXProblemParser.firstUnacceptableCharacter(s) match {
      case Some((loc, char)) => throw ParseException(s"Found a non-ASCII character when parsing tactic: $char", loc, "<unknown>", "<unknown>", "", "")
      case None =>
        invariantGenerator = g
        definitions = defs
        try {
          parseTokenStream(BelleLexer(s), DefScope[String, DefTactic](), DefScope[Expression, DefExpression]())
        } catch {
          case e: Throwable =>
            System.err.println("Error parsing\n" + s)
            throw e
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

  def parseTokenStream(toks: TokenStream, tacticDefs: DefScope[String, DefTactic],
                       exprDefs: DefScope[Expression, DefExpression]): BelleExpr = {
    val result = parseLoop(ParserState(Bottom, toks), tacticDefs, exprDefs)
    result.stack match {
      case Bottom :+ BelleAccept(e) => e
      case context :+ (BelleErrorItem(msg,loc,st)) => throw ParseException(msg, loc, "<unknown>", "<unknown>", "", st) //@todo not sure why I need the extra () around ErrorList.
      case _ => throw new AssertionError(s"Parser terminated with unexpected stack ${result.stack}")
    }
  }

  //@tailrec
  private def parseLoop(st: ParserState, tacticDefs: DefScope[String, DefTactic],
                        exprDefs: DefScope[Expression, DefExpression]) : ParserState = {
    if(DEBUG) println(s"Current state: ${st}")

    st.stack match {
      case _ :+ (result : FinalBelleItem) => st
      case _ => parseLoop(parseStep(st, tacticDefs, exprDefs), tacticDefs, exprDefs)
    }
  }

  private def parseInnerExpr(tokens: List[BelleToken],
                             tacticDefs: DefScope[String, DefTactic],
                             exprDefs: DefScope[Expression, DefExpression]): (BelleExpr, Location, List[BelleToken]) = tokens match {
    case BelleToken(OPEN_PAREN, oParenLoc) :: tail =>
      //@note find matching closing parenthesis, parse inner expr, then continue with remainder
      var openParens = 1
      val (inner, BelleToken(CLOSE_PAREN, cParenLoc) :: remainder) = tail.span({
        case BelleToken(OPEN_PAREN, _) => openParens = openParens + 1; openParens > 0
        case BelleToken(CLOSE_PAREN, _) => openParens = openParens - 1; openParens > 0
        case _ => openParens > 0
      })
      val innerExpr = parseTokenStream(inner,
        DefScope(scala.collection.mutable.Map.empty, Some(tacticDefs)),
        DefScope(scala.collection.mutable.Map.empty, Some(exprDefs)))
      (innerExpr, oParenLoc.spanTo(cParenLoc), remainder)
  }

  private def parseStep(st: ParserState, tacticDefs: DefScope[String, DefTactic],
                        exprDefs: DefScope[Expression, DefExpression]) : ParserState = {
    val stack : Stack[BelleItem] = st.stack

    stack match {
      //@note This is a hack to support "blah & <(blahs)" in addition to "blah <(blahs)" without copying all of branch cases.
      //@todo Diable support for e<(e) entirely.
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, seqCombinatorLoc) :+ BelleToken(BRANCH_COMBINATOR, branchCombinatorLoc) =>
        ParserState(
          r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(BRANCH_COMBINATOR, branchCombinatorLoc),
          st.input
        )

      //region Seq combinator
      case r :+ ParsedBelleExpr(_, _) :+ BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, combatinorLoc) =>
        st.input.headOption match {
          case Some(BelleToken(OPEN_PAREN, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(IDENT(_), _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(BRANCH_COMBINATOR, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(OPTIONAL, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(ON_ALL, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(DONE, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(TACTIC, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(LET, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(DEF, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(EXPAND, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(_) => throw ParseException("A combinator should be followed by a full tactic expression", st)
          case None => throw ParseException("Tactic script cannot end with a combinator", combatinorLoc)
        }
      case r :+ ParsedBelleExpr(left, leftLoc) :+ BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, _) :+ ParsedBelleExpr(right, rightLoc) =>
        st.input.headOption match {
          case Some(BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
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
          case Some(BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
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
      case r :+ BelleToken(ON_ALL, loc) =>
        val (innerExpr, innerLoc, remainder) = parseInnerExpr(st.input, tacticDefs, exprDefs)
        ParserState(r :+ ParsedBelleExpr(OnAll(innerExpr), loc.spanTo(innerLoc)), remainder)
      //endregion

      //region ? combinator
      case r :+ BelleToken(OPTIONAL, loc) =>
        val (innerExpr, innerLoc, remainder) = parseInnerExpr(st.input, tacticDefs, exprDefs)
        ParserState(r :+ ParsedBelleExpr(Idioms.?(innerExpr), loc.spanTo(innerLoc.end)), remainder)
      //endregion

      //region let
      case r :+ BelleToken(LET, loc) => st.input match {
        case BelleToken(OPEN_PAREN, _) :: BelleToken(expr: EXPRESSION, _) :: BelleToken(CLOSE_PAREN, _) :: BelleToken(IN, _) :: tail =>
          val (innerExpr, innerLoc, remainder) = parseInnerExpr(tail, tacticDefs, exprDefs)
          val (abbrv, value) = expr.undelimitedExprString.asFormula match {
            case Equal(a, v) => (a, v)
            case Equiv(a, v) => (a, v)
          }
          ParserState(r :+ ParsedBelleExpr(Let(abbrv, value, innerExpr), loc.spanTo(innerLoc.end)), remainder)
      }
      //endregion

      //region tactic
      case r :+ BelleToken(TACTIC, loc) => st.input match {
        case BelleToken(IDENT(name), _) :: BelleToken(AS, _) :: tail =>
          if (tacticDefs.defs.contains(name)) throw ParseException(s"Tactic definition: unique name '$name' expected in scope", st)
          val (innerExpr, innerLoc, remainder) = parseInnerExpr(tail, tacticDefs, exprDefs)
          tacticDefs.defs(name) = DefTactic(name, innerExpr)
          ParserState(r :+ ParsedBelleExpr(DefTactic(name, innerExpr), loc.spanTo(innerLoc)), remainder)
      }
      //endregion

      //region def
      case r :+ BelleToken(DEF, loc) => st.input match {
        case BelleToken(expr: EXPRESSION, exprLoc) :: tail =>
          val defFml = expr.undelimitedExprString.asFormula
          val (key, value) = defFml match {
            case Equal(fn@FuncOf(_, _), t) => (fn, t)
            case Equiv(p@PredOf(_, _), q) => (p, q)
          }
          if (exprDefs.defs.contains(key)) throw ParseException(s"Expression definition: unique '$key' expected in scope", st)
          exprDefs.defs(key) = DefExpression(defFml)
          ParserState(r :+ ParsedBelleExpr(DefExpression(defFml), loc.spanTo(exprLoc)), tail)
      }

      case r :+ BelleToken(EXPAND, loc) => st.input match {
        case BelleToken(expr: EXPRESSION, exprLoc) :: tail =>
          val key = expr.undelimitedExprString.asExpr
          exprDefs.get(key) match {
            case Some(x) => ParserState(r :+ ParsedBelleExpr(ExpandDef(x), loc.spanTo(exprLoc)), tail)
            case None => throw ParseException(s"Expression definition not found: '$key'", st)
          }

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
            val parsedExpr = constructTactic(name, None, identLoc, tacticDefs)
            ParserState(r :+ ParsedBelleExpr(parsedExpr, identLoc), st.input)
          }
          else {
            val (args, remainder) = parseArgumentList(name, st.input)

            //Do our best at computing the entire range of positions that is encompassed by the tactic application.
            val endLoc = remainder match {
              case hd :: _ => hd.location
              case _ => st.input.last.location
            }
            val spanLoc = if(endLoc.end.column != -1) identLoc.spanTo(endLoc) else identLoc

            val parsedExpr = constructTactic(name, Some(args), identLoc, tacticDefs)
            parsedExpr.setLocation(identLoc)
            ParserState(r :+ ParsedBelleExpr(parsedExpr, spanLoc), remainder)
          }
        }
        catch {
          case e : ClassCastException => throw ParseException(s"Could not convert tactic $name because the arguments passed to it were of incorrect type", e)
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
        else if(isStartingCombinator(st.input.head)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isIdent(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isOpenParen(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isProofStateToken(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else throw ParseException("Bellerophon programs should start with identifiers, open parens, or optional/doall/partial.", st.input.head.location)

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

  private def isStartingCombinator(tok: BelleToken) = tok.terminal match {
    case OPTIONAL => true
    case ON_ALL => true
    case LET => true
    case TACTIC => true
    case DEF => true
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
  private def constructTactic(name: String, args : Option[List[TacticArg]], location: Location, tacticDefs: DefScope[String, DefTactic]) : BelleExpr = {
    // Converts List[Either[Expression, Pos]] to List[Either[Seq[Expression], Pos]] by makikng a bunch of one-tuples.
    val newArgs = args match {
      case None => Nil
      case Some(argList) => argList.map({
        case Left(expression) => Left(Seq(expression))
        case Right(pl) => Right(pl)
      })
    }

    val tacticDef = tacticDefs.get(name)
    if (tacticDef.isDefined) {
      if (newArgs.nonEmpty) throw ParseException("Arguments for def tactics not yet supported", location)
      ApplyDefTactic(tacticDef.get)
    } else {
      try {
        ReflectiveExpressionBuilder(name, newArgs, invariantGenerator, definitions)
      } catch {
        case e: ReflectiveExpressionBuilderExn => throw ParseException(e.getMessage + s" Encountered while parsing $name", location, e)
      }
    }
  }

  //endregion

  //region Ad-hoc Argument List Parser

  type TacticArg = Either[Any, PositionLocator]

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
          Right(Find.FindR(0, Some(definitions.exhaustiveSubst(expr.expression)), exact=matchKind==EXACT_MATCH)) +: arguments(tail)
        case BelleToken(SEARCH_ANTECEDENT, _)::BelleToken(matchKind, _)::BelleToken(expr: EXPRESSION, loc)::tail =>
          Right(Find.FindL(0, Some(definitions.exhaustiveSubst(expr.expression)), exact=matchKind==EXACT_MATCH)) +: arguments(tail)
        case BelleToken(SEARCH_EVERYWHERE, _)::BelleToken(matchKind, _)::BelleToken(expr: EXPRESSION, loc)::tail =>
          Right(new Find(0, Some(definitions.exhaustiveSubst(expr.expression)), AntePosition(1), exact = matchKind==EXACT_MATCH)) +: arguments(tail)
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
          case _:StringArg => Left(tok.undelimitedExprString)
          case _:FormulaArg if tok.expression.isInstanceOf[Formula] => Left(tok.expression)
          case _:FormulaArg => try {
            Left(tok.undelimitedExprString.asFormula)
          } catch {
            case exn: ParseException => throw ParseException(s"Could not parse ${tok.exprString} as a Formula, but a formula was expected. Error: $exn", loc, exn)
          }
          case _:TermArg if tok.expression.isInstanceOf[Term] => Left(tok.expression)
          case _:TermArg => try {
            Left(tok.undelimitedExprString.asTerm)
          } catch {
            case exn: ParseException => throw ParseException(s"Could not parse ${tok.exprString} as a Term, but a term was expected. Error: $exn", loc, exn)
          }
          case _:VariableArg if tok.expression.isInstanceOf[Variable] => Left(tok.expression)
          case _:VariableArg => try {
            Left(tok.undelimitedExprString.asVariable)
          } catch {
            case exn: ParseException => throw ParseException(s"Could not parse ${tok.exprString} as a Variable, but a variable was expected. Error: $exn", loc, exn)
          }
          case _:ExpressionArg if tok.expression.isInstanceOf[Expression] => Left(tok.expression)
          case _:ExpressionArg => try {
            Left(tok.undelimitedExprString.asExpr)
          } catch {
            case exn: ParseException => throw ParseException(s"Could not parse ${tok.exprString} as an Expression, but an expression was expected. Error: $exn", loc, exn)
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
