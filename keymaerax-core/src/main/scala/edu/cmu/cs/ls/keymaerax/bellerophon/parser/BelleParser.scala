package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import BelleLexer.TokenStream
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.parser.Declaration

import scala.annotation.tailrec
import scala.util.matching.Regex

/**
  * The Bellerophon parser
  *
  * @author Nathan Fulton
  * @see [[DLBelleParser]]
  */
object BelleParser extends TacticParser with Logging {
  case class DefScope[K, V](defs: scala.collection.mutable.Map[K, V] = scala.collection.mutable.Map.empty[K, V],
                            parent: Option[DefScope[K, V]] = None) {
    def get(key: K): Option[V] = defs.get(key) match {
      case Some(e) => Some(e)
      case None => parent match {
        case Some(parentScope) => parentScope.get(key)
        case None => None
      }
    }
  }

  override val tacticParser: String => BelleExpr = this
  override val expressionParser: Parser = Parser.parser
  override val printer: BelleExpr => String = BellePrettyPrinter

  /** Parses the string `s` as a Bellerophon tactic. Does not use invariant generators and does not expand definitions. */
  override def apply(s: String): BelleExpr = parseWithInvGen(s, None)

  /** Parses `t` backwards-compatible with definitions `defs` expanded in tactic arguments depending on
    * whether `t` expands symbols or uses substitutions explicitly or not. */
  def parseBackwardsCompatible(t: String, defs: Declaration): BelleExpr =
    if (tacticExpandsDefsExplicitly(t)) BelleParser.parseWithInvGen(t, None, defs)
    else if (tacticSubstsDefsExplicitly(t)) BelleParser.parseWithInvGen(t, None, defs)
    else parseWithInvGen(t, None, defs, expandAll=true) // backwards compatibility

  /** Parses the string `s` as a Bellerophon tactic. Uses optional invariant generator `g` and definitions `defs` to
    * expand function and predicate symbols. */
  def parseWithInvGen(s: String, g: Option[Generator.Generator[GenProduct]] = None,
                      defs: Declaration = Declaration(Map.empty), expandAll: Boolean = false): BelleExpr =
    firstUnacceptableCharacter(s) match {
      case Some((loc, char)) => throw ParseException(s"Found an unacceptable character when parsing tactic (allowed unicode: ${allowedUnicodeChars.toString}): $char", loc, "<unknown>", "<unknown>", "", "")
      case None => parseTokenStream(BelleLexer(s), DefScope[String, DefTactic](), g, defs, expandAll)
    }

  def parseWithTacticDefs(s: String, defs: Map[String, BelleExpr]): BelleExpr = {
    firstUnacceptableCharacter(s) match {
      case Some((loc, char)) => throw ParseException(s"Found an unacceptable character when parsing tactic (allowed unicode: ${allowedUnicodeChars.toString}): $char", loc, "<unknown>", "<unknown>", "", "")
      case None => parseTokenStream(BelleLexer(s), DefScope[String, DefTactic](scala.collection.mutable.Map[String, DefTactic](defs.map({
        case (n, t) => (n, DefTactic(n, t))
      }).toList:_*)), None, Declaration(Map.empty), expandAll = false)
    }
  }

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
    '←',
    '•'
  )

  private val TACTIC_EXPANDS: Regex = "(expand\\s*\"[^\"]*\")|(expandAllDefs)".r
  private val TACTICS_SUBSTS: Regex = """US\([^)]*\)""".r
  private val TACTIC_AUTO_EXPAND_DEFS_COMPATIBILITY = Configuration.getBoolean(Configuration.Keys.TACTIC_AUTO_EXPAND_DEFS_COMPATIBILITY).getOrElse(false)

  /** Detects whether a tactic string uses `expand "..."` or `expandAllDefs`.  */
  def tacticExpandsDefsExplicitly(s: String): Boolean = TACTIC_EXPANDS.findFirstIn(s).isDefined
  /** Detects whether a tactic string uses `US(...)`.  */
  def tacticSubstsDefsExplicitly(s: String): Boolean = TACTICS_SUBSTS.findFirstMatchIn(s).isDefined


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
      assert(lines != null && lines.nonEmpty,
        s"Expected a 'last' element but found $lines because there is a disallowed unicode character _${disallowedChars.mkString(" ")}_")
      val lineNumber = lines.length
      val columnNumber = lines.last.length + 1
      Some(new Region(lineNumber, columnNumber, lineNumber, columnNumber), nonAsciiCharacter)
    }
    else {
      //@todo change this assertion: assert(s.matches("\\A\\p{ASCII}*\\z"))
      None
    }
  }

  //region The LL Parser

  case class ParserState(stack: Stack[BelleItem], input: TokenStream) {
    def topString: String = stack.take(5).fold("")((s, e) => s + " " + e)

    def location: Location = input.headOption match {
      case Some(theHead) => theHead.location
      case None => if(stack.length == 0) UnknownLocation else stack.top.defaultLocation()
    }
  }

  /** Parses the token stream `toks`. Expands tactic abbreviations according to `tacticDefs`, function and predicate
    * symbols according to `defs`, and passes the invariant generator `g` on to tactics requiring a generator. */
  def parseTokenStream(toks: TokenStream, tacticDefs: DefScope[String, DefTactic],
                       g: Option[Generator.Generator[GenProduct]],
                       defs: Declaration, expandAll: Boolean): BelleExpr = {
    val result = parseLoop(ParserState(Bottom, toks), tacticDefs, g, defs, expandAll)
    result.stack match {
      case Bottom :+ BelleAccept(e) => if (expandAll && defs.substs.nonEmpty) ExpandAll(defs.substs) & e else e
      case _ :+ BelleErrorItem(msg,loc,st) => throw ParseException(msg, loc, "<unknown>", "<unknown>", "", st)
      case _ => throw new AssertionError(s"Parser terminated with unexpected stack ${result.stack}")
    }
  }

  @tailrec
  private def parseLoop(st: ParserState, tacticDefs: DefScope[String, DefTactic],
                        g: Option[Generator.Generator[GenProduct]],
                        defs: Declaration, expandAll: Boolean): ParserState = {
    logger.debug(s"Current state: $st")

    st.stack match {
      case _ :+ (_: FinalBelleItem) => st
      case _ => parseLoop(parseStep(st, tacticDefs, g, defs, expandAll), tacticDefs, g, defs, expandAll)
    }
  }

  private def parseInnerExpr(tokens: List[BelleToken], tacticDefs: DefScope[String, DefTactic],
                             g: Option[Generator.Generator[GenProduct]], defs: Declaration,
                             expandAll: Boolean): (BelleExpr, Location, List[BelleToken]) = tokens match {
    case BelleToken(OPEN_PAREN, oParenLoc) :: tail =>
      //@note find matching closing parenthesis, parse inner expr, then continue with remainder
      var openParens = 1
      val (inner, BelleToken(CLOSE_PAREN, cParenLoc) :: remainder) = tail.span({
        case BelleToken(OPEN_PAREN, _) => openParens = openParens + 1; openParens > 0
        case BelleToken(CLOSE_PAREN, _) => openParens = openParens - 1; openParens > 0
        case _ => openParens > 0
      })

      val innerExpr = parseLoop(ParserState(Bottom, inner),
        DefScope(scala.collection.mutable.Map.empty, Some(tacticDefs)), g, defs, expandAll)
      val result = innerExpr.stack match {
        case Bottom :+ BelleAccept(e) => e
        case _ :+ BelleErrorItem(msg,loc,st) => throw ParseException(msg, loc, "<unknown>", "<unknown>", "", st)
        case _ => throw new AssertionError(s"Parser terminated with unexpected stack ${innerExpr.stack}")
      }
      (result, oParenLoc.spanTo(cParenLoc), remainder)
  }

  private def parseStep(st: ParserState, tacticDefs: DefScope[String, DefTactic],
                        g: Option[Generator.Generator[GenProduct]],
                        defs: Declaration, expandAll: Boolean): ParserState = {
    val stack : Stack[BelleItem] = st.stack

    stack match {
      //@note This is a hack to support "blah & <(blahs)" in addition to "blah <(blahs)" without copying all of branch cases.
      case r :+ ParsedBelleExpr(left, leftLoc, None) :+ BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, _) :+ BelleToken(BRANCH_COMBINATOR, branchCombinatorLoc) =>
        ParserState(
          r :+ ParsedBelleExpr(left, leftLoc, None) :+ BelleToken(BRANCH_COMBINATOR, branchCombinatorLoc),
          st.input
        )

      //region Seq combinator
      case _ :+ ParsedBelleExpr(_, _, _) :+ BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, combatinorLoc) =>
        st.input.headOption match {
          case Some(BelleToken(OPEN_PAREN, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(IDENT(_), _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(BRANCH_COMBINATOR, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(OPTIONAL, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(ON_ALL, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(TACTIC, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(LET, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(EXPANDALLDEFS, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(EXPAND, _)) => ParserState(stack :+ st.input.head, st.input.tail)
          case Some(_) => throw BelleParseException("A combinator should be followed by a full tactic expression", st)
          case None => throw ParseException("Tactic script cannot end with a combinator", combatinorLoc)
        }
      case r :+ ParsedBelleExpr(left, leftLoc, None) :+ BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, _) :+ ParsedBelleExpr(right, rightLoc, None) =>
        st.input.headOption match {
          case Some(BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(KLEENE_STAR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(N_TIMES(_), _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(SATURATE, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(USING, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case _ => ParserState(r :+ ParsedBelleExpr(left & right, leftLoc.spanTo(rightLoc), None), st.input)
        }
      //endregion

      //region Either combinator
      case _ :+ ParsedBelleExpr(_, _, _) :+ BelleToken(EITHER_COMBINATOR, combatinorLoc) => st.input.headOption match {
        case Some(BelleToken(OPEN_PAREN, _)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(BelleToken(IDENT(_), _)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(BelleToken(PARTIAL, _)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(BelleToken(OPTIONAL, _)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(_) => throw BelleParseException("A combinator should be followed by a full tactic expression", st)
        case None => throw ParseException("Tactic script cannot end with a combinator", combatinorLoc)
      }
      case r :+ ParsedBelleExpr(left, leftLoc, None) :+ BelleToken(EITHER_COMBINATOR, combatinorLoc) :+ ParsedBelleExpr(right, rightLoc, None) =>
        st.input.headOption match {
          case Some(BelleToken(EITHER_COMBINATOR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(KLEENE_STAR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(N_TIMES(_), _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(SATURATE, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(SEQ_COMBINATOR | DEPRECATED_SEQ_COMBINATOR, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case Some(BelleToken(USING, _)) => ParserState(st.stack :+ st.input.head, st.input.tail)
          case _ =>
            val parsedExpr = left | right
            parsedExpr.setLocation(combatinorLoc)
            ParserState(r :+ ParsedBelleExpr(parsedExpr, leftLoc.spanTo(rightLoc), None), st.input)
        }
      //endregion

      //region Branch and Case combinator
      case _ :+ ParsedBelleExpr(_, _, _) :+ BelleToken(BRANCH_COMBINATOR, combinatorLoc) => st.input.headOption match {
        case Some(BelleToken(OPEN_PAREN, _)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(_) => throw BelleParseException("A branching combinator should be followed by an open paren", st)
        case None => throw ParseException("Tactic script cannot end with a combinator", combinatorLoc)
      }
      case r :+ ParsedBelleExpr(left, leftLoc, l) :+ BelleToken(BRANCH_COMBINATOR, combinatorLoc) :+ ParsedBelleExprList(branchTactics) =>
        assert(branchTactics.nonEmpty)
        val parsedExpr = {
          if (branchTactics.forall(_.label.isDefined)) left.switch(branchTactics.map(t => t.label.get -> t.expr):_*)
          else if (branchTactics.forall(_.label.isEmpty)) left <(branchTactics.map(_.expr):_*)
          else throw ParseException("Not all branches have labels", combinatorLoc)
        }
        parsedExpr.setLocation(combinatorLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, leftLoc.spanTo(branchTactics.last.loc), l), st.input)

      //Allow doStuff<() for partial tactics that just leave all branches open. Useful for interactive tactic development.
      case r :+ ParsedBelleExpr(left, leftLoc, l) :+ BelleToken(BRANCH_COMBINATOR, combinatorLoc) :+ BelleToken(OPEN_PAREN, _) :+ BelleToken(CLOSE_PAREN, cParenLoc) =>
        val parsedExpr = left <(Seq.empty[BelleExpr]:_*)
        parsedExpr.setLocation(combinatorLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, leftLoc.spanTo(cParenLoc), l), st.input)

      case _ :+ ParsedBelleExpr(_, _, _) :+ BelleToken(BRANCH_COMBINATOR, loc) :+ BelleToken(OPEN_PAREN, _) :+ ParsedBelleExpr(_, _, _) :+ BelleToken(CLOSE_PAREN, _) =>
        throw ParseException("Branch tactic has only a single child", loc)

      //Cases
      case _ :+ BelleToken(_: EXPRESSION, loc) => st.input.headOption match {
        case Some(BelleToken(COLON, _)) => ParserState(stack :+ st.input.head, st.input.tail)
        case Some(_) => throw BelleParseException("A case combinator must be followed by a ':'", st)
        case None => throw ParseException("Tactic script cannot end with a combinator", loc)
      }

      case _ :+ BelleToken(_: EXPRESSION, _) :+ BelleToken(COLON, _) => ParserState(stack :+ st.input.head, st.input.tail)

      case r :+ BelleToken(label: EXPRESSION, l1) :+ BelleToken(COLON, _) :+ ParsedBelleExpr(expr, l2, None) => st.input.headOption match {
        case Some(t@BelleToken(SEQ_COMBINATOR, _)) => ParserState(stack :+ t, st.input.tail)
        case Some(t@BelleToken(EITHER_COMBINATOR, _)) => ParserState(stack :+ t, st.input.tail)
        case Some(t@BelleToken(BRANCH_COMBINATOR, _)) => ParserState(stack :+ t, st.input.tail)
        case Some(t@BelleToken(OPTIONAL, _)) => ParserState(stack :+ t, st.input.tail)
        case Some(t@BelleToken(SATURATE, _)) => ParserState(stack :+ t, st.input.tail)
        case Some(t@BelleToken(KLEENE_STAR, _)) => ParserState(stack :+ t, st.input.tail)
        case Some(t@BelleToken(N_TIMES(_), _)) => ParserState(stack :+ t, st.input.tail)
        case Some(t@BelleToken(USING, _)) => ParserState(stack :+ t, st.input.tail)
        case _ => ParserState(r :+ ParsedBelleExpr(expr, l1.spanTo(l2), Some(label.undelimitedExprString.asLabel)), st.input)
      }
      case _ :+ BelleToken(_: EXPRESSION, _) :+ BelleToken(COLON, _) :+ ParsedBelleExpr(_, _, Some(l)) =>
        throw BelleParseException("Already labeled case '" + l.label + "' cannot be relabeled", st)

      //Lists passed into the branch combinator
      case _ :+ ParsedBelleExpr(_, _, _) :+ BelleToken(COMMA, commaLoc) => st.input.headOption match {
        case Some(inputHead) =>
          if (hasOpenParen(st)) ParserState(st.stack :+ inputHead, st.input.tail)
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
      case r :+ (e1: ParsedBelleExpr) :+ BelleToken(COMMA, _) :+ (e2: ParsedBelleExpr) :+ BelleToken(CLOSE_PAREN, _) =>
        ParserState(r :+ ParsedBelleExprList(Seq(e1, e2)), st.input)

      case r :+ (ek: ParsedBelleExpr) :+ BelleToken(COMMA, _) :+ ParsedBelleExprList(es) =>
        ParserState(r :+ ParsedBelleExprList(ek +: es), st.input)

      case r :+ BelleToken(OPEN_PAREN, _) :+ ParsedBelleExprList(es) =>
        ParserState(r :+ ParsedBelleExprList(es), st.input)

      //endregion

      //region OnAll combinator
      case r :+ BelleToken(ON_ALL, loc) =>
        val (innerExpr, innerLoc, remainder) = parseInnerExpr(st.input, tacticDefs, g, defs, expandAll)
        ParserState(r :+ ParsedBelleExpr(OnAll(innerExpr), loc.spanTo(innerLoc), None), remainder)
      //endregion

      //region ? combinator
      case r :+ BelleToken(OPTIONAL, loc) =>
        val (innerExpr, innerLoc, remainder) = parseInnerExpr(st.input, tacticDefs, g, defs, expandAll)
        ParserState(r :+ ParsedBelleExpr(Idioms.?(innerExpr), loc.spanTo(innerLoc.end), None), remainder)
      //endregion

      //region let
      case r :+ BelleToken(LET, loc) => st.input match {
        case BelleToken(OPEN_PAREN, _) :: BelleToken(expr: EXPRESSION, _) :: BelleToken(CLOSE_PAREN, _) :: BelleToken(IN, _) :: tail =>
          val (innerExpr, innerLoc, remainder) = parseInnerExpr(tail, tacticDefs, g, defs, expandAll)
          val (abbrv, value) = expr.undelimitedExprString.asFormula match {
            case Equal(a, v) => (a, v)
            case Equiv(a, v) => (a, v)
          }
          ParserState(r :+ ParsedBelleExpr(Let(abbrv, value, innerExpr), loc.spanTo(innerLoc.end), None), remainder)
      }
      //endregion

      //region tactic
      case r :+ BelleToken(TACTIC, loc) => st.input match {
        case BelleToken(IDENT(name), _) :: BelleToken(AS, _) :: tail =>
          if (tacticDefs.defs.contains(name)) throw BelleParseException(s"Tactic definition: unique name '$name' expected in scope", st)
          val (innerExpr, innerLoc, remainder) = parseInnerExpr(tail, tacticDefs, g, defs, expandAll)
          tacticDefs.defs(name) = DefTactic(name, innerExpr)
          ParserState(r :+ ParsedBelleExpr(DefTactic(name, innerExpr), loc.spanTo(innerLoc), None), remainder)
      }
      //endregion

      //region def
      case r :+ BelleToken(EXPAND, loc) => st.input match {
        case BelleToken(all@IDENT("All"), allLoc) :: tail =>
          // resolve clash with builtin tactic expandAll
          val parsedExpr = constructTactic(EXPAND.img+all.name, None, loc.spanTo(allLoc), tacticDefs, g, defs, expandAll)
          ParserState(r :+ ParsedBelleExpr(parsedExpr, loc.spanTo(allLoc), None), tail)
        case BelleToken(expr: EXPRESSION, identLoc) :: tail =>
          val x: NamedSymbol = expr.undelimitedExprString.asExpr match {
            case v: Variable => v
            case FuncOf(fn, _) => fn
            case PredOf(fn, _) => fn
            case p: ProgramConst => p
            case s: SystemConst => s
          }
          defs.substs.find(sp => sp.what match {
            case PredOf(Function(n, i, _, _, _), _) => n == x.name && i == x.index
            case FuncOf(Function(n, i, _, _, _), _) => n == x.name && i == x.index
            case ProgramConst(n, _) => n == x.name
            case SystemConst(n, _) => n == x.name
          }) match {
            case Some(s) => ParserState(r :+ ParsedBelleExpr(Expand(x, s), loc.spanTo(identLoc), None), tail)
            case None => throw BelleParseException(s"Expression definition not found: '${x.prettyString}'", st)
          }
      }
      case r :+ BelleToken(EXPANDALLDEFS, loc) =>
        //@note uses location information to distinguish file definitions from proof definitions (e.g., abstract loop invariant J(x))
        val (modelDefs, proofDefs) = defs.decls.partition({
          case (_, Signature(_, _, _, _, UnknownLocation)) => false
          case _ => true
        })
        val modelSubsts = Declaration(modelDefs).substs
        val modelExpand = if (modelSubsts.nonEmpty) Some(ExpandAll(modelSubsts)) else None
        // use all defs and filter so that right-hand sides of proof definitions get correctly elaborated
        val proofsExpand = defs.substs.filter(_.what match {
          case FuncOf(ns: Function, _) => proofDefs.exists({ case (Name(name, index), _) => name == ns.name && index == ns.index })
          case PredOf(ns: Function, _) => proofDefs.exists({ case (Name(name, index), _) => name == ns.name && index == ns.index })
          case ns: ProgramConst => proofDefs.exists({ case (Name(name, index), _) => name == ns.name && index == ns.index })
          case ns: SystemConst => proofDefs.exists({ case (Name(name, index), _) => name == ns.name && index == ns.index })
          case _ => false
        }).map(s => TactixLibrary.uniformSubstitute(USubst(s :: Nil))).reduceRightOption[BelleExpr](_ & _)
        val expand = (modelExpand, proofsExpand) match {
          case (Some(me), Some(pe)) => Some(pe & me)
          case (Some(me), None) => Some(me)
          case (None, Some(pe)) => Some(pe)
          case (None, None) => None
        }
        expand match {
          case Some(e) => ParserState(r :+ ParsedBelleExpr(e, loc, None), st.input)
          case None => st.input match {
            case BelleToken(SEQ_COMBINATOR, _) :: rest => ParserState(r, rest)
            case _ => ParserState(r, st.input)
          }
        }
      //endregion

      //region using

      case r :+ ParsedBelleExpr(expr, eLoc, l) :+ BelleToken(USING, _) => st.input match {
        case BelleToken(EXPRESSION(s, delims), esLoc) :: tail =>
          val fmls = s.stripPrefix(delims._1).stripSuffix(delims._2).split("::").map(_.trim).toList match {
            case "nil" :: Nil => Nil // explicit empty list
            case head :: Nil => Parser.parser.formulaParser(head) :: Nil // single-element lists without :: nil
            case scala.collection.:+(args, "nil") => args.map(Parser.parser.formulaParser) // all other lists
            case l => throw ParseException("Formula list in using \"" + l.mkString("::") + "\" must end in :: nil",
              esLoc, s, l.mkString("\"", "::", "::nil\""))
          }
          ParserState(r :+ ParsedBelleExpr(Using(fmls, expr), eLoc.spanTo(esLoc), l), tail)
      }

      //endregion

      //region Stars and Repitition
      case r :+ ParsedBelleExpr(expr, loc, l) :+ BelleToken(KLEENE_STAR, starLoc) =>
        val parsedExpr = SaturateTactic(expr)
        parsedExpr.setLocation(starLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, loc.spanTo(starLoc), l), st.input)

      case r :+ ParsedBelleExpr(expr, loc, l) :+ BelleToken(N_TIMES(n), ntimesloc) =>
        val parsedExpr = RepeatTactic(expr, n)
        parsedExpr.setLocation(ntimesloc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, loc.spanTo(ntimesloc), l), st.input)

      case r :+ ParsedBelleExpr(expr, loc, l) :+ BelleToken(SATURATE, satloc) =>
        val parsedExpr = SeqTactic(expr, SaturateTactic(expr))
        parsedExpr.setLocation(satloc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, loc.spanTo(satloc), l), st.input)

      //endregion

      //region partial

      //Suffix case.
      case r :+ ParsedBelleExpr(expr, exprLoc, l) :+ BelleToken(PARTIAL, partialLoc) =>
        val parsedExpr = PartialTactic(expr)
        parsedExpr.setLocation(partialLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, exprLoc.spanTo(partialLoc), l), st.input)

      case _ :+ BelleToken(PARTIAL, _) => st.input.headOption match {
        case None => throw BelleParseException("Found bare use of partial keyword", st)
        case Some(BelleToken(OPEN_PAREN, _)) =>  ParserState(st.stack :+ st.input.head, st.input.tail)
        case _ => throw BelleParseException("Unrecognized token stream", st)
      }

      case r :+ BelleToken(PARTIAL, partialLoc) :+ ParsedBelleExpr(expr, exprLoc, l) =>
        val parsedExpr = PartialTactic(expr)
        parsedExpr.setLocation(partialLoc)
        ParserState(r :+ ParsedBelleExpr(parsedExpr, partialLoc.spanTo(exprLoc), l), st.input)

      //endregion

      //region built-in tactics
      case r :+ BelleToken(IDENT(name), identLoc) =>
        try {
          if (!isOpenParen(st.input)) {
            val parsedExpr = constructTactic(name, None, identLoc, tacticDefs, g, defs, expandAll)
            ParserState(r :+ ParsedBelleExpr(parsedExpr, identLoc, None), st.input)
          } else {
            val (args, remainder) = parseArgumentList(name, st.input, defs, expandAll)

            //Do our best at computing the entire range of positions that is encompassed by the tactic application.
            val endLoc = remainder match {
              case hd :: _ => hd.location
              case _ => st.input.last.location
            }
            val spanLoc = if(endLoc.end.column != -1) identLoc.spanTo(endLoc) else identLoc

            val parsedExpr = constructTactic(name, Some(args), identLoc, tacticDefs, g, defs, expandAll)
            parsedExpr.setLocation(identLoc)
            ParserState(r :+ ParsedBelleExpr(parsedExpr, spanLoc, None), remainder)
          }
        }
        catch {
          case e : ClassCastException => throw ParseException(s"Could not convert tactic $name because the arguments passed to it were of incorrect type", e)
        }
      //endregion

      //region Parentheses around single expressions (parens around lists of expressions is covered in the branch combinator case.)
      case _ :+ BelleToken(OPEN_PAREN, openParenLoc) => st.input.headOption match {
        case Some(head) => ParserState(st.stack :+ head, st.input.tail)
        case None => throw ParseException("Tactic cannot end with an open-paren.", openParenLoc)
      }

      //A single expression surrounded by parens. Different case from the list of expressions as is used as an argument to the Branch combinator.
      case r :+ BelleToken(OPEN_PAREN, _) :+ expr :+ BelleToken(CLOSE_PAREN, closeParenLoc) =>
        if (isParsedExpression(expr)) ParserState(r :+ expr, st.input)
        else throw ParseException(s"Expected item surrounded by parentheses to be a parsable expression", closeParenLoc)
      //endregion

      case r :+ BelleToken(EOF, _) =>
        if (st.input.isEmpty) ParserState(r, st.input)
        else throw ParseException("Internal parser error: did not expect to find EOF while input stream is unempty.", UnknownLocation)

      case Bottom =>
        if(st.input.isEmpty) throw ParseException("Empty inputs are not parsable.", UnknownLocation)//ParserState(stack :+ FinalItem(), Nil) //Disallow empty inputs.
        else if(isStartingCombinator(st.input.head)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isIdent(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isOpenParen(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else if(isProofStateToken(st.input)) ParserState(stack :+ st.input.head, st.input.tail)
        else throw ParseException("Bellerophon programs should start with identifiers, open parens, or optional/doall/partial.", st.input.head.location)

      case r :+ ParsedBelleExpr(e, _, _) => st.input.headOption match {
        case Some(_) => ParserState(st.stack :+ st.input.head, st.input.tail)
        case None =>
          if (r == Bottom) ParserState(Bottom :+ BelleAccept(e), Nil)
          else throw BelleParseException(s"Cannot continue parsing because detected an infinite loop with stack ${st.topString}", st)
      }

      case _ => throw BelleParseException(s"Unrecognized token stream: ${st.topString}", st)
    }
  }

  //endregion

  //region Recognizers (i.e., predicates over the input stream that determine whether the stream matches some pattern)

  private def isIdent(toks : TokenStream) = toks match {
    case BelleToken(IDENT(_), _) :: _ => true
    case _ => false
  }

  private def isParsedExpression(item: BelleItem) = item match {
    case _: BelleAccept => true
    case _: ParsedBelleExpr => true
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
    case EXPANDALLDEFS => true
    case EXPAND => true
    case _ => false
  }

  private def isProofStateToken(toks: TokenStream) = toks.headOption match {
    case Some(BelleToken(PARTIAL, _)) => true
    case _ => false
  }


  //endregion

  //region Constructors (i.e., functions that construct [[BelleExpr]] and other accepted values from partially parsed inputs.

  /** Constructs a tactic using the reflective expression builder. */
  private def constructTactic(name: String, args : Option[List[TacticArg]], location: Location,
                              tacticDefs: DefScope[String, DefTactic], g: Option[Generator.Generator[GenProduct]],
                              defs: Declaration, expandAll: Boolean) : BelleExpr = {
    // Converts List[Either[Expression, Pos]] to List[Either[Seq[Expression], Pos]] by making a bunch of one-tuples.
    val newArgs = args match {
      case None => Nil
      case Some(argList) => argList.map({
        case Left(Nil) => Left(Nil)
        case Left(x :: xs) => Left(x :: xs)
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
        val t = ReflectiveExpressionBuilder(name, newArgs, g, defs)
        // backwards-compatibility with tactics that used definitions when they were auto-expanded immediately
        if (TACTIC_AUTO_EXPAND_DEFS_COMPATIBILITY && expandAll && defs.decls.exists(_._2.interpretation.nonEmpty)) {
          t.prettyString match {
            case "QE" | "smartQE" | "master" => ExpandAll(defs.substs) & t
            case text =>
              if (text.startsWith("ODE") ||
                text.startsWith("diffInvariant") ||
                text.startsWith("dI")
              ) ExpandAll(defs.substs) & t
              else t
          }
        } else t
      } catch {
        case e: ReflectiveExpressionBuilderExn =>
          throw ParseException(e.getMessage + s" Encountered while parsing $name", location, e)
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
  private def parseArgumentList(codeName: String, input: TokenStream, defs: Declaration,
                                expandAll: Boolean): (List[TacticArg], TokenStream) = input match {
    case BelleToken(OPEN_PAREN, _) +: rest =>
      val (argList, closeParenAndRemainder) = rest.span(tok => tok.terminal != CLOSE_PAREN)

      //Ensure we actually found a close-paren and then compute the remainder.
      if (closeParenAndRemainder.isEmpty)
        throw ParseException("Expected argument list but could not find closing parenthesis.", input.head.location)
      assert(closeParenAndRemainder.head.terminal == CLOSE_PAREN)
      val remainder = closeParenAndRemainder.tail

      def expand[T <: Expression](e: T): T =
        if (expandAll) defs.exhaustiveSubst(defs.elaborateToSystemConsts(defs.elaborateToFunctions(e)))
        else defs.elaborateToSystemConsts(defs.elaborateToFunctions(e))

      //Parse all the arguments.
      var nonPosArgCount = 0 //Tracks the number of non-positional arguments that have already been processed.

      def arguments(al: List[BelleToken]): List[TacticArg] = al match {
        case Nil => Nil
        case (tok@BelleToken(_: EXPRESSION | _: SUBSTITUTION_PAIR, loc))::tail =>
          if (!DerivationInfo.hasCodeName(codeName)) throw ParseException("Unknown tactic '" + codeName + "'", loc)
          val expectedInputs = DerivationInfo(codeName).persistentInputs
          if (nonPosArgCount >= expectedInputs.length) throw ParseException(
            s"Too many expr arguments were passed to $codeName (expected ${expectedInputs.map(_.name)} but found at least ${nonPosArgCount + 1} arguments)", loc)
          val theArg = parseArgumentToken(Some(expectedInputs(nonPosArgCount)), defs)(tok, loc) match {
            case Left(v: Expression) => Left(expand(v))
            case Left(v: List[Any]) => Left(v.map({
              case e: Expression => expand(e)
              case e => e
            }))
            case v => v
          }
          nonPosArgCount = nonPosArgCount + 1
          theArg +: arguments(tail)
        case BelleToken(ABSOLUTE_POSITION(posString), l1)::BelleToken(matchKind, _)::BelleToken(expr: EXPRESSION, l2)::tail =>
          val what: Formula = expr.expression match {
            case f: Formula => expand(f)
            case FuncOf(Function(name, idx, domain, _, _), child) => PredOf(Function(name, idx, domain, Bool), expand(child))
            case e => throw ParseException("Expected formula as exact position locator match, but got " + e.prettyString, l2)
            case e => throw ParseException("Expected formula as exact position locator match, but got " + e.toString, l2)
          }
          Right(parsePositionLocator(posString, l1.spanTo(l2), Some(what), exact=matchKind==EXACT_MATCH, defs)) +: arguments(tail)
        case BelleToken(p: BASE_POSITION, l1)::BelleToken(matchKind, _)::BelleToken(expr: EXPRESSION, l2)::tail =>
          Right(parsePositionLocator(p.positionString, l1.spanTo(l2), Some(expand(expr.expression)), exact=matchKind==EXACT_MATCH, defs)) +: arguments(tail)
        case BelleToken(p: BASE_POSITION, l1)::BelleToken(matchKind, _)::BelleToken(expr: EXPRESSION_SUB, l2)::tail =>
          Right(parsePositionLocator(p.positionString, l1.spanTo(l2), Some(expand(expr.expression._1)), expr.expression._2, exact=matchKind==EXACT_MATCH, defs)) +: arguments(tail)
        case tok::tail => parseArgumentToken(None, defs)(tok, UnknownLocation) +: arguments(tail)
      }

      (arguments(removeCommas(argList, commaExpected=false)), remainder)
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
      case _: TACTIC_ARGUMENT => arg +: removeCommas(r, !commaExpected)
      case _ =>
        assert(!isArgument(toks.head), "Inexhautive pattern matching in removeCommas.")
        throw ParseException(s"Expected tactic argument but found ${arg.terminal.img}", arg.location)
    }
    case Nil => Nil
  }

  /**
    * Parses a tactic argument token.
    * @param expectedType The expected type of the argument..
    * @param tok The argument token that's currently being processed.
    * @return The argument corresponding to the current token.
    */
  private def parseArgumentToken(expectedType: Option[ArgInfo], defs: Declaration)(tok: BelleToken, loc: Location): TacticArg = tok.terminal match {
    case terminal: TACTIC_ARGUMENT => terminal match {
      case ABSOLUTE_POSITION(posString) => Right(parsePositionLocator(posString, tok.location, None, exact=true, defs))
      case LAST_ANTECEDENT(posString)   => Right(parsePositionLocator(posString, tok.location, None, exact=true, defs))
      case LAST_SUCCEDENT(posString)    => Right(parsePositionLocator(posString, tok.location, None, exact=true, defs))
      case SEARCH_ANTECEDENT(posString) => Right(parsePositionLocator(posString, tok.location, None, exact=true, defs))
      case SEARCH_SUCCEDENT(posString)  => Right(parsePositionLocator(posString, tok.location, None, exact=true, defs))
      case SEARCH_EVERYWHERE(posString) => Right(parsePositionLocator(posString, tok.location, None, exact=true, defs))
      case tok: BELLE_EXPRESSION =>
        assert(expectedType.nonEmpty, "When parsing an EXPRESSION argument an expectedType should be specified.")
        parseArg(expectedType.get, tok.undelimitedExprString, loc)
      case _ => throw ParseException(s"Expected a tactic argument (Belle Expression or position locator) but found ${terminal.img}", tok.location)
    }
    case _ => throw ParseException("Encountered non-tactic-argument terminal when trying to parse a tactic argument", tok.location)
  }

  /** Parses string `undelim` according to the `ai` argument info. */
  private def parseArg(ai: ArgInfo, undelim: String, loc: Location): TacticArg = ai match {
    case _: PosInExprArg => Left(PosInExpr(undelim.split('.').filter(_.nonEmpty).map(_.toInt).toList))
    case _: StringArg => Left(undelim)
    case _: SubstitutionArg => try {
      Left(undelim.asSubstitutionPair)
    } catch {
      case exn: ParseException => throw ParseException(s"Could not parse $undelim as a substitution pair when a substitution pair was expected. Error: $exn", loc, exn)
    }
    case _: FormulaArg => try {
      Left(undelim.asFormula)
    } catch {
      case exn: ParseException => throw ParseException(s"Could not parse $undelim as a formula when a formula was expected. Error: $exn", loc, exn)
    }
    case _: TermArg => try {
      Left(undelim.asTerm)
    } catch {
      case exn: ParseException => throw ParseException(s"Could not parse $undelim as a term when a term was expected. Error: $exn", loc, exn)
    }
    case _: VariableArg => try {
      Left(undelim.asVariable)
    } catch {
      case exn: ParseException => throw ParseException(s"Could not parse $undelim as a variable when a variable was expected. Error: $exn", loc, exn)
    }
    case _: NumberArg => try {
      undelim.asExpr match {
        case n: Number => Left(n)
        case _ => throw ParseException(s"Could not parse $undelim as a number when a number was expected.", loc)
      }
    } catch {
      case exn: ParseException => throw ParseException(s"Could not parse $undelim as an expression when an expression was expected. Error: $exn", loc, exn)
    }
    case _: ExpressionArg => try {
      Left(undelim.asExpr)
    } catch {
      case exn: ParseException => throw ParseException(s"Could not parse $undelim as an expression when an expression was expected. Error: $exn", loc, exn)
    }
    case OptionArg(ai) => parseArg(ai, undelim, loc)
    case ListArg(ai) =>
      val listElems = undelim.split("::").map(_.trim)
      if (listElems.last == "nil") Left(listElems.dropRight(1).map(parseArg(ai, _, loc).left.get).toList)
      else if (listElems.length == 1) parseArg(ai, listElems.head, loc) // allow single-element lists without ::nil notation
      else throw ParseException(s"Could not parse $undelim as a list when a list of ${ai.sort} was expected; lists must end in :: nil", loc)
  }

  /** Parses a string of the form int.int.int.int to a Bellerophon position.
    * Public because this is a useful utility function.
    *
    * @see [[parseArgumentToken]] */
  def parsePositionLocator(s: String, location: Location, shape: Option[Expression], exact: Boolean,
                           defs: Declaration): PositionLocator = {
    val subPositionStrings = s.split('.')
    val subPositions = subPositionStrings.tail.map(parseInt(_, location, nonZero=false))
    parsePositionLocator(subPositionStrings.head, location, shape, PosInExpr(subPositions.toList), exact, defs)
  }

  /** Parses a position locator string. */
  def parsePositionLocator(s: String, location: Location, shape: Option[Expression], sub: PosInExpr,
                           exact: Boolean, defs: Declaration): PositionLocator = s match {
    //@note goal index is always 0 because we operate on single-subgoal provables
    //      could extend notation to 'L@1 or 'L@label
    case "'Llast" => LastAnte(0, sub)
    case "'Rlast" => LastSucc(0, sub)
    case "'L" => Find.FindL(0, shape, sub, exact, defs)
    case "'R" => Find.FindR(0, shape, sub, exact, defs)
    case "'_" => new Find(0, shape, AntePosition.base0(0, sub), exact, defs)
    case i => Fixed(parseInt(i, location), sub.pos, shape, exact)
  }

  /** Parses s to a non-zero integer or else throws a ParseException pointing to location.
    *
    * @see [[parsePositionLocator]] */
  private def parseInt(s: String, location: Location, nonZero: Boolean = true) =
    try {
      val pos = Integer.parseInt(s)
      if (nonZero && pos == 0) throw ParseException("0 is not a valid absolute (sub)position -- must be (-inf, -1] \\cup [1, inf)", location)
      else pos
    } catch {
      case _: NumberFormatException => throw ParseException("Could not parse absolute position a (sequence of) integer(s)", location)
    }

  /** Argument tokens are positions and escaped expressions. */
  private def isArgument(tok: BelleToken) = tok.terminal match {
    case ABSOLUTE_POSITION(_) => true
    case SEARCH_ANTECEDENT(_) => true
    case SEARCH_SUCCEDENT(_)  => true
    case SEARCH_EVERYWHERE(_) => true
    case EXPRESSION(_, _)     => true
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
      case (Some(_), None) => true
      case (None, _) => false
    }
  }

  //endregion

  //region Items processed/generated by the Bellerophon Parser

  private[parser] trait BelleItem {
    def defaultLocation(): Location = this match {
      case BelleToken(_, l) => l
      case ParsedBelleExpr(_, l, _) => l
      case ParsedBelleExprList(xs) => xs match {
        case h :: Nil => h.loc
        case h :: _ => h.loc.spanTo(xs.last.loc)
        case Nil => UnknownLocation
      }
      case ParsedPosition(_, l) => l
      case BelleAccept(_) => UnknownLocation
      case BelleErrorItem(_, loc, _) => loc
    }
  }
  private trait FinalBelleItem
  case class BelleToken(terminal: BelleTerminal, location: Location) extends BelleItem
  private case class ParsedBelleExpr(expr: BelleExpr, loc: Location, label: Option[BelleLabel]) extends BelleItem
  private case class ParsedBelleExprList(exprs: Seq[ParsedBelleExpr]) extends BelleItem
  private case class ParsedPosition(pos: Position, loc: Location) extends BelleItem
  private case class BelleAccept(e: BelleExpr) extends BelleItem with FinalBelleItem
  private case class BelleErrorItem(msg: String, loc: Location, state: String) extends BelleItem with FinalBelleItem

  //endregion
}
