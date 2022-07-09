/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Bellerophon tactic parser for Differential Dynamic Logic.
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.macros.{ArgInfo, DerivationInfo, ExpressionArg, FormulaArg, GeneratorArg, ListArg, NumberArg, OptionArg, PosInExprArg, StringArg, SubstitutionArg, TermArg, VariableArg}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import edu.cmu.cs.ls.keymaerax.parser.{DLParser, Declaration, Parser}
import fastparse._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.parser.DLParser.{fullExpression, parseException}

import scala.collection.immutable._
import scala.util.Try

/**
  * Bellerophon tactic parser for Differential Dynamic Logic reads input strings in the concrete syntax of
  * Bellerophon tactics for KeYmaera X. It uses `tacticProvider` to map names and inputs to concrete tactic expressions.
  * @author Andre Platzer
  * @see [[BelleParser]]
  */
class DLBelleParser(override val printer: BelleExpr => String,
                    tacticProvider: (String, List[Either[Seq[Any], PositionLocator]], Declaration) => BelleExpr) extends DLTacticParser {
  /** Definitions, should be provided by the outer parser through [[setDefs]]. */
  private var defs: Declaration = Declaration(Map.empty)

  /** Which formula/term/program parser this archive parser uses. */
  private val expParser = DLParser

  /** Stores defined tactics. */
  private val tactics = scala.collection.mutable.Map.empty[String, DefTactic]

  override val tacticParser: String => BelleExpr = this
  override val expressionParser: Parser = DLParser

  /** @inheritdoc */
  override def apply(input: String, defs: Declaration): BelleExpr = {
    setDefs(defs)
    setDefTactics(Map.empty)
    belleParser(input)
  }

  /** Sets the definitions to be used when parsing tactic expressions. Expected to be set
    * before [[apply]] or [[tactic]] are used. */
  override def setDefs(defs: Declaration): Unit = this.defs = defs

  /** @inheritdoc */
  override def setDefTactics(defs: Map[String, DefTactic]): Unit = {
    tactics.clear
    defs.foreach(tactics += _)
  }

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  //@todo store the parser for speed
  val belleParser: String => BelleExpr = (s => fastparse.parse(s, fullTactic(_)) match {
    case Parsed.Success(value, _) => value
    case f: Parsed.Failure => throw parseException(f)
  })

  import JavaWhitespace._

  def fullTactic[_: P]: P[BelleExpr] = {
    setDefTactics(Map.empty)
    Start ~ tactic ~ End
  }

  private def fixedLocator[_: P](expr: Expression, p: Position, locator: (Position, Expression) => Fixed): P[Fixed] = {
    expr.sub(p.inExpr) match {
      case Some(e) => Pass(locator(p, e))
      case None =>
        // should never happen because either posIn is top-level or was parsed from expr
        Fail.opaque("Sub-position " + p.inExpr.prettyString + " to point to a formula or term inside " + expr.prettyString)
    }
  }

  def posInExpr[_: P]: P[PosInExpr] = P(("." ~~/ natural).repX.map(is => PosInExpr(is.toList)))
  def shape[_: P]: P[(String, (Expression, PosInExpr))] = P( ("==" | "~=").!./ ~ escapedPositionExpression )
  def position[_: P]: P[Position] = P( integer ~~ posInExpr).map({ case (j,js) => Position(j) ++ js })
  def positionLocator[_: P]: P[PositionLocator] = P( position ~~ shape.?).flatMap({
    case (p,None) => Pass(Fixed(p))
    case (p,Some(("==",(expr,posIn)))) if p.isTopLevel || posIn.pos.isEmpty =>
      if (p.isTopLevel) fixedLocator(expr, p ++ posIn, (p, e) => Fixed(p, Some(e), exact=true)) // check #...# sub-locator
      else Pass(Fixed(p, Some(expr), exact=true)) //@note expr already points verbatim to the sub-position, e.g. 2.1.1=="x"
    case (p,Some(("==",(expr,posIn)))) if p.inExpr == posIn =>
      fixedLocator(expr, p, (p, e) => Fixed(p, Some(e), exact=true)) //@note check e.g. 2.1=="[x:=1;]#x=1#" consistent
    case (p,Some(("~=",(expr,posIn)))) if p.isTopLevel || posIn.pos.isEmpty =>
      if (p.isTopLevel) fixedLocator(expr, p ++ posIn, (p, e) => Fixed(p, Some(e), exact=false)) // check #...# sub-locator
      else Pass(Fixed(p, Some(expr), exact=false)) //@note expr already points verbatim to the sub-position, e.g. 2.1.1~="x"
    case (p,Some(("~=",(expr,posIn)))) if p.inExpr == posIn =>
      fixedLocator(expr, p, (p, e) => Fixed(p, Some(e), exact=false)) //@note check e.g. 2.1~="[x:=1;]#x=1#" consistent
    case (p,Some((_, (_, posIn)))) => Fail.opaque("Non-conflicting sub-positions (but " +
      p.inExpr.prettyString + " != " + posIn.prettyString + ")")
  })
  def searchLocator[_: P]: P[PositionLocator] = P(
    ("'Llast".! ~~ posInExpr)./.map({ case (_, js) => LastAnte(0, js) })
      | ("'Rlast".! ~~ posInExpr)./.map({ case (_, js) => LastSucc(0, js) })
      | (("'L" | "'R").!./ ~ shape.?).map({
        case ("'L",None) =>
          Find.FindL(0, None, HereP, exact = true, defs)
        case ("'R",None) =>
          Find.FindR(0, None, HereP, exact = true, defs)
        case ("'L",Some(("==",(expr,posIn)))) =>
          Find.FindL(0, Some(expr), posIn, exact = true, defs)
        case ("'R",Some(("==",(expr,posIn)))) =>
          Find.FindR(0, Some(expr), posIn, exact = true, defs)
        case ("'L",Some(("~=",(expr,posIn)))) =>
          Find.FindL(0, Some(expr), posIn, exact = false, defs)
        case ("'R",Some(("~=",(expr,posIn)))) =>
          Find.FindR(0, Some(expr), posIn, exact = false, defs)
      })
  )

  def locator[_: P]: P[PositionLocator] = P( positionLocator | searchLocator )

  def substPair[_: P]: P[SubstitutionPair] = P(
    // If the left side of the substitution is a term, so must the right hand side be,
    // BUT perhaps the left side is ambiguous and the right side is a formula. So in
    // this case both must be false. :(
    (NoCut(formula ~ "~>" ~ formula) |
      term(false) ~ "~>" ~ term(false) |
      (DLParser.systemSymbol | DLParser.programSymbol) ~ "~>" ~ program).
      map(pair => SubstitutionPair(pair._1, pair._2))
  )

  def argList[_: P,A](p: => P[A]): P[List[A]] = P(
    // Can be nil and nothing else (note this is before trying p,
    // because p may also accept nil, but we should prefer this case)
    "nil".!.map(_ => Nil) |
      // Or it's a single p
      // which might be followed by (:: p)* (:: nil)
      (p ~/ (("::" ~ !"nil" ~/ p).rep ~ "::"./ ~ "nil").?).map({
        case (fst, None) => List(fst)
        case (fst, Some(rest)) => fst :: rest.toList
      })
    )

  def argumentInterior[_: P](argInfo: ArgInfo): P[Seq[Any]] = P(
    argInfo match {
      case FormulaArg(name, allowsFresh) => formula.map(f => List(defs.elaborateToSystemConsts(defs.elaborateToFunctions(f))))
      case TermArg(name, allowsFresh) => term(true).map(t => List(defs.elaborateToFunctions(t)))
      case ExpressionArg(name, allowsFresh) =>
        // I feel like we should never actually hit this because of the cases before it, but ???
        expression.map(e => List(defs.elaborateToSystemConsts(defs.elaborateToFunctions(e))))
      case VariableArg(name, allowsFresh) => DLParser.variable.map(List(_))
      case GeneratorArg(name) => Fail.opaque("unimplemented: generator argument")
      case StringArg(name, allowsFresh) => DLParser.stringInterior.map(List(_))
      case SubstitutionArg(name, allowsFresh) => (("(" ~/ substPair ~ ")") | substPair).map(List(_))
      case PosInExprArg(name, allowsFresh) => posInExpr.map(List(_))
      case OptionArg(arg) => Fail.opaque("Optional argument cannot appear recursively in a different argument type")
      case ListArg(arg) =>
        argList(argumentInterior(arg)).map(_.flatten)
      case NumberArg(_, _) => DLParser.number.map(List(_))
    }
  )

  def argument[_: P](argInfo: ArgInfo): P[Seq[Any]] = P(
    "\"" ~/ argumentInterior(argInfo) ~ "\""
  )(s"Argument ${argInfo.name}: ${argInfo.sort}",implicitly)

  //@note arguments have the funky type List[Either[Seq[Any], PositionLocator]]
  // I believe this is really intended to represent
  //      (List[Seq[Any]], Option[PositionLocator])
  // but squished together, thus why this parser has this type    (- JG)
  def argumentList[_: P](isStart: Boolean, args: List[ArgInfo], numPosArgs: Int): P[(List[Seq[Any]],List[PositionLocator])] = P(
    // If isStart, then we don't expect preceding ","
    // before each arg, but if not isStart then we do.
    args match {
      case Nil => // No more arguments, try parsing a position locator
        ",".rep(exactly=if (isStart || numPosArgs == 0) 0 else 1) ~/ locator.rep(exactly=numPosArgs, sep=",").map(loc => (Nil, loc.toList))
      case (arg: ListArg) :: Nil if isStart => // sole list argument may omit "nil"
        for {
          arg <- argument(arg).?
          // Then the position locator (note if arg is Some(..) then we are no longer at the start)
          pair <- argumentList(isStart && arg.isEmpty, Nil, numPosArgs)
        } yield ( List(arg.getOrElse(Seq.empty[Any])) ++ pair._1, pair._2)
      case OptionArg(arg) :: rest => // Optional argument
        for {
          // Try parsing argument, @note no cut after , because subsequent argumentList expects again , if optional argument does not succeed
          arg <- (if (isStart) argument(arg) else "," ~ argument(arg)).?
          // Then the rest of the arguments (note if arg is Some(..) then we are no longer at the start)
          pair <- argumentList(isStart && arg.isEmpty, rest, numPosArgs)
        } yield (arg.toSeq.flatten.map(List(_)).toList ++ pair._1, pair._2)
      case arg :: rest =>
        for {
          // Parse argument (no longer optional)
          arg <- if (isStart) argument(arg) else ","./ ~ argument(arg)
          // We can't be at the start now
          pair <- argumentList(isStart = false, rest, numPosArgs)
        } yield (arg :: pair._1, pair._2)
    }
  )

  def tacticSymbol[_: P]: P[String] = P(ident).map({case (n,None) => n case (n,Some(idx)) =>n + "_" + idx})
  def atomicTactic[_: P]: P[BelleExpr] = P(tacticSymbol ~ !"("./).map(t => try {
    tacticProvider(t, Nil, defs)
  } catch {
    case _: ReflectiveExpressionBuilderExn =>
      ApplyDefTactic(tactics(t))
      //@todo Pass/Fail does not compile here
  })

  def at[_: P]: P[BelleExpr] = P(
    (tacticSymbol ~~ "("./).flatMap(tacName => {
      val di = DerivationInfo.ofCodeName(tacName)
      val argInfos = di.persistentInputs
      val numPosArgs = di.numPositionArgs
      argumentList(isStart = true, argInfos, numPosArgs).map({
        case (args, pos) => (tacName, args.map(Left(_)) ++ pos.map(Right(_)))
      })
    }) ~ ")"
  )("tactic(...)",implicitly).
    map({case (t,args) => tacticProvider(t, args, defs)})

  def builtinTactic[_: P]: P[BelleExpr] = (
    ("doall" ~ "(" ~/ tactic ~ ")").map(OnAll) |
    ("partial" ~ "(" ~/ tactic ~ ")").map(PartialTactic(_, None)) |
    ("let" ~ "(" ~ "\"" ~/ DLParser.comparison ~ "\"" ~ ")" ~ "in" ~ "(" ~/ tactic ~ ")").flatMap({
      case (Equal(l, r), t) => Pass(Let(l, r, t))
      case (c, _) => Fail("Abbreviation of the shape f()=e (but got " + c.prettyString + ")")
    }) |
    ("tactic" ~ tacticSymbol ~ "as" ~/ baseTac).flatMapX({ case (s, t) =>
      if (tactics.contains(s)) Fail("Unique name " + s)
      else if (Try(tacticProvider(s, Nil, defs)).toOption.isDefined) Fail("Tactic name " + s + " is builtin, please use a different name")
      else {
        tactics += (s -> DefTactic(s, t))
        Pass(tactics(s))
      }
    }) |
    ( /*todo: lots of builtins to implement */
      "USMatch".!
      ).map(_ => fastparse.parse("skip", atomicTactic(_)).get.value)
    )

  def branchTac[_: P]: P[BelleExpr] = P( "<" ~/ "(" ~ (
    eitherTac.rep(min=2,sep=","./).
      map(BranchTactic) |
    (string.map(BelleLabel.fromString).map(_.head) ~ ":" ~ eitherTac).rep(min=2,sep=","./).
      map(CaseTactic)
    ) ~ ")")("<(tactic,tactic,...)",implicitly)

  def parenTac[_: P]: P[BelleExpr] = P("(" ~/ tactic ~ ")")("(tactic)",implicitly)

  def baseTac[_: P]: P[BelleExpr] = P(branchTac | parenTac | builtinTactic | atomicTactic | at)

  def repTac[_: P]: P[BelleExpr] =
    (baseTac ~ (("*".! ~ (integer.map(Left(_)) | (!CharIn("0-9")).map(Right(_)))) | "+".!.map(s => (s, Right(())))).?).
      map({
        case (tac, Some(("*", Left(iters)))) => RepeatTactic(tac, iters)
        case (tac, Some(("*", Right(())))) => SaturateTactic(tac)
        case (tac, Some(("+", Right(())))) => SeqTactic(tac, SaturateTactic(tac))
        case (tac, None) => tac
      })

  def usingTac[_: P]: P[BelleExpr] =
    (repTac ~~
      (blank ~ "using" ~~ blank ~/ "\"" ~ argList(expression) ~ "\"").?
    ).map({
      case (tac, None) => tac
      case (tac, Some(es)) => Using(es.map(defs.elaborateToFunctions(_)).map(defs.elaborateToSystemConsts), tac)
    })

  def partialTac[_: P]: P[BelleExpr] = (eitherTac ~~ (blank ~ "partial").map(_ => "partial").?).map({
    case (t, None) => t
    case (t, Some(_)) => PartialTactic(t)
  })

  def optionTac[_: P]: P[BelleExpr] = ("?".?.! ~~ usingTac).map({
    case ("?", t) => EitherTactic(t, fastparse.parse("nil", atomicTactic(_)).get.value)
    case (_, t) => t
  })

  def seqTac[_: P]: P[BelleExpr] = P( optionTac.rep(min=1,sep=CharIn(";&")./) )("tactic;tactic",implicitly).
    map(SeqTactic.apply)

  def eitherTac[_: P]: P[BelleExpr] = P( seqTac.rep(min=1,sep="|"./) )("tactic|tactic",implicitly).
    map(EitherTactic.apply)

//  //@note macro-expands
//  def ifthen[_: P]: P[BelleExpr] = P( "if" ~/ parenF ~ braceP ~ ("else" ~/ braceP).? ).
//    map({case (f, p, None) => Choice(Compose(Test(f),p), Test(Not(f)))
//    case (f, p, Some(q)) => Choice(Compose(Test(f),p), Compose(Test(Not(f)),q))})


  /** tactic: Parses a dL Bellerophon tactic. */
  def tactic[_: P]: P[BelleExpr] = P( partialTac )


  def escapedString[_: P]: P[String] = P(string).map(
    _.replaceAllLiterally("\\\"","\"")
  )

  def escapedPositionExpression[_: P]: P[(Expression, PosInExpr)] = P(escapedString)./.
    flatMap(str => {
      //todo: make this not hacky -- starts a new parse every time an escaped expression is encountered
      val hashStart = str.indexOf('#')
      val hashEnd = str.lastIndexOf('#')

      if (hashStart == hashEnd && hashStart != -1)
        Fail
      else if (hashStart == -1) {
        // No hashes, just return Here for PosIn
        fastparse.parse(str, fullExpression(_)) match {
          case Parsed.Success(value, _) =>
            defs.elaborateToSystemConsts(defs.elaborateToFunctions(value)) match {
              case f: Formula => Pass((f, HereP))
              case FuncOf(fn, arg) => Pass((PredOf(fn.copy(sort=Bool), arg), HereP)) //@note for ambiguous locators, e.g. 'R=="p(x)"
            }
          case failure: Parsed.Failure =>
            val tr = failure.trace()
            // What information do we expose here??
            Fail
        }
      } else {
        // Has hashes; extract subexpression and find its position in full expression (hashes act as parentheses)
        val sub = str.substring(hashStart+1,hashEnd)
        val (lp, rp) = fastparse.parse(sub, fullExpression(_)) match {
          case Parsed.Success(_: Program, _) => ("{", "}")
          case Parsed.Success(_: Formula, _) => ("(", ")")
          case Parsed.Success(_: Term, _) => ("(", ")")
          case _: Parsed.Failure => return Fail
        }
        val noHashes = str.substring(0, hashStart) + lp + sub + rp + str.substring(hashEnd+1,str.length)
        fastparse.parse(noHashes, fullExpression(_)) match {
          case failure: Parsed.Failure =>
            val tr = failure.trace()
            // What information do we expose here??
            Fail
          case Parsed.Success(expr, _) =>
            fastparse.parse(sub, fullExpression(_)) match {
              case failure: Parsed.Failure =>
                val tr = failure.trace()
                // What information do we expose here??
                Fail
              case Parsed.Success(sub, _) =>
                val posIn = if (noHashes.indexOf(sub) != hashStart+1) {
                  // marked sub-expression is not leftmost in expr, mark with "hash" placeholder function/predicate/program
                  val (markedStr, placeholder) = PositionLocator.withMarkers(noHashes, sub, hashStart, hashEnd - hashStart + 1)
                  val markedExpr = fastparse.parse(markedStr, fullExpression(_)).get.value
                  FormulaTools.posOf(markedExpr, placeholder)
                } else {
                  FormulaTools.posOf(expr, sub)
                }

                posIn match {
                  case Some(pi) =>
                    Pass((defs.elaborateToSystemConsts(defs.elaborateToFunctions(expr)), pi))
                  case None =>
                    Fail.opaque("Parsed a position locator with subexpression successfully, but could not find subexpression: " + sub.prettyString + " in expression " + expr.prettyString)
                }
            }
        }
      }
    }).opaque("escaped expression string")

  // externals
  //@todo or just import if no dynamic forwarding needed


  /** Explicit nonempty whitespace terminal from [[expParser]]. */
  def blank[_:P]: P[Unit] = expParser.blank

  /** parse a number literal from [[expParser]] */
  def number[_: P]: P[Number] = expParser.number
  /** parse an identifier from [[expParser]] */
  def ident[_: P]: P[(String,Option[Int])] = expParser.ident
  def string[_: P]: P[String] = expParser.string
  def integer[_: P]: P[Int] = expParser.integer
  def natural[_: P]: P[Int] = expParser.natural

  def baseVariable[_: P]: P[BaseVariable] = expParser.baseVariable

  /** expression: Parses a dL expression from [[expParser]]. */
  def expression[_: P]: P[Expression] = expParser.expression

  /** term: Parses a dL term from [[expParser]]. */
  def term[_: P](doAmbigCuts: Boolean): P[Term] = expParser.term(doAmbigCuts)

  /** formula: Parses a dL formula from [[expParser]]. */
  def formula[_: P]: P[Formula] = expParser.formula

  /** program: Parses a dL program from [[expParser]]. */
  def program[_: P]: P[Program] = expParser.program

}
