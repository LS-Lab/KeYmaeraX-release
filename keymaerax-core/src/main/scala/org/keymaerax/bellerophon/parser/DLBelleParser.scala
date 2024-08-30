/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Bellerophon tactic parser for Differential Dynamic Logic.
 * @author
 *   Andre Platzer
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 */
package org.keymaerax.bellerophon.parser

import fastparse._
import org.keymaerax.GlobalState
import org.keymaerax.bellerophon._
import org.keymaerax.btactics.macros.{
  ArgInfo,
  DerivationInfo,
  ExpressionArg,
  FormulaArg,
  GeneratorArg,
  ListArg,
  NumberArg,
  OptionArg,
  PosInExprArg,
  StringArg,
  SubstitutionArg,
  TermArg,
  VariableArg,
}
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import org.keymaerax.infrastruct.PosInExpr.HereP
import org.keymaerax.infrastruct.{FormulaTools, PosInExpr, Position}
import org.keymaerax.parser.DLParser.parseException
import org.keymaerax.parser.{Declaration, ParseException, Parser, TacticReservedSymbols}

import scala.annotation.nowarn
import scala.collection.immutable._
import scala.util.Try

/**
 * Bellerophon tactic parser for Differential Dynamic Logic reads input strings in the concrete syntax of Bellerophon
 * tactics for KeYmaera X. It uses `tacticProvider` to map names and inputs to concrete tactic expressions.
 * @author
 *   Andre Platzer
 * @see
 *   [[BelleParser]]
 */
class DLBelleParser(
    override val printer: BelleExpr => String,
    tacticProvider: (String, List[Either[Seq[Any], PositionLocator]], Declaration) => BelleExpr,
) extends DLTacticParser {

  /**
   * Definitions, should be provided by the outer parser through [[setDefs]]. Use [[defs]] instead to get combined outer
   * parser and tactic reserved symbols.
   */
  private var _defs: Declaration = Declaration(Map.empty)

  /** Definitions, provided by outer parser plus tactic reserved symbols. */
  private def defs: Declaration = _defs.addNew(TacticReservedSymbols.asDecl)

  /** Which formula/term/program parser this archive parser uses. */
  private val expParser = GlobalState.parser

  /** Stores defined tactics. */
  private val tactics = scala.collection.mutable.Map.empty[String, DefTactic]

  override val tacticParser: String => BelleExpr = this
  override val expressionParser: Parser = GlobalState.parser

  /** @inheritdoc */
  override def apply(input: String, defs: Declaration): BelleExpr = {
    setDefs(defs)
    setDefTactics(Map.empty)
    belleParser(input)
  }

  /**
   * Sets the definitions to be used when parsing tactic expressions. Expected to be set before [[apply]] or [[tactic]]
   * are used.
   */
  override def setDefs(defs: Declaration): Unit = this._defs = defs

  /** @inheritdoc */
  override def setDefTactics(defs: Map[String, DefTactic]): Unit = {
    tactics.clear()
    defs.foreach(tactics += _)
  }

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  // @todo store the parser for speed
  val belleParser: String => BelleExpr = s =>
    fastparse.parse(s, fullTactic(_)) match {
      case Parsed.Success(value: BelleExpr, _) => value
      case f: Parsed.Failure => throw parseException(f)
    }

  import JavaWhitespace._

  def fullTactic[$: P]: P[BelleExpr] = {
    setDefTactics(Map.empty)
    Start ~ tactic ~ End
  }

  private def fixedLocator[$: P](expr: Expression, p: Position, locator: (Position, Expression) => Fixed): P[Fixed] = {
    expr.sub(p.inExpr) match {
      case Some(e) => Pass(locator(p, e))
      case None =>
        // should never happen because either posIn is top-level or was parsed from expr
        Fail.opaque(
          "Sub-position " + p.inExpr.prettyString + " to point to a formula or term inside " + expr.prettyString
        )
    }
  }

  def posInExpr[$: P]: P[PosInExpr] = P(("." ~~/ natural).repX.map(is => PosInExpr(is.toList)))
  def shape[$: P]: P[(String, (Expression, PosInExpr))] = P(("==" | "~=").!./ ~ escapedPositionExpression)
  def position[$: P]: P[Position] = P(integer ~~ posInExpr).map({ case (j, js) => Position(j) ++ js })
  def positionLocator[$: P]: P[PositionLocator] = P(position ~~ shape.?).flatMap({
    case (p, None) => Pass(Fixed(p))
    case (p, Some(("==", (expr, posIn)))) if p.isTopLevel || posIn.pos.isEmpty =>
      if (p.isTopLevel)
        fixedLocator(expr, p ++ posIn, (p, e) => Fixed(p, Some(e), exact = true)) // check #...# sub-locator
      else
        Pass(
          Fixed(p, Some(expr), exact = true)
        ) // @note expr already points verbatim to the sub-position, e.g. 2.1.1=="x"
    case (p, Some(("==", (expr, posIn)))) if p.inExpr == posIn =>
      fixedLocator(
        expr,
        p,
        (p, e) => Fixed(p, Some(e), exact = true),
      ) // @note check e.g. 2.1=="[x:=1;]#x=1#" consistent
    case (p, Some(("~=", (expr, posIn)))) if p.isTopLevel || posIn.pos.isEmpty =>
      if (p.isTopLevel)
        fixedLocator(expr, p ++ posIn, (p, e) => Fixed(p, Some(e), exact = false)) // check #...# sub-locator
      else
        Pass(
          Fixed(p, Some(expr), exact = false)
        ) // @note expr already points verbatim to the sub-position, e.g. 2.1.1~="x"
    case (p, Some(("~=", (expr, posIn)))) if p.inExpr == posIn =>
      fixedLocator(
        expr,
        p,
        (p, e) => Fixed(p, Some(e), exact = false),
      ) // @note check e.g. 2.1~="[x:=1;]#x=1#" consistent
    case (p, Some((_, (_, posIn)))) => Fail
        .opaque("Non-conflicting sub-positions (but " + p.inExpr.prettyString + " != " + posIn.prettyString + ")")
  })
  @nowarn("msg=match may not be exhaustive")
  def searchLocator[$: P]: P[PositionLocator] = P(
    ("'Llast".! ~~ posInExpr)./.map({ case (_, js) => LastAnte(0, js) }) | ("'Rlast".! ~~ posInExpr)
      ./
      .map({ case (_, js) => LastSucc(0, js) }) | (("'L" | "'R").!./ ~ shape.?).map({
      case ("'L", None) => Find.FindL(0, None, HereP, exact = true, defs)
      case ("'R", None) => Find.FindR(0, None, HereP, exact = true, defs)
      case ("'L", Some(("==", (expr, posIn)))) => Find.FindL(0, Some(expr), posIn, exact = true, defs)
      case ("'R", Some(("==", (expr, posIn)))) => Find.FindR(0, Some(expr), posIn, exact = true, defs)
      case ("'L", Some(("~=", (expr, posIn)))) => Find.FindL(0, Some(expr), posIn, exact = false, defs)
      case ("'R", Some(("~=", (expr, posIn)))) => Find.FindR(0, Some(expr), posIn, exact = false, defs)
    })
  )

  def locator[$: P]: P[PositionLocator] = P(positionLocator | searchLocator)

  def substPair[$: P]: P[SubstitutionPair] = P(
    // If the left side of the substitution is a term, so must the right hand side be,
    // BUT perhaps the left side is ambiguous and the right side is a formula. So in
    // this case both must be false. :(
    (NoCut(formula ~ "~>" ~ formula) | term(false) ~ "~>" ~ term(false) |
      (GlobalState.parser.systemSymbol | GlobalState.parser.programSymbol) ~ "~>" ~ program)
      .map(pair => pair._1.implicitSubst(defs.elaborateToSystemConsts(defs.elaborateToFunctions(pair._2))))
  )

  def argList[$: P, A](p: => P[A]): P[List[A]] = P(
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

  def argumentInterior[$: P](argInfo: ArgInfo): P[Seq[Any]] = P(argInfo match {
    case _: FormulaArg => formula.map(f => List(defs.elaborateFull(f)))
    case _: TermArg => term(true).map(t => List(defs.elaborateFull(t)))
    case _: ExpressionArg => expression.map(e => List(defs.elaborateFull(e)))
    case _: VariableArg => GlobalState.parser.variable.map(List(_))
    case _: GeneratorArg => Fail.opaque("unimplemented: generator argument")
    case _: StringArg => GlobalState.parser.stringInterior.map(List(_))
    case _: SubstitutionArg => (("(" ~/ substPair ~ ")") | substPair).map(List(_))
    case _: PosInExprArg => posInExpr.map(List(_))
    case _: OptionArg => Fail.opaque("Optional argument cannot appear recursively in a different argument type")
    case ListArg(arg) => argList(argumentInterior(arg)).map(_.flatten)
    case _: NumberArg => GlobalState.parser.numberLiteral.map(List(_))
  })

  def argument[$: P](argInfo: ArgInfo): P[Seq[Any]] =
    P("\"" ~/ argumentInterior(argInfo) ~ "\"")(s"Argument ${argInfo.name}: ${argInfo.sort}", implicitly)

  // @note arguments have the funky type List[Either[Seq[Any], PositionLocator]]
  // I believe this is really intended to represent
  //      (List[Seq[Any]], Option[PositionLocator])
  // but squished together, thus why this parser has this type    (- JG)
  def argumentList[$: P](
      isStart: Boolean,
      args: List[ArgInfo],
      numPosArgs: Int,
  ): P[(List[Seq[Any]], List[PositionLocator])] = P(
    // If isStart, then we don't expect preceding ","
    // before each arg, but if not isStart then we do.
    args match {
      case Nil => // No more arguments, try parsing a position locator
        ",".rep(exactly = if (isStart || numPosArgs == 0) 0 else 1) ~/
          locator.rep(exactly = numPosArgs, sep = ",").map(loc => (Nil, loc.toList))
      case (arg: ListArg) :: Nil if isStart => // sole list argument may omit "nil"
        for {
          arg <- argument(arg).?
          // Then the position locator (note if arg is Some(..) then we are no longer at the start)
          pair <- argumentList(isStart && arg.isEmpty, Nil, numPosArgs)
        } yield (List(arg.getOrElse(Seq.empty[Any])) ++ pair._1, pair._2)
      case OptionArg(arg) :: rest => // Optional argument
        for {
          // Try parsing argument, @note no cut after , because subsequent argumentList expects again , if optional argument does not succeed
          arg <- (if (isStart) argument(arg) else "," ~ argument(arg)).?
          // Then the rest of the arguments (note if arg is Some(..) then we are no longer at the start)
          pair <- argumentList(isStart && arg.isEmpty, rest, numPosArgs)
        } yield (arg.toSeq.flatten.map(List(_)).toList ++ pair._1, pair._2)
      case arg :: rest => for {
          // Parse argument (no longer optional)
          arg <- if (isStart) argument(arg) else ","./ ~ argument(arg)
          // We can't be at the start now
          pair <- argumentList(isStart = false, rest, numPosArgs)
        } yield (arg :: pair._1, pair._2)
    }
  )

  def tacticSymbol[$: P]: P[String] = P(ident).map({
    case (n, None) => n
    case (n, Some(idx)) => n + "_" + idx
  })
  def atomicTactic[$: P]: P[BelleExpr] = P((tacticSymbol ~/ !"("./).flatMapX(t =>
    try {
      val di = DerivationInfo.ofCodeName(t)
      (di.persistentInputs, di.numPositionArgs) match {
        case (ListArg(_) :: Nil, 0) => Pass(tacticProvider(t, List(Left(Nil)), defs))
        case (GeneratorArg(_) :: rest, 0) if rest.forall(_.isInstanceOf[OptionArg]) =>
          Pass(tacticProvider(t, Nil, defs))
        case (args, 0) if args.forall(_.isInstanceOf[OptionArg]) =>
          Pass(tacticProvider(t, Nil, defs)) // @note includes args==Nil
        case (args, posArgs) => Fail.opaque(
            "Expected " + args.length + " arguments " + args.map(a => a.name + ":" + a.sort).mkString("(", ",", ")") +
              (if (posArgs > 0) " and " + posArgs + " positions" else "")
          )
      }
    } catch {
      case _: ParseException | _: IllegalArgumentException =>
        if (tactics.contains(t)) Pass(ApplyDefTactic(tactics(t)))
        else Fail.opaque("Expected known tactic, but " + t + " not a known tactic")
    }
  ))

  def at[$: P]: P[BelleExpr] = P((tacticSymbol ~~ "("./).flatMap(tacName => {
    val di = DerivationInfo.ofCodeName(tacName)
    val argInfos = di.persistentInputs
    val numPosArgs = di.numPositionArgs
    argumentList(isStart = true, argInfos, numPosArgs).map({ case (args, pos) =>
      (tacName, args.map(Left(_)) ++ pos.map(Right(_)))
    })
  }) ~ ")")("tactic(...)", implicitly).map({ case (t, args) => tacticProvider(t, args, defs) })

  def builtinTactic[$: P]: P[BelleExpr] = ("doall" ~ "(" ~/ tactic ~ ")")
    .map(OnAll) | ("partial" ~ "(" ~/ tactic ~ ")").map(PartialTactic(_, None)) |
    ("let" ~ "(" ~ "\"" ~/ GlobalState.parser.comparison ~ "\"" ~ ")" ~ "in" ~ "(" ~/ tactic ~ ")").flatMap({
      case (Equal(l, r), t) => Pass(Let(l, r, t))
      case (c, _) => Fail("Abbreviation of the shape f()=e (but got " + c.prettyString + ")")
    }) | ("tactic" ~ tacticSymbol ~ "as" ~/ baseTac).flatMapX({ case (s, t) =>
      if (tactics.contains(s)) Fail("Unique name " + s)
      else if (Try(tacticProvider(s, Nil, defs)).toOption.isDefined)
        Fail("Tactic name " + s + " is builtin, please use a different name")
      else {
        tactics += (s -> DefTactic(s, t))
        Pass(tactics(s))
      }
    }) | "USMatch".!.map(_ => fastparse.parse("skip", atomicTactic(_)).get.value)

  def branchTac[$: P]: P[BelleExpr] = P(
    "<" ~/ "(" ~
      (eitherTac.rep(min = 2, sep = ","./).map(BranchTactic) |
        (string.map(BelleLabel.fromString).map(_.head) ~ ":" ~ eitherTac).rep(min = 2, sep = ","./).map(CaseTactic)) ~
      ")"
  )("<(tactic,tactic,...)", implicitly)

  def parenTac[$: P]: P[BelleExpr] = P("(" ~/ tactic ~ ")")("(tactic)", implicitly)

  def baseTac[$: P]: P[BelleExpr] = P(branchTac | parenTac | builtinTactic | at | atomicTactic)

  @nowarn("msg=match may not be exhaustive")
  def repTac[$: P]: P[BelleExpr] =
    (baseTac ~ (("*".! ~ (integer.map(Left(_)) | (!CharIn("0-9")).map(Right(_)))) | "+".!.map(s => (s, Right(())))).?)
      .map({
        case (tac, Some(("*", Left(iters)))) => RepeatTactic(tac, iters)
        case (tac, Some(("*", Right(())))) => SaturateTactic(tac)
        case (tac, Some(("+", Right(())))) => SeqTactic(tac, SaturateTactic(tac))
        case (tac, None) => tac
      })

  def usingTac[$: P]: P[BelleExpr] = (repTac ~~ (blank ~ "using" ~~ blank ~/ "\"" ~ argList(expression) ~ "\"").?).map({
    case (tac, None) => tac
    case (tac, Some(es)) => Using(es.map(defs.elaborateFull(_)), tac)
  })

  def partialTac[$: P]: P[BelleExpr] = (eitherTac ~~ (blank ~ "partial").map(_ => "partial").?).map({
    case (t, None) => t
    case (t, Some(_)) => PartialTactic(t)
  })

  def optionTac[$: P]: P[BelleExpr] = ("?".?.! ~~ usingTac).map({
    case ("?", t) => EitherTactic(t, fastparse.parse("nil", atomicTactic(_)).get.value)
    case (_, t) => t
  })

  def seqTac[$: P]: P[BelleExpr] = P(optionTac.rep(min = 1, sep = CharIn(";&")./))("tactic;tactic", implicitly)
    .map(SeqTactic.apply)

  def eitherTac[$: P]: P[BelleExpr] = P(seqTac.rep(min = 1, sep = "|"./))("tactic|tactic", implicitly)
    .map(EitherTactic.apply)

//  //@note macro-expands
//  def ifthen[$: P]: P[BelleExpr] = P( "if" ~/ parenF ~ braceP ~ ("else" ~/ braceP).? ).
//    map({case (f, p, None) => Choice(Compose(Test(f),p), Test(Not(f)))
//    case (f, p, Some(q)) => Choice(Compose(Test(f),p), Compose(Test(Not(f)),q))})

  /** tactic: Parses a dL Bellerophon tactic. */
  def tactic[$: P]: P[BelleExpr] = P(partialTac)

  def escapedString[$: P]: P[String] = P(string).map(_.replace("\\\"", "\""))

  @nowarn("msg=match may not be exhaustive")
  def escapedPositionExpression[$: P]: P[(Expression, PosInExpr)] = P(escapedString)
    ./
    .flatMap(str => {
      // todo: make this not hacky -- starts a new parse every time an escaped expression is encountered
      val hashStart = str.indexOf('#')
      val hashEnd = str.lastIndexOf('#')

      if (hashStart == -1) {
        // str contains no hashes, just return Here for PosIn.
        // str can be any expression, including a term (or a program), e.g. "x" in `2.1==x`.
        // Potentially unsafe for ambiguous "p()" with an archive without definition
        return fastparse.parse(str, GlobalState.parser.fullExpression(_)) match {
          case Parsed.Success(value, _) => Pass((defs.elaborateFull(value), HereP))
          case _: Parsed.Failure => Fail
        }
      }

      if (hashStart == hashEnd) {
        // str contains a single hash which is invalid syntax.
        return Fail
      }

      // str contains hashes.
      // Extract subexpression and find its position in full expression (hashes act as parentheses)
      // Outer expression must be a formula
      val beforeHashes = str.substring(0, hashStart)
      val betweenHashes = str.substring(hashStart + 1, hashEnd)
      val afterHashes = str.substring(hashEnd + 1)

      // subExpr need to have the correct sort without ambiguity between predicate and function
      // elaborateFull would also work (if used consistently) but more costly
      val subExpr = fastparse.parse(betweenHashes, GlobalState.parser.fullExpression(_)) match {
        case Parsed.Success(e, _) => defs.elaborateToFunctions[Expression](e)
        case _: Parsed.Failure => return Fail
      }

      // Replace hashes with parentheses
      val (lp, rp) = subExpr match {
        case _: Program => ("{", "}")
        case _: Formula | _: Term => ("(", ")")
      }
      val strWithoutHashes = beforeHashes + lp + betweenHashes + rp + afterHashes

      val reparsedSubExpr = fastparse.parse(strWithoutHashes, GlobalState.parser.fullFormula(_)) match {
        case Parsed.Success(expr, _) => expr
        case _: Parsed.Failure => return Fail
      }

      val posIn =
        if (strWithoutHashes.indexOf(betweenHashes) != hashStart + 1) {
          // marked sub-expression is not leftmost instance in expr
          // mark with "hash" placeholder function/predicate/program depending on subExpr sort
          val (markedStr, placeholder) = PositionLocator
            .withMarkers(strWithoutHashes, subExpr, hashStart, hashEnd - hashStart + 1)
          val markedExpr = fastparse.parse(markedStr, GlobalState.parser.fullFormula(_)).get.value
          FormulaTools.posOf(markedExpr, placeholder)
        } else {
          // reparsedSubExpr need to be elaborated consistently with subExpr
          FormulaTools.posOf(defs.elaborateToFunctions(reparsedSubExpr), subExpr)
        }

      posIn match {
        case Some(pi) => Pass((defs.elaborateFull(reparsedSubExpr), pi))
        case None => Fail.opaque(
            "Parsed a position locator with subexpression successfully, but could not find subexpression: " +
              subExpr.prettyString + " in expression " + reparsedSubExpr.prettyString
          )
      }
    })
    .opaque("escaped expression string")

  // externals
  // @todo or just import if no dynamic forwarding needed

  /** Explicit nonempty whitespace terminal from [[expParser]]. */
  def blank[$: P]: P[Unit] = expParser.blank

  /** parse a number literal from [[expParser]] */
  def number[$: P]: P[Number] = expParser.numberLiteral

  /** parse an identifier from [[expParser]] */
  def ident[$: P]: P[(String, Option[Int])] = expParser.ident
  def string[$: P]: P[String] = expParser.string
  def integer[$: P]: P[Int] = expParser.integer
  def natural[$: P]: P[Int] = expParser.natural

  def baseVariable[$: P]: P[BaseVariable] = expParser.baseVariable

  /** expression: Parses a dL expression from [[expParser]]. */
  def expression[$: P]: P[Expression] = expParser.expression

  /** term: Parses a dL term from [[expParser]]. */
  def term[$: P](doAmbigCuts: Boolean): P[Term] = expParser.term(doAmbigCuts)

  /** formula: Parses a dL formula from [[expParser]]. */
  def formula[$: P]: P[Formula] = expParser.formula

  /** program: Parses a dL program from [[expParser]]. */
  def program[$: P]: P[Program] = expParser.program

}
