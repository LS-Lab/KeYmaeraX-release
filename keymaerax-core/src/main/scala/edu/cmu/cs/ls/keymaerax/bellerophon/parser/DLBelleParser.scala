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
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics
import edu.cmu.cs.ls.keymaerax.btactics.macros.{ArgInfo, DerivationInfo, ExpressionArg, FormulaArg, GeneratorArg, ListArg, NumberArg, OptionArg, PosInExprArg, StringArg, SubstitutionArg, TermArg, VariableArg}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import edu.cmu.cs.ls.keymaerax.parser.{DLParser, DLParserUtils, Declaration, ParseException, Parser}
import fastparse._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.parser.DLParser.{fullExpression, parseException}

import scala.collection.immutable._

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

  override val tacticParser: String => BelleExpr = this
  override val expressionParser: Parser = DLParser

  /** @inheritdoc */
  override def apply(input: String, defs: Declaration): BelleExpr = {
    setDefs(defs)
    belleParser(input)
  }

  /** Sets the definitions to be used when parsing tactic expressions. Expected to be set
    * before [[apply]] or [[tactic]] are used. */
  override def setDefs(defs: Declaration): Unit = this.defs = defs

  /** Parse the input string in the concrete syntax as a differential dynamic logic expression */
  //@todo store the parser for speed
  val belleParser: String => BelleExpr = (s => fastparse.parse(s, fullTactic(_)) match {
    case Parsed.Success(value, index) => value
    case f: Parsed.Failure => throw parseException(f)
  })

  import JavaWhitespace._

  def fullTactic[_: P]: P[BelleExpr] = (Start ~ tactic ~ End)

  private def fixedLocator[_: P](expr: Expression, p: Position, locator: (Position, Expression) => Fixed): P[Fixed] = {
    expr.sub(p.inExpr) match {
      case Some(e) => Pass(locator(p, e))
      case None =>
        // should never happen because either posIn is top-level or was parsed from expr
        Fail.opaque("Sub-position " + p.inExpr.prettyString + " to point to a formula or term inside " + expr.prettyString)
    }
  }

  def shape[_: P]: P[(String, (Expression, PosInExpr))] = P( ("==" | "~=").!./ ~ escapedPositionExpression )
  def position[_: P]: P[Position] = P( integer ~~ ("." ~~/ natural).repX).map({ case (j,js) => Position(j, js.toList) })
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
    ("'Llast".! ~~ ("." ~~/ natural).repX)./.map({ case (_, js) => LastAnte(0, PosInExpr(js.toList)) })
      | ("'Rlast".! ~~ ("." ~~/ natural).repX)./.map({ case (_, js) => LastSucc(0, PosInExpr(js.toList)) })
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
    (formula ~ "~>" ~ formula |
      term(false) ~ "~>" ~ term(false)).
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
      case FormulaArg(name, allowsFresh) => formula.map(List(_))
      case TermArg(name, allowsFresh) => term(true).map(List(_))
      case ExpressionArg(name, allowsFresh) =>
        // I feel like we should never actually hit this because of the cases before it, but ???
        expression.map(List(_))
      case VariableArg(name, allowsFresh) => DLParser.variable.map(List(_))
      case GeneratorArg(name) => Fail.opaque("unimplemented: generator argument")
      case StringArg(name, allowsFresh) => DLParser.stringInterior.map(List(_))
      case SubstitutionArg(name, allowsFresh) => substPair.map(List(_))
      case PosInExprArg(name, allowsFresh) => Fail.opaque("unimplemented: PosInExpr argument")
      case OptionArg(arg) => Fail.opaque("Optional argument cannot appear recursively in a different argument type")
      case ListArg(arg) => argList(argumentInterior(arg)).map(_.flatten)
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
  def argumentList[_: P](isStart: Boolean, args: List[ArgInfo]): P[(List[Seq[Any]],Option[PositionLocator])] = P(
    // If isStart, then we don't expect preceding ","
    // before each arg, but if not isStart then we do.
    args match {
      case Nil => // No more arguments, try parsing a position locator
        (if (isStart) locator else ","./ ~ locator).?.
          map(loc => (Nil, loc))
      case OptionArg(arg) :: rest => // Optional argument
        for {
          // Try parsing argument, @note no cut after , because subsequent argumentList expects again , if optional argument does not succeed
          arg <- (if (isStart) argument(arg) else "," ~ argument(arg)).?
          // Then the rest of the arguments (note if arg is Some(..) then we are no longer at the start)
          pair <- argumentList(isStart && arg.isEmpty, rest)
        } yield (arg.toSeq.flatten.map(List(_)).toList ++ pair._1, pair._2)
      case arg :: rest =>
        for {
          // Parse argument (no longer optional)
          arg <- if (isStart) argument(arg) else ","./ ~ argument(arg)
          // We can't be at the start now
          pair <- argumentList(isStart = false, rest)
        } yield (arg :: pair._1, pair._2)
    }
  )

  def tacticSymbol[_: P]: P[String] = P(ident).map({case (n,None) => n case (n,Some(idx)) =>n + "_" + idx})
  def atomicTactic[_: P]: P[BelleExpr] = ( tacticSymbol ~ !"("./).map(t => tacticProvider(t, Nil, defs))

  def at[_: P]: P[BelleExpr] = P(
    (tacticSymbol ~~ "("./).flatMap(tacName => {
      val argInfos = DerivationInfo.ofCodeName(tacName).persistentInputs
      argumentList(isStart = true, argInfos).map({
        case (args, None) => (tacName, args.map(Left(_)))
        case (args, Some(pos)) => (tacName, args.map(Left(_)) :+ (Right(pos)))
      })
    }) ~ ")"
  )("tactic(...)",implicitly).
    map({case (t,args) => tacticProvider(t, args, defs)})

  def builtinTactic[_: P]: P[BelleExpr] = (
    ("doall".! ~ "(" ~/ tactic ~ ")").
      map({case ("doall", t) => OnAll(t)}) |
    ("partial".! ~ "(" ~/ tactic ~ ")").
      map({case ("partial",t) => PartialTactic(t)}) |
    ("pending".! ~ "(" ~/ escapedString ~ ")").
      map({case ("pending",t) =>
        DebuggingTactics.pending(t)
      }) |
    ( /*todo: lots of builtins to implement */
      "USMatch".! |
      "let".!
      ).map(_ => belleParser("skip"))
    )

  def branchTac[_: P]: P[BelleExpr] = P( "<" ~/ "(" ~ (
    seqTac.rep(min=1,sep=","./).
      map(BranchTactic) |
    (string.map(BelleLabel.fromString).map(_.head) ~ ":" ~ seqTac).rep(min=1,sep=","./).
      map(CaseTactic)
    ) ~ ")")("<(tactic,tactic,...)",implicitly)

  def parenTac[_: P]: P[BelleExpr] = P("(" ~/ tactic ~ ")")("(tactic)",implicitly)

  def baseTac[_: P]: P[BelleExpr] = P(branchTac | parenTac | builtinTactic | atomicTactic | at)

  def repTac[_: P]: P[BelleExpr] =
    (baseTac ~ ("*".! ~ (integer.map(Left(_)) | (!CharIn("0-9")).map(Right(_)))).?).
      map({
        case (tac, Some(("*", Left(iters)))) => RepeatTactic(tac, iters)
        case (tac, Some(("*", Right(())))) => SaturateTactic(tac)
        case (tac, None) => tac
      })

  def usingTac[_: P]: P[BelleExpr] =
    (repTac ~~
      (blank ~ "using" ~~ blank ~/ "\"" ~ argList(expression) ~ "\"").?
    ).map({
      case (tac, None) => tac
      case (tac, Some(es)) => Using(es, tac)
    })

  def partialTac[_: P]: P[BelleExpr] = (usingTac ~~ (blank ~ "partial").map(_ => "partial").?).map({
    case (t, None) => t
    case (t, Some(_)) => PartialTactic(t)
  })

  def seqTac[_: P]: P[BelleExpr] = P( partialTac.rep(min=1,sep=CharIn(";&")./) )("tactic;tactic",implicitly).
    map(SeqTactic.apply)

  def eitherTac[_: P]: P[BelleExpr] = P( seqTac.rep(min=1,sep="|"./) )("tactic|tactic",implicitly).
    map(EitherTactic.apply)

//  //@note macro-expands
//  def ifthen[_: P]: P[BelleExpr] = P( "if" ~/ parenF ~ braceP ~ ("else" ~/ braceP).? ).
//    map({case (f, p, None) => Choice(Compose(Test(f),p), Test(Not(f)))
//    case (f, p, Some(q)) => Choice(Compose(Test(f),p), Compose(Test(Not(f)),q))})


  /** tactic: Parses a dL Bellerophon tactic. */
  def tactic[_: P]: P[BelleExpr] = P( eitherTac )


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
          case Parsed.Success(value, _) => Pass((value, HereP))
          case failure: Parsed.Failure =>
            val tr = failure.trace()
            // What information do we expose here??
            Fail
        }
      } else {
        // Has hashes; extract subexpression and find its position in full expression (hashes act as parentheses)
        val sub = str.substring(hashStart+1,hashEnd)
        val noHashes = str.substring(0, hashStart) + "(" + sub + ")" + str.substring(hashEnd+1,str.length)
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
                FormulaTools.posOf(expr, sub) match {
                  case Some(posIn) =>
                    Pass((expr, posIn))
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
