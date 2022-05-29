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
import edu.cmu.cs.ls.keymaerax.btactics.macros.{ArgInfo, DerivationInfo, FormulaArg, GeneratorArg, ListArg, OptionArg, PosInExprArg, StringArg, SubstitutionArg, TermArg, VariableArg}
import edu.cmu.cs.ls.keymaerax.core._
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
  val belleParser: String => BelleExpr = (s => fastparse.parse(s, tactic(_)) match {
    case Parsed.Success(value, index) => value
    case f: Parsed.Failure => throw parseException(f)
  })

  import JavaWhitespace._

  def position[_: P]: P[Position] = P( integer ~~ ("." ~~/ natural).repX ).map({case (j,js) => Position(j, js.toList)})
  def searchLocator[_: P]: P[PositionLocator] = P(
    "'Llast".!./.map(_ => LastAnte(0))
      | "'Rlast".!./.map(_ => LastSucc(0))
      | (("'L" | "'R").!./ ~ (("==" | "~=").!./ ~ escapedPositionExpression).?).map({
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

  def locator[_: P]: P[PositionLocator] = P( position.map(pos => Fixed(pos)) | searchLocator )

  def argument[_: P](argInfo: ArgInfo): P[Seq[Any]] = P(
    argInfo match {
      case FormulaArg(name, allowsFresh) => formula.map(List(_))
      case TermArg(name, allowsFresh) => term.map(List(_))
      case VariableArg(name, allowsFresh) => DLParser.variable.map(List(_))
      case GeneratorArg(name) => ???
      case StringArg(name, allowsFresh) => DLParser.stringInterior.map(List(_))
      case SubstitutionArg(name, allowsFresh) => ???
      case PosInExprArg(name, allowsFresh) => ???
      case OptionArg(arg) => argument(arg)
      case ListArg(arg) => ((argument(arg) ~ "::"./).rep ~ "nil").map(_.toList)
    }
  )

  def tacticSymbol[_: P]: P[String] = P(ident).map({case (n,None) => n case (n,Some(idx)) =>n + "_" + idx})
  def atomicTactic[_: P]: P[BelleExpr] = ( tacticSymbol ~ !"(").map(t => tacticProvider(t, Nil, defs))
  //@note arguments have the funky type List[Either[Seq[Any], PositionLocator]]
  def at[_: P]: P[BelleExpr] = P(
    (tacticSymbol ~~ "(")./.flatMap(tacName => {
      val argInfos = DerivationInfo.ofCodeName(tacName).persistentInputs
      if (argInfos.isEmpty)
        locator.?.map(loc =>
          (tacName, loc.map(Right(_)).toList)
        )
      else (
        DLParserUtils.mapJoin(argInfos)
          (ai => "\"" ~/ argument(ai) ~ "\"")
          (","./) ~
          (","./ ~ locator).?
      ).map({
        case (args, None) => (tacName, args.map(Left(_)))
        case (args, Some(pos)) => (tacName, args.map(Left(_)) :+ Right(pos))
      })
    }) ~ ")"
  ).map({case (t,args) => tacticProvider(t, args.toList, defs)})

  def builtinTactic[_: P]: P[BelleExpr] = (
    ("doall".! ~~/ "(" ~ tactic ~ ")").
      map({case ("doall", t) => OnAll(t)}) |
    ( /*todo: lots of builtins to implement */
      "USMatch".! |
      "partial".! |
      "let".!
      ).map(_ => belleParser("skip"))
    )

  def branchTac[_: P]: P[BelleExpr] = P( "<" ~/ "(" ~ (
    seqTac.rep(min=1,sep=","./).
      map(BranchTactic) |
    (string.map(BelleLabel.fromString).map(_.head) ~ ":" ~ seqTac).rep(min=1,sep=","./).
      map(CaseTactic)
    ) ~ ")")("<(tactic,tactic,...)",implicitly)

  def parenTac[_: P]: P[BelleExpr] = P(
    ("(" ~/ tactic ~ ")" ~ ("*".! ~ (integer.map(Left(_)) | (!CharIn("0-9")).map(Right(_)))).?).
      map {
        case (tac, Some(("*", Left(iters)))) => RepeatTactic(tac, iters)
        case (tac, Some(("*", Right(())))) => SaturateTactic(tac)
        case (tac, None) => tac
      }
  )("(tactic)*",implicitly)

  def baseTac[_: P]: P[BelleExpr] = P(
    (branchTac | parenTac | builtinTactic | atomicTactic | at) ~~
      (blank ~ "using" ~~ blank ~/ "\"" ~ ((expression ~ "::"./).rep ~ "nil") ~ "\"").?
  ).map({
      case (tac, None) => tac
      case (tac, Some(es)) => Using(es.toList, tac)
    })

  def seqTac[_: P]: P[BelleExpr] = P( baseTac.rep(min=1,sep=CharIn(";&")./) )("tactic;tactic",implicitly).
    map(SeqTactic.apply)

  def eitherTac[_: P]: P[BelleExpr] = P( seqTac.rep(min=1,sep="|"./) )("tactic|tactic",implicitly).
    map(EitherTactic.apply)

//  //@note macro-expands
//  def ifthen[_: P]: P[BelleExpr] = P( "if" ~/ parenF ~ braceP ~ ("else" ~/ braceP).? ).
//    map({case (f, p, None) => Choice(Compose(Test(f),p), Test(Not(f)))
//    case (f, p, Some(q)) => Choice(Compose(Test(f),p), Compose(Test(Not(f)),q))})


  /** tactic: Parses a dL Bellerophon tactic. */
  def tactic[_: P]: P[BelleExpr] = P( eitherTac )


  def escapedString[_: P]: P[String] = P(string).map(_.replaceAllLiterally("\\\"","\""))

  def escapedPositionExpression[_: P]: P[(Expression, PosInExpr)] = P(escapedString)./.
    flatMap(str => {
      //todo: make this not hacky -- starts a new parse every time an escaped expression is encountered
      val hashStart = str.indexOf('#')
      val hashEnd = str.lastIndexOf('#')

      if (hashStart == hashEnd && hashStart != -1)
        Fail.opaque("Mismatched # delimiters")
      else if (hashStart == -1) {
        // No hashes, just return Here for PosIn
        fastparse.parse(str, fullExpression(_)) match {
          case Parsed.Success(value, _) => Pass((value, HereP))
          case failure: Parsed.Failure =>
            val tr = failure.trace()
            // What information do we expose here??
            Fail.opaque("escaped expression string")
        }
      } else {
        // Has hashes; extract subexpression and find its position in full expression
        val sub = str.substring(hashStart+1,hashEnd)
        val noHashes = str.substring(0, hashStart) ++ sub ++ str.substring(hashEnd+1,str.length)
        fastparse.parse(noHashes, fullExpression(_)) match {
          case failure: Parsed.Failure =>
            val tr = failure.trace()
            // What information do we expose here??
            Fail.opaque("escaped expression string")
          case Parsed.Success(expr, _) =>
            fastparse.parse(sub, fullExpression(_)) match {
              case failure: Parsed.Failure =>
                val tr = failure.trace()
                // What information do we expose here??
                Fail.opaque("escaped expression string")
              case Parsed.Success(sub, _) =>
                FormulaTools.posOf(expr, sub) match {
                  case Some(posIn) =>
                    Pass((expr, posIn))
                  case None =>
                    assert(assertion = false, "Parsed a position locator with subexpression successfully, " +
                                  "but could not find subexpression in expression")
                    ???
                }
            }
        }
      }
    })

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
  def term[_: P]: P[Term] = expParser.term

  /** formula: Parses a dL formula from [[expParser]]. */
  def formula[_: P]: P[Formula] = expParser.formula

  /** program: Parses a dL program from [[expParser]]. */
  def program[_: P]: P[Program] = expParser.program

}
