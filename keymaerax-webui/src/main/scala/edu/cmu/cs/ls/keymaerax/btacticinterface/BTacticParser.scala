package edu.cmu.cs.ls.keymaerax.btacticinterface

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.{SuccPos, AntePos, SeqPos, Formula}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.util.parsing.combinator.{PackratParsers, RegexParsers}

/**
  * A parser for the Bellerophon tactics language.
  * Parses tactics of the form: {{{
  *   e < (e, ..., e)
  *   e & e
  *   e | e
  *   e*@(T)
  *   e*@(T)n
  *   partial(e)
  *   e partial
  *   b
  *   b({`formula`} | z, ...)
  * }}}
  * where formula is a \dL formula, n a nat, z an int, T a type, and b a base tactic identifier.
  * Identifiers may contain letters, numbers, and dots. Each identifier should be handled by [[ReflectiveExpressionBuilder]]
  *
  * @author Nathan Fulton
  */
object BTacticParser {
  def apply(s: String, loggingOn:Boolean=false): Option[BelleExpr] = {
    val parser = new TheParser(loggingOn)
    parser.parseAll(parser.expressionParser, s) match {
      case parser.Success(result, next) => Some(result.asInstanceOf[BelleExpr])
      case f: parser.Failure => None
      case e: parser.Error => None
    }
  }

  private class TheParser(enabledLogging: Boolean = false) extends RegexParsers with PackratParsers {
    lazy val expressionParser = expressionParsers.reduce(_ | _)
    lazy val typeParser       = typeParsers.reduce(_ | _)

    /** A precedence list of bell expression language parsers. */
    lazy val expressionParsers: List[PackratParser[BelleExpr]] =
      branchP ::
      seqP    ::
      eitherP ::
      repeatP ::
      repeatPDefaultType ::
      ntimesP ::
      partialP ::
      postPartialP ::
//      usubstCaseAnalysisP ::
      baseTacticWithInputs ::
      baseTacticNoInput ::
      Nil

    lazy val typeParsers : List[PackratParser[BelleType]] =
      theTypeP ::
      Nil

    def log[T](p: Parser[T])(name: String) = if (!enabledLogging) p else super.log(p)(name)

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Regular expressions that match language terminals
    ////////////////////////////////////////////////////////////////////////////////////////////////

    protected override val whiteSpace =
      """(\s|(?m)\(\*(\*(?!/)|[^*])*\*\)|/\*(.)*?\*/|\/\*[\w\W\s\S\d\D]+?\*\/)+""".r
    protected val space = """[\ \t\n]*""".r
    protected val ident = """[a-zA-Z][a-zA-Z0-9\_\.]*""".r
    protected val numberPattern = """[0-9]*""".r

    val positionPattern = """[\-?0-9]*""".r
    val notArgumentDelimiter = """[^`}]""".r
//    val notDoubleQoute = """[^\"]*""".r

    // SYMBOLTABLE contains reserved symbols.
    import SYMBOLTABLE._

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Parsers for each belle expr language construct.
    ////////////////////////////////////////////////////////////////////////////////////////////////

    lazy val seqP : PackratParser[BelleExpr] = {
      lazy val pattern = expressionParser ~ SEQ ~ expressionParser
      log(pattern)(SEQ) ^^ {
        case left ~ SEQ ~ right => SeqTactic(left, right)
      }
    }

    lazy val eitherP : PackratParser[BelleExpr] = {
      lazy val pattern = expressionParser ~ EITHER ~ expressionParser
      log(pattern)(EITHER) ^^ {
        case left ~ EITHER ~ right => EitherTactic(left, right)
      }
    }

    lazy val branchP : PackratParser[BelleExpr] = {
      /** Parses a comma-separated list of tactics containing at least one tactic. */
      lazy val commaSeparatedList = (expressionParser <~ ",").*.? ~ expressionParser

      lazy val pattern = expressionParser ~ BRANCH ~ ("(" ~> commaSeparatedList <~ ")")
      log(pattern)(BRANCH) ^^ {
        case left ~ BRANCH ~ right => {
          val lastRight : BelleExpr = right._2
          val otherRights : List[BelleExpr] = right._1 match {
            case Some(rights) => rights
            case None => List[BelleExpr]()
          }
          val rights = otherRights :+ lastRight
          SeqTactic(left, BranchTactic(rights))
        }
      }
    }

    lazy val repeatP : PackratParser[BelleExpr] = {
      lazy val pattern = expressionParser ~ ANNOTATED_STAR ~ ("(" ~> typeParser <~ ")")
      log(pattern)(ANNOTATED_STAR) ^^ {
        case expr ~ ANNOTATED_STAR ~ ty => SaturateTactic(expr, ty)
      }
    }

    lazy val repeatPDefaultType: PackratParser[BelleExpr] = {
      lazy val pattern = expressionParser <~ STAR
      log(pattern)(STAR + " with default type") ^^ {
        case expr => SaturateTactic(expr, TheType())
      }
    }

    lazy val ntimesP : PackratParser[BelleExpr] = {
      lazy val pattern = expressionParser ~ ANNOTATED_STAR ~ ("(" ~> typeParser <~ ")") ~ numberPattern
      log(pattern)(ANNOTATED_STAR) ^^ {
        case expr ~ ANNOTATED_STAR ~ ty ~ number => RepeatTactic(expr, number.toInt, ty)
      }
    }

    lazy val partialP : PackratParser[BelleExpr] = {
      lazy val pattern = PARTIAL ~ ("(" ~> expressionParser <~ ")")
      log(pattern)(PARTIAL) ^^ {
        case PARTIAL ~ expr => PartialTactic(expr)
      }
    }

    lazy val postPartialP : PackratParser[BelleExpr] = {
      lazy val pattern = expressionParser ~ PARTIAL
      log(pattern)(PARTIAL + " postfix") ^^ {
        case expr ~ PARTIAL => PartialTactic(expr)
      }
    }

    /** Parses a name to a BelleExpr.
      * Each name should be either reserved (i.e., a key in [[edu.cmu.cs.ls.keymaerax.btactics.ExposedTacticsLibrary.tactics]])
      * or else of the form package.method
      */
    lazy val baseTacticNoInput : PackratParser[BelleExpr] = {
      lazy val pattern = ident
      log(pattern)("Built-in Name") ^^ {
        case name => ReflectiveExpressionBuilder(name)
      }
    }

    /** Looks like name(formula | position, formula | position, ..., formula | position) where formula = {` formula `} */
//    lazy val baseTacticWithInputs : PackratParser[BelleExpr] = {
//      lazy val formulaOrPosition = ("{`" ~> notArgumentDelimiter <~ "`}") | positionPattern
//      lazy val pattern = ident ~ ("(" ~> formulaOrPosition ~ formulaOrPosition.*.? <~ ")")
//
//      log(pattern)("base tactic with inputs") ^^ {
//        case name ~ arguments => {
//          val allArguments : List[String] = arguments._2 match {
//            case Some(args) => arguments._1 +: args
//            case None => arguments._1 :: Nil
//          }
//          ReflectiveExpressionBuilder(name, allArguments.map(parseFormulaOrPosition))
//        }
//      }
//    }

    lazy val baseTacticWithInputs : PackratParser[BelleExpr] = {
      lazy val pattern = ident ~ ("(" ~> positionPattern <~ ")")
      log(pattern)("base tactic with position input") ^^ {
        case name ~ argument => {
          ReflectiveExpressionBuilder(name, (argument::Nil).map(parseFormulaOrPosition))
        }
      }
    }

    private def parseFormulaOrPosition(s : String) : Either[Formula, SeqPos] = {
      if (s.startsWith("{`") && s.endsWith("`}")) {
        Left(s.replace("{`", "").replace("`}", "").asFormula)
      }
      else {
        val i = s.toInt
        if(i < 0) Right(AntePos(i * -1 + 1))
        else if(i > 0) Right(SuccPos(i - 1))
        else ??? //Not sure what pos 0 is?
      }
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////
    // Parsers for each type constructor.
    ////////////////////////////////////////////////////////////////////////////////////////////////


    lazy val theTypeP : PackratParser[BelleType] = {
      lazy val pattern = ident
      log(pattern)("TheType") ^^ {
        case _ => TheType()
      }
    }
  }

  private object SYMBOLTABLE {
    val SEQ = "&"
    val BRANCH = "<"
    val ANNOTATED_STAR = "*@"
    val STAR = "*"
    val EITHER = "|"
    val PARTIAL = "partial"
    val MATCH = "match"
  }
}
