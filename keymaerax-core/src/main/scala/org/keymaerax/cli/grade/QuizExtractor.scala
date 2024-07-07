/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli.grade

import org.keymaerax.bellerophon.parser.BelleParser
import org.keymaerax.cli.grade.AssessmentProver.{
  AnyOfArtifact,
  ArchiveArtifact,
  Artifact,
  ExpressionArtifact,
  ListExpressionArtifact,
  SequentArtifact,
  SubstitutionArtifact,
  TacticArtifact,
  TexExpressionArtifact,
  TextArtifact,
}
import org.keymaerax.core.{And, Equal, False, Less, LessEqual, Neg, Number, Or, True, Variable}
import org.keymaerax.parser.StringConverter._
import org.keymaerax.parser.UnificationSubstitutionParser

import scala.util.Try
import scala.util.matching.Regex

/** Extracts assessment information from tex sources. */
object QuizExtractor {
  abstract class Question

  /** One question in a problem with grading information. */
  case class AskQuestion(
      grader: Option[String],
      args: Map[String, String],
      expected: Artifact,
      testSols: List[Artifact],
      noSols: List[Artifact],
  ) extends Question
  object AskQuestion {
    val QUESTION_START: String = "ask"
    val KYXLINE = """\kyxline"""
    val MATH_DELIM = "$"
    val LISTING_DELIM = "\\begin{lstlisting}"
    val INLINE_SOL_DELIM = "____"
    val INLINE_SOL_DELIM_UNI_BEGIN = "\u00ab"
    val INLINE_SOL_DELIM_UNI_END = "\u00bb"
    val ARG_PLACEHOLDER = "\\%"

    private val QUESTION_INFO1 = "qi1"
    private val QUESTION_INFO2 = "qi2"
    private val GRADER = "grader"
    private val ARGS = "args"
    private val SOL_PREFIX = "sol"
    private val KYX_SOL_POSTFIX = "kyx"
    private val TEX_SOL_POSTFIX = "tex"
    private val TXT_SOL_POSTFIX = "txt"
    private val LISTINGS_SOL_POSTFIX = "lst"
    private val KYX_SOL = SOL_PREFIX + KYX_SOL_POSTFIX
    private val TEX_SOL = SOL_PREFIX + TEX_SOL_POSTFIX
    private val TXT_SOL = SOL_PREFIX + TXT_SOL_POSTFIX
    private val LISTINGS_SOL = SOL_PREFIX + LISTINGS_SOL_POSTFIX
    private val SOLFIN = "solfin"
    private val TEST_SOL = "testsol"
    private val NO_SOL = "nosol"
    private val ARG_NAME = "argName"
    private val ARG_VAL = "argVal"
    private val ANSWER = "answer"
    private val TURNSTILE = "==>"
    private val GOAL_SEP = ";;"
    private val TEX_NO_BREAK_SPACE = "~"
    private val TEX_WS = "(?:\\s|~(?!>))"
    private val ANY_TEX_WS = TEX_WS + "*"

    // \solfin
    private def solfinBodyExtractor(capture: String) = """(?s)\\begin\{lstlisting}\s*(""" + capture +
      """.*?)\s*\\end\{lstlisting}"""
    private val SOLFIN_BODY_EXTRACTOR = solfinBodyExtractor(s"?<$SOLFIN>")
    private val SOLFIN_EXTRACTOR = """(?:\\solfin\s*\{?\s*""" + SOLFIN_BODY_EXTRACTOR + """\s*}?)"""
    private val SOLFIN_ANSWER_EXTRACTOR: Regex =
      ("(?s)" + "(?:" + INLINE_SOL_DELIM + "|" + INLINE_SOL_DELIM_UNI_BEGIN + ")" + "\\s*" + TEX_NO_BREAK_SPACE + "*" +
        "(.*?)" + TEX_NO_BREAK_SPACE + "*" + "\\s*" + "(?:" + INLINE_SOL_DELIM + "|" + INLINE_SOL_DELIM_UNI_END + ")")
        .r(ANSWER)
    // \sol
    private def kyxlineExtractor(capture: String) = """\""" + KYXLINE + """\s*"(""" + capture + """[^"]+)""""
    // @note nested {} up to level 2
    private def captureOf(s: String, post: String): String = {
      if (s.nonEmpty && s.startsWith("?:")) s else if (s.nonEmpty) s + post + ">" else s
    }
    private def nestedBracesText(capture: String) = "(" + capture + """(?:[^}{]+|\{(?:[^}{]+|\{[^}{]*})*})*)"""
    private def texMathDelimText(capture: String) = """\""" + MATH_DELIM + "(" + capture + """.+?)\""" + MATH_DELIM
    private def solContent(capture: String) = "(?:" + kyxlineExtractor(captureOf(capture, KYX_SOL_POSTFIX)) + "|" +
      texMathDelimText(captureOf(capture, TEX_SOL_POSTFIX)) + "|" +
      solfinBodyExtractor(captureOf(capture, LISTINGS_SOL_POSTFIX)) + "|" +
      nestedBracesText(captureOf(capture, TXT_SOL_POSTFIX)) + ")"
    private val SOL_EXTRACTOR = """(?:\\sol(?!fin)\s*(?:\{\s*""" + solContent(s"?<$SOL_PREFIX") + """\s*})?)"""
    // \testsol
    private val TEST_SOL_EXTRACTOR = s"(?<$TEST_SOL>" + """(?:\\testsol\s*\{\s*""" + solContent("?:") + """}\s*))"""
    // \nosol
    private val NO_SOL_EXTRACTOR = s"(?<$NO_SOL>" + """(?:\\nosol\s*\{\s*""" + solContent("?:") + """}\s*))"""
    // \autog
    private val GRADER_NAME = s"(?<$GRADER>" + """\w+)"""
    private def doubleQuotesString(capture: String) = """"(""" + capture +
      """(?:[^"\\]|\\.)*)"""" // @note double-quotes with nested escaped quotes
    private def graderArg(capture: String) = "(" + capture + """\w+)\s*=\s*""" + doubleQuotesString(capture)
    private val GRADER_ARG = graderArg("").r(ARG_NAME, ARG_VAL)
    private val GRADER_ARGS = graderArg("?:") + """(?:\s*,\s*""" + graderArg("?:") + """)*"""
    private val GRADER_METHOD = GRADER_NAME + """\((?<""" + ARGS + ">" + GRADER_ARGS + """)?\)"""
    private val GRADER_EXTRACTOR = """(?:\\algog\s*\{""" + GRADER_METHOD + """})"""

    private val EXPR_LIST_SPLITTER =
      """\{[^{}]*}|(,)"""
        .r // @note matches unwanted {...,...} left and , outside {} right so needs filtering of results (not just split)

    private val ASK_EXTRACTOR = """\\""" + QUESTION_START + """(?:.*?)"""
    private val ALL_SOL_EXTRACTOR = """(?:""" + SOL_EXTRACTOR + "|" + SOLFIN_EXTRACTOR + ")"
    private val QUESTION_EXTRACTOR: Regex = ("(?s)" + ASK_EXTRACTOR + "(?:(.*?)(?=\\\\" + QUESTION_START + ")|(.*))")
      .r(QUESTION_INFO1, QUESTION_INFO2)

    def firstFromString(rawContent: String): Option[AskQuestion] = {
      val firstMatch = QUESTION_EXTRACTOR.findFirstMatchIn(rawContent)
      val qi = firstMatch.map(m =>
        Option(m.group(QUESTION_INFO1)) match {
          case Some(qi) => qi
          case _ => m.group(QUESTION_INFO2)
        }
      )
      val graderInfo = qi.map(s =>
        (
          ALL_SOL_EXTRACTOR
            .r
            .findAllMatchIn(s)
            .map(m =>
              (
                Option(m.group(KYX_SOL)),
                Option(m.group(TEX_SOL)),
                Option(m.group(LISTINGS_SOL)),
                Option(m.group(TXT_SOL)),
                Option(m.group(SOLFIN)),
              )
            )
            .toList,
          TEST_SOL_EXTRACTOR.r.findAllMatchIn(s).map(_.group(TEST_SOL)).toList,
          NO_SOL_EXTRACTOR.r.findAllMatchIn(s).map(_.group(NO_SOL)).toList,
          GRADER_EXTRACTOR.r.findAllMatchIn(s).map(m => (m.group(GRADER), Option(m.group(ARGS)))).toList,
        )
      )
      graderInfo.map({ case (sol, testsols, nosols, grader) =>
        assert(sol.length == 1, "Expected exactly 1 solution, but got " + sol.length + " solutions in " + rawContent)
        assert(grader.length <= 1, "Expected at most 1 grader, but got " + grader.length + " graders in " + rawContent)
        val (kyxsol, texsol, listingssol, txtsol, solfin) = sol.head
        val (expectedArtifact, solArgs: Map[String, String]) = (kyxsol, texsol, listingssol, txtsol, solfin) match {
          case (Some(s), None, None, None, None) => (artifactsFromKyxString(s), Map.empty)
          case (None, Some(s), None, None, None) => (artifactsFromTexMathString(s), Map.empty)
          case (None, None, Some(s), None, None) => (ArchiveArtifact(s), Map.empty)
          case (None, None, None, Some(s), None) =>
            val anyOfKyxSols = kyxlineExtractor("").r(KYX_SOL).findAllMatchIn(s).map(_.group(KYX_SOL)).toList
            if (anyOfKyxSols.isEmpty) (artifactsFromTexTextString(s), Map.empty)
            else (AnyOfArtifact(anyOfKyxSols.map(artifactsFromKyxString)), Map.empty)
          case (None, None, None, None, Some(s)) =>
            val (question, artifact) = solfinArtifactsFromString(s)
            (artifact, Map("question" -> question))
          case (None, None, None, None, None) => (TextArtifact(None), Map.empty)
        }
        val testSolArtifacts = expectedArtifact match {
          case AnyOfArtifact(artifacts) => artifacts ++ artifactsFromNSolContents(testsols, "\\testsol")
          case _ => expectedArtifact +: artifactsFromNSolContents(testsols, "\\testsol")
        }
        val noSolArtifacts = artifactsFromNSolContents(nosols, "\\nosol")
        val graderArgs = argsFromString(grader.headOption.flatMap(_._2))
        val uniqueSolArgs =
          solArgs.filter({ case (k, _) => !graderArgs.contains(k) }) // grader arguments override solution arguments
        val firstAlgoIdx = rawContent.indexOf("\\algog")
        val untilFirstAlgo = if (firstAlgoIdx >= 0) rawContent.substring(0, firstAlgoIdx) else rawContent
        assert(
          firstAlgoIdx == -1 || untilFirstAlgo.indexOf("\\ask") != untilFirstAlgo.lastIndexOf("\\ask") ||
            grader.nonEmpty,
          "Expected a grader since \\algog is defined for first question, but couldn't extract from " + rawContent,
        )
        AskQuestion(
          grader.headOption.map(_._1),
          graderArgs ++ uniqueSolArgs,
          expectedArtifact,
          testSolArtifacts,
          noSolArtifacts,
        )
      })
    }

    private def artifactsFromNSolContents(s: List[String], head: String): List[Artifact] = {
      s.map(_.trim.stripPrefix(head).trim.stripPrefix("{").stripSuffix("}"))
        .filter(_.nonEmpty)
        .flatMap(artifactFromSolContent)
    }

    /** Extracts grader information (`method`, `args`) from raw content. */
    def graderInfoFromString(rawContent: String): (String, Map[String, String]) = {
      GRADER_METHOD
        .r(GRADER, ARGS)
        .findFirstMatchIn(rawContent)
        .map(m => (m.group(GRADER), Option(m.group(ARGS)))) match {
        case Some((grader, args)) => (grader, argsFromString(args))
        case None => throw new IllegalArgumentException("Unexpected grader method " + rawContent)
      }
    }

    /** Translates `\sol` into an artifact. */
    def artifactFromSolContent(s: String): Option[Artifact] = {
      val artifacts = solContent("")
        .r(KYX_SOL, TEX_SOL, LISTINGS_SOL, TXT_SOL)
        .findAllMatchIn(s)
        .map(m =>
          (Option(m.group(KYX_SOL)), Option(m.group(TEX_SOL)), Option(m.group(LISTINGS_SOL)), Option(m.group(TXT_SOL)))
        )
        .map({
          case (Some(s), None, None, None) => artifactsFromKyxString(s)
          case (None, Some(s), None, None) => artifactsFromTexMathString(s)
          case (None, None, Some(s), None) => ArchiveArtifact(s)
          case (None, None, None, Some(s)) => artifactsFromTexTextString(s)
        })
        .toList
        .filter(_ != TextArtifact(None))
      artifacts match {
        case Nil => Some(TextArtifact(None))
        case a :: Nil => Some(a)
        case a => Some(AnyOfArtifact(a))
      }
    }

    /** Translates `\kyxline` string into an artifact. */
    def artifactsFromKyxString(s: String): Artifact = {
      if (s.contains(TURNSTILE)) SequentArtifact(s.split(Regex.quote(GOAL_SEP)).map(_.asSequent).toList)
      else {
        "ArchiveEntry|Theorem".r.findFirstMatchIn(s) match {
          case Some(_) => ArchiveArtifact(s)
          case None => Try(BelleParser(s)).toOption match {
              case Some(t) => TacticArtifact(s, t)
              case None =>
                if (s.contains("~>")) { SubstitutionArtifact(UnificationSubstitutionParser.parseSubstitutionPairs(s)) }
                else {
                  val commaMatches = EXPR_LIST_SPLITTER.findAllMatchIn(s).filter(_.group(1) != null)
                  val indices = (-1 +: commaMatches.map(_.start).toList :+ s.length).sliding(2).toList
                  val exprStrings = indices.map({ case i :: j :: Nil => s.substring(i + 1, j) })
                  if (exprStrings.size > 1) ListExpressionArtifact(exprStrings.map(_.asExpr)) else ExpressionArtifact(s)
                }
            }
        }
      }
    }

    /** Translates tex into an artifact. */
    def artifactsFromTexMathString(s: String): Artifact = {
      val x = Variable("x")
      if ((s.startsWith("\\{") || s.startsWith("{")) && s.endsWith("}")) {
        // lists of terms \{1,2,3\} or {1,x,3+4}
        TexExpressionArtifact(
          s.stripPrefix("\\")
            .stripPrefix("{")
            .stripSuffix("}")
            .stripSuffix("\\")
            .split(",")
            .filter(_.trim.nonEmpty)
            .map(s => Equal(x, s.asTerm))
            .reduceRightOption(Or)
            .getOrElse(False)
        )
      } else if (s == "\\infty") { TexExpressionArtifact(Number(Long.MaxValue)) }
      else if (s == "-\\infty") { TexExpressionArtifact(Neg(Number(Long.MaxValue))) }
      else {
        // intervals [0,3] \cup [0,\infty) \cup \lbrack -1.0,4 ] \cup (5,7\rbrack
        val interval = """(\(|\[|\\lbrack)\s*(-?\d+(?:\.\d+)?)\s*,\s*(-?\d+(?:\.\d+)?|\\infty)\s*(\)|]|\\rbrack)"""
          .r("(", "l", "u", ")")
        val ivfml = interval
          .findAllMatchIn(s)
          .map(m => (m.group("(") -> m.group("l"), m.group("u") -> m.group(")")))
          .map({ case (l, u) =>
            And(
              l match {
                case ("(", lv) => Less(Number(lv.toDouble), x)
                case ("[" | "\\lbrack", lv) => LessEqual(Number(lv.toDouble), x)
              },
              u match {
                case ("\\infty", ")") => True
                case (uv, ")") => Less(x, Number(uv.toDouble))
                case (uv, "]" | "\\rbrack") => LessEqual(x, Number(uv.toDouble))
              },
            )
          })
        if (ivfml.hasNext) TexExpressionArtifact(ivfml.reduceRightOption(Or).getOrElse(False))
        else Try(artifactsFromKyxString(s)).getOrElse(
          throw new IllegalArgumentException(
            "String " + s +
              " neither parseable as a list of numbers \\{7,...\\} nor as intervals [l,h) ++ (l,h) ++ [l,h] ++ (l,h] where l is a number and h is a number or \\infty"
          )
        )
      }
    }

    def artifactsFromTexTextString(s: String): Artifact = TextArtifact(if (s.trim.nonEmpty) Some(s) else None)

    /** Extracts the answers enclosed in `____` from `s`. */
    def extractSolfinAnswers(s: String): List[String] = SOLFIN_ANSWER_EXTRACTOR
      .findAllMatchIn(s)
      .map(_.group(ANSWER).trim)
      .toList

    /** Translates a `\solfin` body string (content of lstlisting) into a question string and an artifact. */
    def solfinArtifactsFromString(s: String): (String, Artifact) = {
      val answerStrings = extractSolfinAnswers(s)
      val artifact =
        if (answerStrings.isEmpty || answerStrings.exists(_.isEmpty)) TextArtifact(None)
        else artifactsFromKyxString(answerStrings.mkString(","))
      var i = 0
      val question = SOLFIN_ANSWER_EXTRACTOR
        .replaceAllIn(s, _ => { i = i + 1; Regex.quoteReplacement(ARG_PLACEHOLDER + i) })
        .trim
      (question, artifact)
    }

    /** Translates a `solfin` string (including lstlsting) into a question string and an artifact. */
    def solfinArtifactsFromLstList(s: String): (String, Artifact) = {
      val body = SOLFIN_BODY_EXTRACTOR.r(SOLFIN).findAllMatchIn(s).map(_.group(SOLFIN)).toList
      require(body.size == 1, "Expected a single solfin \\begin{lstlisting}...\\end{lstlsting}, but got " + s)
      solfinArtifactsFromString(body.head)
    }

    /** Translates a string `arg1="v1",arg2="v2",arg3="v\"3\"",...` into a map of arguments */
    def argsFromString(args: Option[String]): Map[String, String] = {
      args
        .map(GRADER_ARG.findAllMatchIn)
        .getOrElse(Iterator.empty)
        .map(m => (m.group(ARG_NAME), m.group(ARG_VAL).replace("\\\"", "\"")))
        .toMap
    }
  }

  /** A question that refers to earlier questions in the same problem. */
  case class MultiAskQuestion(main: AskQuestion, earlier: Map[Int, Question]) extends Question

  /** A question with true/false answer options. */
  case class AskTFQuestion(text: String, isTrue: Boolean) extends Question
  object AskTFQuestion {
    val QUESTION_START: String = "asktf"

    private val QUESTION_TEXT = "questiontext"
    private val SOL = "sol"

    private val GROUPS: List[String] = List(QUESTION_TEXT, SOL)
    private val QUESTION_TEXT_EXTRACTOR = """\s*(.*?)\s*"""
    private val QUESTION_SOL_EXTRACTOR = """\\(solf(?!in)|solt)"""
    private val QUESTION_EXTRACTOR: Regex =
      ("""(?s)\\""" + QUESTION_START + QUESTION_TEXT_EXTRACTOR + QUESTION_SOL_EXTRACTOR).r(GROUPS: _*)

    def firstFromString(rawContent: String): Option[Question] = {
      val asktf = QUESTION_EXTRACTOR.findFirstMatchIn(rawContent).map(m => (m.group(QUESTION_TEXT), m.group(SOL)))
      asktf.map({ case (text, c) => AskTFQuestion(text, c == "solt") })
    }
  }

  case class Choice(text: String, isCorrect: Boolean)
  abstract class ChoiceQuestion(questionStart: String, questionFactory: (String, List[Choice]) => Question) {
    val QUESTION_START: String = questionStart

    private val QUESTION_TEXT = "questiontext"
    private val IS_CORRECT_CHOICE = "*"
    private val CHOICE_TEXT = "choicetext"
    private val CHOICES = "choices"

    private val GROUPS: List[String] = List(QUESTION_TEXT, CHOICES)
    private val QUESTION_TEXT_EXTRACTOR = """\s*(.*?)\s*"""
    private val CHOICES_EXTRACTOR = """((?:\\choice(?:\*)?\s*(?-s:.*)\s*)+)"""
    private val SINGLE_CHOICE_EXTRACTOR = """\\choice(\*)?\s*(.*)""".r(IS_CORRECT_CHOICE, CHOICE_TEXT)
    private val QUESTION_EXTRACTOR: Regex =
      ("""(?s)\\""" + QUESTION_START + QUESTION_TEXT_EXTRACTOR + CHOICES_EXTRACTOR).r(GROUPS: _*)

    def firstFromString(rawContent: String): Option[Question] = {
      val choices = QUESTION_EXTRACTOR.findFirstMatchIn(rawContent).map(m => (m.group(QUESTION_TEXT), m.group(CHOICES)))
      choices.map({ case (text, c) => questionFactory(text, choicesFromString(c)) })
    }

    private def choicesFromString(rawContent: String): List[Choice] = {
      SINGLE_CHOICE_EXTRACTOR
        .findAllMatchIn(rawContent)
        .map(m => Choice(m.group(CHOICE_TEXT), m.group(IS_CORRECT_CHOICE) != null))
        .toList
    }
  }
  case class OneChoiceQuestion(text: String, choices: List[Choice]) extends Question
  object OneChoiceQuestion extends ChoiceQuestion("onechoice", new OneChoiceQuestion(_, _))

  case class AnyChoiceQuestion(text: String, choices: List[Choice]) extends Question
  object AnyChoiceQuestion extends ChoiceQuestion("anychoice", new AnyChoiceQuestion(_, _))

  /** A quiz problem block. */
  case class Problem(name: Option[String], label: Option[String], questions: List[Question], points: Option[Double])

  object Problem {
    private val PROBLEM_NAME = "problemname"
    private val PROBLEM_CONTENT = "problemcontent"
    private val PROBLEM_POINTS = "problempoints"
    private val PROBLEM_LABEL = "problemlabel"
    private val PROBLEM_EXTRACTOR =
      """(?s)\\begin\{problem}(?:\[(\d+\.?\d*)])?(?:\[([^]]*)])?(?:\\label\{([^}]+)})?(.*?)\\end\{problem}"""
        .r(PROBLEM_POINTS, PROBLEM_NAME, PROBLEM_LABEL, PROBLEM_CONTENT)
    private val QUESTION_EXTRACTOR =
      (AskTFQuestion.QUESTION_START :: AskQuestion.QUESTION_START :: OneChoiceQuestion.QUESTION_START ::
        AnyChoiceQuestion.QUESTION_START :: Nil)
        .map("\\\\(" + _ + ")")
        .mkString("|")
        .r(
          AskTFQuestion.getClass.getSimpleName,
          AskQuestion.getClass.getSimpleName,
          OneChoiceQuestion.getClass.getSimpleName,
          AnyChoiceQuestion.getClass.getSimpleName,
        )

    def fromString(s: String): List[Problem] = {
      PROBLEM_EXTRACTOR
        .findAllMatchIn(s)
        .map(m =>
          Problem(
            Option(m.group(PROBLEM_NAME)),
            Option(m.group(PROBLEM_LABEL)),
            questionsFromString(m.group(PROBLEM_CONTENT)),
            pointsFromString(Option(m.group(PROBLEM_POINTS))),
          )
        )
        .filter(!_.name.contains("Reflection"))
        .toList
    }

    /** The problem questions with grading information. */
    private def questionsFromString(rawContent: String): List[Question] = {
      val questions = QUESTION_EXTRACTOR
        .findAllMatchIn(rawContent)
        .flatMap(m => {
          (Option(m.group(AskQuestion.getClass.getSimpleName)) ::
            Option(m.group(OneChoiceQuestion.getClass.getSimpleName)) ::
            Option(m.group(AnyChoiceQuestion.getClass.getSimpleName)) ::
            Option(m.group(AskTFQuestion.getClass.getSimpleName)) :: Nil).filter(_.isDefined).head match {
            case Some(AskQuestion.QUESTION_START) => AskQuestion.firstFromString(rawContent.substring(m.start))
            case Some(OneChoiceQuestion.QUESTION_START) => OneChoiceQuestion
                .firstFromString(rawContent.substring(m.start))
            case Some(AnyChoiceQuestion.QUESTION_START) => AnyChoiceQuestion
                .firstFromString(rawContent.substring(m.start))
            case Some(AskTFQuestion.QUESTION_START) => AskTFQuestion.firstFromString(rawContent.substring(m.start))
          }
        })
        .toList
      val ARG_PLACEHOLDER_GROUP = "argPlaceholder"
      val NEG_HASH = (Regex.quote(AskQuestion.ARG_PLACEHOLDER) + """(-\d+)""").r(ARG_PLACEHOLDER_GROUP)
      questions
        .zipWithIndex
        .map({
          case (q @ AskQuestion(_, args, _, _, _), i) =>
            val backRefs = args
              .map({ case (k, v) =>
                (k, (v, NEG_HASH.findAllMatchIn(v).map(_.group(ARG_PLACEHOLDER_GROUP).toInt).toList))
              })
              .values
              .flatMap(_._2)
              .toList
            if (backRefs.nonEmpty) MultiAskQuestion(q, backRefs.map(j => (j, questions(i + j))).toMap) else q
          case (q, _) => q
        })
    }

    /** The total points of the problem. */
    private def pointsFromString(rawPoints: Option[String]): Option[Double] = rawPoints.map(_.toDouble)
  }
}
