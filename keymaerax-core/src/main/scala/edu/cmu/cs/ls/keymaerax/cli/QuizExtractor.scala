/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.{Artifact, ExpressionArtifact, ListExpressionArtifact, SequentArtifact, TexExpressionArtifact, TextArtifact}
import edu.cmu.cs.ls.keymaerax.core.{And, Equal, False, Less, LessEqual, Number, Or, True, Variable}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.util.matching.Regex

/** Extracts assessment information from tex sources. */
object QuizExtractor {
  abstract class Question

  /** One question in a problem with grading information. */
  case class AskQuestion(grader: Option[String], args: Map[String, String],
                         expected: Artifact, testSols: List[Artifact], noSols: List[Artifact]) extends Question
  object AskQuestion {
    val QUESTION_START: String = "ask"

    private val GRADER = "grader"
    private val ARGS = "args"
    private val KYX_SOL = "sol"
    private val TEX_TEXT_SOL = "textextsol"
    private val TEXT_SOL = "textsol"
    private val SOLFIN = "solfin"
    private val TEST_SOL = "testsol"
    private val NO_SOL = "nosol"
    private val ARG_NAME = "argName"
    private val ARG_VAL = "argVal"
    private val ANSWER = "answer"
    private val TURNSTILE = "==>"
    private val GOAL_SEP = ";;"
    private val INLINE_SOL_DELIM = "____"
    private val TEX_NO_BREAK_SPACE = "~"

    private def kyxlineExtractor(capture: String) = """\\kyxline\s*"(""" + capture + """[^"]+)""""
    private val KYXLINE_EXTRACTOR = kyxlineExtractor("").r(KYX_SOL)
    private val KYX_SOL_EXTRACTOR = """(?:\\sol(?!fin)\s*\{?\s*""" + KYXLINE_EXTRACTOR.regex + "}?)"
    //@note nested {} up to level 2
    private val TEXT_SOL_EXTRACTOR = """(?:\\sol(?!fin)\s*\{((?:[^}{]+|\{(?:[^}{]+|\{[^}{]*})*})*)})"""
    private val TEX_TEXT_SOL_EXTRACTOR = """(?:\\sol(?!fin)\s*\{\$(.+?)\$})"""
    private val SOLFIN_EXTRACTOR = """(?:\\solfin\s*\\begin\{lstlisting}([^\\]*)\\end\{lstlisting})"""
    private val SOL_EXTRACTOR = """(?:""" + KYX_SOL_EXTRACTOR + "|" + TEX_TEXT_SOL_EXTRACTOR + "|" + TEXT_SOL_EXTRACTOR + "|" + SOLFIN_EXTRACTOR + """)\s*"""
    private val SOLFIN_ANSWER_EXTRACTOR = ("(?s)" + INLINE_SOL_DELIM + TEX_NO_BREAK_SPACE + "*" + "(.*?)" + TEX_NO_BREAK_SPACE + "*" + INLINE_SOL_DELIM).r(ANSWER)
    //@todo test and no sol text answers
    private val TEST_SOL_EXTRACTOR = """((?:\\testsol\s*\{?\s*""" + kyxlineExtractor("?:") + """}?\s*)*)"""
    private val NO_SOL_EXTRACTOR = """((?:\\nosol\s*\{?\s*""" + kyxlineExtractor("?:") + """}?\s*)*)"""
    private val GRADER_EXTRACTOR = """(?:\\autog\s*\{(\w+)\((.*?)\)})?""".stripMargin

    private val ARG_SPLITTER = """(\w+)\s*=\s*"([^"]+)"""".r(ARG_NAME, ARG_VAL)
    private val EXPR_LIST_SPLITTER = """(?:\{[^{}]*})|(,)""".r //@note matches unwanted {...,...} left and , outside {} right so needs filtering of results (not just split)

    private val ASK_EXTRACTOR = """\\""" + QUESTION_START + """(?:.*?)"""
    private val GROUPS: List[String] = List(KYX_SOL, TEX_TEXT_SOL, TEXT_SOL, SOLFIN, TEST_SOL, NO_SOL, GRADER, ARGS)
    private val QUESTION_EXTRACTOR: Regex = ("(?s)" + ASK_EXTRACTOR + SOL_EXTRACTOR + TEST_SOL_EXTRACTOR + NO_SOL_EXTRACTOR + GRADER_EXTRACTOR).r(GROUPS:_*)

    def firstFromString(rawContent: String): Option[AskQuestion] = {
      val graderInfo = QUESTION_EXTRACTOR.findFirstMatchIn(rawContent).map(m => (m.group(KYX_SOL), m.group(TEX_TEXT_SOL), m.group(TEXT_SOL), m.group(SOLFIN), m.group(TEST_SOL), m.group(NO_SOL), Option(m.group(GRADER)), Option(m.group(ARGS))))
      graderInfo.map({ case (kyxsol, textextsol, textsol, solfin, testsol, nosol, grader, args) =>
        val (expectedArtifact, solArgs) = (kyxsol, textextsol, textsol, solfin) match {
          case (s, null, null, null) => (artifactsFromKyxString(s), Map.empty)
          case (null, s, null, null) => (artifactsFromTexMathString(s), Map.empty)
          case (null, null, s, null) => (artifactsFromTexTextString(s), Map.empty)
          case (null, null, null, s) =>
            val (question, artifact) = solfinArtifactsFromString(s)
            (artifact, Map("question" -> question))
        }
        val testSolArtifacts = expectedArtifact +: KYXLINE_EXTRACTOR.findAllMatchIn(testsol).map(_.group(KYX_SOL)).map(artifactsFromKyxString).toList
        val noSolArtifacts = KYXLINE_EXTRACTOR.findAllMatchIn(nosol).map(_.group(KYX_SOL)).map(artifactsFromKyxString).toList
        AskQuestion(grader, argsFromString(args) ++ solArgs, expectedArtifact, testSolArtifacts, noSolArtifacts)
      })
    }

    /** Translates `\kyxline` string into an artifact. */
    def artifactsFromKyxString(s: String): Artifact = {
      if (s.contains(TURNSTILE)) SequentArtifact(s.split(GOAL_SEP).map(_.asSequent).toList)
      else {
        val commaMatches = EXPR_LIST_SPLITTER.findAllMatchIn(s).filter(_.group(1) != null)
        val indices = (-1 +: commaMatches.map(_.start).toList :+ s.length).sliding(2).toList
        val exprStrings = indices.map({ case i :: j :: Nil => s.substring(i+1,j) })
        if (exprStrings.size > 1) ListExpressionArtifact(exprStrings.map(_.asExpr))
        else ExpressionArtifact(s.asExpr)
      }
    }

    /** Translates tex into an artifact. */
    def artifactsFromTexMathString(s: String): Artifact = {
      val x = Variable("x")
      if ((s.startsWith("\\{") || s.startsWith("{")) && s.endsWith("}")) {
        // lists of terms \{1,2,3\} or {1,x,3+4}
        TexExpressionArtifact(s.stripPrefix("\\").stripPrefix("{").stripSuffix("}").stripSuffix("\\").split(",").
          map(s => Equal(x, s.asTerm)).reduceRightOption(Or).getOrElse(False))
      } else {
        // intervals [0,3] \cup [0,\infty) \cup \lbrack -1.0,4 ] \cup (5,7\rbrack
        val interval = """(\(|\[|\\lbrack)\s*(-?\d+(?:\.\d+)?)\s*,\s*(-?\d+(?:\.\d+)?|\\infty)\s*(\)|]|\\rbrack)""".r("(", "l", "u", ")")
        val ivfml = interval.findAllMatchIn(s).map(m => (m.group("(") -> m.group("l"), m.group("u") -> m.group(")"))).map({
          case (l, u) => And(
            l match {
              case ("(", lv) => Less(Number(lv.toDouble), x)
              case ("[" | "\\lbrack", lv) => LessEqual(Number(lv.toDouble), x)
            },
            u match {
              case ("\\infty", ")") => True
              case (uv, ")") => Less(x, Number(uv.toDouble))
              case (uv, "]" | "\\rbrack") => LessEqual(x, Number(uv.toDouble))
            }
          )
        })
        if (ivfml.hasNext) TexExpressionArtifact(ivfml.reduceRightOption(Or).getOrElse(False))
        else throw new IllegalArgumentException("String " + s + " neither parseable as a a list of numbers \\{7,...\\} nor as intervals [l,h) ++ (l,h) ++ [l,h] ++ (l,h] where l is a number and h is a number or \\infty")
      }
    }

    def artifactsFromTexTextString(s: String): Artifact = TextArtifact(if (s.trim.nonEmpty) Some(s) else None)

    /** Translates a `\solfin` string into a question string and an artifact. */
    def solfinArtifactsFromString(s: String): (String, Artifact) = {
      val answerStrings = SOLFIN_ANSWER_EXTRACTOR.findAllMatchIn(s).map(_.group(ANSWER)).mkString(",")
      val artifact = artifactsFromKyxString(answerStrings)
      var i = 0
      val question = SOLFIN_ANSWER_EXTRACTOR.replaceAllIn(s, _ => { i = i+1; "#" + i }).trim
      (question, artifact)
    }

    def argsFromString(args: Option[String]): Map[String, String] = {
      args.map(ARG_SPLITTER.findAllMatchIn).getOrElse(Iterator.empty).
        map(m => (m.group(ARG_NAME), m.group(ARG_VAL))).
        toMap
    }
  }

  case class AskTFQuestion(text: String, isTrue: Boolean) extends Question
  object AskTFQuestion {
    val QUESTION_START: String = "asktf"

    private val QUESTION_TEXT = "questiontext"
    private val SOL = "sol"

    private val GROUPS: List[String] = List(QUESTION_TEXT, SOL)
    private val QUESTION_TEXT_EXTRACTOR = """\s*(.*?)\s*"""
    private val QUESTION_SOL_EXTRACTOR = """\\(solf(?!in)|solt)"""
    private val QUESTION_EXTRACTOR: Regex = ("""(?s)\\""" + QUESTION_START + QUESTION_TEXT_EXTRACTOR +
      QUESTION_SOL_EXTRACTOR).r(GROUPS:_*)

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
    private val QUESTION_EXTRACTOR: Regex = ("""(?s)\\""" + QUESTION_START + QUESTION_TEXT_EXTRACTOR +
      CHOICES_EXTRACTOR).r(GROUPS:_*)

    def firstFromString(rawContent: String): Option[Question] = {
      val choices = QUESTION_EXTRACTOR.findFirstMatchIn(rawContent).map(m => (m.group(QUESTION_TEXT), m.group(CHOICES)))
      choices.map({ case (text, c) => questionFactory(text, choicesFromString(c)) })
    }

    private def choicesFromString(rawContent: String): List[Choice] = {
      SINGLE_CHOICE_EXTRACTOR.findAllMatchIn(rawContent).map(m =>
        Choice(m.group(CHOICE_TEXT), m.group(IS_CORRECT_CHOICE) != null)).toList
    }
  }
  case class OneChoiceQuestion(text: String, choices: List[Choice]) extends Question
  object OneChoiceQuestion extends ChoiceQuestion("onechoice", new OneChoiceQuestion(_, _))

  case class AnyChoiceQuestion(text: String, choices: List[Choice]) extends Question
  object AnyChoiceQuestion extends ChoiceQuestion("anychoice", new AnyChoiceQuestion(_, _))

  /** A quiz problem block. */
  case class Problem(name: Option[String], label: Option[String], rawContent: String, rawPoints: Option[String]) {
    private val QUESTION_EXTRACTOR =
      (AskTFQuestion.QUESTION_START ::
        AskQuestion.QUESTION_START ::
        OneChoiceQuestion.QUESTION_START ::
        AnyChoiceQuestion.QUESTION_START :: Nil).
        map("\\\\(" + _ + ")").mkString("|").r(
        AskTFQuestion.getClass.getSimpleName,
        AskQuestion.getClass.getSimpleName,
        OneChoiceQuestion.getClass.getSimpleName,
        AnyChoiceQuestion.getClass.getSimpleName
      )

    /** The problem questions with grading information. */
    lazy val questions: List[Question] = QUESTION_EXTRACTOR.findAllMatchIn(rawContent).flatMap(m => {
      (Option(m.group(AskQuestion.getClass.getSimpleName)) ::
        Option(m.group(OneChoiceQuestion.getClass.getSimpleName)) ::
        Option(m.group(AnyChoiceQuestion.getClass.getSimpleName)) ::
        Option(m.group(AskTFQuestion.getClass.getSimpleName)) :: Nil).filter(_.isDefined).head match {
        case Some(AskQuestion.QUESTION_START) =>
          AskQuestion.firstFromString(rawContent.substring(m.start))
        case Some(OneChoiceQuestion.QUESTION_START) =>
          OneChoiceQuestion.firstFromString(rawContent.substring(m.start))
        case Some(AnyChoiceQuestion.QUESTION_START) =>
          AnyChoiceQuestion.firstFromString(rawContent.substring(m.start))
        case Some(AskTFQuestion.QUESTION_START) =>
          AskTFQuestion.firstFromString(rawContent.substring(m.start))
      }
    }).toList

    /** The total points of the problem. */
    def points: Option[Double] = rawPoints.map(_.toDouble)
  }

  object Problem {
    private val PROBLEM_NAME = "problemname"
    private val PROBLEM_CONTENT = "problemcontent"
    private val PROBLEM_POINTS = "problempoints"
    private val PROBLEM_LABEL = "problemlabel"
    private val PROBLEM_EXTRACTOR = """(?s)\\begin\{problem}(?:\[(\d+\.?\d*)])?(?:\[([^]]*)])?(?:\\label\{([^}]+)})?(.*?)\\end\{problem}""".r(PROBLEM_POINTS, PROBLEM_NAME, PROBLEM_LABEL, PROBLEM_CONTENT)

    def fromString(s: String): List[Problem] = {
      PROBLEM_EXTRACTOR.findAllMatchIn(s).map(m => Problem(Option(m.group(PROBLEM_NAME)), Option(m.group(PROBLEM_LABEL)), m.group(PROBLEM_CONTENT), Option(m.group(PROBLEM_POINTS)))).
        filter(_.points.exists(_ > 0.0)).
        toList
    }
  }
}
