/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.cli.QuizExtractor.AskQuestion
import spray.json._

import scala.util.matching.Regex

/** Extracts submission information from a JSON AST. */
object Submission {

  object GradeJsonFormat {
    import spray.json.DefaultJsonProtocol._

    private val PROBLEMS = "problems"
    private val SCORES = "scores"

    implicit val scoreJsonFormat: JsonFormat[List[(Submission.Problem, Double)]] =
      new RootJsonFormat[List[(Submission.Problem, Double)]] {
        override def write(scores: List[(Submission.Problem, Double)]): JsValue = JsObject(
          PROBLEMS -> JsObject(scores.map({ case (p, _) => p.title -> p.points.toJson }).toMap),
          SCORES -> JsObject(scores.map({ case (p, s) => p.title -> s.toJson }).toMap),
        )

        override def read(json: JsValue): List[(Problem, Double)] = {
          val problems = json.asJsObject.fields(PROBLEMS).asJsObject.fields
          json
            .asJsObject
            .fields(SCORES)
            .asJsObject
            .fields
            .toList
            .map({ case (title, JsNumber(v)) =>
              val JsNumber(points) = problems(title)
              (Problem(-1, -1, "-1", title.trim, "", points.toDouble, Nil), v.toDouble)
            })
        }
      }
  }

  object SubmissionJsonFormat {
    import spray.json.DefaultJsonProtocol._

    private val CHILDREN = "children"
    private val POINT_VALUE = "point_value"
    private val NUMBER = "number"
    private val TITLE = "title"
    private val ID = "id"
    private val RANK = "rank"
    private val LABEL = "label"
    private val NAME = "name"
    private val TYPE = "type"
    private val BODY = "body"
    private val IS_CHOICE = "is_choice"
    private val IS_FILL_IN_GAP = "is_fill_in_the_gap"
    private val IS_CHECKED = "is_checked"
    private val PROMPTS = "prompts"
    private val USER_ANSWER = "user_answer"
    private val TEXT = "text"
    private val COOKIES = "cookies"
    private val BODY_SRC = "body_src"
    private val SOLUTION_PROMPT = "solution_prompt"

    implicit val graderCookieJsonFormat: JsonFormat[Submission.GraderCookie] =
      new RootJsonFormat[Submission.GraderCookie] {
        override def write(grader: GraderCookie): JsValue = {
          JsObject(ID -> grader.id.toJson, NAME -> grader.name.toJson, BODY -> s"${grader.method}".toJson)
        }

        override def read(json: JsValue): GraderCookie = {
          json.asJsObject.getFields(ID, NAME, BODY).toList match {
            case JsNumber(id) :: JsString(name) :: JsString(graderMethod) :: Nil =>
              GraderCookie(id.toLong, name, sanitizeGraderMethod(graderMethod))
          }
        }

        private def sanitizeGraderMethod(m: String): String = {
          // @note \%1 is %1 in JSON
          val m1 = m.replaceAll("""(?<!\\)%""", Regex.quoteReplacement("\\%")).replace("\n", " ")
          // @note {` `} become \u2018 in JSON
          var i = 0
          val m2 = "\u2018".r.replaceAllIn(m1, _ => { i = i + 1; if (i % 2 == 1) "{`" else "`}" })
          m2
        }
      }

    implicit val answerJsonFormat: JsonFormat[Submission.Answer] = new RootJsonFormat[Submission.Answer] {
      private val argPlaceholder = "(?s)<%%(?<arg>.*?)%%>".r

      override def write(answer: Answer): JsValue = {
        answer match {
          case ChoiceAnswer(id, label, name, _, text, isSelected) => JsObject(
              ID -> id.toJson,
              LABEL -> label.toJson,
              NAME -> name.toJson,
              BODY -> text.toJson,
              IS_CHOICE -> true.toJson,
              IS_FILL_IN_GAP -> false.toJson,
              COOKIES -> JsArray(),
              USER_ANSWER -> JsObject(IS_CHECKED -> isSelected.toJson, TEXT -> "".toJson),
            )
          case TextAnswer(id, label, name, grader, answer, expected) =>
            if (name == "\\sol") {
              JsObject(
                ID -> id.toJson,
                LABEL -> label.toJson,
                NAME -> name.toJson,
                COOKIES ->
                  (grader match {
                    case Some(g) => JsArray(g.toJson)
                    case None => JsArray()
                  }),
                BODY_SRC -> expected.toJson,
                USER_ANSWER -> JsObject(TEXT -> answer.toJson, IS_CHECKED -> false.toJson),
                IS_CHOICE -> false.toJson,
                IS_FILL_IN_GAP -> false.toJson,
              )
            } else if (name == "\\solfin" || name == "\\solfinask") {
              JsObject(
                ID -> id.toJson,
                LABEL -> label.toJson,
                NAME -> "\\solfinask".toJson,
                COOKIES -> JsArray(), // @note empty here, but filled in solution_prompt
                BODY_SRC -> argPlaceholder.replaceAllIn(expected, " ").toJson,
                SOLUTION_PROMPT -> JsObject(
                  NAME -> "solfinsol".toJson,
                  BODY_SRC ->
                    argPlaceholder.replaceAllIn(expected, m => Regex.quoteReplacement(s"~~${m.group("arg")}~~")).toJson,
                  COOKIES -> JsArray(grader.map(_.toJson).toList: _*),
                ),
                USER_ANSWER -> JsObject(TEXT -> answer.toJson, IS_CHECKED -> false.toJson),
                IS_CHOICE -> false.toJson,
                IS_FILL_IN_GAP -> true.toJson,
              )
            } else throw new IllegalArgumentException("Unknown text question type " + name)
        }
      }

      override def read(json: JsValue): Answer = {
        val fields = json.asJsObject.fields
        val id = fields(ID) match { case JsNumber(n) => n.toLong }
        val name = fields(NAME) match { case JsString(s) => s }
        val label = fields(LABEL) match { case JsString(s) => s }
        val grader = fields(COOKIES).convertTo[List[GraderCookie]].find(_.name == "\\algog")
        (fields.get(IS_CHOICE), fields.get(IS_FILL_IN_GAP)) match {
          case (Some(JsBoolean(true)), None | Some(JsBoolean(false))) =>
            val text = fields(BODY) match { case JsString(s) => s }
            val answer =
              fields(USER_ANSWER) match { case a: JsObject => a.fields(IS_CHECKED) match { case JsBoolean(b) => b } }
            ChoiceAnswer(id, label, name, grader, text, answer)
          case (None | Some(JsBoolean(false)), None | Some(JsBoolean(false))) =>
            val bodySrc = fields(BODY_SRC) match {
              case JsString(s) =>
                // @note sometimes ~ and \testsol and \nosols show up
                val trimmed = s
                  .replaceAll("~(?!>)", " ")
                  .trim
                  .linesWithSeparators
                  .filter(l => {
                    val ltrimmed = l.trim
                    !ltrimmed.startsWith("\\testsol") && !ltrimmed.startsWith("\\nosol")
                  })
                  .mkString
                  .trim
                // @note tex may mention extra braces (e.g. \solfin {\begin{lstlisting}...} \sol {\kyxline...})
                // @note careful: always annotate set answers in tex as math and extra braces to be save: \sol {$\{...\}$}
                if (trimmed.startsWith("{")) trimmed.stripPrefix("{").stripSuffix("}") else trimmed
            }
            val answer =
              fields(USER_ANSWER) match { case a: JsObject => a.fields(TEXT) match { case JsString(s) => s } }
            TextAnswer(id, label, name, grader, answer, bodySrc)
          case (None | Some(JsBoolean(false)), None | Some(JsBoolean(true))) =>
            // @note fill_in_the_gap_text contains question with empty placeholders <%% %%>
            // @note body_src contains question with empty placeholders <%% %%>
            // @note solution_prompt.body_src contains solution without placeholders (but retains ~)!
            // @note user_answers contains user answer filled into placeholders <%% answer %%>
            val solutionPrompt = fields(SOLUTION_PROMPT).asJsObject
            val solfinGrader = solutionPrompt.fields(COOKIES).convertTo[List[GraderCookie]].find(_.name == "\\algog")
            val rawSolPromptQuestion = solutionPrompt.fields(BODY_SRC) match { case JsString(s) => s }
            val solPromptQuestion = "(?s)~+(?<arg>.+?)~+"
              .r
              .replaceAllIn(
                rawSolPromptQuestion,
                m =>
                  Regex.quoteReplacement(AskQuestion.INLINE_SOL_DELIM + m.group("arg") + AskQuestion.INLINE_SOL_DELIM),
              )
            val answer = fields(USER_ANSWER) match {
              case a: JsObject => a.fields(TEXT) match {
                  case JsString(s) => argPlaceholder.replaceAllIn(
                      s,
                      m =>
                        Regex.quoteReplacement(
                          AskQuestion.INLINE_SOL_DELIM + m.group("arg") + AskQuestion.INLINE_SOL_DELIM
                        ),
                    )
                }
            }
            TextAnswer(id, label, name, solfinGrader, answer, solPromptQuestion)
        }
      }
    }

    /** Prints and extracts a prompt and the answers submitted in response to it. */
    implicit val promptJsonFormat: JsonFormat[Submission.Prompt] = new RootJsonFormat[Submission.Prompt] {
      override def write(prompt: Submission.Prompt): JsValue = JsObject(
        ID -> prompt.id.toJson,
        RANK -> prompt.rank.toJson,
        POINT_VALUE -> prompt.points.toJson,
        NAME -> prompt.name.toJson,
        CHILDREN -> prompt.answers.toJson,
      )

      override def read(json: JsValue): Submission.Prompt = {
        val root = json.asJsObject
        val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
        val rank = root.fields(RANK) match { case JsNumber(n) => n.toLong }
        val name = root.fields(NAME) match { case JsString(s) => s }
        val points = root.fields(POINT_VALUE) match { case JsNumber(n) => n.toDouble }
        val answers = root.fields(CHILDREN) match {
          case JsArray(s) => s.map(_.convertTo[Submission.Answer]).toList
          case _ => List.empty
        }
        SinglePrompt(id, rank, "-1", name, points, answers)
      }
    }

    implicit val problemJsonFormat: JsonFormat[Problem] = new RootJsonFormat[Problem] {
      override def write(problem: Problem): JsValue = JsObject(
        NUMBER -> problem.number.toJson,
        TITLE -> problem.title.toUpperCase.toJson,
        TYPE -> "segment".toJson,
        POINT_VALUE -> {
          val promptSum = problem.prompts.map(_.points).sum
          assert(problem.points == promptSum, "Problem total points is not equal to sum of prompt points")
          problem.points.toJson
        },
        CHILDREN -> JsArray(JsObject(
          ID -> problem.id.toJson,
          RANK -> problem.rank.toJson,
          NUMBER -> problem.number.toJson,
          TITLE -> problem.title.toJson,
          LABEL -> problem.label.toJson,
          PROMPTS -> problem.prompts.toJson,
          TYPE -> "atom".toJson,
          NAME -> "problem".toJson,
          POINT_VALUE -> problem.prompts.map(_.points).sum.toJson,
        )),
      )

      /** Extracts a problem segment from the `json` problem object (identified by having "name"="problem"). */
      override def read(json: JsValue): Problem = {
        val root = json.asJsObject()
        require(
          root.fields(TYPE) match {
            case JsString("atom") => true
            case _ => false
          },
          "Type 'atom' expected",
        )
        require(
          root.fields(NAME) match {
            case JsString("problem") => true
            case _ => false
          },
          "Name 'problem' expected",
        )
        val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
        val rank = root.fields(RANK) match { case JsNumber(n) => n.toLong }
        val title = root.fields(TITLE) match { case JsString(s) => s }
        val label = root.fields(LABEL) match { case JsString(s) => s }
        val points = root.fields(POINT_VALUE) match { case JsNumber(n) => n.toDouble }
        val prompts = root.fields.get(PROMPTS) match {
          case Some(JsArray(prompts)) => prompts
              .map(_.convertTo[Prompt])
              .toList
              .zipWithIndex
              .map({
                case (p: SinglePrompt, i) => p.copy(number = (i + 'a'.toInt).toChar.toString)
                case (m @ MultiPrompt(p: SinglePrompt, _), i) =>
                  m.copy(main = p.copy(number = (i + 'a'.toInt).toChar.toString))
              })
          case _ => List.empty
        }
        Problem(id, rank, "-1", title, label, points, prompts)
      }
    }

    implicit val chapterJsonFormat: JsonFormat[Chapter] = new RootJsonFormat[Chapter] {
      override def write(chapter: Chapter): JsValue =
        JsObject(ID -> chapter.id.toJson, LABEL -> chapter.label.toJson, CHILDREN -> chapter.problems.toJson)

      override def read(json: JsValue): Chapter = {
        val root = json.asJsObject
        // val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
        // val label = root.fields(LABEL) match { case JsString(s) => s }
        val problems = extractProblems(root, None)
        Chapter(-1, "", problems)
      }

      /** Extract problems from the chapter JSON object `root`, looking for the section number along the way. */
      private def extractProblems(root: JsObject, sectionNumber: Option[String]): List[Problem] = {
        root.fields.get(CHILDREN) match {
          case Some(JsArray(segments)) => segments
              .flatMap({
                case s: JsObject =>
                  // @note assumes we have only 1 problem per section, the problems themselves do not have numbers
                  val sn =
                    if (sectionNumber.isEmpty)
                      s.fields.get(NUMBER).map({ case JsString(n) => n.trim }).filter(_.nonEmpty)
                    else sectionNumber
                  // @note only auto-grade those segments that are worth points
                  s.fields.get(POINT_VALUE) match {
                    case Some(JsNumber(n)) if n > 0 =>
                      s.fields.get(TYPE) match {
                        case Some(JsString("segment")) => extractProblems(s, sn)
                        case Some(JsString("atom")) => s.fields(NAME) match {
                            case JsString("problem") => Some(s.convertTo[Problem].copy(number = sn.getOrElse("-1")))
                            case _ => None
                          }
                        case _ => None
                      }
                    case _ => None
                  }
                case _ => None
              })
              .toList
          case _ => List.empty
        }
      }
    }
  }

  /** Autograder information. */
  case class GraderCookie(id: Long, name: String, method: String)

  trait Answer {
    val id: Long
    val label: String
    val name: String
    val grader: Option[GraderCookie]
  }
  case class TextAnswer(
      id: Long,
      label: String,
      name: String,
      grader: Option[GraderCookie],
      answer: String,
      expected: String,
  ) extends Answer
  case class ChoiceAnswer(
      id: Long,
      label: String,
      name: String,
      grader: Option[GraderCookie],
      text: String,
      isSelected: Boolean,
  ) extends Answer

  /** A question with submitted answer, name indicates the type of prompt. */
  trait Prompt {
    val id: Long
    val rank: Long
    val number: String
    val name: String
    val points: Double
    val answers: List[Answer]
  }

  /** A single quiz question with submitted answer. `name` indicates the type of prompt. */
  case class SinglePrompt(id: Long, rank: Long, number: String, name: String, points: Double, answers: List[Answer])
      extends Prompt

  /** An answered quiz question that needs access to answers of earlier questions. */
  case class MultiPrompt(main: Prompt, earlier: Map[Int, Prompt]) extends Prompt {
    val id: Long = main.id
    val rank: Long = main.rank
    val number: String = main.number
    val name: String = main.name
    val points: Double = main.points
    val answers: List[Answer] = main.answers
  }

  /** A problem segment. */
  case class Problem(
      id: Long,
      rank: Long,
      number: String,
      title: String,
      label: String,
      points: Double,
      prompts: List[Prompt],
  )

  /** A quiz chapter. */
  case class Chapter(id: Long, label: String, problems: List[Problem])
}
