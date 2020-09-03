package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.cli.QuizExtractor.AskQuestion
import spray.json._

import scala.util.matching.Regex

/** Extracts submission information from a JSON AST.  */
object Submission {

  object GradeJsonFormat {
    import spray.json.DefaultJsonProtocol._

    private val SCORES = "scores"

    implicit val scoreJsonFormat: JsonFormat[List[(Submission.Prompt, Double)]] = new RootJsonFormat[List[(Submission.Prompt, Double)]] {
      override def write(scores: List[(Submission.Prompt, Double)]): JsValue =
        JsObject(SCORES -> JsObject(scores.map({ case (p, s) => p.id.toString -> s.toJson }).toMap))

      override def read(json: JsValue): List[(Prompt, Double)] = {
        json.asJsObject.fields(SCORES).asJsObject.fields.toList.map({ case (k, JsNumber(v)) =>
          (SinglePrompt(k.toLong, "-1", "", -1.0, Nil), v.toDouble)
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

    implicit val graderCookieJsonFormat: JsonFormat[Submission.GraderCookie] = new RootJsonFormat[Submission.GraderCookie] {
      override def write(grader: GraderCookie): JsValue = {
        JsObject(
          ID -> grader.id.toJson,
          NAME -> grader.name.toJson,
          BODY -> s"${grader.method}".toJson
        )
      }

      override def read(json: JsValue): GraderCookie = {
        json.asJsObject.getFields(ID, NAME, BODY).toList match {
          case JsNumber(id) :: JsString(name) :: JsString(graderMethod) :: Nil =>
            GraderCookie(id.toLong, name, graderMethod)
        }
      }
    }

    implicit val answerJsonFormat: JsonFormat[Submission.Answer] = new RootJsonFormat[Submission.Answer] {
      override def write(answer: Answer): JsValue = {
        answer match {
          case ChoiceAnswer(id, label, name, _, text, isSelected) =>
            JsObject(
              ID -> id.toJson,
              LABEL -> label.toJson,
              NAME -> name.toJson,
              BODY -> text.toJson,
              IS_CHOICE -> true.toJson,
              IS_FILL_IN_GAP -> false.toJson,
              COOKIES -> JsArray(),
              USER_ANSWER -> JsObject(
                IS_CHECKED -> isSelected.toJson,
                TEXT -> "".toJson
              )
            )
          case TextAnswer(id, label, name, grader, answer, expected) =>
            if (name == "\\sol") {
              JsObject(
                ID -> id.toJson,
                LABEL -> label.toJson,
                NAME -> name.toJson,
                COOKIES -> (grader match {
                  case Some(g) => JsArray(g.toJson)
                  case None => JsArray()
                }),
                BODY_SRC -> expected.toJson,
                USER_ANSWER -> JsObject(
                  TEXT -> answer.toJson,
                  IS_CHECKED -> false.toJson
                ),
                IS_CHOICE -> false.toJson,
                IS_FILL_IN_GAP -> false.toJson
              )
            } else if (name == "\\solfin" || name == "\\solfinask") {
              JsObject(
                ID -> id.toJson,
                LABEL -> label.toJson,
                NAME -> "\\solfinask".toJson,
                //@todo fill cookies once JSON format is fixed
                COOKIES -> JsArray() /*(grader match {
                  case Some(g) => JsArray(g.toJson)
                  case None => JsArray()
                })*/,
                //@todo remove \\algog from body_src once JSON format is fixed
                BODY_SRC -> ("<%%(.+?)%%>".r("arg").replaceAllIn(expected, " ") + "\\algog {" + grader.map(_.method) + "}").toJson,
                SOLUTION_PROMPT -> JsObject(
                  NAME -> "solfin_sol".toJson,
                  BODY_SRC -> ("<%%(.+?)%%>".r("arg").replaceAllIn(expected, m =>
                    Regex.quoteReplacement("~~" + m.group("arg")) + "~~") +
                    "\\algog {" + grader.map(_.method) + "}").toJson,
                  COOKIES -> JsArray()
                ),
                USER_ANSWER -> JsObject(
                  TEXT -> answer.toJson,
                  IS_CHECKED -> false.toJson
                ),
                IS_CHOICE -> false.toJson,
                IS_FILL_IN_GAP -> true.toJson
              )
            } else throw new IllegalArgumentException("Unknown text question type " + name)
        }
      }

      override def read(json: JsValue): Answer = {
        val fields = json.asJsObject.fields
        val id = fields(ID) match { case JsNumber(n) => n.toLong }
        val name = fields(NAME) match { case JsString(s) => s }
        val label = fields(LABEL) match { case JsString(s) => s}
        val grader = fields(COOKIES).convertTo[List[GraderCookie]].find(_.name == "\\algog")
        (fields.get(IS_CHOICE), fields.get(IS_FILL_IN_GAP)) match {
          case (Some(JsBoolean(true)), None | Some(JsBoolean(false))) =>
            val text = fields(BODY) match { case JsString(s) => s }
            val answer = fields(USER_ANSWER) match {
              case a: JsObject => a.fields(IS_CHECKED) match { case JsBoolean(b) => b }
            }
            ChoiceAnswer(id, label, name, grader, text, answer)
          case (None | Some(JsBoolean(false)), None | Some(JsBoolean(false))) =>
            val bodySrc = fields(BODY_SRC) match { case JsString(s) =>
              val trimmed = s.trim
              //@note tex may mention extra braces (e.g. \solfin {\begin{lstlisting}...} \sol {\kyxline...})
              //@note careful: always annotate set answers in tex as math and extra braces to be save: \sol {$\{...\}$}
              if (trimmed.startsWith("{")) trimmed.stripPrefix("{").stripSuffix("}")
              else trimmed
            }
            val answer = fields(USER_ANSWER) match {
              case a: JsObject => a.fields(TEXT) match { case JsString(s) => s }
            }
            TextAnswer(id, label, name, grader, answer, bodySrc)
          case (None | Some(JsBoolean(false)), None | Some(JsBoolean(true))) =>
            //@note fill_in_the_gap_text contains question with empty placeholders <%% %%>
            //@note body_src contains question with empty placeholders <%% %%> plus autograder
            //@note solution_prompt.body_src contains solution without placeholders (but retains ~)! plus autograder
            //@note user_answers contains user answer filled into placeholders <%% answer %%>

            //val (bodySrcQuestion, bodySrcGrader) = extractQuestionGrader(json.asJsObject) //@note ignored for now
            val (rawSolPromptQuestion, solPromptGrader) = extractQuestionGrader(fields(SOLUTION_PROMPT).asJsObject)
            val placeHolderRepl = "~+(.+?)~+".r("arg")
            val solPromptQuestion = placeHolderRepl.replaceAllIn(rawSolPromptQuestion,
              m => Regex.quoteReplacement(AskQuestion.INLINE_SOL_DELIM + m.group("arg") + AskQuestion.INLINE_SOL_DELIM))
            //@note prefer grader cookie in case it is present
            val theGrader = (grader, solPromptGrader) match {
              case (Some(g), _) => Some(g)
              case (None, Some(g)) => Some(g)
              case (None, None) => None
            }
            val answer = fields(USER_ANSWER) match {
              case a: JsObject => a.fields(TEXT) match {
                case JsString(s) => "<%%(.+?)%%>".r("arg").replaceAllIn(s,
                  m => Regex.quoteReplacement(AskQuestion.INLINE_SOL_DELIM + m.group("arg") + AskQuestion.INLINE_SOL_DELIM))
              }
            }
            TextAnswer(id, label, name, theGrader, answer, solPromptQuestion)
        }
      }
    }

    private def extractQuestionGrader(o: JsObject): (String, Option[GraderCookie]) = {
      o.fields(BODY_SRC) match { case JsString(s) =>
        val trimmed = s.trim
        //@note solfin does not yet have grader cookie, grader info is (accidentally?) packed into body_src
        val (question, bodySrcGrader) = trimmed.split("""\\algog""").toList match {
          case q :: g :: Nil =>
            val graderCookie = GraderCookie(-1, "\\algog", g.trim.stripPrefix("{").stripSuffix("}"))
            (q.trim, Some(graderCookie))
          case q :: Nil => (q.trim, None)
        }
        //@note tex usually does not mention extra braces (e.g. \solfin \begin{lstlisting}...)
        val trimmedQuestion =
          if (question.startsWith("{")) question.stripPrefix("{").stripSuffix("}")
          else question
        (trimmedQuestion, bodySrcGrader)
      }
    }

    /** Prints and extracts a prompt and the answers submitted in response to it. */
    implicit val promptJsonFormat: JsonFormat[Submission.Prompt] = new RootJsonFormat[Submission.Prompt] {
      override def write(prompt: Submission.Prompt): JsValue = JsObject(
        ID -> prompt.id.toJson,
        POINT_VALUE -> prompt.points.toJson,
        NAME -> prompt.name.toJson,
        CHILDREN -> prompt.answers.toJson
      )

      override def read(json: JsValue): Submission.Prompt = {
        val root = json.asJsObject
        val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
        val name = root.fields(NAME) match { case JsString(s) => s }
        val points = root.fields(POINT_VALUE) match { case JsNumber(n) => n.toDouble }
        val answers = root.fields(CHILDREN) match {
          case JsArray(s) => s.map(_.convertTo[Submission.Answer]).toList
          case _ => List.empty
        }
        SinglePrompt(id, "-1", name, points, answers)
      }
    }

    implicit val problemJsonFormat: JsonFormat[Problem] = new RootJsonFormat[Problem] {
      override def write(problem: Problem): JsValue = JsObject(
        NUMBER -> problem.number.toJson,
        TITLE -> problem.title.toUpperCase.toJson,
        TYPE -> "segment".toJson,
        POINT_VALUE -> problem.prompts.map(_.points).sum.toJson,
        CHILDREN -> JsArray(JsObject(
          ID -> problem.id.toJson,
          NUMBER -> problem.number.toJson,
          TITLE -> problem.title.toJson,
          LABEL -> problem.label.toJson,
          PROMPTS -> problem.prompts.toJson,
          TYPE -> "atom".toJson,
          NAME -> "problem".toJson,
          POINT_VALUE -> problem.prompts.map(_.points).sum.toJson
        ))
      )

      /** Extracts a problem segment from the `json` problem object (identified by having "name"="problem"). */
      override def read(json: JsValue): Problem = {
        val root = json.asJsObject()
        require(root.fields(TYPE) match { case JsString("atom") => true case _ => false }, "Type 'atom' expected")
        require(root.fields(NAME) match { case JsString("problem") => true case _ => false }, "Name 'problem' expected")
        val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
        val title = root.fields(TITLE) match { case JsString(s) => s }
        val label = root.fields(LABEL) match { case JsString(s) => s }
        val prompts = root.fields.get(PROMPTS) match {
          case Some(JsArray(prompts)) => prompts.map(_.convertTo[Prompt]).toList.zipWithIndex.map({
            case (p: SinglePrompt, i) => p.copy(number=(i+'a'.toInt).toChar.toString)
            case (m@MultiPrompt(p: SinglePrompt, _), i) => m.copy(main=p.copy(number=(i+'a'.toInt).toChar.toString))
          })
          case _ => List.empty
        }
        Problem(id, "-1", title, label, prompts)
      }
    }

    implicit val chapterJsonFormat: JsonFormat[Chapter] = new RootJsonFormat[Chapter] {
      override def write(chapter: Chapter): JsValue = JsObject(
        ID -> chapter.id.toJson,
        LABEL -> chapter.label.toJson,
        CHILDREN -> chapter.problems.toJson
      )

      override def read(json: JsValue): Chapter = {
        val root = json.asJsObject
        //val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
        //val label = root.fields(LABEL) match { case JsString(s) => s }
        val problems = extractProblems(root, None)
        Chapter(-1, "", problems)
      }

      /** Extract problems from the chapter JSON object `root`, looking for the section number along the way. */
      private def extractProblems(root: JsObject, sectionNumber: Option[String]): List[Problem] = {
        root.fields.get(CHILDREN) match {
          case Some(JsArray(segments)) =>
            segments.flatMap({
              case s: JsObject =>
                //@note assumes we have only 1 problem per section, the problems themselves do not have numbers
                val sn = if (sectionNumber.isEmpty) s.fields.get(NUMBER).map({ case JsString(n) => n.trim }).filter(_.nonEmpty) else sectionNumber
                //@note only auto-grade those segments that are worth points
                s.fields.get(POINT_VALUE) match {
                  case Some(JsNumber(n)) if n > 0 => s.fields.get(TYPE) match {
                    case Some(JsString("segment")) => extractProblems(s, sn)
                    case Some(JsString("atom")) => s.fields(NAME) match {
                      case JsString("problem") => Some(s.convertTo[Problem].copy(number=sn.getOrElse("-1")))
                      case _ => None
                    }
                    case _ => None
                  }
                  case _ => None
                }
              case _ => None
            }).toList
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
  case class TextAnswer(id: Long, label: String, name: String, grader: Option[GraderCookie], answer: String, expected: String) extends Answer
  case class ChoiceAnswer(id: Long, label: String, name: String, grader: Option[GraderCookie], text: String, isSelected: Boolean) extends Answer

  /** A question with submitted answer, name indicates the type of prompt. */
  trait Prompt {
    val id: Long
    val number: String
    val name: String
    val points: Double
    val answers: List[Answer]
  }
  /** A single quiz question with submitted answer. `name` indicates the type of prompt. */
  case class SinglePrompt(id: Long, number: String, name: String, points: Double, answers: List[Answer]) extends Prompt
  /** An answered quiz question that needs access to answers of earlier questions. */
  case class MultiPrompt(main: Prompt, earlier: Map[Int, Prompt]) extends Prompt {
    val id: Long = main.id
    val number: String = main.number
    val name: String = main.name
    val points: Double = main.points
    val answers: List[Answer] = main.answers
  }
  /** A problem segment. */
  case class Problem(id: Long, number: String, title: String, label: String, prompts: List[Prompt])
  /** A quiz chapter. */
  case class Chapter(id: Long, label: String, problems: List[Problem])
}
