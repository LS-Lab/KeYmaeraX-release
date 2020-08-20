package edu.cmu.cs.ls.keymaerax.cli

import spray.json._

/** Extracts submission information from a JSON AST.  */
object Submission {

  object GradeJsonFormat {
    import spray.json.DefaultJsonProtocol._

    private val ID = "prompt_id"
    private val MAX_POINTS = "prompt_max_points"

    implicit val promptJsonFormat: JsonFormat[Submission.Prompt] = new RootJsonFormat[Submission.Prompt] {
      override def write(prompt: Submission.Prompt): JsValue = {
        JsObject(
          ID -> prompt.id.toJson,
          MAX_POINTS -> prompt.points.toJson
        )
      }
      override def read(json: JsValue): Submission.Prompt = {
        json.asJsObject.getFields(ID, MAX_POINTS) match {
          case JsNumber(id) :: JsNumber(points) :: Nil => Prompt(id.toLong, "", points.toDouble, Nil)
        }
      }
    }
  }

  object SubmissionJsonFormat {
    import spray.json.DefaultJsonProtocol._

    private val CHILDREN = "children"
    private val POINT_VALUE = "point_value"
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

    implicit val answerJsonFormat: JsonFormat[Submission.Answer] = new RootJsonFormat[Submission.Answer] {
      override def write(answer: Answer): JsValue = {
        answer match {
          case ChoiceAnswer(id, label, name, text, isSelected) =>
            JsObject(
              ID -> id.toJson,
              LABEL -> label.toJson,
              NAME -> name.toJson,
              BODY -> text.toJson,
              IS_CHOICE -> true.toJson,
              IS_FILL_IN_GAP -> false.toJson,
              USER_ANSWER -> JsObject(
                IS_CHECKED -> isSelected.toJson,
                TEXT -> "".toJson
              )
            )
          case TextAnswer(id, label, name, answer) =>
            JsObject(
              ID -> id.toJson,
              LABEL -> label.toJson,
              NAME -> name.toJson,
              USER_ANSWER -> JsObject(
                TEXT -> answer.toJson,
                IS_CHECKED -> false.toJson
              ),
              IS_CHOICE -> false.toJson,
              IS_FILL_IN_GAP -> false.toJson //@todo
            )
        }
      }

      override def read(json: JsValue): Answer = {
        val fields = json.asJsObject.fields
        val id = fields(ID) match { case JsNumber(n) => n.toLong }
        val name = fields(NAME) match { case JsString(s) => s }
        val label = fields(LABEL) match { case JsString(s) => s}
        (fields.get(IS_CHOICE), fields.get(IS_FILL_IN_GAP)) match {
          case (Some(JsBoolean(true)), None | Some(JsBoolean(false))) =>
            val text = fields(BODY) match { case JsString(s) => s }
            val answer = fields(USER_ANSWER) match {
              case a: JsObject => a.fields(IS_CHECKED) match { case JsBoolean(b) => b }
            }
            ChoiceAnswer(id, label, name, text, answer)
          case (None | Some(JsBoolean(false)), None | Some(JsBoolean(_))) =>
            val answer = fields(USER_ANSWER) match {
              case a: JsObject => a.fields(TEXT) match { case JsString(s) => s }
            }
            TextAnswer(id, label, name, answer)
        }
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
        Prompt(id, name, points, answers)
      }
    }

    implicit val problemJsonFormat: JsonFormat[Problem] = new RootJsonFormat[Problem] {
      override def write(problem: Problem): JsValue = JsObject(
        ID -> problem.id.toJson,
        TITLE -> problem.title.toJson,
        LABEL -> problem.label.toJson,
        PROMPTS -> problem.prompts.toJson,
        TYPE -> "atom".toJson,
        NAME -> "problem".toJson,
        POINT_VALUE -> problem.prompts.map(_.points).sum.toJson
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
          case Some(JsArray(prompts)) => prompts.map(_.convertTo[Prompt]).toList
          case _ => List.empty
        }
        Problem(id, title, label, prompts)
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
        val id = root.fields(ID) match { case JsNumber(n) => n.toLong }
        val label = root.fields(LABEL) match { case JsString(s) => s }
        val problems = extractProblems(root)
        Chapter(id, label, problems)
      }

      /** Extract problems from the chapter JSON object `root`. */
      private def extractProblems(root: JsObject): List[Problem] = {
        root.fields.get(CHILDREN) match {
          case Some(JsArray(segments)) =>
            segments.flatMap({
              case s: JsObject =>
                //@note only auto-grade those segments that are worth points
                s.fields.get(POINT_VALUE) match {
                  case Some(JsNumber(n)) if n > 0 => s.fields.get(TYPE) match {
                    case Some(JsString("segment")) => extractProblems(s)
                    case Some(JsString("atom")) => s.fields(NAME) match {
                      case JsString("problem") => Some(s.convertTo[Problem])
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


  trait Answer {
    val id: Long
    val label: String
    val name: String
  }
  case class TextAnswer(id: Long, label: String, name: String, answer: String) extends Answer
  case class ChoiceAnswer(id: Long, label: String, name: String, text: String, isSelected: Boolean) extends Answer
  /** A single quiz question with submitted answer. `name` indicates the type of prompt. */
  case class Prompt(id: Long, name: String, points: Double, answers: List[Answer])
  /** A problem segment. */
  case class Problem(id: Long, title: String, label: String, prompts: List[Prompt])
  /** A quiz chapter. */
  case class Chapter(id: Long, label: String, problems: List[Problem])
}
