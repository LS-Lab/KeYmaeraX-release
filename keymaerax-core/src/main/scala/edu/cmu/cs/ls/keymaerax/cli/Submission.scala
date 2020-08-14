package edu.cmu.cs.ls.keymaerax.cli

import spray.json._

/** Extracts submission information from a JSON AST.  */
object Submission {

  private val CHILDREN = "children"
  private val POINT_VALUE = "point_value"
  private val TITLE = "title"
  private val ID = "id"
  private val LABEL = "label"
  private val NAME = "name"
  private val TYPE = "type"
  private val BODY = "body"
  private val PROMPTS = "prompts"

  case class Answer(id: Long, text: String)
  /** A single quiz question with submitted answer. */
  case class Prompt(id: Long, points: Double, submission: Option[Answer])
  /** A problem segment. */
  case class Problem(id: Long, title: String, prompts: List[Prompt])
  /** A quiz chapter. */
  case class Chapter(id: Long, label: String, problems: List[Problem])

  def extract(root: JsObject): Chapter = {
    val id = root.fields(ID) match { case JsString(n) => n.toLong }
    val label = root.fields(LABEL) match { case JsString(s) => s }
    val problems = extractProblems(root)
    Chapter(id, label, problems)
  }

  def extractProblems(root: JsObject): List[Problem] = {
    root.fields.get(CHILDREN) match {
      case Some(JsArray(segments)) =>
        segments.flatMap({
          case s: JsObject =>
            //@note only auto-grade those segments that are worth points
            s.fields.get(POINT_VALUE) match {
              case Some(JsNumber(n)) if n>0 => s.fields.get(TYPE) match {
                case Some(JsString("segment")) => extractProblems(s)
                case Some(JsString("atom")) => s.fields(NAME) match {
                  case JsString("problem") => Some(extractProblem(s))
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

  /** Extracts a problem segment from the `root` JSON problem object (identified by having "name"="problem"). */
  private def extractProblem(root: JsObject): Problem = {
    require(root.fields(NAME) match { case JsString("problem") => true case _ => false })
    val id = root.fields(ID) match { case JsString(n) => n.toLong }
    val title = root.fields(TITLE) match { case JsString(s) => s }
    val prompts = root.fields.get(PROMPTS) match {
      case Some(JsArray(prompts)) => prompts.map(_.asJsObject).map(extractPrompt).toList
      case _ => List.empty
    }
    Problem(id, title, prompts)
  }

  /** Extracts a prompt and the answer submitted in response to it. */
  private def extractPrompt(root: JsObject): Prompt = {
    val id = root.fields(ID) match { case JsString(n) => n.toLong }
    val points = root.fields(POINT_VALUE) match { case JsNumber(n) => n.toDouble }
    val submission = root.fields(CHILDREN) match {
      case JsArray(s) =>
        require(s.size <= 1, "Expected at most one submission, but got " + s.size + " for prompt " + id)
        s.headOption.map(sub => {
          val fields = sub.asJsObject.fields
          val id = fields(ID) match { case JsString(n) => n.toLong }
          //@todo assumes submission will be in the prompt body
          val answer = fields(BODY) match {
            case JsString(s) => s
          }
          Answer(id, answer)
        })
    }
    Prompt(id, points, submission)
  }

}
