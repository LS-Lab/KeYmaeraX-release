package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.{IllFormedTacticApplicationException, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.{Artifact, AskGrader, ChoiceArtifact, ExpressionArtifact, ListExpressionArtifact, OneChoiceGrader, SequentArtifact}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.Inside.inside
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.LoneElement._

import scala.util.Try
import scala.util.matching.Regex

class AssessmentProverTests extends TacticTestBase {

  abstract class Question

  /** One question in a problem with grading information. */
  case class AskQuestion(grader: Option[String], args: Map[String, String],
                         expected: Artifact, testSols: List[Artifact], noSols: List[Artifact]) extends Question
  object AskQuestion {
    val QUESTION_START: String = "ask"

    private val GRADER = "grader"
    private val ARGS = "args"
    private val SOL = "sol"
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
    private val KYXLINE_EXTRACTOR = kyxlineExtractor("").r(SOL)
    private val SOL_EXTRACTOR = """(?:\\sol\s*""" + KYXLINE_EXTRACTOR.regex + ")"
    private val SOLFIN_EXTRACTOR = """(?:\\solfin\s*\\begin\{lstlisting}([^\\]*)\\end\{lstlisting})"""
    private val EITHER_SOL_EXTRACTOR = """(?:""" + SOL_EXTRACTOR + """|""" + SOLFIN_EXTRACTOR + """)\s*"""
    private val SOLFIN_ANSWER_EXTRACTOR = ("(?s)" + INLINE_SOL_DELIM + TEX_NO_BREAK_SPACE + "*" + "(.*?)" + TEX_NO_BREAK_SPACE + "*" + INLINE_SOL_DELIM).r(ANSWER)
    private val TEST_SOL_EXTRACTOR = """((?:\\testsol\s*""" + kyxlineExtractor("?:") + """\s*)*)"""
    private val NO_SOL_EXTRACTOR = """((?:\\nosol\s*""" + kyxlineExtractor("?:") + """\s*)*)"""
    private val GRADER_EXTRACTOR = """(?:\\autog\{(\w+)\((.*?)\)})?""".stripMargin

    private val ARG_SPLITTER = """(\w+)\s*=\s*"([^"]+)"""".r(ARG_NAME, ARG_VAL)
    private val EXPR_LIST_SPLITTER = """(?:\{[^{}]*})|(,)""".r //@note matches unwanted {...,...} left and , outside {} right so needs filtering of results (not just split)

    private val ASK_EXTRACTOR = """\\""" + QUESTION_START + """(?:.*?)"""
    private val GROUPS: List[String] = List(SOL, SOLFIN, TEST_SOL, NO_SOL, GRADER, ARGS)
    private val QUESTION_EXTRACTOR: Regex = ("(?s)" + ASK_EXTRACTOR + EITHER_SOL_EXTRACTOR + TEST_SOL_EXTRACTOR + NO_SOL_EXTRACTOR + GRADER_EXTRACTOR).r(GROUPS:_*)

    def firstFromString(rawContent: String): Option[AskQuestion] = {
      val graderInfo = QUESTION_EXTRACTOR.findFirstMatchIn(rawContent).map(m => (m.group(SOL), m.group(SOLFIN), m.group(TEST_SOL), m.group(NO_SOL), Option(m.group(GRADER)), Option(m.group(ARGS))))
      graderInfo.map({ case (sol, solfin, testsol, nosol, grader, args) =>
        val (expectedArtifact, solArgs) = (sol, solfin) match {
          case (s, null) => (artifactsFromString(s), Map.empty)
          case (null, s) =>
            val (question, artifact) = solfinArtifactsFromString(s)
            (artifact, Map("question" -> question))
        }
        val testSolArtifacts = expectedArtifact +: KYXLINE_EXTRACTOR.findAllMatchIn(testsol).map(_.group(SOL)).map(artifactsFromString).toList
        val noSolArtifacts = KYXLINE_EXTRACTOR.findAllMatchIn(nosol).map(_.group(SOL)).map(artifactsFromString).toList
        AskQuestion(grader, argsFromString(args) ++ solArgs, expectedArtifact, testSolArtifacts, noSolArtifacts)
      })
    }

    /** Translates a `\kyxline` string into an artifact. */
    def artifactsFromString(s: String): Artifact = {
      if (s.contains(TURNSTILE)) SequentArtifact(s.split(GOAL_SEP).map(_.asSequent).toList)
      else {
        val commaMatches = EXPR_LIST_SPLITTER.findAllMatchIn(s).filter(_.group(1) != null)
        val indices = (-1 +: commaMatches.map(_.start).toList :+ s.length).sliding(2).toList
        val exprStrings = indices.map({ case i :: j :: Nil => s.substring(i+1,j) })
        if (exprStrings.size > 1) ListExpressionArtifact(exprStrings.map(_.asExpr))
        else ExpressionArtifact(s.asExpr)
      }
    }

    /** Translates a `\solfin` string into a question string and an artifact. */
    def solfinArtifactsFromString(s: String): (String, Artifact) = {
      val answerStrings = SOLFIN_ANSWER_EXTRACTOR.findAllMatchIn(s).map(_.group(ANSWER)).mkString(",")
      val artifact = artifactsFromString(answerStrings)
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


  case class Choice(text: String, isCorrect: Boolean)
  case class OneChoiceQuestion(text: String, choices: List[(Choice)]) extends Question
  object OneChoiceQuestion {
    val QUESTION_START = "onechoice"

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

    def firstFromString(rawContent: String): Option[OneChoiceQuestion] = {
      val choices = QUESTION_EXTRACTOR.findFirstMatchIn(rawContent).map(m => (m.group(QUESTION_TEXT), m.group(CHOICES)))
      choices.map({ case (text, c) => OneChoiceQuestion(text, choicesFromString(c)) })
    }

    private def choicesFromString(rawContent: String): List[Choice] = {
      SINGLE_CHOICE_EXTRACTOR.findAllMatchIn(rawContent).map(m =>
        Choice(m.group(CHOICE_TEXT), m.group(IS_CORRECT_CHOICE) != null)).toList
    }
  }


  /** A quiz problem block. */
  case class Problem(name: Option[String], label: Option[String], rawContent: String, rawPoints: Option[String]) {
    private val QUESTION_EXTRACTOR =
      (AskQuestion.QUESTION_START :: OneChoiceQuestion.QUESTION_START :: Nil).
        map("\\\\(" + _ + ")").mkString("|").r(AskQuestion.getClass.getSimpleName, OneChoiceQuestion.getClass.getSimpleName)

    /** The problem questions with grading information. */
    lazy val questions: List[Question] = QUESTION_EXTRACTOR.findAllMatchIn(rawContent).flatMap(m => {
      (Option(m.group(AskQuestion.getClass.getSimpleName)) ::
       Option(m.group(OneChoiceQuestion.getClass.getSimpleName)) :: Nil).filter(_.isDefined).head match {
        case Some(AskQuestion.QUESTION_START) =>
          AskQuestion.firstFromString(rawContent.substring(m.start))
        case Some(OneChoiceQuestion.QUESTION_START) =>
          OneChoiceQuestion.firstFromString(rawContent.substring(m.start))
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
      PROBLEM_EXTRACTOR.findAllMatchIn(s).map(m => Problem(Option(m.group(PROBLEM_NAME)), Option(m.group(PROBLEM_LABEL)), m.group(PROBLEM_CONTENT), Option(m.group(PROBLEM_POINTS)))).toList
    }
  }

  private val COURSE_PATH: String = "/Course-current"
  private val QUIZ_PATH: String = COURSE_PATH + "/diderot/quiz"

  "Extractor" should "extract grading information" in {
    inside (Problem.fromString("""\begin{problem}\label{prob:first} \ask \sol \kyxline"x>=0" \end{problem}""")) {
      case p :: Nil =>
        p.name shouldBe empty
        p.points shouldBe empty
        p.label should contain ("prob:first")
        p.questions shouldBe List(AskQuestion(None, Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[4.][Problem A] \ask Something simple \sol \kyxline"x>=0" \end{problem}""")) {
      case p :: Nil =>
        p.name should contain ("Problem A")
        p.points should contain (4.0)
        p.questions shouldBe List(AskQuestion(None, Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[Problem B] \ask A syntactic equality \sol \kyxline"x>=0" \autog{syneq()} \end{problem}""")) {
      case p :: Nil =>
        p.name should contain ("Problem B")
        p.questions shouldBe
          List(AskQuestion(Some("syneq"), Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    }
    inside (Problem.fromString(
      """\begin{problem}
        |\ask \sol \kyxline"x>=0" \autog{syneq()}
        |\ask \sol \kyxline"y=2"
        |\autog{prove(question="#1 -> [{x'=v}]x>=0"
        |             tactic="auto")}
        |\end{problem}""".stripMargin)) {
      case p :: Nil =>
        p.questions shouldBe
          List(
            AskQuestion(Some("syneq"), Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty),
            AskQuestion(Some("prove"), Map("question" -> "#1 -> [{x'=v}]x>=0", "tactic" -> "auto"),
              ExpressionArtifact("y=2".asFormula), List(ExpressionArtifact("y=2".asFormula)), List.empty)
          )
    }
    inside (Problem.fromString("""\begin{problem}\ask \sol \kyxline"x>=0" \autog{polyeq(vars="x")}\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}\ask \sol \kyxline"x>=0" \testsol \kyxline"x+1>=1" \testsol \kyxline"x+2>=2" \autog{polyeq(vars="x")}\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula),
            List(ExpressionArtifact("x>=0".asFormula), ExpressionArtifact("x+1>=1".asFormula), ExpressionArtifact("x+2>=2".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}\ask \sol \kyxline"x>=0" \testsol \kyxline"x+1>=1" \nosol \kyxline"x+1>=0" \nosol \kyxline"x-1>=2" \autog{polyeq(vars="x")}\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula),
            List(ExpressionArtifact("x>=0".asFormula), ExpressionArtifact("x+1>=1".asFormula)),
            List(ExpressionArtifact("x+1>=0".asFormula), ExpressionArtifact("x-1>=2".asFormula))))
    }
    inside (Problem.fromString(
      """\begin{problem}
        |\ask A DI question
        |\sol \kyxline"2*x=y"
        |\autog{dI(vars="x",
        |          question="{x'=1,y'=2}")}
        |\end{problem}""".stripMargin)) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("dI"), Map("vars"->"x", "question"->"{x'=1,y'=2}"), ExpressionArtifact("2*x=y".asFormula), List(ExpressionArtifact("2*x=y".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}\ask \sol \kyxline"x>0 ==> x>=0 ;; y<0 ==> y<=0"\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(None, Map.empty,
            SequentArtifact(List("x>0 ==> x>=0".asSequent, "y<0 ==> y<=0".asSequent)),
            List(SequentArtifact(List("x>0 ==> x>=0".asSequent, "y<0 ==> y<=0".asSequent))), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}\ask \sol \kyxline"x>0,y>0,z>0"\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(None, Map.empty,
            ListExpressionArtifact(List("x>0".asFormula, "y>0".asFormula, "z>0".asFormula)),
            List(ListExpressionArtifact(List("x>0".asFormula, "y>0".asFormula, "z>0".asFormula))), List.empty))
    }
    inside (Problem.fromString(
      """\begin{problem}
        |\ask
        |\solfin
        |\begin{lstlisting}
        |x>=0 -> [{?____~~~~ true ~~~~____; x:=x+1;}*@invariant(____~~~~ x>=0 ~~~~____)]x>=0
        |\end{lstlisting}
        |\autog{loop()}
        |\end{problem}""".stripMargin)) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("loop"), Map("question" -> "x>=0 -> [{?#1; x:=x+1;}*@invariant(#2)]x>=0"),
            ListExpressionArtifact("true".asFormula :: "x>=0".asFormula :: Nil),
            List(ListExpressionArtifact("true".asFormula :: "x>=0".asFormula :: Nil)), List.empty))
    }
    inside (Problem.fromString(
      """\begin{problem}
        |\ask \sol \kyxline"x>=0"
        |\onechoice
        |A choice question
        |\choice  Wrong answer
        |\choice* Right answer
        |\choice  Another wrong answer
        |\onechoice
        |Another choice question
        |\choice* Correct
        |\choice Incorrect
        |\end{problem}""".stripMargin)) {
      case p :: Nil =>
        p.questions shouldBe List(
          AskQuestion(None, Map.empty, ExpressionArtifact("x>=0".asFormula),
            List(ExpressionArtifact("x>=0".asFormula)), List.empty),
          OneChoiceQuestion("A choice question", List(
            Choice("Wrong answer", isCorrect=false),
            Choice("Right answer", isCorrect=true),
            Choice("Another wrong answer", isCorrect=false))),
          OneChoiceQuestion("Another choice question", List(
            Choice("Correct", isCorrect=true),
            Choice("Incorrect", isCorrect=false)))
        )
    }
  }

  "Polynomial equality" should "prove simple term examples" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("2*x^2".asTerm, "x^2*2".asTerm) shouldBe 'proved
    AssessmentProver.polynomialEquality("x^3*y^2".asTerm, "y * x/1^2 * 4*x^2/2^2 * y".asTerm) shouldBe 'proved
    AssessmentProver.polynomialEquality("2*x^2".asTerm, "x^(1+3-2)*(3-1)/(-1+2)".asTerm) shouldBe 'proved
  }

  it should "prove simple formula examples" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("true".asFormula, "true".asFormula, normalize=false) shouldBe 'proved
    AssessmentProver.polynomialEquality("[ctrl;]true".asFormula, "[ctrl;]true".asFormula, normalize=false) shouldBe 'proved
    AssessmentProver.polynomialEquality("[ctrl;]P()".asFormula, "[ctrl;]P()".asFormula, normalize=false) shouldBe 'proved
    inside (AssessmentProver.polynomialEquality("x>=0".asFormula, "x+0*5>=2-4*1/2".asFormula, normalize=false)) {
      case p =>
        p.conclusion shouldBe "==> x=x+0*5 & 0=2-4*1/2".asSequent
        p shouldBe 'proved
    }
    inside (AssessmentProver.polynomialEquality("[x:=2;][?x>=0;]x>=0".asFormula, "[x:=3-1;][?x+0*5>=2-4*1/2;]x+0>=1-1".asFormula, normalize=false)) {
      case p =>
        p.conclusion shouldBe "==> x=x & 2=3-1 & x=x+0*5&0=2-4*1/2 & x=x+0 & 0=1-1".asSequent
        p shouldBe 'proved
    }
    inside (AssessmentProver.polynomialEquality("[x':=2;]x>=0".asFormula, "[x':=3-1;]x>=0".asFormula, normalize=false)) {
      case p =>
        p.conclusion shouldBe "==> x'=x' & 2=3-1 & x=x & 0=0".asSequent
        p shouldBe 'proved
    }
    the [IllegalArgumentException] thrownBy AssessmentProver.polynomialEquality(
      "x>=0".asFormula, "x+0*5>2-4*1/2".asFormula, normalize=false) should have message
      "requirement failed: Formula operators do not match at position '.'; expected x>=0 (GreaterEqual) but got x+0*5>2-4*1/2 (Greater)"
    the [IllegalArgumentException] thrownBy AssessmentProver.polynomialEquality(
      "[x:=2;]x>=0".asFormula, "[?x=2;]x+0*5>2-4*1/2".asFormula, normalize=false) should have message
      "requirement failed: Program operators do not match at position '.0'; expected x:=2; (Assign) but got ?x=2; (Test)"
    the [IllFormedTacticApplicationException] thrownBy AssessmentProver.polynomialEquality(
      "[x:=2;]x>=0".asFormula, "[x':=2;]x>=0".asFormula, normalize=false) should have message
      "Unable to create dependent tactic 'ANON', cause: 1*x^1 and 1*x'^1 do not fit"
  }

  it should "prove formula examples with normalization" in withZ3 { _ =>
    inside (AssessmentProver.polynomialEquality("x>=0".asFormula, "x+0*5>=2-4*1/2".asFormula, normalize=true)) {
      case p =>
        p.conclusion shouldBe "==> x=x+0*5-(2-4*1/2) & 0=0".asSequent
        p shouldBe 'proved
    }
    inside (AssessmentProver.polynomialEquality("x>=0".asFormula, "-(x+0*5)<=-(2-4*1/2)".asFormula, normalize=true)) {
      case p =>
        p.conclusion shouldBe "==> x=-(2-4*1/2)--(x+0*5) & 0=0".asSequent
        p shouldBe 'proved
    }
    inside (AssessmentProver.polynomialEquality("x>=0 & y=2".asFormula, "!(!-(x+0*5)<=-(2-4*1/2) | y!=2)".asFormula, normalize=true)) {
      case p =>
        p.conclusion shouldBe "==> x=-(2-4*1/2)--(x+0*5) & 0=0 & y-2=y-2 & 0=0".asSequent
        p shouldBe 'proved
    }
    the [IllegalArgumentException] thrownBy AssessmentProver.polynomialEquality(
      "x>=0".asFormula, "-(x+0*5) < -(2-4*1/2)".asFormula, normalize=true) should have message
      "requirement failed: Formula operators do not match at position '.'; expected x>=0 (GreaterEqual) but got -(2-4*1/2)--(x+0*5)>0 (Greater)"
  }

  "Value equality" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.valueEquality("1".asTerm, "1".asTerm) shouldBe 'proved
    AssessmentProver.valueEquality("1".asTerm :: "2".asTerm :: Nil, "1+0".asTerm :: "4-2".asTerm :: Nil) shouldBe 'proved
  }

  "DI result check" should "prove simple DI examples" in withZ3 { _ =>
    AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'=0".asSequent, diffAssignsMandatory=true, normalize=false) shouldBe 'proved
    AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [w':=-v;][v':=w;]2*v*v'+2*w*w'=0".asSequent, diffAssignsMandatory=true, normalize=false) shouldBe 'proved
    AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [w':=-v;v':=w;]2*v*v'+2*w*w'=0".asSequent, diffAssignsMandatory=true, normalize=false) shouldBe 'proved
    the [IllegalArgumentException] thrownBy
      AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w+2*w*v=0".asSequent, diffAssignsMandatory=true, normalize=false) should
      have message "requirement failed: Differential assignments do not match: expected assignments to v',w' but found none"
    the [IllegalArgumentException] thrownBy
      AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [v':=w;][w':=-v;]2*v*w<=2*w*v".asSequent, diffAssignsMandatory=true, normalize=false) should
      have message "requirement failed: Formula operators do not match at position '.1'; expected 2*v*w+2*w*(-v)-0=0 (Equal) but got 2*v*w<=2*w*v (LessEqual)"
  }

  it should "allow (partially) executed differential assignments on request" in withZ3 { _ =>
    AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [w':=-v;]2*v*w+2*w*w'=0".asSequent, diffAssignsMandatory=false, normalize=false) shouldBe 'proved
    AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w-2*w*v=0".asSequent, diffAssignsMandatory=false, normalize=false) shouldBe 'proved
    the [TacticInapplicableFailure] thrownBy AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w=2*w*v".asSequent, diffAssignsMandatory=false, normalize=false) should
      have message "Terms not equal (by equating coefficients): 2*v*w+2*w*(-v)-0, 2*v*w"
    the [TacticInapplicableFailure] thrownBy
      AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w+2*w*v=0".asSequent, diffAssignsMandatory=false, normalize=false) should
      have message "Terms not equal (by equating coefficients): 2*v*w+2*w*(-v)-0, 2*v*w+2*w*v"
    the [IllegalArgumentException] thrownBy
      AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w<=2*w*v".asSequent, diffAssignsMandatory=false, normalize=false) should
      have message "requirement failed: Formula operators do not match at position '.1'; expected 2*v*w+2*w*(-v)-0=0 (Equal) but got 2*v*w<=2*w*v (LessEqual)"
    the [IllegalArgumentException] thrownBy
      AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w<=2*w*v & 0=0".asSequent, diffAssignsMandatory=false, normalize=false) should
      have message "requirement failed: Formula operators do not match at position '.1'; expected 2*v*w+2*w*(-v)-0=0 (Equal) but got 2*v*w<=2*w*v&0=0 (And)"
  }

  it should "normalize" in withZ3 { _ =>
    AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [v':=w;][w':=-v;]2*v*w=2*w*v".asSequent, diffAssignsMandatory=true, normalize=true) shouldBe 'proved
    AssessmentProver.dIPremiseCheck("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w=2*w*v".asSequent, diffAssignsMandatory=false, normalize=true) shouldBe 'proved
  }

  "QE equivalence" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.qeEquivalence("x>=0".asFormula, "0<=x".asFormula)
    AssessmentProver.qeEquivalence("x>=4".asFormula, "x>=0 & x^2>=16".asFormula) shouldBe 'proved
    AssessmentProver.qeEquivalence("x=1".asFormula, "x^2>=1 & x^2<=x".asFormula) shouldBe 'proved
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      AssessmentProver.qeEquivalence("x>=4".asFormula, "abs(x)>=4 & abs(x)<=x".asFormula) shouldBe 'proved
    }
    AssessmentProver.qeEquivalence("x>=4".asFormula, "\\forall y (0<=y&y<=4 -> x>=y)".asFormula) shouldBe 'proved
    AssessmentProver.qeEquivalence("x>=4".asFormula, "\\exists y (y>=2 & x>=y^2)".asFormula) shouldBe 'proved
  }

  "Syntactic sequent equality" should "prove simple examples" in {
    AssessmentProver.syntacticEquality(List("x>0 ==> x>=0".asSequent), List("x>0 ==> x>=0".asSequent)) shouldBe 'proved
    AssessmentProver.syntacticEquality(List("x>0,y>0 ==> x>=0".asSequent), List("y>0,x>0 ==> x>=0".asSequent)) shouldBe 'proved
    AssessmentProver.syntacticEquality(List("x>0 ==> x>=0,y>0".asSequent), List("x>0 ==> y>0,x>=0".asSequent)) shouldBe 'proved
    AssessmentProver.syntacticEquality(
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent),
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent)) shouldBe 'proved
    the [IllFormedTacticApplicationException] thrownBy AssessmentProver.syntacticEquality(
      List("y>0 ==> y>=0".asSequent, "x>0 ==> x>=0".asSequent),
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent)) should have message
        """Unable to create dependent tactic 'equivReflexive', cause: requirement failed: Conclusion of fact
          |ElidingProvable(Provable(  ==>  (y>0->y>=0)&(x>0->x>=0)<->(y>0->y>=0)&(x>0->x>=0) proved))
          |must match sole open goal in
          |ElidingProvable(Provable(  ==>  (y>0->y>=0)&(x>0->x>=0)<->(x>0->x>=0)&(y>0->y>=0)
          |  from     ==>  (y>0->y>=0)&(x>0->x>=0)<->(x>0->x>=0)&(y>0->y>=0)))""".stripMargin
  }

  "Differential invariant checker" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.dICheck(ODESystem("{x'=1,y'=2}".asDifferentialProgram), "2*x=y".asFormula) shouldBe 'proved
    AssessmentProver.dICheck(ODESystem("{x'=x,y'=-y}".asDifferentialProgram), "x*y=1".asFormula) shouldBe 'proved
    AssessmentProver.dICheck(ODESystem("{x'=-y,y'=x}".asDifferentialProgram), "x^2+y^2=1".asFormula) shouldBe 'proved
    AssessmentProver.dICheck(ODESystem("{x'=1,y'=2}".asDifferentialProgram), "3*x=y".asFormula).subgoals.loneElement shouldBe "3*x=y, true ==> 3*1=2".asSequent
  }

  "Generic prove checker" should "prove simple examples" in withZ3 { _ =>
    AskGrader(Some(AskGrader.Modes.BELLE_PROOF), Map("tactic" -> "chase(1);prop"), ExpressionArtifact("A() -> [prg;]B()".asFormula)).
      check(ExpressionArtifact("A()->[prg;]B()".asFormula)) shouldBe 'proved
    AskGrader(Some(AskGrader.Modes.BELLE_PROOF), Map("tactic" -> "chase(1);prop"), SequentArtifact("A() ==> [prg;]B()".asSequent::Nil)).
      check(SequentArtifact("==> A() -> [prg;]B()".asSequent::Nil)) shouldBe 'proved
    val p = AskGrader(Some(AskGrader.Modes.BELLE_PROOF), Map("tactic" -> "chase(1);prop"), SequentArtifact("==> A() -> [prg;]B()".asSequent::"[sys;]C() ==> ".asSequent::Nil)).
      check(SequentArtifact("A() ==> [prg;]B()".asSequent::"==> [sys;]C() -> false&x=4".asSequent::Nil))
    p.conclusion shouldBe "==> ((A() -> [prg;]B()) <-> (true -> A() -> [prg;]B())) & ((true -> [sys;]C() -> false&x=4) <-> ([sys;]C() -> false))".asSequent
    p shouldBe 'proved
  }

  it should "prove optional question with solution as loop tactic input" in withZ3 { _ =>
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map(
        "question" -> "x>2 & y>=1 -> [{x:=x+y;y:=y+2;}*]x>1",
        "tactic" -> "implyR(1);loop({`#1`},1);auto;done"),
      ExpressionArtifact("false".asFormula)). //@note ignored because question will be used instead
      check(ExpressionArtifact("x>1&y>=0".asFormula)
    ) shouldBe 'proved
  }

  it should "prove optional question with a list of diffcuts" in withZ3 { _ =>
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map(
        "question" -> "x>=3 & v>=2 & a>=1 & j>=0 -> [{x'=v,v'=a,a'=j}]x>=3",
        "tactic" -> "implyR(1); for #i do dC({`#i`},1); <(nil, dI(1); done) endfor; dW(1); QE; done"
      ),
      ExpressionArtifact("false".asFormula)). //@note ignored because question will be used instead
      check(ListExpressionArtifact("a>=1".asFormula :: "v>=2".asFormula :: "x>=3".asFormula :: Nil)
    ) shouldBe 'proved
  }

  it should "prove optional question with solution as uniform substitution tactic input" in withZ3 { _ =>
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map(
        "question" -> "x<=m & V>=0 -> [{{v:=0; ++ ?Q(m,t,x,T,V);v:=V;};{x'=v,t'=1 & t<=T}}*]x<=m",
        "tactic" -> "US({`Q(m,t,x,T,V) ~> #1`});implyR(1);loop({`x<=m`},1);auto;done"),
      ExpressionArtifact("false".asFormula) //@note ignored because question will be used instead
    ).check(
      ExpressionArtifact("x<=m-V*(T-t)".asFormula)
    ) shouldBe 'proved
  }

  "Program equivalence" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.prgEquivalence("a;b;c;".asProgram, "{a;b;};c;".asProgram) shouldBe 'proved
    AssessmentProver.prgEquivalence("a;++b;++c;".asProgram, "{a;++b;}++c;".asProgram) shouldBe 'proved
    AssessmentProver.prgEquivalence("{a;++b;}{c;++d;++e;}".asProgram, "{a;++b;}{{c;++d;}++e;}".asProgram) shouldBe 'proved
    AssessmentProver.prgEquivalence("x:=2;++y:=3;".asProgram, "y:=4-1;++z:=2;x:=z;".asProgram) shouldBe 'proved
  }

  it should "prove simple system loops" in withZ3 { _ =>
    AssessmentProver.prgEquivalence("{a{|^@|};++b{|^@|};}*".asProgram, "{b{|^@|};++a{|^@|};}*".asProgram) shouldBe 'proved
  }

  it should "elaborate to system loops when dual does not occur literally" in withZ3 { _ =>
    AssessmentProver.prgEquivalence("{a;++b;}*".asProgram, "{b;++a;}*".asProgram) shouldBe 'proved
  }

  "Quiz checking" should "prove quiz 2" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/2/main.tex"))
  }

  it should "prove quiz 3" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/3/main.tex"))
  }

  it should "prove quiz 4" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/4/main.tex"))
  }

  it should "prove quiz 5" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/5/main.tex"))
  }

  it should "prove quiz 6" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/6/main.tex"))
  }

  it should "prove quiz 7" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/7/main.tex"))
  }

  it should "prove quiz 8" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/8/main.tex"))
  }

  it should "prove quiz 10" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/10/main.tex"))
  }

  it should "prove quiz 11" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/11/main.tex"))
  }

  it should "prove quiz 14" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/14/main.tex"))
  }

  private def run(problems: List[Problem]): Unit = {
    forEvery (table(problems)) { case (problem, grader, testAnswers, noAnswers) =>
      println("Problem section: " + problem)
      testAnswers.foreach(t => {
        println("Testing sol: " + t)
        val tic = System.nanoTime()
        grader.check(t) shouldBe 'proved withClue t
        println("Successfully verified sol")
        val toc = System.nanoTime()
        (toc - tic) should be <= 5000000000L
      })
      noAnswers.foreach(t => {
        println("Testing no-sol: " + t)
        val tic = System.nanoTime()
        Try(grader.check(t)).toOption.map(_ shouldNot be ('proved)) withClue t
        println("Successfully rejected no-sol")
        val toc = System.nanoTime()
        (toc - tic) should be <= 5000000000L
      })
    }
  }

  /** Extracts solutions (have, expected) from the resource ath `path`. */
  private def extractSolutions(path: String): List[Problem] = {
    val content = resource.managed(io.Source.fromInputStream(getClass.getResourceAsStream(path), "UTF-8")).apply(_.mkString)
    Problem.fromString(content.linesWithSeparators.filterNot(_.startsWith("%")).mkString)
  }

  private def table(problems: List[Problem]) = {
    Table(("Problem", "Grader", "TestAnswers", "NoAnswers"), problems.flatMap(p => p.questions.map({
      case q: AskQuestion =>
        (p.name, AskGrader(q.grader, q.args, q.expected), q.testSols, q.noSols)
      case q: OneChoiceQuestion =>
        val (correct, incorrect) = q.choices.partition(_.isCorrect) match {
          case (c, i) => (c.map(c => ChoiceArtifact(c.text)), i.map(c => ChoiceArtifact(c.text)))
        }
        assert(correct.size == 1, "Missing or non-unique correct solution")
        (p.name, OneChoiceGrader(Map.empty[String, String], correct.head), correct, incorrect)
    })):_*)
  }

}
