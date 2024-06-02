/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.{
  IllFormedTacticApplicationException,
  InapplicableUnificationKeyFailure,
  TacticInapplicableFailure,
}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.AskGrader.Modes
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.{
  AnyChoiceGrader,
  AnyOfArtifact,
  ArchiveArtifact,
  Artifact,
  AskGrader,
  AskTFGrader,
  BoolArtifact,
  ChoiceArtifact,
  ExpressionArtifact,
  Grader,
  ListExpressionArtifact,
  MultiArtifact,
  MultiAskGrader,
  OneChoiceGrader,
  SequentArtifact,
  SubstitutionArtifact,
  TacticArtifact,
  TexExpressionArtifact,
  TextArtifact,
}
import edu.cmu.cs.ls.keymaerax.cli.QuizExtractor._
import edu.cmu.cs.ls.keymaerax.cli.Submission.{ChoiceAnswer, TextAnswer}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.{ParseException, SubstitutionParser}
import edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest
import org.scalatest.EitherValues._
import org.scalatest.Inside.inside
import org.scalatest.LoneElement._
import org.scalatest.OptionValues._
import org.scalatest.prop.TableDrivenPropertyChecks._
import spray.json._

import java.io.{ByteArrayOutputStream, PrintWriter}
import scala.annotation.tailrec
import scala.collection.immutable.StringOps
import scala.io.Source

@IgnoreInBuildTest
class AssessmentProverTests extends TacticTestBase {

  private val COURSE_PATH: String = "/Course-current"
  private val QUIZ_PATH: String = COURSE_PATH + "/diderot/quizzes"
  private val LAB_PATH: String = COURSE_PATH + "/diderot/labs"

  private val RANDOM_TRIALS = 3
  private val rand = RepeatableRandom( /*1429498057447373779L*/ )

  "Extractor" should "extract grading information" in {
    inside(
      Problem.fromString("""\begin{problem}\label{prob:withoutpoints} \ask \sol{\kyxline"x>=0"} \end{problem}""")
    ) { case p :: Nil =>
      p.name shouldBe Symbol("empty")
      p.points shouldBe Symbol("empty")
      p.label should contain("prob:withoutpoints")
      p.questions shouldBe List(
        AskQuestion(None, Map.empty, ExpressionArtifact("x>=0"), List(ExpressionArtifact("x>=0")), List.empty)
      )
    }
    inside(
      Problem.fromString("""\begin{problem} \ask \sol{It is a text answer with $x=5$ some math} \end{problem}""")
    ) { case p :: Nil =>
      p.name shouldBe Symbol("empty")
      p.points shouldBe Symbol("empty")
      p.label shouldBe Symbol("empty")
      p.questions shouldBe List(AskQuestion(
        None,
        Map.empty,
        TextArtifact(Some("It is a text answer with $x=5$ some math")),
        List(TextArtifact(Some("It is a text answer with $x=5$ some math"))),
        List.empty,
      ))
    }
    inside(Problem.fromString("""\begin{problem}[1.0]\label{prob:first} \ask \sol{\kyxline"x>=0"} \end{problem}""")) {
      case p :: Nil =>
        p.name shouldBe Symbol("empty")
        p.points should contain(1.0)
        p.label should contain("prob:first")
        p.questions shouldBe List(
          AskQuestion(None, Map.empty, ExpressionArtifact("x>=0"), List(ExpressionArtifact("x>=0")), List.empty)
        )
    }
    inside(
      Problem.fromString("""\begin{problem}[4.][Problem A] \ask Something simple \sol{\kyxline"x>=0"} \end{problem}""")
    ) { case p :: Nil =>
      p.name should contain("Problem A")
      p.points should contain(4.0)
      p.questions shouldBe List(
        AskQuestion(None, Map.empty, ExpressionArtifact("x>=0"), List(ExpressionArtifact("x>=0")), List.empty)
      )
    }
    inside(
      Problem.fromString("""\begin{problem}[4.][Problem A] \ask A tex question \sol{$\{1,(-2),x^2\}$} \end{problem}""")
    ) { case p :: Nil =>
      p.name should contain("Problem A")
      p.points should contain(4.0)
      p.questions shouldBe List(AskQuestion(
        None,
        Map.empty,
        TexExpressionArtifact("x=1|x=-2|x=x^2".asFormula),
        List(TexExpressionArtifact("x=1|x=-2|x=x^2".asFormula)),
        List.empty,
      ))
    }
    inside(Problem.fromString(
      """\begin{problem}[4.][Problem A] \ask A tex question with missing set elements \sol{$\{1,,x^2,,,\}$} \end{problem}"""
    )) { case p :: Nil =>
      p.name should contain("Problem A")
      p.points should contain(4.0)
      p.questions shouldBe List(AskQuestion(
        None,
        Map.empty,
        TexExpressionArtifact("x=1|x=x^2".asFormula),
        List(TexExpressionArtifact("x=1|x=x^2".asFormula)),
        List.empty,
      ))
    }
    inside(Problem.fromString(
      """\begin{problem}[4.][Problem A] \ask A tex interval question \sol{$[-2.0,3) \cup (1,\infty)$} \end{problem}"""
    )) { case p :: Nil =>
      p.name should contain("Problem A")
      p.points should contain(4.0)
      p.questions shouldBe List(AskQuestion(
        None,
        Map.empty,
        TexExpressionArtifact("-2.0<=x&x<3|1<x&true".asFormula),
        List(TexExpressionArtifact("-2.0<=x&x<3|1<x&true".asFormula)),
        List.empty,
      ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0][Problem B] \ask A syntactic equality \sol{\kyxline"x>=0"} \algog{syneq()} \end{problem}"""
    )) { case p :: Nil =>
      p.name should contain("Problem B")
      p.questions shouldBe
        List(AskQuestion(
          Some("syneq"),
          Map.empty,
          ExpressionArtifact("x>=0"),
          List(ExpressionArtifact("x>=0")),
          List.empty,
        ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask \sol{\kyxline"x>=0"} \algog{syneq()}
        |\ask \sol{\kyxline"y=2"}
        |\algog{prove(question="\%1 -> [{x'=v}]x>=0",
        |             tactic="auto")}
        |\end{problem}""".stripMargin
    )) { case p :: Nil =>
      p.questions shouldBe
        List(
          AskQuestion(
            Some("syneq"),
            Map.empty,
            ExpressionArtifact("x>=0"),
            List(ExpressionArtifact("x>=0")),
            List.empty,
          ),
          AskQuestion(
            Some("prove"),
            Map("question" -> "\\%1 -> [{x'=v}]x>=0", "tactic" -> "auto"),
            ExpressionArtifact("y=2"),
            List(ExpressionArtifact("y=2")),
            List.empty,
          ),
        )
    }
    inside(
      Problem.fromString("""\begin{problem}[1.0]\ask \sol{\kyxline"x>=0"} \algog{polyeq(vars="x")}\end{problem}""")
    ) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          Some("polyeq"),
          Map("vars" -> "x"),
          ExpressionArtifact("x>=0"),
          List(ExpressionArtifact("x>=0")),
          List.empty,
        ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]\ask \sol{\kyxline"x>=0"} \testsol{\kyxline"x+1>=1"} \testsol{\kyxline"x+2>=2"} \algog{polyeq(vars="x", question="x>=0 -> [{x'=2}@invariant(x>=0)}*]x>=0")}\end{problem}"""
    )) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          Some("polyeq"),
          Map("vars" -> "x", "question" -> "x>=0 -> [{x'=2}@invariant(x>=0)}*]x>=0"),
          ExpressionArtifact("x>=0"),
          List(ExpressionArtifact("x>=0"), ExpressionArtifact("x+1>=1"), ExpressionArtifact("x+2>=2")),
          List.empty,
        ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]\ask \sol{\kyxline"x>=0"} \testsol{\kyxline"x+1>=1"} \nosol{\kyxline"x+1>=0"} \nosol{\kyxline"x-1>=2"} \algog{polyeq(vars="x")}\end{problem}"""
    )) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          Some("polyeq"),
          Map("vars" -> "x"),
          ExpressionArtifact("x>=0"),
          List(ExpressionArtifact("x>=0"), ExpressionArtifact("x+1>=1")),
          List(ExpressionArtifact("x+1>=0"), ExpressionArtifact("x-1>=2")),
        ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask A DI question
        |\sol{\kyxline"2*x=y"}
        |\algog{dI(vars="x",
        |          question="{x'=1,y'=2}")}
        |\end{problem}""".stripMargin
    )) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          Some("dI"),
          Map("vars" -> "x", "question" -> "{x'=1,y'=2}"),
          ExpressionArtifact("2*x=y"),
          List(ExpressionArtifact("2*x=y")),
          List.empty,
        ))
    }
    inside(
      Problem.fromString("""\begin{problem}[1.0]\ask \sol{\kyxline"x>0 ==> x>=0 ;; y<0 ==> y<=0"}\end{problem}""")
    ) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          None,
          Map.empty,
          SequentArtifact(List("x>0 ==> x>=0".asSequent, "y<0 ==> y<=0".asSequent)),
          List(SequentArtifact(List("x>0 ==> x>=0".asSequent, "y<0 ==> y<=0".asSequent))),
          List.empty,
        ))
    }
    inside(Problem.fromString("""\begin{problem}[1.0]\ask \sol{\kyxline"x>0,y>0,z>0"}\end{problem}""")) {
      case p :: Nil => p.questions shouldBe
          List(AskQuestion(
            None,
            Map.empty,
            ListExpressionArtifact(List("x>0".asFormula, "y>0".asFormula, "z>0".asFormula)),
            List(ListExpressionArtifact(List("x>0".asFormula, "y>0".asFormula, "z>0".asFormula))),
            List.empty,
          ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask
        |\solfin
        |\begin{lstlisting}
        |x>=0 -> [{?____~~~~ true ~~~~____; x:=x+1;}*@invariant(____~~~~ x>=0 ~~~~____)]x>=0
        |\end{lstlisting}
        |\algog{loop(feedback="3.4")}
        |\end{problem}""".stripMargin
    )) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          Some("loop"),
          Map("question" -> "x>=0 -> [{?\\%1; x:=x+1;}*@invariant(\\%2)]x>=0", "feedback" -> "3.4"),
          ListExpressionArtifact("true".asFormula :: "x>=0".asFormula :: Nil),
          List(ListExpressionArtifact("true".asFormula :: "x>=0".asFormula :: Nil)),
          List.empty,
        ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask
        |\solfin
        |\begin{lstlisting}
        |x>=0 -> [{?____~~~~ true ~~~~____; x:=x+1;}*@invariant(____~~~~ x>=0 ~~~~____)]x>=0
        |\end{lstlisting}
        |\algog{qe(question="\%1->true",feedback="3.4")}
        |\end{problem}""".stripMargin
    )) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          Some("qe"),
          Map("question" -> "\\%1->true", "feedback" -> "3.4"),
          ListExpressionArtifact("true".asFormula :: "x>=0".asFormula :: Nil),
          List(ListExpressionArtifact("true".asFormula :: "x>=0".asFormula :: Nil)),
          List.empty,
        ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask
        |\solfin
        |\begin{lstlisting}
        |x>=0 -> [{?____~~~~ true ~~~~____; x:=x+1;}*@invariant(____~~~~ x>=0 ~~~~____)]x>=0
        |\end{lstlisting}
        |\algog{testModel(precondition="x>0",postcondition="x>0)}
        |\end{problem}""".stripMargin
    )) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          Some("testModel"),
          Map("precondition" -> "x>0", "postcondition" -> "y>0"),
          ListExpressionArtifact("true".asFormula :: "x>=0".asFormula :: Nil),
          List(ListExpressionArtifact("true".asFormula :: "x>=0".asFormula :: Nil)),
          List.empty,
        ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask
        |\sol
        |{\begin{lstlisting}
        |x>=0 -> [{?true; x:=x+1;}*@invariant(x>=0)]x>=0
        |\end{lstlisting}}
        |\algog{checkArchive()}
        |\end{problem}}""".stripMargin
    )) { case p :: Nil =>
      p.questions shouldBe
        List(AskQuestion(
          Some("checkArchive"),
          Map.empty,
          ArchiveArtifact("x>=0 -> [{?true; x:=x+1;}*@invariant(x>=0)]x>=0"),
          List(ArchiveArtifact("x>=0 -> [{?true; x:=x+1;}*@invariant(x>=0)]x>=0")),
          List.empty,
        ))
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask \sol{\kyxline"x>=0"}
        |\onechoice
        |A choice question
        |\choice  Wrong answer
        |\choice* Right answer
        |\choice  Another wrong answer
        |\onechoice
        |Another choice question
        |\choice* Correct
        |\choice Incorrect
        |\end{problem}""".stripMargin
    )) { case p :: Nil =>
      p.questions shouldBe List(
        AskQuestion(None, Map.empty, ExpressionArtifact("x>=0"), List(ExpressionArtifact("x>=0")), List.empty),
        OneChoiceQuestion(
          "A choice question",
          List(
            QuizExtractor.Choice("Wrong answer", isCorrect = false),
            QuizExtractor.Choice("Right answer", isCorrect = true),
            QuizExtractor.Choice("Another wrong answer", isCorrect = false),
          ),
        ),
        OneChoiceQuestion(
          "Another choice question",
          List(QuizExtractor.Choice("Correct", isCorrect = true), QuizExtractor.Choice("Incorrect", isCorrect = false)),
        ),
      )
    }
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask Question 1 \sol{\kyxline"x*y^2=-1"}
        |\ask Question 2 \sol{\kyxline"y'=y/2"}
        |\algog{prove(question="x<0 -> [{x'=-x}]x<0",tactic="implyR(1); dG({`\%1`},{`\%-1`},1); dI(1.0); QE; done")}
        |\end{problem}""".stripMargin
    )) { case p :: Nil =>
      val first =
        AskQuestion(None, Map.empty, ExpressionArtifact("x*y^2=-1"), List(ExpressionArtifact("x*y^2=-1")), List.empty)
      val second = AskQuestion(
        Some("prove"),
        Map("question" -> "x<0 -> [{x'=-x}]x<0", "tactic" -> "implyR(1); dG({`\\%1`},{`\\%-1`},1); dI(1.0); QE; done"),
        ExpressionArtifact("y'=y/2"),
        List(ExpressionArtifact("y'=y/2")),
        List.empty,
      )
      p.questions shouldBe List(first, MultiAskQuestion(second, Map(-1 -> first)))
    }
    // test that all test cases are read
    inside(Problem.fromString(
      """\begin{problem}[1.0]
        |\ask Question 1
        |\sol{\kyxline"3"}
        |\testsol{\kyxline"2+1"}
        |\testsol{$\{1,2,3\}$}
        |\testsol{$[3,4] \cup \lbrack -1,\infty)$}
        |\testsol{A text answer}
        |\nosol{\kyxline"2+2"}
        |\nosol{A wrong text answer}
        |\nosol{$[8,9] \cup \lbrack -2,4)$}
        |\nosol{$\{5,6,7\}$}
        |\nosol{ }
        |\algog{syneq(feedback="A
        |very long
        |feedback.")}
        |\end{problem}""".stripMargin
    )) { case p :: Nil =>
      p.questions shouldBe List(AskQuestion(
        grader = Some("syneq"),
        args = Map("feedback" -> "A\nvery long\nfeedback."),
        expected = ExpressionArtifact("3"),
        testSols = List(
          ExpressionArtifact("3"),
          ExpressionArtifact("2+1"),
          TexExpressionArtifact("x=1|x=2|x=3".asFormula),
          TexExpressionArtifact("3<=x&x<=4 | -1<=x&true".asFormula),
          TextArtifact(Some("A text answer")),
        ),
        noSols = List(
          ExpressionArtifact("2+2"),
          TextArtifact(Some("A wrong text answer")),
          TexExpressionArtifact("8<=x&x<=9 | -2<=x&x<4".asFormula),
          TexExpressionArtifact("x=5|x=6|x=7".asFormula),
          TextArtifact(None),
        ),
      ))
    }
  }

  "Syntactic equality" should "return useful error messages" in withZ3 { _ =>
    // expected formula, answered with predicate
    AskGrader(Some(Modes.SYN_EQ), Map.empty, ExpressionArtifact("x>=0"))
      .check(ExpressionArtifact("p(x)"))
      .toOption
      .value shouldBe "" // @note expect term p(x) to be elaborated to predicate p(x), so no hint about wrong answer kind expected
  }

  it should "handle expected n/a" in withZ3 { _ =>
    AskGrader(Some(Modes.SYN_EQ), Map.empty, ExpressionArtifact("n/a"))
      .check(ExpressionArtifact("n/a"))
      .left
      .value shouldBe Symbol("proved")
    AskGrader(Some(Modes.SYN_EQ), Map.empty, ExpressionArtifact("n/a"))
      .check(ExpressionArtifact("N/A"))
      .left
      .value shouldBe Symbol("proved")
    AskGrader(Some(Modes.SYN_EQ), Map.empty, ExpressionArtifact("n/a"))
      .check(ExpressionArtifact("f(x)"))
      .toOption
      .value shouldBe "Incorrect f(x)"
  }

  "Polynomial equality" should "prove simple term examples" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("2*x^2".asTerm, "x^2*2".asTerm) shouldBe Symbol("proved")
    AssessmentProver.polynomialEquality("x^3*y^2".asTerm, "y * x/1^2 * 4*x^2/2^2 * y".asTerm) shouldBe Symbol("proved")
    AssessmentProver.polynomialEquality("2*x^2".asTerm, "x^(1+3-2)*(3-1)/(-1+2)".asTerm) shouldBe Symbol("proved")
    AssessmentProver.polynomialEquality("x^2^3".asTerm, "x^8".asTerm) shouldBe Symbol("proved")
  }

  it should "prove non-constant polynomial exponentials" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("e^(6*t)".asTerm, "e^((5+1)*t)".asTerm) shouldBe Symbol("proved")
    AssessmentProver.polynomialEquality("e^2^t".asTerm, "e^(3-1)^t".asTerm) shouldBe Symbol("proved")
    AssessmentProver.polynomialEquality("(e^2)^(t^1)".asTerm, "(e^(3-1))^t".asTerm) shouldBe Symbol("proved")
    AssessmentProver.polynomialEquality("e^x+e^y".asTerm, "e^(2*x/2)+e^(1*y*(1^2))".asTerm) shouldBe Symbol("proved")
    the[IllegalArgumentException] thrownBy AssessmentProver
      .polynomialEquality("e^(6*t)".asTerm, "f^(6*t)".asTerm) should
      have message "requirement failed: Expected all function symbols to match, but found non-matching symbols (pow,Set(e, t)) vs. (pow,Set(f, t))"
    // true but doesn't work
    the[IllegalArgumentException] thrownBy AssessmentProver
      .polynomialEquality("e^x*e^y".asTerm, "e^(x+y)".asTerm) should
      have message "requirement failed: Expected all function symbols to match, but found non-matching symbols (pow,Set(e, x)),(pow,Set(e, y)) vs. (pow,Set(e, x, y))"
  }

  it should "prove non-constant divisions" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("x^2/x".asTerm, "x^2/(2*x/2)".asTerm) shouldBe Symbol("proved")
  }

  it should "prove functions" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("sin(x)".asTerm, "sin(0+x/1)".asTerm) shouldBe Symbol("proved")
    AssessmentProver
      .polynomialEquality("sin(x)*cos(y)".asTerm, "cos(2*y/2)*sin(0+x/1)".asTerm) shouldBe Symbol("proved")
    AssessmentProver.polynomialEquality("sin(x)*sin(y)".asTerm, "sin(x*1)*sin(y*1)".asTerm) shouldBe Symbol("proved")
    the[IllegalArgumentException] thrownBy AssessmentProver
      .polynomialEquality("sin(x)*sin(y)".asTerm, "sin(x)*sin(z)".asTerm) should
      have message "requirement failed: Expected all function symbols to match, but found non-matching symbols (sin,Set(x)),(sin,Set(y)) vs. (sin,Set(x)),(sin,Set(z))"
    the[IllegalArgumentException] thrownBy AssessmentProver
      .polynomialEquality("sin(x)*sin(y)".asTerm, "sin(z)*sin(y)".asTerm) should
      have message "requirement failed: Expected all function symbols to match, but found non-matching symbols (sin,Set(x)),(sin,Set(y)) vs. (sin,Set(z)),(sin,Set(y))"
    the[IllegalArgumentException] thrownBy AssessmentProver.polynomialEquality("cos(x)".asTerm, "sin(x)".asTerm) should
      have message "requirement failed: Expected all function symbols to match, but found non-matching symbols (cos,Set(x)) vs. (sin,Set(x))"
  }

  it should "prove simple formula examples" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("true".asFormula, "true".asFormula, normalize = false) shouldBe Symbol("proved")
    AssessmentProver
      .polynomialEquality("[ctrl;]true".asFormula, "[ctrl;]true".asFormula, normalize = false) shouldBe Symbol("proved")
    AssessmentProver
      .polynomialEquality("[ctrl;]P()".asFormula, "[ctrl;]P()".asFormula, normalize = false) shouldBe Symbol("proved")
    inside(AssessmentProver.polynomialEquality("x>=0".asFormula, "x+0*5>=2-4*1/2".asFormula, normalize = false)) {
      case p =>
        p.conclusion shouldBe "==> x=x+0*5 & 0=2-4*1/2".asSequent
        p shouldBe Symbol("proved")
    }
    inside(AssessmentProver.polynomialEquality(
      "[x:=2;][?x>=0;]x>=0".asFormula,
      "[x:=3-1;][?x+0*5>=2-4*1/2;]x+0>=1-1".asFormula,
      normalize = false,
    )) { case p =>
      p.conclusion shouldBe "==> x=x & 2=3-1 & x=x+0*5&0=2-4*1/2 & x=x+0 & 0=1-1".asSequent
      p shouldBe Symbol("proved")
    }
    inside(
      AssessmentProver.polynomialEquality("[x':=2;]x>=0".asFormula, "[x':=3-1;]x>=0".asFormula, normalize = false)
    ) { case p =>
      p.conclusion shouldBe "==> x'=x' & 2=3-1 & x=x & 0=0".asSequent
      p shouldBe Symbol("proved")
    }
    the[IllegalArgumentException] thrownBy AssessmentProver
      .polynomialEquality("x>=0".asFormula, "x+0*5>2-4*1/2".asFormula, normalize = false) should have message
      "requirement failed: Formula operators do not match at position '.'; expected x>=0 (GreaterEqual) but got x+0*5>2-4*1/2 (Greater)"
    the[IllegalArgumentException] thrownBy AssessmentProver.polynomialEquality(
      "[x:=2;]x>=0".asFormula,
      "[?x=2;]x+0*5>2-4*1/2".asFormula,
      normalize = false,
    ) should have message
      "requirement failed: Program operators do not match at position '.0'; expected x:=2; (Assign) but got ?x=2; (Test)"
    the[IllFormedTacticApplicationException] thrownBy AssessmentProver
      .polynomialEquality("[x:=2;]x>=0".asFormula, "[x':=2;]x>=0".asFormula, normalize = false) should have message
      "1*x^1 and 1*x'^1 do not fit"
  }

  it should "prove formula examples with normalization" in withZ3 { _ =>
    inside(AssessmentProver.polynomialEquality("x>=0".asFormula, "x+0*5>=2-4*1/2".asFormula, normalize = true)) {
      case p =>
        p.conclusion shouldBe "==> x=x+0*5-(2-4*1/2) & 0=0".asSequent
        p shouldBe Symbol("proved")
    }
    inside(AssessmentProver.polynomialEquality("x>=0".asFormula, "-(x+0*5)<=-(2-4*1/2)".asFormula, normalize = true)) {
      case p =>
        p.conclusion shouldBe "==> x=-(2-4*1/2)--(x+0*5) & 0=0".asSequent
        p shouldBe Symbol("proved")
    }
    inside(
      AssessmentProver
        .polynomialEquality("x>=0 & y=2".asFormula, "!(!-(x+0*5)<=-(2-4*1/2) | y!=2)".asFormula, normalize = true)
    ) { case p =>
      p.conclusion shouldBe "==> x=-(2-4*1/2)--(x+0*5) & 0=0 & y-2=y-2 & 0=0".asSequent
      p shouldBe Symbol("proved")
    }
    the[IllegalArgumentException] thrownBy AssessmentProver
      .polynomialEquality("x>=0".asFormula, "-(x+0*5) < -(2-4*1/2)".asFormula, normalize = true) should have message
      "requirement failed: Formula operators do not match at position '.'; expected x>=0 (GreaterEqual) but got -(2-4*1/2)--(x+0*5)>0 (Greater)"
  }

  it should "return useful error messages" in withZ3 { _ =>
    // expected single expression, ok to answer with a list of duplicate elements
    AskGrader(Some(Modes.POLY_EQ), Map.empty, ExpressionArtifact("-3"))
      .check(ListExpressionArtifact(List("-3".asTerm, "-3".asTerm)))
      .left
      .value shouldBe Symbol("proved")
    // expected single expression, not ok to answer with a list
    AskGrader(Some(Modes.POLY_EQ), Map.empty, ExpressionArtifact("-3"))
      .check(ListExpressionArtifact(List("-1".asTerm, "-3".asTerm))) shouldBe Right(
      """Expected a Term but got Term,Term:
        |  (-1): Term
        |  (-3): Term""".stripMargin
    )
    // expected list of expression that happens to be one element (make it a list by duplicating element),
    // ok to answer with a single expression
    AskGrader(Some(Modes.POLY_EQ), Map.empty, ListExpressionArtifact(List("-3".asTerm, "-3".asTerm)))
      .check(ExpressionArtifact("-3"))
      .left
      .value shouldBe Symbol("proved")
    // expected list of expressions, ok to answer with a list
    AskGrader(Some(Modes.POLY_EQ), Map.empty, ListExpressionArtifact(List("-3".asTerm, "-3".asTerm)))
      .check(ListExpressionArtifact(List("-1".asTerm, "-3".asTerm)))
      .toOption
      .value shouldBe "" // wrong but syntactically ok
  }

  "Value equality" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.valueEquality("1".asTerm, "1".asTerm) shouldBe Symbol("proved")
    AssessmentProver
      .valueEquality("1".asTerm :: "2".asTerm :: Nil, "1+0".asTerm :: "4-2".asTerm :: Nil) shouldBe Symbol("proved")
    AssessmentProver.valueEquality("1".asTerm, "2".asTerm) shouldNot be(Symbol("proved"))
    AssessmentProver.valueEquality("1".asTerm :: "1".asTerm :: Nil, "2-1".asTerm :: "2-2".asTerm :: Nil) shouldNot be(
      Symbol("proved")
    )
  }

  "DI result check" should "prove simple DI examples" in withZ3 { _ =>
    AssessmentProver.dIPremiseCheck(
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'=0".asSequent,
      diffAssignsMandatory = true,
      normalize = false,
    ) shouldBe Symbol("proved")
    AssessmentProver.dIPremiseCheck(
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
      "==> [w':=-v;][v':=w;]2*v*v'+2*w*w'=0".asSequent,
      diffAssignsMandatory = true,
      normalize = false,
    ) shouldBe Symbol("proved")
    AssessmentProver.dIPremiseCheck(
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
      "==> [w':=-v;v':=w;]2*v*v'+2*w*w'=0".asSequent,
      diffAssignsMandatory = true,
      normalize = false,
    ) shouldBe Symbol("proved")
    the[IllegalArgumentException] thrownBy
      AssessmentProver.dIPremiseCheck(
        "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
        "==> 2*v*w+2*w*v=0".asSequent,
        diffAssignsMandatory = true,
        normalize = false,
      ) should
      have message "requirement failed: Differential assignments do not match: expected assignments to v',w' but found none"
    the[IllegalArgumentException] thrownBy
      AssessmentProver.dIPremiseCheck(
        "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
        "==> [v':=w;][w':=-v;]2*v*w<=2*w*v".asSequent,
        diffAssignsMandatory = true,
        normalize = false,
      ) should
      have message "requirement failed: Formula operators do not match at position '.1'; expected 2*v*w+2*w*(-v)-0=0 (Equal) but got 2*v*w<=2*w*v (LessEqual)"
  }

  it should "allow (partially) executed differential assignments on request" in withZ3 { _ =>
    AssessmentProver.dIPremiseCheck(
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
      "==> [w':=-v;]2*v*w+2*w*w'=0".asSequent,
      diffAssignsMandatory = false,
      normalize = false,
    ) shouldBe Symbol("proved")
    AssessmentProver.dIPremiseCheck(
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
      "==> 2*v*w-2*w*v=0".asSequent,
      diffAssignsMandatory = false,
      normalize = false,
    ) shouldBe Symbol("proved")
    the[TacticInapplicableFailure] thrownBy AssessmentProver.dIPremiseCheck(
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
      "==> 2*v*w=2*w*v".asSequent,
      diffAssignsMandatory = false,
      normalize = false,
    ) should
      have message "Terms not equal (by equating coefficients): 2*v*w+2*w*(-v)-0, 2*v*w"
    the[TacticInapplicableFailure] thrownBy
      AssessmentProver.dIPremiseCheck(
        "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
        "==> 2*v*w+2*w*v=0".asSequent,
        diffAssignsMandatory = false,
        normalize = false,
      ) should
      have message "Terms not equal (by equating coefficients): 2*v*w+2*w*(-v)-0, 2*v*w+2*w*v"
    the[IllegalArgumentException] thrownBy
      AssessmentProver.dIPremiseCheck(
        "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
        "==> 2*v*w<=2*w*v".asSequent,
        diffAssignsMandatory = false,
        normalize = false,
      ) should
      have message "requirement failed: Formula operators do not match at position '.1'; expected 2*v*w+2*w*(-v)-0=0 (Equal) but got 2*v*w<=2*w*v (LessEqual)"
    the[IllegalArgumentException] thrownBy
      AssessmentProver.dIPremiseCheck(
        "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
        "==> 2*v*w<=2*w*v & 0=0".asSequent,
        diffAssignsMandatory = false,
        normalize = false,
      ) should
      have message "requirement failed: Formula operators do not match at position '.1'; expected 2*v*w+2*w*(-v)-0=0 (Equal) but got 2*v*w<=2*w*v&0=0 (And)"
  }

  it should "normalize" in withZ3 { _ =>
    AssessmentProver.dIPremiseCheck(
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
      "==> [v':=w;][w':=-v;]2*v*w=2*w*v".asSequent,
      diffAssignsMandatory = true,
      normalize = true,
    ) shouldBe Symbol("proved")
    AssessmentProver.dIPremiseCheck(
      "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent,
      "==> 2*v*w=2*w*v".asSequent,
      diffAssignsMandatory = false,
      normalize = true,
    ) shouldBe Symbol("proved")
  }

  "QE equivalence" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.qe("x>=0".asFormula, "0<=x".asFormula, Equiv)
    AssessmentProver.qe("x>=4".asFormula, "x>=0 & x^2>=16".asFormula, Equiv) shouldBe Symbol("proved")
    AssessmentProver.qe("x=1".asFormula, "x^2>=1 & x^2<=x".asFormula, Equiv) shouldBe Symbol("proved")
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      AssessmentProver.qe("x>=4".asFormula, "abs(x)>=4 & abs(x)<=x".asFormula, Equiv) shouldBe Symbol("proved")
    }
    AssessmentProver.qe("x>=4".asFormula, "\\forall y (0<=y&y<=4 -> x>=y)".asFormula, Equiv) shouldBe Symbol("proved")
    AssessmentProver.qe("x>=4".asFormula, "\\exists y (y>=2 & x>=y^2)".asFormula, Equiv) shouldBe Symbol("proved")
  }

  "Syntactic sequent equality" should "prove simple examples" in {
    AssessmentProver
      .syntacticEquality(List("x>0 ==> x>=0".asSequent), List("x>0 ==> x>=0".asSequent)) shouldBe Symbol("proved")
    AssessmentProver
      .syntacticEquality(List("x>0,y>0 ==> x>=0".asSequent), List("y>0,x>0 ==> x>=0".asSequent)) shouldBe Symbol(
      "proved"
    )
    AssessmentProver
      .syntacticEquality(List("x>0 ==> x>=0,y>0".asSequent), List("x>0 ==> y>0,x>=0".asSequent)) shouldBe Symbol(
      "proved"
    )
    AssessmentProver.syntacticEquality(
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent),
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent),
    ) shouldBe Symbol("proved")
    AssessmentProver.syntacticEquality(
      List("y>0 ==> y>=0".asSequent, "x>0 ==> x>=0".asSequent),
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent),
    ) shouldBe Symbol("proved")
    the[InapplicableUnificationKeyFailure] thrownBy AssessmentProver.syntacticEquality(
      List("y>0 ==> y>=0".asSequent, "x>0 ==> x>=0".asSequent, "z>0 ==> z>0".asSequent),
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent, "y>0 ==> y>0".asSequent),
    ) should have message
      """Axiom equivReflexive p_()<->p_() cannot be applied: The shape of
        |  expression               (x>0->x>=0)&(y>0->y>=0)&(z>0->z>0)<->(x>0->x>=0)&(y>0->y>0)&(y>0->y>=0)
        |  does not match axiom key p_()<->p_()""".stripMargin
    the[IllegalArgumentException] thrownBy AssessmentProver.syntacticEquality(
      List("y>0 ==> y>=0".asSequent, "x>0 ==> x>=0".asSequent),
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent, "y>0 ==> y>0".asSequent),
    ) should have message
      "requirement failed: Cannot check empty lists of sequents or sequent lists of different size"
  }

  it should "not reply with a syntax error on n/a" in withZ3 { _ =>
    AskGrader(Some(Modes.SYN_EQ), Map.empty, SequentArtifact(List("x>0 ==> [x:=x+1;]x>1".asSequent)))
      .check(ExpressionArtifact("n/a")) shouldBe Right("Incorrect n/a")
  }

  it should "not reply with a syntax error on expected n/a" in withZ3 { _ =>
    AskGrader(Some(Modes.SYN_EQ), Map.empty, ExpressionArtifact("n/a"))
      .check(SubstitutionArtifact(List("f() ~> 5".asSubstitutionPair))) shouldBe Right("Incorrect (f()~>5)")
  }

  "Differential invariant checker" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver
      .dICheck(ODESystem("{x'=1,y'=2}".asDifferentialProgram), "2*x=y".asFormula) shouldBe Symbol("proved")
    AssessmentProver
      .dICheck(ODESystem("{x'=x,y'=-y}".asDifferentialProgram), "x*y=1".asFormula) shouldBe Symbol("proved")
    AssessmentProver
      .dICheck(ODESystem("{x'=-y,y'=x}".asDifferentialProgram), "x^2+y^2=1".asFormula) shouldBe Symbol("proved")
    AssessmentProver
      .dICheck(ODESystem("{x'=1,y'=2}".asDifferentialProgram), "3*x=y".asFormula)
      .subgoals
      .loneElement shouldBe "3*x=y, true ==> 3*1=2".asSequent
  }

  "Generic prove checker" should "prove simple examples" in withZ3 { _ =>
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map("tactic" -> "chase(1);prop"),
      ExpressionArtifact("A() -> [prg;]B()"),
    ).check(ExpressionArtifact("A()->[prg;]B()")).left.value shouldBe Symbol("proved")
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map("tactic" -> "chase(1);prop"),
      SequentArtifact("A() ==> [prg;]B()".asSequent :: Nil),
    ).check(SequentArtifact("==> A() -> [prg;]B()".asSequent :: Nil)).left.value shouldBe Symbol("proved")
    val p = AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map("tactic" -> "chase(1);prop"),
      SequentArtifact("==> A() -> [prg;]B()".asSequent :: "[sys;]C() ==> ".asSequent :: Nil),
    ).check(SequentArtifact("A() ==> [prg;]B()".asSequent :: "==> [sys;]C() -> false&x=4".asSequent :: Nil))
    p.left
      .value
      .conclusion shouldBe "==> ((A() -> [prg;]B()) <-> (true -> A() -> [prg;]B())) & ((true -> [sys;]C() -> false&x=4) <-> ([sys;]C() -> false))"
      .asSequent
    p.left.value shouldBe Symbol("proved")
  }

  it should "prove optional question with solution as loop tactic input" in withZ3 { _ =>
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map("question" -> "x>2 & y>=1 -> [{x:=x+y;y:=y+2;}*]x>1", "tactic" -> "implyR(1);loop({`\\%1`},1);auto;done"),
      ExpressionArtifact("false"),
    ). // @note ignored because question will be used instead
      check(ExpressionArtifact("x>1&y>=0"))
      .left
      .value shouldBe Symbol("proved")
  }

  it should "prove optional question with a list of diffcuts" in withZ3 { _ =>
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map(
        "question" -> "x>=3 & v>=2 & a>=1 & j>=0 -> [{x'=v,v'=a,a'=j}]x>=3",
        "tactic" -> "implyR(1); for \\%i do dC({`\\%i`},1); <(nil, dI(1); done) endfor; dW(1); QE; done",
      ),
      ExpressionArtifact("false"),
    ). // @note ignored because question will be used instead
      check(ListExpressionArtifact("a>=1".asFormula :: "v>=2".asFormula :: "x>=3".asFormula :: Nil))
      .left
      .value shouldBe Symbol("proved")
  }

  it should "prove optional question with solution as uniform substitution tactic input" in withZ3 { _ =>
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map(
        "question" -> "x<=m & V>=0 -> [{{v:=0; ++ ?Q(m,t,x,T,V);v:=V;};{x'=v,t'=1 & t<=T}}*]x<=m",
        "tactic" -> "US({`Q(m,t,x,T,V) ~> \\%1`});implyR(1);loop({`x<=m`},1);auto;done",
      ),
      ExpressionArtifact("false"), // @note ignored because question will be used instead
    ).check(ExpressionArtifact("x<=m-V*(T-t)")).left.value shouldBe Symbol("proved")
  }

  it should "reply with expected answer type to wrong answer format" in {
    AskGrader(Some(AskGrader.Modes.SYN_EQ), Map.empty, ExpressionArtifact("x>0"))
      .check(SequentArtifact("==> x>0".asSequent :: Nil))
      .toOption
      .value shouldBe "Expected a Formula but got Sequent:\n==> 1:  x>0\tGreater"
  }

  it should "give correct feedback on model conditions" in {
    AskGrader(
      Some(AskGrader.Modes.TEST_MODEL),
      Map("precondition" -> "x>0 & y>0", "postcondition" -> "x>0 & y>0"),
      ListExpressionArtifact(List("x>0".asFormula, "x>0 & y>0 & z>0".asFormula)),
    ).check(ListExpressionArtifact(List("x>0".asFormula, "x>0 & y>0 & z>0".asFormula))).toOption.value shouldBe (
      AssessmentProver.Messages.OK
    )
  }

  "Program equivalence" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.prgEquivalence("a;b;c;".asProgram, "{a;b;};c;".asProgram) shouldBe Symbol("proved")
    AssessmentProver.prgEquivalence("a;++b;++c;".asProgram, "{a;++b;}++c;".asProgram) shouldBe Symbol("proved")
    AssessmentProver
      .prgEquivalence("{a;++b;}{c;++d;++e;}".asProgram, "{a;++b;}{{c;++d;}++e;}".asProgram) shouldBe Symbol("proved")
    AssessmentProver.prgEquivalence("x:=2;++y:=3;".asProgram, "y:=4-1;++z:=2;x:=z;".asProgram) shouldBe Symbol("proved")
  }

  "Formula implication" should "succeed for simple examples" in withZ3 { _ =>
    AssessmentProver.formulaImplication("a=0".asFormula, "a=0".asFormula) shouldBe Symbol("proved")
    AssessmentProver.formulaImplication("a=0 & b=0".asFormula, "a=0".asFormula) shouldBe Symbol("proved")
    AssessmentProver.formulaImplication("x>=0 & a=1".asFormula, "x>0 | a=1".asFormula) shouldBe Symbol("proved")
  }

//  "Formula implication" should "not prove false implications" in withZ3 { _ =>
//    AssessmentProver.formulaImplication("x>=0 | a=1".asFormula, "x>0 & a=1".asFormula) shouldNot be ('proved)
//  }

  it should "prove simple system loops" in withZ3 { _ =>
    AssessmentProver
      .prgEquivalence("{a{|^@|};++b{|^@|};}*".asProgram, "{b{|^@|};++a{|^@|};}*".asProgram) shouldBe Symbol("proved")
  }

  it should "elaborate to system loops when dual does not occur literally" in withZ3 { _ =>
    AssessmentProver.prgEquivalence("{a;++b;}*".asProgram, "{b;++a;}*".asProgram) shouldBe Symbol("proved")
  }

  "Explanation check" should "accept long enough answers" in {
    AskGrader(Some(AskGrader.Modes.EXPLANATION_CHECK), Map.empty, TextArtifact(Some("An acceptable answer")))
      .check(TextArtifact(Some("An elaborate answer")))
      .left
      .value
      .conclusion shouldBe "==> explanation&full<->explanation&full".asSequent
  }

  it should "accept long enough answers with line breaks" in {
    AskGrader(Some(AskGrader.Modes.EXPLANATION_CHECK), Map.empty, TextArtifact(Some("An acceptable answer")))
      .check(TextArtifact(Some("A\n good\n answer\n with line\n breaks")))
      .left
      .value
      .conclusion shouldBe "==> explanation&full<->explanation&full".asSequent
  }

  it should "not accept too short answers" in {
    AskGrader(Some(AskGrader.Modes.EXPLANATION_CHECK), Map.empty, TextArtifact(Some("An acceptable answer")))
      .check(TextArtifact(Some("Short")))
      .toOption
      .value shouldBe "Please elaborate your explanation"
  }

  it should "partially accept medium answers" in {
    AskGrader(
      Some(AskGrader.Modes.EXPLANATION_CHECK),
      Map.empty,
      TextArtifact(Some("An acceptable answer that requires a little more words")),
    ).check(TextArtifact(Some("Medium short"))).left.value.conclusion shouldBe "==> explanation&min<->explanation&min"
      .asSequent
  }

  "Substitution parser" should "adjust positions in exceptions" in {
    the[ParseException] thrownBy SubstitutionParser.parseSubstitutionPairs("c() ~> 5**4") should have message
      """1:10 Unexpected token cannot be parsed
        |Found:    * at 1:10
        |Expected: <BeginningOfTerm>""".stripMargin

    the[ParseException] thrownBy SubstitutionParser.parseSubstitutionPairs("c() ~> 5 , d() ~> *4") should have message
      """1:19 Unexpected token cannot be parsed
        |Found:    * at 1:19
        |Expected: <BeginningOfExpression>""".stripMargin

    the[ParseException] thrownBy SubstitutionParser
      .parseSubstitutionPairs("c() ~> 5, d() ~> 4    ,   e() ~> *3") should have message
      """1:34 Unexpected token cannot be parsed
        |Found:    * at 1:34
        |Expected: <BeginningOfExpression>""".stripMargin

    the[ParseException] thrownBy SubstitutionParser
      .parseSubstitutionPairs(" ( c() ~> 5, (d() ~> 4  )  ,   e() ~> *3)") should have message
      """1:39 Unexpected token cannot be parsed
        |Found:    * at 1:39
        |Expected: <BeginningOfExpression>""".stripMargin

    the[ParseException] thrownBy SubstitutionParser.parseSubstitutionPairs("x+y ~> 5+4") should have message
      """1:1 Non-substitutable expression on left-hand side of ~>
        |Found:    x+y  at 1:1
        |Expected: substitutable expression (e.g., predicate, function, program constant)""".stripMargin

    the[ParseException] thrownBy SubstitutionParser
      .parseSubstitutionPairs("c() ~> x^2, x+y ~> 5+4, p(||) ~> x=y") should have message
      """1:13 Non-substitutable expression on left-hand side of ~>
        |Found:    x+y  at 1:13
        |Expected: substitutable expression (e.g., predicate, function, program constant)""".stripMargin
  }

  it should "parse typical examples" in {
    SubstitutionParser.parseSubstitutionPairs("a~>{x'=v}, b~>{v:=-c*v;}, p(||)~>2*g*x<=2*g*H-v^2") should
      contain theSameElementsAs List(
        SubstitutionPair(ProgramConst("a"), ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Variable("v")))),
        SubstitutionPair(ProgramConst("b"), Assign(Variable("v"), Neg(Times(Variable("c"), Variable("v"))))),
        SubstitutionPair(UnitPredicational("p", AnyArg), "2*g*x<=2*g*H-v^2".asFormula),
      )
    SubstitutionParser
      .parseSubstitutionPairs("(a~>{x'=v}, b~>{v:=-c*v;}, p(||)~>2*g*x<=2*g*H-v^2)") shouldBe SubstitutionParser
      .parseSubstitutionPairs("a~>{x'=v}, b~>{v:=-c*v;}, p(||)~>2*g*x<=2*g*H-v^2")
    SubstitutionParser.parseSubstitutionPairs("p~>v^2<=2*x, a~>{x'=v}") should
      contain theSameElementsAs List(
        SubstitutionPair(PredOf(Function("p", None, Unit, Bool), Nothing), "v^2<=2*x".asFormula),
        SubstitutionPair(ProgramConst("a"), ODESystem(AtomicODE(DifferentialSymbol(Variable("x")), Variable("v")))),
      )
    SubstitutionParser.parseSubstitutionPairs("(c() ~> x+y, p(.) ~> [z:=.;{z:=z-.;}*].-1>=0)") should
      contain theSameElementsAs List(
        SubstitutionPair(FuncOf(Function("c", None, Unit, Real), Nothing), Plus(Variable("x"), Variable("y"))),
        SubstitutionPair(
          PredOf(Function("p", None, Real, Bool), DotTerm()),
          Box(
            Compose(Assign(Variable("z"), DotTerm()), Loop(Assign(Variable("z"), Minus(Variable("z"), DotTerm())))),
            GreaterEqual(Minus(DotTerm(), Number(1)), Number(0)),
          ),
        ),
      )
  }

  "Grading" should "not give points for \\anychoice when no answer was selected" in withZ3 { _ =>
    val problems = (2 to 16).flatMap(i => extractProblems(QUIZ_PATH + "/" + i + "/main.tex"))
    val anyChoiceProblems = problems
      .map(p => p.copy(questions = p.questions.filter(_.isInstanceOf[AnyChoiceQuestion])))
      .toList
    val graders = anyChoiceProblems.flatMap(p => p.questions.map(toGrader)).map(_._1)
    forEvery(Table("Grader", graders: _*)) {
      _.check(ChoiceArtifact(Nil)).toOption.value shouldBe AssessmentProver.Messages.BLANK
    }
  }

  it should "not give points for \\onechoice when no answer was selected" in withZ3 { _ =>
    val problems = (2 to 16).flatMap(i => extractProblems(QUIZ_PATH + "/" + i + "/main.tex"))
    val oneChoiceProblems = problems
      .map(p => p.copy(questions = p.questions.filter(_.isInstanceOf[OneChoiceQuestion])))
      .toList
    val graders = oneChoiceProblems.flatMap(p => p.questions.map(toGrader)).map(_._1)
    forEvery(Table("Grader", graders: _*)) {
      _.check(ChoiceArtifact(Nil)).toOption.value shouldBe AssessmentProver.Messages.BLANK
    }
  }

  it should "not give points for \\asktf when no answer was selected" in withZ3 { _ =>
    val problems = (2 to 16).flatMap(i => extractProblems(QUIZ_PATH + "/" + i + "/main.tex"))
    val asktfProblems = problems.map(p => p.copy(questions = p.questions.filter(_.isInstanceOf[AskTFQuestion]))).toList
    val graders = asktfProblems.flatMap(p => p.questions.map(toGrader)).map(_._1)
    forEvery(Table("Grader", graders: _*)) {
      _.check(BoolArtifact(None)).toOption.value shouldBe AssessmentProver.Messages.BLANK
    }
  }

  it should "not give points for \\ask when answer is empty" in withZ3 { _ =>
    val problems = (2 to 16).flatMap(i => extractProblems(QUIZ_PATH + "/" + i + "/main.tex"))
    val askProblems = problems.map(p => p.copy(questions = p.questions.filter(_.isInstanceOf[AskQuestion]))).toList
    val graders = askProblems.flatMap(p => p.questions.map(toGrader)).map(_._1)
    forEvery(Table("Grader", graders.drop(42): _*)) { g =>
      g.expected match {
        case TextArtifact(None) =>
          g.check(TextArtifact(None)).left.value.conclusion shouldBe "==>  explanation()&full()<->explanation()&full()"
            .asSequent
        case TextArtifact(Some("")) =>
          g.check(TextArtifact(None)).left.value.conclusion shouldBe "==>  explanation()&full()<->explanation()&full()"
            .asSequent
        case _ => g.check(TextArtifact(None)).toOption.value shouldBe AssessmentProver.Messages.BLANK
      }
    }
    forEvery(Table("Grader", graders: _*)) { g =>
      g.expected match {
        case TextArtifact(None) => g
            .check(TextArtifact(Some("")))
            .left
            .value
            .conclusion shouldBe "==>  explanation()&full()<->explanation()&full()".asSequent
        case TextArtifact(Some("")) => g
            .check(TextArtifact(Some("")))
            .left
            .value
            .conclusion shouldBe "==>  explanation()&full()<->explanation()&full()".asSequent
        case _ => g.check(TextArtifact(Some(""))).toOption.value shouldBe AssessmentProver.Messages.BLANK
      }
    }
    forEvery(Table("Grader", graders: _*)) { g =>
      g.expected match {
        case TextArtifact(None) => g
            .check(TextArtifact(Some("   \n  \t  ")))
            .left
            .value
            .conclusion shouldBe "==>  explanation()&full()<->explanation()&full()".asSequent
        case TextArtifact(Some("")) => g
            .check(TextArtifact(Some("\n  \t\n")))
            .left
            .value
            .conclusion shouldBe "==>  explanation()&full()<->explanation()&full()".asSequent
        case _ => g.check(TextArtifact(Some(""))).toOption.value shouldBe AssessmentProver.Messages.BLANK
      }
    }
  }

  "Quiz checking" should "prove quiz 2" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/2/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Solve ODEs", 5) :: ("Vector field examples", 4) :: ("Semantics of terms", 2) ::
      ("Semantics of formulas", 5) :: ("Formulas as evolution domain constraints", 4) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 12
    nosols shouldBe 10
    run(problems)
  }

  it should "prove quiz 3" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/3/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Programs vs. formulas vs. terms", 10) :: ("Misplaced parentheses", 6) ::
      ("Reachable sets", 5) :: ("Program shapes", 8) :: ("Modeling pitfalls", 4) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 10
    nosols shouldBe 16
    run(problems)
  }

  it should "prove quiz 4" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/4/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Valid formulas", 10) :: ("Truth identification", 7) :: ("Multiple pre/postconditions", 4) ::
      ("Direct velocity control", 2) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 12
    nosols shouldBe 18
    run(problems)
  }

  it should "prove quiz 5" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/5/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Axiom application", 10) :: ("Axiom identification: Top", 6) :: ("Axiom identification: All", 6) ::
      ("Distributivity and non-distributivity", 10) :: ("If-then-else", 2) :: ("Nondeterministic assignments", 2) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 19
    nosols shouldBe 21
    run(problems)
  }

  it should "prove quiz 6" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/6/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Rule application", 10) :: ("Rule identification", 8) :: ("Arithmetic simplification", 6) ::
      ("Proof rule criticism", 10) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 14
    nosols shouldBe 26
    run(problems)
  }

  it should "prove quiz 7" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/7/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Loop invariants", 5) :: ("Other loop rules", 8) ::
      ("Incremental design in direct velocity control", 5) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 2
    nosols shouldBe 5
    run(problems)
  }

  it should "prove quiz 8" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/8/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Revisiting ping-pong events", 4) :: ("Faithful event models", 6) ::
      ("Identify event invariants", 3) :: ("Incremental design in velocity event control", 5) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 0
    nosols shouldBe 0
    run(problems)
  }

  it should "prove quiz 9" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/9/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Comparing event-triggered versus time-triggered controllers", 4) :: ("Reaction times", 2) ::
      ("From event responses to reaction times", 5) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 0
    nosols shouldBe 0
    run(problems)
  }

  it should "prove quiz 10" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/10/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Differential invariance", 10) :: ("Identify differential invariants", 5) ::
      ("Differential invariant rules", 10) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 14
    nosols shouldBe 9
    run(problems)
  }

  it should "prove quiz 11" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/11/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Explain differential cuts", 8) :: ("Identify differential invariants to cut", 10) ::
      ("Differential invariance rules", 14) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 7
    nosols shouldBe 1
    run(problems)
  }

  it should "prove quiz 12" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/12/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Using differential ghosts", 3) :: ("Differential ghost construction", 8) ::
      ("Parachute", 3) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 11
    nosols shouldBe 8
    run(problems)
  }

  it should "prove quiz 13" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/13/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Provability with differential invariants", 3) :: ("Differential invariant reduction", 5) ::
      ("Differential invariant search", 2) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 5
    nosols shouldBe 15
    run(problems)
  }

  it should "prove quiz 14" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/14/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Player count", 5) :: ("Strategically reachable minima", 6) :: ("Game shapes", 2) ::
      ("Truth identification", 10) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 11
    nosols shouldBe 28
    run(problems)
  }

  it should "prove quiz 15" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/15/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Semantic comparisons", 4) :: ("Game region shapes", 6) :: ("Game loop semantics", 5) ::
      ("Direct velocity control", 2) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 11
    nosols shouldBe 15
    run(problems)
  }

  it should "prove quiz 16" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/16/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Truth identification", 5) :: ("Axiom or not?", 10) :: ("Demon's controls", 5) ::
      ("Robot simple chase game", 2) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 10
    nosols shouldBe 6
    run(problems)
  }

  it should "prove quiz 17" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/17/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Comparing systems versus games", 4) :: ("Loop variant identification", 3) :: ("Other loop variant rules", 8) ::
      ("Complete diamond loop game proofs", 3) :: ("Completeness questions", 4) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 21
    nosols shouldBe 6
    run(problems)
  }

  it should "prove quiz 18" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/18/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Uniform substitution application", 13) :: ("Finding uniform substitutions", 8) :: (
        "Axiom for axiom schema",
        4,
      ) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 1
    nosols shouldBe 0
    run(problems)
  }

  it should "prove quiz 19" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/19/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Check the monitor quality", 8) :: ("Controller monitor for runaround robot", 2) ::
      ("Monitors for velocity controlled car", 4) :: ("Controller monitor for event-triggered ping-pong ball", 2) ::
      ("Controller monitor for time-triggered ping-pong", 2) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 24
    nosols shouldBe 8
    run(problems)

    // @note for debugging the partial points computation: particularly bad partial solution that doesn't earn points
    runGrader(
      createSubmission(problems.filter(_.name.contains("Monitors for velocity controlled car")), "", rand, Some("true"))
        ._1
    )
    // not a solution
    runGrader(
      createSubmission(
        problems.filter(_.name.contains("Monitors for velocity controlled car")),
        "",
        rand,
        Some("false"),
      )._1
    )
  }

  it should "prove quiz 20" in withZ3 { _ =>
    // most questions flagged INSPECT, those need Mathematica
    val problems = extractProblems(QUIZ_PATH + "/20/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Substitution of linear equations", 7) :: ("Square root arithmetic", 3) :: ("Eliminate quantifiers", 6) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 15
    nosols shouldBe 16
    run(problems)
  }

  it should "prove quiz 21" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/21/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Virtual substitution with real tradeoffs", 1) :: ("Infinity and infinitesimal virtual substitution", 2) ::
      ("Eliminate quantifiers", 10) :: Nil
    val (sols, testsols, nosols) = solCounts(problems)
    sols shouldBe problems.map(_.questions.size).sum
    testsols shouldBe 3
    nosols shouldBe 5
    run(problems)
  }

  "Submission extraction" should "extract answers in the order listed in the file" in {
    val s = Source
      .fromInputStream(getClass.getResourceAsStream("/edu/cmu/cs/ls/keymaerax/cli/submission.json"))
      .mkString
    import Submission.SubmissionJsonFormat._
    s.parseJson.convertTo[Submission.Chapter] shouldBe Submission.Chapter(
      -1,
      "",
      List(
        Submission.Problem(
          25053,
          1,
          "2",
          "Problem block 1 (2 questions)",
          "prob::1",
          3.0,
          List(
            Submission.SinglePrompt(
              141,
              1,
              "a",
              "\\ask",
              2.0,
              List(Submission.TextAnswer(
                142,
                "prt-sol::1::a1",
                "\\sol",
                Some(Submission.GraderCookie(500, "\\algog", "valueeq()")),
                "3",
                """\kyxline"2"""",
              )),
            ),
            Submission.SinglePrompt(
              143,
              2,
              "b",
              "\\ask",
              1.0,
              List(Submission.TextAnswer(
                144,
                "prt-sol::2::a1",
                "\\sol",
                Some(Submission.GraderCookie(501, "\\algog", "polyeq()")),
                "x^2>=+0",
                """\kyxline"x^2>=0"""",
              )),
            ),
          ),
        ),
        Submission.Problem(
          25160,
          3,
          "-1",
          "Problem block 3 (single question)",
          "prob::3",
          1.0,
          List(Submission.SinglePrompt(
            147,
            1,
            "a",
            "\\ask",
            1.0,
            List(Submission.TextAnswer(148, "prt::block3::a1", "\\sol", None, "1,2", """${1,2,3}$""")),
          )),
        ),
        Submission.Problem(
          25057,
          1,
          "5",
          "Problem block in second segment",
          "prob::4",
          1.0,
          List(Submission.SinglePrompt(
            149,
            1,
            "a",
            "\\onechoice",
            1.0,
            List(
              Submission.ChoiceAnswer(150, "prt::seg2block::a1", "\\choice*", None, "Sound", isSelected = true),
              Submission.ChoiceAnswer(151, "prt::seg2block::a2", "\\choice", None, "Unsound", isSelected = false),
            ),
          )),
        ),
      ),
    )
  }

  "Command line grader" should "grade random quiz 2 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/2/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qdiffeq") }
  }

  it should "grade random quiz 3 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/3/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qchoicecontrol") }
  }

  it should "grade random quiz 4 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/4/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qcontracts") }
  }

  it should "grade random quiz 5 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/5/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qdynax") }
  }

  it should "grade random quiz 6 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/6/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qtruth") }
  }

  it should "grade random quiz 7 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/7/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qloops") }
  }

  it should "grade random quiz 8 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/8/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qevents") }
  }

  it should "grade random quiz 9 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/9/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qtime") }
  }

  it should "grade random quiz 10 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/10/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qdiffinv") }
  }

  it should "grade random quiz 11 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/11/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qdiffcut") }
  }

  it should "grade random quiz 12 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/12/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qdiffghost") }
  }

  it should "grade random quiz 13 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/13/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qdiffchart") }
  }

  it should "grade random quiz 14 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/14/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qHgames") }
  }

  it should "grade random quiz 15 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/15/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qwinning") }
  }

  it should "grade random quiz 16 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/16/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qgameproofs") }
  }

  it should "grade random quiz 17 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/17/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qaxiomaticgames") }
  }

  it should "grade random quiz 18 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/18/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qusubst") }
  }

  it should "grade random quiz 19 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/19/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qmodelplex") }
  }

  it should "grade random quiz 20 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/20/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qvirteq") }
  }

  it should "grade random quiz 21 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/21/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qvirtreal") }
  }

  it should "handle empty text answers" in withZ3 { _ =>
    val problems = (2 to 16).flatMap(i => extractProblems(QUIZ_PATH + "/" + i + "/main.tex")).toList
    runGrader(problems, 0, "", Some("", true), 0.0)
  }

  it should "handle n/a text answers" in withZ3 { _ =>
    val problems = (2 to 16).flatMap(i => extractProblems(QUIZ_PATH + "/" + i + "/main.tex")).toList
    runGrader(problems, 0, "", Some("n/a", true))
  }

  it should "handle non-parseable text answers" in withZ3 { _ =>
    val problems = (2 to 16).flatMap(i => extractProblems(QUIZ_PATH + "/" + i + "/main.tex")).toList
    runGrader(problems, 0, "", Some("x*v+", false), 0.0)
  }

  it should "run all quizzes" in {
    val quizzes = (1 to 21).map(QUIZ_PATH + "/" + _ + "/main.tex")
    val allProblems = quizzes.map(extractProblems)
    val tic = System.nanoTime()
    allProblems
      .zipWithIndex
      .foreach({ case (problems, i) =>
        val tic = System.nanoTime()
        // DerivationInfoRegistry.init(true)
        Thread.sleep(4000) // emulate derivation info registry initialization
        beforeAll()
        beforeEach()
        withZ3 { _ =>
          val (submission, _) = createSubmission(problems, "", rand, None)
          runGrader(submission)
        }
        afterEach()
        afterAll()
        // DerivationInfo.empty() // force re-initalizing like during startup
        val toc = System.nanoTime()
        println("Quiz " + (i + 2) + " duration: " + (toc - tic) / 1000000L + "ms")
      })
    val toc = System.nanoTime()
    println("Total duration: " + (toc - tic) / 1000000L + "ms")
  }

  "Lab Command Line" should "grade random lab 0 submissions" in withZ3 { _ =>
    val problems = extractProblems(LAB_PATH + "/0/main.tex")
    // can't check score because lab 0 problems don't have titles in main.tex to identify them
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "lab:0", checkScore = false) }
  }

  /**
   * Runs the autograder on the `i`th random submission (list of `problems`), unless `uniformAnswer` (text+whether
   * parseable) is provided; uses `chapterLabel` to look up the grading information currently missing from problems.
   */
  private def runGrader(
      problems: List[Problem],
      i: Int,
      chapterLabel: String,
      uniformAnswer: Option[(String, Boolean)] = None,
      expectedFailScore: Double = 0.0,
      checkScore: Boolean = true,
  ): Unit = {
    val randClue = "Submission produced in " + i + "th run of " + RANDOM_TRIALS + " random trials from seed " + rand
      .seed
    val (submission, expected) = createSubmission(problems, chapterLabel, rand, uniformAnswer.map(_._1))
    val (resultsString, msgLines) = runGrader(submission)

    val parseFailed = """.*?\((?<id>\d+)\)\.\.\.PARSE ERROR""".r
    val graded = """.*?\((?<id>\d+)\)\.\.\.(?:(?:PASS)|(?:FAILED)|(?:BLANK)|(?:INSPECT)|(?:SKIPPED))""".r

    def checkGradedLines(gradedLines: List[String], expectPass: Boolean) = {
      gradedLines.loneElement.split("""\.\.\.""")(1) should (if (expectPass)
                                                               startWith(AssessmentProver.Messages.PASS) or
                                                                 startWith(AssessmentProver.Messages.SKIPPED) or
                                                                 startWith(AssessmentProver.Messages.INSPECT)
                                                             else startWith(AssessmentProver.Messages.FAILED) or
                                                               startWith(AssessmentProver.Messages.BLANK) or
                                                               startWith(AssessmentProver.Messages.INSPECT) or
                                                               startWith(AssessmentProver.Messages.SKIPPED) or
                                                               startWith(
                                                                 AssessmentProver.Messages.PASS + ":Partial"
                                                               )) withClue randClue
    }

    val gradedLinesById = msgLines
      .map(l => graded.findFirstMatchIn(l).map(_.group("id").toLong).getOrElse(-1) -> l)
      .groupBy(_._1)
      .map({ case (k, v) => k -> v.map(_._2) })
    val parseFailedLinesById = msgLines
      .map(l => parseFailed.findFirstMatchIn(l).map(_.group("id").toLong).getOrElse(-1) -> l)
      .groupBy(_._1)
      .map({ case (k, v) => k -> v.map(_._2) })

    expected.foreach(e => {
      val parseFailedLines = parseFailedLinesById.getOrElse(e._1.id, List.empty)
      val gradedLines = gradedLinesById.getOrElse(e._1.id, List.empty)
      parseFailedLines.intersect(gradedLines) shouldBe Symbol("empty")
      uniformAnswer match {
        case None | Some((_, true)) =>
          parseFailedLines shouldBe Symbol("empty")
          checkGradedLines(gradedLines, e._2)
        case _ => e._1.name match {
            case "\\ask" => e
                ._1
                .answers
                .map({ case Submission.TextAnswer(_, _, name, _, _, expected) =>
                  name match {
                    case "\\sol" =>
                      val trimmed =
                        if (expected.trim.startsWith("{")) expected.stripPrefix("{").stripSuffix("}").trim
                        else expected.trim
                      if (
                        trimmed.startsWith(QuizExtractor.AskQuestion.KYXLINE) || trimmed
                          .startsWith(QuizExtractor.AskQuestion.MATH_DELIM)
                      ) {
                        // parsed answer
                        gradedLines shouldBe Symbol("empty")
                        parseFailedLines.size shouldBe 1
                      } else {
                        // text answer
                        parseFailedLines shouldBe Symbol("empty")
                        checkGradedLines(gradedLines, e._2)
                      }
                    case "\\solfinask" =>
                      // parsed answer
                      gradedLines shouldBe Symbol("empty")
                      parseFailedLines.size shouldBe 1
                  }
                })
            case _ =>
              // other question types do not have free-text input
              checkGradedLines(gradedLines, e._2)
          }
      }
    })

    if (checkScore) {
      val results = {
        import Submission.GradeJsonFormat._
        resultsString.parseJson.convertTo[List[(Submission.Problem, Double)]]
      }

      results.map(_._1.id.toString) shouldBe sorted
      results.foreach({ case (problem, grade) =>
        val submittedProblem = submission.problems.find(_.title == problem.title).get
        val achievedPoints = submittedProblem
          .prompts
          .map(prompt =>
            expected.find(_._1.id == prompt.id) match {
              case Some((p, answeredCorrectly)) => p.name match {
                  case "\\ask" | "\\anychoice" =>
                    val skipped = gradedLinesById.contains(p.id) && gradedLinesById(p.id)
                      .map(_.split("""\.\.\.""")(1))
                      .forall(_ == AssessmentProver.Messages.SKIPPED)
                    val partial = gradedLinesById.contains(p.id) && gradedLinesById(p.id)
                      .map(_.split("""\.\.\.""")(1))
                      .forall(_.startsWith(AssessmentProver.Messages.PASS + ":Partial"))
                    val inspect = gradedLinesById.contains(p.id) && gradedLinesById(p.id)
                      .map(_.split("""\.\.\.""")(1))
                      .forall(_.startsWith(AssessmentProver.Messages.INSPECT))
                    if (!skipped && !partial && !inspect && uniformAnswer.forall(_._2) && answeredCorrectly) 1.0
                    else if (partial) {
                      // @todo introduce \partialsol tex command with expected partial score
                      // monitor check computes score depending on how wrong the answer is, does not return a single uniform partial score
                      if (problem.title.toLowerCase.contains("monitor"))
                        cancel("Test TODO: unable to check partial score of monitors")
                      else 0.5
                    } else if (inspect) 0.0
                    else expectedFailScore
                  case _ => if (answeredCorrectly) 1.0 else expectedFailScore
                }
              case None => fail("Grade for unknown question " + prompt.id + "; " + randClue)
            }
          )
          .sum
        grade shouldBe achievedPoints withClue randClue
      })
    }
  }

  private def runGrader(submission: Submission.Chapter) = {
    val json = {
      import Submission.SubmissionJsonFormat._
      submission.toJson
    }
    val f = java.io.File.createTempFile("quiz", ".json")
    val w = new PrintWriter(f)
    w.print(json.compactPrint)
    w.flush()
    w.close()

    val options = Options(name = "", args = Nil, in = Some(f.getAbsolutePath))
    val msgsStream = new ByteArrayOutputStream()
    val resultsStream = new ByteArrayOutputStream()
    AssessmentProver.grade(options, msgsStream, resultsStream)
    val msgs = msgsStream.toString
    print(msgs)
    val msgLines = (msgs: StringOps).linesIterator.toList
    (resultsStream.toString, msgLines)
  }

  /**
   * Creates a submission with randomly selected answers from the correct/incorrect sets in `problems`, or with the
   * `uniformAnswer` provided. Returns the submission and the list of questions with indicator correctly/incorrectly
   * answered.
   */
  private def createSubmission(
      problems: List[Problem],
      chapterLabel: String,
      r: RepeatableRandom,
      uniformAnswer: Option[String],
  ): (Submission.Chapter, List[(Submission.Prompt, Boolean)]) = {
    @tailrec
    def createGraderCookie(grader: Grader): Option[Submission.GraderCookie] = grader match {
      case AskGrader(Some(mode), args, _) => Some(Submission.GraderCookie(
          1,
          "\\algog",
          mode + "(" + args.map({ case (k, v) => k + "=\"" + v.replace("\"", "\\\"") + "\"" }).mkString(",") + ")",
        ))
      case AskGrader(None, _, _) => None
      case MultiAskGrader(main, _) => createGraderCookie(main)
      case _: OneChoiceGrader => None
      case _: AnyChoiceGrader => None
      case _: AskTFGrader => None
    }

    def artifactString(a: Artifact): String = a match {
      case ExpressionArtifact(expr, _) => expr
      case TexExpressionArtifact(expr) => expr match {
          case fml: Formula =>
            val disjuncts = FormulaTools.disjuncts(fml)
            if (
              disjuncts.forall({
                case Equal(_: Variable, _: Number) => true
                case _ => false
              })
            ) {
              // list of values
              disjuncts.map({ case Equal(_, n) => n.prettyString }).mkString("{", ",", "}")
            } else {
              // intervals
              def left(a: Formula) = a match {
                case Less(a, _) => "(" + a.prettyString
                case LessEqual(a, _) => "[" + a.prettyString
                case True => "(\\infty"
              }
              def right(a: Formula) = a match {
                case Less(_, a) => a.prettyString + ")"
                case LessEqual(_, a) => a.prettyString + "]"
                case True => "\\infty)"
              }
              disjuncts.map({ case And(l, r) => left(l) + "," + right(r) }).mkString("\\cup")
            }
          case _ => expr.prettyString
        }
      case ListExpressionArtifact(exprs) => exprs.map(_.prettyString).mkString(",")
      case SequentArtifact(goals) => goals.map(_.toString).mkString(";;")
      case TacticArtifact(s, _) => s
      case TextArtifact(text) => text.getOrElse("")
      case ArchiveArtifact(s) => s
      case SubstitutionArtifact(s) => "(" + s.map(_.toString).mkString(",") + ")"
    }

    def artifactSrcString(a: Artifact): String = a match {
      case _: ExpressionArtifact => """{\kyxline"""" + artifactString(a) + """"}"""
      case _: TexExpressionArtifact => "{$" + artifactString(a) + "$}"
      case _: ListExpressionArtifact => """{\kyxline"""" + artifactString(a) + "\"}"
      case _: SequentArtifact => """{\kyxline"""" + artifactString(a) + """"}"""
      case _: TacticArtifact => """{\kyxline"""" + artifactString(a) + """"}"""
      case _: TextArtifact => artifactString(a)
      case _: ArchiveArtifact => """{\begin{lstlisting}""" + artifactString(a) + """\end{lstlisting}}"""
      case _: SubstitutionArtifact => """{\kyxline"""" + artifactString(a) + """"}"""
      case AnyOfArtifact(a) => "{" + a.map(artifactSrcString).map(_.stripPrefix("{").stripSuffix("}")).mkString + "}"
    }

    def createAnswer(grader: Grader, a: Artifact): List[Submission.Answer] = {
      val graderCookie = createGraderCookie(grader)
      a match {
        case _: ExpressionArtifact | _: TexExpressionArtifact | _: ListExpressionArtifact | _: SequentArtifact |
            _: TacticArtifact | _: ArchiveArtifact | _: SubstitutionArtifact =>
          // @note guesses solfin from presence of grader question with placeholders
          val (name, answer, expected) = grader match {
            case AskGrader(_, args, _) => args.get("question") match {
                case Some(q) if q.contains(AskQuestion.ARG_PLACEHOLDER) =>
                  def solfinText(artifact: Artifact): String = {
                    val exprs = artifact match {
                      case ExpressionArtifact(s, _) => s :: Nil
                      case ListExpressionArtifact(exprs) => exprs.map(_.prettyString)
                      case TacticArtifact(s, _) => s :: Nil
                      case ArchiveArtifact(s) => s :: Nil
                      case SequentArtifact(s) => s.map(_.toString).mkString(";;") :: Nil
                    }
                    exprs
                      .zipWithIndex
                      .foldRight(q)({ case ((expr, i), answer) =>
                        answer.replace(s"${AskQuestion.ARG_PLACEHOLDER}${i + 1}", "<%%" + expr + "%%>")
                      })
                  }
                  val answerText = solfinText(a)
                  val expectedText = """{\begin{lstlisting}""" + solfinText(grader.expected) + """\end{lstlisting}}"""
                  ("\\solfinask", answerText, expectedText)
                case _ => ("\\sol", artifactString(a), artifactSrcString(grader.expected))
              }
            case MultiAskGrader(main, _) =>
              val TextAnswer(_, _, name, _, answer, expected) :: Nil = createAnswer(main, a)
              (name, answer, expected)
          }
          TextAnswer(1, "", name, graderCookie, answer, expected) :: Nil
        case ChoiceArtifact(selected) =>
          selected.map(s =>
            Submission.ChoiceAnswer(
              1,
              "",
              grader.expected match { case ChoiceArtifact(es) => if (es.contains(s)) "\\choice*" else "\\choice" },
              graderCookie,
              s,
              isSelected = true,
            )
          )
          grader.expected match {
            case ChoiceArtifact(es) =>
              val expectedTicked = es.intersect(selected)
              val expectedNotick = es.toSet -- selected.toSet
              val unexpectedTick = selected.toSet -- es.toSet
              expectedTicked
                .map(s => Submission.ChoiceAnswer(1, "", "\\choice*", graderCookie, s, isSelected = true)) ++
                expectedNotick
                  .map(s => Submission.ChoiceAnswer(1, "", "\\choice*", graderCookie, s, isSelected = false)) ++
                unexpectedTick.map(s => Submission.ChoiceAnswer(1, "", "\\choice", graderCookie, s, isSelected = true))
          }
        case BoolArtifact(value) =>
          // @todo assumes askTF is a choice with two options
          Submission.ChoiceAnswer(
            1,
            "",
            grader.expected match { case BoolArtifact(b) => if (b.contains(true)) "\\choice*" else "\\choice" },
            graderCookie,
            "True",
            isSelected = value.getOrElse(false),
          ) ::
            Submission.ChoiceAnswer(
              1,
              "",
              grader.expected match { case BoolArtifact(b) => if (b.contains(false)) "\\choice*" else "\\choice" },
              graderCookie,
              "False",
              isSelected = value.exists(!_),
            ) :: Nil
        case TextArtifact(value) =>
          TextAnswer(1, "", "\\sol", graderCookie, value.getOrElse(""), artifactSrcString(grader.expected)) :: Nil
        case MultiArtifact(artifacts) => createAnswer(grader, artifacts.last)
      }
    }

    /** Creates a prompt with its answers. Returns the prompt and correct=true/incorrect=false. */
    def createPrompt(q: Question, i: Int): (Submission.Prompt, Boolean) = {
      val (grader, correct, incorrect) = toGrader(q)
      // @note some questions may not have incorrect test answers annotated, but all have a correct solution
      val (answers, answerIncorrectly) = uniformAnswer match {
        case Some(s) if q.isInstanceOf[AskQuestion] || q.isInstanceOf[MultiAskQuestion] =>
          @tailrec
          def correctString(a: Artifact): String = a match {
            case ExpressionArtifact(s, _) => s
            case ListExpressionArtifact(expr) => expr.map(_.prettyString).mkString(",")
            case TexExpressionArtifact(expr) => expr.prettyString
            case TextArtifact(Some(s)) => s
            case SequentArtifact(_) => ""
            case MultiArtifact(a) => correctString(a.last)
          }
          def answeredIncorrectly(
              grader: Option[Submission.GraderCookie],
              expected: Artifact,
              answer: String,
          ): Boolean = {
            grader match {
              case Some(Submission.GraderCookie(_, _, method))
                  if method.startsWith(AskGrader.Modes.EXPLANATION_CHECK) =>
                // @note replicate explanation check grader
                // @todo inspect method
                answer.trim.length < 8
              case _ => answer.trim.isEmpty || !correctString(expected).contains(answer)
            }
          }
          createAnswer(grader, correct(0)) match {
            case TextAnswer(id, label, name, grader, _, expected) :: Nil =>
              if (name == "\\sol") {
                (TextAnswer(id, label, name, grader, s, expected) :: Nil, answeredIncorrectly(grader, correct(0), s))
              } else if (name == "\\solfinask") {
                val answer = expected.replaceAll("(?s)<%%.*?%%>", "<%%" + s + "%%>")
                (
                  TextAnswer(id, label, name, grader, answer, expected) :: Nil,
                  answeredIncorrectly(grader, correct(0), s),
                )
              } else throw new IllegalArgumentException("Unknown text answer type " + name)
          }
        case Some("") => (
            createAnswer(grader, correct(0)).map({ case ChoiceAnswer(id, label, name, grader, text, _) =>
              ChoiceAnswer(id, label, name, grader, text, isSelected = false)
            }),
            true,
          )
        case _ =>
          val answerIncorrectly = !r.rand.nextBoolean() && incorrect.nonEmpty
          val answers = {
            if (answerIncorrectly) createAnswer(grader, incorrect(r.rand.nextInt(incorrect.size)))
            else createAnswer(grader, correct(r.rand.nextInt(correct.size)))
          }
          (answers, answerIncorrectly)
      }
      def charNumber(i: Int): String = (i + 'a'.toInt).toChar.toString
      q match {
        case _: AskQuestion => (Submission.SinglePrompt(i, 1, charNumber(i), "\\ask", 1.0, answers), !answerIncorrectly)
        case _: AnyChoiceQuestion =>
          (Submission.SinglePrompt(i, 1, charNumber(i), "\\anychoice", 1.0, answers), !answerIncorrectly)
        case _: OneChoiceQuestion =>
          (Submission.SinglePrompt(i, 1, charNumber(i), "\\onechoice", 1.0, answers), !answerIncorrectly)
        case _: AskTFQuestion =>
          (Submission.SinglePrompt(i, 1, charNumber(i), "\\asktf", 1.0, answers), !answerIncorrectly)
        case _: MultiAskQuestion =>
          // @note name of main question and mark as multiprompt to adjust correct=true/false according to other subquestions
          (
            Submission.MultiPrompt(Submission.SinglePrompt(i, 1, charNumber(i), "\\ask", 1.0, answers), Map.empty),
            !answerIncorrectly,
          )
      }
    }

    def createProblem(p: Problem, i: Int): (Submission.Problem, List[(Submission.Prompt, Boolean)]) = {
      // @note problems have IDs 1000,..., prompts of problem 1000 have IDs 2000,.... etc.
      val answers = p.questions.zipWithIndex.map({ case (q, j) => createPrompt(q, 2000 + 1000 * i + j) })
      // @note multiprompts only correct if all subprompts are correct
      val adjustedAnswers = answers
        .zipWithIndex
        .map({
          case (a @ (_: Submission.SinglePrompt, _), _) => a
          case ((Submission.MultiPrompt(main, _), answeredCorrectly), i) =>
            // @todo so far all multiprompts only use \\%-1, but will need to inspect multiprompt graders to know which other prompts to consult when adjusting correct=true/false
            (main, answeredCorrectly && answers(i - 1)._2)
        })
      val pointsTotal = answers.map(_._1.points).sum
      (
        Submission.Problem(1000 + i, 1, i.toString, p.name.getOrElse(""), "", pointsTotal, answers.map(_._1)),
        adjustedAnswers,
      )
    }
    val submittedProblems = problems.zipWithIndex.map((createProblem _).tupled)
    (Submission.Chapter(1, chapterLabel, submittedProblems.map(_._1)), submittedProblems.flatMap(_._2))
  }

  private def run(problems: List[Problem]): Unit = {
    forEvery(table(problems)) { case (problem, grader, testAnswers, noAnswers) =>
      println("Problem section: " + problem)
      testAnswers.foreach(t => {
        println("Testing sol: " + t)
        val tic = System.nanoTime()
        val result = grader.check(t)
        result match {
          case Left(l) =>
            l shouldBe Symbol("proved") withClue s"$t: ${result.toOption.getOrElse("<unknown>")}"
            println("Successfully verified sol")
          case Right(msg) =>
            msg shouldBe "INSPECT" withClue t
            println("WARNING: sol needs manual inspection (INSPECT)")
        }
        val toc = System.nanoTime()
        // (toc - tic) should be <= 5000000000L
      })
      noAnswers.foreach(t => {
        println("Testing no-sol: " + t)
        val tic = System.nanoTime()
        grader.check(t) match {
          case Left(l) => grader match {
              case _: AnyChoiceGrader if l.isProved =>
                l.conclusion shouldBe "==> anychoice&partial <-> anychoice&partial".asSequent withClue t
              case _ => l shouldNot be(Symbol("proved")) withClue t
            }
          case Right(_) => //
        }
        println("Successfully rejected no-sol")
        val toc = System.nanoTime()
        // (toc - tic) should be <= 5000000000L
      })
    }
  }

  /** Extracts quiz problems with their solutions (have, expected) from the resource at `path`. */
  private def extractProblems(path: String): List[Problem] = {
    val r = getClass.getResourceAsStream(path)
    require(
      r != null,
      "Unable to find " + path + "; please check that keymaerax-webui/src/test/resources" + path + " exists",
    )
    val source = io.Source.fromInputStream(r, "UTF-8")
    val content =
      try source.mkString
      finally source.close()
    Problem.fromString(content.linesWithSeparators.filterNot(_.startsWith("%")).mkString)
  }

  private def table(problems: List[Problem]) = {
    Table(
      ("Problem", "Grader", "TestAnswers", "NoAnswers"),
      problems.flatMap(p =>
        p.questions
          .map(q => {
            val (grader, correct, incorrect) = toGrader(q)
            (p.name, grader, correct, incorrect)
          })
      ): _*
    )
  }

  /** Returns a grader, a list of correct solutions, and a list of incorrect solutions for question `q`. */
  private def toGrader(q: Question): (Grader, List[Artifact], List[Artifact]) = q match {
    case q: AskQuestion => (AskGrader(q.grader, q.args, q.expected), q.testSols, q.noSols)
    case MultiAskQuestion(main, earlier) =>
      val (mainGrader, mainSols, mainNosols) = toGrader(main)
      val earlierGraders = earlier.map({ case (k, v) => (k, toGrader(v)) }).toList.sortBy(_._1)
      val grader = MultiAskGrader(mainGrader, earlierGraders.map({ case (k, (grader, _, _)) => (k, grader) }).toMap)
      // take first solution from each question, second from each question, ... (result sorted earliest to main),
      // padded to same length with last element from each question
      val earlierSols = earlierGraders.map(_._2._2)
      val maxSols = (earlierSols.map(_.size) :+ mainSols.size).max
      val sols = (earlierSols.map(n => n ++ List.fill(maxSols - n.size)(n.last)) :+
        (mainSols ++ List.fill(maxSols - mainSols.size)(mainSols.last))).transpose.map(MultiArtifact)
      // same for nosols, but fill in missing nosols with earlier sols (nosol on main answer is wrong even for earlier correct answer)
      val earlierNosols = earlierGraders.map(_._2._3)
      val maxNosols = (earlierNosols.map(_.size) :+ mainNosols.size).max
      val paddedNosols = earlierNosols
        .zipWithIndex
        .map({ case (n, i) =>
          n ++ List.fill(maxNosols - n.size)(earlierSols(i).take(maxNosols - n.size)).flatten.take(maxNosols - n.size)
        })
      val nosols = (paddedNosols :+ (mainNosols ++ List.fill(maxNosols - mainNosols.size)(TextArtifact(None))))
        .transpose
        .map(MultiArtifact)
      (grader, sols, nosols)
    case q: OneChoiceQuestion =>
      val (correct, incorrect) = q.choices.partition(_.isCorrect) match {
        case (c, i) => (c.map(c => ChoiceArtifact(c.text :: Nil)), i.map(c => ChoiceArtifact(c.text :: Nil)))
      }
      // @todo do we ever have a \\onechoice with more than 1 correct answer?
      assert(correct.size == 1, "Missing or non-unique correct solution")
      (OneChoiceGrader(Map.empty[String, String], correct.head), correct, incorrect)
    case q: AnyChoiceQuestion =>
      val (correct, incorrect) = q.choices.partition(_.isCorrect) match {
        case (c, _) =>
          // @note any other combination of selected choices
          val incorrectCombinations = q.choices.toSet.subsets().filter(_ != c.toSet)
          (ChoiceArtifact(c.map(_.text)), incorrectCombinations.map(c => ChoiceArtifact(c.map(_.text).toList)))
      }
      (AnyChoiceGrader(Map.empty[String, String], correct), correct :: Nil, incorrect.toList)
    case q: AskTFQuestion =>
      val correct = BoolArtifact(Some(q.isTrue))
      val incorrect = BoolArtifact(Some(!q.isTrue))
      (AskTFGrader(correct), correct :: Nil, incorrect :: Nil)
  }

  private def solCounts(problems: List[Problem]): (Int, Int, Int) = {
    problems
      .flatMap(
        _.questions
          .map({
            case AskQuestion(_, _, _, testsols, nosols) => (1, testsols.size - 1, nosols.size)
            case MultiAskQuestion(AskQuestion(_, _, _, testsols, nosols), _) => (1, testsols.size - 1, nosols.size)
            case _ => (1, 0, 0)
          })
      )
      .reduce[(Int, Int, Int)]({ case ((la, lb, lc), (ra, rb, rc)) => (la + ra, lb + rb, lc + rc) })
  }

}
