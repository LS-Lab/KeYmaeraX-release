package edu.cmu.cs.ls.keymaerax.cli

import java.io.{ByteArrayOutputStream, PrintWriter}

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.{IllFormedTacticApplicationException, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.{AnyChoiceGrader, Artifact, AskGrader, AskTFGrader, BoolArtifact, ChoiceArtifact, ExpressionArtifact, Grader, ListExpressionArtifact, OneChoiceGrader, SequentArtifact, TexExpressionArtifact, TextArtifact}
import edu.cmu.cs.ls.keymaerax.cli.QuizExtractor._
import edu.cmu.cs.ls.keymaerax.cli.Submission.TextAnswer
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.Inside.inside
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.LoneElement._
import org.scalatest.EitherValues._
import spray.json._

class AssessmentProverTests extends TacticTestBase {

  private val COURSE_PATH: String = "/Course-current"
  private val QUIZ_PATH: String = COURSE_PATH + "/diderot/quizzes"

  private val RANDOM_TRIALS = 100
  private val rand = RepeatableRandom()

  "Extractor" should "extract grading information" in {
    Problem.fromString("""\begin{problem}\label{prob:withoutpoints} \ask \sol{\kyxline"x>=0}" \end{problem}""") shouldBe 'empty
    inside (Problem.fromString("""\begin{problem}[1.0]\label{prob:first} \ask \sol{\kyxline"x>=0"} \end{problem}""")) {
      case p :: Nil =>
        p.name shouldBe 'empty
        p.points should contain (1.0)
        p.label should contain ("prob:first")
        p.questions shouldBe List(AskQuestion(None, Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[4.][Problem A] \ask Something simple \sol{\kyxline"x>=0"} \end{problem}""")) {
      case p :: Nil =>
        p.name should contain ("Problem A")
        p.points should contain (4.0)
        p.questions shouldBe List(AskQuestion(None, Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[4.][Problem A] \ask A tex question \sol{$\{1,(-2),x^2\}$} \end{problem}""")) {
      case p :: Nil =>
        p.name should contain ("Problem A")
        p.points should contain (4.0)
        p.questions shouldBe List(AskQuestion(None, Map.empty, TexExpressionArtifact("x=1|x=-2|x=x^2".asFormula), List(TexExpressionArtifact("x=1|x=-2|x=x^2".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[4.][Problem A] \ask A tex interval question \sol{$[-2.0,3) \cup (1,\infty)$} \end{problem}""")) {
      case p :: Nil =>
        p.name should contain ("Problem A")
        p.points should contain (4.0)
        p.questions shouldBe List(AskQuestion(None, Map.empty, TexExpressionArtifact("-2.0<=x&x<3|1<x&true".asFormula), List(TexExpressionArtifact("-2.0<=x&x<3|1<x&true".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[1.0][Problem B] \ask A syntactic equality \sol{\kyxline"x>=0"} \autog{syneq()} \end{problem}""")) {
      case p :: Nil =>
        p.name should contain ("Problem B")
        p.questions shouldBe
          List(AskQuestion(Some("syneq"), Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    }
    inside (Problem.fromString(
      """\begin{problem}[1.0]
        |\ask \sol{\kyxline"x>=0"} \autog{syneq()}
        |\ask \sol{\kyxline"y=2"}
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
    inside (Problem.fromString("""\begin{problem}[1.0]\ask \sol{\kyxline"x>=0"} \autog{polyeq(vars="x")}\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[1.0]\ask \sol{\kyxline"x>=0"} \testsol \kyxline"x+1>=1" \testsol{\kyxline"x+2>=2"} \autog{polyeq(vars="x")}\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula),
            List(ExpressionArtifact("x>=0".asFormula), ExpressionArtifact("x+1>=1".asFormula), ExpressionArtifact("x+2>=2".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[1.0]\ask \sol{\kyxline"x>=0"} \testsol \kyxline"x+1>=1" \nosol \kyxline"x+1>=0" \nosol \kyxline"x-1>=2" \autog{polyeq(vars="x")}\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula),
            List(ExpressionArtifact("x>=0".asFormula), ExpressionArtifact("x+1>=1".asFormula)),
            List(ExpressionArtifact("x+1>=0".asFormula), ExpressionArtifact("x-1>=2".asFormula))))
    }
    inside (Problem.fromString(
      """\begin{problem}[1.0]
        |\ask A DI question
        |\sol{\kyxline"2*x=y"}
        |\autog{dI(vars="x",
        |          question="{x'=1,y'=2}")}
        |\end{problem}""".stripMargin)) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(Some("dI"), Map("vars"->"x", "question"->"{x'=1,y'=2}"), ExpressionArtifact("2*x=y".asFormula), List(ExpressionArtifact("2*x=y".asFormula)), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[1.0]\ask \sol{\kyxline"x>0 ==> x>=0 ;; y<0 ==> y<=0"}\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(None, Map.empty,
            SequentArtifact(List("x>0 ==> x>=0".asSequent, "y<0 ==> y<=0".asSequent)),
            List(SequentArtifact(List("x>0 ==> x>=0".asSequent, "y<0 ==> y<=0".asSequent))), List.empty))
    }
    inside (Problem.fromString("""\begin{problem}[1.0]\ask \sol{\kyxline"x>0,y>0,z>0"}\end{problem}""")) {
      case p :: Nil =>
        p.questions shouldBe
          List(AskQuestion(None, Map.empty,
            ListExpressionArtifact(List("x>0".asFormula, "y>0".asFormula, "z>0".asFormula)),
            List(ListExpressionArtifact(List("x>0".asFormula, "y>0".asFormula, "z>0".asFormula))), List.empty))
    }
    inside (Problem.fromString(
      """\begin{problem}[1.0]
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
        |\end{problem}""".stripMargin)) {
      case p :: Nil =>
        p.questions shouldBe List(
          AskQuestion(None, Map.empty, ExpressionArtifact("x>=0".asFormula),
            List(ExpressionArtifact("x>=0".asFormula)), List.empty),
          OneChoiceQuestion("A choice question", List(
            QuizExtractor.Choice("Wrong answer", isCorrect=false),
            QuizExtractor.Choice("Right answer", isCorrect=true),
            QuizExtractor.Choice("Another wrong answer", isCorrect=false))),
          OneChoiceQuestion("Another choice question", List(
            QuizExtractor.Choice("Correct", isCorrect=true),
            QuizExtractor.Choice("Incorrect", isCorrect=false)))
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
    AssessmentProver.qe("x>=0".asFormula, "0<=x".asFormula, Equiv)
    AssessmentProver.qe("x>=4".asFormula, "x>=0 & x^2>=16".asFormula, Equiv) shouldBe 'proved
    AssessmentProver.qe("x=1".asFormula, "x^2>=1 & x^2<=x".asFormula, Equiv) shouldBe 'proved
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      AssessmentProver.qe("x>=4".asFormula, "abs(x)>=4 & abs(x)<=x".asFormula, Equiv) shouldBe 'proved
    }
    AssessmentProver.qe("x>=4".asFormula, "\\forall y (0<=y&y<=4 -> x>=y)".asFormula, Equiv) shouldBe 'proved
    AssessmentProver.qe("x>=4".asFormula, "\\exists y (y>=2 & x>=y^2)".asFormula, Equiv) shouldBe 'proved
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
      check(ExpressionArtifact("A()->[prg;]B()".asFormula)).left.value shouldBe 'proved
    AskGrader(Some(AskGrader.Modes.BELLE_PROOF), Map("tactic" -> "chase(1);prop"), SequentArtifact("A() ==> [prg;]B()".asSequent::Nil)).
      check(SequentArtifact("==> A() -> [prg;]B()".asSequent::Nil)).left.value shouldBe 'proved
    val p = AskGrader(Some(AskGrader.Modes.BELLE_PROOF), Map("tactic" -> "chase(1);prop"), SequentArtifact("==> A() -> [prg;]B()".asSequent::"[sys;]C() ==> ".asSequent::Nil)).
      check(SequentArtifact("A() ==> [prg;]B()".asSequent::"==> [sys;]C() -> false&x=4".asSequent::Nil))
    p.left.value.conclusion shouldBe "==> ((A() -> [prg;]B()) <-> (true -> A() -> [prg;]B())) & ((true -> [sys;]C() -> false&x=4) <-> ([sys;]C() -> false))".asSequent
    p.left.value shouldBe 'proved
  }

  it should "prove optional question with solution as loop tactic input" in withZ3 { _ =>
    AskGrader(
      Some(AskGrader.Modes.BELLE_PROOF),
      Map(
        "question" -> "x>2 & y>=1 -> [{x:=x+y;y:=y+2;}*]x>1",
        "tactic" -> "implyR(1);loop({`#1`},1);auto;done"),
      ExpressionArtifact("false".asFormula)). //@note ignored because question will be used instead
      check(ExpressionArtifact("x>1&y>=0".asFormula)
    ).left.value shouldBe 'proved
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
    ).left.value shouldBe 'proved
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
    ).left.value shouldBe 'proved
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
    val problems = extractProblems(QUIZ_PATH + "/2/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Solve ODEs", 5) :: ("Vector Field Examples", 4) :: ("Semantics of terms", 4) ::
      ("Semantics of formulas", 5) :: ("Formulas as evolution domain constraints", 4) :: Nil
    run(problems)
  }

  it should "prove quiz 3" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/3/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Programs vs. formulas vs. terms", 10) :: ("Misplaced parentheses", 3) ::
        ("Reachable Sets", 5) :: ("Program Shapes", 8) :: ("Modeling pitfalls", 4) :: Nil
    run(problems)
  }

  it should "prove quiz 4" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/4/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("", 10) :: ("Truth Identification", 7) :: ("Multiple pre/postconditions", 4) ::
        ("Direct velocity control", 1) :: Nil
    run(problems)
  }

  it should "prove quiz 5" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/5/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Axiom application", 10) :: ("Axiom identification: Top", 6) :: ("Axiom identification: All", 6) ::
        ("Distributivity and non-distributivity", 5) :: ("If-then-else", 2) :: ("Nondeterministic assignments", 2) :: Nil
    run(problems)
  }

  it should "prove quiz 6" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/6/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Rule application", 10) :: ("Rule identification", 8) :: ("Arithmetic simplification", 6) ::
        ("Proof rule criticism", 10) :: Nil
    run(problems)
  }

  it should "prove quiz 7" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/7/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Loop invariants", 5) :: ("Other Loop Rules", 8) ::
        ("Incremental design in direct velocity control", 3) :: Nil
    run(problems)
  }

  it should "prove quiz 8" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/8/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Revisiting ping-pong events", 4) :: ("Faithful Event Models", 6) ::
        ("Identify event invariants", 3) :: ("Incremental design in velocity event control", 5) :: Nil
    run(problems)
  }

  it should "prove quiz 10" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/10/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Differential invariance", 10) :: ("Identify differential invariants", 5) ::
        ("Differential Invariant Rules", 10) :: Nil
    run(problems)
  }

  it should "prove quiz 11" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/11/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Explain differential cuts", 8) :: ("Identify differential invariants to cut", 10) ::
        ("Differential Invariance Rules", 14) :: Nil
    run(problems)
  }

  it should "prove quiz 14" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/14/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Player Count", 5) :: ("Strategically reachable set", 6) :: ("Game Shapes", 2) ::
        ("Truth Identification", 10) :: Nil
    run(problems)
  }

  it should "prove quiz 15" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/15/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Game Region Shapes", 5) :: ("Game loop semantics", 5) :: ("Direct velocity control", 1) :: Nil
    run(problems)
  }

  it should "prove quiz 16" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/16/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Truth Identification", 5) :: ("Axiom or not?", 10) :: ("Demon's controls", 5) ::
        ("Robot simple chase game", 1) :: Nil
    run(problems)
  }

  "Submission extraction" should "extract answers in the order listed in the file" in {
    //@todo assumes that there will be information to identify the chapter in the tex source (outermost title, or label)
    //@todo assumes that answers will be in the prompt body
    val s = """
      |{"id": 11,
      | "label": "ch:qdiffcut",
      | "children": [
      |   {
      |     "type": "segment",
      |     "otherStuff": [ { "lots": "of", "it": "?" }],
      |     "children": [
      |       {
      |         "type": "segment",
      |         "not actually": "a segment with questions",
      |         "point_value": 0.0
      |       },
      |       {
      |         "type": "segment",
      |         "some intermediate": "segment that does not yet have the question prompt",
      |         "children": [
      |           {
      |             "type": "atom",
      |             "name": "problem",
      |             "id": 25053,
      |             "point_value": 3.0,
      |             "title": "Problem block 1 (2 questions)",
      |             "prompts": [
      |               {
      |                 "point_value": 2.0,
      |                 "body": "A question",
      |                 "id": 141,
      |                 "children": [
      |                   {
      |                     "id": 142,
      |                     "body": "y>=0"
      |                   }
      |                 ]
      |               },
      |               {
      |                 "body": "This question has an answer with a syntax error",
      |                 "point_value": 1.0,
      |                 "id": 143,
      |                 "children": [
      |                   {
      |                     "id": 144,
      |                     "body": "x^2>=+0"
      |                   }
      |                 ]
      |               }
      |             ]
      |           }
      |         ],
      |         "point_value": 3.0
      |       },
      |       {
      |         "type": "segment",
      |         "this segment": "has prompts but none of them auto-gradable (worth no points)",
      |         "children": [
      |           {
      |             "type": "segment",
      |             "point_value": 0.0
      |           },
      |           {
      |             "type": "atom",
      |             "name": "problem",
      |             "title": "Problem block 2 (one non-autogradable question)",
      |             "id": 17218,
      |             "prompts": [
      |                {
      |                  "id": 145,
      |                  "body": "This is the question",
      |                  "children": [
      |                    {
      |                      "id": 146,
      |                      "body": "Here is an answer",
      |                      "and": "other stuff"
      |                    }
      |                  ],
      |                  "point_value": 0.0
      |                }
      |             ],
      |             "point_value": 0.0
      |           }
      |         ],
      |         "point_value": 0.0
      |       },
      |       {
      |         "point_value": 1.0,
      |         "type": "atom",
      |         "name": "problem",
      |         "id": 25160,
      |         "title": "Problem block 3 (single question)",
      |         "this entry": "has one question",
      |         "prompts": [
      |           {
      |             "id": 147,
      |             "body": "The question in LaTeX: \\(x\\geq 0 \\ldots\\)",
      |             "children": [
      |               {
      |                 "body": "x>=0",
      |                 "id": 148
      |               }
      |             ],
      |             "point_value": 1.0
      |           }
      |         ]
      |       }
      |     ],
      |     "point_value": 4.0
      |   },
      |   {
      |     "type": "segment",
      |     "point_value": 1.0,
      |     "children": [
      |       {
      |         "type": "atom",
      |         "name": "problem",
      |         "id": 25057,
      |         "title": "Problem block in second segment",
      |         "point_value": 1.0,
      |         "prompts": [
      |           {
      |             "body": " A question in the second segment",
      |             "id": 149,
      |             "point_value": 1.0,
      |             "is_question_any_choice": false,
      |             "children": [
      |               {
      |                 "id": 150,
      |                 "body": "Sound",
      |                 "is_selected": true,
      |                 "is_choice": true
      |               },
      |               {
      |                 "id": 151,
      |                 "body": "Unsound",
      |                 "is_selected": false,
      |                 "is_choice": true
      |               }
      |             ]
      |           }
      |         ]
      |       }
      |     ]
      |   }
      | ]
      |}""".stripMargin
    import Submission.SubmissionJsonFormat._
    s.parseJson.convertTo[Submission.Chapter] shouldBe Submission.Chapter(11, "ch:qdiffcut", List(
      Submission.Problem(25053, "Problem block 1 (2 questions)", List(
        Submission.Prompt(141, 2.0, List(Submission.TextAnswer(142, "y>=0"))),
        Submission.Prompt(143, 1.0, List(Submission.TextAnswer(144, "x^2>=+0")))
      )),
      Submission.Problem(25160, "Problem block 3 (single question)", List(
        Submission.Prompt(147, 1.0, List(Submission.TextAnswer(148, "x>=0")))
      )),
      Submission.Problem(25057, "Problem block in second segment", List(
        Submission.Prompt(149, 1.0, List(
          Submission.ChoiceAnswer(150, "Sound", isSelected=true),
          Submission.ChoiceAnswer(151, "Unsound", isSelected=false)))
      ))
    ))
  }

  "Command line grader" should "grade random quiz 3 submissions" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/3/main.tex")
    for (i <- 1 to RANDOM_TRIALS) { runGrader(problems, i, "ch:qchoicecontrol") }
  }

  /** Runs the autograder on the `i`th random submission (list of `problems`); uses `chapterLabel` to look up the
    * grading information currently missing from problems. Requires `lfcpsgrader.conf` to map `chapterLabel` to
    * an absolute file path pointing to the quiz tex source. */
  private def runGrader(problems: List[Problem], i: Int, chapterLabel: String): Unit = {
    val randClue = "Submission produced in " + i + "th run of " + RANDOM_TRIALS + " random trials from seed " + rand.seed
    val (submission, expected) = createSubmission(problems, chapterLabel, rand)
    val json = {
      import Submission.SubmissionJsonFormat._
      submission.toJson
    }
    val f = java.io.File.createTempFile("quiz", ".json")
    val w = new PrintWriter(f)
    w.print(json.compactPrint)
    w.flush()
    w.close()

    val options = Map('in -> f.getAbsolutePath, 'config -> "lfcpsgrader.conf")
    val msgsStream = new ByteArrayOutputStream()
    val resultsStream = new ByteArrayOutputStream()
    AssessmentProver.grade(options, msgsStream, resultsStream, "")
    val msgs = msgsStream.toString
    print(msgs)
    val msgLines = msgs.lines
    expected.foreach(e =>
      msgLines.find(_.startsWith("Grading question " + e._1.id)) match {
        case Some(t) => t should startWith ("Grading question " + e._1.id + "..." + (if (e._2) "PASSED" else "FAILED")) withClue randClue
        case _ => fail("Question " + e._1.id + " was not graded; " + randClue)
      }
    )
    val results = {
      import DefaultJsonProtocol._
      import Submission.GradeJsonFormat._
      resultsStream.toString.parseJson.convertTo[List[(Submission.Prompt, Double)]]
    }

    results.foreach({ case (prompt, grade) =>
      expected.find(_._1.id == prompt.id) match {
        case Some((_, answeredCorrectly)) => (if (answeredCorrectly) grade shouldBe 1.0 else grade shouldBe 0.0) withClue randClue
        case None => fail("Grade for unknown question " + prompt.id + "; " + randClue)
      }
    })
  }

  /** Creates a submission with randomly selected answers from the correct/incorrect sets in `problems`.
    * Returns the submission and the list of questions with indicator correctly/incorrectly answered. */
  private def createSubmission(problems: List[Problem], chapterLabel: String, r: RepeatableRandom): (Submission.Chapter, List[(Submission.Prompt, Boolean)]) = {
    def createAnswer(p: Artifact): List[Submission.Answer] = p match {
      case ExpressionArtifact(expr) => TextAnswer(1, expr.prettyString) :: Nil
      case TexExpressionArtifact(expr) => expr match {
        case fml: Formula =>
          val disjuncts = FormulaTools.disjuncts(fml)
          if (disjuncts.forall({ case Equal(_: Variable, _: Number) => true case _ => false })) {
            // list of values
            TextAnswer(1, disjuncts.map({ case Equal(_, n) => n.prettyString }).mkString("{", ",", "}")) :: Nil
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
            val answer = disjuncts.map({ case And(l, r) => left(l) + "," + right(r) }).mkString("\\cup")
            TextAnswer(1, answer) :: Nil
          }
        case _ => TextAnswer(1, expr.prettyString) :: Nil
      }
      case ListExpressionArtifact(exprs) => TextAnswer(1, exprs.map(_.prettyString).mkString(",")) :: Nil
      case SequentArtifact(goals) => TextAnswer(1, goals.map(_.prettyString).mkString(";;")) :: Nil
      case ChoiceArtifact(selected) => selected.map(Submission.ChoiceAnswer(1, _, isSelected=true))
      case BoolArtifact(value) =>
        //@todo assumes askTF is a choice with two options
        Submission.ChoiceAnswer(1, "True", isSelected=value.getOrElse(false)) ::
        Submission.ChoiceAnswer(1, "False", isSelected=value.exists(!_)) :: Nil
      case TextArtifact(value) => TextAnswer(1, value.getOrElse("")) :: Nil
    }

    /** Creates a prompt with its answers. Returns the prompt and correct=true/incorrect=false. */
    def createPrompt(q: Question, i: Int): (Submission.Prompt, Boolean) = {
      val (_, correct, incorrect) = toGrader(q)
      //@note some questions may not have incorrect test answers annotated, but all have a correct solution
      val answerIncorrectly = !r.rand.nextBoolean() && incorrect.nonEmpty
      val answers = {
        if (answerIncorrectly) createAnswer(incorrect(r.rand.nextInt(incorrect.size)))
        else createAnswer(correct(r.rand.nextInt(correct.size)))
      }
      (Submission.Prompt(i, 1.0, answers), !answerIncorrectly)
    }

    def createProblem(p: Problem, i: Int): (Submission.Problem, List[(Submission.Prompt, Boolean)]) = {
      //@note problems have IDs 1000,..., prompts of problem 1000 have IDs 2000,.... etc.
      val answers = p.questions.zipWithIndex.map({ case (q, j) => createPrompt(q, 2000+1000*i+j) })
      (Submission.Problem(1000 + i, p.name.getOrElse(""), answers.map(_._1)), answers)
    }
    val submittedProblems = problems.zipWithIndex.map((createProblem _).tupled)
    (Submission.Chapter(1, chapterLabel, submittedProblems.map(_._1)),
      submittedProblems.flatMap(_._2))
  }

  private def run(problems: List[Problem]): Unit = {
    forEvery (table(problems)) { case (problem, grader, testAnswers, noAnswers) =>
      println("Problem section: " + problem)
      testAnswers.foreach(t => {
        println("Testing sol: " + t)
        val tic = System.nanoTime()
        grader.check(t).left.value shouldBe 'proved withClue t
        println("Successfully verified sol")
        val toc = System.nanoTime()
        (toc - tic) should be <= 5000000000L
      })
      noAnswers.foreach(t => {
        println("Testing no-sol: " + t)
        val tic = System.nanoTime()
        grader.check(t) shouldNot be ('left)
        println("Successfully rejected no-sol")
        val toc = System.nanoTime()
        (toc - tic) should be <= 5000000000L
      })
    }
  }

  /** Extracts quiz problems with their solutions (have, expected) from the resource at `path`. */
  private def extractProblems(path: String): List[Problem] = {
    val r = getClass.getResourceAsStream(path)
    require(r != null, "Unable to find " + path + "; please check that keymaerax-webui/src/test/resources" + path + " exists")
    val content = resource.managed(io.Source.fromInputStream(r, "UTF-8")).apply(_.mkString)
    Problem.fromString(content.linesWithSeparators.filterNot(_.startsWith("%")).mkString)
  }

  private def table(problems: List[Problem]) = {
    Table(("Problem", "Grader", "TestAnswers", "NoAnswers"), problems.flatMap(p => p.questions.map(q => {
      val (grader, correct, incorrect) = toGrader(q)
      (p.name, grader, correct, incorrect)
    })):_*)
  }

  /** Returns a grader, a list of correct solutions, and a list of incorrect solutions for question `q`. */
  private def toGrader(q: Question): (Grader, List[Artifact], List[Artifact]) = q match {
    case q: AskQuestion =>
      (AskGrader(q.grader, q.args, q.expected), q.testSols, q.noSols)
    case q: OneChoiceQuestion =>
      val (correct, incorrect) = q.choices.partition(_.isCorrect) match {
        case (c, i) =>
          (c.map(c => ChoiceArtifact(c.text :: Nil)), i.map(c => ChoiceArtifact(c.text :: Nil)))
      }
      //@todo do we ever have a \\onechoice with more than 1 correct answer?
      assert(correct.size == 1, "Missing or non-unique correct solution")
      (OneChoiceGrader(Map.empty[String, String], correct.head), correct, incorrect)
    case q: AnyChoiceQuestion =>
      val (correct, incorrect) = q.choices.partition(_.isCorrect) match {
        case (c, _) =>
          //@note any other combination of selected choices
          val incorrectCombinations = q.choices.toSet.subsets.filter(_ != c.toSet)
          (ChoiceArtifact(c.map(_.text)), incorrectCombinations.map(c => ChoiceArtifact(c.map(_.text).toList)))
      }
      (AnyChoiceGrader(Map.empty[String, String], correct), correct :: Nil, incorrect.toList)
    case q: AskTFQuestion =>
      val correct = BoolArtifact(Some(q.isTrue))
      val incorrect = BoolArtifact(Some(!q.isTrue))
      (AskTFGrader(correct), correct :: Nil, incorrect :: Nil)
  }

}
