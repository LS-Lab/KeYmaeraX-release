package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.{IllFormedTacticApplicationException, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.{AnyChoiceGrader, AskGrader, AskTFGrader, BoolArtifact, ChoiceArtifact, ExpressionArtifact, ListExpressionArtifact, OneChoiceGrader, SequentArtifact}
import edu.cmu.cs.ls.keymaerax.cli.QuizExtractor._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.Inside.inside
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.LoneElement._

import scala.util.Try

class AssessmentProverTests extends TacticTestBase {

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
    inside (Problem.fromString("""\begin{problem}\ask \sol \kyxline"x>=0" \testsol \kyxline"x+1>=1" \testsol{\kyxline"x+2>=2"} \autog{polyeq(vars="x")}\end{problem}""")) {
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
    val problems = extractProblems(QUIZ_PATH + "/2/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Solve ODEs", 5) :: ("Vector Field Examples", 4) :: ("Semantics of terms", 4) ::
      ("Semantics of formulas", 5) :: ("Formulas as evolution domain constraints", 2) :: Nil
    run(problems)
  }

  it should "prove quiz 3" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/3/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Programs vs. formulas vs. terms", 10) :: ("Misplaced parentheses", 3) ::
        ("Reachable Sets", 5) :: ("Program Shapes", 4) :: Nil
    run(problems)
  }

  it should "prove quiz 4" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/4/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("", 10) :: ("Truth Identification", 7) :: ("Multiple pre/postconditions", 3) ::
        ("Direct velocity control", 1) :: Nil
    run(problems)
  }

  it should "prove quiz 5" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/5/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Axiom application", 10) :: ("Axiom identification: Top", 6) :: ("Axiom identification: All", 6) ::
        ("Distributivity and non-distributivity", 5) :: ("If-then-else", 2) :: ("Nondeterministic assignments", 2) :: Nil
    run(problems)
  }

  it should "prove quiz 6" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/6/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Rule application", 10) :: ("Rule identification", 8) :: ("Arithmetic simplification", 6) ::
        ("Proof rule criticism", 5) :: Nil
    run(problems)
  }

  it should "prove quiz 7" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/7/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Loop invariants", 5) :: ("Other Loop Rules", 4) ::
        ("Incremental design in direct velocity control", 3) :: Nil
    run(problems)
  }

  it should "prove quiz 8" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/8/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Revisiting ping-pong events", 4) :: ("Faithful Event Models", 6) ::
        ("Identify event invariants", 3) :: ("Incremental design in velocity event control", 4) :: Nil
    run(problems)
  }

  it should "prove quiz 10" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/10/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Differential invariance", 10) :: ("Identify differential invariants", 5) ::
        ("Differential Invariant Rules", 5) :: Nil
    run(problems)
  }

  it should "prove quiz 11" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/11/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Identify differential invariants and cuts", 10) :: ("Differential Invariance Rules", 5) :: Nil
    run(problems)
  }

  it should "prove quiz 14" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/14/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Player Count", 5) :: ("Strategically reachable set", 5) :: ("Game Shapes", 2) ::
        ("Truth Identification", 5) :: Nil
    run(problems)
  }

  it should "prove quiz 15" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/15/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Game Region Shapes", 5) :: ("Game loop semantics", 5) :: ("Direct velocity control", 1) :: Nil
    run(problems)
  }

  it should "prove quiz 16" in withZ3 { _ =>
    val problems = extractProblems(QUIZ_PATH + "/16/main.tex")
    problems.map(p => (p.name.getOrElse(""), p.questions.size)) shouldBe
      ("Reflection", 0) :: ("Truth Identification", 5) :: ("Axiom or not?", 10) :: ("Demon's controls", 5) ::
        ("Robot simple chase game", 1) :: Nil
    run(problems)
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

  /** Extracts quiz problems with their solutions (have, expected) from the resource at `path`. */
  private def extractProblems(path: String): List[Problem] = {
    val r = getClass.getResourceAsStream(path)
    require(r != null, "Unable to find " + path + "; please check that keymaerax-webui/src/test/resources" + path + " exists")
    val content = resource.managed(io.Source.fromInputStream(r, "UTF-8")).apply(_.mkString)
    Problem.fromString(content.linesWithSeparators.filterNot(_.startsWith("%")).mkString)
  }

  private def table(problems: List[Problem]) = {
    Table(("Problem", "Grader", "TestAnswers", "NoAnswers"), problems.flatMap(p => p.questions.map({
      case q: AskQuestion =>
        (p.name, AskGrader(q.grader, q.args, q.expected), q.testSols, q.noSols)
      case q: OneChoiceQuestion =>
        val (correct, incorrect) = q.choices.partition(_.isCorrect) match {
          case (c, i) =>
            (c.map(c => ChoiceArtifact(c.text :: Nil)), i.map(c => ChoiceArtifact(c.text :: Nil)))
        }
        //@todo do we ever have a \\onechoice with more than 1 correct answer?
        assert(correct.size == 1, "Missing or non-unique correct solution")
        (p.name, OneChoiceGrader(Map.empty[String, String], correct.head), correct, incorrect)
      case q: AnyChoiceQuestion =>
        val (correct, incorrect) = q.choices.partition(_.isCorrect) match {
          case (c, i) =>
            //@note any other combination of selected choices
            val incorrectCombinations = q.choices.toSet.subsets.filter(_ != c.toSet)
            (ChoiceArtifact(c.map(_.text)), incorrectCombinations.map(c => ChoiceArtifact(c.map(_.text).toList)))
        }
        (p.name, AnyChoiceGrader(Map.empty[String, String], correct), correct :: Nil, incorrect)
      case q: AskTFQuestion =>
        val correct = BoolArtifact(q.isTrue)
        val incorrect = BoolArtifact(!q.isTrue)
        (p.name, AskTFGrader(correct), correct :: Nil, incorrect :: Nil)
    })):_*)
  }

}
