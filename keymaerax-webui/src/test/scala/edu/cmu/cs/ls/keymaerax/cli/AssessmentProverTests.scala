package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.{IllFormedTacticApplicationException, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.cli.AssessmentProver.{Artifact, ExpressionArtifact, ListExpressionArtifact, SequentArtifact}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.Inside.inside
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.scalatest.LoneElement._

import scala.util.Try

class AssessmentProverTests extends TacticTestBase {

  object AssessmentProverInfo {
    private val GRADER = "grader"
    private val ARGS = "args"
    private val SOL = "sol"
    private val TEST_SOL = "testsol"
    private val NO_SOL = "nosol"
    private val ARG_NAME = "argName"
    private val ARG_VAL = "argVal"
    private val TURNSTILE = "==>"
    private val GOAL_SEP = ";;"

    private def kyxlineExtractor(capture: String) = """\\kyxline\s*"(""" + capture + """[^"]+)""""
    private val KYXLINE_EXTRACTOR = kyxlineExtractor("").r(SOL)
    private val SOL_EXTRACTOR = """\\sol\s*""" + KYXLINE_EXTRACTOR.regex + """\s*"""
    private val TEST_SOL_EXTRACTOR = """((?:\\testsol\s*""" + kyxlineExtractor("?:") + """\s*)*)"""
    private val NO_SOL_EXTRACTOR = """((?:\\nosol\s*""" + kyxlineExtractor("?:") + """\s*)*)"""
    private val GRADER_EXTRACTOR = """(?:\\autog\{(\w+)\((.*)\)})?""".stripMargin
    private val EXTRACTOR = (SOL_EXTRACTOR + TEST_SOL_EXTRACTOR + NO_SOL_EXTRACTOR + GRADER_EXTRACTOR).r(SOL, TEST_SOL, NO_SOL, GRADER, ARGS)
    private val ARG_SPLITTER = """(\w+)\s*=\s*"([^"]+)"""".r(ARG_NAME, ARG_VAL)
    private val EXPR_LIST_SPLITTER = """(?:\{[^{}]*})|(,)""".r //@note matches unwanted {...,...} left and , outside {} right so needs filtering of results (not just split)

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

    def fromString(s: String): List[AssessmentProverInfo] = {
      val graderInfo = EXTRACTOR.findAllMatchIn(s).map(m => (m.group(SOL), m.group(TEST_SOL), m.group(NO_SOL), Option(m.group(GRADER)), Option(m.group(ARGS))))
      graderInfo.map({ case (sol, testsol, nosol, grader, args) =>
        val expectedArtifact = artifactsFromString(sol)
        val testSolArtifacts = expectedArtifact +: KYXLINE_EXTRACTOR.findAllMatchIn(testsol).map(_.group(SOL)).map(artifactsFromString).toList
        val noSolArtifacts = KYXLINE_EXTRACTOR.findAllMatchIn(nosol).map(_.group(SOL)).map(artifactsFromString).toList
        AssessmentProverInfo(grader, argsFromString(args), expectedArtifact, testSolArtifacts, noSolArtifacts)
      }).toList
    }

    def argsFromString(args: Option[String]): Map[String, String] = {
      args.map(ARG_SPLITTER.findAllMatchIn).getOrElse(Iterator.empty).
        map(m => (m.group(ARG_NAME), m.group(ARG_VAL))).
        toMap
    }
  }

  case class AssessmentProverInfo(grader: Option[String], args: Map[String, String],
                                  expected: Artifact, testSols: List[Artifact], noSols: List[Artifact])

  private val COURSE_PATH: String = "/Course-current"
  private val QUIZ_PATH: String = COURSE_PATH + "/diderot/quiz"

  "Extractor" should "extract grading information" in {
    AssessmentProverInfo.fromString("""\sol \kyxline"x>=0"""") shouldBe
      List(AssessmentProverInfo(None, Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    AssessmentProverInfo.fromString("""\sol \kyxline"x>=0" \autog{syneq()}""") shouldBe
      List(AssessmentProverInfo(Some("syneq"), Map.empty, ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    AssessmentProverInfo.fromString("""\sol \kyxline"x>=0" \autog{polyeq(vars="x")}""") shouldBe
      List(AssessmentProverInfo(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula), List(ExpressionArtifact("x>=0".asFormula)), List.empty))
    AssessmentProverInfo.fromString("""\sol \kyxline"x>=0" \testsol \kyxline"x+1>=1" \testsol \kyxline"x+2>=2" \autog{polyeq(vars="x")}""") shouldBe
      List(AssessmentProverInfo(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula),
        List(ExpressionArtifact("x>=0".asFormula), ExpressionArtifact("x+1>=1".asFormula), ExpressionArtifact("x+2>=2".asFormula)), List.empty))
    AssessmentProverInfo.fromString("""\sol \kyxline"x>=0" \testsol \kyxline"x+1>=1" \nosol \kyxline"x+1>=0" \nosol \kyxline"x-1>=2" \autog{polyeq(vars="x")}""") shouldBe
      List(AssessmentProverInfo(Some("polyeq"), Map("vars"->"x"), ExpressionArtifact("x>=0".asFormula),
        List(ExpressionArtifact("x>=0".asFormula), ExpressionArtifact("x+1>=1".asFormula)),
        List(ExpressionArtifact("x+1>=0".asFormula), ExpressionArtifact("x-1>=2".asFormula))))
    AssessmentProverInfo.fromString("""\sol \kyxline"2*x=y" \autog{dI(vars="x",question="{x'=1,y'=2}")}""") shouldBe
      List(AssessmentProverInfo(Some("dI"), Map("vars"->"x", "question"->"{x'=1,y'=2}"), ExpressionArtifact("2*x=y".asFormula), List(ExpressionArtifact("2*x=y".asFormula)), List.empty))
    AssessmentProverInfo.fromString("""\sol \kyxline"x>0 ==> x>=0 ;; y<0 ==> y<=0"""") shouldBe
      List(AssessmentProverInfo(None, Map.empty,
        SequentArtifact(List("x>0 ==> x>=0".asSequent, "y<0 ==> y<=0".asSequent)),
        List(SequentArtifact(List("x>0 ==> x>=0".asSequent, "y<0 ==> y<=0".asSequent))), List.empty))
    AssessmentProverInfo.fromString("""\sol \kyxline"x>0,y>0,z>0"""") shouldBe
      List(AssessmentProverInfo(None, Map.empty,
        ListExpressionArtifact(List("x>0".asFormula, "y>0".asFormula, "z>0".asFormula)),
        List(ListExpressionArtifact(List("x>0".asFormula, "y>0".asFormula, "z>0".asFormula))), List.empty))
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
    AssessmentProver.check(ExpressionArtifact("A() -> [prg;]B()".asFormula), ExpressionArtifact("A()->[prg;]B()".asFormula),
      Some(AssessmentProver.Modes.BELLE_PROOF), Map("tactic" -> "chase(1);prop")) shouldBe 'proved
    AssessmentProver.check(
      SequentArtifact("A() ==> [prg;]B()".asSequent::Nil),
      SequentArtifact("==> A() -> [prg;]B()".asSequent::Nil),
      Some(AssessmentProver.Modes.BELLE_PROOF), Map("tactic" -> "chase(1);prop")) shouldBe 'proved
    val p = AssessmentProver.check(
      SequentArtifact("A() ==> [prg;]B()".asSequent::"==> [sys;]C() -> false&x=4".asSequent::Nil),
      SequentArtifact("==> A() -> [prg;]B()".asSequent::"[sys;]C() ==> ".asSequent::Nil),
      Some(AssessmentProver.Modes.BELLE_PROOF), Map("tactic" -> "chase(1);prop"))
    p.conclusion shouldBe "==> ((A() -> [prg;]B()) <-> (true -> A() -> [prg;]B())) & ((true -> [sys;]C() -> false&x=4) <-> ([sys;]C() -> false))".asSequent
    p shouldBe 'proved
  }

  it should "prove optional question with solution as loop tactic input" in withZ3 { _ =>
    AssessmentProver.check(
      ExpressionArtifact("x>1&y>=0".asFormula),
      ExpressionArtifact("false".asFormula), //@note ignored because question will be used instead
      Some(AssessmentProver.Modes.BELLE_PROOF),
      Map(
        "question" -> "x>2 & y>=1 -> [{x:=x+y;y:=y+2;}*]x>1",
        "tactic" -> "implyR(1);loop({`#1`},1);auto;done")
    ) shouldBe 'proved
  }

  it should "prove optional question with a list of diffcuts" in withZ3 { _ =>
    AssessmentProver.check(
      ListExpressionArtifact("a>=1".asFormula :: "v>=2".asFormula :: "x>=3".asFormula :: Nil),
      ExpressionArtifact("false".asFormula), //@note ignored because question will be used instead
      Some(AssessmentProver.Modes.BELLE_PROOF),
      Map(
        "question" -> "x>=3 & v>=2 & a>=1 & j>=0 -> [{x'=v,v'=a,a'=j}]x>=3",
        "tactic" -> "implyR(1); for #i do dC({`#i`},1); <(nil, dI(1); done) endfor; dW(1); QE; done"
      )
    ) shouldBe 'proved
  }

  it should "prove optional question with solution as uniform substitution tactic input" in withZ3 { _ =>
    AssessmentProver.check(
      ExpressionArtifact("x<=m-V*(T-t)".asFormula),
      ExpressionArtifact("false".asFormula), //@note ignored because question will be used instead
      Some(AssessmentProver.Modes.BELLE_PROOF),
      Map(
        "question" -> "x<=m & V>=0 -> [{{v:=0; ++ ?Q(m,t,x,T,V);v:=V;};{x'=v,t'=1 & t<=T}}*]x<=m",
        "tactic" -> "US({`Q(m,t,x,T,V) ~> #1`});implyR(1);loop({`x<=m`},1);auto;done")
    ) shouldBe 'proved
  }

  "Program equivalence" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.prgEquivalence("a;b;c;".asProgram, "{a;b;};c;".asProgram) shouldBe 'proved
    AssessmentProver.prgEquivalence("a;++b;++c;".asProgram, "{a;++b;}++c;".asProgram) shouldBe 'proved
    AssessmentProver.prgEquivalence("{a;++b;}{c;++d;++e;}".asProgram, "{a;++b;}{{c;++d;}++e;}".asProgram) shouldBe 'proved
  }

  "Quiz checking" should "prove quiz 2" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/2/main.tex"))
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

  it should "prove quiz 10" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/10/main.tex"))
  }

  it should "prove quiz 11" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/11/main.tex"))
  }

  it should "prove quiz 14" in withZ3 { _ =>
    run(extractSolutions(QUIZ_PATH + "/14/main.tex"))
  }

  private def run(assessments: List[AssessmentProverInfo]): Unit = {
    forEvery (table(assessments)) { case (grader, args, sol, testSols, noSols) =>
      testSols.foreach(t => {
        println("Testing sol: " + t)
        val tic = System.nanoTime()
        AssessmentProver.check(t, sol, grader, args) shouldBe 'proved withClue t
        println("Successfully verified sol")
        val toc = System.nanoTime()
        (toc - tic) should be <= 5000000000L
      })
      noSols.foreach(t => {
        println("Testing no-sol: " + t)
        val tic = System.nanoTime()
        Try(AssessmentProver.check(t, sol, grader, args)).toOption.map(_ shouldNot be ('proved)) withClue t
        println("Successfully rejected no-sol")
        val toc = System.nanoTime()
        (toc - tic) should be <= 5000000000L
      })
    }
  }

  /** Extracts solutions (have, expected) from the resource ath `path`. */
  private def extractSolutions(path: String): List[AssessmentProverInfo] = {
    val content = resource.managed(io.Source.fromInputStream(getClass.getResourceAsStream(path), "UTF-8")).apply(_.mkString)
    AssessmentProverInfo.fromString(content)
  }

  private def table(infos: List[AssessmentProverInfo]) = {
    Table(("Method", "Args", "Sol", "TestSols", "NoSols"), infos.map(i => (i.grader, i.args, i.expected, i.testSols, i.noSols)):_*)
  }


}
