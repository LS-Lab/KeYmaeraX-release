package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.TacticInapplicableFailure
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.ParseException
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest.prop.TableDrivenPropertyChecks._

import org.scalatest.LoneElement._

class AssessmentProverTests extends TacticTestBase {

  object AssessmentProverInfo {
    private val GRADER = "grader"
    private val ARGS = "args"
    private val EXPR = "expr"
    private val ARG_NAME = "argName"
    private val ARG_VAL = "argVal"
    private val TURNSTILE = "==>"
    private val GOAL_SEP = ";;"

    private val EXTRACTOR = """\\sol\s*(?:\[(syneq|polyeq|qe|loop|dI)(?:\s*:\s*(\w+\s*=\s*"[^"]+")+)?\])?\s*\\kyxline\s*"([^"]+)"""".r(GRADER, ARGS, EXPR)
    private val ARG_SPLITTER = """(\w+)\s*=\s*"([^"]+)"""".r(ARG_NAME, ARG_VAL)

    def fromString(s: String): List[AssessmentProverInfo] = {
      val graderInfo = EXTRACTOR.findAllMatchIn(s).map(m => (Option(m.group(GRADER)), Option(m.group(ARGS)), m.group(EXPR)))
      val (infos, invalidInfos) = graderInfo.map({ case (grader, args, expr) =>
        try {
          val artifacts =
            if (expr.contains(TURNSTILE)) expr.split(GOAL_SEP).map(g => SequentArtifact(g.asSequent)).toList
            else List(ExpressionArtifact(expr.asExpr))
          //@todo alternate solutions
          Left(AssessmentProverInfo(grader, argsFromString(args), artifacts, artifacts))
        } catch {
          case ex: ParseException => Right((grader, args, expr, ex))
        }
      }).partition(_.isLeft)

      invalidInfos.map(_.right.get).foreach(i => System.err.println("Invalid \\sol: " + i))

      infos.map(_.left.get).toList
    }

    def argsFromString(args: Option[String]): Map[String, String] = {
      args.map(ARG_SPLITTER.findAllMatchIn).getOrElse(Iterator.empty).
        map(m => (m.group(ARG_NAME), m.group(ARG_VAL))).
        toMap
    }
  }

  abstract class Artifact
  case class ExpressionArtifact(expr: Expression) extends Artifact
  case class SequentArtifact(seq: Sequent) extends Artifact

  case class AssessmentProverInfo(grader: Option[String], args: Map[String, String], have: List[Artifact], expected: List[Artifact])

  private val COURSE_PATH: String = "/Course-current"
  private val QUIZ_PATH: String = COURSE_PATH + "/diderot/quiz"

  "Extractor" should "extract grading information" in {
    AssessmentProverInfo.fromString("""\sol \kyxline"x>=0"""") shouldBe
      List(AssessmentProverInfo(None, Map.empty, List(ExpressionArtifact("x>=0".asFormula)), List(ExpressionArtifact("x>=0".asFormula))))
    AssessmentProverInfo.fromString("""\sol[syneq] \kyxline"x>=0"""") shouldBe
      List(AssessmentProverInfo(Some("syneq"), Map.empty, List(ExpressionArtifact("x>=0".asFormula)), List(ExpressionArtifact("x>=0".asFormula))))
    AssessmentProverInfo.fromString("""\sol[polyeq: vars="x"] \kyxline"x>=0"""") shouldBe
      List(AssessmentProverInfo(Some("polyeq"), Map("vars"->"x"), List(ExpressionArtifact("x>=0".asFormula)), List(ExpressionArtifact("x>=0".asFormula))))
    AssessmentProverInfo.fromString("""\sol \kyxline"x>0 ==> x>=0 ;; y<0 ==> y<=0"""") shouldBe
      List(AssessmentProverInfo(None, Map.empty,
        List(SequentArtifact("x>0 ==> x>=0".asSequent), SequentArtifact("y<0 ==> y<=0".asSequent)),
        List(SequentArtifact("x>0 ==> x>=0".asSequent), SequentArtifact("y<0 ==> y<=0".asSequent))))
  }

  "Polynomial equality" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("2*x^2".asTerm, "x^2*2".asTerm) shouldBe 'proved
    AssessmentProver.polynomialEquality("x^3*y^2".asTerm, "y * x/1^2 * 4*x^2/2^2 * y".asTerm) shouldBe 'proved
    AssessmentProver.polynomialEquality("2*x^2".asTerm, "x^(1+3-2)*(3-1)/(-1+2)".asTerm) shouldBe 'proved
  }

  it should "prove quiz 2" in withZ3 { _ =>
    val solutions = extractSolutions(QUIZ_PATH + "/2/main.tex")
    forEvery (table(solutions)) { case (grader, args, ExpressionArtifact(have: Term)::Nil, ExpressionArtifact(expected: Term)::Nil) =>
      val tic = System.nanoTime()
      AssessmentProver.polynomialEquality(have, expected) shouldBe 'proved
      val toc = System.nanoTime()
      (toc-tic) should be <= 1000000000L
    }
  }

  it should "prove simple DI examples" in withZ3 { _ =>
    AssessmentProver.polynomialEquality("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [v':=w;][w':=-v;]2*v*v'+2*w*w'=0".asSequent) shouldBe 'proved
    AssessmentProver.polynomialEquality("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [w':=-v;][v':=w;]2*v*v'+2*w*w'=0".asSequent) shouldBe 'proved
    AssessmentProver.polynomialEquality("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> [w':=-v;]2*v*w+2*w*w'=0".asSequent) shouldBe 'proved
    AssessmentProver.polynomialEquality("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w-2*w*v=0".asSequent) shouldBe 'proved
    AssessmentProver.polynomialEquality("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w=2*w*v".asSequent) shouldBe 'proved
    the [TacticInapplicableFailure] thrownBy
      AssessmentProver.polynomialEquality("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w+2*w*v=0".asSequent) should
      have message "Terms not equal (by equating coefficients): 2*v*w+2*w*(-v)-0-0, 2*v*w+2*w*v-0"
    the [IllegalArgumentException] thrownBy
      AssessmentProver.polynomialEquality("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w<=2*w*v".asSequent) should
      have message "requirement failed: Same comparison operator expected, but got Equal vs. LessEqual"
    the [IllegalArgumentException] thrownBy
      AssessmentProver.polynomialEquality("==> [v':=w;][w':=-v;]2*v*v'+2*w*w'-0=0".asSequent, "==> 2*v*w<=2*w*v & 0=0".asSequent) should
      have message "Atomic comparison formulas expected, but got 2*v*w+2*w*(-v)-0=0, 2*v*w<=2*w*v&0=0"
  }

  it should "prove some of quiz 10" in withZ3 { _ =>
    val solutions = extractSolutions(QUIZ_PATH + "/10/main.tex")
    forEvery (table(solutions)) { case (grader, args, SequentArtifact(have) :: Nil, SequentArtifact(expected) :: Nil) =>
      //@todo filter
      AssessmentProver.polynomialEquality(have, expected) shouldBe 'proved
    }
  }

  it should "prove quiz 11" in withZ3 { _ =>
    val solutions = extractSolutions(QUIZ_PATH + "/11/main.tex")
    forEvery (table(solutions)) { case (grader, args, have, expected) =>
      have.zip(expected).foreach({
        case (ExpressionArtifact(h: ComparisonFormula), ExpressionArtifact(e: ComparisonFormula)) =>
          //@todo do we really want to check with polynomial equality as mentioned in 11/main.tex? allow stronger invariants?
          AssessmentProver.polynomialEquality(h, e) shouldBe 'proved
        case (ExpressionArtifact(h), ExpressionArtifact(e)) => h shouldBe e
      })
    }
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

  it should "prove quiz 4" in withZ3 { _ =>
    val solutions = extractSolutions(QUIZ_PATH + "/4/main.tex")
    forEvery (table(solutions)) { case (grader, args, ExpressionArtifact(have: Formula)::Nil, ExpressionArtifact(expected: Formula)::Nil) =>
      AssessmentProver.qeEquivalence(have, expected) shouldBe 'proved
    }
  }

  "Syntactic expression equality" should "prove quiz 5" in {
    val solutions = extractSolutions(QUIZ_PATH + "/5/main.tex")
    forEvery (table(solutions)) { case (grader, args, ExpressionArtifact(have)::Nil, ExpressionArtifact(expected)::Nil) =>
      AssessmentProver.syntacticEquality(have, expected) shouldBe true
    }
  }

  "Syntactic sequent equality" should "prove simple examples" in {
    AssessmentProver.syntacticEquality(List("x>0 ==> x>=0".asSequent), List("x>0 ==> x>=0".asSequent)) shouldBe true
    AssessmentProver.syntacticEquality(List("x>0,y>0 ==> x>=0".asSequent), List("y>0,x>0 ==> x>=0".asSequent)) shouldBe true
    AssessmentProver.syntacticEquality(List("x>0 ==> x>=0,y>0".asSequent), List("x>0 ==> y>0,x>=0".asSequent)) shouldBe true
    AssessmentProver.syntacticEquality(
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent),
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent)) shouldBe true
    AssessmentProver.syntacticEquality(
      List("y>0 ==> y>=0".asSequent, "x>0 ==> x>=0".asSequent),
      List("x>0 ==> x>=0".asSequent, "y>0 ==> y>=0".asSequent)) shouldBe false
  }

  it should "prove quiz 6" in withZ3 { _ =>
    val solutions = extractSolutions(QUIZ_PATH + "/6/main.tex")
    forEvery (table(solutions)) {
      case (grader, args, ExpressionArtifact(have)::Nil, ExpressionArtifact(expected)::Nil) =>
        AssessmentProver.syntacticEquality(have, expected) shouldBe true
      case (grader, args, have, expected) =>
        AssessmentProver.syntacticEquality(
          have.map({ case SequentArtifact(s) => s }),
          expected.map({ case SequentArtifact(s) => s})) shouldBe true
    }
  }

  "Loop invariant checker" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.loopInvCheck("==> x>2 & y>=1 -> [{x:=x+y; y:=y+2;}*]x>1".asSequent, "x>1 & y>=0".asFormula) shouldBe 'proved
    AssessmentProver.loopInvCheck("==> x>2 & y>=1 -> [{x:=y; {x'=y}}*]x>=1".asSequent, "x>=1 & y>=1".asFormula) shouldBe 'proved
    AssessmentProver.loopInvCheck("==> x=5 & c>1 & d>-c -> [{{x'=c+d}}*]x>=0".asSequent, "x>=1&c+d>=0".asFormula) shouldBe 'proved
    AssessmentProver.loopInvCheck("==> x=1 & y=2 -> [{x:=x+1; {x'=y, y'=2}}*]x>=0".asSequent, "x>=0&y>=0".asFormula) shouldBe 'proved
  }

  it should "prove quiz 7" in withZ3 { _ =>
    //@todo need question resource
  }

  "Differential invariant checker" should "prove simple examples" in withZ3 { _ =>
    AssessmentProver.dICheck(ODESystem("{x'=1,y'=2}".asDifferentialProgram), "2*x=y".asFormula) shouldBe 'proved
    AssessmentProver.dICheck(ODESystem("{x'=x,y'=-y}".asDifferentialProgram), "x*y=1".asFormula) shouldBe 'proved
    AssessmentProver.dICheck(ODESystem("{x'=-y,y'=x}".asDifferentialProgram), "x^2+y^2=1".asFormula) shouldBe 'proved
    AssessmentProver.dICheck(ODESystem("{x'=1,y'=2}".asDifferentialProgram), "3*x=y".asFormula).subgoals.loneElement shouldBe "3*x=y, true ==> 3*1=2".asSequent
  }

  it should "prove some of quiz 10" in withZ3 { _ =>
    //@todo need question resource
  }

  it should "prove quiz 11" in withZ3 { _ =>

  }

  /** Extracts solutions (have, expected) from the resource ath `path`. */
  private def extractSolutions(path: String): List[AssessmentProverInfo] = {
    val content = resource.managed(io.Source.fromInputStream(getClass.getResourceAsStream(path), "UTF-8")).apply(_.mkString)
    AssessmentProverInfo.fromString(content)
  }

  private def table(exprs: List[AssessmentProverInfo]) = {
    Table(("Method", "Args", "Have", "Expected"), exprs.map(i => (i.grader, i.args, i.have, i.expected)):_*)
  }


}
