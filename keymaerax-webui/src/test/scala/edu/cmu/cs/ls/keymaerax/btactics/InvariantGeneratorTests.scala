/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import java.io.{FileOutputStream, PrintWriter}
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.{AnnotationProofHint, PegasusProofHint}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, Parser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{ExtremeTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement
import edu.cmu.cs.ls.keymaerax.btactics.NonlinearExamplesTests._
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, SuccPosition}
import edu.cmu.cs.ls.keymaerax.tools.ext.{MathematicaInvGenTool, PlotConverter}
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import org.scalatest.{AppendedClues, PrivateMethodTester, Suites}
import org.scalatest.LoneElement._
import org.scalatest.exceptions.TestFailedDueToTimeoutException
import org.scalatest.time.{Seconds, Span}
import testHelper.KeYmaeraXTestTags.TodoTest

import scala.collection.immutable
import scala.collection.immutable.{IndexedSeq, Map, Nil}
import scala.collection.mutable.ListBuffer

/**
 * Tests invariant generators.
 * [[edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator]].
 */
@UsualTest
class InvariantGeneratorTests extends TacticTestBase with PrivateMethodTester {

  "Loop invariants" should "be generated from pre and postconditions" in withTactics {
    InvariantGenerator.loopInvariantGenerator("x>=1 ==> [{x:=x+1;}*][x:=x+1;]x>=2".asSequent, SuccPos(0), Declaration(Map.empty)).toList should
      contain theSameElementsInOrderAs(("x>=1".asFormula, None) :: ("[x:=x+1;]x>=2".asFormula, None) :: ("[x:=x+1;]x>=2 & x>=1".asFormula, None) :: Nil)
  }

  it should "be generated from unexpanded pre and postconditions" in withTactics {
    //@note no counter-example tool, so definitions don't need to be expanded
    InvariantGenerator.loopInvariantGenerator("init(x) ==> [{x:=x+1;}*][x:=x+1;]post(x)".asSequent, SuccPos(0), Declaration(Map.empty)).toList should
      contain theSameElementsInOrderAs(("init(x)".asFormula, None) :: ("[x:=x+1;]post(x)".asFormula, None) :: ("[x:=x+1;]post(x) & init(x)".asFormula, None) :: Nil)
  }

  it should "be generated from unexpanded pre and postconditions (with CEX tool for filtering)" in withMathematica { _ =>
    //@note counter-example tool needs to know what init and post are
    val defs = "init(.) ~> .>=1 & z=2 :: post(.) ~> .>=2".asDeclaration
    InvariantGenerator.loopInvariantGenerator("init(x) ==> [{x:=x+1;}*][x:=x+1;]post(x)".asSequent, SuccPos(0), defs).toList should
      contain theSameElementsInOrderAs(("x>=1".asFormula, None) :: ("[x:=x+1;]x>=2".asFormula, None) :: Nil)
  }

  it should "not include equivalent postcondition conjuncts if it has a counterexample tool" in withMathematica { _ =>
    //@todo some conjuncts are redundant
    InvariantGenerator.loopInvariantGenerator("x>=2 & x>=3 ==> [{x:=x+1;}*](x>=1 & x>=2 & y>=3)".asSequent, SuccPos(0), Declaration(Map.empty)).toList should
      contain theSameElementsInOrderAs(("x>=1".asFormula, None) :: ("x>=2".asFormula, None) :: ("x>=3".asFormula, None) ::
      ("x>=1 & x>=2 & y>=3 & x>=3".asFormula, None) :: ("x>=1 & x>=2 & y>=3".asFormula, None) :: Nil)
  }

  it should "not fail on missing counterexample tool" in withTactics {
    InvariantGenerator.loopInvariantGenerator("x>=2 & x>=3 ==> [{x:=x+1;}*](x>=1 & x>=2)".asSequent, SuccPos(0), Declaration(Map.empty)).toList should
      contain theSameElementsInOrderAs(("x>=1".asFormula, None) :: ("x>=2".asFormula, None) :: ("x>=3".asFormula, None) ::
        ("x>=1&x>=2&x>=3".asFormula, None) :: ("x>=1&x>=2".asFormula, None) :: Nil)
  }

  it should "not fail on non-FOL postcondition" in withMathematica { _ =>
    InvariantGenerator.loopInvariantGenerator("x>=1 ==> [{x:=x+1;}*][x:=x+1;]x>=2".asSequent, SuccPos(0), Declaration(Map.empty)).toList should
      contain theSameElementsAs(("[x:=x+1;]x>=2".asFormula, None) :: ("x>=1".asFormula, None) ::Nil)
  }

  it should "find an invariant for the runaround robot" in withMathematica { _ =>
    val s = """x!=ox | y!=oy ==>
                #  [{
                #    {?(x+w/-1-ox)^2+(y-v/-1-oy)^2!=v^2+w^2; om:=-1;
                #    ++ ?(x+w-ox)^2+(y-v-oy)^2!=v^2+w^2; om:=1;
                #    ++ ?(ox-x)*w!=(oy-y)*v; om:=0;}
                #    {x'=v,y'=w,v'=om*w,w'=-om*v}
                #   }*
                #  ] !(x=ox & y=oy)""".stripMargin('#').asSequent
    //@note precondition and postcondition are invariant
    InvariantGenerator.loopInvariantGenerator(s, SuccPos(0), Declaration(Map.empty)).toList should contain theSameElementsAs List(
      "x!=ox|y!=oy".asFormula -> None, "!(x=ox&y=oy)".asFormula -> None
    )
    proveBy(s, autoClose) shouldBe Symbol("proved")
  }

  "Differential counterexample generator" should "analyze a simple example" in withMathematica { t =>
    t.refuteODE(ODESystem("{x'=v}".asDifferentialProgram), List("x>=0".asFormula, "v>=0".asFormula), "x>=0".asFormula) shouldBe None
  }

  it should "find a counterexample in a simple example" in withMathematica { t =>
    t.refuteODE(ODESystem("{x'=v}".asDifferentialProgram), List("x>=0".asFormula), "x>=0".asFormula) shouldBe Some(
      Map("v".asNamedSymbol -> Number(-1), "x".asNamedSymbol -> Number(0))
    )
  }

  "Differential invariant generator" should "use Pegasus lazily" in withTactics {
    //@note pegasusInvariantGenerator asks ToolProvider.invGenTool

    def mockProvider(requestedInvGenerators: ListBuffer[Option[String]]): NoneToolProvider = new NoneToolProvider {
      override def invGenTool(name: Option[String]): Option[InvGenTool] = {
        requestedInvGenerators.append(name)
        super.invGenTool(name)
      }
    }

    val requestedInvGenerators: ListBuffer[Option[String]] = ListBuffer.empty
    ToolProvider.setProvider(mockProvider(requestedInvGenerators))

    val gen = InvariantGenerator.differentialInvariantGenerator("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0), Declaration(Map.empty))
    requestedInvGenerators shouldBe Symbol("empty")
    gen should not be Symbol("empty")
    gen.head shouldBe ("x>0".asFormula, None)
  }

  it should "use Pegasus lazily from ODE" in withTactics {
    // InvariantGenerator relevance filter tends to break this test
    def mockInvgen(requestedInvs: ListBuffer[ODESystem]): InvGenTool = new InvGenTool {
      override def invgen(ode: ODESystem, assumptions: immutable.Seq[Formula], postCond: Formula): immutable.Seq[Either[immutable.Seq[(Formula, String)], immutable.Seq[(Formula, String)]]] = {
        requestedInvs.append(ode)
        Nil
      }
      override def lzzCheck(ode: ODESystem, inv: Formula): Boolean = true
      override def refuteODE(ode: ODESystem, assumptions: immutable.Seq[Formula], postCond: Formula): Option[Map[NamedSymbol, Expression]] = None
      override def genODECond(ode: ODESystem, assumptions: immutable.Seq[Formula], postCond: Formula): (List[Formula],List[Formula]) = (Nil,Nil)
    }

    val requestedInvs: ListBuffer[ODESystem] = ListBuffer.empty
    ToolProvider.setProvider(new MathematicaToolProvider(ToolConfiguration.config("mathematica")) {
      override def invGenTool(name: Option[String]): Option[InvGenTool] = Some(mockInvgen(requestedInvs))
    })
    TactixLibrary.proveBy("x>0 -> [{x'=-x}]x>0".asFormula, implyR(1) & ODE(1)) shouldBe Symbol("proved")
    requestedInvs shouldBe Symbol("empty")
  }

  it should "not fail if Mathematica is unavailable" in withTactics {
    val gen = InvariantGenerator.pegasusInvariants("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0), Declaration(Map.empty))
    gen shouldBe Symbol("empty")
  }

  it should "use Pegasus if available" in withMathematica { _ =>
    val gen = InvariantGenerator.pegasusInvariants("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0), Declaration(Map.empty))
    gen should not be Symbol("empty")
    gen.head shouldBe ("true".asFormula, Some(PegasusProofHint(isInvariant = true, Some("PostInv"))))
  }

  it should "split formulas correctly" in withTactics {
    FormulaTools.leftConjuncts("(1=1&2=2)&3=3".asFormula, 1) should contain theSameElementsInOrderAs
      "(1=1&2=2)&3=3".asFormula :: Nil
    FormulaTools.leftConjuncts("(1=1&2=2)&3=3".asFormula, 2) should contain theSameElementsInOrderAs
      "1=1&2=2".asFormula :: "3=3".asFormula :: Nil
    FormulaTools.leftConjuncts("(1=1&2=2)&3=3".asFormula, 3) should contain theSameElementsInOrderAs
      "1=1".asFormula :: "2=2".asFormula :: "3=3".asFormula :: Nil
    FormulaTools.leftConjuncts("(1=1&2=2)&3=3".asFormula, -1) should contain theSameElementsInOrderAs
      "1=1".asFormula :: "2=2".asFormula :: "3=3".asFormula :: Nil
  }

  it should "not generate duplicate invariants" in withTactics {
    val s = "x>=0&x<=H(), g()>0, 1>=c(), c()>=0, x>=0&x=H()&v=0&g()>0&1>=c()&c()>=0 ==> [{x'=v,v'=-g()&x>=0}]((x=0->x>=0&x<=H())&(x!=0->x>=0&x<=H()))".asSequent
    invGenerator(s, SuccPos(0), Declaration(Map.empty)).toList.loneElement shouldBe ("v=0".asFormula, None)
  }

  it should "provide precondition as invariant candidate" in withTactics {
    val s = "x^2+y^2=2 ==> [{x'=-x,y'=-y}]x^2+y^2<=2".asSequent
    invGenerator(s, SuccPos(0), Declaration(Map.empty)).toList.loneElement shouldBe ("x^2+y^2=2".asFormula, None)
  }

  "Pegasus" should "FEATURE_REQUEST: generate invariants in correct order" taggedAs TodoTest in withMathematica { _ =>
    val s = "x=1, y=1/8 ==> [{x'=x-y^2, y'=y*(x-y^2)}]!(x<0)".asSequent
    //@note produces 8*y>=1, x*y>y^3, but 8*y>=1 only provable if we know x>y^2
    InvariantGenerator.pegasusInvariants(s, SuccPos(0), Declaration(Map.empty)).toList should contain theSameElementsInOrderAs
      List(
        "x*y>y^3".asFormula -> PegasusProofHint(isInvariant=true, None),
        "8*y>=1".asFormula -> PegasusProofHint(isInvariant=true, None),
        "x*y>y^3 & 8*y>=1".asFormula -> PegasusProofHint(isInvariant=true, None)
      )
  }

  it should "generate Darboux polynomials" in withMathematicaMatlab { _ =>
    val s =
      """x > -1, x < -3/4, y <= 3/2 & y >= 1
        |==>
        |[
        |  {x'=-42*x^7+50*x^2*y+156*x^3*y+258*x^4*y-46*x^5*y+68*x^6*y+20*x*y^6-8*y^7,
        |   y'=y*(1110*x^6-3182*x^4*y-220*x^5*y+478*x^3*y^3+487*x^2*y^4-102*x*y^5-12*y^6)}
        |] !(x > 1 + y)""".stripMargin.asSequent
    InvariantGenerator.pegasusInvariants(s, SuccPos(0), Declaration(Map.empty)).toList should contain theSameElementsInOrderAs List()
  }

  "Auto with invariant generator" should "prove simple loop from precondition invariant" in withQE { _ =>
    proveBy("x=0 -> [{x:=-x;}*]x>=0".asFormula, autoClose) shouldBe Symbol("proved")
  }

  it should "prove simple loop from postcondition invariant" in withQE { _ =>
    proveBy("x=1 -> [{x:=x+1;}*]x>=1".asFormula, autoClose) shouldBe Symbol("proved")
  }

  it should "discrete ghost on old(.) notation in ODE annotations" in withQE { tool =>
    //@note unprovable so that we can inspect the effect of the invariant generator
    val fastODE = PrivateMethod[DependentPositionTactic](Symbol("fastODE"))
    val s = "==> [{x'=3}@invariant(x>=old(x))]x>=0".asSequent
    val expectedInvs =
      if (tool.name == "Mathematica") List(
        ("x>=old(x)".asFormula, Some(AnnotationProofHint(tryHard = true))),
        ("true".asFormula, Some(PegasusProofHint(isInvariant = true, Some("PreNoImpPost")))))
      else List(("x>=old(x)".asFormula, Some(AnnotationProofHint(tryHard = true))))
    val invs = TactixLibrary.invGenerator("==> [{x'=3}]x>=0".asSequent, SuccPosition(1), Declaration(Map.empty))
    invs should contain theSameElementsInOrderAs expectedInvs
    //@note ODE will return with counterexample before even trying fastODE, so call fastODE directly
    proveBy(s, (DifferentialTactics invokePrivate fastODE(() => invs.iterator, skip))(1)).subgoals.
      loneElement shouldBe "x_0=x ==> [{x'=3 & true&x>=x_0}]x>=0".asSequent
  }

  "Configurable generator" should "return annotated conditional invariants" in withQE { tool =>
    // parse formula with invariant annotations to populate invariant generator
    "y>0 ==> [{x:=2; ++ x:=(-2);}{{y'=x*y}@invariant((y'=2*y -> y>=old(y)), (y'=(-2)*y -> y<=old(y)))}]y>0".asSequent
    def expectedInvs(inv: String) =
      if (tool.name == "Mathematica") List(
        (inv.asFormula, Some(AnnotationProofHint(tryHard = true))),
        ("true".asFormula, Some(PegasusProofHint(isInvariant = true, Some("PreNoImpPost")))))
      else List((inv.asFormula, Some(AnnotationProofHint(tryHard = true))))

    TactixLibrary.invGenerator("==> [{y'=2*y&true}]y>0".asSequent, SuccPosition(1), Declaration(Map.empty)) should contain theSameElementsInOrderAs expectedInvs("y>=old(y)")
    TactixLibrary.invGenerator("==> [{y'=(-2)*y&true}]y>0".asSequent, SuccPosition(1), Declaration(Map.empty)) should contain theSameElementsInOrderAs expectedInvs("y<=old(y)")
  }

  it should "FEATURE_REQUEST: return annotated conditional invariants with negated numbers" taggedAs TodoTest in withQE { tool =>
    // parse formula with invariant annotations to populate invariant generator
    "y>0 ==> [{x:=2; ++ x:=-2;}{{y'=x*y}@invariant((y'=2*y -> y>=old(y)), (y'=-2*y -> y<=old(y)))}]y>0".asSequent
    def expectedInvs(inv: String) =
      if (tool.name == "Mathematica") List(
        (inv.asFormula, Some(AnnotationProofHint(tryHard = true))),
        ("true".asFormula, Some(PegasusProofHint(isInvariant = true, Some("PreNoImpPost")))))
      else List((inv.asFormula, Some(AnnotationProofHint(tryHard = true))))

    TactixLibrary.invGenerator("==> [{y'=2*y&true}]y>0".asSequent, SuccPosition(1), Declaration(Map.empty)) should contain theSameElementsInOrderAs expectedInvs("y>=old(y)")
    //@todo does not find annotated invariant because -(2*y) does not unify with x*y
    TactixLibrary.invGenerator("==> [{y'=-2*y&true}]y>0".asSequent, SuccPosition(1), Declaration(Map.empty)) should contain theSameElementsInOrderAs expectedInvs("y<=old(y)")
  }

  "Pegasus" should "return trivial invariant postcondition result if sanity timeout > 0" in withMathematica { _ =>
    val seq = "x^2+y^2=2 ==> [{x'=-x,y'=-y}]x^2+y^2<=2".asSequent
    withTemporaryConfig(Map(Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0")) {
      InvariantGenerator.pegasusInvariants(seq, SuccPosition(1), Declaration(Map.empty)).toList should contain theSameElementsInOrderAs ("x^2+y^2<=2".asFormula -> Some(PegasusProofHint(isInvariant = true, None)) :: Nil)
    }
    withTemporaryConfig(Map(Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "5")) {
      InvariantGenerator.pegasusInvariants(seq, SuccPosition(1), Declaration(Map.empty)).toList should contain theSameElementsInOrderAs ("true".asFormula -> Some(PegasusProofHint(isInvariant = true, Some("PostInv")))) :: Nil
    }
  }

}

object NonlinearExamplesTests {
  private val GITHUB_PROJECTS_RAW_PATH = "https://raw.githubusercontent.com/LS-Lab/KeYmaeraX-projects/master/benchmarks"
}

@ExtremeTest
class NonlinearExamplesTests extends Suites(
  new NonlinearExamplesTester(
    "Nonlinear_",
    s"$GITHUB_PROJECTS_RAW_PATH/nonlinear.kyx",
    300,
    genCheck = true,
    keepUnverifiedCandidates = false)
)

@ExtremeTest
class NonlinearExamplesTester(val benchmarkName: String, val url: String, val timeout: Int,
                              val genCheck: Boolean, val keepUnverifiedCandidates: Boolean) extends TacticTestBase with AppendedClues {

  private val entries = {
    println("Reading " + url)
    try {
      DatabasePopulator.readKyx(url)
    } catch {
      case ex: Throwable =>
        println("Failed reading: " + ex.getMessage)
        ex.printStackTrace()
        Nil
    }
  }

  private def setTimeouts(tool: ToolOperationManagement)(testcode: => Any): Unit = {
    withTemporaryConfig(Map(
      Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true",
      Configuration.Keys.ODE_TIMEOUT_FINALQE -> "120",
      Configuration.Keys.ODE_USE_NILPOTENT_SOLVE -> "false",
      Configuration.Keys.Pegasus.INVGEN_TIMEOUT -> "125",
      Configuration.Keys.Pegasus.INVCHECK_TIMEOUT ->"0",
      Configuration.Keys.LOG_QE_DURATION -> "true")) {
      //@note do not set operation timeout here, it will defeat the Reap/Sow behavior of the invariant generator
      //tool.setOperationTimeout(120)
      testcode
    }
  }

  private val infoPrinter = (info: Any) => info match {
    case i: Map[String, Any] => i.values.mkString(",")
  }

  it should "output plots" ignore withMathematica { _ =>
    entries.foreach(e => {
      val (model, defs) = parseStripHints(e.model)
      println(edu.cmu.cs.ls.keymaerax.tools.qe.MathematicaOpSpec.string(e.name).toString + "\n" + PlotConverter(defs.exhaustiveSubst(model)).toString)
    })
  }

  it should "classification of problems" in withMathematica { tool => setTimeouts(tool) {
    val mPegasus = PrivateMethod[MathematicaInvGenTool](Symbol("mPegasus"))
    val pegasus = tool invokePrivate mPegasus()
    val classifications = entries.map(e => {
      val (model, defs) = parseStripHints(e.model)
      val expandedModel = defs.exhaustiveSubst(model)
      val Imply(assumptions, Box(ode: ODESystem, post)) = expandedModel
      e.name -> pegasus.problemClassification(ode, assumptions :: Nil, post)
    })
    val filename = "_classification.csv"
    val categories: List[(String, List[String])] = ("Boundedness" -> ("Initial Set" :: "Unsafe Set" :: "Evolution Constraint" :: Nil)) ::
      ("Algebraity" -> ("Precondition" :: "Postcondition" :: "Evolution Constraint" :: Nil)) ::
      ("Boolean Structure" -> ("Precondition" :: "Postcondition" :: "Evolution Constraint" :: Nil) ) ::
      ("Topology" -> ("Precondition" :: "Postcondition" :: "Evolution Constraint" :: Nil)) ::
      ("Space Boundedness" -> ("Time" :: Nil)) :: Nil
    val writer = new PrintWriter(benchmarkName + filename)
    val categoryHeadings = categories.map(_._1).mkString(",,,")
    val categorySubheadings = categories.map(_._2.mkString(",")).mkString(",")
    writer.write("Name,Dimension,Class," + categoryHeadings + "\r\n")
    writer.write(",,," + categorySubheadings + "\r\n")
    classifications.foreach({ case (name, (dimension, clazz, details)) =>
      val detailsString = categories.map({ case (key, subKeys) =>
        subKeys.map(details(key)(_)).mkString(",")
      }).mkString(",")
      writer.write(s"$name,$dimension,$clazz,$detailsString\r\n")
    })
    writer.close()
  }}

  it should "generate invariants with default DiffSat strategy" in withMathematicaMatlab { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "10",
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "30",
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "40",
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "false",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_saturate_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()

      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = true, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with DiffSat strategy and restricted maximum degrees" ignore withMathematicaMatlab { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "10",
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "30",
      Configuration.Keys.Pegasus.Darboux.DEGREE -> "2",
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "40",
      Configuration.Keys.Pegasus.Barrier.DEGREE -> "10",
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "false",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_saturate_restrictdegree_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()

      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = true, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with default DiffSat strategy, not using depedencies" in withMathematicaMatlab { tool => setTimeouts(tool) {
    // No Subsystem Splitting
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "10",
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "30",
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "40",
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "false",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "false",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_saturate_nodep_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()

      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = true, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with default DiffSat strategy, no cut minimize" in withMathematicaMatlab { tool => setTimeouts(tool) {
    // No Auto-Reduction
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "10",
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "30",
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "40",
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "false",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "false",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_saturate_nocutminimize_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()
      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {

          val result = robustRunInvGen(e.name, e.model, matlab = true, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with DiffSat strategy without heuristics" in withMathematicaMatlab { tool => setTimeouts(tool) {
    // No Heuristic Search
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "30",
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "15", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "15", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "40",
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "50",
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "false",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_saturate_noheuristics_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()
      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {

          val result = robustRunInvGen(e.name, e.model, matlab = true, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with default DiffSat strategy, and prove without proof hints" in withMathematicaMatlab { tool => setTimeouts(tool) {
    // No Proof Hints
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "10",
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "30",
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "40",
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "false",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_saturate_noproofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()

      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = true, stripProofHints = true, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with default DiffSat strategy and strict method timeouts" in withMathematicaMatlab { tool => setTimeouts(tool) {
    // No Budget Redistribution
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "10",
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "20",
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "10", /* half of FirstIntegrals (work on disjoint classes) */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "30",
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "40",
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_saturate_stricttimeouts.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()

      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = true, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with Barrier only" in withMathematicaMatlab { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.DEGREE -> "-1",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "120",
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_barrier_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()
      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = true, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with Darboux only (default max. degree)" in withMathematica { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "120",
      Configuration.Keys.Pegasus.Darboux.DEGREE -> "-1",
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_dbx_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()
      writer.close()
      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = false, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with invariant heuristics (summands) only" in withMathematica { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "120",
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_summands_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()
      writer.close()
      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = false, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  it should "generate invariants with first integrals only" in withMathematica { tool => setTimeouts(tool) {
    withTemporaryConfig(Map(
      Configuration.Keys.Pegasus.SANITY_TIMEOUT -> "0",
      Configuration.Keys.Pegasus.PreservedStateHeuristic.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.HeuristicInvariants.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.FirstIntegrals.TIMEOUT -> "120",
      Configuration.Keys.Pegasus.LinearFirstIntegrals.TIMEOUT -> "60", /* half of FirstIntegrals, work on disjoint classes */
      Configuration.Keys.Pegasus.LinearGenericMethod.TIMEOUT -> "60", /* half of FirstIntegrals, work on disjoint classes */
      Configuration.Keys.Pegasus.Darboux.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.Darboux.STAGGERED -> "false",
      Configuration.Keys.Pegasus.Barrier.TIMEOUT -> "0", /* disable */
      Configuration.Keys.Pegasus.DiffSaturation.MINIMIZE_CUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.STRICT_METHOD_TIMEOUTS -> "true",
      Configuration.Keys.Pegasus.DiffSaturation.USE_DEPENDENCIES -> "true",
      Configuration.Keys.Pegasus.InvariantExtractor.SUFFICIENCY_TIMEOUT -> "1",
      Configuration.Keys.Pegasus.InvariantExtractor.DW_TIMEOUT -> "1"
    )) {
      val filename = "_invgen_firstintegrals_proofhints.csv"
      val writer = new PrintWriter(benchmarkName + filename)
      writer.write(
        "Name,Status,Timeout[min],Duration total[ms],Duration QE[ms],Duration gen[ms],Duration check[ms],Proof Steps,Tactic Size,Info\r\n")
      writer.close()
      entries.foreach(e => {
        val writer = new PrintWriter(new FileOutputStream(benchmarkName + filename, true))
        try {
          val result = robustRunInvGen(e.name, e.model, matlab = false, stripProofHints = false, keepUnverifiedCandidates)
          writer.write(result.toCsv(infoPrinter) + "\r\n")
        } catch {
            case ex: Throwable => writer.write(s"${e.name} failed ${ex.getMessage}\r\n")
        } finally {
          writer.close()
        }
      })
    }
  }
  }

  private def pegasusGen(name: String, model: Formula, keepCandidates: Boolean, defs: Declaration) = {
    model match {
      case Imply(ante, succ@Box(_: ODESystem, _)) =>
        val seq = Sequent(IndexedSeq(ante), IndexedSeq(succ))
        println(s"Generating invariants $name")
        val invGenStart = System.currentTimeMillis()
        val candidates =
          if (keepCandidates) InvariantGenerator.pegasusCandidates(seq, SuccPos(0), defs).toList
          else InvariantGenerator.pegasusInvariants(seq, SuccPos(0), defs).toList
        val invGenEnd = System.currentTimeMillis()
        println(s"Done generating in ${invGenEnd-invGenStart}ms (${candidates.map(c => c._1.prettyString + " (proof hint " + c._2 + ")").mkString(",")}) $name")
        Some((candidates, invGenStart, invGenEnd))
      case _ => None
    }
  }

  /** Runs invGen with retry if it fails too fast. */
  private def robustRunInvGen(name: String, modelContent: String, matlab: Boolean, stripProofHints: Boolean, keepUnverifiedCandidates: Boolean): BenchmarkResult = {
    runInvGen(name, modelContent, matlab, stripProofHints, keepUnverifiedCandidates) match {
      case BenchmarkResult(_, "unfinished (gen)", _, duration, _, _, _, _, _, _, _) if duration <= 10000 =>
        //@HACK suspected test case separation: sometimes examples result in immediate $Aborted: restart the example
        runInvGen(name, modelContent, matlab, stripProofHints, keepUnverifiedCandidates)
      case r => r
    }
  }

  /** Runs invariant generation and checking on the model `name` with content `modelContent`.
    * @param matlab If true, initializes and restarts Matlab before the run, uses Mathematica otherwise.
    * @param stripProofHints If true, deletes proof hints from generated invariants, otherwise keeps proof hints.
    * @param keepUnverifiedCandidates If true, tries proving candidates that are marked false, otherwise discards them without proving. */
  private def runInvGen(name: String, modelContent: String, matlab: Boolean, stripProofHints: Boolean, keepUnverifiedCandidates: Boolean): BenchmarkResult = {
    if (genCheck) {
      // need to tear down and restart Mathematica because Pegasus caches ruin test separation
      Thread.sleep(1000) //@HACK suspected test case separation issue: allow Mathematica to start and stop
      afterEach()
      afterAll()
      Thread.sleep(1000)
      beforeAll()
      beforeEach()
      if (matlab) withMathematicaMatlab(_ => {}) //@HACK beforeEach and afterEach clean up tool provider
      else withMathematica(_ => {})
      Thread.sleep(1000)
      qeDurationListener.reset()
      val (model, defs) = parseStripHints(modelContent)
      val expandedModel = defs.exhaustiveSubst(model)

      try {
        pegasusGen(name, expandedModel, keepUnverifiedCandidates, defs) match {
          case Some((candidates, invGenStart, invGenEnd)) =>
            if (candidates.nonEmpty) {
              println(s"Checking $name with candidates " + candidates.map(_._1.prettyString).mkString(","))
              val pegasusInvariant = candidates.forall({
                case (_, Some(PegasusProofHint(isInvariant, _))) => isInvariant
                case _ => false
              })
              val strippedCandidates = if (stripProofHints) stripHints(candidates) else candidates
              TactixInit.invSupplier = FixedGenerator(List.empty) //@note invSupplier is for user-provided invariants
              TactixInit.differentialInvGenerator = FixedGenerator(strippedCandidates)
              val checkStart = System.currentTimeMillis()
              //val proof = proveBy(seq, TactixLibrary.master())
              try {
                val proof = failAfter(Span(timeout, Seconds)) { proveBy(expandedModel, implyR(1) & ODE(1)) }
                val checkEnd = System.currentTimeMillis()
                println(s"Done checking $name " + (if (proof.isProved) "(proved)" else "(unfinished)"))

                val result =
                  if (proof.isProved) "proved"
                  else if (proof.subgoals.exists(s => s.ante.isEmpty && s.succ.size == 1 && s.succ.head == False)) "disproved"
                  else "unfinished"
                BenchmarkResult(name, result, timeout, checkEnd - invGenStart,
                  qeDurationListener.duration, invGenEnd - invGenStart, checkEnd - checkStart, proof.steps, 1, None,
                  Map("dchainlength" -> (candidates.length-1, "pegasusInvariant" -> pegasusInvariant)))
              } catch {
                case ex: TestFailedDueToTimeoutException =>
                  println(s"Timeout checking $name")
                  BenchmarkResult(name, "timeout", timeout, -1, -1, -1, -1, -1, -1, Some(ex),
                    Map("dchainlength" -> (candidates.length-1, "pegasusInvariant" -> pegasusInvariant)))
              }
            } else {
              BenchmarkResult(name, "unfinished (gen)", timeout, invGenEnd - invGenStart, invGenEnd - invGenStart, -1, -1, 0, 1, None)
            }
          case None =>
            println("Skipping " + name + " for unknown shape, expected A -> [{x'=f(x)}]p(x), but got " + model.prettyString)
            BenchmarkResult(name, "skipped", timeout, -1, -1, -1, -1, -1, -1, None)
        }
      } catch {
        case ex: TestFailedDueToTimeoutException => BenchmarkResult(name, "timeout", timeout,
          -1, qeDurationListener.duration, -1, -1, -1, -1, Some(ex))
        case ex: Throwable =>
          ex.printStackTrace()
          BenchmarkResult(name, "failed", timeout, -1, qeDurationListener.duration, -1, -1, -1, -1, Some(ex))
      }
    } else {
      BenchmarkResult(name, "skipped", timeout, -1, -1, -1, -1, -1, -1, None)
    }
  }

  /** Parse model but ignore all proof hints. */
  private def parseStripHints(modelContent: String): (Formula, Declaration) = {
    TactixInit.invSupplier = FixedGenerator(Nil)
    TactixInit.differentialInvGenerator = FixedGenerator(Nil)
    Parser.parser.setAnnotationListener((_: Program, _: Formula) => {})
    val entry = ArchiveParser.parser(modelContent).head
    (entry.model.asInstanceOf[Formula], entry.defs)
  }

  /** Removes all proof hints from invariant candidates and merges diff-cut chains into a single simplified formula. */
  private def stripHints(candidates: List[(Formula, Option[InvariantGenerator.ProofHint])]): List[(Formula, Option[InvariantGenerator.ProofHint])] = {
    // strip hints and merge diff cut chain
    val stripMerged = candidates.map(_._1).reduce(And)
    val simplified = SimplifierV3.formulaSimp(stripMerged, immutable.HashSet.empty, SimplifierV3.defaultFaxs, SimplifierV3.defaultTaxs)._1
    (simplified, None) :: Nil
  }

}
