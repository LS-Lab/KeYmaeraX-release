package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{DependentPositionTactic, PosInExpr, TheType}
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.ModelPlex.createMonitorSpecificationConjecture
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest
import testHelper.ParserFactory._

import scala.language.postfixOps

/**
 * Created by smitsch on 3/8/15.
 *
 * @author Stefan Mitsch
 * @author Ran Ji
 */
@SlowTest
class ModelplexTacticTests extends TacticTestBase {

  def monitorSize(f: Formula): Int = {
    var numOperators = 0
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case _ => numOperators += 1; Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case _: Variable => Left(None)
        case Number(_) => Left(None)
        case FuncOf(_, _) => Left(None)
        case Nothing => Left(None)
        case _ => numOperators += 1; Left(None)
      }
    }, f)
    numOperators
  }

//  def numSteps(n: Provable): Int = if (n.subgoals.nonEmpty) n.subgoals.map(numSteps).min else 0
//  def numSteps(s: ProofStep): Int = if (s.subgoals.nonEmpty) 1 + s.subgoals.map(numSteps).sum else 1
//
//  def numBranches(n: ProofNode): Int = if (n.children.nonEmpty) n.children.map(numBranches).min else 0
//  def numBranches(s: ProofStep): Int = if (s.subgoals.nonEmpty) s.subgoals.map(numBranches).sum else 1

  def report(result: Formula, proof: ProvableSig, name: String) = {
    println(s"$name monitor size: " + monitorSize(result))
//    println("Number of proof steps: " + numSteps(proof))
//    println("Number of branches (open/all): " + proof.subgoals.size + "/" + numBranches(proof))
  }

  "Simple modelplex" should "chase: find correct controller monitor by updateCalculus implicationally" in {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/simple.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model, Variable("x"))

    def modelPlex: DependentPositionTactic = chase(3, 3, (e:Expression) => e match {
      // no equational assignments
      case Box(Assign(_, _), _) => "[:=] assign" :: "[:=] assign update" :: Nil
      case Diamond(Assign(_, _), _) => "<:=> assign" :: "<:=> assign update" :: Nil
      // remove loops
      case Diamond(Loop(_), _) => "<*> approx" :: Nil
      // remove ODEs for controller monitor
      case Diamond(ODESystem(_, _), _) => "DX diamond differential skip" :: Nil
      case _ => AxiomIndex.axiomsFor(e)
    })

    val result = TactixLibrary.proveBy(modelplexInput, modelPlex(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "xpost()=1".asFormula
  }

  it should "chase away a loop by updateCalculus implicationally" in {
    val model = KeYmaeraXProblemParser("ProgramVariables. R x. End. Problem. 0 <= x -> [{x:=2;}*](0 <= x) End.")
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model, Variable("x"))

    def modelPlex: DependentPositionTactic = chase(3, 3, (e:Expression) => e match {
      case Diamond(Loop(_), _) => "<*> approx" :: Nil
      case _ => AxiomIndex.axiomsFor(e)
    })

    val result = proveBy(modelplexInput, modelPlex(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "xpost()=2".asFormula
  }

//  "Watertank modelplex" should "find correct controller monitor condition" in {
//    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-ctrl.key"))
//    val tactic = locateSucc(modelplexSequentStyle)
//    val result = helper.runTactic(tactic, new RootNode(s))
//    result.openGoals() should have size 2
//    result.openGoals()(0).sequent.ante should contain only ("0<=x".asFormula, "x<=m".asFormula, "0<ep".asFormula)
//    result.openGoals()(0).sequent.succ should contain only "-1<=fpost_0() & fpost_0()<=(m-x)/ep".asFormula
//    result.openGoals()(1).sequent.ante should contain only ("0<=x".asFormula, "x<=m".asFormula, "0<ep".asFormula, "-1<=fpost_0()".asFormula, "fpost_0()<=(m-x)/ep".asFormula)
//    result.openGoals()(1).sequent.succ should contain only "tpost_0()=0 & (fpost()=fpost_0() & xpost()=x & tpost()=tpost_0())".asFormula
//  }
//
  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("f"), Variable("l"), Variable("c"))

    val foResult = TactixLibrary.proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists f ((-1<=f&f<=(m-l)/ep)&(0<=l&0<=ep)&fpost()=f&lpost()=l&cpost()=0)".asFormula

    // Opt. 1
    val opt1Result = TactixLibrary.proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "(-1<=fpost()&fpost()<=(m-l)/ep)&(0<=l&0<=ep)&fpost()=fpost()&lpost()=l&cpost()=0".asFormula

    report(opt1Result.subgoals.head.succ.head, opt1Result, "Water tank controller monitor (forward chase)")

    // Cleanup
//    val finalResult = proveBy(opt1Result.subgoals.head.succ.head, chase(3,3)(1))
//    finalResult.subgoals should have size 1
//    finalResult.subgoals.head.ante shouldBe empty
//    finalResult.subgoals.head.succ should contain only "(-1<=fpost()&fpost()<=(m-l)/ep)&(0<=l&0<=ep) & lpost()=l & cpost()=0".asFormula
  }

  it should "find correct model monitor condition" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("f"), Variable("l"), Variable("c"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    //@todo can steer result depending on where and when we use partial QE
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=false)(ModelPlex.modelMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(tool, assumptions)(1) & simplifier(1)
    val result = proveBy(modelplexInput, tactic)

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "(-1<=fpost()&fpost()<=(m-l)/ep)&(0=cpost()&(lpost()=l&(fpost() < 0&(0=ep&l>=0|ep>0&l>=0)|(ep>=0&l>=0)&fpost()>0)|((fpost()=0&l=lpost())&ep>=0)&l>=0)|(cpost()>0&ep>=cpost())&(l>=0&(fpost()=0&l=lpost()|lpost()=cpost()*fpost()+l&fpost()>0)|(lpost()=cpost()*fpost()+l&fpost() < 0)&cpost()*fpost()+l>=0))".asFormula
  }

  it should "find correct model monitor condition by chase" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("f"), Variable("l"), Variable("c"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val tactic = ModelPlex.modelMonitorByChase(1) & ModelPlex.optimizationOneWithSearch(tool, assumptions)(1) & simplifier(1)
    val result = proveBy(modelplexInput, tactic)

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "(-1<=fpost()&fpost()<=(m-l)/ep)&(0=cpost()&(lpost()=l&(fpost() < 0&(0=ep&l>=0|ep>0&l>=0)|(ep>=0&l>=0)&fpost()>0)|((fpost()=0&l=lpost())&ep>=0)&l>=0)|(cpost()>0&ep>=cpost())&(l>=0&(fpost()=0&l=lpost()|lpost()=cpost()*fpost()+l&fpost()>0)|(lpost()=cpost()*fpost()+l&fpost() < 0)&cpost()*fpost()+l>=0))".asFormula
  }

  "Watertank modelplex in place" should "find correct controller monitor condition with Optimization 1" in {
    val s = KeYmaeraXProblemParser(
      io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank-ctrl.key")).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(s, tactic)

    // with ordinary diamond test
    val expected = "(-1<=fpost_0()&fpost_0()<=(m-x)/ep)&fpost()=fpost_0()&xpost()=x&tpost()=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expected

    report(expected, result, "Watertank controller monitor (backward tactic)")
  }

  it should "find correct controller monitor condition from model file" ignore {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model, Variable("f"), Variable("l"), Variable("c"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)('R)
    val result = proveBy(modelplexInput, tactic)

    val expected = "(-1<=fpost_0()&fpost_0()<=(m-l)/ep)&(0<=l&0<=ep)&(fpost()=fpost_0()&lpost()=l)&cpost()=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expected

    report(expected, result, "Watertank controller monitor (backward tactic)")
  }

  it should "find correct controller monitor condition without intermediate Optimization 1" in {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank-ctrl.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=false)(ModelPlex.controllerMonitorT)(1) & ModelPlex.optimizationOne()(1)
    val result = proveBy(model, tactic)

    // with ordinary diamond test
    val expected = "(-1<=fpost_0()&fpost_0()<=(m-x)/ep)&fpost()=fpost_0()&xpost()=x&tpost()=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expected

    report(expected, result, "Watertank controller monitor (backward tactic)")
  }

  it should "work using the command line interface" taggedAs IgnoreInBuildTest in {
    // command line main has to initialize the prover itself, so dispose all test setup first
    afterEach()

    val inputFileName = "keymaerax-webui/src/test/resources/examples/casestudies/modelplex/watertank/watertank.key"
    val vars = "f,l,c"
    val outputFileName = File.createTempFile("watertank", ".kym").getAbsolutePath
    KeYmaeraX.main(Array("-tool", "mathematica", "-modelplex", inputFileName, "-vars", vars, "-monitorKind", "ctrl", "-out", outputFileName))

    val expectedFileContent = "(-1<=fpost()&fpost()<=(m-l)/ep)&(0<=l&0<=ep)&lpost()=l&cpost()=0".asFormula

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    KeYmaeraXParser(actualFileContent) shouldBe expectedFileContent
  }

//
//  ignore should "find correct model monitor condition" in {
//    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
//    val tactic = modelplexAxiomaticStyle(useOptOne=true)(modelMonitorT)(SuccPosition(0))
//    val result = helper.runTactic(tactic, new RootNode(s))
//
//    // with diamond test, after local QE
//    val expected = "-1<=fpost_0()&fpost_0()<=(m-l)/ep&(cpost_0()=0&(ep=cpost()&(l=0&(tpost_0()=0&(cpost_0()=ep&(fpost_0() < 0&(fpost()=fpost_0()&lpost()=0)|(fpost_0()=0&(fpost()=0&lpost()=0)|fpost_0()>0&(fpost()=fpost_0()&lpost()=0))))|tpost_0()>0&(cpost_0()=-1*tpost_0()+ep&(fpost_0()=0&(fpost()=0&lpost()=0)|fpost_0()>0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()))))|l>0&(tpost_0()=0&(cpost_0()=ep&(fpost_0() < 0&(fpost()=fpost_0()&lpost()=l)|(fpost_0()=0&(fpost()=0&lpost()=l)|fpost_0()>0&(fpost()=fpost_0()&lpost()=l))))|tpost_0()>0&(cpost_0()=-1*tpost_0()+ep&(-1*tpost_0()^-1*l<=fpost_0()&fpost_0() < 0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()+l)|(fpost_0()=0&(fpost()=0&lpost()=l)|fpost_0()>0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()+l))))))|ep>cpost()&(l=0&(tpost_0()=0&(cpost_0()=cpost()&(fpost_0() < 0&(fpost()=fpost_0()&lpost()=0)|(fpost_0()=0&(fpost()=0&lpost()=0)|fpost_0()>0&(fpost()=fpost_0()&lpost()=0))))|tpost_0()>0&(cpost_0()=cpost()+-1*tpost_0()&(fpost_0()=0&(fpost()=0&lpost()=0)|fpost_0()>0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()))))|l>0&(tpost_0()=0&(cpost_0()=cpost()&(fpost_0() < 0&(fpost()=fpost_0()&lpost()=l)|(fpost_0()=0&(fpost()=0&lpost()=l)|fpost_0()>0&(fpost()=fpost_0()&lpost()=l))))|tpost_0()>0&(cpost_0()=cpost()+-1*tpost_0()&(-1*tpost_0()^-1*l<=fpost_0()&fpost_0() < 0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()+l)|(fpost_0()=0&(fpost()=0&lpost()=l)|fpost_0()>0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()+l))))))))".asFormula
//
//    result.openGoals() should have size 1
//    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=l & l<=m & 0<ep".asFormula
//    result.openGoals().flatMap(_.sequent.succ) should contain only expected
//
//    report(expected, result, "Watertank model")
//  }
//
//  ignore should "find correct model monitor condition without intermediate Optimization 1" in {
//    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
//    val tactic = modelplexAxiomaticStyle(useOptOne=false)(modelMonitorT)(SuccPosition(0)) &
//      (optimizationOne()(SuccPosition(0))*)
//    val result = helper.runTactic(tactic, new RootNode(s))
//
//    // with diamond test, after local QE
//    val expected = "-1<=f&f<=(m-l)/ep&(f()=f&(c_1=0&(t>=0&(((c_1<ep&(t<0|((t=0&l>=0)|(0<t&t<=-1*c_1+ep&(l>=0&f()>=-1*l*t^-1)))))|((c_1=ep&(t<0|(t=0&l>=0)))|(c_1>ep&t<0)))&(f_post=f()&l_post=t*f()+l&c_post=1*t+c_1)))))".asFormula
//
//    result.openGoals() should have size 1
//    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=l & l<=m & 0<ep".asFormula
//    result.openGoals().flatMap(_.sequent.succ) should contain only expected
//
//    report(expected, result, "Watertank model")
//  }
//
  "Local lane control modelplex in place" should "find correct controller monitor condition" ignore {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc-ctrl.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)('R)
    val result = proveBy(model, tactic)

    // with ordinary diamond test
    val expected = "(-B<=alpost_0()&alpost_0()<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&(-B<=afpost_0()&afpost_0()<=A)&xfpost()=xf&vfpost()=vf&afpost()=afpost_0()&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0|vf=0&xfpost()=xf&vfpost()=vf&afpost()=0&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0|(-B<=afpost_0()&afpost_0()<=-b)&xfpost()=xf&vfpost()=vf&afpost()=afpost_0()&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0)".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only
      "xf < xl & xf + vf^2/(2*b) < xl + vl^2/(2*B) & B >= b & b > 0 & vf >= 0 & vl >= 0 & A >= 0 & ep > 0".asFormula
    result.subgoals.head.succ should contain only expected

    report(expected, result, "Local lane controller (backward tactic)")
  }
//
//  ignore should "find correct controller monitor condition without intermediate Optimization 1" in {
//    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key"))
//    val tactic = modelplexAxiomaticStyle(useOptOne=false)(controllerMonitorT)(SuccPosition(0)) &
//      (optimizationOne()(SuccPosition(0))*)
//    val result = helper.runTactic(tactic, new RootNode(s))
//
//    // with ordinary diamond test
//    val expected = ("-B<=alpost_0() & alpost_0()<=A & " +
//      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
//      "(-B<=afpost_0()&afpost_0()<=A&(xfpost()=xf&vfpost()=vf&afpost()=afpost_0()&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0))) | " +
//      "((vf=0&(xfpost()=xf&vfpost()=vf&afpost()=0&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0)) | " +
//      "(-B<=afpost_0()&afpost_0()<=-b&(xfpost()=xf&vfpost()=vf&afpost()=afpost_0()&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0))))").asFormula
//
//    result.openGoals() should have size 1
//    result.openGoals().flatMap(_.sequent.ante) should contain only
//      "xf < xl & xf + vf^2/(2*b) < xl + vl^2/(2*B) & B >= b & b > 0 & vf >= 0 & vl >= 0 & A >= 0 & ep > 0".asFormula
//    result.openGoals().flatMap(_.sequent.succ) should contain only expected
//
//    report(expected, result, "LLC controller monitor (backward tactic, from pre-fabricated conjecture)")
//  }
//
  it should "find correct controller monitor from model" ignore {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model,
      Variable("xl"), Variable("vl"), Variable("al"), Variable("xf"), Variable("vf"), Variable("af"), Variable("t"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(modelplexInput, tactic)

    val expected = "(-B<=alpost_0()&alpost_0()<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&(-B<=afpost_0()&afpost_0()<=A)&(vf>=0&vl>=0&0<=ep)&(((((xlpost()=xl&vlpost()=vl)&alpost()=alpost_0())&xfpost()=xf)&vfpost()=vf)&afpost()=afpost_0())&tpost()=0|vf=0&(vf>=0&vl>=0&0<=ep)&(((((xlpost()=xl&vlpost()=vl)&alpost()=alpost_0())&xfpost()=xf)&vfpost()=vf)&afpost()=0)&tpost()=0|(-B<=afpost_0()&afpost_0()<=-b)&(vf>=0&vl>=0&0<=ep)&(((((xlpost()=xl&vlpost()=vl)&alpost()=alpost_0())&xfpost()=xf)&vfpost()=vf)&afpost()=afpost_0())&tpost()=0)".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "true".asFormula
    result.subgoals.head.succ should contain only expected

    report(expected, result, "LLC controller monitor (backward tactic)")
  }

  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xl"), Variable("vl"), Variable("al"), Variable("xf"), Variable("vf"), Variable("af"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists al ((-B<=al&al<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&\\exists af ((-B<=af&af<=A)&(vf>=0&vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&alpost()=al&xfpost()=xf&vfpost()=vf&afpost()=af&tpost()=0)|vf=0&(vf>=0&vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&alpost()=al&xfpost()=xf&vfpost()=vf&afpost()=0&tpost()=0|\\exists af ((-B<=af&af<=-b)&(vf>=0&vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&alpost()=al&xfpost()=xf&vfpost()=vf&afpost()=af&tpost()=0)))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "(-B<=alpost()&alpost()<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&(-B<=afpost()&afpost()<=A)&(vf>=0&vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&alpost()=alpost()&xfpost()=xf&vfpost()=vf&afpost()=afpost()&tpost()=0|vf=0&(vf>=0&vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&alpost()=alpost()&xfpost()=xf&vfpost()=vf&afpost()=0&tpost()=0|(-B<=afpost()&afpost()<=-b)&(vf>=0&vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&alpost()=alpost()&xfpost()=xf&vfpost()=vf&afpost()=afpost()&tpost()=0)".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "(-B<=alpost()&alpost()<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&(-B<=afpost()&afpost()<=A)&(vf>=0&vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&xfpost()=xf&vfpost()=vf&tpost()=0|vf=0&(vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&xfpost()=xf&vfpost()=0&afpost()=0&tpost()=0|(-B<=afpost()&afpost()<=-b)&(vf>=0&vl>=0&0<=ep)&xlpost()=xl&vlpost()=vl&xfpost()=xf&vfpost()=vf&tpost()=0)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "LLC controller monitor (forward chase)")
  }

  "Fixedwing" should "find correct controller monitor" in withMathematica { implicit tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fixedwing_simple_nobound.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("a"), Variable("w"), Variable("xo"), Variable("theta"), Variable("dxy"), Variable("y"), Variable("t"), Variable("v"), Variable("dx"), Variable("w"), Variable("yo"), Variable("dz"), Variable("x"), Variable("dy"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "(v=Vmin&(theta=Theta&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=0&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=0&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|theta=-Theta&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=0&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=0&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(0<=theta&theta < Theta)&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=0&wpost()=W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=W&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(-Theta < theta&theta < 0)&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=0&wpost()=-W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=-W&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy)|v>Vmin&(theta=Theta&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=-B&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=0&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|theta=-Theta&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=-B&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=0&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(0<=theta&theta < Theta)&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=-B&wpost()=W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=W&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(-Theta < theta&theta < 0)&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=-B&wpost()=-W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=-W&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy))|\\exists a ((-B<=a&a<=A)&\\exists w ((-W<=w&w<=W)&\\exists v (v>=Vmin&\\exists theta ((-Theta<=theta&theta<=Theta)&\\exists xo \\exists yo ((abs(x-xo)>(v^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v)&abs(x-xo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v)+Vmin*ep|abs(y-yo)>(v^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*v)&abs(y-yo)>(v^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(theta))/W-(v-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*v)+Vmin*ep)&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=a&wpost()=w&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=w&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy)))))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "(v=Vmin&(theta=Theta&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=0&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=0&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|theta=-Theta&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=0&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=0&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(0<=theta&theta < Theta)&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=0&wpost()=W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=W&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(-Theta < theta&theta < 0)&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=0&wpost()=-W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=-W&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy)|v>Vmin&(theta=Theta&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=-B&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=0&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|theta=-Theta&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=-B&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=0&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(0<=theta&theta < Theta)&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=-B&wpost()=W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=W&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(-Theta < theta&theta < 0)&((!theta=Theta|dxy=dXY&dz=dZ)&(!theta=-Theta|dxy=-dXY&dz=dZ))&(0<=ep&v>=Vmin&-Theta<=theta&theta<=Theta)&apost()=-B&wpost()=-W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&wpost()=-W&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy))|(-B<=apost()&apost()<=A)&(-W<=wpost()&wpost()<=W)&vpost()>=Vmin&(-Theta<=thetapost()&thetapost()<=Theta)&(abs(x-xopost())>(vpost()^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*vpost())&abs(x-xopost())>(vpost()^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(thetapost()))/W-(vpost()-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*vpost())+Vmin*ep|abs(y-yopost())>(vpost()^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*vpost())&abs(y-yopost())>(vpost()^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(thetapost()))/W-(vpost()-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*vpost())+Vmin*ep)&(0<=ep&vpost()>=Vmin&-Theta<=thetapost()&thetapost()<=Theta)&apost()=apost()&wpost()=wpost()&xopost()=xopost()&thetapost()=thetapost()&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=vpost()&dxpost()=dx&wpost()=wpost()&yopost()=yopost()&dzpost()=dz&xpost()=x&dypost()=dy".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "(v=Vmin&(theta=Theta&((dxy=dXY&dz=dZ)&(theta!=-Theta|dxy=-dXY))&(0<=ep&-Theta<=theta)&apost()=0&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|theta=-Theta&((theta!=Theta|dxy=dXY&dz=dZ)&dxy=-dXY&dz=dZ)&(0<=ep&theta<=Theta)&apost()=0&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(0<=theta&theta < Theta)&(theta!=-Theta|dxy=-dXY&dz=dZ)&(0<=ep&-Theta<=theta)&apost()=0&wpost()=W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(-Theta < theta&theta < 0)&(theta!=Theta|dxy=dXY&dz=dZ)&(0<=ep&theta<=Theta)&apost()=0&wpost()=-W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy)|v>Vmin&(theta=Theta&((dxy=dXY&dz=dZ)&(theta!=-Theta|dxy=-dXY))&(0<=ep&-Theta<=theta)&apost()=-B&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|theta=-Theta&((theta!=Theta|dxy=dXY&dz=dZ)&dxy=-dXY&dz=dZ)&(0<=ep&theta<=Theta)&apost()=-B&wpost()=0&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(0<=theta&theta < Theta)&(theta!=-Theta|dxy=-dXY&dz=dZ)&(0<=ep&-Theta<=theta)&apost()=-B&wpost()=W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy|(-Theta < theta&theta < 0)&(theta!=Theta|dxy=dXY&dz=dZ)&(0<=ep&theta<=Theta)&apost()=-B&wpost()=-W&xopost()=xo&thetapost()=theta&dxypost()=dxy&ypost()=y&tpost()=0&vpost()=v&dxpost()=dx&yopost()=yo&dzpost()=dz&xpost()=x&dypost()=dy))|(-B<=apost()&apost()<=A)&(-W<=wpost()&wpost()<=W)&vpost()>=Vmin&(-Theta<=thetapost()&thetapost()<=Theta)&(abs(x-xopost())>(vpost()^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*vpost())&abs(x-xopost())>(vpost()^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(thetapost()))/W-(vpost()-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*vpost())+Vmin*ep|abs(y-yopost())>(vpost()^2-Vmin^2)/(2*B)+2*r+(A/B+1)*(A/2*ep^2+ep*vpost())&abs(y-yopost())>(vpost()^2-Vmin^2)/(2*B)+Vmin*((Theta-abs(thetapost()))/W-(vpost()-Vmin)/B)+2*r+(A/B+1)*(A/2*ep^2+ep*vpost())+Vmin*ep)&0<=ep&dxypost()=dxy&ypost()=y&tpost()=0&dxpost()=dx&dzpost()=dz&xpost()=x&dypost()=dy".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "Fixedwing controller monitor (forward chase)")
  }

  // works but is super-slow (46min vs. 2s next with chase)
  "ETCS safety lemma modelplex in place" should "find correct controller monitor condition" ignore {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/icfem08/safetylemma-ctrl.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=false)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(model, tactic)
    result.subgoals should have size 1
    result.subgoals.head.succ should have size 1

    report(result.subgoals.head.succ.head, result, "ETCS controller")
  }

//
//  ignore should "find correct controller monitor condition from model" in {
//    val in = getClass.getResourceAsStream("examples/casestudies/modelplex/icfem08/safetylemma.key")
//    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val modelplexInput = createMonitorSpecificationConjecture(model, Variable("vdes"), Variable("SB"), Variable("v"),
//      Variable("state"), Variable("do"), Variable("z"), Variable("t"), Variable("mo"), Variable("m"), Variable("d"),
//      Variable("a"))
//
//    val tactic = modelplexAxiomaticStyle(useOptOne=false)(controllerMonitorT)(1)
//    val result = proveUncheckedBy(modelplexInput, tactic)
//
//    result.openGoals() should have size 1
//    result.openGoals().head.sequent.ante should contain only "true".asFormula
//    result.openGoals().head.sequent.succ should contain only "".asFormula
//
//    report(result.openGoals().head.sequent.succ.head, result, "ETCS controller monitor (backward tactic)")
//  }
//

  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/icfem08/safetylemma.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("vdes"), Variable("SB"), Variable("v"),
      Variable("state"), Variable("do"), Variable("z"), Variable("t"), Variable("mo"), Variable("m"), Variable("d"),
      Variable("a"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "(\\forall do (do=d->\\forall mo (mo=m->\\exists m \\exists d \\exists vdes ((d>=0&do^2-d^2<=2*b*(m-mo)&vdes>=0)&vdespost()=vdes&SBpost()=SB&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=t&mopost()=mo&mpost()=m&dpost()=d&apost()=a)))|vdespost()=vdes&SBpost()=SB&vpost()=v&statepost()=brake&dopost()=do&zpost()=z&tpost()=t&mopost()=mo&mpost()=m&dpost()=d&apost()=a)|v<=vdes&\\exists a ((a>=-b&a<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=a))|v>=vdes&\\exists a ((a < 0&a>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=a))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&vdespost()=vdespost()&SBpost()=SB&vpost()=v&statepost()=state&dopost()=d&zpost()=z&tpost()=t&mopost()=m&mpost()=mpost()&dpost()=dpost()&apost()=a|vdespost()=vdes&SBpost()=SB&vpost()=v&statepost()=brake&dopost()=do&zpost()=z&tpost()=t&mopost()=mo&mpost()=m&dpost()=d&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=apost())|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=apost())".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&SBpost()=SB&vpost()=v&statepost()=state&dopost()=d&zpost()=z&tpost()=t&mopost()=m&apost()=a|vdespost()=vdes&SBpost()=SB&vpost()=v&statepost()=brake&dopost()=do&zpost()=z&tpost()=t&mopost()=mo&mpost()=m&dpost()=d&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b|(m-z>(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&state!=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|state=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b|(m-z>(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&state!=brake)&(v>=0&0<=ep)&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v&statepost()=state&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "ETCS controller monitor (forward chase)")
  }

  "RSS passive safety modelplex in place" should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists dxo \\exists dyo (dxo^2+dyo^2<=V^2&((0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0|v=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=0&rpost()=r&tpost()=0|\\exists a ((-B<=a&a<=A)&\\exists r (r!=0&\\exists w (w*r=v&\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yo)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=a&rpost()=r&tpost()=0))))))".asFormula
    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*)
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "dxopost()^2+dyopost()^2<=V^2&((0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0|v=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=0&rpost()=r&tpost()=0|(-B<=apost()&apost()<=A)&rpost()!=0&wpost()*rpost()=v&(abs(x-xopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&xopost()=xopost()&yopost()=yopost()&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=wpost()&apost()=apost()&rpost()=rpost()&tpost()=0)".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "dxopost()^2+dyopost()^2<=V^2&((0<=ep&v>=0)&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0|v=0&0<=ep&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=0&wpost()=0&apost()=0&rpost()=r&tpost()=0|(-B<=apost()&apost()<=A)&rpost()!=0&wpost()*rpost()=v&(abs(x-xopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&tpost()=0)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS controller monitor (forward chase)")
  }

  // works but is super-slow
  it should "find the correct controller monitor condition from the input model" ignore {
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(modelplexInput, tactic)

    val expectedSucc = "dxopost_0()^2+dyopost_0()^2<=V^2&((0<=ep&v>=0)&(((((((((((xopost()=xo&yopost()=yo)&dxopost()=dxopost_0())&dyopost()=dyopost_0())&xpost()=x)&ypost()=y)&dxpost()=dx)&dypost()=dy)&vpost()=v)&wpost()=w)&apost()=-B)&rpost()=r)&tpost()=0|v=0&(0<=ep&v>=0)&(((((((((((xopost()=xo&yopost()=yo)&dxopost()=dxopost_0())&dyopost()=dyopost_0())&xpost()=x)&ypost()=y)&dxpost()=dx)&dypost()=dy)&vpost()=v)&wpost()=0)&apost()=0)&rpost()=r)&tpost()=0|(-B<=apost_0()&apost_0()<=A)&rpost_0()!=0&wpost_0()*rpost_0()=v&(abs(x-xopost_0())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost_0())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&(((((((((((xopost()=xopost_0()&yopost()=yopost_0())&dxopost()=dxopost_0())&dyopost()=dyopost_0())&xpost()=x)&ypost()=y)&dxpost()=dx)&dypost()=dy)&vpost()=v)&wpost()=wpost_0())&apost()=apost_0())&rpost()=rpost_0())&tpost()=0)".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expectedSucc

    report(expectedSucc, result, "RSS controller monitor (backward tactic)")
  }

  it should "work using the command line interface" taggedAs IgnoreInBuildTest in {
    // command line main has to initialize the prover itself, so dispose all test setup first
    afterEach()

    val inputFileName = "keymaerax-webui/src/test/resources/examples/casestudies/robix/passivesafetyabs.key"
    val vars = "xo,yo,dxo,dyo,x,y,dx,dy,v,w,a,r,t"
    val outputFileName = File.createTempFile("passivesafetyabs", ".kym").getAbsolutePath
    KeYmaeraX.main(Array("-tool", "mathematica", "-modelplex", inputFileName, "-vars", vars, "-monitorKind", "ctrl", "-out", outputFileName))

    val expectedFileContent = "dxopost()^2+dyopost()^2<=V^2&((0<=ep&v>=0)&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0|v=0&0<=ep&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=0&wpost()=0&apost()=0&rpost()=r&tpost()=0|(-B<=apost()&apost()<=A)&rpost()!=0&wpost()*rpost()=v&(abs(x-xopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&tpost()=0)".asFormula

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    KeYmaeraXParser(actualFileContent) shouldBe expectedFileContent
  }

  "RSS passive orientation safety modelplex in place" should "extract the correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passiveorientationsafety.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("a"), Variable("r"),
      Variable("talpha"), Variable("odx"), Variable("ody"), Variable("ox"), Variable("oy"), Variable("dx"),
      Variable("dy"), Variable("w"), Variable("isVisible"), Variable("t"), Variable("v"), Variable("talpha"),
      Variable("x"), Variable("y"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists odx \\exists ody (odx^2+ody^2<=V()^2&(\\exists w (w*r=v&(0<=ep&v>=0)&apost()=-b()&rpost()=r&talphapost()=talpha&odxpost()=odx&odypost()=ody&oxpost()=ox&oypost()=oy&dxpost()=dx&dypost()=dy&wpost()=w&isVisiblepost()=isVisible&tpost()=0&vpost()=v&talphapost()=talpha&xpost()=x&ypost()=y)|v=0&\\exists w (w*r=v&(0<=ep&v>=0)&apost()=0&rpost()=r&talphapost()=talpha&odxpost()=odx&odypost()=ody&oxpost()=ox&oypost()=oy&dxpost()=-dx&dypost()=-dy&wpost()=w&isVisiblepost()=isVisible&tpost()=0&vpost()=v&talphapost()=talpha&xpost()=x&ypost()=y)|\\exists a ((-b()<=a&a<=A)&\\exists r (r!=0&\\exists ox \\exists oy \\exists isVisible (v+a*ep < 0&(isVisible < 0|(x-ox>=0->x-ox>v^2/(-2*a)+V()*(v/(-a)))&(x-ox<=0->ox-x>v^2/(-2*a)+V()*(v/(-a)))|(y-oy>=0->y-oy>v^2/(-2*a)+V()*(v/(-a)))&(y-oy<=0->oy-y>v^2/(-2*a)+V()*(v/(-a))))&((r>=0->v^2/(-2*a) < alpha()*r)&(r < 0->v^2/(-2*a) < -alpha()*r))&\\exists w (w*r=v&(0<=ep&v>=0)&apost()=a&rpost()=r&talphapost()=0&odxpost()=odx&odypost()=ody&oxpost()=ox&oypost()=oy&dxpost()=dx&dypost()=dy&wpost()=w&isVisiblepost()=isVisible&tpost()=0&vpost()=v&talphapost()=0&xpost()=x&ypost()=y)|v+a*ep>=0&(isVisible < 0|(x-ox>=0->x-ox>v^2/(2*b())+V()*(v/b())+(a/b()+1)*(a/2*ep^2+ep*(v+V())))&(x-ox<=0->ox-x>v^2/(2*b())+V()*(v/b())+(a/b()+1)*(a/2*ep^2+ep*(v+V())))|(y-oy>=0->y-oy>v^2/(2*b())+V()*(v/b())+(a/b()+1)*(a/2*ep^2+ep*(v+V())))&(y-oy<=0->oy-y>v^2/(2*b())+V()*(v/b())+(a/b()+1)*(a/2*ep^2+ep*(v+V()))))&((r>=0->v^2/(2*b())+(a/b()+1)*(a/2*ep^2+ep*v) < alpha()*r)&(r < 0->v^2/(2*b())+(a/b()+1)*(a/2*ep^2+ep*v) < -alpha()*r))&\\exists w (w*r=v&(0<=ep&v>=0)&apost()=a&rpost()=r&talphapost()=0&odxpost()=odx&odypost()=ody&oxpost()=ox&oypost()=oy&dxpost()=dx&dypost()=dy&wpost()=w&isVisiblepost()=isVisible&tpost()=0&vpost()=v&talphapost()=0&xpost()=x&ypost()=y))))))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*)
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "odxpost()^2+odypost()^2<=V()^2&(wpost()*r=v&(0<=ep&v>=0)&apost()=-b()&rpost()=r&talphapost()=talpha&odxpost()=odxpost()&odypost()=odypost()&oxpost()=ox&oypost()=oy&dxpost()=dx&dypost()=dy&wpost()=wpost()&isVisiblepost()=isVisible&tpost()=0&vpost()=v&talphapost()=talpha&xpost()=x&ypost()=y|v=0&wpost()*r=v&(0<=ep&v>=0)&apost()=0&rpost()=r&talphapost()=talpha&odxpost()=odxpost()&odypost()=odypost()&oxpost()=ox&oypost()=oy&dxpost()=-dx&dypost()=-dy&wpost()=wpost()&isVisiblepost()=isVisible&tpost()=0&vpost()=v&talphapost()=talpha&xpost()=x&ypost()=y|(-b()<=apost()&apost()<=A)&rpost()!=0&(v+apost()*ep < 0&(isVisiblepost() < 0|(x-oxpost()>=0->x-oxpost()>v^2/(-2*apost())+V()*(v/(-apost())))&(x-oxpost()<=0->oxpost()-x>v^2/(-2*apost())+V()*(v/(-apost())))|(y-oypost()>=0->y-oypost()>v^2/(-2*apost())+V()*(v/(-apost())))&(y-oypost()<=0->oypost()-y>v^2/(-2*apost())+V()*(v/(-apost()))))&((rpost()>=0->v^2/(-2*apost()) < alpha()*rpost())&(rpost() < 0->v^2/(-2*apost()) < -alpha()*rpost()))&wpost()*rpost()=v&(0<=ep&v>=0)&apost()=apost()&rpost()=rpost()&talphapost()=0&odxpost()=odxpost()&odypost()=odypost()&oxpost()=oxpost()&oypost()=oypost()&dxpost()=dx&dypost()=dy&wpost()=wpost()&isVisiblepost()=isVisiblepost()&tpost()=0&vpost()=v&talphapost()=0&xpost()=x&ypost()=y|v+apost()*ep>=0&(isVisiblepost() < 0|(x-oxpost()>=0->x-oxpost()>v^2/(2*b())+V()*(v/b())+(apost()/b()+1)*(apost()/2*ep^2+ep*(v+V())))&(x-oxpost()<=0->oxpost()-x>v^2/(2*b())+V()*(v/b())+(apost()/b()+1)*(apost()/2*ep^2+ep*(v+V())))|(y-oypost()>=0->y-oypost()>v^2/(2*b())+V()*(v/b())+(apost()/b()+1)*(apost()/2*ep^2+ep*(v+V())))&(y-oypost()<=0->oypost()-y>v^2/(2*b())+V()*(v/b())+(apost()/b()+1)*(apost()/2*ep^2+ep*(v+V()))))&((rpost()>=0->v^2/(2*b())+(apost()/b()+1)*(apost()/2*ep^2+ep*v) < alpha()*rpost())&(rpost() < 0->v^2/(2*b())+(apost()/b()+1)*(apost()/2*ep^2+ep*v) < -alpha()*rpost()))&wpost()*rpost()=v&(0<=ep&v>=0)&apost()=apost()&rpost()=rpost()&talphapost()=0&odxpost()=odxpost()&odypost()=odypost()&oxpost()=oxpost()&oypost()=oypost()&dxpost()=dx&dypost()=dy&wpost()=wpost()&isVisiblepost()=isVisiblepost()&tpost()=0&vpost()=v&talphapost()=0&xpost()=x&ypost()=y))".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "odxpost()^2+odypost()^2<=V()^2&(wpost()*r=v&(0<=ep&v>=0)&apost()=-b()&rpost()=r&talphapost()=talpha&oxpost()=ox&oypost()=oy&dxpost()=dx&dypost()=dy&isVisiblepost()=isVisible&tpost()=0&vpost()=v&xpost()=x&ypost()=y|v=0&wpost()*r=0&0<=ep&apost()=0&rpost()=r&talphapost()=talpha&oxpost()=ox&oypost()=oy&dxpost()=-dx&dypost()=-dy&isVisiblepost()=isVisible&tpost()=0&vpost()=0&xpost()=x&ypost()=y|(-b()<=apost()&apost()<=A)&rpost()!=0&(v+apost()*ep < 0&(isVisiblepost() < 0|(x-oxpost()>=0->x-oxpost()>v^2/(-2*apost())+V()*(v/(-apost())))&(x-oxpost()<=0->oxpost()-x>v^2/(-2*apost())+V()*(v/(-apost())))|(y-oypost()>=0->y-oypost()>v^2/(-2*apost())+V()*(v/(-apost())))&(y-oypost()<=0->oypost()-y>v^2/(-2*apost())+V()*(v/(-apost()))))&((rpost()>=0->v^2/(-2*apost()) < alpha()*rpost())&(rpost() < 0->v^2/(-2*apost()) < -alpha()*rpost()))&wpost()*rpost()=v&(0<=ep&v>=0)&talphapost()=0&dxpost()=dx&dypost()=dy&tpost()=0&vpost()=v&xpost()=x&ypost()=y|v+apost()*ep>=0&(isVisiblepost() < 0|(x-oxpost()>=0->x-oxpost()>v^2/(2*b())+V()*(v/b())+(apost()/b()+1)*(apost()/2*ep^2+ep*(v+V())))&(x-oxpost()<=0->oxpost()-x>v^2/(2*b())+V()*(v/b())+(apost()/b()+1)*(apost()/2*ep^2+ep*(v+V())))|(y-oypost()>=0->y-oypost()>v^2/(2*b())+V()*(v/b())+(apost()/b()+1)*(apost()/2*ep^2+ep*(v+V())))&(y-oypost()<=0->oypost()-y>v^2/(2*b())+V()*(v/b())+(apost()/b()+1)*(apost()/2*ep^2+ep*(v+V()))))&((rpost()>=0->v^2/(2*b())+(apost()/b()+1)*(apost()/2*ep^2+ep*v) < alpha()*rpost())&(rpost() < 0->v^2/(2*b())+(apost()/b()+1)*(apost()/2*ep^2+ep*v) < -alpha()*rpost()))&wpost()*rpost()=v&(0<=ep&v>=0)&talphapost()=0&dxpost()=dx&dypost()=dy&tpost()=0&vpost()=v&xpost()=x&ypost()=y))".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS passive orientation controller monitor (forward chase)")
  }

  "RSS passive safety curve straight" should "find correct controller monitor" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists dxo \\exists dyo (dxo^2+dyo^2<=V^2&((w=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0|w!=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0)|v=0&(0=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=0&rpost()=r&tpost()=0|0!=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=0&rpost()=r&tpost()=0)|\\exists a ((-B<=a&a<=A)&(\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yo)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=a&rpost()=r&tpost()=0|0!=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=a&rpost()=r&tpost()=0))|\\exists r (r!=0&\\exists w (w*r=v&\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yo)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(w=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=a&rpost()=r&tpost()=0|w!=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=a&rpost()=r&tpost()=0))))))))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*)
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "dxopost()^2+dyopost()^2<=V^2&((w=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0|w!=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0)|v=0&(0=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=0&rpost()=r&tpost()=0|0!=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=0&rpost()=r&tpost()=0)|(-B<=apost()&apost()<=A)&((abs(x-xopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0=0&(0<=ep&v>=0)&xopost()=xopost()&yopost()=yopost()&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=apost()&rpost()=r&tpost()=0|0!=0&(0<=ep&v>=0)&xopost()=xopost()&yopost()=yopost()&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=apost()&rpost()=r&tpost()=0)|rpost()!=0&0*rpost()=v&(abs(x-xopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0=0&(0<=ep&v>=0)&xopost()=xopost()&yopost()=yopost()&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=apost()&rpost()=rpost()&tpost()=0|0!=0&(0<=ep&v>=0)&xopost()=xopost()&yopost()=yopost()&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=apost()&rpost()=rpost()&tpost()=0)))".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "dxopost()^2+dyopost()^2<=V^2&((w=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=-B&rpost()=r&tpost()=0|w!=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&rpost()=r&tpost()=0)|v=0&0<=ep&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=0&wpost()=0&apost()=0&rpost()=r&tpost()=0|(-B<=apost()&apost()<=A)&((abs(x-xopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&rpost()=r&tpost()=0|rpost()!=0&0=v&(abs(x-xopost())>0/(2*B)+0/B+(A/B+1)*(A/2*ep^2+ep*V)|abs(y-yopost())>0/(2*B)+0/B+(A/B+1)*(A/2*ep^2+ep*V))&0<=ep&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=0&wpost()=0&tpost()=0))".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS controller monitor (forward chase)")
  }

  "RSS passive safety curve straight curvature" should "find correct controller monitor" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight_curvature.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("k"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists dxo \\exists dyo (dxo^2+dyo^2<=V^2&((0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&kpost()=k&tpost()=0|v=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=0&kpost()=k&tpost()=0|\\exists a ((-B<=a&a<=A)&\\exists k \\exists w (v*k=w&\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yo)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxo&dyopost()=dyo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=a&kpost()=k&tpost()=0)))))".asFormula

    //Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*)
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "dxopost()^2+dyopost()^2<=V^2&((0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&kpost()=k&tpost()=0|v=0&(0<=ep&v>=0)&xopost()=xo&yopost()=yo&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=0&apost()=0&kpost()=k&tpost()=0|(-B<=apost()&apost()<=A)&v*kpost()=v*kpost()&(abs(x-xopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&xopost()=xopost()&yopost()=yopost()&dxopost()=dxopost()&dyopost()=dyopost()&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=v*kpost()&apost()=apost()&kpost()=kpost()&tpost()=0)".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "dxopost()^2+dyopost()^2<=V^2&((0<=ep&v>=0)&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=w&apost()=-B&kpost()=k&tpost()=0|v=0&0<=ep&xopost()=xo&yopost()=yo&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=0&wpost()=0&apost()=0&kpost()=k&tpost()=0|(-B<=apost()&apost()<=A)&(abs(x-xopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost())>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&xpost()=x&ypost()=y&dxpost()=dx&dypost()=dy&vpost()=v&wpost()=v*kpost()&tpost()=0)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS controller monitor (forward chase)")
  }
//
//  ignore should "extract the correct controller monitor" in {
//    val in = getClass.getResourceAsStream("examples/casestudies/robix/passiveorientationsafety.key")
//    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val modelplexInput = createMonitorSpecificationConjecture(model, Variable("a"), Variable("r"),
//      Variable("talpha"), Variable("odx"), Variable("ody"), Variable("ox"), Variable("oy"), Variable("dx"),
//      Variable("dy"), Variable("w"), Variable("isVisible"), Variable("t"), Variable("v"), Variable("talpha"),
//      Variable("x"), Variable("y"))
//
//    //@todo fix bug in instantiateExistentialQuanT
//    val tactic = modelplexAxiomaticStyle(useOptOne=true)(controllerMonitorT)(1)
//    val result = proveUncheckedBy(modelplexInput, tactic)
//
//    val expectedAnte = "true".asFormula
//    val expectedSucc = "odxpost_0()^2+odypost_0()^2<=V()^2&(wpost_0()*r=v&(apost()=-b()&rpost()=r&talphapost()=talpha&odxpost()=odxpost_0()&odypost()=odypost_0()&oxpost()=ox&oypost()=oy&dxpost()=dx&dypost()=dy&wpost()=wpost_0()&isVisiblepost()=isVisible&tpost()=0)|(v=0&(wpost_0()*r=v&(apost()=0&rpost()=r&talphapost()=talpha&odxpost()=odxpost_0()&odypost()=odypost_0()&oxpost()=ox&oypost()=oy&dxpost()=-dx&dypost()=-dy&wpost()=wpost_0()&isVisiblepost()=isVisible&tpost()=0))|-b()<=apost_0()&apost_0()<=A&(rpost_0()!=0&(v+apost_0()*ep < 0&((isVisiblepost_0() < 0|((x-oxpost_0()>=0->x-oxpost_0()>v^2/(-2*apost_0())+V()*(v/-apost_0()))&(x-oxpost_0()<=0->oxpost_0()-x>v^2/(-2*apost_0())+V()*(v/-apost_0()))|(y-oypost_0()>=0->y-oypost_0()>v^2/(-2*apost_0())+V()*(v/-apost_0()))&(y-oypost_0()<=0->oypost_0()-y>v^2/(-2*apost_0())+V()*(v/-apost_0()))))&((rpost_0()>=0->v^2/(-2*apost_0()) < alpha()*rpost_0())&(rpost_0() < 0->v^2/(-2*apost_0()) < -alpha()*rpost_0())&(wpost_0()*rpost_0()=v&(apost()=apost_0()&rpost()=rpost_0()&talphapost()=0&odxpost()=odxpost_0()&odypost()=odypost_0()&oxpost()=oxpost_0()&oypost()=oypost_0()&dxpost()=dx&dypost()=dy&wpost()=wpost_0()&isVisiblepost()=isVisiblepost_0()&tpost()=0))))|v+apost_0()*ep>=0&((isVisiblepost_0() < 0|((x-oxpost_0()>=0->x-oxpost_0()>v^2/(2*b())+V()*(v/b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*(v+V())))&(x-oxpost_0()<=0->oxpost_0()-x>v^2/(2*b())+V()*(v/b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*(v+V())))|(y-oypost_0()>=0->y-oypost_0()>v^2/(2*b())+V()*(v/b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*(v+V())))&(y-oypost_0()<=0->oypost_0()-y>v^2/(2*b())+V()*(v/b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*(v+V())))))&((rpost_0()>=0->v^2/(2*b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*v) < alpha()*rpost_0())&(rpost_0() < 0->v^2/(2*b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*v) < -alpha()*rpost_0())&(wpost_0()*rpost_0()=v&(apost()=apost_0()&rpost()=rpost_0()&talphapost()=0&odxpost()=odxpost_0()&odypost()=odypost_0()&oxpost()=oxpost_0()&oypost()=oypost_0()&dxpost()=dx&dypost()=dy&wpost()=wpost_0()&isVisiblepost()=isVisiblepost_0()&tpost()=0))))))))".asFormula
//
//    result.openGoals() should have size 1
//    result.openGoals().head.sequent.ante should contain only expectedAnte
//    result.openGoals().head.sequent.succ should contain only expectedSucc
//
//    report(result.openGoals().head.sequent.succ.head, result, "RSS passive orientation safety controller monitor (backward tactic)")
//  }
//
  "Hybrid quadcopter" should "extract the correct controller monitor" ignore {
    val in = getClass.getResourceAsStream("/examples/casestudies/quadcopter/hybridquadrotor.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model, Variable("href"), Variable("v"), Variable("h"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(modelplexInput, tactic)

    val expectedSucc = "(h>=hrefpost_0()&hrefpost_0()>0&((kp < 0&v=0&hrefpost_0()>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&hrefpost_0()=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*hrefpost_0()*kp^2+hrefpost_0()^2*kp^2+h*kd()*kp*v-hrefpost_0()*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>hrefpost_0())|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*hrefpost_0()*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*hrefpost_0()*kp)|kp>0&v=0&(h!=hrefpost_0()&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>hrefpost_0()|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*hrefpost_0()*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*hrefpost_0()*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*hrefpost_0()*kp|2*hrefpost_0()*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*hrefpost_0()*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*hrefpost_0()*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*hrefpost_0()*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*hrefpost_0()*kp|2*hrefpost_0()*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*hrefpost_0()*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*hrefpost_0()*kp^2+hrefpost_0()^2*kp^2+h*kd()*kp*v-hrefpost_0()*kd()*kp*v+kp*v^2=0))&true&(hrefpost()=hrefpost_0()&vpost()=v)&hpost()=h".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expectedSucc

    report(result.subgoals.head.succ.head, result, "Hybrid quadcopter controller monitor (backward tactic)")
  }

  it should "extract the correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/quadcopter/hybridquadrotor.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("href"), Variable("v"), Variable("h"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists href ((h>=href&href>0&((kp < 0&v=0&href>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*href*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*href*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&href=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*href*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*href*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*href*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*href*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*href*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*href*kp^2+href^2*kp^2+h*kd()*kp*v-href*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>href)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*href*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*href*kp)|kp>0&v=0&(h!=href&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>href|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*href*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*href*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*href*kp|2*href*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*href*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*href*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*href*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*href*kp|2*href*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*href*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*href*kp^2+href^2*kp^2+h*kd()*kp*v-href*kd()*kp*v+kp*v^2=0))&hrefpost()=href&vpost()=v&hpost()=h)".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "(h>=h&h>0&((kp < 0&v=0&h>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*h*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*h*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&h=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*h*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*h*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*h*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*h*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*h*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*h*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*h*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*h*kp^2+h^2*kp^2+h*kd()*kp*v-h*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>h)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*h*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*h*kp)|kp>0&v=0&(h!=h&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>h|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*h*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*h*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*h*kp|2*h*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*h*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*h*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*h*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*h*kp|2*h*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*h*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*h*kp^2+h^2*kp^2+h*kd()*kp*v-h*kd()*kp*v+kp*v^2=0))&hrefpost()=h&vpost()=v&hpost()=h".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "(h>0&((kp < 0&v=0|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*h*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*h*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*h*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*h*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*h*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*h*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*h*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*h*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*h*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*h*kp^2+h^2*kp^2+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*h*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*h*kp)|kp>0&v=0&(kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*h*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*h*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*h*kp|2*h*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*h*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*h*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*h*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*h*kp|2*h*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*h*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*h*kp^2+h^2*kp^2+kp*v^2=0))&hrefpost()=h&vpost()=v&hpost()=h".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "Hybrid quadcopter controller monitor (forward chase)")
  }

  "VSL modelplex in place" should "find correct controller monitor condition" ignore {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl-ctrl.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(model, tactic)

    // with ordinary diamond test
    val expected = "(x1post()=x1&v1post()=v1&a1post()=-B&tpost()=0&vslpost()=vsl&xslpost()=xsl|(vslpost_0()>=0&xslpost_0()>=x1+(v1^2-vslpost_0()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post()=x1&v1post()=v1&a1post()=-B&tpost()=0&vslpost()=vslpost_0()&xslpost()=xslpost_0())|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post_0()&a1post_0()<=A)&(x1post()=x1&v1post()=v1&a1post()=a1post_0()&tpost()=0&vslpost()=vsl&xslpost()=xsl|(vslpost_0()>=0&xslpost_0()>=x1+(v1^2-vslpost_0()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post()=x1&v1post()=v1&a1post()=a1post_0()&tpost()=0&vslpost()=vslpost_0()&xslpost()=xslpost_0())|x1>=xsl&(-B<=a1post_0()&a1post_0()<=A&a1post_0()<=(v1-vsl)/ep)&(x1post()=x1&v1post()=v1&a1post()=a1post_0()&tpost()=0&vslpost()=vsl&xslpost()=xsl|(vslpost_0()>=0&xslpost_0()>=x1+(v1^2-vslpost_0()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post()=x1&v1post()=v1&a1post()=a1post_0()&tpost()=0&vslpost()=vslpost_0()&xslpost()=xslpost_0())".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only
      "v1>=0&vsl>=0&x1<=xsl&2*B*(xsl-x1)>=v1^2-vsl^2&A>=0&B>0&ep>0".asFormula
    result.subgoals.head.succ should contain only expected

    report(expected, result, "VSL controller (backward tactic from prefabricated conjecture)")
  }

  it should "find correct controller monitor condition from input file" ignore {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model,
      Variable("xsl"), Variable("vsl"), Variable("x1"), Variable("v1"), Variable("a1"), Variable("t"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(modelplexInput, tactic)

    // with ordinary diamond test
    val expected = "((((xslpost()=xsl&vslpost()=vsl)&x1post()=x1)&v1post()=v1)&a1post()=-B)&tpost()=t|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post_0()&a1post_0()<=A)&((((xslpost()=xsl&vslpost()=vsl)&x1post()=x1)&v1post()=v1)&a1post()=a1post_0())&tpost()=t|x1>=xsl&(-B<=a1post_0()&a1post_0()<=A&a1post_0()<=(v1-vsl)/ep)&((((xslpost()=xsl&vslpost()=vsl)&x1post()=x1)&v1post()=v1)&a1post()=a1post_0())&tpost()=t|(vslpost_0()>=0&xslpost_0()>=x1+(v1^2-vslpost_0()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&(v1>=0&0<=ep)&((((xslpost()=xslpost_0()&vslpost()=vslpost_0())&x1post()=x1)&v1post()=v1)&a1post()=a1)&tpost()=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "true".asFormula
    result.subgoals.head.succ should contain only expected

    report(expected, result, "VSL controller monitor (backward tactic)")
  }

  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xsl"), Variable("vsl"), Variable("x1"), Variable("v1"), Variable("a1"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&a1post()=-B&tpost()=t|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&\\exists a1 ((-B<=a1&a1<=A)&xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&a1post()=a1&tpost()=t)|x1>=xsl&\\exists a1 ((-B<=a1&a1<=A&a1<=(v1-vsl)/ep)&xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&a1post()=a1&tpost()=t)|\\exists xsl \\exists vsl ((vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&(v1>=0&0<=ep)&xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&a1post()=a1&tpost()=0)".asFormula

    // Opt. 1
    val expected = "xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&a1post()=-B&tpost()=t|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post()&a1post()<=A)&xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&a1post()=a1post()&tpost()=t|x1>=xsl&(-B<=a1post()&a1post()<=A&a1post()<=(v1-vsl)/ep)&xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&a1post()=a1post()&tpost()=t|(vslpost()>=0&xslpost()>=x1+(v1^2-vslpost()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&(v1>=0&0<=ep)&xslpost()=xslpost()&vslpost()=vslpost()&x1post()=x1&v1post()=v1&a1post()=a1&tpost()=0".asFormula
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(tool, assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only expected

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&a1post()=-B&tpost()=t|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post()&a1post()<=A)&xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&tpost()=t|x1>=xsl&(-B<=a1post()&a1post()<=A&a1post()<=(v1-vsl)/ep)&xslpost()=xsl&vslpost()=vsl&x1post()=x1&v1post()=v1&tpost()=t|(vslpost()>=0&xslpost()>=x1+(v1^2-vslpost()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&(v1>=0&0<=ep)&x1post()=x1&v1post()=v1&a1post()=a1&tpost()=0".asFormula

    report(expected, foResult, "VSL controller monitor (forward chase without Opt. 1)")
    report(expected, opt1Result, "VSL controller monitor (forward chase with Opt. 1)")
  }

  "PLDI" should "prove stopsign" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove stopsign with direct v control" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove stopsign with v change and disturbance" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "find correct controller monitor for stopsign" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("a"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & (ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&xpost()=x&vpost()=v&apost()=A&tpost()=0|v=0&0<=ep&xpost()=x&vpost()=0&apost()=0&tpost()=0|(v>=0&0<=ep)&xpost()=x&vpost()=v&apost()=-b&tpost()=0".asFormula

    val Or(acc,Or(coast,brake)) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&xpost()=x&vpost()=v&apost()=A&tpost()=0".asFormula
    coast shouldBe "v=0&0<=ep&xpost()=x&vpost()=0&apost()=0&tpost()=0".asFormula
    brake shouldBe "(v>=0&0<=ep)&xpost()=x&vpost()=v&apost()=-b&tpost()=0".asFormula
  }

  it should "find correct controller monitor for stopsign with direct v control" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & (ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=ep*vpost()&0<=ep&xpost()=x&tpost()=0|0<=ep&xpost()=x&vpost()=0&tpost()=0".asFormula

    val Or(acc,stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*vpost()&0<=ep&xpost()=x&tpost()=0".asFormula
    stop shouldBe "0<=ep&xpost()=x&vpost()=0&tpost()=0".asFormula
  }

  it should "find correct controller monitor for stopsign with direct v change and disturbance" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("d"), Variable("c"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & (ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=ep*(v+cpost()+D)&(-D<=dpost()&dpost()<=D)&0<=ep&xpost()=x&vpost()=v&tpost()=0|0<=ep&xpost()=x&vpost()=0&dpost()=0&cpost()=0&tpost()=0".asFormula

    val Or(acc,stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*(v+cpost()+D)&(-D<=dpost()&dpost()<=D)&0<=ep&xpost()=x&vpost()=v&tpost()=0".asFormula
    stop shouldBe "0<=ep&xpost()=x&vpost()=0&dpost()=0&cpost()=0&tpost()=0".asFormula
  }

  it should "find correct model monitor for stopsign" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("a"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) & (ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((ep=0&0=tpost())&((A=0&apost()=0)&((v=0&vpost()=0)&x=xpost()|(v=vpost()&x=xpost())&v>0)|(A=apost()&A>0)&((v=0&vpost()=0)&xpost()=x|(v=vpost()&xpost()=x)&v>0))|ep>0&(((A=0&apost()=0)&((v=0&vpost()=0)&x=xpost()|(v=vpost()&xpost()=tpost()*v+x)&v>0))&((ep=tpost()|0=tpost())|0 < tpost()&tpost() < ep)|(A=apost()&A>0)&(((v=0&vpost()=A*tpost())&xpost()=1/2*A*(-tpost())^2+x|(vpost()=A*tpost()+v&xpost()=1/2*A*(-tpost())^2+tpost()*v+x)&v>0)&(ep=tpost()|0 < tpost()&tpost() < ep)|0=tpost()&((v=0&vpost()=0)&xpost()=x|(vpost()=v&xpost()=x)&v>0))))|v=0&(((0<=tpost()&ep>=tpost())&xpost()=x)&0=vpost())&apost()=0|((ep=0&0=tpost())&apost()+b=0)&((v=0&vpost()=0)&xpost()=x|(vpost()=v&xpost()=x)&v>0)|(ep>0&apost()+b=0)&(((v=b*tpost()+vpost()&b*(-tpost())^2+2*((-tpost())*v+-x+xpost())=0)&v>0)&((ep=tpost()&b<=ep^-1*v|0=tpost())|(tpost() < ep&0 < tpost())&b*tpost()<=v)|((0=tpost()&v=0)&vpost()=0)&2*xpost()=2*x)".asFormula

    val Or(acc,Or(coast,brake)) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((ep=0&0=tpost())&((A=0&apost()=0)&((v=0&vpost()=0)&x=xpost()|(v=vpost()&x=xpost())&v>0)|(A=apost()&A>0)&((v=0&vpost()=0)&xpost()=x|(v=vpost()&xpost()=x)&v>0))|ep>0&(((A=0&apost()=0)&((v=0&vpost()=0)&x=xpost()|(v=vpost()&xpost()=tpost()*v+x)&v>0))&((ep=tpost()|0=tpost())|0 < tpost()&tpost() < ep)|(A=apost()&A>0)&(((v=0&vpost()=A*tpost())&xpost()=1/2*A*(-tpost())^2+x|(vpost()=A*tpost()+v&xpost()=1/2*A*(-tpost())^2+tpost()*v+x)&v>0)&(ep=tpost()|0 < tpost()&tpost() < ep)|0=tpost()&((v=0&vpost()=0)&xpost()=x|(vpost()=v&xpost()=x)&v>0))))".asFormula
    coast shouldBe "v=0&(((0<=tpost()&ep>=tpost())&xpost()=x)&0=vpost())&apost()=0".asFormula
    brake shouldBe "((ep=0&0=tpost())&apost()+b=0)&((v=0&vpost()=0)&xpost()=x|(vpost()=v&xpost()=x)&v>0)|(ep>0&apost()+b=0)&(((v=b*tpost()+vpost()&b*(-tpost())^2+2*((-tpost())*v+-x+xpost())=0)&v>0)&((ep=tpost()&b<=ep^-1*v|0=tpost())|(tpost() < ep&0 < tpost())&b*tpost()<=v)|((0=tpost()&v=0)&vpost()=0)&2*xpost()=2*x)".asFormula
  }

  it should "find correct model monitor for stopsign with direct v control" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) & (ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=ep*vpost()&(0<=tpost()&ep>=tpost())&xpost()=tpost()*vpost()+x|((0<=tpost()&ep>=tpost())&x=xpost())&vpost()=0".asFormula

    val Or(acc,stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*vpost()&(0<=tpost()&ep>=tpost())&xpost()=tpost()*vpost()+x".asFormula
    stop shouldBe "((0<=tpost()&ep>=tpost())&x=xpost())&vpost()=0".asFormula
  }

  it should "find correct model monitor for stopsign with direct v change and disturbance" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("d"), Variable("c"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) & (ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)*) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=ep*(v+cpost()+D)&(-D<=dpost()&dpost()<=D)&((0<=tpost()&ep>=tpost())&(-tpost())*(cpost()+dpost()+v)+xpost()=x)&v=vpost()|((((0<=tpost()&ep>=tpost())&x=xpost())&vpost()=0)&dpost()=0)&cpost()=0".asFormula

    val Or(acc,stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*(v+cpost()+D)&(-D<=dpost()&dpost()<=D)&((0<=tpost()&ep>=tpost())&(-tpost())*(cpost()+dpost()+v)+xpost()=x)&v=vpost()".asFormula
    stop shouldBe "((((0<=tpost()&ep>=tpost())&x=xpost())&vpost()=0)&dpost()=0)&cpost()=0".asFormula
  }

  "ModelPlex formula metric" should "convert simple formula" in withMathematica { tool =>
    val fml = "x>=y & a=b & c<=d+e".asFormula
    ModelPlex.toMetric(fml) shouldBe "max(y-x, max(max(a-b, b-a), c-(d+e)))<=0".asFormula
  }

  it should "convert simple formula 2" in withMathematica { tool =>
    val fml = "x>=y&a=b | c<=d+e".asFormula
    ModelPlex.toMetric(fml) shouldBe "min((max((y-x,max((a-b,b-a)))),c-(d+e)))<=0".asFormula
  }

  it should "convert simple formula 3" in withMathematica { tool =>
    val fml = "x>=y&a=b&c<=d | c<=d+e | f<=g&h<=0".asFormula
    val metric = ModelPlex.toMetric(fml)
    metric shouldBe "min((max((y-x,max((max((a-b,b-a)),c-d)))),min((c-(d+e),max((f-g,h))))))<=0".asFormula
    tool.findCounterExample(metric)
  }

  it should "convert simple formula 4" in withMathematica { tool =>
    val fml = "xpost>=x+5&ypost=y&cpost<=d | cpost>=d+e | fpost<=f&hpost<=0".asFormula
    val metric = ModelPlex.toMetric(fml)
    metric shouldBe "min((max((x+5-xpost,max((max((ypost-y,y-ypost)),cpost-d)))),min((d+e-cpost,max((fpost-f,hpost))))))<=0".asFormula
    tool.findCounterExample(metric)
  }

  it should "convert mixed open/closed formula" in withMathematica { tool =>
    val fml = "x>=y & a<b".asFormula
    ModelPlex.toMetric(fml) shouldBe "max(y-x, a-b)<0".asFormula
  }

//
//  "Quadcopter modelplex in place" should "find correct controller monitor condition" in {
//    val in = getClass.getResourceAsStream("examples/casestudies/modelplex/quadcopter/simplepid.key")
//    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val modelplexInput = createMonitorSpecificationConjecture(model, Variable("h"), Variable("v"), Variable("kp"),
//      Variable("kd"), Variable("href"))
//
//    val tactic = locateSucc(modelplexAxiomaticStyle(useOptOne=true)(controllerMonitorT))
//    val result = proveUncheckedBy(modelplexInput, tactic)
//
//    val expectedAnte = "true".asFormula
//    val expectedSucc = "true&(((hpost()=h&vpost()=v)&kppost()=kp)&kdpost()=kd)&hrefpost()=href".asFormula
//
//    result.openGoals() should have size 1
//    result.openGoals().head.sequent.ante should contain only expectedAnte
//    result.openGoals().head.sequent.succ should contain only expectedSucc
//  }
//
//  // Performance tests
//
//  val performanceRuns = 2
//
////  private def compareControllerMonitorTactics(modelFile: String, vars: Variable*) = {
////    val in = getClass.getResourceAsStream(modelFile)
////    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
////    val modelplexInput = createMonitorSpecificationConjecture(model, vars:_*)
////
////    val chaseTime = config(
////      Key.exec.benchRuns -> performanceRuns,
////      Key.verbose -> false
////    ) withWarmer {
////      new Warmer.Default
////    } withMeasurer {
////      new Measurer.IgnoringGC
////    } measure {
////      proveUncheckedBy(modelplexInput, ModelPlex.controllerMonitorByChase(1, 1::Nil))
////    }
////
////    val tacticTime = config(
////      Key.exec.benchRuns -> performanceRuns,
////      Key.verbose -> false
////    ) withWarmer {
////      new Warmer.Default
////    } withMeasurer {
////      new Measurer.IgnoringGC
////    } measure {
////      proveUncheckedBy(modelplexInput, modelplexAxiomaticStyle(useOptOne=true)(controllerMonitorT)(1))
////    }
////
////    println(s"Averaged time over $performanceRuns runs: $chaseTime (forward chase) vs. $tacticTime (backward tactic)")
////  }
//
////  "Performance measurement" should "on water tank compare backward tactic and forward chase controller monitor performance" taggedAs SlowTest in {
////    compareControllerMonitorTactics("examples/casestudies/modelplex/watertank/watertank.key", Variable("f"), Variable("l"), Variable("c"))
////  }
////
////  it should "on LLC compare backward tactic and forward chase controller monitor performance" taggedAs SlowTest in {
////    compareControllerMonitorTactics("examples/casestudies/modelplex/fm11/llc.key",
////      Variable("xl"), Variable("vl"), Variable("al"), Variable("xf"), Variable("vf"), Variable("af"), Variable("t"))
////  }
////
////  it should "on Robix compare backward tactic and forward chase controller monitor performance" taggedAs SlowTest in {
////    compareControllerMonitorTactics("examples/casestudies/robix/passivesafetyabs.key",
////      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
////      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))
////  }
////
////  it should "on VSL compare backward tactic and forward chase controller monitor performance" taggedAs SlowTest in {
////    compareControllerMonitorTactics("examples/casestudies/modelplex/iccps12/vsl.key",
////      Variable("xsl"), Variable("vsl"), Variable("x1"), Variable("v1"), Variable("a1"), Variable("t"))
////  }
//
//  "Interval arithmetic" should "intervalify grotesquely simplified watertank controller monitor" in {
//    //"(-1<=fpost()&fpost()<=(m-l)/ep)&(0<=l&0<=ep)&(fpost()=fpost()&lpost()=l)&cpost()=0".asFormula
//    val input = "-1<=fpost()&fpost()*ep+(l-m)<=0".asFormula
//    //@todo ouch, this is an awkard implementation for give the upper bound of a term as its interval
//    def upperBound(t: Term): Term = KeYmaeraXParser.termParser(t.prettyString.toUpperCase())
//    def intervalify: PositionTactic = chaseI(3, 3, e => e match {
//      // remove ODEs for controller monitor
//      case LessEqual(Plus(_,_), _) => "+<= up" :: Nil
//      case LessEqual(Minus(_,_), _) => "-<= up" :: Nil
//      case _ => AxiomIndex.axiomsFor(e)
//    },
//      ax => us => ax match {
//        case "+<= up" | "-<= up" => us ++
//          RenUSubst(immutable.Seq((FuncOf(Function("F",None,Unit,Real),Nothing),
//            upperBound(us(FuncOf(Function("f",None,Unit,Real),Nothing)))),
//            (FuncOf(Function("G",None,Unit,Real),Nothing),
//              upperBound(us(FuncOf(Function("g",None,Unit,Real),Nothing))))
//          ))
//        case _ => us
//      }
//    )
//
//    val result = proveBy(input, intervalify(SuccPosition(0, PosInExpr(1 :: Nil))))
//    result.subgoals should have size 1
//    result.subgoals.head.ante shouldBe empty
//    result.subgoals.head.succ should contain only "true".asFormula
//  }
}