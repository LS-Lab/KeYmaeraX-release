package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.ModelPlex.createMonitorSpecificationConjecture
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, ParsedArchiveEntry}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest
import testHelper.ParserFactory._

import scala.language.postfixOps
import org.scalatest.LoneElement._
import java.io.File

import edu.cmu.cs.ls.keymaerax.codegen._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, FormulaTools, PosInExpr, Statistics}

/**
  * Created by smitsch on 3/8/15.
  *
  * @author Stefan Mitsch
  * @author Ran Ji
  */
@SlowTest
class ModelplexTacticTests extends TacticTestBase {

  def monitorSize(f: Formula): Int = Statistics.countFormulaOperators(f, arith = true)

//  def numSteps(n: Provable): Int = if (n.subgoals.nonEmpty) n.subgoals.map(numSteps).min else 0
//  def numSteps(s: ProofStep): Int = if (s.subgoals.nonEmpty) 1 + s.subgoals.map(numSteps).sum else 1
//
//  def numBranches(n: ProofNode): Int = if (n.children.nonEmpty) n.children.map(numBranches).min else 0
//  def numBranches(s: ProofStep): Int = if (s.subgoals.nonEmpty) s.subgoals.map(numBranches).sum else 1

  private def report(result: Formula, proof: ProvableSig, name: String): Unit = {
    println(s"$name monitor size: " + monitorSize(result))
//    println("Number of proof steps: " + numSteps(proof))
//    println("Number of branches (open/all): " + proof.subgoals.size + "/" + numBranches(proof))
  }

  "Simple modelplex" should "chase: find correct controller monitor by updateCalculus implicationally" in withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/simple.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model, Variable("x"))

    def modelPlex: DependentPositionTactic = chase(3, 3, (e:Expression) => e match {
      // no equational assignments
      case Box(Assign(_, _), _) => Ax.assignbAxiom :: Ax.assignbup :: Nil
      case Diamond(Assign(_, _), _) => Ax.assigndAxiom :: Ax.assigndup :: Nil
      // remove loops
      case Diamond(Loop(_), _) => Ax.loopApproxd :: Nil
      // remove ODEs for controller monitor
      case Diamond(ODESystem(_, _), _) => Ax.dDX :: Nil
      case _ => AxIndex.axiomsFor(e)
    })

    val result = TactixLibrary.proveBy(modelplexInput, modelPlex(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "xpost=1".asFormula

    val monitorCorrectnessConjecture = ModelPlex.createMonitorCorrectnessConjecture(Variable("x")::Nil, 'ctrl, None)(model)
    println("Correctness conjecture " + monitorCorrectnessConjecture.prettyString)
    proveBy(monitorCorrectnessConjecture , implyR(1)*2 & ModelPlex.controllerMonitorByChase(1) & autoClose) shouldBe 'proved

  }

  it should "chase away a loop by updateCalculus implicationally" in withTactics {
    val model = ArchiveParser.parseAsFormula("ProgramVariables. R x. End. Problem. 0 <= x -> [{x:=2;}*](0 <= x) End.")
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model, Variable("x"))

    def modelPlex: DependentPositionTactic = chase(3, 3, (e:Expression) => e match {
      case Diamond(Loop(_), _) => Ax.loopApproxd :: Nil
      case _ => AxIndex.axiomsFor(e)
    })

    val result = proveBy(modelplexInput, modelPlex(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "xpost=2".asFormula
  }

//  "Watertank modelplex" should "find correct controller monitor condition" in {
//    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-ctrl.key"))
//    val tactic = locateSucc(modelplexSequentStyle)
//    val result = helper.runTactic(tactic, new RootNode(s))
//    result.openGoals() should have size 2
//    result.openGoals()(0).sequent.ante should contain only ("0<=x".asFormula, "x<=m".asFormula, "0<ep".asFormula)
//    result.openGoals()(0).sequent.succ should contain only "-1<=fpost_0 & fpost_0<=(m-x)/ep".asFormula
//    result.openGoals()(1).sequent.ante should contain only ("0<=x".asFormula, "x<=m".asFormula, "0<ep".asFormula, "-1<=fpost_0".asFormula, "fpost_0<=(m-x)/ep".asFormula)
//    result.openGoals()(1).sequent.succ should contain only "tpost_0=0 & (fpost=fpost_0 & xpost=x & tpost=tpost_0)".asFormula
//  }
//
  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("f"), Variable("l"), Variable("c"))

    val foResult = TactixLibrary.proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists f ((-1<=f&f<=(m()-l)/ep())&(0<=l&0<=ep())&fpost=f&lpost=l&cpost=0)".asFormula

    // Opt. 1
    val opt1Result = TactixLibrary.proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "(-1<=fpost&fpost<=(m()-l)/ep())&(0<=l&0<=ep())&fpost=fpost&lpost=l&cpost=0".asFormula

    report(opt1Result.subgoals.head.succ.head, opt1Result, "Water tank controller monitor (forward chase)")

    // Cleanup
//    val finalResult = proveBy(opt1Result.subgoals.head.succ.head, chase(3,3)(1))
//    finalResult.subgoals should have size 1
//    finalResult.subgoals.head.ante shouldBe empty
//    finalResult.subgoals.head.succ should contain only "(-1<=fpost&fpost<=(m-l)/ep)&(0<=l&0<=ep) & lpost=l & cpost=0".asFormula
  }

  it should "find correct model monitor condition" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("f"), Variable("l"), Variable("c"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    //@todo can steer result depending on where and when we use partial QE
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=false)(ModelPlex.modelMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & simplifier(1)
    val result = proveBy(modelplexInput, tactic)

    result.subgoals.loneElement shouldBe "==> (-1<=fpost&fpost<=(m()-l)/ep())&0 < ep()&(0=cpost&(lpost=l&(fpost < 0&l>=0|l>=0&fpost>0)|(fpost=0&l=lpost)&l>=0)|(cpost>0&ep()>=cpost)&(l>=0&(fpost=0&l=lpost|lpost=cpost*fpost+l&fpost>0)|(lpost=cpost*fpost+l&fpost < 0)&cpost*fpost+l>=0))".asSequent
  }

  it should "find euler model monitor condition" ignore withMathematica { tool =>
    val model = "true -> [x:=2;{x'=-3*x}]x>0".asFormula
    val (modelplexConjecture, assumptions) = createMonitorSpecificationConjecture(model, Variable("x"))
    //replace post with post()
    //@todo no longer necessary when axiom is added to axiom base
    val modelplexInput = ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case BaseVariable(v, i, s) if v.endsWith("post") => Right(FuncOf(Function(v, i, Unit, s), Nothing))
        case _ => Left(None)
      }
    }, modelplexConjecture).get

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    //@todo chase uses supplied tactic in first step, which results in "unexpected" branches since not an axiom
    val tactic = ModelPlex.modelMonitorByChase(ModelPlex.eulerAllIn)(1) & Idioms.<(
      ModelPlex.unrollLoop(2)(1) & ModelPlex.chaseEulerAssignments(1),
      skip
    )
    val result = proveBy(modelplexInput, tactic)

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x (x=2->\\exists t_ (t_>=0&\\forall e_ (e_>0->\\forall h0_ (h0_>0->\\exists h_ (0 < h_&h_ < h0_&((t_>=0&\\exists y_ (abs(x-y_) < e_&xpost()=y_))|(t_>=0&\\exists y_ (abs(x+h_*(-3*x)+h_*(-3*(x+h_*(-3*x)))-y_) < e_&xpost()=y_))))))))".asFormula
    //@note don't care about second branch - axiom not in axiom base

    //@note unsound approximation step
    val flipped = ModelPlex.flipUniversalEulerQuantifiers(result.subgoals.head.succ.head)
    flipped shouldBe "\\forall x (x=2->\\exists t_ (t_>=0&\\exists e_ (e_>0&\\exists h0_ (h0_>0&\\exists h_ (0 < h_&h_ < h0_&((t_>=0&\\exists y_ (abs(x-y_) < e_&xpost()=y_))|(t_>=0&\\exists y_ (abs(x+h_*(-3*x)+h_*(-3*(x+h_*(-3*x)))-y_) < e_&xpost()=y_))))))))".asFormula

    val simplified = proveBy(flipped, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & simplifier(1))
    simplified.subgoals should have size 1
    simplified.subgoals.head.ante shouldBe empty
    //@todo auto-generated post names are somewhat weird here for parameters t, e, h0, h
    simplified.subgoals.head.succ should contain only "tpost_0>=0&epost_0>0&h0post_0>0&0 < hpost_0&hpost_0 < h0post_0&(abs(2-xpost()) < epost_0|abs(2+hpost_0*-6+hpost_0*(-3*(2+hpost_0*-6))-xpost()) < epost_0)".asFormula
  }

  it should "find euler model monitor condition for systems" ignore withMathematica { tool =>
    val model = "true -> [x:=2;{x'=-3*x,y'=x-y}]x>0".asFormula
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("x"), Variable("y"))

    val eulerApproxed = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(ModelPlex.eulerSystemAllIn)(1))
    eulerApproxed.subgoals should have size 2
    eulerApproxed.subgoals.head.ante shouldBe empty
    eulerApproxed.subgoals.head.succ should contain only "\\forall x (x=2->\\exists t_ (t_>=0&\\forall e_ (e_>0->\\forall h0_ (h0_>0->\\exists h_ (0 < h_&h_ < h0_&<{{x_0:=x;y_0:=y;}x:=x+h_*(-3*x_0);y:=y+h_*(x_0-y_0);}*>(t_>=0&\\exists yy \\exists yx ((x-yx)^2+(y-yy)^2 < e_^2&xpost=yx&ypost=yy)))))))".asFormula

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val tactic = ModelPlex.modelMonitorByChase(ModelPlex.eulerSystemAllIn)(1) & Idioms.<(
      ModelPlex.unrollLoop(1)(1) & SaturateTactic(ModelPlex.chaseEulerAssignments(1)),
      skip)
    val result = proveBy(modelplexInput, tactic)
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "\\forall x (x=2->\\exists t_ (t_>=0&\\forall e_ (e_>0->\\forall h0_ (h0_>0->\\exists h_ (0 < h_&h_ < h0_&t_>=0&\\exists yy \\exists yx ((x+h_*(-3*x)-yx)^2+(y+h_*(x-y)-yy)^2 < e_^2&xpost=yx&ypost=yy))))))".asFormula

    //@note unsound approximation step
    val flipped = ModelPlex.flipUniversalEulerQuantifiers(result.subgoals.head.succ.head)
    val simplified = proveBy(flipped, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & simplifier(1))
    simplified.subgoals should have size 1
    simplified.subgoals.head.ante shouldBe empty
    //@todo auto-generated post names are somewhat weird here for parameters t, e, h0, h
    simplified.subgoals.head.succ should contain only "tpost_0>=0&epost_0>0&h0post_0>0&0 < hpost_0&hpost_0 < h0post_0&(2+hpost_0*-6-xpost)^2+(y+hpost_0*(2-y)-ypost)^2 < epost_0^2".asFormula
  }

  it should "find correct model monitor condition by chase" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("f"), Variable("l"), Variable("c"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val tactic = ModelPlex.modelMonitorByChase(1) & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & simplifier(1)
    val result = proveBy(modelplexInput, tactic)

    result.subgoals.loneElement shouldBe "==> (-1<=fpost&fpost<=(m()-l)/ep())&0 < ep()&(((((cpost=0&(fpost=0|fpost!=0))&(l=0|l=lpost))&l>=0)&(lpost=0|l=lpost))&(lpost=0|l>0)|(cpost>0&ep()>=cpost)&(fpost=0&(l=0&lpost=0|l=lpost&l>0)|cpost*fpost+l=lpost&(cpost*fpost+l>=0&fpost < 0|fpost>0&l>=0)))".asSequent
  }

  "Watertank modelplex in place" should "find correct controller monitor condition with Optimization 1" in withTactics {
    val s = ArchiveParser.parseAsFormula(
      io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank-ctrl.key")).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(s, tactic)

    // with ordinary diamond test
    val expected = "(-1<=fpost_0&fpost_0<=(m()-x)/ep())&fpost=fpost_0&xpost=x&tpost=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expected

    report(expected, result, "Watertank controller monitor (backward tactic)")
  }

  it should "find correct controller monitor condition by chase" in withMathematica { tool =>
    val model = ArchiveParser.parseAsFormula(
      io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")).mkString)

    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("f"), Variable("l"), Variable("c"))
    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val tactic = ModelPlex.controllerMonitorByChase(1) &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1)
    val result = proveBy(modelplexInput, tactic)

    // with ordinary diamond test
    val expected = "(-1<=fpost&fpost<=(m()-l)/ep())&(0<=l&0<=ep())&lpost=l&cpost=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expected

    report(expected, result, "Watertank controller monitor (chase)")
  }

  it should "chase controller monitor condition to tests" in withMathematica { tool =>
    val model = ArchiveParser.parseAsFormula(
      io.Source.fromInputStream(
        getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")).mkString)
    val Imply(_, Box(prg, _)) = model

    val stateVars = ("f"::"l"::"c"::Nil).map(_.asVariable.asInstanceOf[BaseVariable])
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, stateVars:_*)
    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val tactic = ModelPlex.controllerMonitorByChase(1) &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1)
    val result = proveBy(modelplexInput, tactic)

    val testProg = proveBy(result.subgoals.loneElement, ModelPlex.chaseToTests(combineTests=false)(1))
    testProg.subgoals.loneElement shouldBe "==> <?-1<=fpost&fpost<=(m()-l)/ep();><?0<=l&0<=ep();><?lpost=l;><?cpost=0;>true".asSequent

    val monitorFml = result.subgoals.loneElement.succ.head
    val reassociatedMonitorFml = FormulaTools.reassociate(monitorFml)
    proveBy(Equiv(monitorFml, reassociatedMonitorFml), prop) shouldBe 'proved

    // example: combine all tests for a single if-then-else condition
    val testProg2 = proveBy(reassociatedMonitorFml, ModelPlex.chaseToTests(combineTests=true)(1)*2)
    testProg2.subgoals.loneElement shouldBe "==> <?((((-1<=fpost&fpost<=(m()-l)/ep())&0<=l)&0<=ep())&lpost=l)&cpost=0;>true".asSequent

    val inputs = CGenerator.getInputs(prg)
    CPrettyPrinter.printer = new CExpressionPlainPrettyPrinter(printDebugOut = true)
    val code = (new CMonitorGenerator())(testProg.subgoals.head.succ.head, stateVars.toSet, inputs, "Monitor")
    code._1 shouldBe
      """/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */
        |verdict boundaryDist(state pre, state curr, const parameters* const params) {
        |  if (((-1.0L) <= curr.f) && (curr.f <= ((params->m)-(pre.l))/(params->ep))) {
        |if ((0.0L <= pre.l) && (0.0L <= params->ep)) {
        |if (curr.l == pre.l) {
        |if (curr.c == 0.0L) {
        |verdict result = { .id=1, .val=(1.0L)/(((1.0L)/(-(fmaxl(-((curr.f)-((-1.0L))), -((((params->m)-(pre.l))/(params->ep))-(curr.f))))))+((1.0L)/(-(fmaxl(-(pre.l), -(params->ep)))))) }; return result;
        |} else {
        |printf("Failed %d=%s\n", -1, "cpost=0"); verdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl(curr.c, -(curr.c)))) }; return result;
        |}
        |} else {
        |printf("Failed %d=%s\n", -2, "lpost=l"); verdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.l)-(pre.l), -((curr.l)-(pre.l))))) }; return result;
        |}
        |} else {
        |printf("Failed %d=%s\n", -3, "0<=l&0<=ep()"); verdict result = { .id=-3, .val=((-1.0L))+(-(fmaxl(-(pre.l), -(params->ep)))) }; return result;
        |}
        |} else {
        |printf("Failed %d=%s\n", -4, "(-1)<=fpost&fpost<=(m()-l)/ep()"); verdict result = { .id=-4, .val=((-1.0L))+(-(fmaxl(-((curr.f)-((-1.0L))), -((((params->m)-(pre.l))/(params->ep))-(curr.f))))) }; return result;
        |};
        |}
        |
        |/* Evaluates monitor condition in prior and current state */
        |bool monitorSatisfied(state pre, state curr, const parameters* const params) {
        |  return boundaryDist(pre,curr,params).val >= 0.0L;
        |}
        |
        |/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */
        |state monitoredCtrl(state curr, const parameters* const params, const input* const in,
        |                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const)) {
        |  state pre = curr;
        |  state post = (*ctrl)(pre,params,in);
        |  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);
        |  else return post;
        |}
        |
        |""".stripMargin

    val monitorCode = (new CGenerator(new CMonitorGenerator()))(testProg2.subgoals.head.succ.head, stateVars.toSet, inputs, "Monitor")

    val codeFileContent =
      s"""
         |#include <stdio.h>
         |${monitorCode._1}
         |
         |state ctrl(state curr, const parameters* const params, const input* const in) { return curr; }
         |state fallback(state curr, const parameters* const params, const input* const in) { return curr; }
         |
         |int main() {
         |  return 0;
         |}
         |""".stripMargin

    val cmd = CodeGenTestTools.compileC(codeFileContent)
    val p = Runtime.getRuntime.exec(cmd)
    withClue(scala.io.Source.fromInputStream(p.getErrorStream).mkString) { p.waitFor() shouldBe 0 }
  }

  it should "find correct controller monitor condition from model file" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model, Variable("f"), Variable("l"), Variable("c"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)('R)
    val result = proveBy(modelplexInput, tactic)

    val expected = "(-1<=fpost_0&fpost_0<=(m-l)/ep)&(0<=l&0<=ep)&(fpost=fpost_0&lpost=l)&cpost=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expected

    report(expected, result, "Watertank controller monitor (backward tactic)")
  }

  it should "find correct controller monitor condition without intermediate Optimization 1" in withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank-ctrl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=false)(ModelPlex.controllerMonitorT)(1) & ModelPlex.optimizationOne()(1)
    val result = proveBy(model, tactic)

    // with ordinary diamond test
    val expected = "(-1<=fpost_0&fpost_0<=(m()-x)/ep())&fpost=fpost_0&xpost=x&tpost=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expected

    report(expected, result, "Watertank controller monitor (backward tactic)")
  }

  it should "work using the command line interface" taggedAs IgnoreInBuildTest in withTactics {
    // command line main has to initialize the prover itself, so dispose all test setup first
    afterEach()

    val inputFileName = "keymaerax-webui/src/test/resources/examples/casestudies/modelplex/watertank/watertank.key"
    val vars = "f,l,c"
    val outputFileName = File.createTempFile("watertank", ".kym").getAbsolutePath
    KeYmaeraX.main(Array("-tool", "mathematica", "-modelplex", inputFileName, "-vars", vars, "-monitor", "ctrl", "-out", outputFileName))

    val expectedFileContent = "(-1<=fpost&fpost<=(m()-l)/ep())&(0<=l&0<=ep())&lpost=l&cpost=0".asFormula

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    Parser(actualFileContent) shouldBe expectedFileContent
  }

//
//  ignore should "find correct model monitor condition" in {
//    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
//    val tactic = modelplexAxiomaticStyle(useOptOne=true)(modelMonitorT)(SuccPosition(0))
//    val result = helper.runTactic(tactic, new RootNode(s))
//
//    // with diamond test, after local QE
//    val expected = "-1<=fpost_0&fpost_0<=(m-l)/ep&(cpost_0=0&(ep=cpost&(l=0&(tpost_0=0&(cpost_0=ep&(fpost_0 < 0&(fpost=fpost_0&lpost=0)|(fpost_0=0&(fpost=0&lpost=0)|fpost_0>0&(fpost=fpost_0&lpost=0))))|tpost_0>0&(cpost_0=-1*tpost_0+ep&(fpost_0=0&(fpost=0&lpost=0)|fpost_0>0&(fpost=fpost_0&lpost=fpost_0*tpost_0))))|l>0&(tpost_0=0&(cpost_0=ep&(fpost_0 < 0&(fpost=fpost_0&lpost=l)|(fpost_0=0&(fpost=0&lpost=l)|fpost_0>0&(fpost=fpost_0&lpost=l))))|tpost_0>0&(cpost_0=-1*tpost_0+ep&(-1*tpost_0^-1*l<=fpost_0&fpost_0 < 0&(fpost=fpost_0&lpost=fpost_0*tpost_0+l)|(fpost_0=0&(fpost=0&lpost=l)|fpost_0>0&(fpost=fpost_0&lpost=fpost_0*tpost_0+l))))))|ep>cpost&(l=0&(tpost_0=0&(cpost_0=cpost&(fpost_0 < 0&(fpost=fpost_0&lpost=0)|(fpost_0=0&(fpost=0&lpost=0)|fpost_0>0&(fpost=fpost_0&lpost=0))))|tpost_0>0&(cpost_0=cpost+-1*tpost_0&(fpost_0=0&(fpost=0&lpost=0)|fpost_0>0&(fpost=fpost_0&lpost=fpost_0*tpost_0))))|l>0&(tpost_0=0&(cpost_0=cpost&(fpost_0 < 0&(fpost=fpost_0&lpost=l)|(fpost_0=0&(fpost=0&lpost=l)|fpost_0>0&(fpost=fpost_0&lpost=l))))|tpost_0>0&(cpost_0=cpost+-1*tpost_0&(-1*tpost_0^-1*l<=fpost_0&fpost_0 < 0&(fpost=fpost_0&lpost=fpost_0*tpost_0+l)|(fpost_0=0&(fpost=0&lpost=l)|fpost_0>0&(fpost=fpost_0&lpost=fpost_0*tpost_0+l))))))))".asFormula
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
  "Local lane control modelplex in place" should "find correct controller monitor condition" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc-ctrl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)('R)
    val result = proveBy(model, tactic)

    // with ordinary diamond test
    val expected = "(-B<=alpost_0&alpost_0<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&(-B<=afpost_0&afpost_0<=A)&xfpost=xf&vfpost=vf&afpost=afpost_0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0|vf=0&xfpost=xf&vfpost=vf&afpost=0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0|(-B<=afpost_0&afpost_0<=-b)&xfpost=xf&vfpost=vf&afpost=afpost_0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0)".asFormula

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
//    val expected = ("-B<=alpost_0 & alpost_0<=A & " +
//      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
//      "(-B<=afpost_0&afpost_0<=A&(xfpost=xf&vfpost=vf&afpost=afpost_0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0))) | " +
//      "((vf=0&(xfpost=xf&vfpost=vf&afpost=0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0)) | " +
//      "(-B<=afpost_0&afpost_0<=-b&(xfpost=xf&vfpost=vf&afpost=afpost_0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0))))").asFormula
//
//    result.openGoals() should have size 1
//    result.openGoals().flatMap(_.sequent.ante) should contain only
//      "xf < xl & xf + vf^2/(2*b) < xl + vl^2/(2*B) & B >= b & b > 0 & vf >= 0 & vl >= 0 & A >= 0 & ep > 0".asFormula
//    result.openGoals().flatMap(_.sequent.succ) should contain only expected
//
//    report(expected, result, "LLC controller monitor (backward tactic, from pre-fabricated conjecture)")
//  }
//
  it should "find correct controller monitor from model" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model,
      Variable("xl"), Variable("vl"), Variable("al"), Variable("xf"), Variable("vf"), Variable("af"), Variable("t"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(modelplexInput, tactic)

    val expected = "(-B<=alpost_0&alpost_0<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&(-B<=afpost_0&afpost_0<=A)&(vf>=0&vl>=0&0<=ep)&(((((xlpost=xl&vlpost=vl)&alpost=alpost_0)&xfpost=xf)&vfpost=vf)&afpost=afpost_0)&tpost=0|vf=0&(vf>=0&vl>=0&0<=ep)&(((((xlpost=xl&vlpost=vl)&alpost=alpost_0)&xfpost=xf)&vfpost=vf)&afpost=0)&tpost=0|(-B<=afpost_0&afpost_0<=-b)&(vf>=0&vl>=0&0<=ep)&(((((xlpost=xl&vlpost=vl)&alpost=alpost_0)&xfpost=xf)&vfpost=vf)&afpost=afpost_0)&tpost=0)".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "true".asFormula
    result.subgoals.head.succ should contain only expected

    report(expected, result, "LLC controller monitor (backward tactic)")
  }

  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xl"), Variable("vl"), Variable("al"), Variable("xf"), Variable("vf"), Variable("af"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists al ((-B()<=al&al<=A())&(xf+vf^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*vf) < xl+vl^2/(2*B())&\\exists af ((-B()<=af&af<=A())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=al&xfpost=xf&vfpost=vf&afpost=af&tpost=0)|vf=0&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=al&xfpost=xf&vfpost=vf&afpost=0&tpost=0|\\exists af ((-B()<=af&af<=-b())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=al&xfpost=xf&vfpost=vf&afpost=af&tpost=0)))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "(-B()<=alpost&alpost<=A())&(xf+vf^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*vf) < xl+vl^2/(2*B())&(-B()<=afpost&afpost<=A())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=alpost&xfpost=xf&vfpost=vf&afpost=afpost&tpost=0|vf=0&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=alpost&xfpost=xf&vfpost=vf&afpost=0&tpost=0|(-B()<=afpost&afpost<=-b())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=alpost&xfpost=xf&vfpost=vf&afpost=afpost&tpost=0)".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "(-B()<=alpost&alpost<=A())&(xf+vf^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*vf) < xl+vl^2/(2*B())&(-B()<=afpost&afpost<=A())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&xfpost=xf&vfpost=vf&tpost=0|vf=0&(vl>=0&0<=ep())&xlpost=xl&vlpost=vl&xfpost=xf&vfpost=0&afpost=0&tpost=0|(-B()<=afpost&afpost<=-b())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&xfpost=xf&vfpost=vf&tpost=0)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "LLC controller monitor (forward chase)")
  }

  "Fixedwing" should "find correct controller monitor" in withMathematica { implicit tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fixedwing_simple_nobound.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("a"), Variable("w"), Variable("xo"), Variable("theta"), Variable("dxy"), Variable("y"), Variable("t"), Variable("v"), Variable("dx"), Variable("w"), Variable("yo"), Variable("dz"), Variable("x"), Variable("dy"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "(v=Vmin()&(theta=Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=-W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy)|v>Vmin()&(theta=Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=-W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy))|\\exists a ((-B()<=a&a<=A())&\\exists w ((-W()<=w&w<=W())&\\exists v (v>=Vmin()&\\exists theta ((-Theta()<=theta&theta<=Theta())&\\exists xo \\exists yo ((abs(x-xo)>(v^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*v)&abs(x-xo)>(v^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(theta))/W()-(v-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*v)+Vmin()*ep()|abs(y-yo)>(v^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*v)&abs(y-yo)>(v^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(theta))/W()-(v-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*v)+Vmin()*ep())&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=a&wpost=w&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=w&yopost=yo&dzpost=dz&xpost=x&dypost=dy)))))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "(v=Vmin()&(theta=Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=-W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy)|v>Vmin()&(theta=Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=-W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy))|(-B()<=apost&apost<=A())&(-W()<=wpost&wpost<=W())&vpost>=Vmin()&(-Theta()<=thetapost&thetapost<=Theta())&(abs(x-xopost)>(vpost^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)&abs(x-xopost)>(vpost^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(thetapost))/W()-(vpost-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)+Vmin()*ep()|abs(y-yopost)>(vpost^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)&abs(y-yopost)>(vpost^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(thetapost))/W()-(vpost-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)+Vmin()*ep())&(0<=ep()&vpost>=Vmin()&-Theta()<=thetapost&thetapost<=Theta())&apost=apost&wpost=wpost&xopost=xopost&thetapost=thetapost&dxypost=dxy&ypost=y&tpost=0&vpost=vpost&dxpost=dx&wpost=wpost&yopost=yopost&dzpost=dz&xpost=x&dypost=dy".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "(v=Vmin()&(theta=Theta()&((dxy=dXY()&dz=dZ())&(theta!=-Theta()|dxy=-dXY()))&(0<=ep()&-Theta()<=theta)&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((theta!=Theta()|dxy=dXY()&dz=dZ())&dxy=-dXY()&dz=dZ())&(0<=ep()&theta<=Theta())&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&(theta!=-Theta()|dxy=-dXY()&dz=dZ())&(0<=ep()&-Theta()<=theta)&apost=0&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&(theta!=Theta()|dxy=dXY()&dz=dZ())&(0<=ep()&theta<=Theta())&apost=0&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy)|v>Vmin()&(theta=Theta()&((dxy=dXY()&dz=dZ())&(theta!=-Theta()|dxy=-dXY()))&(0<=ep()&-Theta()<=theta)&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((theta!=Theta()|dxy=dXY()&dz=dZ())&dxy=-dXY()&dz=dZ())&(0<=ep()&theta<=Theta())&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&(theta!=-Theta()|dxy=-dXY()&dz=dZ())&(0<=ep()&-Theta()<=theta)&apost=-B()&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&(theta!=Theta()|dxy=dXY()&dz=dZ())&(0<=ep()&theta<=Theta())&apost=-B()&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy))|(-B()<=apost&apost<=A())&(-W()<=wpost&wpost<=W())&vpost>=Vmin()&(-Theta()<=thetapost&thetapost<=Theta())&(abs(x-xopost)>(vpost^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)&abs(x-xopost)>(vpost^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(thetapost))/W()-(vpost-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)+Vmin()*ep()|abs(y-yopost)>(vpost^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)&abs(y-yopost)>(vpost^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(thetapost))/W()-(vpost-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)+Vmin()*ep())&0<=ep()&dxypost=dxy&ypost=y&tpost=0&dxpost=dx&dzpost=dz&xpost=x&dypost=dy".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "Fixedwing controller monitor (forward chase)")
  }

  // works but is super-slow (46min vs. 2s next with chase)
  "ETCS safety lemma modelplex in place" should "find correct controller monitor condition" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/icfem08/safetylemma-ctrl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=false)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(model, tactic)
    result.subgoals should have size 1
    result.subgoals.head.succ should have size 1

    report(result.subgoals.head.succ.head, result, "ETCS controller")
  }

//
//  ignore should "find correct controller monitor condition from model" in {
//    val in = getClass.getResourceAsStream("examples/casestudies/modelplex/icfem08/safetylemma.key")
//    val model = KeYmaeraXArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
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
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("vdes"), Variable("SB"), Variable("v"),
      Variable("state"), Variable("do"), Variable("z"), Variable("t"), Variable("mo"), Variable("m"), Variable("d"),
      Variable("a"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "(\\forall do (do=d->\\forall mo (mo=m->\\exists m \\exists d \\exists vdes ((d>=0&do^2-d^2<=2*b()*(m-mo)&vdes>=0)&vdespost=vdes&SBpost=SB&vpost=v&statepost=state&dopost=do&zpost=z&tpost=t&mopost=mo&mpost=m&dpost=d&apost=a)))|vdespost=vdes&SBpost=SB&vpost=v&statepost=brake&dopost=do&zpost=z&tpost=t&mopost=mo&mpost=m&dpost=d&apost=a)|v<=vdes&\\exists a ((a>=-b()&a<=A())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=a))|v>=vdes&\\exists a ((a < 0&a>=-b())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=a))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "((dpost>=0&d^2-dpost^2<=2*b()*(mpost-m)&vdespost>=0)&vdespost=vdespost&SBpost=SB&vpost=v&statepost=state&dopost=d&zpost=z&tpost=t&mopost=m&mpost=mpost&dpost=dpost&apost=a|vdespost=vdes&SBpost=SB&vpost=v&statepost=brake&dopost=do&zpost=z&tpost=t&mopost=mo&mpost=m&dpost=d&apost=a)|v<=vdes&(apost>=-b()&apost<=A())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=apost)|v>=vdes&(apost < 0&apost>=-b())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=apost)".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "((dpost>=0&d^2-dpost^2<=2*b()*(mpost-m)&vdespost>=0)&SBpost=SB&vpost=v&statepost=state&dopost=d&zpost=z&tpost=t&mopost=m&apost=a|vdespost=vdes&SBpost=SB&vpost=v&statepost=brake&dopost=do&zpost=z&tpost=t&mopost=mo&mpost=m&dpost=d&apost=a)|v<=vdes&(apost>=-b()&apost<=A())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d)|v>=vdes&(apost < 0&apost>=-b())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "ETCS controller monitor (forward chase)")
  }

  "RSS passive safety modelplex in place" should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists dxo \\exists dyo (dxo^2+dyo^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|\\exists a ((-B()<=a&a<=A())&\\exists r (r!=0&\\exists w (w*r=v&\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=a&rpost=r&tpost=0))))))".asFormula
    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "dxopost^2+dyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|(-B()<=apost&apost<=A())&rpost!=0&wpost*rpost=v&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xopost&yopost=yopost&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=wpost&apost=apost&rpost=rpost&tpost=0)".asFormula

    // Opt. 1 with less simplification
    val opt1AltResult = proveBy(foResult.subgoals.head, SaturateTactic(ModelPlex.optimizationOneWithSearch(None, assumptions)(1)))
    opt1AltResult.subgoals should have size 1
    opt1AltResult.subgoals.head.ante shouldBe empty
    opt1AltResult.subgoals.head.succ should contain only "dxopost^2+dyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|(-B()<=apost&apost<=A())&rpost!=0&wpost*rpost=v&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xopost&yopost=yopost&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=wpost&apost=apost&rpost=rpost&tpost=0)".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "dxopost^2+dyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|v=0&0<=ep()&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=0&wpost=0&apost=0&rpost=r&tpost=0|(-B()<=apost&apost<=A())&rpost!=0&wpost*rpost=v&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&tpost=0)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS controller monitor (forward chase)")
  }

  "RSS passive safety modelplex in place" should "find correct controller monitor by updateCalculus implicationally with Z3" in withZ3 { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists dxo \\exists dyo (dxo^2+dyo^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|\\exists a ((-B()<=a&a<=A())&\\exists r (r!=0&\\exists w (w*r=v&\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=a&rpost=r&tpost=0))))))".asFormula

    // Opt. 1 with less simplification
    val opt1AltResult = proveBy(foResult.subgoals.head, SaturateTactic(ModelPlex.optimizationOneWithSearch(None, assumptions)(1)))
    opt1AltResult.subgoals should have size 1
    opt1AltResult.subgoals.head.ante shouldBe empty
    opt1AltResult.subgoals.head.succ should contain only "dxopost^2+dyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|(-B()<=apost&apost<=A())&rpost!=0&wpost*rpost=v&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xopost&yopost=yopost&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=wpost&apost=apost&rpost=rpost&tpost=0)".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1AltResult.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "dxopost^2+dyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|v=0&0<=ep()&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=0&wpost=0&apost=0&rpost=r&tpost=0|(-B()<=apost&apost<=A())&rpost!=0&wpost*rpost=v&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&tpost=0)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS controller monitor (forward chase)")
  }

  // works but is super-slow
  it should "find the correct controller monitor condition from the input model" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(modelplexInput, tactic)

    val expectedSucc = "dxopost_0^2+dyopost_0^2<=V^2&((0<=ep&v>=0)&(((((((((((xopost=xo&yopost=yo)&dxopost=dxopost_0)&dyopost=dyopost_0)&xpost=x)&ypost=y)&dxpost=dx)&dypost=dy)&vpost=v)&wpost=w)&apost=-B)&rpost=r)&tpost=0|v=0&(0<=ep&v>=0)&(((((((((((xopost=xo&yopost=yo)&dxopost=dxopost_0)&dyopost=dyopost_0)&xpost=x)&ypost=y)&dxpost=dx)&dypost=dy)&vpost=v)&wpost=0)&apost=0)&rpost=r)&tpost=0|(-B<=apost_0&apost_0<=A)&rpost_0!=0&wpost_0*rpost_0=v&(abs(x-xopost_0)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yopost_0)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V)))&(0<=ep&v>=0)&(((((((((((xopost=xopost_0&yopost=yopost_0)&dxopost=dxopost_0)&dyopost=dyopost_0)&xpost=x)&ypost=y)&dxpost=dx)&dypost=dy)&vpost=v)&wpost=wpost_0)&apost=apost_0)&rpost=rpost_0)&tpost=0)".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expectedSucc

    report(expectedSucc, result, "RSS controller monitor (backward tactic)")
  }

  it should "work using the command line interface" taggedAs IgnoreInBuildTest in withTactics {
    // command line main has to initialize the prover itself, so dispose all test setup first
    afterEach()

    val inputFileName = "keymaerax-webui/src/test/resources/examples/casestudies/robix/passivesafetyabs.key"
    val vars = "xo,yo,dxo,dyo,x,y,dx,dy,v,w,a,r,t"
    val outputFileName = File.createTempFile("passivesafetyabs", ".kym").getAbsolutePath
    KeYmaeraX.main(Array("-tool", "mathematica", "-modelplex", inputFileName, "-vars", vars, "-monitor", "ctrl", "-out", outputFileName))

    val expectedFileContent = "dxopost^2+dyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|v=0&0<=ep()&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=0&wpost=0&apost=0&rpost=r&tpost=0|(-B()<=apost&apost<=A())&rpost!=0&wpost*rpost=v&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&tpost=0)".asFormula

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    Parser(actualFileContent) shouldBe expectedFileContent
  }

  "RSS passive orientation safety modelplex in place" should "extract the correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passiveorientationsafety.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("a"), Variable("r"),
      Variable("talpha"), Variable("odx"), Variable("ody"), Variable("ox"), Variable("oy"), Variable("dx"),
      Variable("dy"), Variable("w"), Variable("isVisible"), Variable("t"), Variable("v"), Variable("talpha"),
      Variable("x"), Variable("y"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists odx \\exists ody (odx^2+ody^2<=V()^2&(\\exists w (w*r=v&(0<=ep()&v>=0)&apost=-b()&rpost=r&talphapost=talpha&odxpost=odx&odypost=ody&oxpost=ox&oypost=oy&dxpost=dx&dypost=dy&wpost=w&isVisiblepost=isVisible&tpost=0&vpost=v&talphapost=talpha&xpost=x&ypost=y)|v=0&\\exists w (w*r=v&(0<=ep()&v>=0)&apost=0&rpost=r&talphapost=talpha&odxpost=odx&odypost=ody&oxpost=ox&oypost=oy&dxpost=-dx&dypost=-dy&wpost=w&isVisiblepost=isVisible&tpost=0&vpost=v&talphapost=talpha&xpost=x&ypost=y)|\\exists a ((-b()<=a&a<=A())&\\exists r (r!=0&\\exists ox \\exists oy \\exists isVisible (v+a*ep() < 0&(isVisible < 0|(x-ox>=0->x-ox>v^2/(-2*a)+V()*(v/(-a)))&(x-ox<=0->ox-x>v^2/(-2*a)+V()*(v/(-a)))|(y-oy>=0->y-oy>v^2/(-2*a)+V()*(v/(-a)))&(y-oy<=0->oy-y>v^2/(-2*a)+V()*(v/(-a))))&((r>=0->v^2/(-2*a) < alpha()*r)&(r < 0->v^2/(-2*a) < -alpha()*r))&\\exists w (w*r=v&(0<=ep()&v>=0)&apost=a&rpost=r&talphapost=0&odxpost=odx&odypost=ody&oxpost=ox&oypost=oy&dxpost=dx&dypost=dy&wpost=w&isVisiblepost=isVisible&tpost=0&vpost=v&talphapost=0&xpost=x&ypost=y)|v+a*ep()>=0&(isVisible < 0|(x-ox>=0->x-ox>v^2/(2*b())+V()*(v/b())+(a/b()+1)*(a/2*ep()^2+ep()*(v+V())))&(x-ox<=0->ox-x>v^2/(2*b())+V()*(v/b())+(a/b()+1)*(a/2*ep()^2+ep()*(v+V())))|(y-oy>=0->y-oy>v^2/(2*b())+V()*(v/b())+(a/b()+1)*(a/2*ep()^2+ep()*(v+V())))&(y-oy<=0->oy-y>v^2/(2*b())+V()*(v/b())+(a/b()+1)*(a/2*ep()^2+ep()*(v+V()))))&((r>=0->v^2/(2*b())+(a/b()+1)*(a/2*ep()^2+ep()*v) < alpha()*r)&(r < 0->v^2/(2*b())+(a/b()+1)*(a/2*ep()^2+ep()*v) < -alpha()*r))&\\exists w (w*r=v&(0<=ep()&v>=0)&apost=a&rpost=r&talphapost=0&odxpost=odx&odypost=ody&oxpost=ox&oypost=oy&dxpost=dx&dypost=dy&wpost=w&isVisiblepost=isVisible&tpost=0&vpost=v&talphapost=0&xpost=x&ypost=y))))))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "odxpost^2+odypost^2<=V()^2&(wpost*r=v&(0<=ep()&v>=0)&apost=-b()&rpost=r&talphapost=talpha&odxpost=odxpost&odypost=odypost&oxpost=ox&oypost=oy&dxpost=dx&dypost=dy&wpost=wpost&isVisiblepost=isVisible&tpost=0&vpost=v&talphapost=talpha&xpost=x&ypost=y|v=0&wpost*r=v&(0<=ep()&v>=0)&apost=0&rpost=r&talphapost=talpha&odxpost=odxpost&odypost=odypost&oxpost=ox&oypost=oy&dxpost=-dx&dypost=-dy&wpost=wpost&isVisiblepost=isVisible&tpost=0&vpost=v&talphapost=talpha&xpost=x&ypost=y|(-b()<=apost&apost<=A())&rpost!=0&(v+apost*ep() < 0&(isVisiblepost < 0|(x-oxpost>=0->x-oxpost>v^2/(-2*apost)+V()*(v/(-apost)))&(x-oxpost<=0->oxpost-x>v^2/(-2*apost)+V()*(v/(-apost)))|(y-oypost>=0->y-oypost>v^2/(-2*apost)+V()*(v/(-apost)))&(y-oypost<=0->oypost-y>v^2/(-2*apost)+V()*(v/(-apost))))&((rpost>=0->v^2/(-2*apost) < alpha()*rpost)&(rpost < 0->v^2/(-2*apost) < -alpha()*rpost))&wpost*rpost=v&(0<=ep()&v>=0)&apost=apost&rpost=rpost&talphapost=0&odxpost=odxpost&odypost=odypost&oxpost=oxpost&oypost=oypost&dxpost=dx&dypost=dy&wpost=wpost&isVisiblepost=isVisiblepost&tpost=0&vpost=v&talphapost=0&xpost=x&ypost=y|v+apost*ep()>=0&(isVisiblepost < 0|(x-oxpost>=0->x-oxpost>v^2/(2*b())+V()*(v/b())+(apost/b()+1)*(apost/2*ep()^2+ep()*(v+V())))&(x-oxpost<=0->oxpost-x>v^2/(2*b())+V()*(v/b())+(apost/b()+1)*(apost/2*ep()^2+ep()*(v+V())))|(y-oypost>=0->y-oypost>v^2/(2*b())+V()*(v/b())+(apost/b()+1)*(apost/2*ep()^2+ep()*(v+V())))&(y-oypost<=0->oypost-y>v^2/(2*b())+V()*(v/b())+(apost/b()+1)*(apost/2*ep()^2+ep()*(v+V()))))&((rpost>=0->v^2/(2*b())+(apost/b()+1)*(apost/2*ep()^2+ep()*v) < alpha()*rpost)&(rpost < 0->v^2/(2*b())+(apost/b()+1)*(apost/2*ep()^2+ep()*v) < -alpha()*rpost))&wpost*rpost=v&(0<=ep()&v>=0)&apost=apost&rpost=rpost&talphapost=0&odxpost=odxpost&odypost=odypost&oxpost=oxpost&oypost=oypost&dxpost=dx&dypost=dy&wpost=wpost&isVisiblepost=isVisiblepost&tpost=0&vpost=v&talphapost=0&xpost=x&ypost=y))".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "odxpost^2+odypost^2<=V()^2&(wpost*r=v&(0<=ep()&v>=0)&apost=-b()&rpost=r&talphapost=talpha&oxpost=ox&oypost=oy&dxpost=dx&dypost=dy&isVisiblepost=isVisible&tpost=0&vpost=v&xpost=x&ypost=y|v=0&wpost*r=0&0<=ep()&apost=0&rpost=r&talphapost=talpha&oxpost=ox&oypost=oy&dxpost=-dx&dypost=-dy&isVisiblepost=isVisible&tpost=0&vpost=0&xpost=x&ypost=y|(-b()<=apost&apost<=A())&rpost!=0&(v+apost*ep() < 0&(isVisiblepost < 0|(x-oxpost>=0->x-oxpost>v^2/(-2*apost)+V()*(v/(-apost)))&(x-oxpost<=0->oxpost-x>v^2/(-2*apost)+V()*(v/(-apost)))|(y-oypost>=0->y-oypost>v^2/(-2*apost)+V()*(v/(-apost)))&(y-oypost<=0->oypost-y>v^2/(-2*apost)+V()*(v/(-apost))))&((rpost>=0->v^2/(-2*apost) < alpha()*rpost)&(rpost < 0->v^2/(-2*apost) < -alpha()*rpost))&wpost*rpost=v&(0<=ep()&v>=0)&talphapost=0&dxpost=dx&dypost=dy&tpost=0&vpost=v&xpost=x&ypost=y|v+apost*ep()>=0&(isVisiblepost < 0|(x-oxpost>=0->x-oxpost>v^2/(2*b())+V()*(v/b())+(apost/b()+1)*(apost/2*ep()^2+ep()*(v+V())))&(x-oxpost<=0->oxpost-x>v^2/(2*b())+V()*(v/b())+(apost/b()+1)*(apost/2*ep()^2+ep()*(v+V())))|(y-oypost>=0->y-oypost>v^2/(2*b())+V()*(v/b())+(apost/b()+1)*(apost/2*ep()^2+ep()*(v+V())))&(y-oypost<=0->oypost-y>v^2/(2*b())+V()*(v/b())+(apost/b()+1)*(apost/2*ep()^2+ep()*(v+V()))))&((rpost>=0->v^2/(2*b())+(apost/b()+1)*(apost/2*ep()^2+ep()*v) < alpha()*rpost)&(rpost < 0->v^2/(2*b())+(apost/b()+1)*(apost/2*ep()^2+ep()*v) < -alpha()*rpost))&wpost*rpost=v&(0<=ep()&v>=0)&talphapost=0&dxpost=dx&dypost=dy&tpost=0&vpost=v&xpost=x&ypost=y))".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS passive orientation controller monitor (forward chase)")
  }

  "RSS passive safety curve straight" should "find correct controller monitor" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists dxo \\exists dyo (dxo^2+dyo^2<=V()^2&((w=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|w!=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0)|v=0&(0=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|0!=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0)|\\exists a ((-B()<=a&a<=A())&(\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=a&rpost=r&tpost=0|0!=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=a&rpost=r&tpost=0))|\\exists r (r!=0&\\exists w (w*r=v&\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(w=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=a&rpost=r&tpost=0|w!=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=a&rpost=r&tpost=0))))))))".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "dxopost^2+dyopost^2<=V()^2&((w=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0|w!=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0)|v=0&(0=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|0!=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0)|(-B()<=apost&apost<=A())&((abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0=0&(0<=ep()&v>=0)&xopost=xopost&yopost=yopost&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=apost&rpost=r&tpost=0|0!=0&(0<=ep()&v>=0)&xopost=xopost&yopost=yopost&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=apost&rpost=r&tpost=0)|rpost!=0&wpost*rpost=v&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(wpost=0&(0<=ep()&v>=0)&xopost=xopost&yopost=yopost&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=wpost&apost=apost&rpost=rpost&tpost=0|wpost!=0&(0<=ep()&v>=0)&xopost=xopost&yopost=yopost&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=wpost&apost=apost&rpost=rpost&tpost=0)))".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "dxopost^2+dyopost^2<=V()^2&((w=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=-B()&rpost=r&tpost=0|w!=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&rpost=r&tpost=0)|v=0&0<=ep()&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=0&wpost=0&apost=0&rpost=r&tpost=0|(-B()<=apost&apost<=A())&((abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&rpost=r&tpost=0|rpost!=0&wpost*rpost=v&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(wpost=0&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&tpost=0|wpost!=0&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&tpost=0)))".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS controller monitor (forward chase)")
  }

  it should "find correct controller monitor test program" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("r"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    val opt1Result = proveBy(foResult.subgoals.head, SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)))

    val testResult = proveBy(opt1Result.subgoals.head, ModelPlex.chaseToTests(combineTests=false)(1))
    testResult.subgoals.loneElement shouldBe "==> <?dxopost^2+dyopost^2<=V()^2;>((<?w=0;><?0<=ep()&v>=0;><?xopost=xo;><?yopost=yo;><?dxopost=dxopost;><?dyopost=dyopost;><?xpost=x;><?ypost=y;><?dxpost=dx;><?dypost=dy;><?vpost=v;><?wpost=w;><?apost=-B();><?rpost=r;><?tpost=0;>true|<?w!=0;><?0<=ep()&v>=0;><?xopost=xo;><?yopost=yo;><?dxopost=dxopost;><?dyopost=dyopost;><?xpost=x;><?ypost=y;><?dxpost=dx;><?dypost=dy;><?vpost=v;><?wpost=w;><?apost=-B();><?rpost=r;><?tpost=0;>true)|<?v=0;>(<?0=0;><?0<=ep()&v>=0;><?xopost=xo;><?yopost=yo;><?dxopost=dxopost;><?dyopost=dyopost;><?xpost=x;><?ypost=y;><?dxpost=dx;><?dypost=dy;><?vpost=v;><?wpost=0;><?apost=0;><?rpost=r;><?tpost=0;>true|<?0!=0;><?0<=ep()&v>=0;><?xopost=xo;><?yopost=yo;><?dxopost=dxopost;><?dyopost=dyopost;><?xpost=x;><?ypost=y;><?dxpost=dx;><?dypost=dy;><?vpost=v;><?wpost=0;><?apost=0;><?rpost=r;><?tpost=0;>true)|<?-B()<=apost&apost<=A();>(<?abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()));>(<?0=0;><?0<=ep()&v>=0;><?xopost=xopost;><?yopost=yopost;><?dxopost=dxopost;><?dyopost=dyopost;><?xpost=x;><?ypost=y;><?dxpost=dx;><?dypost=dy;><?vpost=v;><?wpost=0;><?apost=apost;><?rpost=r;><?tpost=0;>true|<?0!=0;><?0<=ep()&v>=0;><?xopost=xopost;><?yopost=yopost;><?dxopost=dxopost;><?dyopost=dyopost;><?xpost=x;><?ypost=y;><?dxpost=dx;><?dypost=dy;><?vpost=v;><?wpost=0;><?apost=apost;><?rpost=r;><?tpost=0;>true)|<?rpost!=0;><?wpost*rpost=v;><?abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()));>(<?wpost=0;><?0<=ep()&v>=0;><?xopost=xopost;><?yopost=yopost;><?dxopost=dxopost;><?dyopost=dyopost;><?xpost=x;><?ypost=y;><?dxpost=dx;><?dypost=dy;><?vpost=v;><?wpost=wpost;><?apost=apost;><?rpost=rpost;><?tpost=0;>true|<?wpost!=0;><?0<=ep()&v>=0;><?xopost=xopost;><?yopost=yopost;><?dxopost=dxopost;><?dyopost=dyopost;><?xpost=x;><?ypost=y;><?dxpost=dx;><?dypost=dy;><?vpost=v;><?wpost=wpost;><?apost=apost;><?rpost=rpost;><?tpost=0;>true)))".asSequent
  }

  "RSS passive safety curve straight curvature" should "find correct controller monitor" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs_curvestraight_curvature.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xo"), Variable("yo"), Variable("dxo"), Variable("dyo"), Variable("x"), Variable("y"), Variable("dx"),
      Variable("dy"), Variable("v"), Variable("w"), Variable("a"), Variable("k"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals.loneElement.ante shouldBe empty
    foResult.subgoals.loneElement.succ.loneElement shouldBe "\\exists dxo \\exists dyo (dxo^2+dyo^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&kpost=k&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&kpost=k&tpost=0|\\exists a ((-B()<=a&a<=A())&\\exists k \\exists w (v*k=w&\\exists xo \\exists yo ((abs(x-xo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yo)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxo&dyopost=dyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=a&kpost=k&tpost=0)))))".asFormula

    //Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)))
    opt1Result.subgoals.loneElement.ante shouldBe empty
    opt1Result.subgoals.loneElement.succ.loneElement shouldBe "dxopost^2+dyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&kpost=k&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&kpost=k&tpost=0|(-B()<=apost&apost<=A())&v*kpost=wpost&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xopost&yopost=yopost&dxopost=dxopost&dyopost=dyopost&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=wpost&apost=apost&kpost=kpost&tpost=0)".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals.loneElement.ante shouldBe empty
    simplifiedResult.subgoals.loneElement.succ.loneElement shouldBe "dxopost^2+dyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-B()&kpost=k&tpost=0|v=0&0<=ep()&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=0&wpost=0&apost=0&kpost=k&tpost=0|(-B()<=apost&apost<=A())&v*kpost=wpost&(abs(x-xopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*B())+V()*v/B()+(A()/B()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&tpost=0)".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "RSS controller monitor (forward chase)")
  }
//
//  ignore should "extract the correct controller monitor" in {
//    val in = getClass.getResourceAsStream("examples/casestudies/robix/passiveorientationsafety.key")
//    val model = KeYmaeraXArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
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
//    val expectedSucc = "odxpost_0^2+odypost_0^2<=V()^2&(wpost_0*r=v&(apost=-b()&rpost=r&talphapost=talpha&odxpost=odxpost_0&odypost=odypost_0&oxpost=ox&oypost=oy&dxpost=dx&dypost=dy&wpost=wpost_0&isVisiblepost=isVisible&tpost=0)|(v=0&(wpost_0*r=v&(apost=0&rpost=r&talphapost=talpha&odxpost=odxpost_0&odypost=odypost_0&oxpost=ox&oypost=oy&dxpost=-dx&dypost=-dy&wpost=wpost_0&isVisiblepost=isVisible&tpost=0))|-b()<=apost_0&apost_0<=A&(rpost_0!=0&(v+apost_0*ep < 0&((isVisiblepost_0 < 0|((x-oxpost_0>=0->x-oxpost_0>v^2/(-2*apost_0)+V()*(v/-apost_0))&(x-oxpost_0<=0->oxpost_0-x>v^2/(-2*apost_0)+V()*(v/-apost_0))|(y-oypost_0>=0->y-oypost_0>v^2/(-2*apost_0)+V()*(v/-apost_0))&(y-oypost_0<=0->oypost_0-y>v^2/(-2*apost_0)+V()*(v/-apost_0))))&((rpost_0>=0->v^2/(-2*apost_0) < alpha()*rpost_0)&(rpost_0 < 0->v^2/(-2*apost_0) < -alpha()*rpost_0)&(wpost_0*rpost_0=v&(apost=apost_0&rpost=rpost_0&talphapost=0&odxpost=odxpost_0&odypost=odypost_0&oxpost=oxpost_0&oypost=oypost_0&dxpost=dx&dypost=dy&wpost=wpost_0&isVisiblepost=isVisiblepost_0&tpost=0))))|v+apost_0*ep>=0&((isVisiblepost_0 < 0|((x-oxpost_0>=0->x-oxpost_0>v^2/(2*b())+V()*(v/b())+(apost_0/b()+1)*(apost_0/2*ep^2+ep*(v+V())))&(x-oxpost_0<=0->oxpost_0-x>v^2/(2*b())+V()*(v/b())+(apost_0/b()+1)*(apost_0/2*ep^2+ep*(v+V())))|(y-oypost_0>=0->y-oypost_0>v^2/(2*b())+V()*(v/b())+(apost_0/b()+1)*(apost_0/2*ep^2+ep*(v+V())))&(y-oypost_0<=0->oypost_0-y>v^2/(2*b())+V()*(v/b())+(apost_0/b()+1)*(apost_0/2*ep^2+ep*(v+V())))))&((rpost_0>=0->v^2/(2*b())+(apost_0/b()+1)*(apost_0/2*ep^2+ep*v) < alpha()*rpost_0)&(rpost_0 < 0->v^2/(2*b())+(apost_0/b()+1)*(apost_0/2*ep^2+ep*v) < -alpha()*rpost_0)&(wpost_0*rpost_0=v&(apost=apost_0&rpost=rpost_0&talphapost=0&odxpost=odxpost_0&odypost=odypost_0&oxpost=oxpost_0&oypost=oypost_0&dxpost=dx&dypost=dy&wpost=wpost_0&isVisiblepost=isVisiblepost_0&tpost=0))))))))".asFormula
//
//    result.openGoals() should have size 1
//    result.openGoals().head.sequent.ante should contain only expectedAnte
//    result.openGoals().head.sequent.succ should contain only expectedSucc
//
//    report(result.openGoals().head.sequent.succ.head, result, "RSS passive orientation safety controller monitor (backward tactic)")
//  }
//
  "Hybrid quadcopter" should "extract the correct controller monitor" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/quadcopter/hybridquadrotor.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model, Variable("href"), Variable("v"), Variable("h"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(modelplexInput, tactic)

    val expectedSucc = "(h>=hrefpost_0&hrefpost_0>0&((kp < 0&v=0&hrefpost_0>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&hrefpost_0=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*hrefpost_0*kp^2+hrefpost_0^2*kp^2+h*kd()*kp*v-hrefpost_0*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>hrefpost_0)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*hrefpost_0*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*hrefpost_0*kp)|kp>0&v=0&(h!=hrefpost_0&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>hrefpost_0|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*hrefpost_0*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*hrefpost_0*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*hrefpost_0*kp|2*hrefpost_0*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*hrefpost_0*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*hrefpost_0*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*hrefpost_0*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*hrefpost_0*kp|2*hrefpost_0*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*hrefpost_0*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*hrefpost_0*kp^2+hrefpost_0^2*kp^2+h*kd()*kp*v-hrefpost_0*kd()*kp*v+kp*v^2=0))&true&(hrefpost=hrefpost_0&vpost=v)&hpost=h".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only expectedSucc

    report(result.subgoals.head.succ.head, result, "Hybrid quadcopter controller monitor (backward tactic)")
  }

  it should "extract the correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/quadcopter/hybridquadrotor.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, Variable("href"), Variable("v"), Variable("h"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "\\exists href ((h>=href&href>0&((kp < 0&v=0&href>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*href*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*href*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&href=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*href*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*href*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*href*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*href*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*href*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*href*kp^2+href^2*kp^2+h*kd()*kp*v-href*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>href)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*href*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*href*kp)|kp>0&v=0&(h!=href&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>href|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*href*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*href*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*href*kp|2*href*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*href*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*href*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*href*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*href*kp|2*href*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*href*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*href*kp^2+href^2*kp^2+h*kd()*kp*v-href*kd()*kp*v+kp*v^2=0))&hrefpost=href&vpost=v&hpost=h)".asFormula

    // Opt. 1
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only "(h>=hrefpost&hrefpost>0&((kp < 0&v=0&hrefpost>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*hrefpost*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*hrefpost*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&hrefpost=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*hrefpost*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*hrefpost*kp^2+hrefpost^2*kp^2+h*kd()*kp*v-hrefpost*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>hrefpost)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*hrefpost*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*hrefpost*kp)|kp>0&v=0&(h!=hrefpost&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>hrefpost|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*hrefpost*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*hrefpost*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*hrefpost*kp|2*hrefpost*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*hrefpost*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*hrefpost*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*hrefpost*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*hrefpost*kp|2*hrefpost*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*hrefpost*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*hrefpost*kp^2+hrefpost^2*kp^2+h*kd()*kp*v-hrefpost*kd()*kp*v+kp*v^2=0))&hrefpost=hrefpost&vpost=v&hpost=h".asFormula

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals.loneElement.ante shouldBe empty
    simplifiedResult.subgoals.loneElement.succ.loneElement shouldBe "(h>=hrefpost&hrefpost>0&((kp < 0&v=0&hrefpost>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*hrefpost*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*hrefpost*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&hrefpost=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*hrefpost*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*hrefpost*kp^2+hrefpost^2*kp^2+h*kd()*kp*v-hrefpost*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>hrefpost)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*hrefpost*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*hrefpost*kp)|kp>0&v=0&(h!=hrefpost&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>hrefpost|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*hrefpost*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*hrefpost*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*hrefpost*kp|2*hrefpost*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*hrefpost*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*hrefpost*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*hrefpost*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*hrefpost*kp|2*hrefpost*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*hrefpost*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*hrefpost*kp^2+hrefpost^2*kp^2+h*kd()*kp*v-hrefpost*kd()*kp*v+kp*v^2=0))&vpost=v&hpost=h".asFormula

    report(simplifiedResult.subgoals.head.succ.head, simplifiedResult, "Hybrid quadcopter controller monitor (forward chase)")
  }

  "VSL modelplex in place" should "find correct controller monitor condition" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl-ctrl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(model, tactic)

    // with ordinary diamond test
    val expected = "(x1post=x1&v1post=v1&a1post=-B&tpost=0&vslpost=vsl&xslpost=xsl|(vslpost_0>=0&xslpost_0>=x1+(v1^2-vslpost_0^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post=x1&v1post=v1&a1post=-B&tpost=0&vslpost=vslpost_0&xslpost=xslpost_0)|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post_0&a1post_0<=A)&(x1post=x1&v1post=v1&a1post=a1post_0&tpost=0&vslpost=vsl&xslpost=xsl|(vslpost_0>=0&xslpost_0>=x1+(v1^2-vslpost_0^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post=x1&v1post=v1&a1post=a1post_0&tpost=0&vslpost=vslpost_0&xslpost=xslpost_0)|x1>=xsl&(-B<=a1post_0&a1post_0<=A&a1post_0<=(v1-vsl)/ep)&(x1post=x1&v1post=v1&a1post=a1post_0&tpost=0&vslpost=vsl&xslpost=xsl|(vslpost_0>=0&xslpost_0>=x1+(v1^2-vslpost_0^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post=x1&v1post=v1&a1post=a1post_0&tpost=0&vslpost=vslpost_0&xslpost=xslpost_0)".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only
      "v1>=0&vsl>=0&x1<=xsl&2*B*(xsl-x1)>=v1^2-vsl^2&A>=0&B>0&ep>0".asFormula
    result.subgoals.head.succ should contain only expected

    report(expected, result, "VSL controller (backward tactic from prefabricated conjecture)")
  }

  it should "find correct controller monitor condition from input file" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = createMonitorSpecificationConjecture(model,
      Variable("xsl"), Variable("vsl"), Variable("x1"), Variable("v1"), Variable("a1"), Variable("t"))

    val tactic = ModelPlex.modelplexAxiomaticStyle(useOptOne=true)(ModelPlex.controllerMonitorT)(1)
    val result = proveBy(modelplexInput, tactic)

    // with ordinary diamond test
    val expected = "((((xslpost=xsl&vslpost=vsl)&x1post=x1)&v1post=v1)&a1post=-B)&tpost=t|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post_0&a1post_0<=A)&((((xslpost=xsl&vslpost=vsl)&x1post=x1)&v1post=v1)&a1post=a1post_0)&tpost=t|x1>=xsl&(-B<=a1post_0&a1post_0<=A&a1post_0<=(v1-vsl)/ep)&((((xslpost=xsl&vslpost=vsl)&x1post=x1)&v1post=v1)&a1post=a1post_0)&tpost=t|(vslpost_0>=0&xslpost_0>=x1+(v1^2-vslpost_0^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&(v1>=0&0<=ep)&((((xslpost=xslpost_0&vslpost=vslpost_0)&x1post=x1)&v1post=v1)&a1post=a1)&tpost=0".asFormula

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "true".asFormula
    result.subgoals.head.succ should contain only expected

    report(expected, result, "VSL controller monitor (backward tactic)")
  }

  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("xsl"), Variable("vsl"), Variable("x1"), Variable("v1"), Variable("a1"), Variable("t"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=-B()&tpost=t|xsl>=x1+(v1^2-vsl^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1)&\\exists a1 ((-B()<=a1&a1<=A())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=a1&tpost=t)|x1>=xsl&\\exists a1 ((-B()<=a1&a1<=A()&a1<=(v1-vsl)/ep())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=a1&tpost=t)|\\exists xsl \\exists vsl ((vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1))&(v1>=0&0<=ep())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=a1&tpost=0)".asFormula

    // Opt. 1
    val expected = "xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=-B()&tpost=t|xsl>=x1+(v1^2-vsl^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1)&(-B()<=a1post&a1post<=A())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=a1post&tpost=t|x1>=xsl&(-B()<=a1post&a1post<=A()&a1post<=(v1-vsl)/ep())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=a1post&tpost=t|(vslpost>=0&xslpost>=x1+(v1^2-vslpost^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1))&(v1>=0&0<=ep())&xslpost=xslpost&vslpost=vslpost&x1post=x1&v1post=v1&a1post=a1&tpost=0".asFormula
    val opt1Result = proveBy(foResult.subgoals.head, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1))
    opt1Result.subgoals should have size 1
    opt1Result.subgoals.head.ante shouldBe empty
    opt1Result.subgoals.head.succ should contain only expected

    // simplify
    val simplifiedResult = proveBy(opt1Result.subgoals.head, ModelPlex.simplify())
    simplifiedResult.subgoals should have size 1
    simplifiedResult.subgoals.head.ante shouldBe empty
    simplifiedResult.subgoals.head.succ should contain only "xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=-B()&tpost=t|xsl>=x1+(v1^2-vsl^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1)&(-B()<=a1post&a1post<=A())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&tpost=t|x1>=xsl&(-B()<=a1post&a1post<=A()&a1post<=(v1-vsl)/ep())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&tpost=t|(vslpost>=0&xslpost>=x1+(v1^2-vslpost^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1))&(v1>=0&0<=ep())&x1post=x1&v1post=v1&a1post=a1&tpost=0".asFormula

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
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("a"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&xpost=x&vpost=v&apost=A&tpost=0|v=0&0<=ep&xpost=x&vpost=0&apost=0&tpost=0|(v>=0&0<=ep)&xpost=x&vpost=v&apost=-b&tpost=0".asFormula

    val Or(acc,Or(coast,brake)) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&xpost=x&vpost=v&apost=A&tpost=0".asFormula
    coast shouldBe "v=0&0<=ep&xpost=x&vpost=0&apost=0&tpost=0".asFormula
    brake shouldBe "(v>=0&0<=ep)&xpost=x&vpost=v&apost=-b&tpost=0".asFormula
  }

  it should "find correct controller monitor for stopsign with direct v control" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=ep*vpost&0<=ep&xpost=x&tpost=0|0<=ep&xpost=x&vpost=0&tpost=0".asFormula

    val Or(acc,stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*vpost&0<=ep&xpost=x&tpost=0".asFormula
    stop shouldBe "0<=ep&xpost=x&vpost=0&tpost=0".asFormula
  }

  it should "find correct controller monitor for stopsign with direct v change and disturbance" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("d"), Variable("c"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "S-x>=ep*(v+cpost+D)&(-D<=dpost&dpost<=D)&0<=ep&xpost=x&vpost=v&tpost=0|0<=ep&xpost=x&vpost=0&dpost=0&cpost=0&tpost=0".asFormula

    val Or(acc,stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*(v+cpost+D)&(-D<=dpost&dpost<=D)&0<=ep&xpost=x&vpost=v&tpost=0".asFormula
    stop shouldBe "0<=ep&xpost=x&vpost=0&dpost=0&cpost=0&tpost=0".asFormula
  }

  it should "find correct model monitor for stopsign" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("a"), Variable("t"))

    val mxResult = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1))
    mxResult.subgoals.loneElement shouldBe "==> S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&\\exists t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->A*s_+v>=0&s_+0<=ep)&xpost=A*(t_^2/2)+v*t_+x&vpost=A*t_+v&apost=A&tpost=t_+0)|v=0&\\exists t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->0*s_+v>=0&s_+0<=ep)&xpost=0*(t_^2/2)+v*t_+x&vpost=0*t_+v&apost=0&tpost=t_+0)|\\exists t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->(-b)*s_+v>=0&s_+0<=ep)&xpost=(-b)*(t_^2/2)+v*t_+x&vpost=(-b)*t_+v&apost=-b&tpost=t_+0)".asSequent
    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(mxResult, SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1))
    result.subgoals.loneElement shouldBe "==> S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((A>=0&b>0)&ep>0)&(((((((((tpost=0&(A=0|A=apost))&(apost=0|A=apost))&(apost=0|A>0))&(v=0|v=vpost))&v>=0)&(vpost=0|v=vpost))&(vpost=0|v>0))&x=xpost|(tpost>0&tpost < ep)&((A=0&apost=0)&((v=0&vpost=0)&x=xpost|(v=vpost&tpost*v+x=xpost)&v>0)|(A=apost&A>0)&((A*tpost=vpost&v=0)&xpost=1/2*A*tpost^2+x|(A*tpost+v=vpost&xpost=1/2*A*tpost^2+tpost*v+x)&v>0)))|ep=tpost&((A=0&apost=0)&((v=0&vpost=0)&x=xpost|(v=vpost&tpost*v+x=xpost)&v>0)|(A=apost&A>0)&((A*tpost=vpost&v=0)&xpost=1/2*A*tpost^2+x|(A*tpost+v=vpost&xpost=1/2*A*tpost^2+tpost*v+x)&v>0)))|v=0&((A>=0&b>0)&ep>0)&(((tpost>=0&ep>=tpost)&x=xpost)&0=vpost)&apost=0|((A>=0&b>0)&ep>0)&((((v=0&vpost=0)&x=xpost)&apost+b=0)&tpost=0|(v>0&apost+b=0)&((tpost=0&v=vpost)&x=xpost|(1/2*b*tpost^2+xpost=tpost*v+x&ep>=tpost)&(b*tpost=v&vpost=0|(b*tpost+vpost=v&vpost>0)&vpost < v)))".asSequent
    val Or(acc,Or(coast,brake)) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((A>=0&b>0)&ep>0)&(((((((((tpost=0&(A=0|A=apost))&(apost=0|A=apost))&(apost=0|A>0))&(v=0|v=vpost))&v>=0)&(vpost=0|v=vpost))&(vpost=0|v>0))&x=xpost|(tpost>0&tpost < ep)&((A=0&apost=0)&((v=0&vpost=0)&x=xpost|(v=vpost&tpost*v+x=xpost)&v>0)|(A=apost&A>0)&((A*tpost=vpost&v=0)&xpost=1/2*A*tpost^2+x|(A*tpost+v=vpost&xpost=1/2*A*tpost^2+tpost*v+x)&v>0)))|ep=tpost&((A=0&apost=0)&((v=0&vpost=0)&x=xpost|(v=vpost&tpost*v+x=xpost)&v>0)|(A=apost&A>0)&((A*tpost=vpost&v=0)&xpost=1/2*A*tpost^2+x|(A*tpost+v=vpost&xpost=1/2*A*tpost^2+tpost*v+x)&v>0)))".asFormula
    coast shouldBe "v=0&((A>=0&b>0)&ep>0)&(((tpost>=0&ep>=tpost)&x=xpost)&0=vpost)&apost=0".asFormula
    brake shouldBe "((A>=0&b>0)&ep>0)&((((v=0&vpost=0)&x=xpost)&apost+b=0)&tpost=0|(v>0&apost+b=0)&((tpost=0&v=vpost)&x=xpost|(1/2*b*tpost^2+xpost=tpost*v+x&ep>=tpost)&(b*tpost=v&vpost=0|(b*tpost+vpost=v&vpost>0)&vpost < v)))".asFormula
  }

  it should "find correct model monitor for stopsign with direct v control" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1))
    result.subgoals.loneElement shouldBe "==> S-x>=ep*vpost&ep>0&(tpost>=0&ep>=tpost)&tpost*vpost+x=xpost|ep>0&((tpost>=0&ep>=tpost)&x=xpost)&vpost=0".asSequent

    val Or(acc,stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*vpost&ep>0&(tpost>=0&ep>=tpost)&tpost*vpost+x=xpost".asFormula
    stop shouldBe "ep>0&((tpost>=0&ep>=tpost)&x=xpost)&vpost=0".asFormula
  }

  it should "find correct model monitor for stopsign with direct v change and disturbance" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("x"), Variable("v"), Variable("d"), Variable("c"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1))
    result.subgoals.loneElement shouldBe "==> S-x>=ep*(v+cpost+D)&(-D<=dpost&dpost<=D)&(ep>0&D>=0)&((tpost>=0&ep>=tpost)&tpost*(cpost+dpost+v)+x=xpost)&v=vpost|(ep>0&D>=0)&((((tpost>=0&ep>=tpost)&x=xpost)&vpost=0)&dpost=0)&cpost=0".asSequent

    val Or(acc,stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*(v+cpost+D)&(-D<=dpost&dpost<=D)&(ep>0&D>=0)&((tpost>=0&ep>=tpost)&tpost*(cpost+dpost+v)+x=xpost)&v=vpost".asFormula
    stop shouldBe "(ep>0&D>=0)&((((tpost>=0&ep>=tpost)&x=xpost)&vpost=0)&dpost=0)&cpost=0".asFormula
  }

  "PLDI17" should "prove velocity car safety" taggedAs IgnoreInBuildTest in withMathematica { _ =>
    //@note run this test with -DPLDI17_BASE_DIR=/path/to/paper
    val baseDir = System.getProperty("PLDI17_BASE_DIR")
    val entry = ArchiveParser.parser.parseFromFile(s"$baseDir/velocitycar_dist.kyx#Velocity Car Safety").head
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3) shouldBe 'proved
  }

  it should "derive controller monitor for velocity car safety" taggedAs IgnoreInBuildTest in withMathematica { tool =>
    //@note run this test with -DPLDI17_BASE_DIR=/path/to/paper
    val baseDir = System.getProperty("PLDI17_BASE_DIR")
    val entry = ArchiveParser.parser.parseFromFile(s"$baseDir/velocitycar_dist.kyx#Velocity Car Safety").head
    val model = entry.model.asInstanceOf[Formula]
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model,
      Variable("d"), Variable("v"), Variable("t"))

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) & simplifier(1))
    result.subgoals.loneElement shouldBe "==> d>=V()*ep()&(0<=vpost&vpost<=V())&0<=ep()&dpost=d&tpost=0|0<=ep()&dpost=d&vpost=0&tpost=0".asSequent
  }

  it should "prove controller monitor correctness" taggedAs IgnoreInBuildTest in withMathematica { _ =>
    //@note run this test with -DPLDI17_BASE_DIR=/path/to/paper
    val baseDir = System.getProperty("PLDI17_BASE_DIR")
    val entry = ArchiveParser.parser.parseFromFile(s"$baseDir/velocitycar_dist.kyx#Controller Monitor Formula Implies Controller Monitor Specification").head
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3) shouldBe 'proved
  }

  it should "generate a correct sandbox conjecture" taggedAs IgnoreInBuildTest in withMathematica { _ => withDatabase { db =>
    //@note run this test with -DPLDI17_BASE_DIR=/path/to/paper
    val baseDir = System.getProperty("PLDI17_BASE_DIR")
    val entry = ArchiveParser.parser.parseFromFile(s"$baseDir/velocitycar_dist.kyx#Velocity Car Safety").head
    val fallback = "t:=0;v:=0;".asProgram
    val ((sandbox, sbTactic), lemmas) = ModelPlex.createSandbox(entry.name, entry.tactics.head._3,
      Some(fallback), 'ctrl, None)(entry.model.asInstanceOf[Formula])

    sandbox shouldBe
      """
        |[{V:=*;ep:=*;}
        | {d:=*;t:=*;}
        | ?d>=0&v=0&t=0&V>=0&ep>=0;
        | {{tpost:=*;vpost:=*;}
        |  {  ?  d>=V*ep&(0<=vpost&vpost<=V)&0<=ep&dpost=d&tpost=0|0<=ep&dpost=d&tpost=0&vpost=0;t:=tpost;v:=vpost;
        |   ++?!(d>=V*ep&(0<=vpost&vpost<=V)&0<=ep&dpost=d&tpost=0|0<=ep&dpost=d&tpost=0&vpost=0);t:=0;v:=0;
        |  }
        |  {dpost:=*;tpost:=*;}
        |  ?tpost>=0&v>=0&dpost>=v*(ep-tpost)&tpost<=ep;
        |  d:=dpost;t:=tpost;
        | }*]d>=0
      """.stripMargin.asFormula

    def defs(f: Formula): Declaration = Declaration(Map.empty)

    val lemmaEntries = lemmas.map({ case (name, fml, tactic) =>
      val serializableTactic = db.extractSerializableTactic(fml, tactic)
      ParsedArchiveEntry(name, "lemma", "", "", defs(fml), fml,
      (name + " Proof", BellePrettyPrinter(serializableTactic), serializableTactic)::Nil, Nil, Map.empty)})
    val lemmaTempArchive = lemmaEntries.map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))(_)).mkString("\n\n")
    checkArchiveEntries(ArchiveParser.parse(lemmaTempArchive))

    val serializableTactic = db.extractSerializableTactic(sandbox, sbTactic)
    val sandboxEntry = ParsedArchiveEntry(entry.name + " Sandbox", "theorem", "", "", defs(sandbox),
      sandbox, (entry.name + " Sandbox Proof", BellePrettyPrinter(serializableTactic), serializableTactic)::Nil, Nil, Map.empty)

    val archive = (lemmaEntries :+ sandboxEntry).map(new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))(_)).mkString("\n\n")
    checkArchiveEntries(ArchiveParser.parse(archive))
  }}

  it should "prove fallback preserves controller monitor" taggedAs IgnoreInBuildTest in withMathematica { _ =>
    //@note run this test with -DPLDI17_BASE_DIR=/path/to/paper
    val baseDir = System.getProperty("PLDI17_BASE_DIR")
    val entry = ArchiveParser.parser.parseFromFile(s"$baseDir/velocitycar_dist.kyx#Fallback Preserves Controller Monitor").head
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3) shouldBe 'proved
  }

  it should "check all archive entries" taggedAs IgnoreInBuildTest in withMathematica { _ =>
    //@note run this test with -DPLDI17_BASE_DIR=/path/to/paper
    val baseDir = System.getProperty("PLDI17_BASE_DIR")
    val entries = ArchiveParser.parser.parseFromFile(s"$baseDir/velocitycar_dist.kyx")
    checkArchiveEntries(entries)
    //checkArchiveEntries(entries.filter(_.name == "Velocity Car Safety"))
    //checkArchiveEntries(entries.filter(_.name == "Velocity Car Plant Preserves Invariant"))
    //checkArchiveEntries(entries.filter(_.name == "Velocity Car Sandbox Safety from Car Safety"))
  }

  it should "generate a quantitative monitor" taggedAs IgnoreInBuildTest in withMathematica { tool =>
    //@note run this test with -DTEST_BASE_DIR=/path/to/modeldirectory (e.g., keymaerax-webui/src/main/resources/keymaerax-projects/ral)
    val baseDir = System.getProperty("PLDI17_BASE_DIR")
    val entry = ArchiveParser.parseFromFile(s"$baseDir/velocitycar_dist.kyx#Velocity Car Safety").head
    val model = entry.defs.exhaustiveSubst(entry.model.asInstanceOf[Formula])

    val ctrlMonitorStateVars = List(Variable("d"), Variable("v"), Variable("t"))
    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(model, ctrlMonitorStateVars:_*)

    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val monitorTactic = DebuggingTactics.print("Deriving Monitor") & ModelPlex.controllerMonitorByChase(1) & DebuggingTactics.print("Chased") &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) &
      DebuggingTactics.print("Quantifiers instantiated") &
      simplifier(1) & DebuggingTactics.print("Monitor Result")
    val ctrlMonitorResult = proveBy(modelplexInput, monitorTactic)
    val ctrlMonitorFml = ctrlMonitorResult.subgoals.head.succ.head
    ctrlMonitorFml shouldBe "(V()>=0&ep()>=0)&(d>=V()*ep()&(0<=vpost&vpost<=V())&dpost=d&tpost=0|dpost=d&vpost=0&tpost=0)".asFormula

    /* Generate C code for controller monitor */
    val reassociatedCtrlMonitorFml = FormulaTools.reassociate(ctrlMonitorFml)
    proveBy(Equiv(ctrlMonitorFml, reassociatedCtrlMonitorFml), TactixLibrary.prop) shouldBe 'proved
    val ctrlMonitorProg = proveBy(reassociatedCtrlMonitorFml, ModelPlex.chaseToTests(combineTests=false)(1)*2).subgoals.head.succ.head
    val ctrlInputs = CGenerator.getInputs(ctrlMonitorProg)
    val ctrlMonitorCode = (new CGenerator(new CMonitorGenerator()))(ctrlMonitorProg, ctrlMonitorStateVars.toSet, ctrlInputs, "Monitor")
    ctrlMonitorCode._1.trim shouldBe "/**************************\n * Monitor.c\n * Generated by KeYmaera X\n **************************/\n\n#include <math.h>\n#include <stdbool.h>\n\ntypedef struct parameters {\n  long double V;\n  long double ep;\n} parameters;\n\ntypedef struct state {\n  long double d;\n  long double t;\n  long double v;\n} state;\n\ntypedef struct input input;\n\ntypedef struct verdict { int id; long double val; } verdict;\n\nverdict OrLeft1896387834(state pre, state curr, const parameters* const params) {\n  if (pre.d >= (params->V)*(params->ep)) {\nif (0.0L <= curr.v) {\nif (curr.v <= params->V) {\nif (curr.d == pre.d) {\nif (curr.t == 0.0L) {\nverdict result = { .id=1, .val=(1.0L)/(((1.0L)/((pre.d)-((params->V)*(params->ep))))+(((1.0L)/(curr.v))+((1.0L)/((params->V)-(curr.v))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), -((curr.d)-(pre.d))))) }; return result;\n}\n} else {\nverdict result = { .id=-3, .val=((-1.0L))+((params->V)-(curr.v)) }; return result;\n}\n} else {\nverdict result = { .id=-4, .val=((-1.0L))+(curr.v) }; return result;\n}\n} else {\nverdict result = { .id=-5, .val=((-1.0L))+((pre.d)-((params->V)*(params->ep))) }; return result;\n}\n}\n\nverdict OrRight1981114317(state pre, state curr, const parameters* const params) {\n  if (curr.d == pre.d) {\nif (curr.v == 0.0L) {\nif (curr.t == 0.0L) {\nverdict result = { .id=1, .val=0.0L }; return result;\n} else {\nverdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;\n}\n} else {\nverdict result = { .id=-6, .val=((-1.0L))+(-(fmaxl(curr.v, -(curr.v)))) }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), -((curr.d)-(pre.d))))) }; return result;\n}\n}"
    ctrlMonitorCode._2.trim shouldBe "/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */\nverdict boundaryDist(state pre, state curr, const parameters* const params) {\n  if (params->V >= 0.0L) {\nif (params->ep >= 0.0L) {\nverdict leftDist = OrLeft1896387834(pre,curr,params);\nverdict rightDist = OrRight1981114317(pre,curr,params);\nint verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;\nverdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };\nreturn result;\n} else {\nverdict result = { .id=-7, .val=((-1.0L))+(params->ep) }; return result;\n}\n} else {\nverdict result = { .id=-8, .val=((-1.0L))+(params->V) }; return result;\n};\n}\n\n/* Evaluates monitor condition in prior and current state */\nbool monitorSatisfied(state pre, state curr, const parameters* const params) {\n  return boundaryDist(pre,curr,params).val >= 0.0L;\n}\n\n/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */\nstate monitoredCtrl(state curr, const parameters* const params, const input* const in,\n                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const)) {\n  state pre = curr;\n  state post = (*ctrl)(pre,params,in);\n  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);\n  else return post;\n}"
  }

  "Waypoint navigation" should "generate a controller monitor" taggedAs IgnoreInBuildTest in withMathematica { tool =>
    //@note run this test with -DTEST_BASE_DIR=/path/to/modeldirectory (e.g., keymaerax-webui/src/main/resources/keymaerax-projects/ral)
    val baseDir = System.getProperty("TEST_BASE_DIR")
    val entry = ArchiveParser.parseFromFile(s"$baseDir/relative-full.kyx#Robot preserves loop invariant").head
    val model = entry.model.asInstanceOf[Formula]
    val Imply(_, Box(prg, _)) = model

    val stateVars = ("xg" :: "yg" :: "v" :: "a" :: "t" :: "vl" :: "vh" :: "k" :: Nil).map(_.asVariable.asInstanceOf[BaseVariable])
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, stateVars: _*)
    val simplifier = SimplifierV3.simpTac(taxs = SimplifierV3.composeIndex(
      SimplifierV3.groundEqualityIndex, SimplifierV3.defaultTaxs))
    val ctrlTactic = DebuggingTactics.print("Deriving Ctrl Monitor") & ModelPlex.controllerMonitorByChase(1) & DebuggingTactics.print("Chased") &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) &
      DebuggingTactics.print("Quantifiers instantiated") &
      simplifier(1) & DebuggingTactics.print("Ctrl Monitor Result")
    val ctrlResult = proveBy(modelplexInput, ctrlTactic)
    val ctrlMonitorFml = ctrlResult.subgoals.head.succ.head
    ctrlMonitorFml shouldBe "(ygpost>0&abs(kpost)*eps()<=100&((kpost*(eps()*eps())-200*eps())*100 < kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10&kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10 < (kpost*(eps()*eps())+200*eps())*100)&0<=vlpost&vlpost < vhpost&A()*T()<=10*(vhpost-vlpost)&B()*T()<=10*(vhpost-vlpost))&((-B()<=apost&apost<=A())&10*v+apost*T()>=0&(v<=vhpost&10*v+apost*T()<=10*vhpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(abs(xgpost)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(ygpost-10*eps())*10000*100)&(vlpost<=v&10*v+apost*T()>=10*vlpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(abs(xgpost)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(ygpost-10*eps())*10000*100))&(v>=0&0<=T())&vpost=v&tpost=0".asFormula
  }

  "RSSRail" should "generate a controller monitor" taggedAs IgnoreInBuildTest in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/keymaerax-projects/rssrail17/rssrail.kyx")
    val entry = ArchiveParser.parse(io.Source.fromInputStream(in).mkString).
      find(_.name == "RSSRail17/Theorem 2: Train Controller with Brake Pressure Propagation is Safe").head
    val model = entry.expandedModel.asInstanceOf[Formula]
    val Imply(_, Box(prg, _)) = model

    val stateVars = ("acc" :: "d" :: "jpb" :: "m" :: "st" :: "t" :: "v" :: "z" :: Nil).map(_.asVariable.asInstanceOf[BaseVariable])
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, stateVars: _*)
    val simplifier = SimplifierV3.simpTac(taxs = SimplifierV3.composeIndex(
      SimplifierV3.groundEqualityIndex, SimplifierV3.defaultTaxs))
    val ctrlTactic = DebuggingTactics.print("Deriving Ctrl Monitor") & ModelPlex.controllerMonitorByChase(1) & DebuggingTactics.print("Chased") &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) &
      DebuggingTactics.print("Quantifiers instantiated") &
      simplifier(1) & DebuggingTactics.print("Ctrl Monitor Result")
    val ctrlResult = proveBy(modelplexInput, ctrlTactic)
    val ctrlMonitorFml = ctrlResult.subgoals.head.succ.head
    ctrlMonitorFml shouldBe "(dpost>=0&v^2-dpost^2<=2*Fsb()/mt()*(mpost-z))&accpost=acc&jpbpost=jpb&stpost=st&tpost=t&vpost=v&zpost=z|(-Fsb()<=accpost&accpost<=Amax())&(d>=0&m-z>=(v^2-d^2)/(2*Fsb()/mt())+(Amax()/Fsb()+1)*(Amax()/(2*mt())*ep()^2+v*ep())|d<=0&(accpost<=0&v-d>=Fpb()^2/(2*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))&m-z>=v*ep()+(mt()*v^2/(2*Fpb())+Fpb()*v/(2*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))-Fpb()^3/(24*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2))^2))|accpost>=0&v-d>=Fpb()^2/(2*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))&m-z>=v*ep()+accpost/(2*mt())*ep()^2+(mt()*(v+accpost/mt()*ep())^2/(2*Fpb())+Fpb()*(v+accpost/mt()*ep())/(2*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))-Fpb()^3/(24*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2))^2))|accpost<=0&v-d<=Fpb()^2/(2*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))&m-z>=v*ep()+2/3*v*(2*mt()*v/(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))^(1/2)|accpost>=0&v+accpost/mt()*ep()-d<=Fpb()^2/(2*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))&m-z>=v*ep()+accpost/(2*mt())*ep()^2+2/3*(v+accpost/mt()*ep())*(2*mt()*(v+accpost/mt()*ep())/(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))^(1/2)))&(v>=0&0<=ep()&-Fpb()<=accpost)&dpost=d&jpbpost=0&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z|m-z>=(v^2-d^2)/(2*Fsb()/mt())&(v>=0&0<=ep()&-Fpb()<=-Fsb())&accpost=-Fsb()&dpost=d&jpbpost=jpb&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z|m-z < (v^2-d^2)/(2*Fsb()/mt())&(v<=d&(-Fsb()<=accpost&accpost<=0)&(v>=0&0<=ep()&-Fpb()<=accpost)&dpost=d&jpbpost=0&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z|v>d&(acc<=-Fpb()&(v>=0&0<=ep()&-Fpb()<=acc)&accpost=acc&dpost=d&jpbpost=0&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z|acc>-Fpb()&(v>=0&0<=ep()&-Fpb()<=min(acc,0))&accpost=min(acc,0)&dpost=d&jpbpost=-Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z))".asFormula

    /* Generate C code for controller monitor */
    val reassociatedCtrlMonitorFml = FormulaTools.reassociate(ctrlMonitorFml)
    //proveBy(Equiv(ctrlMonitorFml, reassociatedCtrlMonitorFml), TactixLibrary.prop) shouldBe 'proved
    val ctrlMonitorProg = proveBy(reassociatedCtrlMonitorFml, ModelPlex.chaseToTests(combineTests=false)(1)*2).subgoals.head.succ.head
    val ctrlInputs = CGenerator.getInputs(ctrlMonitorProg)
    val ctrlMonitorCode = (new CGenerator(new CMonitorGenerator()))(ctrlMonitorProg, stateVars.toSet, ctrlInputs, "Monitor")
    ctrlMonitorCode._1.trim shouldBe "/**************************\n * Monitor.c\n * Generated by KeYmaera X\n **************************/\n\n#include <math.h>\n#include <stdbool.h>\n\n/** Model parameters */\ntypedef struct parameters {\n  long double Amax;\n  long double Fpb;\n  long double Fsb;\n  long double L;\n  long double cappl1;\n  long double cappl2;\n  long double cappl3;\n  long double ep;\n  long double mt;\n} parameters;\n\n/** State (control choices, environment measurements etc.) */\ntypedef struct state {\n  long double acc;\n  long double d;\n  long double jpb;\n  long double m;\n  long double st;\n  long double t;\n  long double v;\n  long double z;\n} state;\n\n/** Values for resolving non-deterministic assignments in control code */\ntypedef struct input input;\n\n/** Monitor verdict: `id` identifies the violated monitor sub-condition, `val` the safety margin (<0 violated, >=0 satisfied). */\ntypedef struct verdict { int id; long double val; } verdict;\n\nverdict OrLeft614666496(state pre, state curr, const parameters* const params) {\n  if (pre.acc <= -(params->Fpb)) {\nif (pre.v >= 0.0L) {\nif (0.0L <= params->ep) {\nif (-(params->Fpb) <= pre.acc) {\nif (curr.acc == pre.acc) {\nif (curr.d == pre.d) {\nif (curr.jpb == 0.0L) {\nif (curr.m == pre.m) {\nif (curr.st == 0.0L) {\nif (curr.t == 0.0L) {\nif (curr.v == pre.v) {\nif (curr.z == pre.z) {\nverdict result = { .id=1, .val=(1.0L)/(((1.0L)/((-(params->Fpb))-(pre.acc)))+((((1.0L)/(-(-(pre.v))))+((1.0L)/(-(-(params->ep)))))+((1.0L)/((pre.acc)-(-(params->Fpb)))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl((curr.z)-(pre.z), (pre.z)-(curr.z)))) }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.v)-(pre.v), (pre.v)-(curr.v)))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-(fmaxl(curr.st, -(curr.st)))) }; return result;\n}\n} else {\nverdict result = { .id=-11, .val=((-1.0L))+(-(fmaxl((curr.m)-(pre.m), (pre.m)-(curr.m)))) }; return result;\n}\n} else {\nverdict result = { .id=-12, .val=((-1.0L))+(-(fmaxl(curr.jpb, -(curr.jpb)))) }; return result;\n}\n} else {\nverdict result = { .id=-13, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), (pre.d)-(curr.d)))) }; return result;\n}\n} else {\nverdict result = { .id=-6, .val=((-1.0L))+(-(fmaxl((curr.acc)-(pre.acc), (pre.acc)-(curr.acc)))) }; return result;\n}\n} else {\nverdict result = { .id=-25, .val=((-1.0L))+((pre.acc)-(-(params->Fpb))) }; return result;\n}\n} else {\nverdict result = { .id=-15, .val=((-1.0L))+(-(-(params->ep))) }; return result;\n}\n} else {\nverdict result = { .id=-16, .val=((-1.0L))+(-(-(pre.v))) }; return result;\n}\n} else {\nverdict result = { .id=-26, .val=((-1.0L))+((-(params->Fpb))-(pre.acc)) }; return result;\n}\n}\n\nverdict OrRight516276781(state pre, state curr, const parameters* const params) {\n  if (pre.acc > -(params->Fpb)) {\nif (pre.v >= 0.0L) {\nif (0.0L <= params->ep) {\nif (-(params->Fpb) <= fminl(pre.acc, 0.0L)) {\nif (curr.acc == fminl(pre.acc, 0.0L)) {\nif (curr.d == pre.d) {\nif (curr.jpb == -((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))) {\nif (curr.m == pre.m) {\nif (curr.st == 0.0L) {\nif (curr.t == 0.0L) {\nif (curr.v == pre.v) {\nif (curr.z == pre.z) {\nverdict result = { .id=1, .val=(1.0L)/(((1.0L)/((pre.acc)-(-(params->Fpb))))+((((1.0L)/(-(-(pre.v))))+((1.0L)/(-(-(params->ep)))))+((1.0L)/((fminl(pre.acc, 0.0L))-(-(params->Fpb)))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl((curr.z)-(pre.z), (pre.z)-(curr.z)))) }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.v)-(pre.v), (pre.v)-(curr.v)))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-(fmaxl(curr.st, -(curr.st)))) }; return result;\n}\n} else {\nverdict result = { .id=-11, .val=((-1.0L))+(-(fmaxl((curr.m)-(pre.m), (pre.m)-(curr.m)))) }; return result;\n}\n} else {\nverdict result = { .id=-27, .val=((-1.0L))+(-(fmaxl((curr.jpb)-(-((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))), (-((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))-(curr.jpb)))) }; return result;\n}\n} else {\nverdict result = { .id=-13, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), (pre.d)-(curr.d)))) }; return result;\n}\n} else {\nverdict result = { .id=-28, .val=((-1.0L))+(-(fmaxl((curr.acc)-(fminl(pre.acc, 0.0L)), (fminl(pre.acc, 0.0L))-(curr.acc)))) }; return result;\n}\n} else {\nverdict result = { .id=-29, .val=((-1.0L))+((fminl(pre.acc, 0.0L))-(-(params->Fpb))) }; return result;\n}\n} else {\nverdict result = { .id=-15, .val=((-1.0L))+(-(-(params->ep))) }; return result;\n}\n} else {\nverdict result = { .id=-16, .val=((-1.0L))+(-(-(pre.v))) }; return result;\n}\n} else {\nverdict result = { .id=-30, .val=((-1.0L))+((pre.acc)-(-(params->Fpb))) }; return result;\n}\n}\n\n\nverdict OrLeft460872904(state pre, state curr, const parameters* const params) {\n  if (pre.v <= pre.d) {\nif (-(params->Fsb) <= curr.acc) {\nif (curr.acc <= 0.0L) {\nif (pre.v >= 0.0L) {\nif (0.0L <= params->ep) {\nif (-(params->Fpb) <= curr.acc) {\nif (curr.d == pre.d) {\nif (curr.jpb == 0.0L) {\nif (curr.m == pre.m) {\nif (curr.st == 0.0L) {\nif (curr.t == 0.0L) {\nif (curr.v == pre.v) {\nif (curr.z == pre.z) {\nverdict result = { .id=1, .val=(1.0L)/(((1.0L)/((pre.d)-(pre.v)))+((((((1.0L)/((curr.acc)-(-(params->Fsb))))+((1.0L)/(-(-(-(curr.acc))))))+((1.0L)/(-(-(pre.v)))))+((1.0L)/(-(-(params->ep)))))+((1.0L)/((curr.acc)-(-(params->Fpb)))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl((curr.z)-(pre.z), (pre.z)-(curr.z)))) }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.v)-(pre.v), (pre.v)-(curr.v)))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-(fmaxl(curr.st, -(curr.st)))) }; return result;\n}\n} else {\nverdict result = { .id=-11, .val=((-1.0L))+(-(fmaxl((curr.m)-(pre.m), (pre.m)-(curr.m)))) }; return result;\n}\n} else {\nverdict result = { .id=-12, .val=((-1.0L))+(-(fmaxl(curr.jpb, -(curr.jpb)))) }; return result;\n}\n} else {\nverdict result = { .id=-13, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), (pre.d)-(curr.d)))) }; return result;\n}\n} else {\nverdict result = { .id=-14, .val=((-1.0L))+((curr.acc)-(-(params->Fpb))) }; return result;\n}\n} else {\nverdict result = { .id=-15, .val=((-1.0L))+(-(-(params->ep))) }; return result;\n}\n} else {\nverdict result = { .id=-16, .val=((-1.0L))+(-(-(pre.v))) }; return result;\n}\n} else {\nverdict result = { .id=-23, .val=((-1.0L))+(-(-(-(curr.acc)))) }; return result;\n}\n} else {\nverdict result = { .id=-19, .val=((-1.0L))+((curr.acc)-(-(params->Fsb))) }; return result;\n}\n} else {\nverdict result = { .id=-24, .val=((-1.0L))+((pre.d)-(pre.v)) }; return result;\n}\n}\n\nverdict OrRight_2008606857(state pre, state curr, const parameters* const params) {\n  if (pre.v > pre.d) {\nverdict leftDist = OrLeft614666496(pre,curr,params);\nverdict rightDist = OrRight516276781(pre,curr,params);\nint verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;\nverdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };\nreturn result;\n} else {\nverdict result = { .id=-31, .val=((-1.0L))+((pre.v)-(pre.d)) }; return result;\n}\n}\n\n\nverdict OrLeft_27625164(state pre, state curr, const parameters* const params) {\n  if ((pre.m)-(pre.z) >= (((pre.v)*(pre.v))-((pre.d)*(pre.d)))/(((2.0L)*(params->Fsb))/(params->mt))) {\nif (pre.v >= 0.0L) {\nif (0.0L <= params->ep) {\nif (-(params->Fpb) <= -(params->Fsb)) {\nif (curr.acc == -(params->Fsb)) {\nif (curr.d == pre.d) {\nif (curr.jpb == pre.jpb) {\nif (curr.m == pre.m) {\nif (curr.st == 0.0L) {\nif (curr.t == 0.0L) {\nif (curr.v == pre.v) {\nif (curr.z == pre.z) {\nverdict result = { .id=1, .val=(1.0L)/(((1.0L)/(((pre.m)-(pre.z))-((((pre.v)*(pre.v))-((pre.d)*(pre.d)))/(((2.0L)*(params->Fsb))/(params->mt)))))+((((1.0L)/(-(-(pre.v))))+((1.0L)/(-(-(params->ep)))))+((1.0L)/((-(params->Fsb))-(-(params->Fpb)))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl((curr.z)-(pre.z), (pre.z)-(curr.z)))) }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.v)-(pre.v), (pre.v)-(curr.v)))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-(fmaxl(curr.st, -(curr.st)))) }; return result;\n}\n} else {\nverdict result = { .id=-11, .val=((-1.0L))+(-(fmaxl((curr.m)-(pre.m), (pre.m)-(curr.m)))) }; return result;\n}\n} else {\nverdict result = { .id=-5, .val=((-1.0L))+(-(fmaxl((curr.jpb)-(pre.jpb), (pre.jpb)-(curr.jpb)))) }; return result;\n}\n} else {\nverdict result = { .id=-13, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), (pre.d)-(curr.d)))) }; return result;\n}\n} else {\nverdict result = { .id=-20, .val=((-1.0L))+(-(fmaxl((curr.acc)-(-(params->Fsb)), (-(params->Fsb))-(curr.acc)))) }; return result;\n}\n} else {\nverdict result = { .id=-21, .val=((-1.0L))+((-(params->Fsb))-(-(params->Fpb))) }; return result;\n}\n} else {\nverdict result = { .id=-15, .val=((-1.0L))+(-(-(params->ep))) }; return result;\n}\n} else {\nverdict result = { .id=-16, .val=((-1.0L))+(-(-(pre.v))) }; return result;\n}\n} else {\nverdict result = { .id=-22, .val=((-1.0L))+(((pre.m)-(pre.z))-((((pre.v)*(pre.v))-((pre.d)*(pre.d)))/(((2.0L)*(params->Fsb))/(params->mt)))) }; return result;\n}\n}\n\nverdict OrRight_1283792078(state pre, state curr, const parameters* const params) {\n  if ((pre.m)-(pre.z) < (((pre.v)*(pre.v))-((pre.d)*(pre.d)))/(((2.0L)*(params->Fsb))/(params->mt))) {\nverdict leftDist = OrLeft460872904(pre,curr,params);\nverdict rightDist = OrRight_2008606857(pre,curr,params);\nint verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;\nverdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };\nreturn result;\n} else {\nverdict result = { .id=-32, .val=((-1.0L))+(((((pre.v)*(pre.v))-((pre.d)*(pre.d)))/(((2.0L)*(params->Fsb))/(params->mt)))-((pre.m)-(pre.z))) }; return result;\n}\n}\n\nverdict OrLeft955701495(state pre, state curr, const parameters* const params) {\n  if (-(params->Fsb) <= curr.acc) {\nif (curr.acc <= params->Amax) {\nif (((pre.d >= 0.0L) && ((pre.m)-(pre.z) >= ((((pre.v)*(pre.v))-((pre.d)*(pre.d)))/(((2.0L)*(params->Fsb))/(params->mt)))+((((params->Amax)/(params->Fsb))+(1.0L))*((((params->Amax)/((2.0L)*(params->mt)))*((params->ep)*(params->ep)))+((pre.v)*(params->ep)))))) || ((pre.d <= 0.0L) && (((curr.acc <= 0.0L) && (((pre.v)-(pre.d) >= ((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))) && ((pre.m)-(pre.z) >= ((pre.v)*(params->ep))+(((((params->mt)*((pre.v)*(pre.v)))/((2.0L)*(params->Fpb)))+(((params->Fpb)*(pre.v))/((2.0L)*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))-(((params->Fpb)*((params->Fpb)*(params->Fpb)))/(((24.0L)*(params->mt))*(((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))))))))) || (((curr.acc >= 0.0L) && (((pre.v)-(pre.d) >= ((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))) && ((pre.m)-(pre.z) >= (((pre.v)*(params->ep))+(((curr.acc)/((2.0L)*(params->mt)))*((params->ep)*(params->ep))))+(((((params->mt)*(((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))))/((2.0L)*(params->Fpb)))+(((params->Fpb)*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))/((2.0L)*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))-(((params->Fpb)*((params->Fpb)*(params->Fpb)))/(((24.0L)*(params->mt))*(((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))))))))) || (((curr.acc <= 0.0L) && (((pre.v)-(pre.d) <= ((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))) && ((pre.m)-(pre.z) >= ((pre.v)*(params->ep))+((((2.0L)/(3.0L))*(pre.v))*(pow((((2.0L)*(params->mt))*(pre.v))/((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))),(1.0L)/(2.0L))))))) || ((curr.acc >= 0.0L) && ((((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))-(pre.d) <= ((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))) && ((pre.m)-(pre.z) >= (((pre.v)*(params->ep))+(((curr.acc)/((2.0L)*(params->mt)))*((params->ep)*(params->ep))))+((((2.0L)/(3.0L))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))*(pow((((2.0L)*(params->mt))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))/((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))),(1.0L)/(2.0L)))))))))))) {\nif (pre.v >= 0.0L) {\nif (0.0L <= params->ep) {\nif (-(params->Fpb) <= curr.acc) {\nif (curr.d == pre.d) {\nif (curr.jpb == 0.0L) {\nif (curr.m == pre.m) {\nif (curr.st == 0.0L) {\nif (curr.t == 0.0L) {\nif (curr.v == pre.v) {\nif (curr.z == pre.z) {\nverdict result = { .id=1, .val=(1.0L)/(((1.0L)/((curr.acc)-(-(params->Fsb))))+((((((1.0L)/((params->Amax)-(curr.acc)))+((1.0L)/(-(fminl(fmaxl(-(pre.d), (((((pre.v)*(pre.v))-((pre.d)*(pre.d)))/(((2.0L)*(params->Fsb))/(params->mt)))+((((params->Amax)/(params->Fsb))+(1.0L))*((((params->Amax)/((2.0L)*(params->mt)))*((params->ep)*(params->ep)))+((pre.v)*(params->ep)))))-((pre.m)-(pre.z))), fmaxl(-(-(pre.d)), fminl(fmaxl(-(-(curr.acc)), fmaxl((((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))))-((pre.v)-(pre.d)), (((pre.v)*(params->ep))+(((((params->mt)*((pre.v)*(pre.v)))/((2.0L)*(params->Fpb)))+(((params->Fpb)*(pre.v))/((2.0L)*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))-(((params->Fpb)*((params->Fpb)*(params->Fpb)))/(((24.0L)*(params->mt))*(((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))))-((pre.m)-(pre.z)))), fminl(fmaxl(-(curr.acc), fmaxl((((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))))-((pre.v)-(pre.d)), ((((pre.v)*(params->ep))+(((curr.acc)/((2.0L)*(params->mt)))*((params->ep)*(params->ep))))+(((((params->mt)*(((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))))/((2.0L)*(params->Fpb)))+(((params->Fpb)*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))/((2.0L)*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))-(((params->Fpb)*((params->Fpb)*(params->Fpb)))/(((24.0L)*(params->mt))*(((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))))-((pre.m)-(pre.z)))), fminl(fmaxl(-(-(curr.acc)), fmaxl(((pre.v)-(pre.d))-(((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))), (((pre.v)*(params->ep))+((((2.0L)/(3.0L))*(pre.v))*(pow((((2.0L)*(params->mt))*(pre.v))/((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))),(1.0L)/(2.0L)))))-((pre.m)-(pre.z)))), fmaxl(-(curr.acc), fmaxl((((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))-(pre.d))-(((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))), ((((pre.v)*(params->ep))+(((curr.acc)/((2.0L)*(params->mt)))*((params->ep)*(params->ep))))+((((2.0L)/(3.0L))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))*(pow((((2.0L)*(params->mt))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))/((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))),(1.0L)/(2.0L)))))-((pre.m)-(pre.z)))))))))))))+((1.0L)/(-(-(pre.v)))))+((1.0L)/(-(-(params->ep)))))+((1.0L)/((curr.acc)-(-(params->Fpb)))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl((curr.z)-(pre.z), (pre.z)-(curr.z)))) }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.v)-(pre.v), (pre.v)-(curr.v)))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-(fmaxl(curr.st, -(curr.st)))) }; return result;\n}\n} else {\nverdict result = { .id=-11, .val=((-1.0L))+(-(fmaxl((curr.m)-(pre.m), (pre.m)-(curr.m)))) }; return result;\n}\n} else {\nverdict result = { .id=-12, .val=((-1.0L))+(-(fmaxl(curr.jpb, -(curr.jpb)))) }; return result;\n}\n} else {\nverdict result = { .id=-13, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), (pre.d)-(curr.d)))) }; return result;\n}\n} else {\nverdict result = { .id=-14, .val=((-1.0L))+((curr.acc)-(-(params->Fpb))) }; return result;\n}\n} else {\nverdict result = { .id=-15, .val=((-1.0L))+(-(-(params->ep))) }; return result;\n}\n} else {\nverdict result = { .id=-16, .val=((-1.0L))+(-(-(pre.v))) }; return result;\n}\n} else {\nverdict result = { .id=-17, .val=((-1.0L))+(-(fminl(fmaxl(-(pre.d), (((((pre.v)*(pre.v))-((pre.d)*(pre.d)))/(((2.0L)*(params->Fsb))/(params->mt)))+((((params->Amax)/(params->Fsb))+(1.0L))*((((params->Amax)/((2.0L)*(params->mt)))*((params->ep)*(params->ep)))+((pre.v)*(params->ep)))))-((pre.m)-(pre.z))), fmaxl(-(-(pre.d)), fminl(fmaxl(-(-(curr.acc)), fmaxl((((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))))-((pre.v)-(pre.d)), (((pre.v)*(params->ep))+(((((params->mt)*((pre.v)*(pre.v)))/((2.0L)*(params->Fpb)))+(((params->Fpb)*(pre.v))/((2.0L)*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))-(((params->Fpb)*((params->Fpb)*(params->Fpb)))/(((24.0L)*(params->mt))*(((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))))-((pre.m)-(pre.z)))), fminl(fmaxl(-(curr.acc), fmaxl((((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))))-((pre.v)-(pre.d)), ((((pre.v)*(params->ep))+(((curr.acc)/((2.0L)*(params->mt)))*((params->ep)*(params->ep))))+(((((params->mt)*(((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))))/((2.0L)*(params->Fpb)))+(((params->Fpb)*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))/((2.0L)*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))-(((params->Fpb)*((params->Fpb)*(params->Fpb)))/(((24.0L)*(params->mt))*(((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L)))))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))))))-((pre.m)-(pre.z)))), fminl(fmaxl(-(-(curr.acc)), fmaxl(((pre.v)-(pre.d))-(((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))), (((pre.v)*(params->ep))+((((2.0L)/(3.0L))*(pre.v))*(pow((((2.0L)*(params->mt))*(pre.v))/((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))),(1.0L)/(2.0L)))))-((pre.m)-(pre.z)))), fmaxl(-(curr.acc), fmaxl((((pre.v)+(((curr.acc)/(params->mt))*(params->ep)))-(pre.d))-(((params->Fpb)*(params->Fpb))/(((2.0L)*(params->mt))*((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))))), ((((pre.v)*(params->ep))+(((curr.acc)/((2.0L)*(params->mt)))*((params->ep)*(params->ep))))+((((2.0L)/(3.0L))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))*(pow((((2.0L)*(params->mt))*((pre.v)+(((curr.acc)/(params->mt))*(params->ep))))/((params->Fpb)/(((params->cappl1)+((params->cappl2)*(params->L)))-((params->cappl3)*((params->L)*(params->L))))),(1.0L)/(2.0L)))))-((pre.m)-(pre.z))))))))))) }; return result;\n}\n} else {\nverdict result = { .id=-18, .val=((-1.0L))+((params->Amax)-(curr.acc)) }; return result;\n}\n} else {\nverdict result = { .id=-19, .val=((-1.0L))+((curr.acc)-(-(params->Fsb))) }; return result;\n}\n}\n\nverdict OrRight700689157(state pre, state curr, const parameters* const params) {\n  verdict leftDist = OrLeft_27625164(pre,curr,params);\nverdict rightDist = OrRight_1283792078(pre,curr,params);\nint verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;\nverdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };\nreturn result;\n}\n\nverdict OrLeft_655767488(state pre, state curr, const parameters* const params) {\n  if (curr.d >= 0.0L) {\nif (((pre.v)*(pre.v))-((curr.d)*(curr.d)) <= (((2.0L)*(params->Fsb))/(params->mt))*((curr.m)-(pre.z))) {\nif (curr.acc == pre.acc) {\nif (curr.jpb == pre.jpb) {\nif (curr.st == pre.st) {\nif (curr.t == pre.t) {\nif (curr.v == pre.v) {\nif (curr.z == pre.z) {\nverdict result = { .id=1, .val=(1.0L)/(((1.0L)/(-(-(curr.d))))+((1.0L)/(((((2.0L)*(params->Fsb))/(params->mt))*((curr.m)-(pre.z)))-(((pre.v)*(pre.v))-((curr.d)*(curr.d)))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl((curr.z)-(pre.z), (pre.z)-(curr.z)))) }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.v)-(pre.v), (pre.v)-(curr.v)))) }; return result;\n}\n} else {\nverdict result = { .id=-3, .val=((-1.0L))+(-(fmaxl((curr.t)-(pre.t), (pre.t)-(curr.t)))) }; return result;\n}\n} else {\nverdict result = { .id=-4, .val=((-1.0L))+(-(fmaxl((curr.st)-(pre.st), (pre.st)-(curr.st)))) }; return result;\n}\n} else {\nverdict result = { .id=-5, .val=((-1.0L))+(-(fmaxl((curr.jpb)-(pre.jpb), (pre.jpb)-(curr.jpb)))) }; return result;\n}\n} else {\nverdict result = { .id=-6, .val=((-1.0L))+(-(fmaxl((curr.acc)-(pre.acc), (pre.acc)-(curr.acc)))) }; return result;\n}\n} else {\nverdict result = { .id=-7, .val=((-1.0L))+(((((2.0L)*(params->Fsb))/(params->mt))*((curr.m)-(pre.z)))-(((pre.v)*(pre.v))-((curr.d)*(curr.d)))) }; return result;\n}\n} else {\nverdict result = { .id=-8, .val=((-1.0L))+(-(-(curr.d))) }; return result;\n}\n}\n\nverdict OrRight1544619243(state pre, state curr, const parameters* const params) {\n  verdict leftDist = OrLeft955701495(pre,curr,params);\nverdict rightDist = OrRight700689157(pre,curr,params);\nint verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;\nverdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };\nreturn result;\n}"
    ctrlMonitorCode._2.trim shouldBe "/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */\nverdict boundaryDist(state pre, state curr, const parameters* const params) {\n  verdict leftDist = OrLeft_655767488(pre,curr,params);\nverdict rightDist = OrRight1544619243(pre,curr,params);\nint verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;\nverdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };\nreturn result;;\n}\n\n/* Evaluates monitor condition in prior and current state */\nbool monitorSatisfied(state pre, state curr, const parameters* const params) {\n  return boundaryDist(pre,curr,params).val >= 0.0L;\n}\n\n/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */\nstate monitoredCtrl(state curr, const parameters* const params, const input* const in,\n                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const)) {\n  state pre = curr;\n  state post = (*ctrl)(pre,params,in);\n  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);\n  else return post;\n}"
  }

  it should "generate monitors from plant overapproximation" taggedAs IgnoreInBuildTest in withMathematica { tool =>
    //@note run this test with -DTEST_BASE_DIR=/path/to/modeldirectory (e.g., keymaerax-webui/src/main/resources/keymaerax-projects/ral)
    val baseDir = System.getProperty("TEST_BASE_DIR")
    val entry = ArchiveParser.parseFromFile(s"$baseDir/relative-full.kyx#Robot preserves loop invariant").head
    val model = entry.model.asInstanceOf[Formula]
    val Imply(_, Box(Loop(Compose(prg, _)), _)) = model

    val diffCuts = "(t>=0&(k*(eps()*eps())-2*100*eps())*(10*10) < k*(xg*xg+yg*yg)-2*xg*100*10&k*(xg*xg+yg*yg)-2*xg*100*10 < (k*(eps()*eps())+2*100*eps())*(10*10)|10*v+a*(T()-t)>=0&((a>=0&10*v+a*(T()-t)<=10*vh|a<=0&v<=vh)|(1*100*(1*100)+2*eps()*abs(k)*1*100+eps()*eps()*(k*k))*(B()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+((v*10+a*(T()-t))*(v*10+a*(T()-t))-10*vh*(10*vh)))<=2*B()*(yg-10*eps())*(100*100)*(10*10)|(1*100*(1*100)+2*eps()*abs(k)*1*100+eps()*eps()*(k*k))*(B()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+((v*10+a*(T()-t))*(v*10+a*(T()-t))-10*vh*(10*vh)))<=2*B()*(abs(xg)-10*eps())*(100*100)*(10*10))&((a>=0&v>=vl|a<=0&10*v+a*(T()-t)>=10*vl)|(1*100*(1*100)+2*eps()*abs(k)*1*100+eps()*eps()*(k*k))*(A()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+(vl*10*(vl*10)-(v*10+a*(T()-t))*(v*10+a*(T()-t))))<=2*A()*(yg-10*eps())*(100*100)*(10*10)|(1*100*(1*100)+2*eps()*abs(k)*1*100+eps()*eps()*(k*k))*(A()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+(vl*10*(vl*10)-(v*10+a*(T()-t))*(v*10+a*(T()-t))))<=2*A()*(abs(xg)-10*eps())*(100*100)*(10*10)))".asFormula
    val expectedEvolutionDomain = And("v>=0&t<=T()".asFormula, diffCuts)

    val nonlinearModelApprox = ModelPlex.createNonlinearModelApprox("Waypoint", entry.tactics.head._3)(model)
    val Imply(init, Box(Loop(Compose(
      ctrl,
      plant@Compose(x0Ghosts, Compose(Test(x0EvolDomain), Compose(nondetPlant, Test(evolDomain)))))), safe)) = nonlinearModelApprox._1
    ctrl shouldBe prg
    x0Ghosts shouldBe "t_0:=t;v_0:=v;xg_0:=xg;yg_0:=yg;".asProgram
    x0EvolDomain shouldBe expectedEvolutionDomain
    nondetPlant shouldBe "t:=*;v:=*;xg:=*;yg:=*;".asProgram
    evolDomain shouldBe expectedEvolutionDomain

    val modelMonitorStateVars = ("xg" :: "yg" :: "v" :: "a" :: "t" :: "vl" :: "vh" :: "k" :: "t_0" :: "v_0" :: "xg_0" :: "yg_0" :: Nil).map(_.asVariable.asInstanceOf[BaseVariable])
    val (modelMonitorInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(nonlinearModelApprox._1, modelMonitorStateVars: _*)
    val simplifier = SimplifierV3.simpTac(taxs = SimplifierV3.composeIndex(
      SimplifierV3.groundEqualityIndex, SimplifierV3.defaultTaxs))
    val monitorTactic = DebuggingTactics.print("Deriving Monitor") & ModelPlex.controllerMonitorByChase(1) & DebuggingTactics.print("Chased") &
      SaturateTactic(ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)) &
      DebuggingTactics.print("Quantifiers instantiated") &
      simplifier(1) & DebuggingTactics.print("Monitor Result")

    /* Derive a model monitor (monitor controller + plant, use after plant/before controller) */
    val modelMonitorResult = proveBy(modelMonitorInput, monitorTactic)
    val modelMonitorFml = modelMonitorResult.subgoals.head.succ.head
    modelMonitorFml shouldBe "(ygpost_0>0&abs(kpost)*eps()<=100&((kpost*(eps()*eps())-200*eps())*100 < kpost*(xgpost_0*xgpost_0+ygpost_0*ygpost_0)-2*xgpost_0*100*10&kpost*(xgpost_0*xgpost_0+ygpost_0*ygpost_0)-2*xgpost_0*100*10 < (kpost*(eps()*eps())+200*eps())*100)&0<=vlpost&vlpost < vhpost&A()*T()<=10*(vhpost-vlpost)&B()*T()<=10*(vhpost-vlpost))&((-B()<=apost&apost<=A())&10*v+apost*T()>=0&(v<=vhpost&10*v+apost*T()<=10*vhpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(abs(xgpost_0)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(ygpost_0-10*eps())*10000*100)&(vlpost<=v&10*v+apost*T()>=10*vlpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(abs(xgpost_0)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(ygpost_0-10*eps())*10000*100))&(v>=0&0<=T())&((vpost>=0&tpost<=T())&(tpost>=0&(kpost*(eps()*eps())-200*eps())*100 < kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10&kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10 < (kpost*(eps()*eps())+200*eps())*100|10*vpost+apost*(T()-tpost)>=0&((apost>=0&10*vpost+apost*(T()-tpost)<=10*vhpost|apost<=0&vpost<=vhpost)|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*vpost*(T()-tpost)*10+apost*((T()-tpost)*(T()-tpost)))+((vpost*10+apost*(T()-tpost))*(vpost*10+apost*(T()-tpost))-10*vhpost*(10*vhpost)))<=2*B()*(ygpost-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*vpost*(T()-tpost)*10+apost*((T()-tpost)*(T()-tpost)))+((vpost*10+apost*(T()-tpost))*(vpost*10+apost*(T()-tpost))-10*vhpost*(10*vhpost)))<=2*B()*(abs(xgpost)-10*eps())*10000*100)&((apost>=0&vpost>=vlpost|apost<=0&10*vpost+apost*(T()-tpost)>=10*vlpost)|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*vpost*(T()-tpost)*10+apost*((T()-tpost)*(T()-tpost)))+(vlpost*10*(vlpost*10)-(vpost*10+apost*(T()-tpost))*(vpost*10+apost*(T()-tpost))))<=2*A()*(ygpost-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*vpost*(T()-tpost)*10+apost*((T()-tpost)*(T()-tpost)))+(vlpost*10*(vlpost*10)-(vpost*10+apost*(T()-tpost))*(vpost*10+apost*(T()-tpost))))<=2*A()*(abs(xgpost)-10*eps())*10000*100)))&tpost_0=0&vpost_0=v".asFormula

    /* Derive a controller monitor (monitor only controller, use right after control decision) */
    val ctrlMonitorStateVars = ("xg" :: "yg" :: "v" :: "a" :: "t" :: "vl" :: "vh" :: "k" :: Nil).map(_.asVariable.asInstanceOf[BaseVariable])
    val (ctrlMonitorInput, _) = ModelPlex.createMonitorSpecificationConjecture(Imply(init, Box(Loop(ctrl), safe)), ctrlMonitorStateVars: _*)
    val ctrlMonitorResult = proveBy(ctrlMonitorInput, monitorTactic)
    val ctrlMonitorFml = ctrlMonitorResult.subgoals.head.succ.head
    ctrlMonitorFml shouldBe "(ygpost>0&abs(kpost)*eps()<=100&((kpost*(eps()*eps())-200*eps())*100 < kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10&kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10 < (kpost*(eps()*eps())+200*eps())*100)&0<=vlpost&vlpost < vhpost&A()*T()<=10*(vhpost-vlpost)&B()*T()<=10*(vhpost-vlpost))&((-B()<=apost&apost<=A())&10*v+apost*T()>=0&(v<=vhpost&10*v+apost*T()<=10*vhpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(abs(xgpost)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(ygpost-10*eps())*10000*100)&(vlpost<=v&10*v+apost*T()>=10*vlpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(abs(xgpost)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(ygpost-10*eps())*10000*100))&vpost=v&tpost=0".asFormula

    /* Derive a plant monitor (monitor only physics, use right after plant/before controller) */
    val plantMonitorStateVars = ("xg" :: "yg" :: "v" :: "t" :: "t_0" :: "v_0" :: "xg_0" :: "yg_0" :: Nil).map(_.asVariable.asInstanceOf[BaseVariable])
    val (plantMonitorInput, _) = ModelPlex.createMonitorSpecificationConjecture(Imply(init, Box(Loop(plant), safe)), plantMonitorStateVars: _*)
    val plantMonitorResult = proveBy(plantMonitorInput, monitorTactic)
    val plantMonitorFml = plantMonitorResult.subgoals.head.succ.head
    plantMonitorFml shouldBe "((v>=0&t<=T())&(t>=0&(k*(eps()*eps())-200*eps())*100 < k*(xg*xg+yg*yg)-2*xg*100*10&k*(xg*xg+yg*yg)-2*xg*100*10 < (k*(eps()*eps())+200*eps())*100|10*v+a*(T()-t)>=0&((a>=0&10*v+a*(T()-t)<=10*vh|a<=0&v<=vh)|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(B()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+((v*10+a*(T()-t))*(v*10+a*(T()-t))-10*vh*(10*vh)))<=2*B()*(yg-10*eps())*10000*100|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(B()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+((v*10+a*(T()-t))*(v*10+a*(T()-t))-10*vh*(10*vh)))<=2*B()*(abs(xg)-10*eps())*10000*100)&((a>=0&v>=vl|a<=0&10*v+a*(T()-t)>=10*vl)|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(A()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+(vl*10*(vl*10)-(v*10+a*(T()-t))*(v*10+a*(T()-t))))<=2*A()*(yg-10*eps())*10000*100|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(A()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+(vl*10*(vl*10)-(v*10+a*(T()-t))*(v*10+a*(T()-t))))<=2*A()*(abs(xg)-10*eps())*10000*100)))&((vpost>=0&tpost<=T())&(tpost>=0&(k*(eps()*eps())-200*eps())*100 < k*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10&k*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10 < (k*(eps()*eps())+200*eps())*100|10*vpost+a*(T()-tpost)>=0&((a>=0&10*vpost+a*(T()-tpost)<=10*vh|a<=0&vpost<=vh)|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(B()*(2*vpost*(T()-tpost)*10+a*((T()-tpost)*(T()-tpost)))+((vpost*10+a*(T()-tpost))*(vpost*10+a*(T()-tpost))-10*vh*(10*vh)))<=2*B()*(ygpost-10*eps())*10000*100|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(B()*(2*vpost*(T()-tpost)*10+a*((T()-tpost)*(T()-tpost)))+((vpost*10+a*(T()-tpost))*(vpost*10+a*(T()-tpost))-10*vh*(10*vh)))<=2*B()*(abs(xgpost)-10*eps())*10000*100)&((a>=0&vpost>=vl|a<=0&10*vpost+a*(T()-tpost)>=10*vl)|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(A()*(2*vpost*(T()-tpost)*10+a*((T()-tpost)*(T()-tpost)))+(vl*10*(vl*10)-(vpost*10+a*(T()-tpost))*(vpost*10+a*(T()-tpost))))<=2*A()*(ygpost-10*eps())*10000*100|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(A()*(2*vpost*(T()-tpost)*10+a*((T()-tpost)*(T()-tpost)))+(vl*10*(vl*10)-(vpost*10+a*(T()-tpost))*(vpost*10+a*(T()-tpost))))<=2*A()*(abs(xgpost)-10*eps())*10000*100)))&tpost_0=t&vpost_0=v&xgpost_0=xg&ygpost_0=yg".asFormula

    /* Generate C code for controller monitor */
    val reassociatedCtrlMonitorFml = FormulaTools.reassociate(ctrlMonitorFml)
    proveBy(Equiv(ctrlMonitorFml, reassociatedCtrlMonitorFml), TactixLibrary.prop) shouldBe 'proved
    val ctrlMonitorProg = proveBy(reassociatedCtrlMonitorFml, ModelPlex.chaseToTests(combineTests=false)(1)*2).subgoals.head.succ.head
    val ctrlInputs = CGenerator.getInputs(ctrlMonitorProg)
    val ctrlMonitorCode = (new CGenerator(new CMonitorGenerator()))(ctrlMonitorProg, ctrlMonitorStateVars.toSet, ctrlInputs, "Monitor")
    //@todo update expected code
    ctrlMonitorCode._1.trim shouldBe "/**************************\n * Monitor.c\n * Generated by KeYmaera X\n **************************/\n\n#include <math.h>\n#include <stdbool.h>\n\ntypedef struct parameters {\n  long double A;\n  long double B;\n  long double T;\n  long double eps;\n} parameters;\n\ntypedef struct state {\n  long double a;\n  long double k;\n  long double t;\n  long double v;\n  long double vh;\n  long double vl;\n  long double xg;\n  long double yg;\n} state;\n\ntypedef struct input input;\n\ntypedef struct verdict { int id; long double val; } verdict;"
    ctrlMonitorCode._2.trim shouldBe "/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */\nverdict boundaryDist(state pre, state curr, const parameters* const params) {\n  if (curr.yg > 0.0L) {\nif ((fabsl(curr.k))*(params->eps) <= 100.0L) {\nif ((((curr.k)*((params->eps)*(params->eps)))-((200.0L)*(params->eps)))*(100.0L) < ((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))) {\nif (((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)) < (((curr.k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)) {\nif (0.0L <= curr.vl) {\nif (curr.vl < curr.vh) {\nif ((params->A)*(params->T) <= (10.0L)*((curr.vh)-(curr.vl))) {\nif ((params->B)*(params->T) <= (10.0L)*((curr.vh)-(curr.vl))) {\nif (-(params->B) <= curr.a) {\nif (curr.a <= params->A) {\nif (((10.0L)*(pre.v))+((curr.a)*(params->T)) >= 0.0L) {\nif (((pre.v <= curr.vh) && (((10.0L)*(pre.v))+((curr.a)*(params->T)) <= (10.0L)*(curr.vh))) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh))))) <= ((((2.0L)*(params->B))*((fabsl(curr.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh))))) <= ((((2.0L)*(params->B))*((curr.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)))) {\nif (((curr.vl <= pre.v) && (((10.0L)*(pre.v))+((curr.a)*(params->T)) >= (10.0L)*(curr.vl))) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T)))))) <= ((((2.0L)*(params->A))*((fabsl(curr.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T)))))) <= ((((2.0L)*(params->A))*((curr.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)))) {\nif (curr.v == pre.v) {\nif (curr.t == 0.0L) {\nverdict result = { .id=1, .val=(((((((((((((0.0L)+(-((0.0L)-(curr.yg))))+(-(((fabsl(curr.k))*(params->eps))-(100.0L))))+(-(((((curr.k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)))))))+(-((((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))))-((((curr.k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))))+(-((0.0L)-(curr.vl))))+(-((curr.vl)-(curr.vh))))+(-(((params->A)*(params->T))-((10.0L)*((curr.vh)+(-(curr.vl)))))))+(-(((params->B)*(params->T))-((10.0L)*((curr.vh)+(-(curr.vl)))))))+(-((-(params->B))-(curr.a))))+(-((curr.a)-(params->A))))+(-((0.0L)-(((10.0L)*(pre.v))+((curr.a)*(params->T))))))+(-(fminl(fmaxl((pre.v)-(curr.vh), (((10.0L)*(pre.v))+((curr.a)*(params->T)))-((10.0L)*(curr.vh))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))+(-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh)))))))-(((((2.0L)*(params->B))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))+(-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh)))))))-(((((2.0L)*(params->B))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))+(-(fminl(fmaxl((curr.vl)-(pre.v), ((10.0L)*(curr.vl))-(((10.0L)*(pre.v))+((curr.a)*(params->T)))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))))))-(((((2.0L)*(params->A))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))))))-(((((2.0L)*(params->A))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-3, .val=((-1.0L))+(-(fminl(fmaxl((curr.vl)-(pre.v), ((10.0L)*(curr.vl))-(((10.0L)*(pre.v))+((curr.a)*(params->T)))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))))))-(((((2.0L)*(params->A))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))))))-(((((2.0L)*(params->A))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))) }; return result;\n}\n} else {\nverdict result = { .id=-4, .val=((-1.0L))+(-(fminl(fmaxl((pre.v)-(curr.vh), (((10.0L)*(pre.v))+((curr.a)*(params->T)))-((10.0L)*(curr.vh))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))+(-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh)))))))-(((((2.0L)*(params->B))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))+(-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh)))))))-(((((2.0L)*(params->B))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))) }; return result;\n}\n} else {\nverdict result = { .id=-5, .val=((-1.0L))+(-((0.0L)-(((10.0L)*(pre.v))+((curr.a)*(params->T))))) }; return result;\n}\n} else {\nverdict result = { .id=-6, .val=((-1.0L))+(-((curr.a)-(params->A))) }; return result;\n}\n} else {\nverdict result = { .id=-7, .val=((-1.0L))+(-((-(params->B))-(curr.a))) }; return result;\n}\n} else {\nverdict result = { .id=-8, .val=((-1.0L))+(-(((params->B)*(params->T))-((10.0L)*((curr.vh)+(-(curr.vl)))))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-(((params->A)*(params->T))-((10.0L)*((curr.vh)+(-(curr.vl)))))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-((curr.vl)-(curr.vh))) }; return result;\n}\n} else {\nverdict result = { .id=-11, .val=((-1.0L))+(-((0.0L)-(curr.vl))) }; return result;\n}\n} else {\nverdict result = { .id=-12, .val=((-1.0L))+(-((((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))))-((((curr.k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))) }; return result;\n}\n} else {\nverdict result = { .id=-13, .val=((-1.0L))+(-(((((curr.k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)))))) }; return result;\n}\n} else {\nverdict result = { .id=-14, .val=((-1.0L))+(-(((fabsl(curr.k))*(params->eps))-(100.0L))) }; return result;\n}\n} else {\nverdict result = { .id=-15, .val=((-1.0L))+(-((0.0L)-(curr.yg))) }; return result;\n};\n}\n\n/* Evaluates monitor condition in prior and current state */\nbool monitorSatisfied(state pre, state curr, const parameters* const params) {\n  return boundaryDist(pre,curr,params).val >= 0.0L;\n}\n\n/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */\nstate monitoredCtrl(state curr, const parameters* const params, const input* const in,\n                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const)) {\n  state pre = curr;\n  state post = (*ctrl)(pre,params,in);\n  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);\n  else return post;\n}"

    /* Generate C code for plant monitor */
    val reassociatedPlantMonitorFml = FormulaTools.reassociate(plantMonitorFml)
    proveBy(Equiv(plantMonitorFml, reassociatedPlantMonitorFml), TactixLibrary.prop) shouldBe 'proved
    val plantMonitorProg = proveBy(reassociatedPlantMonitorFml, ModelPlex.chaseToTests(combineTests=false)(1)*2).subgoals.head.succ.head
    val plantInputs = CGenerator.getInputs(plantMonitorProg)
    val plantMonitorCode = (new CGenerator(new CMonitorGenerator()))(plantMonitorProg, plantMonitorStateVars.toSet, plantInputs, "Monitor")
    //@todo update expected code
    plantMonitorCode._1.trim shouldBe "/**************************\n * Monitor.c\n * Generated by KeYmaera X\n **************************/\n\n#include <math.h>\n#include <stdbool.h>\n\ntypedef struct parameters {\n  long double A;\n  long double B;\n  long double T;\n  long double a;\n  long double eps;\n  long double k;\n  long double vh;\n  long double vl;\n} parameters;\n\ntypedef struct state {\n  long double t;\n  long double t_0;\n  long double v;\n  long double v_0;\n  long double xg;\n  long double xg_0;\n  long double yg;\n  long double yg_0;\n} state;\n\ntypedef struct input input;\n\ntypedef struct verdict { int id; long double val; } verdict;"
    plantMonitorCode._2.trim shouldBe "/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */\nverdict boundaryDist(state pre, state curr, const parameters* const params) {\n  if (pre.v >= 0.0L) {\nif (pre.t <= params->T) {\nif (((pre.t >= 0.0L) && (((((params->k)*((params->eps)*(params->eps)))-((200.0L)*(params->eps)))*(100.0L) < ((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))-((((2.0L)*(pre.xg))*(100.0L))*(10.0L))) && (((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))-((((2.0L)*(pre.xg))*(100.0L))*(10.0L)) < (((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))) || ((((10.0L)*(pre.v))+((params->a)*((params->T)-(pre.t))) >= 0.0L) && ((((params->a >= 0.0L) && (((10.0L)*(pre.v))+((params->a)*((params->T)-(pre.t))) <= (10.0L)*(params->vh))) || (((params->a <= 0.0L) && (pre.v <= params->vh)) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)-(pre.t)))*(10.0L))+((params->a)*(((params->T)-(pre.t))*((params->T)-(pre.t))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))*(((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t)))))-(((10.0L)*(params->vh))*((10.0L)*(params->vh))))) <= ((((2.0L)*(params->B))*((pre.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)-(pre.t)))*(10.0L))+((params->a)*(((params->T)-(pre.t))*((params->T)-(pre.t))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))*(((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t)))))-(((10.0L)*(params->vh))*((10.0L)*(params->vh))))) <= ((((2.0L)*(params->B))*((fabsl(pre.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L))))) && (((params->a >= 0.0L) && (pre.v >= params->vl)) || (((params->a <= 0.0L) && (((10.0L)*(pre.v))+((params->a)*((params->T)-(pre.t))) >= (10.0L)*(params->vl))) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)-(pre.t)))*(10.0L))+((params->a)*(((params->T)-(pre.t))*((params->T)-(pre.t))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))-((((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))*(((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))))) <= ((((2.0L)*(params->A))*((pre.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)-(pre.t)))*(10.0L))+((params->a)*(((params->T)-(pre.t))*((params->T)-(pre.t))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))-((((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))*(((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))))) <= ((((2.0L)*(params->A))*((fabsl(pre.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)))))))) {\nif (curr.v >= 0.0L) {\nif (curr.t <= params->T) {\nif (((curr.t >= 0.0L) && (((((params->k)*((params->eps)*(params->eps)))-((200.0L)*(params->eps)))*(100.0L) < ((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))) && (((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)) < (((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))) || ((((10.0L)*(curr.v))+((params->a)*((params->T)-(curr.t))) >= 0.0L) && ((((params->a >= 0.0L) && (((10.0L)*(curr.v))+((params->a)*((params->T)-(curr.t))) <= (10.0L)*(params->vh))) || (((params->a <= 0.0L) && (curr.v <= params->vh)) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)-(curr.t)))*(10.0L))+((params->a)*(((params->T)-(curr.t))*((params->T)-(curr.t))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))*(((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t)))))-(((10.0L)*(params->vh))*((10.0L)*(params->vh))))) <= ((((2.0L)*(params->B))*((curr.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)-(curr.t)))*(10.0L))+((params->a)*(((params->T)-(curr.t))*((params->T)-(curr.t))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))*(((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t)))))-(((10.0L)*(params->vh))*((10.0L)*(params->vh))))) <= ((((2.0L)*(params->B))*((fabsl(curr.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L))))) && (((params->a >= 0.0L) && (curr.v >= params->vl)) || (((params->a <= 0.0L) && (((10.0L)*(curr.v))+((params->a)*((params->T)-(curr.t))) >= (10.0L)*(params->vl))) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)-(curr.t)))*(10.0L))+((params->a)*(((params->T)-(curr.t))*((params->T)-(curr.t))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))-((((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))*(((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))))) <= ((((2.0L)*(params->A))*((curr.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)-(curr.t)))*(10.0L))+((params->a)*(((params->T)-(curr.t))*((params->T)-(curr.t))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))-((((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))*(((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))))) <= ((((2.0L)*(params->A))*((fabsl(curr.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)))))))) {\nif (curr.t_0 == pre.t) {\nif (curr.v_0 == pre.v) {\nif (curr.xg_0 == pre.xg) {\nif (curr.yg_0 == pre.yg) {\nverdict result = { .id=1, .val=((((((0.0L)+(-((0.0L)-(pre.v))))+(-((pre.t)-(params->T))))+(-(fminl(fmaxl((0.0L)-(pre.t), fmaxl(((((params->k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))+(-((((2.0L)*(pre.xg))*(100.0L))*(10.0L)))), (((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))+(-((((2.0L)*(pre.xg))*(100.0L))*(10.0L))))-((((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))), fmaxl((0.0L)-(((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t))))), fmaxl(fminl(fmaxl((0.0L)-(params->a), (((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t)))))-((10.0L)*(params->vh))), fminl(fmaxl(params->a, (pre.v)-(params->vh)), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((pre.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((fabsl(pre.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L))))), fminl(fmaxl((0.0L)-(params->a), (params->vl)-(pre.v)), fminl(fmaxl(params->a, ((10.0L)*(params->vl))-(((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t)))))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))))))-(((((2.0L)*(params->A))*((pre.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))))))-(((((2.0L)*(params->A))*((fabsl(pre.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))))))+(-((0.0L)-(curr.v))))+(-((curr.t)-(params->T))))+(-(fminl(fmaxl((0.0L)-(curr.t), fmaxl(((((params->k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)))), (((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))))-((((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))), fmaxl((0.0L)-(((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t))))), fmaxl(fminl(fmaxl((0.0L)-(params->a), (((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t)))))-((10.0L)*(params->vh))), fminl(fmaxl(params->a, (curr.v)-(params->vh)), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L))))), fminl(fmaxl((0.0L)-(params->a), (params->vl)-(curr.v)), fminl(fmaxl(params->a, ((10.0L)*(params->vl))-(((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t)))))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))))))-(((((2.0L)*(params->A))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))))))-(((((2.0L)*(params->A))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-3, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-4, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-5, .val=((-1.0L))+(-(fminl(fmaxl((0.0L)-(curr.t), fmaxl(((((params->k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)))), (((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))))-((((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))), fmaxl((0.0L)-(((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t))))), fmaxl(fminl(fmaxl((0.0L)-(params->a), (((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t)))))-((10.0L)*(params->vh))), fminl(fmaxl(params->a, (curr.v)-(params->vh)), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L))))), fminl(fmaxl((0.0L)-(params->a), (params->vl)-(curr.v)), fminl(fmaxl(params->a, ((10.0L)*(params->vl))-(((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t)))))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))))))-(((((2.0L)*(params->A))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))))))-(((((2.0L)*(params->A))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))))) }; return result;\n}\n} else {\nverdict result = { .id=-6, .val=((-1.0L))+(-((curr.t)-(params->T))) }; return result;\n}\n} else {\nverdict result = { .id=-7, .val=((-1.0L))+(-((0.0L)-(curr.v))) }; return result;\n}\n} else {\nverdict result = { .id=-8, .val=((-1.0L))+(-(fminl(fmaxl((0.0L)-(pre.t), fmaxl(((((params->k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))+(-((((2.0L)*(pre.xg))*(100.0L))*(10.0L)))), (((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))+(-((((2.0L)*(pre.xg))*(100.0L))*(10.0L))))-((((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))), fmaxl((0.0L)-(((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t))))), fmaxl(fminl(fmaxl((0.0L)-(params->a), (((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t)))))-((10.0L)*(params->vh))), fminl(fmaxl(params->a, (pre.v)-(params->vh)), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((pre.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((fabsl(pre.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L))))), fminl(fmaxl((0.0L)-(params->a), (params->vl)-(pre.v)), fminl(fmaxl(params->a, ((10.0L)*(params->vl))-(((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t)))))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))))))-(((((2.0L)*(params->A))*((pre.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))))))-(((((2.0L)*(params->A))*((fabsl(pre.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-((pre.t)-(params->T))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-((0.0L)-(pre.v))) }; return result;\n};\n}\n\n/* Evaluates monitor condition in prior and current state */\nbool monitorSatisfied(state pre, state curr, const parameters* const params) {\n  return boundaryDist(pre,curr,params).val >= 0.0L;\n}\n\n/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */\nstate monitoredCtrl(state curr, const parameters* const params, const input* const in,\n                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const)) {\n  state pre = curr;\n  state post = (*ctrl)(pre,params,in);\n  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);\n  else return post;\n}"
  }

  "ModelPlex formula metric" should "convert simple formula" in withMathematica { _ =>
    val fml = "x>=y & a=b & c<=d+e".asFormula
    ModelPlex.toMetric(fml) shouldBe "max(-(x-y),max(max(a-b,-(a-b)),-(d+e-c)))<=0".asFormula
  }

  it should "convert formulas with function symbols" in withMathematica { _ =>
    val fml = "x()>=y & a=b & c<=d+e(f(),g())".asFormula
    ModelPlex.toMetric(fml) shouldBe "max(-(x()-y),max(max(a-b,-(a-b)),-(d+e(f(),g())-c)))<=0".asFormula
  }

  it should "convert simple formula 2" in withMathematica { _ =>
    val fml = "x>=y&a=b | c<=d+e".asFormula
    ModelPlex.toMetric(fml) shouldBe "min(max(-(x-y),max(a-b,-(a-b))),-(d+e-c))<=0".asFormula
  }

  it should "convert simple formula 3" in withMathematica { tool =>
    val fml = "x>=y&a=b&c<=d | c<=d+e | f<=g&h<=0".asFormula
    val metric = ModelPlex.toMetric(fml)
    metric shouldBe "min(max(-(x-y),max(max(a-b,-(a-b)),-(d-c))),min(-(d+e-c),max(-(g-f),--h)))<=0".asFormula
    tool.findCounterExample(metric)
  }

  it should "convert simple formula 4" in withMathematica { tool =>
    val fml = "xpost>=x+5&ypost=y&cpost<=d | cpost>=d+e | fpost<=f&hpost<=0".asFormula
    val metric = ModelPlex.toMetric(fml)
    metric shouldBe "min(max(-(xpost-(x+5)),max(max(ypost-y,-(ypost-y)),-(d-cpost))),min(-(cpost-(d+e)),max(-(f-fpost),--hpost)))<=0".asFormula
    tool.findCounterExample(metric)
  }

  it should "convert inequalities" in withMathematica { _ =>
    val fml = "x!=y | x>4&y!=3".asFormula
    ModelPlex.toMetric(fml) shouldBe "min(min(x-y,-(x-y)),max(-(x-4),min(y-3,-(y-3)))) < 0".asFormula
  }

  it should "convert mixed open/closed formula" in withMathematica { _ =>
    val fml = "x>=y & a<b".asFormula
    ModelPlex.toMetric(fml) shouldBe "max(-(x-y),-(b-a)) < 0".asFormula
  }

  it should "convert disjunctions of mixed open/closed formula" in withMathematica { _ =>
    val fml = "x<5 & y>=2 | x>=y & a<b".asFormula
    ModelPlex.toMetric(fml) shouldBe "min(max(-(5-x),-(y-2)),max(-(x-y),-(b-a))) < 0".asFormula
  }

  it should "convert disjunction of mixed open/closed formula" in withMathematica { _ =>
    val fml = "x<=5 | x>=y & a<b".asFormula
    //@todo metric evaluates to false at the boundary, when x=5 and y>5
    ModelPlex.toMetric(fml) shouldBe "min(-(5-x),max(-(x-y),-(b-a))) < 0".asFormula
  }

  "Partial observability" should "prove non-diverging error bound estimator" in withMathematica { _ =>

  }

  "Aircraft partial observability" should "prove non-diverging error bound estimator property" in withMathematica { _ =>
    val f = "\\forall v (vv+l<=v&v<=vv+u -> P(||)) -> [l:=max(-D,vv0-vv+l; u:=min(D,vv0-vv+u;]\\forall v (vv+l<=v&v<=vv+u -> P(||))".asFormula
    //proveBy(f, implyR(1) & )
  }

//
//  "Quadcopter modelplex in place" should "find correct controller monitor condition" in {
//    val in = getClass.getResourceAsStream("examples/casestudies/modelplex/quadcopter/simplepid.key")
//    val model = KeYmaeraXArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
//    val modelplexInput = createMonitorSpecificationConjecture(model, Variable("h"), Variable("v"), Variable("kp"),
//      Variable("kd"), Variable("href"))
//
//    val tactic = locateSucc(modelplexAxiomaticStyle(useOptOne=true)(controllerMonitorT))
//    val result = proveUncheckedBy(modelplexInput, tactic)
//
//    val expectedAnte = "true".asFormula
//    val expectedSucc = "true&(((hpost=h&vpost=v)&kppost=kp)&kdpost=kd)&hrefpost=href".asFormula
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
////    val model = KeYmaeraXArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
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
//    //"(-1<=fpost&fpost<=(m-l)/ep)&(0<=l&0<=ep)&(fpost=fpost&lpost=l)&cpost=0".asFormula
//    val input = "-1<=fpost&fpost*ep+(l-m)<=0".asFormula
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