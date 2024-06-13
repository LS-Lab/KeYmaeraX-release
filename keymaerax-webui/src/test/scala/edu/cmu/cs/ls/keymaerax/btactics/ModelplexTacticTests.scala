/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.ModelPlex.createMonitorSpecificationConjecture
import edu.cmu.cs.ls.keymaerax.btactics.TacticHelper.timed
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.cli.KeymaeraxWebui
import edu.cmu.cs.ls.keymaerax.codegen._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, FormulaTools, PosInExpr, Statistics}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tagobjects.IgnoreInBuildTest
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.testhelper.ParserFactory._
import org.scalatest.LoneElement._

import java.io.File
import scala.collection.immutable.{IndexedSeq, ListMap}
import scala.language.postfixOps

/**
 * Created by smitsch on 3/8/15.
 *
 * @author
 *   Stefan Mitsch
 * @author
 *   Ran Ji
 */
@SlowTest
class ModelplexTacticTests extends TacticTestBase {

  override def afterEach(): Unit = {
    super.afterEach()
    CPrettyPrinter.printer = null
  }

  def monitorSize(f: Formula): Int = Statistics.countFormulaOperators(f, arith = true)

  private def report(result: Formula, proof: ProvableSig, name: String): Unit = {
    println(s"$name monitor size: " + monitorSize(result))
    println("Number of proof steps: " + proof.steps)
  }

  "Simple modelplex" should "chase: find correct controller monitor by updateCalculus implicationally" in withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/simple.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, _) =
      createMonitorSpecificationConjecture(model, List(Variable("x")), ListMap.empty)

    def modelPlex: BuiltInPositionTactic = chase(
      3,
      3,
      (e: Expression) =>
        e match {
          // no equational assignments
          case Box(Assign(_, _), _) => Ax.assignbAxiom :: Ax.assignbup :: Nil
          case Diamond(Assign(_, _), _) => Ax.assigndAxiom :: Ax.assigndup :: Nil
          // remove loops
          case Diamond(Loop(_), _) => Ax.loopApproxd :: Nil
          // remove ODEs for controller monitor
          case Diamond(ODESystem(_, _), _) => Ax.dDX :: Nil
          case _ => AxIndex.axiomsFor(e)
        },
    )

    val result = TactixLibrary.proveBy(modelplexInput, modelPlex(1))
    result.subgoals.loneElement shouldBe "==> xpost=1".asSequent

    val monitorCorrectnessConjecture = ModelPlex
      .createMonitorCorrectnessConjecture(List(Variable("x")), ModelPlexKind.Ctrl, None, ListMap.empty)(model)
    println("Correctness conjecture " + monitorCorrectnessConjecture.prettyString)
    proveBy(monitorCorrectnessConjecture, implyR(1) * 2 & ModelPlex.controllerMonitorByChase(1) & autoClose) shouldBe
      Symbol("proved")
  }

  it should "chase away a loop by updateCalculus implicationally" in withTactics {
    val model = ArchiveParser.parseAsFormula("ProgramVariables. R x. End. Problem. 0 <= x -> [{x:=2;}*](0 <= x) End.")
    val ModelPlexConjecture(_, modelplexInput, _) =
      createMonitorSpecificationConjecture(model, List(Variable("x")), ListMap.empty)

    def modelPlex: BuiltInPositionTactic = chase(
      3,
      3,
      (e: Expression) =>
        e match {
          case Diamond(Loop(_), _) => Ax.loopApproxd :: Nil
          case _ => AxIndex.axiomsFor(e)
        },
    )

    proveBy(modelplexInput, modelPlex(1)).subgoals.loneElement shouldBe "==> xpost=2".asSequent
  }

  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("f", "l", "c").map(_.asVariable), ListMap.empty)

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals.loneElement shouldBe
      "==> \\exists f ((-1<=f&f<=(m()-l)/ep())&(0<=l&0<=ep())&fpost=f&lpost=l&cpost=0)".asSequent

    // Opt. 1
    val opt1Result = proveBy(
      foResult.subgoals.head,
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    opt1Result.subgoals.loneElement shouldBe
      "==> ((-1)<=fpost&fpost<=(m()-l)/ep())&(0<=l&0<=ep())&lpost=l&cpost=0".asSequent

    report(opt1Result.subgoals.head.succ.head, opt1Result, "Water tank controller monitor (forward chase)")
  }

  it should "find correct model monitor condition" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("f", "l", "c").map(_.asVariable), ListMap.empty)
    val expected =
      "==> ((-1)<=fpost&fpost<=(m()-l)/ep())&(0=cpost&(lpost=l&(fpost < 0&(0=ep()&l>=0|ep()>0&l>=0)|(ep()>=0&l>=0)&fpost>0)|((fpost=0&l=lpost)&ep()>=0)&l>=0)|(cpost>0&ep()>=cpost)&(l>=0&(fpost=0&l=lpost|lpost=cpost*fpost+l&fpost>0)|(lpost=cpost*fpost+l&fpost < 0)&cpost*fpost+l>=0))"
        .asSequent

    val axiomatic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.modelMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1)
    proveBy(modelplexInput, axiomatic).subgoals.loneElement shouldBe expected

    val byChase = ModelPlex.modelMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1)
    val byChaseResult = proveBy(modelplexInput, byChase).subgoals.loneElement
    proveBy(Equiv(expected.toFormula, byChaseResult.toFormula), QE) shouldBe Symbol("proved")
  }

  it should "find euler model monitor condition" ignore withMathematica { tool =>
    val model = "true -> [x:=2;{x'=-3*x}]x>0".asFormula
    val ModelPlexConjecture(_, modelplexConjecture, assumptions) =
      createMonitorSpecificationConjecture(model, List(Variable("x")), ListMap.empty)
    // replace post with post()
    // @todo no longer necessary when axiom is added to axiom base
    val modelplexInput = ExpressionTraversal
      .traverse(
        new ExpressionTraversalFunction() {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
            case BaseVariable(v, i, s) if v.endsWith("post") => Right(FuncOf(Function(v, i, Unit, s), Nothing))
            case _ => Left(None)
          }
        },
        modelplexConjecture,
      )
      .get

    // @todo chase uses supplied tactic in first step, which results in "unexpected" branches since not an axiom
    val tactic = ModelPlex.modelMonitorByChase(ModelPlex.eulerAllIn)(1) <
      (ModelPlex.unrollLoop(2)(1) & ModelPlex.chaseEulerAssignments(1), skip)
    val result = proveBy(modelplexInput, tactic)

    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only
      "\\forall x (x=2->\\exists t_ (t_>=0&\\forall e_ (e_>0->\\forall h0_ (h0_>0->\\exists h_ (0 < h_&h_ < h0_&((t_>=0&\\exists y_ (abs(x-y_) < e_&xpost()=y_))|(t_>=0&\\exists y_ (abs(x+h_*(-3*x)+h_*(-3*(x+h_*(-3*x)))-y_) < e_&xpost()=y_))))))))"
        .asFormula
    // @note don't care about second branch - axiom not in axiom base

    // @note unsound approximation step
    val flipped = ModelPlex.flipUniversalEulerQuantifiers(result.subgoals.head.succ.head)
    flipped shouldBe
      "\\forall x (x=2->\\exists t_ (t_>=0&\\exists e_ (e_>0&\\exists h0_ (h0_>0&\\exists h_ (0 < h_&h_ < h0_&((t_>=0&\\exists y_ (abs(x-y_) < e_&xpost()=y_))|(t_>=0&\\exists y_ (abs(x+h_*(-3*x)+h_*(-3*(x+h_*(-3*x)))-y_) < e_&xpost()=y_))))))))"
        .asFormula

    val simplified =
      proveBy(flipped, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1))
    // @todo auto-generated post names are somewhat weird here for parameters t, e, h0, h
    simplified.subgoals.loneElement shouldBe
      "==> tpost_0>=0&epost_0>0&h0post_0>0&0 < hpost_0&hpost_0 < h0post_0&(abs(2-xpost()) < epost_0|abs(2+hpost_0*-6+hpost_0*(-3*(2+hpost_0*-6))-xpost()) < epost_0)"
        .asSequent
  }

  it should "find euler model monitor condition for systems" ignore withMathematica { tool =>
    val model = "true -> [x:=2;{x'=-3*x,y'=x-y}]x>0".asFormula
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("x", "y").map(_.asVariable), ListMap.empty)

    val eulerApproxed = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(ModelPlex.eulerSystemAllIn)(1))
    eulerApproxed.subgoals should have size 2
    eulerApproxed.subgoals.head.ante shouldBe empty
    eulerApproxed.subgoals.head.succ should contain only
      "\\forall x (x=2->\\exists t_ (t_>=0&\\forall e_ (e_>0->\\forall h0_ (h0_>0->\\exists h_ (0 < h_&h_ < h0_&<{{x_0:=x;y_0:=y;}x:=x+h_*(-3*x_0);y:=y+h_*(x_0-y_0);}*>(t_>=0&\\exists yy \\exists yx ((x-yx)^2+(y-yy)^2 < e_^2&xpost=yx&ypost=yy)))))))"
        .asFormula

    val tactic = ModelPlex.modelMonitorByChase(ModelPlex.eulerSystemAllIn)(1) <
      (ModelPlex.unrollLoop(1)(1) & SaturateTactic(ModelPlex.chaseEulerAssignments(1)), skip)
    val result = proveBy(modelplexInput, tactic)
    result.subgoals should have size 2
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only
      "\\forall x (x=2->\\exists t_ (t_>=0&\\forall e_ (e_>0->\\forall h0_ (h0_>0->\\exists h_ (0 < h_&h_ < h0_&t_>=0&\\exists yy \\exists yx ((x+h_*(-3*x)-yx)^2+(y+h_*(x-y)-yy)^2 < e_^2&xpost=yx&ypost=yy))))))"
        .asFormula

    // @note unsound approximation step
    val flipped = ModelPlex.flipUniversalEulerQuantifiers(result.subgoals.head.succ.head)
    val simplified =
      proveBy(flipped, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1))
    // @todo auto-generated post names are somewhat weird here for parameters t, e, h0, h
    simplified.subgoals.loneElement shouldBe
      "==> tpost_0>=0&epost_0>0&h0post_0>0&0 < hpost_0&hpost_0 < h0post_0&(2+hpost_0*-6-xpost)^2+(y+hpost_0*(2-y)-ypost)^2 < epost_0^2"
        .asSequent
  }

  "Watertank modelplex in place" should "find correct controller monitor condition with Optimization 1" in withTactics {
    val s = ArchiveParser.parseAsFormula(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank-ctrl.key"))
        .mkString
    )
    val expected = "(-1<=fpost&fpost<=(m()-x)/ep())&xpost=x&tpost=0".asFormula

    val axiomatic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val axiomaticResult = proveBy(s, axiomatic)
    axiomaticResult.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))

    val byChase = ModelPlex.controllerMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val byChaseResult = proveBy(s, byChase)
    byChaseResult.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))

    report(expected, axiomaticResult, "Watertank controller monitor (backward tactic)")
    report(expected, byChaseResult, "Watertank controller monitor (chase)")
  }

  it should "chase controller monitor condition to tests" in withMathematica { tool =>
    val model = ArchiveParser.parseAsFormula(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key"))
        .mkString
    )
    val Imply(_, Box(prg, _)) = model

    val stateVars = List("f", "l", "c").map(_.asVariable.asInstanceOf[BaseVariable])
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, stateVars, ListMap.empty)
    val tactic = ModelPlex.controllerMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1)
    val result = proveBy(modelplexInput, tactic)

    val testProg = proveBy(result.subgoals.loneElement, ModelPlex.chaseToTests(combineTests = false)(1))
    testProg.subgoals.loneElement shouldBe
      "==> <?-1<=fpost&fpost<=(m()-l)/ep();><?0<=l&0<=ep();><?lpost=l;><?cpost=0;>true".asSequent

    val monitorFml = result.subgoals.loneElement.succ.head
    val reassociatedMonitorFml = FormulaTools.reassociate(monitorFml)
    proveBy(Equiv(monitorFml, reassociatedMonitorFml), prop) shouldBe Symbol("proved")

    // example: combine all tests for a single if-then-else condition
    val testProg2 = proveBy(reassociatedMonitorFml, ModelPlex.chaseToTests(combineTests = true)(1) * 2)
    testProg2.subgoals.loneElement shouldBe
      "==> <?((((-1<=fpost&fpost<=(m()-l)/ep())&0<=l)&0<=ep())&lpost=l)&cpost=0;>true".asSequent

    val inputs = CodeGenerator.getInputs(prg)
    CPrettyPrinter.printer = new CExpressionPlainPrettyPrinter(printDebugOut = true)
    val code = (
      new CMonitorGenerator(Symbol("resist"), Declaration(Map.empty))
    )(testProg.subgoals.head.succ.head, stateVars.toSet, inputs, "Monitor")
    code._1.trim should equal(
      """/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */
        |verdict boundaryDist(state pre, state curr, const parameters* const params) {
        |  if (((-1.0L) <= curr.f) && (curr.f <= ((params->m)-(pre.l))/(params->ep))) {
        |if ((0.0L <= pre.l) && (0.0L <= params->ep)) {
        |if (curr.l == pre.l) {
        |if (curr.c == 0.0L) {
        |verdict result = { .id=1, .val=(1.0L)/(((1.0L)/(-(fmaxl(((-1.0L))-(curr.f), (curr.f)-(((params->m)-(pre.l))/(params->ep))))))+((1.0L)/(-(fmaxl(-(pre.l), -(params->ep)))))) }; return result;
        |} else {
        |printf("Failed %d=%s\n", -1, "cpost=0"); verdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl(curr.c, -(curr.c)))) }; return result;
        |}
        |} else {
        |printf("Failed %d=%s\n", -2, "lpost=l"); verdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.l)-(pre.l), (pre.l)-(curr.l)))) }; return result;
        |}
        |} else {
        |printf("Failed %d=%s\n", -3, "0<=l&0<=ep()"); verdict result = { .id=-3, .val=((-1.0L))+(-(fmaxl(-(pre.l), -(params->ep)))) }; return result;
        |}
        |} else {
        |printf("Failed %d=%s\n", -4, "(-1)<=fpost&fpost<=(m()-l)/ep()"); verdict result = { .id=-4, .val=((-1.0L))+(-(fmaxl(((-1.0L))-(curr.f), (curr.f)-(((params->m)-(pre.l))/(params->ep))))) }; return result;
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
        |                    state (*ctrl)(state,const parameters* const,const input* const),
        |                    state (*fallback)(state,const parameters* const,const input* const)) {
        |  state pre = curr;
        |  state post = (*ctrl)(pre,params,in);
        |  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);
        |  else return post;
        |}""".stripMargin
    )(after being whiteSpaceRemoved)

    val monitorCode = (
      new CGenerator(new CMonitorGenerator(Symbol("resist"), Declaration(Map.empty)), True, Declaration(Map.empty))
    )(testProg2.subgoals.head.succ.head, stateVars.toSet, inputs, "Monitor")

    val codeFileContent =
      s"""#include <stdio.h>
         |${monitorCode._1}
         |state ctrl(state curr, const parameters* const params, const input* const in) { return curr; }
         |state fallback(state curr, const parameters* const params, const input* const in) { return curr; }
         |int main() { return 0; }
         |""".stripMargin

    val file = CodeGenTestTools.compileC(codeFileContent)
    val p = Runtime.getRuntime.exec(Array(file))
    withClue(scala.io.Source.fromInputStream(p.getErrorStream).mkString) { p.waitFor() shouldBe 0 }
  }

  it should "find correct controller monitor condition from model file" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, _) =
      createMonitorSpecificationConjecture(model, List("f", "l", "c").map(_.asVariable), ListMap.empty)

    val tactic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(Symbol("R")) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val result = proveBy(modelplexInput, tactic)

    val expected = "(-1<=fpost_0&fpost_0<=(m-l)/ep)&(0<=l&0<=ep)&(fpost=fpost_0&lpost=l)&cpost=0".asFormula
    result.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))
    report(expected, result, "Watertank controller monitor (backward tactic)")
  }

  it should "find correct controller monitor condition without intermediate Optimization 1" in withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/watertank/watertank-ctrl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val expected = "(-1<=fpost&fpost<=(m()-x)/ep())&xpost=x&tpost=0".asFormula

    val axiomatic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val axiomaticResult = proveBy(model, axiomatic)
    axiomaticResult.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))

    val byChase = ModelPlex.controllerMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val byChaseResult = proveBy(model, byChase)
    byChaseResult.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))

    report(expected, axiomaticResult, "Watertank controller monitor (backward tactic)")
    report(expected, byChaseResult, "Watertank controller monitor (chase)")
  }

  it should "work using the command line interface" taggedAs IgnoreInBuildTest in withTactics {
    // command line main has to initialize the prover itself, so dispose all test setup first
    afterEach()

    val inputFileName = "keymaerax-webui/src/test/resources/examples/casestudies/modelplex/watertank/watertank.key"
    val vars = "f,l,c"
    val outputFileName = File.createTempFile("watertank", ".kym").getAbsolutePath
    KeymaeraxWebui.main(Array(
      "-tool",
      "mathematica",
      "-modelplex",
      inputFileName,
      "-vars",
      vars,
      "-monitor",
      "ctrl",
      "-out",
      outputFileName,
    ))

    val expectedFileContent = "(-1<=fpost&fpost<=(m()-l)/ep())&(0<=l&0<=ep())&lpost=l&cpost=0".asFormula

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    Parser(actualFileContent) shouldBe expectedFileContent
  }

  "Local lane control modelplex in place" should "find correct controller monitor condition" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc-ctrl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(Symbol("R")) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val result = proveBy(model, tactic)

    // with ordinary diamond test
    val expected =
      "(-B<=alpost_0&alpost_0<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&(-B<=afpost_0&afpost_0<=A)&xfpost=xf&vfpost=vf&afpost=afpost_0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0|vf=0&xfpost=xf&vfpost=vf&afpost=0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0|(-B<=afpost_0&afpost_0<=-b)&xfpost=xf&vfpost=vf&afpost=afpost_0&xlpost=xl&vlpost=vl&alpost=alpost_0&tpost=0)"
        .asFormula

    result.subgoals.loneElement shouldBe Sequent(
      IndexedSeq(
        "xf < xl & xf + vf^2/(2*b) < xl + vl^2/(2*B) & B >= b & b > 0 & vf >= 0 & vl >= 0 & A >= 0 & ep > 0".asFormula
      ),
      IndexedSeq(expected),
    )

    report(expected, result, "Local lane controller (backward tactic)")
  }

  it should "find correct controller monitor from model" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, _) = createMonitorSpecificationConjecture(
      model,
      List("xl", "vl", "al", "xf", "vf", "af", "t").map(_.asVariable),
      ListMap.empty,
    )

    val tactic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val result = proveBy(modelplexInput, tactic)

    val expected =
      "(-B<=alpost_0&alpost_0<=A)&(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf) < xl+vl^2/(2*B)&(-B<=afpost_0&afpost_0<=A)&(vf>=0&vl>=0&0<=ep)&(((((xlpost=xl&vlpost=vl)&alpost=alpost_0)&xfpost=xf)&vfpost=vf)&afpost=afpost_0)&tpost=0|vf=0&(vf>=0&vl>=0&0<=ep)&(((((xlpost=xl&vlpost=vl)&alpost=alpost_0)&xfpost=xf)&vfpost=vf)&afpost=0)&tpost=0|(-B<=afpost_0&afpost_0<=-b)&(vf>=0&vl>=0&0<=ep)&(((((xlpost=xl&vlpost=vl)&alpost=alpost_0)&xfpost=xf)&vfpost=vf)&afpost=afpost_0)&tpost=0)"
        .asFormula
    result.subgoals.loneElement shouldBe Sequent(IndexedSeq(True), IndexedSeq(expected))
    report(expected, result, "LLC controller monitor (backward tactic)")
  }

  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fm11/llc.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) = createMonitorSpecificationConjecture(
      model,
      List("xl", "vl", "al", "xf", "vf", "af", "t").map(_.asVariable),
      ListMap.empty,
    )

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals.loneElement shouldBe
      "==> \\exists al ((-B()<=al&al<=A())&(xf+vf^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*vf) < xl+vl^2/(2*B())&\\exists af ((-B()<=af&af<=A())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=al&xfpost=xf&vfpost=vf&afpost=af&tpost=0)|vf=0&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=al&xfpost=xf&vfpost=vf&afpost=0&tpost=0|\\exists af ((-B()<=af&af<=-b())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&alpost=al&xfpost=xf&vfpost=vf&afpost=af&tpost=0)))"
        .asSequent

    val opt1Result = proveBy(
      foResult.subgoals.head,
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    opt1Result.subgoals.loneElement shouldBe
      "==> (-B()<=alpost&alpost<=A())&(xf+vf^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*vf) < xl+vl^2/(2*B())&(-B()<=afpost&afpost<=A())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&xfpost=xf&vfpost=vf&tpost=0|vf=0&(vl>=0&0<=ep())&xlpost=xl&vlpost=vl&xfpost=xf&vfpost=0&afpost=0&tpost=0|(-B()<=afpost&afpost<=-b())&(vf>=0&vl>=0&0<=ep())&xlpost=xl&vlpost=vl&xfpost=xf&vfpost=vf&tpost=0)"
        .asSequent

    report(opt1Result.subgoals.head.succ.head, opt1Result, "LLC controller monitor (forward chase)")
  }

  "Fixedwing" should "find correct controller monitor" in withMathematica { implicit tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/fixedwing_simple_nobound.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) = createMonitorSpecificationConjecture(
      model,
      List("a", "w", "xo", "theta", "dxy", "y", "t", "v", "dx", "w", "yo", "dz", "x", "dy").map(_.asVariable),
      ListMap.empty,
    )

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals.loneElement shouldBe
      "==> (v=Vmin()&(theta=Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=0&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=-W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy)|v>Vmin()&(theta=Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=0&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&((!theta=Theta()|dxy=dXY()&dz=dZ())&(!theta=-Theta()|dxy=-dXY()&dz=dZ()))&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=-B()&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=-W()&yopost=yo&dzpost=dz&xpost=x&dypost=dy))|\\exists a ((-B()<=a&a<=A())&\\exists w ((-W()<=w&w<=W())&\\exists v (v>=Vmin()&\\exists theta ((-Theta()<=theta&theta<=Theta())&\\exists xo \\exists yo ((abs(x-xo)>(v^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*v)&abs(x-xo)>(v^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(theta))/W()-(v-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*v)+Vmin()*ep()|abs(y-yo)>(v^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*v)&abs(y-yo)>(v^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(theta))/W()-(v-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*v)+Vmin()*ep())&(0<=ep()&v>=Vmin()&-Theta()<=theta&theta<=Theta())&apost=a&wpost=w&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&wpost=w&yopost=yo&dzpost=dz&xpost=x&dypost=dy)))))"
        .asSequent

    val opt1Result = proveBy(
      foResult.subgoals.head,
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    opt1Result.subgoals.loneElement shouldBe
      "==> (v=Vmin()&(theta=Theta()&((dxy=dXY()&dz=dZ())&(theta!=-Theta()|dxy=-dXY()))&(0<=ep()&-Theta()<=theta)&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((theta!=Theta()|dxy=dXY()&dz=dZ())&dxy=-dXY()&dz=dZ())&(0<=ep()&theta<=Theta())&apost=0&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&(theta!=-Theta()|dxy=-dXY()&dz=dZ())&(0<=ep()&-Theta()<=theta)&apost=0&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&(theta!=Theta()|dxy=dXY()&dz=dZ())&(0<=ep()&theta<=Theta())&apost=0&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy)|v>Vmin()&(theta=Theta()&((dxy=dXY()&dz=dZ())&(theta!=-Theta()|dxy=-dXY()))&(0<=ep()&-Theta()<=theta)&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|theta=-Theta()&((theta!=Theta()|dxy=dXY()&dz=dZ())&dxy=-dXY()&dz=dZ())&(0<=ep()&theta<=Theta())&apost=-B()&wpost=0&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(0<=theta&theta < Theta())&(theta!=-Theta()|dxy=-dXY()&dz=dZ())&(0<=ep()&-Theta()<=theta)&apost=-B()&wpost=W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy|(-Theta() < theta&theta < 0)&(theta!=Theta()|dxy=dXY()&dz=dZ())&(0<=ep()&theta<=Theta())&apost=-B()&wpost=-W()&xopost=xo&thetapost=theta&dxypost=dxy&ypost=y&tpost=0&vpost=v&dxpost=dx&yopost=yo&dzpost=dz&xpost=x&dypost=dy))|(-B()<=apost&apost<=A())&(-W()<=wpost&wpost<=W())&vpost>=Vmin()&(-Theta()<=thetapost&thetapost<=Theta())&(abs(x-xopost)>(vpost^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)&abs(x-xopost)>(vpost^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(thetapost))/W()-(vpost-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)+Vmin()*ep()|abs(y-yopost)>(vpost^2-Vmin()^2)/(2*B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)&abs(y-yopost)>(vpost^2-Vmin()^2)/(2*B())+Vmin()*((Theta()-abs(thetapost))/W()-(vpost-Vmin())/B())+2*r()+(A()/B()+1)*(A()/2*ep()^2+ep()*vpost)+Vmin()*ep())&0<=ep()&dxypost=dxy&ypost=y&tpost=0&dxpost=dx&dzpost=dz&xpost=x&dypost=dy"
        .asSequent

    report(opt1Result.subgoals.head.succ.head, opt1Result, "Fixedwing controller monitor (forward chase)")
  }

  "ETCS safety lemma modelplex in place" should "find correct controller monitor by updateCalculus implicationally" in
    withMathematica { tool =>
      val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/icfem08/safetylemma.key")
      val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
      val ModelPlexConjecture(_, modelplexInput, assumptions) = createMonitorSpecificationConjecture(
        model,
        List("vdes", "SB", "v", "state", "do", "z", "t", "mo", "m", "d", "a").map(_.asVariable),
        ListMap.empty,
      )

      val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
      foResult.subgoals.loneElement shouldBe
        "==> (\\forall do (do=d->\\forall mo (mo=m->\\exists m \\exists d \\exists vdes ((d>=0&do^2-d^2<=2*b()*(m-mo)&vdes>=0)&vdespost=vdes&SBpost=SB&vpost=v&statepost=state&dopost=do&zpost=z&tpost=t&mopost=mo&mpost=m&dpost=d&apost=a)))|vdespost=vdes&SBpost=SB&vpost=v&statepost=brake&dopost=do&zpost=z&tpost=t&mopost=mo&mpost=m&dpost=d&apost=a)|v<=vdes&\\exists a ((a>=-b()&a<=A())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=a))|v>=vdes&\\exists a ((a < 0&a>=-b())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=a))"
          .asSequent

      val opt1Result = proveBy(
        foResult.subgoals.head,
        ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
      )
      StaticSemantics.boundVars(opt1Result.subgoals.loneElement) shouldBe Symbol("empty")
      opt1Result.subgoals.loneElement shouldBe
        "==> ((dpost>=0&d^2-dpost^2<=2*b()*(mpost-m)&vdespost>=0)&SBpost=SB&vpost=v&statepost=state&dopost=d&zpost=z&tpost=t&mopost=m&apost=a|vdespost=vdes&SBpost=SB&vpost=v&statepost=brake&dopost=do&zpost=z&tpost=t&mopost=mo&mpost=m&dpost=d&apost=a)|v<=vdes&(apost>=-b()&apost<=A())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d)|v>=vdes&(apost < 0&apost>=-b())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|state=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d&apost=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&state!=brake)&(v>=0&0<=ep())&vdespost=vdes&SBpost=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost=v&statepost=state&dopost=do&zpost=z&tpost=0&mopost=mo&mpost=m&dpost=d)"
          .asSequent

      report(opt1Result.subgoals.head.succ.head, opt1Result, "ETCS controller monitor (forward chase)")
    }

  it should "find controller monitor condition from safety proof" in withMathematica { tool =>
    val Some(entry) = ArchiveParser.getEntry(
      "ICFEM09/Proposition 5: Safety",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/etcs/etcs.kyx")).mkString,
    )
    val model = entry.expandedModel.asInstanceOf[Formula]

    val unobservable: ListMap[NamedSymbol, Option[Formula]] =
      ListMap.empty // add sensor definitions here if some variables should be unobservable
    val sensorDefs = unobservable.filter(_._1.isInstanceOf[Variable])
    val allVars = StaticSemantics
      .boundVars(entry.expandedModel.asInstanceOf[Formula])
      .toSet
      .filter(_.isInstanceOf[BaseVariable])
      .toList

    val ModelPlexConjecture(init, modelMonitorInput, assumptions) = ModelPlex
      .createMonitorSpecificationConjecture(model, allVars, unobservable)
    println("Monitor specification: " + modelMonitorInput.prettyString)

    Configuration.set(Configuration.Keys.MATHEMATICA_QE_METHOD, "Resolve", saveToFile = false)
    val chaseStartPos = List.fill(unobservable.size)(0) ++
      (if (unobservable.values.exists(_.isDefined)) 1 :: Nil else Nil)
    val foResult = timed(proveBy(modelMonitorInput, ModelPlex.controllerMonitorByChase(1, chaseStartPos)), "Chasing")
    println("FO result: " + foResult)

    val opt1Result = timed(
      proveBy(
        foResult,
        ModelPlex
          .optimizationOneWithSearch(Some(tool), assumptions, unobservable.keySet.toList, Some(ModelPlex.mxSimplify))(1),
      ),
      "Opt. 1",
    )
    StaticSemantics.freeVars(opt1Result.subgoals.loneElement).toSet[NamedSymbol].intersect(unobservable.keySet) shouldBe
      Symbol("empty")
    println("Opt. 1 result: " + opt1Result)

    val qfResult = timed(
      proveBy(entry.defs.exhaustiveSubst(opt1Result.subgoals.loneElement), SimplifierV3.simplify(1)),
      "Simplifying",
    )

    val testResult = timed(
      proveBy(qfResult, PropositionalTactics.rightAssociate(1) & ModelPlex.chaseToTests(combineTests = false)(1)),
      "Combining tests",
    )

    val testProg = testResult.subgoals.loneElement.succ.loneElement
    val Imply(_, Box(Loop(prg), _)) = entry.expandedModel
    val inputs = CodeGenerator.getInputs(prg) -- sensorDefs.keySet.map(_.asInstanceOf[BaseVariable])
    println("Inputs: " + inputs)
    val sensors = sensorDefs
      .values
      .flatMap(_.map(StaticSemantics.freeVars(_).toSet))
      .reduceOption(_ ++ _)
      .getOrElse(Set.empty)
      .map(_.asInstanceOf[BaseVariable])
    println("Sensors: " + sensors)

    println("Generating Python code")
    val stateVars = allVars.map(_.asInstanceOf[BaseVariable]).toSet ++ sensors --
      sensorDefs.keySet.map(_.asInstanceOf[BaseVariable])
    println("Monitor state: " + stateVars)
    val monitorPythonCode = timed(
      (
        new PythonGenerator(new PythonMonitorGenerator(Symbol("resist"), entry.defs), init, entry.defs)
      )(testProg, stateVars, inputs, entry.name),
      "Printing Python code",
    )
    println(monitorPythonCode)
  }

  "RSS passive safety modelplex in place" should "find correct controller monitor by updateCalculus implicationally" in
    withMathematica { tool =>
      // val in = getClass.getResourceAsStream("/examples/casestudies/robix/passivesafetyabs.key")
      val Some(entry) = ArchiveParser.getEntry(
        "IJRR17/Theorem 2: Passive safety",
        io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/ijrr/robix.kyx")).mkString,
      )
      val model = entry.defs.exhaustiveSubst(entry.model.asInstanceOf[Formula])
      val ModelPlexConjecture(_, modelplexInput, assumptions) = createMonitorSpecificationConjecture(
        model,
        List("xo", "yo", "vxo", "vyo", "x", "y", "dx", "dy", "v", "w", "a", "r", "t").map(_.asVariable),
        ListMap.empty,
      )

      val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
      foResult.subgoals.loneElement shouldBe
        "==> \\exists vxo \\exists vyo (vxo^2+vyo^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-b()&rpost=r&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|\\exists w ((-W()<=w&w<=W())&\\exists r \\exists xo \\exists yo ((r!=0&r*w=v)&(abs(x-xo)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yo)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=A()&rpost=r&tpost=0))))"
          .asSequent

      val opt1Result = proveBy(
        foResult.subgoals.head,
        ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
      )
      opt1Result.subgoals.loneElement shouldBe
        "==> vxopost^2+vyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-b()&rpost=r&tpost=0|v=0&0<=ep()&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=0&wpost=0&apost=0&rpost=r&tpost=0|(-W()<=wpost&wpost<=W())&(rpost!=0&rpost*wpost=v)&(abs(x-xopost)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&apost=A()&tpost=0)"
          .asSequent

      report(opt1Result.subgoals.head.succ.head, opt1Result, "RSS controller monitor (forward chase)")
    }

  it should "find correct controller monitor by updateCalculus implicationally without simplification tool" in withQE {
    _ =>
      val Some(entry) = ArchiveParser.getEntry(
        "IJRR17/Theorem 2: Passive safety",
        io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/ijrr/robix.kyx")).mkString,
      )
      val model = entry.defs.exhaustiveSubst(entry.model.asInstanceOf[Formula])
      val ModelPlexConjecture(_, modelplexInput, assumptions) = createMonitorSpecificationConjecture(
        model,
        List("xo", "yo", "vxo", "vyo", "x", "y", "dx", "dy", "v", "w", "a", "r", "t").map(_.asVariable),
        ListMap.empty,
      )

      val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
      foResult.subgoals.loneElement shouldBe
        "==> \\exists vxo \\exists vyo (vxo^2+vyo^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-b()&rpost=r&tpost=0|v=0&(0<=ep()&v>=0)&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=0&apost=0&rpost=r&tpost=0|\\exists w ((-W()<=w&w<=W())&\\exists r \\exists xo \\exists yo ((r!=0&r*w=v)&(abs(x-xo)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yo)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=A()&rpost=r&tpost=0))))"
          .asSequent

      val opt1AltResult = proveBy(
        foResult.subgoals.head,
        ModelPlex.optimizationOneWithSearch(None, assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
      )
      opt1AltResult.subgoals.loneElement shouldBe
        "==> vxopost^2+vyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-b()&rpost=r&tpost=0|v=0&0<=ep()&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=0&wpost=0&apost=0&rpost=r&tpost=0|(-W()<=wpost&wpost<=W())&(rpost!=0&rpost*wpost=v)&(abs(x-xopost)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&apost=A()&tpost=0)"
          .asSequent

      report(opt1AltResult.subgoals.head.succ.head, opt1AltResult, "RSS controller monitor (forward chase)")
  }

  it should "find the correct controller monitor condition from the input model" in withTactics {
    val Some(entry) = ArchiveParser.getEntry(
      "IJRR17/Theorem 2: Passive safety",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/ijrr/robix.kyx")).mkString,
    )
    val model = entry.defs.exhaustiveSubst(entry.model.asInstanceOf[Formula])
    val ModelPlexConjecture(_, modelplexInput, _) = createMonitorSpecificationConjecture(
      model,
      List("xo", "yo", "vxo", "vyo", "x", "y", "dx", "dy", "v", "w", "a", "r", "t").map(_.asVariable),
      ListMap.empty,
    )
    val expected =
      "vxopost^2+vyopost^2<=V()^2&((0<=ep()&v>=0)&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&wpost=w&apost=-b()&rpost=r&tpost=0|v=0&0<=ep()&xopost=xo&yopost=yo&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=0&wpost=0&apost=0&rpost=r&tpost=0|(-W()<=wpost&wpost<=W())&(rpost!=0&rpost*wpost=v)&(abs(x-xopost)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V()))|abs(y-yopost)>v^2/(2*b())+V()*v/b()+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V())))&(0<=ep()&v>=0)&xpost=x&ypost=y&dxpost=dx&dypost=dy&vpost=v&apost=A()&tpost=0)"
        .asFormula

    val axiomatic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val axiomaticResult = proveBy(modelplexInput, axiomatic)
    axiomaticResult.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))

    val byChase = ModelPlex.controllerMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val byChaseResult = proveBy(modelplexInput, byChase)
    byChaseResult.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))

    report(expected, axiomaticResult, "RSS controller monitor (backward tactic)")
    report(expected, byChaseResult, "RSS controller monitor (chase)")
  }

  "RSS passive orientation safety modelplex in place" should
    "extract the correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
      val Some(entry) = ArchiveParser.getEntry(
        "IJRR17/Theorem 4: Passive orientation safety",
        io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/ijrr/robix.kyx")).mkString,
      )
      val model = entry.defs.exhaustiveSubst(entry.model.asInstanceOf[Formula])

      val ModelPlexConjecture(_, modelplexInput, assumptions) = createMonitorSpecificationConjecture(
        model,
        List("x", "y", "v", "a", "dx", "dy", "w", "r", "xo", "yo", "vxo", "vyo", "t", "beta", "visDeg")
          .map(_.asVariable),
        ListMap.empty,
      )

      val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
      foResult.subgoals.loneElement shouldBe
        "==> \\exists vxo \\exists vyo (vxo^2+vyo^2<=V()^2&(\\exists w (w*r=v&(0<=ep()&v>=0)&xpost=x&ypost=y&vpost=v&apost=-b()&dxpost=dx&dypost=dy&wpost=w&rpost=r&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&tpost=0&betapost=beta&visDegpost=visDeg)|v=0&\\exists w (w*r=v&(0<=ep()&v>=0)&xpost=x&ypost=y&vpost=v&apost=0&dxpost=dx&dypost=dy&wpost=w&rpost=r&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&tpost=0&betapost=beta&visDegpost=visDeg)|\\exists r (r!=0&\\exists xo \\exists yo \\exists visDeg ((visDeg>0->abs(x-xo)>v^2/(2*b())+V()*v/b()+((A()/b()+1)*(A()/2*ep()^2+ep()*v)+(A()/b()+1)*ep()*V())|abs(y-yo)>v^2/(2*b())+V()*v/b()+((A()/b()+1)*(A()/2*ep()^2+ep()*v)+(A()/b()+1)*ep()*V()))&v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < GammA()*abs(r)&\\exists w (w*r=v&(0<=ep()&v>=0)&xpost=x&ypost=y&vpost=v&apost=A()&dxpost=dx&dypost=dy&wpost=w&rpost=r&xopost=xo&yopost=yo&vxopost=vxo&vyopost=vyo&tpost=0&betapost=0&visDegpost=visDeg)))))"
          .asSequent

      // Opt. 1
      val opt1Result = proveBy(
        foResult.subgoals.head,
        ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
      )
      opt1Result.subgoals.loneElement shouldBe
        "==> vxopost^2+vyopost^2<=V()^2&(wpost*r=v&(0<=ep()&v>=0)&xpost=x&ypost=y&vpost=v&apost=-b()&dxpost=dx&dypost=dy&rpost=r&xopost=xo&yopost=yo&tpost=0&betapost=beta&visDegpost=visDeg|v=0&wpost*r=0&0<=ep()&xpost=x&ypost=y&vpost=0&apost=0&dxpost=dx&dypost=dy&rpost=r&xopost=xo&yopost=yo&tpost=0&betapost=beta&visDegpost=visDeg|rpost!=0&(visDegpost>0->abs(x-xopost)>v^2/(2*b())+V()*v/b()+((A()/b()+1)*(A()/2*ep()^2+ep()*v)+(A()/b()+1)*ep()*V())|abs(y-yopost)>v^2/(2*b())+V()*v/b()+((A()/b()+1)*(A()/2*ep()^2+ep()*v)+(A()/b()+1)*ep()*V()))&v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < GammA()*abs(rpost)&wpost*rpost=v&(0<=ep()&v>=0)&xpost=x&ypost=y&vpost=v&apost=A()&dxpost=dx&dypost=dy&tpost=0&betapost=0)"
          .asSequent

      // transform to test program
      val testResult = proveBy(opt1Result.subgoals.head, ModelPlex.chaseToTests(combineTests = false)(1))
      testResult.subgoals.loneElement shouldBe
        "==> <?vxopost^2+vyopost^2<=V()^2;>(<?wpost*r=v;><?0<=ep()&v>=0;><?xpost=x;><?ypost=y;><?vpost=v;><?apost=-b();><?dxpost=dx;><?dypost=dy;><?rpost=r;><?xopost=xo;><?yopost=yo;><?tpost=0;><?betapost=beta;><?visDegpost=visDeg;>true|<?v=0;><?wpost*r=0;><?0<=ep();><?xpost=x;><?ypost=y;><?vpost=0;><?apost=0;><?dxpost=dx;><?dypost=dy;><?rpost=r;><?xopost=xo;><?yopost=yo;><?tpost=0;><?betapost=beta;><?visDegpost=visDeg;>true|<?rpost!=0;><?visDegpost>0->abs(x-xopost)>v^2/(2*b())+V()*v/b()+((A()/b()+1)*(A()/2*ep()^2+ep()*v)+(A()/b()+1)*ep()*V())|abs(y-yopost)>v^2/(2*b())+V()*v/b()+((A()/b()+1)*(A()/2*ep()^2+ep()*v)+(A()/b()+1)*ep()*V());><?v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < GammA()*abs(rpost);><?wpost*rpost=v;><?0<=ep()&v>=0;><?xpost=x;><?ypost=y;><?vpost=v;><?apost=A();><?dxpost=dx;><?dypost=dy;><?tpost=0;><?betapost=0;>true)"
          .asSequent

      report(
        opt1Result.subgoals.head.succ.head,
        opt1Result,
        "RSS passive orientation controller monitor (forward chase)",
      )
    }

  "Hybrid quadcopter" should "extract the correct controller monitor" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/quadcopter/hybridquadrotor.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, _) =
      createMonitorSpecificationConjecture(model, List("href", "v", "h").map(_.asVariable), ListMap.empty)

    val tactic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val result = proveBy(modelplexInput, tactic)

    val expected =
      "(h>=hrefpost_0&hrefpost_0>0&((kp < 0&v=0&hrefpost_0>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&hrefpost_0=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*hrefpost_0*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*hrefpost_0*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*hrefpost_0*kp^2+hrefpost_0^2*kp^2+h*kd()*kp*v-hrefpost_0*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>hrefpost_0)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*hrefpost_0*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*hrefpost_0*kp)|kp>0&v=0&(h!=hrefpost_0&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>hrefpost_0|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*hrefpost_0*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*hrefpost_0*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*hrefpost_0*kp|2*hrefpost_0*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*hrefpost_0*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*hrefpost_0*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*hrefpost_0*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*hrefpost_0*kp|2*hrefpost_0*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*hrefpost_0*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*hrefpost_0*kp^2+hrefpost_0^2*kp^2+h*kd()*kp*v-hrefpost_0*kd()*kp*v+kp*v^2=0))&true&(hrefpost=hrefpost_0&vpost=v)&hpost=h"
        .asFormula
    result.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))
    report(expected, result, "Hybrid quadcopter controller monitor (backward tactic)")
  }

  it should "extract the correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/quadcopter/hybridquadrotor.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("href", "v", "h").map(_.asVariable), ListMap.empty)

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals.loneElement shouldBe
      "==> \\exists href ((h>=href&href>0&((kp < 0&v=0&href>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*href*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*href*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&href=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*href*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*href*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*href*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*href*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*href*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*href*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*href*kp^2+href^2*kp^2+h*kd()*kp*v-href*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>href)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*href*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*href*kp)|kp>0&v=0&(h!=href&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>href|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*href*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*href*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*href*kp|2*href*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*href*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*href*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*href*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*href*kp|2*href*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*href*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*href*kp^2+href^2*kp^2+h*kd()*kp*v-href*kd()*kp*v+kp*v^2=0))&true&hrefpost=href&vpost=v&hpost=h)"
        .asSequent

    val opt1Result = proveBy(
      foResult.subgoals.head,
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    opt1Result.subgoals.loneElement shouldBe
      "==> (h>=hrefpost&hrefpost>0&((kp < 0&v=0&hrefpost>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*hrefpost*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*hrefpost*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&hrefpost=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*hrefpost*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*hrefpost*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*hrefpost*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*hrefpost*kp^2+hrefpost^2*kp^2+h*kd()*kp*v-hrefpost*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>hrefpost)|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*hrefpost*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*hrefpost*kp)|kp>0&v=0&(h!=hrefpost&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>hrefpost|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*hrefpost*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*hrefpost*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*hrefpost*kp|2*hrefpost*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*hrefpost*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*hrefpost*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*hrefpost*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*hrefpost*kp|2*hrefpost*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*hrefpost*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*hrefpost*kp^2+hrefpost^2*kp^2+h*kd()*kp*v-hrefpost*kd()*kp*v+kp*v^2=0))&vpost=v&hpost=h"
        .asSequent

    report(opt1Result.subgoals.head.succ.head, opt1Result, "Hybrid quadcopter controller monitor (forward chase)")
  }

  "VSL modelplex in place" should "find correct controller monitor condition" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl-ctrl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val tactic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val result = proveBy(model, tactic)

    // with ordinary diamond test
    val expected =
      "(x1post=x1&v1post=v1&a1post=-B&tpost=0&vslpost=vsl&xslpost=xsl|(vslpost_0>=0&xslpost_0>=x1+(v1^2-vslpost_0^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post=x1&v1post=v1&a1post=-B&tpost=0&vslpost=vslpost_0&xslpost=xslpost_0)|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post_0&a1post_0<=A)&(x1post=x1&v1post=v1&a1post=a1post_0&tpost=0&vslpost=vsl&xslpost=xsl|(vslpost_0>=0&xslpost_0>=x1+(v1^2-vslpost_0^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post=x1&v1post=v1&a1post=a1post_0&tpost=0&vslpost=vslpost_0&xslpost=xslpost_0)|x1>=xsl&(-B<=a1post_0&a1post_0<=A&a1post_0<=(v1-vsl)/ep)&(x1post=x1&v1post=v1&a1post=a1post_0&tpost=0&vslpost=vsl&xslpost=xsl|(vslpost_0>=0&xslpost_0>=x1+(v1^2-vslpost_0^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&x1post=x1&v1post=v1&a1post=a1post_0&tpost=0&vslpost=vslpost_0&xslpost=xslpost_0)"
        .asFormula
    result.subgoals.loneElement shouldBe
      Sequent(IndexedSeq("v1>=0&vsl>=0&x1<=xsl&2*B*(xsl-x1)>=v1^2-vsl^2&A>=0&B>0&ep>0".asFormula), IndexedSeq(expected))
    report(expected, result, "VSL controller (backward tactic from prefabricated conjecture)")
  }

  it should "find correct controller monitor condition from input file" ignore withTactics {
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, _) = createMonitorSpecificationConjecture(
      model,
      List("xsl", "vsl", "x1", "v1", "a1", "t").map(_.asVariable),
      ListMap.empty,
    )

    val tactic = ModelPlex.modelplexAxiomaticStyle(ModelPlex.controllerMonitorT)(1) &
      ModelPlex.optimizationOneWithSearch(None, Nil, Nil, Some(ModelPlex.mxSimplify))(1)
    val result = proveBy(modelplexInput, tactic)

    // with ordinary diamond test
    val expected =
      "((((xslpost=xsl&vslpost=vsl)&x1post=x1)&v1post=v1)&a1post=-B)&tpost=t|xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post_0&a1post_0<=A)&((((xslpost=xsl&vslpost=vsl)&x1post=x1)&v1post=v1)&a1post=a1post_0)&tpost=t|x1>=xsl&(-B<=a1post_0&a1post_0<=A&a1post_0<=(v1-vsl)/ep)&((((xslpost=xsl&vslpost=vsl)&x1post=x1)&v1post=v1)&a1post=a1post_0)&tpost=t|(vslpost_0>=0&xslpost_0>=x1+(v1^2-vslpost_0^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1))&(v1>=0&0<=ep)&((((xslpost=xslpost_0&vslpost=vslpost_0)&x1post=x1)&v1post=v1)&a1post=a1)&tpost=0"
        .asFormula
    result.subgoals.loneElement shouldBe Sequent(IndexedSeq(True), IndexedSeq(expected))
    report(expected, result, "VSL controller monitor (backward tactic)")
  }

  it should "find correct controller monitor by updateCalculus implicationally" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/iccps12/vsl.key")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) = createMonitorSpecificationConjecture(
      model,
      List("xsl", "vsl", "x1", "v1", "a1", "t").map(_.asVariable),
      ListMap.empty,
    )

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1))
    foResult.subgoals.loneElement shouldBe
      "==> xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=-B()&tpost=t|xsl>=x1+(v1^2-vsl^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1)&\\exists a1 ((-B()<=a1&a1<=A())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=a1&tpost=t)|x1>=xsl&\\exists a1 ((-B()<=a1&a1<=A()&a1<=(v1-vsl)/ep())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=a1&tpost=t)|\\exists xsl \\exists vsl ((vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1))&(v1>=0&0<=ep())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=a1&tpost=0)"
        .asSequent

    val expected =
      "xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&a1post=-B()&tpost=t|xsl>=x1+(v1^2-vsl^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1)&(-B()<=a1post&a1post<=A())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&tpost=t|x1>=xsl&(-B()<=a1post&a1post<=A()&a1post<=(v1-vsl)/ep())&xslpost=xsl&vslpost=vsl&x1post=x1&v1post=v1&tpost=t|(vslpost>=0&xslpost>=x1+(v1^2-vslpost^2)/(2*B())+(A()/B()+1)*(A()/2*ep()^2+ep()*v1))&(v1>=0&0<=ep())&x1post=x1&v1post=v1&a1post=a1&tpost=0"
        .asFormula
    val opt1Result = proveBy(
      foResult.subgoals.head,
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    opt1Result.subgoals.loneElement shouldBe Sequent(IndexedSeq.empty, IndexedSeq(expected))

    report(expected, foResult, "VSL controller monitor (forward chase without Opt. 1)")
    report(expected, opt1Result, "VSL controller monitor (forward chase with Opt. 1)")
  }

  "PLDI" should "prove stopsign" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyt"))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "prove stopsign with direct v control" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyt"))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "prove stopsign with v change and disturbance" in withMathematica { _ =>
    val s =
      parseToSequent(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyt"))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "find correct controller monitor for stopsign" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("x", "v", "a", "t").map(_.asVariable), ListMap.empty)

    val result = proveBy(
      modelplexInput,
      ModelPlex.controllerMonitorByChase(1) &
        ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    result.subgoals.loneElement shouldBe
      "==> S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&xpost=x&vpost=v&apost=A&tpost=0|v=0&0<=ep&xpost=x&vpost=0&apost=0&tpost=0|(v>=0&0<=ep)&xpost=x&vpost=v&apost=-b&tpost=0"
        .asSequent

    val Or(acc, Or(coast, brake)) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&xpost=x&vpost=v&apost=A&tpost=0".asFormula
    coast shouldBe "v=0&0<=ep&xpost=x&vpost=0&apost=0&tpost=0".asFormula
    brake shouldBe "(v>=0&0<=ep)&xpost=x&vpost=v&apost=-b&tpost=0".asFormula
  }

  it should "find correct controller monitor for stopsign with direct v control" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("x", "v", "t").map(_.asVariable), ListMap.empty)

    val result = proveBy(
      modelplexInput,
      ModelPlex.controllerMonitorByChase(1) &
        ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    result.subgoals.loneElement shouldBe
      "==> S-x>=ep*vpost&0<=ep&xpost=x&tpost=0|0<=ep&xpost=x&vpost=0&tpost=0".asSequent

    val Or(acc, stop) = result.subgoals.head.succ.head
    acc shouldBe "S-x>=ep*vpost&0<=ep&xpost=x&tpost=0".asFormula
    stop shouldBe "0<=ep&xpost=x&vpost=0&tpost=0".asFormula
  }

  it should "find correct controller monitor for stopsign with direct v change and disturbance" in withMathematica {
    tool =>
      val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyx")
      val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
      val ModelPlexConjecture(_, modelplexInput, assumptions) =
        createMonitorSpecificationConjecture(model, List("x", "v", "d", "c", "t").map(_.asVariable), ListMap.empty)

      val result = proveBy(
        modelplexInput,
        ModelPlex.controllerMonitorByChase(1) &
          ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
      )
      result.subgoals.loneElement shouldBe
        "==> S-x>=ep*(v+cpost+D)&(-D<=dpost&dpost<=D)&0<=ep&xpost=x&vpost=v&tpost=0|0<=ep&xpost=x&vpost=0&dpost=0&cpost=0&tpost=0"
          .asSequent

      val Or(acc, stop) = result.subgoals.head.succ.head
      acc shouldBe "S-x>=ep*(v+cpost+D)&(-D<=dpost&dpost<=D)&0<=ep&xpost=x&vpost=v&tpost=0".asFormula
      stop shouldBe "0<=ep&xpost=x&vpost=0&dpost=0&cpost=0&tpost=0".asFormula
  }

  it should "find correct model monitor for stopsign" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsign.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("x", "v", "a", "t").map(_.asVariable), ListMap.empty)

    val mxResult = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1))
    mxResult.subgoals.loneElement shouldBe
      "==> S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&\\exists t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->A*s_+v>=0&s_+0<=ep)&xpost=A*(t_^2/2)+v*t_+x&vpost=A*t_+v&apost=A&tpost=t_+0)|v=0&\\exists t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->0*s_+v>=0&s_+0<=ep)&xpost=0*(t_^2/2)+v*t_+x&vpost=0*t_+v&apost=0&tpost=t_+0)|\\exists t_ (t_>=0&\\forall s_ (0<=s_&s_<=t_->(-b)*s_+v>=0&s_+0<=ep)&xpost=(-b)*(t_^2/2)+v*t_+x&vpost=(-b)*t_+v&apost=-b&tpost=t_+0)"
        .asSequent
    val result = proveBy(
      mxResult,
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    val Sequent(IndexedSeq(), IndexedSeq(Or(acc, Or(coast, brake)))) = result.subgoals.loneElement
    acc shouldBe
      "S-x>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((((((((ep=0&tpost=0)&(A!=0|apost=0))&(A=0|A=apost))&(v=0|v=vpost))&(v=vpost|vpost=0))&(vpost=0|v>0))&x=xpost)&v>=0|ep>0&((((((((tpost=0&(A!=0|apost=0))&(A=0|A=apost))&(v=0|v=vpost))&(v=vpost|vpost=0))&(vpost=0|v>0))&x=xpost)&v>=0|(tpost>0&tpost < ep)&(v=0&(((A=0&vpost=0)&x=xpost)&apost=0|((A>0&A*tpost=vpost)&xpost=1/2*A*tpost^2+x)&A=apost)|v>0&(((A=0&apost=0)&v=vpost)&tpost*v+x=xpost|((A=apost&A*tpost+v=vpost)&xpost=1/2*A*tpost^2+tpost*v+x)&(A < 0&(-tpost^(-1))*v<=A|A>0))))|ep=tpost&(v=0&(((A=0&vpost=0)&x=xpost)&apost=0|((A>0&A*tpost=vpost)&xpost=1/2*A*tpost^2+x)&A=apost)|v>0&(((A=0&apost=0)&v=vpost)&tpost*v+x=xpost|((A=apost&A*tpost+v=vpost)&xpost=1/2*A*tpost^2+tpost*v+x)&(A < 0&(-ep^(-1))*v<=A|A>0)))))"
        .asFormula
    coast shouldBe "v=0&(((tpost>=0&ep>=tpost)&x=xpost)&0=vpost)&apost=0".asFormula
    brake shouldBe
      "v=0&((vpost=0&x=xpost)&((apost=0&b=0)&(tpost=0&ep>=0|tpost>0&ep>=tpost)|((apost+b=0&tpost=0)&ep>=0)&b!=0)|((((vpost>0&b < 0)&tpost+b^(-1)*vpost=0)&1/2*b*tpost^2+xpost=x)&ep>=tpost)&apost+b=0)|v>0&(v=vpost&((apost=0&b=0)&((tpost=0&x=xpost)&ep>=0|(tpost*v+x=xpost&tpost>0)&ep>=tpost)|(((apost+b=0&tpost=0)&x=xpost)&ep>=0)&b!=0)|((apost+b=0&1/2*b*tpost^2+xpost=tpost*v+x)&ep>=tpost)&(b>0&(tpost=b^(-1)*v&vpost=0|(tpost=b^(-1)*(v+-vpost)&vpost>0)&vpost < v)|(tpost=b^(-1)*(v+-vpost)&vpost>v)&b < 0))"
        .asFormula
  }

  it should "find correct model monitor for stopsign with direct v control" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignv.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("x", "v", "t").map(_.asVariable), ListMap.empty)

    val result = proveBy(
      modelplexInput,
      ModelPlex.modelMonitorByChase(1) &
        ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )

    val Sequent(IndexedSeq(), IndexedSeq(Or(acc, stop))) = result.subgoals.loneElement
    acc shouldBe "S-x>=ep*vpost&(tpost>=0&ep>=tpost)&tpost*vpost+x=xpost".asFormula
    stop shouldBe "((tpost>=0&ep>=tpost)&x=xpost)&vpost=0".asFormula
  }

  it should "find correct model monitor for stopsign with direct v change and disturbance" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/modelplex/pldi16/stopsignvdistchange.kyx")
    val model = ArchiveParser.parseAsFormula(io.Source.fromInputStream(in).mkString)
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("x", "v", "d", "c", "t").map(_.asVariable), ListMap.empty)

    val result = proveBy(
      modelplexInput,
      ModelPlex.modelMonitorByChase(1) &
        ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )

    val Sequent(IndexedSeq(), IndexedSeq(Or(acc, stop))) = result.subgoals.loneElement
    acc shouldBe
      "S-x>=ep*(v+cpost+D)&(-D<=dpost&dpost<=D)&((tpost>=0&ep>=tpost)&tpost*(cpost+dpost+v)+x=xpost)&v=vpost".asFormula
    stop shouldBe "((((tpost>=0&ep>=tpost)&x=xpost)&vpost=0)&dpost=0)&cpost=0".asFormula
  }

  "ModelPlex for Veriphy" should "prove velocity car safety" in withMathematica { _ =>
    val Some(entry) = ArchiveParser.getEntry(
      "Veriphy/Velocity Car Safety",
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/veriphy/velocitycar_extended_dist.kyx"))
        .mkString,
    )
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3, defs = entry.defs) shouldBe Symbol("proved")
  }

  it should "derive controller monitor for velocity car safety" in withMathematica { tool =>
    val Some(entry) = ArchiveParser.getEntry(
      "Veriphy/Velocity Car Safety",
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/veriphy/velocitycar_extended_dist.kyx"))
        .mkString,
    )
    val model = entry.defs.exhaustiveSubst(entry.model.asInstanceOf[Formula])
    val ModelPlexConjecture(_, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, List("d", "v", "t").map(_.asVariable), ListMap.empty)

    val result = proveBy(
      modelplexInput,
      ModelPlex.controllerMonitorByChase(1) &
        ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1),
    )
    result.subgoals.loneElement shouldBe
      "==> d>=V()*ep()&(0<=vpost&vpost<=V())&0<=ep()&dpost=d&tpost=0|0<=ep()&dpost=d&vpost=0&tpost=0".asSequent
  }

  it should "prove controller monitor correctness" in withMathematica { _ =>
    val Some(entry) = ArchiveParser.getEntry(
      "Veriphy/Controller Monitor Formula Implies Controller Monitor Specification",
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/veriphy/velocitycar_extended_dist.kyx"))
        .mkString,
    )
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3) shouldBe Symbol("proved")
  }

  it should "generate a correct sandbox conjecture" in withMathematica { _ =>
    withDatabase { db =>
      val Some(entry) = ArchiveParser.getEntry(
        "Veriphy/Velocity Car Safety",
        io.Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/veriphy/velocitycar_extended_dist.kyx"))
          .mkString,
      )
      val fallback = "t:=0;v:=0;".asProgram
      val ((sandbox, sbTactic), lemmas) = ModelPlex.createSandbox(
        entry.name,
        entry.tactics.head._3,
        Some(fallback),
        ModelPlexKind.Ctrl,
        None,
        synthesizeProofs = false,
        defs = entry.defs,
      )(entry.model.asInstanceOf[Formula])

      sandbox shouldBe
        """d>=0&V>=0&ep>=0
          |->
          |[/* initialize parameters and state variables with anything satisfying init() */
          | { {V:=*;ep:=*;?true;}
          |   {t:=*;v:=*;?true;}
          |   {d:=*;t:=*;?true;}
          |   ?(V>=0&ep>=0)&d>=0;
          | }
          | /* sandbox loop */
          | { {tpost:=*;vpost:=*;?true;}
          |   {dpost:=d;?true;}
          |   {   ?d>=V*ep&(0<=vpost&vpost<=V)&0<=ep&dpost=d&tpost=0|0<=ep&dpost=d&tpost=0&vpost=0;
          |    ++ tpost:=0;vpost:=0;?true;}
          |   {t:=tpost;v:=vpost;?true;}
          |   {dpost:=*;tpost:=*;?true;}
          |   ?tpost>=0&dpost>=v*(ep-tpost)&dpost>=0&tpost<=ep;
          |   d:=dpost;t:=tpost;?true;
          | }*]d>=0
      """.stripMargin.asFormula

      def defs(f: Formula): Declaration = Declaration(Map.empty)

      // @TODO reactivate once sandbox tactic is synthesized

      /*

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

       */
    }
  }

  it should "prove fallback preserves controller monitor" in withMathematica { _ =>
    val Some(entry) = ArchiveParser.getEntry(
      "Veriphy/Fallback Preserves Controller Monitor",
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/veriphy/velocitycar_extended_dist.kyx"))
        .mkString,
    )
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3, defs = entry.defs) shouldBe Symbol("proved")
  }

  it should "check all archive entries" in withMathematica { _ =>
    val entries = ArchiveParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/veriphy/velocitycar_extended_dist.kyx"))
        .mkString
    )
    checkArchiveEntries(entries)
  }

  it should "generate a quantitative monitor" in withMathematica { tool =>
    val Some(entry) = ArchiveParser.getEntry(
      "Veriphy/Velocity Car Safety",
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/veriphy/velocitycar_dist.kyx"))
        .mkString,
    )
    val model = entry.defs.exhaustiveSubst(entry.model.asInstanceOf[Formula])

    val ctrlMonitorStateVars = List("d", "v", "t").map(_.asVariable.asInstanceOf[BaseVariable])
    val ModelPlexConjecture(init, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(model, ctrlMonitorStateVars, ListMap.empty)

    val monitorTactic = DebuggingTactics
      .print("Deriving Monitor") & ModelPlex.controllerMonitorByChase(1) & DebuggingTactics.print("Chased") &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1) &
      DebuggingTactics.print("Monitor Result")
    val ctrlMonitorResult = proveBy(modelplexInput, monitorTactic)
    val ctrlMonitorFml = ctrlMonitorResult.subgoals.head.succ.head
    ctrlMonitorFml shouldBe
      "d>=V()*ep()&(0<=vpost&vpost<=V())&0<=ep()&dpost=d&tpost=0|0<=ep()&dpost=d&vpost=0&tpost=0".asFormula

    /* Generate C code for controller monitor */
    val reassociatedCtrlMonitorFml = FormulaTools.reassociate(ctrlMonitorFml)
    proveBy(Equiv(ctrlMonitorFml, reassociatedCtrlMonitorFml), TactixLibrary.prop) shouldBe Symbol("proved")
    val ctrlMonitorProg =
      proveBy(reassociatedCtrlMonitorFml, ModelPlex.chaseToTests(combineTests = false)(1) * 2).subgoals.head.succ.head
    CPrettyPrinter.printer = new CExpressionPlainPrettyPrinter(printDebugOut = false)
    val ctrlInputs = CodeGenerator.getInputs(ctrlMonitorProg)
    val ctrlMonitorCode = (
      new CGenerator(new CMonitorGenerator(Symbol("resist"), entry.defs), init, entry.defs)
    )(ctrlMonitorProg, ctrlMonitorStateVars.toSet, ctrlInputs, "Monitor")
    ctrlMonitorCode._1.trim should equal(
      """/**************************
        | * Monitor.c
        | * Generated by KeYmaera X
        | **************************/
        |
        |#include <math.h>
        |#include <stdbool.h>
        |
        |/** Model parameters */
        |typedef struct parameters {
        |  long double V;
        |  long double ep;
        |} parameters;
        |
        |/** State (control choices, environment measurements etc.) */
        |typedef struct state {
        |  long double d;
        |  long double t;
        |  long double v;
        |} state;
        |
        |/** Values for resolving non-deterministic assignments in control code */
        |typedef struct input input;
        |
        |/** Monitor verdict: `id` identifies the violated monitor sub-condition, `val` the safety margin (<0 violated, >=0 satisfied). */
        |typedef struct verdict { int id; long double val; } verdict;
        |
        |bool bounds(const parameters* const params, long double V, long double ep) {
        |  return (V >= 0.0L) && (ep >= 0.0L);
        |}
        |bool loopinv(const parameters* const params, long double d) {
        |  return d >= 0.0L;
        |}
        |bool safe(const parameters* const params, long double d) {
        |  return d >= 0.0L;
        |}
        |bool init(const parameters* const params, long double d, long double t, long double v, long double V, long double ep) {
        |  return (d >= 0.0L) && ((v == 0.0L) && ((t == 0.0L) && (bounds(params,V,ep))));
        |}
        |bool throughoutinv(const parameters* const params, long double d, long double t, long double v, long double V, long double ep) {
        |  return (d >= (v)*((ep)-(t))) && ((t >= 0.0L) && ((t <= ep) && ((0.0L <= v) && (v <= V))));
        |}
        |verdict checkInit(const state* const init, const parameters* const params) {
        |  bool initOk = (init->d >= 0.0L) && ((init->v == 0.0L) && ((init->t == 0.0L) && ((params->V >= 0.0L) && (params->ep >= 0.0L))));
        |  verdict result = { .id=(initOk ? 1 : -1), .val=(initOk ? 1.0L : -1.0L) };
        |  return result;
        |}
        |
        |verdict OrLeft430835732(state pre, state curr, const parameters* const params) {
        |  if (pre.d >= (params->V)*(params->ep)) {
        |if (0.0L <= curr.v) {
        |if (curr.v <= params->V) {
        |if (0.0L <= params->ep) {
        |if (curr.d == pre.d) {
        |if (curr.t == 0.0L) {
        |verdict result = { .id=1, .val=(1.0L)/(((1.0L)/((pre.d)-((params->V)*(params->ep))))+((((1.0L)/(curr.v))+((1.0L)/((params->V)-(curr.v))))+((1.0L)/(params->ep)))) }; return result;
        |} else {
        |verdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;
        |}
        |} else {
        |verdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), (pre.d)-(curr.d)))) }; return result;
        |}
        |} else {
        |verdict result = { .id=-3, .val=((-1.0L))+(params->ep) }; return result;
        |}
        |} else {
        |verdict result = { .id=-4, .val=((-1.0L))+((params->V)-(curr.v)) }; return result;
        |}
        |} else {
        |verdict result = { .id=-5, .val=((-1.0L))+(curr.v) }; return result;
        |}
        |} else {
        |verdict result = { .id=-6, .val=((-1.0L))+((pre.d)-((params->V)*(params->ep))) }; return result;
        |}
        |}
        |
        |verdict OrRight_1760563851(state pre, state curr, const parameters* const params) {
        |  if (0.0L <= params->ep) {
        |if (curr.d == pre.d) {
        |if (curr.v == 0.0L) {
        |if (curr.t == 0.0L) {
        |verdict result = { .id=1, .val=params->ep }; return result;
        |} else {
        |verdict result = { .id=-1, .val=((-1.0L))+(-(fmaxl(curr.t, -(curr.t)))) }; return result;
        |}
        |} else {
        |verdict result = { .id=-7, .val=((-1.0L))+(-(fmaxl(curr.v, -(curr.v)))) }; return result;
        |}
        |} else {
        |verdict result = { .id=-2, .val=((-1.0L))+(-(fmaxl((curr.d)-(pre.d), (pre.d)-(curr.d)))) }; return result;
        |}
        |} else {
        |verdict result = { .id=-3, .val=((-1.0L))+(params->ep) }; return result;
        |}
        |}""".stripMargin
    )(after being whiteSpaceRemoved)
    ctrlMonitorCode._2.trim should equal(
      """/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */
        |verdict boundaryDist(state pre, state curr, const parameters* const params) {
        |  verdict leftDist = OrLeft430835732(pre,curr,params);
        |verdict rightDist = OrRight_1760563851(pre,curr,params);
        |int verdictId = leftDist.val >= rightDist.val ? leftDist.id : rightDist.id;
        |verdict result = { .id=verdictId, .val=fmaxl(leftDist.val, rightDist.val) };
        |return result;;
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
        |}""".stripMargin
    )(after being whiteSpaceRemoved)
  }

  "Waypoint navigation" should "generate a controller monitor" in withMathematica { tool =>
    val Some(entry) = ArchiveParser.getEntry(
      "RAL19/Robot preserves loop invariant",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/ral/relative-full.kyx")).mkString,
      parseTactics = false,
    )
    val model = entry.defs.exhaustiveSubst(entry.model.asInstanceOf[Formula])

    val stateVars = List("xg", "yg", "v", "a", "t", "vl", "vh", "k").map(_.asVariable.asInstanceOf[BaseVariable])
    val ModelPlexConjecture(_, modelplexInput, assumptions) = ModelPlex
      .createMonitorSpecificationConjecture(model, stateVars, ListMap.empty)
    val ctrlTactic = DebuggingTactics
      .print("Deriving Ctrl Monitor") & ModelPlex.controllerMonitorByChase(1) & DebuggingTactics.print("Chased") &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1) &
      DebuggingTactics.print("Ctrl Monitor Result")
    val ctrlResult = proveBy(modelplexInput, ctrlTactic)
    val ctrlMonitorFml = ctrlResult.subgoals.head.succ.head
    ctrlMonitorFml shouldBe
      "(ygpost>0&abs(kpost)*eps()<=100&((kpost*(eps()*eps())-200*eps())*100 < kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10&kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10 < (kpost*(eps()*eps())+200*eps())*100)&0<=vlpost&vlpost < vhpost&A()*T()<=10*(vhpost-vlpost)&B()*T()<=10*(vhpost-vlpost))&((-B()<=apost&apost<=A())&10*v+apost*T()>=0&(v<=vhpost&10*v+apost*T()<=10*vhpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(abs(xgpost)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(ygpost-10*eps())*10000*100)&(vlpost<=v&10*v+apost*T()>=10*vlpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(abs(xgpost)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(ygpost-10*eps())*10000*100))&(v>=0&0<=T())&vpost=v&tpost=0"
        .asFormula
  }

  it should "generate monitors from plant overapproximation" ignore withMathematica { tool =>
    // @todo DV
    val Some(entry) = ArchiveParser.getEntry(
      "RAL19/Robot preserves loop invariant",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/ral/relative-full.kyx")).mkString,
      parseTactics = true,
    )
    val model = entry.model.asInstanceOf[Formula]
    val Imply(_, Box(Loop(Compose(prg, _)), _)) = model

    val diffCuts =
      "(t>=0&(k*(eps()*eps())-2*100*eps())*(10*10) < k*(xg*xg+yg*yg)-2*xg*100*10&k*(xg*xg+yg*yg)-2*xg*100*10 < (k*(eps()*eps())+2*100*eps())*(10*10)|10*v+a*(T()-t)>=0&((a>=0&10*v+a*(T()-t)<=10*vh|a<=0&v<=vh)|(1*100*(1*100)+2*eps()*abs(k)*1*100+eps()*eps()*(k*k))*(B()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+((v*10+a*(T()-t))*(v*10+a*(T()-t))-10*vh*(10*vh)))<=2*B()*(yg-10*eps())*(100*100)*(10*10)|(1*100*(1*100)+2*eps()*abs(k)*1*100+eps()*eps()*(k*k))*(B()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+((v*10+a*(T()-t))*(v*10+a*(T()-t))-10*vh*(10*vh)))<=2*B()*(abs(xg)-10*eps())*(100*100)*(10*10))&((a>=0&v>=vl|a<=0&10*v+a*(T()-t)>=10*vl)|(1*100*(1*100)+2*eps()*abs(k)*1*100+eps()*eps()*(k*k))*(A()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+(vl*10*(vl*10)-(v*10+a*(T()-t))*(v*10+a*(T()-t))))<=2*A()*(yg-10*eps())*(100*100)*(10*10)|(1*100*(1*100)+2*eps()*abs(k)*1*100+eps()*eps()*(k*k))*(A()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+(vl*10*(vl*10)-(v*10+a*(T()-t))*(v*10+a*(T()-t))))<=2*A()*(abs(xg)-10*eps())*(100*100)*(10*10)))"
        .asFormula
    val expectedEvolutionDomain = And("v>=0&t<=T()".asFormula, diffCuts)

    val nonlinearModelApprox = ModelPlex
      .createNonlinearModelApprox("Waypoint", entry.tactics.head._3, entry.defs)(model)
    val Imply(
      init,
      Box(
        Loop(
          Compose(ctrl, plant @ Compose(x0Ghosts, Compose(Test(x0EvolDomain), Compose(nondetPlant, Test(evolDomain)))))
        ),
        safe,
      ),
    ) = nonlinearModelApprox._1
    ctrl shouldBe prg
    x0Ghosts shouldBe "t_0:=t;v_0:=v;xg_0:=xg;yg_0:=yg;".asProgram
    x0EvolDomain shouldBe expectedEvolutionDomain
    nondetPlant shouldBe "t:=*;v:=*;xg:=*;yg:=*;".asProgram
    evolDomain shouldBe expectedEvolutionDomain

    val modelMonitorStateVars = List("xg", "yg", "v", "a", "t", "vl", "vh", "k", "t_0", "v_0", "xg_0", "yg_0")
      .map(_.asVariable.asInstanceOf[BaseVariable])
    val ModelPlexConjecture(monitorInit, modelMonitorInput, assumptions) = ModelPlex
      .createMonitorSpecificationConjecture(nonlinearModelApprox._1, modelMonitorStateVars, ListMap.empty)
    val monitorTactic = DebuggingTactics
      .print("Deriving Monitor") & ModelPlex.controllerMonitorByChase(1) & DebuggingTactics.print("Chased") &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1) &
      DebuggingTactics.print("Monitor Result")

    /* Derive a model monitor (monitor controller + plant, use after plant/before controller) */
    val modelMonitorResult = proveBy(modelMonitorInput, monitorTactic)
    val modelMonitorFml = modelMonitorResult.subgoals.head.succ.head
    modelMonitorFml shouldBe
      "(ygpost_0>0&abs(kpost)*eps()<=100&((kpost*(eps()*eps())-200*eps())*100 < kpost*(xgpost_0*xgpost_0+ygpost_0*ygpost_0)-2*xgpost_0*100*10&kpost*(xgpost_0*xgpost_0+ygpost_0*ygpost_0)-2*xgpost_0*100*10 < (kpost*(eps()*eps())+200*eps())*100)&0<=vlpost&vlpost < vhpost&A()*T()<=10*(vhpost-vlpost)&B()*T()<=10*(vhpost-vlpost))&((-B()<=apost&apost<=A())&10*v+apost*T()>=0&(v<=vhpost&10*v+apost*T()<=10*vhpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(abs(xgpost_0)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(ygpost_0-10*eps())*10000*100)&(vlpost<=v&10*v+apost*T()>=10*vlpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(abs(xgpost_0)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(ygpost_0-10*eps())*10000*100))&(v>=0&0<=T())&((vpost>=0&tpost<=T())&(tpost>=0&(kpost*(eps()*eps())-200*eps())*100 < kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10&kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10 < (kpost*(eps()*eps())+200*eps())*100|10*vpost+apost*(T()-tpost)>=0&((apost>=0&10*vpost+apost*(T()-tpost)<=10*vhpost|apost<=0&vpost<=vhpost)|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*vpost*(T()-tpost)*10+apost*((T()-tpost)*(T()-tpost)))+((vpost*10+apost*(T()-tpost))*(vpost*10+apost*(T()-tpost))-10*vhpost*(10*vhpost)))<=2*B()*(ygpost-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*vpost*(T()-tpost)*10+apost*((T()-tpost)*(T()-tpost)))+((vpost*10+apost*(T()-tpost))*(vpost*10+apost*(T()-tpost))-10*vhpost*(10*vhpost)))<=2*B()*(abs(xgpost)-10*eps())*10000*100)&((apost>=0&vpost>=vlpost|apost<=0&10*vpost+apost*(T()-tpost)>=10*vlpost)|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*vpost*(T()-tpost)*10+apost*((T()-tpost)*(T()-tpost)))+(vlpost*10*(vlpost*10)-(vpost*10+apost*(T()-tpost))*(vpost*10+apost*(T()-tpost))))<=2*A()*(ygpost-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*vpost*(T()-tpost)*10+apost*((T()-tpost)*(T()-tpost)))+(vlpost*10*(vlpost*10)-(vpost*10+apost*(T()-tpost))*(vpost*10+apost*(T()-tpost))))<=2*A()*(abs(xgpost)-10*eps())*10000*100)))&tpost_0=0&vpost_0=v"
        .asFormula

    /* Derive a controller monitor (monitor only controller, use right after control decision) */
    val ctrlMonitorStateVars = List("xg", "yg", "v", "a", "t", "vl", "vh", "k")
      .map(_.asVariable.asInstanceOf[BaseVariable])
    val ModelPlexConjecture(_, ctrlMonitorInput, _) = ModelPlex
      .createMonitorSpecificationConjecture(Imply(init, Box(Loop(ctrl), safe)), ctrlMonitorStateVars, ListMap.empty)
    val ctrlMonitorResult = proveBy(ctrlMonitorInput, monitorTactic)
    val ctrlMonitorFml = ctrlMonitorResult.subgoals.head.succ.head
    ctrlMonitorFml shouldBe
      "(ygpost>0&abs(kpost)*eps()<=100&((kpost*(eps()*eps())-200*eps())*100 < kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10&kpost*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10 < (kpost*(eps()*eps())+200*eps())*100)&0<=vlpost&vlpost < vhpost&A()*T()<=10*(vhpost-vlpost)&B()*T()<=10*(vhpost-vlpost))&((-B()<=apost&apost<=A())&10*v+apost*T()>=0&(v<=vhpost&10*v+apost*T()<=10*vhpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(abs(xgpost)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(B()*(2*v*T()*10+apost*(T()*T()))+((v*10+apost*T())*(v*10+apost*T())-10*vhpost*(10*vhpost)))<=2*B()*(ygpost-10*eps())*10000*100)&(vlpost<=v&10*v+apost*T()>=10*vlpost|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(abs(xgpost)-10*eps())*10000*100|(10000+2*eps()*abs(kpost)*100+eps()*eps()*(kpost*kpost))*(A()*(2*v*T()*10+apost*(T()*T()))+(vlpost*10*(vlpost*10)-(v*10+apost*T())*(v*10+apost*T())))<=2*A()*(ygpost-10*eps())*10000*100))&vpost=v&tpost=0"
        .asFormula

    /* Derive a plant monitor (monitor only physics, use right after plant/before controller) */
    val plantMonitorStateVars = List("xg", "yg", "v", "t", "t_0", "v_0", "xg_0", "yg_0")
      .map(_.asVariable.asInstanceOf[BaseVariable])
    val ModelPlexConjecture(_, plantMonitorInput, _) = ModelPlex
      .createMonitorSpecificationConjecture(Imply(init, Box(Loop(plant), safe)), plantMonitorStateVars, ListMap.empty)
    val plantMonitorResult = proveBy(plantMonitorInput, monitorTactic)
    val plantMonitorFml = plantMonitorResult.subgoals.head.succ.head
    plantMonitorFml shouldBe
      "((v>=0&t<=T())&(t>=0&(k*(eps()*eps())-200*eps())*100 < k*(xg*xg+yg*yg)-2*xg*100*10&k*(xg*xg+yg*yg)-2*xg*100*10 < (k*(eps()*eps())+200*eps())*100|10*v+a*(T()-t)>=0&((a>=0&10*v+a*(T()-t)<=10*vh|a<=0&v<=vh)|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(B()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+((v*10+a*(T()-t))*(v*10+a*(T()-t))-10*vh*(10*vh)))<=2*B()*(yg-10*eps())*10000*100|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(B()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+((v*10+a*(T()-t))*(v*10+a*(T()-t))-10*vh*(10*vh)))<=2*B()*(abs(xg)-10*eps())*10000*100)&((a>=0&v>=vl|a<=0&10*v+a*(T()-t)>=10*vl)|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(A()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+(vl*10*(vl*10)-(v*10+a*(T()-t))*(v*10+a*(T()-t))))<=2*A()*(yg-10*eps())*10000*100|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(A()*(2*v*(T()-t)*10+a*((T()-t)*(T()-t)))+(vl*10*(vl*10)-(v*10+a*(T()-t))*(v*10+a*(T()-t))))<=2*A()*(abs(xg)-10*eps())*10000*100)))&((vpost>=0&tpost<=T())&(tpost>=0&(k*(eps()*eps())-200*eps())*100 < k*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10&k*(xgpost*xgpost+ygpost*ygpost)-2*xgpost*100*10 < (k*(eps()*eps())+200*eps())*100|10*vpost+a*(T()-tpost)>=0&((a>=0&10*vpost+a*(T()-tpost)<=10*vh|a<=0&vpost<=vh)|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(B()*(2*vpost*(T()-tpost)*10+a*((T()-tpost)*(T()-tpost)))+((vpost*10+a*(T()-tpost))*(vpost*10+a*(T()-tpost))-10*vh*(10*vh)))<=2*B()*(ygpost-10*eps())*10000*100|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(B()*(2*vpost*(T()-tpost)*10+a*((T()-tpost)*(T()-tpost)))+((vpost*10+a*(T()-tpost))*(vpost*10+a*(T()-tpost))-10*vh*(10*vh)))<=2*B()*(abs(xgpost)-10*eps())*10000*100)&((a>=0&vpost>=vl|a<=0&10*vpost+a*(T()-tpost)>=10*vl)|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(A()*(2*vpost*(T()-tpost)*10+a*((T()-tpost)*(T()-tpost)))+(vl*10*(vl*10)-(vpost*10+a*(T()-tpost))*(vpost*10+a*(T()-tpost))))<=2*A()*(ygpost-10*eps())*10000*100|(10000+2*eps()*abs(k)*100+eps()*eps()*(k*k))*(A()*(2*vpost*(T()-tpost)*10+a*((T()-tpost)*(T()-tpost)))+(vl*10*(vl*10)-(vpost*10+a*(T()-tpost))*(vpost*10+a*(T()-tpost))))<=2*A()*(abs(xgpost)-10*eps())*10000*100)))&tpost_0=t&vpost_0=v&xgpost_0=xg&ygpost_0=yg"
        .asFormula

    /* Generate C code for controller monitor */
    val reassociatedCtrlMonitorFml = FormulaTools.reassociate(ctrlMonitorFml)
    proveBy(Equiv(ctrlMonitorFml, reassociatedCtrlMonitorFml), TactixLibrary.prop) shouldBe Symbol("proved")
    val ctrlMonitorProg =
      proveBy(reassociatedCtrlMonitorFml, ModelPlex.chaseToTests(combineTests = false)(1) * 2).subgoals.head.succ.head
    val ctrlInputs = CodeGenerator.getInputs(ctrlMonitorProg)
    val ctrlMonitorCode = (
      new CGenerator(new CMonitorGenerator(Symbol("resist"), entry.defs), monitorInit, entry.defs)
    )(ctrlMonitorProg, ctrlMonitorStateVars.toSet, ctrlInputs, "Monitor")
    // @todo update expected code
    ctrlMonitorCode._1.trim shouldBe
      "/**************************\n * Monitor.c\n * Generated by KeYmaera X\n **************************/\n\n#include <math.h>\n#include <stdbool.h>\n\ntypedef struct parameters {\n  long double A;\n  long double B;\n  long double T;\n  long double eps;\n} parameters;\n\ntypedef struct state {\n  long double a;\n  long double k;\n  long double t;\n  long double v;\n  long double vh;\n  long double vl;\n  long double xg;\n  long double yg;\n} state;\n\ntypedef struct input input;\n\ntypedef struct verdict { int id; long double val; } verdict;"
    ctrlMonitorCode._2.trim shouldBe
      "/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */\nverdict boundaryDist(state pre, state curr, const parameters* const params) {\n  if (curr.yg > 0.0L) {\nif ((fabsl(curr.k))*(params->eps) <= 100.0L) {\nif ((((curr.k)*((params->eps)*(params->eps)))-((200.0L)*(params->eps)))*(100.0L) < ((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))) {\nif (((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)) < (((curr.k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)) {\nif (0.0L <= curr.vl) {\nif (curr.vl < curr.vh) {\nif ((params->A)*(params->T) <= (10.0L)*((curr.vh)-(curr.vl))) {\nif ((params->B)*(params->T) <= (10.0L)*((curr.vh)-(curr.vl))) {\nif (-(params->B) <= curr.a) {\nif (curr.a <= params->A) {\nif (((10.0L)*(pre.v))+((curr.a)*(params->T)) >= 0.0L) {\nif (((pre.v <= curr.vh) && (((10.0L)*(pre.v))+((curr.a)*(params->T)) <= (10.0L)*(curr.vh))) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh))))) <= ((((2.0L)*(params->B))*((fabsl(curr.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh))))) <= ((((2.0L)*(params->B))*((curr.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)))) {\nif (((curr.vl <= pre.v) && (((10.0L)*(pre.v))+((curr.a)*(params->T)) >= (10.0L)*(curr.vl))) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T)))))) <= ((((2.0L)*(params->A))*((fabsl(curr.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T)))))) <= ((((2.0L)*(params->A))*((curr.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)))) {\nif (curr.v == pre.v) {\nif (curr.t == 0.0L) {\nverdict result = { .id=1, .val=(((((((((((((0.0L)+(-((0.0L)-(curr.yg))))+(-(((fabsl(curr.k))*(params->eps))-(100.0L))))+(-(((((curr.k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)))))))+(-((((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))))-((((curr.k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))))+(-((0.0L)-(curr.vl))))+(-((curr.vl)-(curr.vh))))+(-(((params->A)*(params->T))-((10.0L)*((curr.vh)+(-(curr.vl)))))))+(-(((params->B)*(params->T))-((10.0L)*((curr.vh)+(-(curr.vl)))))))+(-((-(params->B))-(curr.a))))+(-((curr.a)-(params->A))))+(-((0.0L)-(((10.0L)*(pre.v))+((curr.a)*(params->T))))))+(-(fminl(fmaxl((pre.v)-(curr.vh), (((10.0L)*(pre.v))+((curr.a)*(params->T)))-((10.0L)*(curr.vh))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))+(-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh)))))))-(((((2.0L)*(params->B))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))+(-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh)))))))-(((((2.0L)*(params->B))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))+(-(fminl(fmaxl((curr.vl)-(pre.v), ((10.0L)*(curr.vl))-(((10.0L)*(pre.v))+((curr.a)*(params->T)))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))))))-(((((2.0L)*(params->A))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))))))-(((((2.0L)*(params->A))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-3, .val=((-1.0L))+(-(fminl(fmaxl((curr.vl)-(pre.v), ((10.0L)*(curr.vl))-(((10.0L)*(pre.v))+((curr.a)*(params->T)))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))))))-(((((2.0L)*(params->A))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->A)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+((((curr.vl)*(10.0L))*((curr.vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))))))-(((((2.0L)*(params->A))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))) }; return result;\n}\n} else {\nverdict result = { .id=-4, .val=((-1.0L))+(-(fminl(fmaxl((pre.v)-(curr.vh), (((10.0L)*(pre.v))+((curr.a)*(params->T)))-((10.0L)*(curr.vh))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))+(-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh)))))))-(((((2.0L)*(params->B))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(curr.k)))*(100.0L)))+(((params->eps)*(params->eps))*((curr.k)*(curr.k))))*(((params->B)*(((((2.0L)*(pre.v))*(params->T))*(10.0L))+((curr.a)*((params->T)*(params->T)))))+(((((pre.v)*(10.0L))+((curr.a)*(params->T)))*(((pre.v)*(10.0L))+((curr.a)*(params->T))))+(-(((10.0L)*(curr.vh))*((10.0L)*(curr.vh)))))))-(((((2.0L)*(params->B))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))) }; return result;\n}\n} else {\nverdict result = { .id=-5, .val=((-1.0L))+(-((0.0L)-(((10.0L)*(pre.v))+((curr.a)*(params->T))))) }; return result;\n}\n} else {\nverdict result = { .id=-6, .val=((-1.0L))+(-((curr.a)-(params->A))) }; return result;\n}\n} else {\nverdict result = { .id=-7, .val=((-1.0L))+(-((-(params->B))-(curr.a))) }; return result;\n}\n} else {\nverdict result = { .id=-8, .val=((-1.0L))+(-(((params->B)*(params->T))-((10.0L)*((curr.vh)+(-(curr.vl)))))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-(((params->A)*(params->T))-((10.0L)*((curr.vh)+(-(curr.vl)))))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-((curr.vl)-(curr.vh))) }; return result;\n}\n} else {\nverdict result = { .id=-11, .val=((-1.0L))+(-((0.0L)-(curr.vl))) }; return result;\n}\n} else {\nverdict result = { .id=-12, .val=((-1.0L))+(-((((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))))-((((curr.k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))) }; return result;\n}\n} else {\nverdict result = { .id=-13, .val=((-1.0L))+(-(((((curr.k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((curr.k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)))))) }; return result;\n}\n} else {\nverdict result = { .id=-14, .val=((-1.0L))+(-(((fabsl(curr.k))*(params->eps))-(100.0L))) }; return result;\n}\n} else {\nverdict result = { .id=-15, .val=((-1.0L))+(-((0.0L)-(curr.yg))) }; return result;\n};\n}\n\n/* Evaluates monitor condition in prior and current state */\nbool monitorSatisfied(state pre, state curr, const parameters* const params) {\n  return boundaryDist(pre,curr,params).val >= 0.0L;\n}\n\n/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */\nstate monitoredCtrl(state curr, const parameters* const params, const input* const in,\n                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const)) {\n  state pre = curr;\n  state post = (*ctrl)(pre,params,in);\n  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);\n  else return post;\n}"

    /* Generate C code for plant monitor */
    val reassociatedPlantMonitorFml = FormulaTools.reassociate(plantMonitorFml)
    proveBy(Equiv(plantMonitorFml, reassociatedPlantMonitorFml), TactixLibrary.prop) shouldBe Symbol("proved")
    val plantMonitorProg =
      proveBy(reassociatedPlantMonitorFml, ModelPlex.chaseToTests(combineTests = false)(1) * 2).subgoals.head.succ.head
    val plantInputs = CodeGenerator.getInputs(plantMonitorProg)
    val plantMonitorCode = (
      new CGenerator(new CMonitorGenerator(Symbol("resist"), entry.defs), monitorInit, entry.defs)
    )(plantMonitorProg, plantMonitorStateVars.toSet, plantInputs, "Monitor")
    // @todo update expected code
    plantMonitorCode._1.trim shouldBe
      "/**************************\n * Monitor.c\n * Generated by KeYmaera X\n **************************/\n\n#include <math.h>\n#include <stdbool.h>\n\ntypedef struct parameters {\n  long double A;\n  long double B;\n  long double T;\n  long double a;\n  long double eps;\n  long double k;\n  long double vh;\n  long double vl;\n} parameters;\n\ntypedef struct state {\n  long double t;\n  long double t_0;\n  long double v;\n  long double v_0;\n  long double xg;\n  long double xg_0;\n  long double yg;\n  long double yg_0;\n} state;\n\ntypedef struct input input;\n\ntypedef struct verdict { int id; long double val; } verdict;"
    plantMonitorCode._2.trim shouldBe
      "/* Computes distance to safety boundary on prior and current state (>=0 is safe, <0 is unsafe) */\nverdict boundaryDist(state pre, state curr, const parameters* const params) {\n  if (pre.v >= 0.0L) {\nif (pre.t <= params->T) {\nif (((pre.t >= 0.0L) && (((((params->k)*((params->eps)*(params->eps)))-((200.0L)*(params->eps)))*(100.0L) < ((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))-((((2.0L)*(pre.xg))*(100.0L))*(10.0L))) && (((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))-((((2.0L)*(pre.xg))*(100.0L))*(10.0L)) < (((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))) || ((((10.0L)*(pre.v))+((params->a)*((params->T)-(pre.t))) >= 0.0L) && ((((params->a >= 0.0L) && (((10.0L)*(pre.v))+((params->a)*((params->T)-(pre.t))) <= (10.0L)*(params->vh))) || (((params->a <= 0.0L) && (pre.v <= params->vh)) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)-(pre.t)))*(10.0L))+((params->a)*(((params->T)-(pre.t))*((params->T)-(pre.t))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))*(((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t)))))-(((10.0L)*(params->vh))*((10.0L)*(params->vh))))) <= ((((2.0L)*(params->B))*((pre.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)-(pre.t)))*(10.0L))+((params->a)*(((params->T)-(pre.t))*((params->T)-(pre.t))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))*(((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t)))))-(((10.0L)*(params->vh))*((10.0L)*(params->vh))))) <= ((((2.0L)*(params->B))*((fabsl(pre.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L))))) && (((params->a >= 0.0L) && (pre.v >= params->vl)) || (((params->a <= 0.0L) && (((10.0L)*(pre.v))+((params->a)*((params->T)-(pre.t))) >= (10.0L)*(params->vl))) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)-(pre.t)))*(10.0L))+((params->a)*(((params->T)-(pre.t))*((params->T)-(pre.t))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))-((((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))*(((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))))) <= ((((2.0L)*(params->A))*((pre.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)-(pre.t)))*(10.0L))+((params->a)*(((params->T)-(pre.t))*((params->T)-(pre.t))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))-((((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))*(((pre.v)*(10.0L))+((params->a)*((params->T)-(pre.t))))))) <= ((((2.0L)*(params->A))*((fabsl(pre.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)))))))) {\nif (curr.v >= 0.0L) {\nif (curr.t <= params->T) {\nif (((curr.t >= 0.0L) && (((((params->k)*((params->eps)*(params->eps)))-((200.0L)*(params->eps)))*(100.0L) < ((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))) && (((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)) < (((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))) || ((((10.0L)*(curr.v))+((params->a)*((params->T)-(curr.t))) >= 0.0L) && ((((params->a >= 0.0L) && (((10.0L)*(curr.v))+((params->a)*((params->T)-(curr.t))) <= (10.0L)*(params->vh))) || (((params->a <= 0.0L) && (curr.v <= params->vh)) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)-(curr.t)))*(10.0L))+((params->a)*(((params->T)-(curr.t))*((params->T)-(curr.t))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))*(((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t)))))-(((10.0L)*(params->vh))*((10.0L)*(params->vh))))) <= ((((2.0L)*(params->B))*((curr.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)-(curr.t)))*(10.0L))+((params->a)*(((params->T)-(curr.t))*((params->T)-(curr.t))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))*(((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t)))))-(((10.0L)*(params->vh))*((10.0L)*(params->vh))))) <= ((((2.0L)*(params->B))*((fabsl(curr.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L))))) && (((params->a >= 0.0L) && (curr.v >= params->vl)) || (((params->a <= 0.0L) && (((10.0L)*(curr.v))+((params->a)*((params->T)-(curr.t))) >= (10.0L)*(params->vl))) || (((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)-(curr.t)))*(10.0L))+((params->a)*(((params->T)-(curr.t))*((params->T)-(curr.t))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))-((((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))*(((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))))) <= ((((2.0L)*(params->A))*((curr.yg)-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)) || ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)-(curr.t)))*(10.0L))+((params->a)*(((params->T)-(curr.t))*((params->T)-(curr.t))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))-((((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))*(((curr.v)*(10.0L))+((params->a)*((params->T)-(curr.t))))))) <= ((((2.0L)*(params->A))*((fabsl(curr.xg))-((10.0L)*(params->eps))))*(10000.0L))*(100.0L)))))))) {\nif (curr.t_0 == pre.t) {\nif (curr.v_0 == pre.v) {\nif (curr.xg_0 == pre.xg) {\nif (curr.yg_0 == pre.yg) {\nverdict result = { .id=1, .val=((((((0.0L)+(-((0.0L)-(pre.v))))+(-((pre.t)-(params->T))))+(-(fminl(fmaxl((0.0L)-(pre.t), fmaxl(((((params->k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))+(-((((2.0L)*(pre.xg))*(100.0L))*(10.0L)))), (((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))+(-((((2.0L)*(pre.xg))*(100.0L))*(10.0L))))-((((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))), fmaxl((0.0L)-(((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t))))), fmaxl(fminl(fmaxl((0.0L)-(params->a), (((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t)))))-((10.0L)*(params->vh))), fminl(fmaxl(params->a, (pre.v)-(params->vh)), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((pre.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((fabsl(pre.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L))))), fminl(fmaxl((0.0L)-(params->a), (params->vl)-(pre.v)), fminl(fmaxl(params->a, ((10.0L)*(params->vl))-(((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t)))))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))))))-(((((2.0L)*(params->A))*((pre.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))))))-(((((2.0L)*(params->A))*((fabsl(pre.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))))))+(-((0.0L)-(curr.v))))+(-((curr.t)-(params->T))))+(-(fminl(fmaxl((0.0L)-(curr.t), fmaxl(((((params->k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)))), (((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))))-((((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))), fmaxl((0.0L)-(((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t))))), fmaxl(fminl(fmaxl((0.0L)-(params->a), (((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t)))))-((10.0L)*(params->vh))), fminl(fmaxl(params->a, (curr.v)-(params->vh)), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L))))), fminl(fmaxl((0.0L)-(params->a), (params->vl)-(curr.v)), fminl(fmaxl(params->a, ((10.0L)*(params->vl))-(((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t)))))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))))))-(((((2.0L)*(params->A))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))))))-(((((2.0L)*(params->A))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))))) }; return result;\n} else {\nverdict result = { .id=-1, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-2, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-3, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-4, .val=-1.0L }; return result;\n}\n} else {\nverdict result = { .id=-5, .val=((-1.0L))+(-(fminl(fmaxl((0.0L)-(curr.t), fmaxl(((((params->k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L)))), (((params->k)*(((curr.xg)*(curr.xg))+((curr.yg)*(curr.yg))))+(-((((2.0L)*(curr.xg))*(100.0L))*(10.0L))))-((((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))), fmaxl((0.0L)-(((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t))))), fmaxl(fminl(fmaxl((0.0L)-(params->a), (((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t)))))-((10.0L)*(params->vh))), fminl(fmaxl(params->a, (curr.v)-(params->vh)), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+(((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L))))), fminl(fmaxl((0.0L)-(params->a), (params->vl)-(curr.v)), fminl(fmaxl(params->a, ((10.0L)*(params->vl))-(((10.0L)*(curr.v))+((params->a)*((params->T)+(-(curr.t)))))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))))))-(((((2.0L)*(params->A))*((curr.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(curr.v))*((params->T)+(-(curr.t))))*(10.0L))+((params->a)*(((params->T)+(-(curr.t)))*((params->T)+(-(curr.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t)))))*(((curr.v)*(10.0L))+((params->a)*((params->T)+(-(curr.t))))))))))-(((((2.0L)*(params->A))*((fabsl(curr.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))))) }; return result;\n}\n} else {\nverdict result = { .id=-6, .val=((-1.0L))+(-((curr.t)-(params->T))) }; return result;\n}\n} else {\nverdict result = { .id=-7, .val=((-1.0L))+(-((0.0L)-(curr.v))) }; return result;\n}\n} else {\nverdict result = { .id=-8, .val=((-1.0L))+(-(fminl(fmaxl((0.0L)-(pre.t), fmaxl(((((params->k)*((params->eps)*(params->eps)))+(-((200.0L)*(params->eps))))*(100.0L))-(((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))+(-((((2.0L)*(pre.xg))*(100.0L))*(10.0L)))), (((params->k)*(((pre.xg)*(pre.xg))+((pre.yg)*(pre.yg))))+(-((((2.0L)*(pre.xg))*(100.0L))*(10.0L))))-((((params->k)*((params->eps)*(params->eps)))+((200.0L)*(params->eps)))*(100.0L)))), fmaxl((0.0L)-(((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t))))), fmaxl(fminl(fmaxl((0.0L)-(params->a), (((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t)))))-((10.0L)*(params->vh))), fminl(fmaxl(params->a, (pre.v)-(params->vh)), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((pre.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->B)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+(((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))+(-(((10.0L)*(params->vh))*((10.0L)*(params->vh)))))))-(((((2.0L)*(params->B))*((fabsl(pre.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L))))), fminl(fmaxl((0.0L)-(params->a), (params->vl)-(pre.v)), fminl(fmaxl(params->a, ((10.0L)*(params->vl))-(((10.0L)*(pre.v))+((params->a)*((params->T)+(-(pre.t)))))), fminl(((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))))))-(((((2.0L)*(params->A))*((pre.yg)+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)), ((((10000.0L)+((((2.0L)*(params->eps))*(fabsl(params->k)))*(100.0L)))+(((params->eps)*(params->eps))*((params->k)*(params->k))))*(((params->A)*(((((2.0L)*(pre.v))*((params->T)+(-(pre.t))))*(10.0L))+((params->a)*(((params->T)+(-(pre.t)))*((params->T)+(-(pre.t)))))))+((((params->vl)*(10.0L))*((params->vl)*(10.0L)))+(-((((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t)))))*(((pre.v)*(10.0L))+((params->a)*((params->T)+(-(pre.t))))))))))-(((((2.0L)*(params->A))*((fabsl(pre.xg))+(-((10.0L)*(params->eps)))))*(10000.0L))*(100.0L)))))))))) }; return result;\n}\n} else {\nverdict result = { .id=-9, .val=((-1.0L))+(-((pre.t)-(params->T))) }; return result;\n}\n} else {\nverdict result = { .id=-10, .val=((-1.0L))+(-((0.0L)-(pre.v))) }; return result;\n};\n}\n\n/* Evaluates monitor condition in prior and current state */\nbool monitorSatisfied(state pre, state curr, const parameters* const params) {\n  return boundaryDist(pre,curr,params).val >= 0.0L;\n}\n\n/* Run controller `ctrl` monitored, return `fallback` if `ctrl` violates monitor */\nstate monitoredCtrl(state curr, const parameters* const params, const input* const in,\n                    state (*ctrl)(state,const parameters* const,const input* const), state (*fallback)(state,const parameters* const,const input* const)) {\n  state pre = curr;\n  state post = (*ctrl)(pre,params,in);\n  if (!monitorSatisfied(pre,post,params)) return (*fallback)(pre,params,in);\n  else return post;\n}"
  }

  "RSSRail" should "generate a controller monitor" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/keymaerax-projects/rssrail17/rssrail.kyx")
    val entry = ArchiveParser
      .parse(io.Source.fromInputStream(in).mkString)
      .find(_.name == "RSSRail17/Theorem 2: Train Controller with Brake Pressure Propagation is Safe")
      .head
    val model = entry.expandedModel.asInstanceOf[Formula]

    val stateVars = List("acc", "d", "jpb", "m", "st", "t", "v", "z").map(_.asVariable.asInstanceOf[BaseVariable])
    val ModelPlexConjecture(init, modelplexInput, assumptions) = ModelPlex
      .createMonitorSpecificationConjecture(model, stateVars, ListMap.empty)
    val ctrlTactic = DebuggingTactics
      .print("Deriving Ctrl Monitor") & ModelPlex.controllerMonitorByChase(1) & DebuggingTactics.print("Chased") &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1) &
      DebuggingTactics.print("Ctrl Monitor Result")
    val ctrlResult = proveBy(modelplexInput, ctrlTactic)
    val ctrlMonitorFml = ctrlResult.subgoals.head.succ.head
    ctrlMonitorFml shouldBe
      "(dpost>=0&v^2-dpost^2<=2*Fsb()/mt()*(mpost-z))&accpost=acc&jpbpost=jpb&stpost=st&tpost=t&vpost=v&zpost=z|(-Fsb()<=accpost&accpost<=Amax())&(d>=0&m-z>=(v^2-d^2)/(2*Fsb()/mt())+(Amax()/Fsb()+1)*(Amax()/(2*mt())*ep()^2+v*ep())|d<=0&(accpost<=0&v-d>=Fpb()^2/(2*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))&m-z>=v*ep()+(mt()*v^2/(2*Fpb())+Fpb()*v/(2*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))-Fpb()^3/(24*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2))^2))|accpost>=0&v-d>=Fpb()^2/(2*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))&m-z>=v*ep()+accpost/(2*mt())*ep()^2+(mt()*(v+accpost/mt()*ep())^2/(2*Fpb())+Fpb()*(v+accpost/mt()*ep())/(2*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))-Fpb()^3/(24*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2))^2))|accpost<=0&v-d<=Fpb()^2/(2*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))&m-z>=v*ep()+2/3*v*(2*mt()*v/(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))^(1/2)|accpost>=0&v+accpost/mt()*ep()-d<=Fpb()^2/(2*mt()*(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))&m-z>=v*ep()+accpost/(2*mt())*ep()^2+2/3*(v+accpost/mt()*ep())*(2*mt()*(v+accpost/mt()*ep())/(Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)))^(1/2)))&(v>=0&0<=ep()&-Fpb()<=accpost)&dpost=d&jpbpost=0&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z|m-z>=(v^2-d^2)/(2*Fsb()/mt())&(v>=0&0<=ep()&-Fpb()<=-Fsb())&accpost=-Fsb()&dpost=d&jpbpost=jpb&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z|m-z < (v^2-d^2)/(2*Fsb()/mt())&(v<=d&(-Fsb()<=accpost&accpost<=0)&(v>=0&0<=ep()&-Fpb()<=accpost)&dpost=d&jpbpost=0&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z|v>d&(acc<=-Fpb()&(v>=0&0<=ep()&-Fpb()<=acc)&accpost=acc&dpost=d&jpbpost=0&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z|acc>-Fpb()&(v>=0&0<=ep()&-Fpb()<=min(acc,0))&accpost=min(acc,0)&dpost=d&jpbpost=-Fpb()/(cappl1()+cappl2()*L()-cappl3()*L()^2)&mpost=m&stpost=0&tpost=0&vpost=v&zpost=z))"
        .asFormula

    /* Generate C code for controller monitor */
    CPrettyPrinter.printer = new CExpressionPlainPrettyPrinter(printDebugOut = false)
    val reassociatedCtrlMonitorFml = FormulaTools.reassociate(ctrlMonitorFml)
    // proveBy(Equiv(ctrlMonitorFml, reassociatedCtrlMonitorFml), TactixLibrary.prop) shouldBe 'proved
    val ctrlMonitorProg =
      proveBy(reassociatedCtrlMonitorFml, ModelPlex.chaseToTests(combineTests = false)(1) * 2).subgoals.head.succ.head
    val ctrlInputs = CodeGenerator.getInputs(ctrlMonitorProg)
    val ctrlMonitorCode = (
      new CGenerator(new CMonitorGenerator(Symbol("resist"), entry.defs), init, entry.defs)
    )(ctrlMonitorProg, stateVars.toSet, ctrlInputs, "Monitor")
    println(ctrlMonitorCode)
  }

  "ModelPlex formula metric" should "convert simple formula" in withMathematica { _ =>
    val fml = "x>=y & a=b & c<=d+e".asFormula
    ModelPlex.toMetric(fml) shouldBe "max(y-x,max(max(a-b,b-a),c-(d+e)))<=0".asFormula
  }

  it should "convert formulas with function symbols" in withMathematica { _ =>
    val fml = "x()>=y & a=b & c<=d+e(f(),g())".asFormula
    ModelPlex.toMetric(fml) shouldBe "max(y-x(),max(max(a-b,b-a),c-(d+e(f(),g()))))<=0".asFormula
  }

  it should "convert simple formula 2" in withMathematica { _ =>
    val fml = "x>=y&a=b | c<=d+e".asFormula
    ModelPlex.toMetric(fml) shouldBe "min(max(y-x,max(a-b,b-a)),c-(d+e))<=0".asFormula
  }

  it should "convert simple formula 3" in withMathematica { tool =>
    val fml = "x>=y&a=b&c<=d | c<=d+e | f<=g&h<=0".asFormula
    val metric = ModelPlex.toMetric(fml)
    metric shouldBe "min(max(y-x,max(max(a-b,b-a),c-d)),min(c-(d+e),max(f-g,h)))<=0".asFormula
    tool.findCounterExample(metric)
  }

  it should "convert simple formula 4" in withMathematica { tool =>
    val fml = "xpost>=x+5&ypost=y&cpost<=d | cpost>=d+e | fpost<=f&hpost<=0".asFormula
    val metric = ModelPlex.toMetric(fml)
    metric shouldBe
      "min(max(x+5-xpost,max(max(ypost-y,y-ypost),cpost-d)),min(d+e-cpost,max(fpost-f,hpost)))<=0".asFormula
    tool.findCounterExample(metric)
  }

  it should "convert inequalities" in withMathematica { _ =>
    val fml = "x!=y | x>4&y!=3".asFormula
    ModelPlex.toMetric(fml) shouldBe "min(min(y-x,x-y),max(4-x,min(3-y,y-3))) < 0".asFormula
  }

  it should "convert mixed open/closed formula" in withMathematica { _ =>
    val fml = "x>=y & a<b".asFormula
    ModelPlex.toMetric(fml) shouldBe "max(y-x,a-b) < 0".asFormula
  }

  it should "convert disjunctions of mixed open/closed formula" in withMathematica { _ =>
    val fml = "x<5 & y>=2 | x>=y & a<b".asFormula
    ModelPlex.toMetric(fml) shouldBe "min(max(x-5,2-y),max(y-x,a-b)) < 0".asFormula
  }

  it should "convert disjunction of mixed open/closed formula" in withMathematica { _ =>
    val fml = "x<=5 | x>=y & a<b".asFormula
    // @todo metric evaluates to false at the boundary, when x=5 and y>5
    ModelPlex.toMetric(fml) shouldBe "min(x-5,max(y-x,a-b)) < 0".asFormula
  }

  "Opt. 1" should "refuse to apply forall simplification when right-hand side is bound" in withMathematica { tool =>
    proveBy(
      """==> \forall x1_0 (x1_0=x1 -> x1_0>=0 & \exists x1 (x1>=2 & x1=x1 & x1_0=x1_0))""".asSequent,
      ModelPlex.optimizationOneWithSearch(Some(tool), Nil, "x1".asVariable :: Nil, Some(ModelPlex.mxSimplify))(1),
    ).subgoals.loneElement shouldBe """==> \forall x1_0 (x1_0=x1->x1_0>=0&\exists x1 x1>=2)""".asSequent
  }

  "Reassociating formulas" should "be fast" taggedAs IgnoreInBuildTest in withTactics {
    // run with -da -Xss20M
    val predicates = (0 to 1000).map(i => PredOf(Function("p", Some(i), Unit, Bool), Nothing))
    val p = predicates.reduceLeft(Or)
    val tic = System.currentTimeMillis()
    val (q, proof) = PropositionalTactics.rightAssociate(p)
    val toc = System.currentTimeMillis()
    proof shouldBe Symbol("proved")
    q shouldBe predicates.reduceRight(Or)
    (toc - tic) should be <= 60000L
  }

  it should "be fast on a robot example" taggedAs IgnoreInBuildTest in withTactics {
    // run with -da -Xss20M
    val p =
      "((v=vpost&(A()=0&(v < 0&xpost < x|v>0&xpost>x)|x=xpost&v!=0)|v=0&(2*A()+vpost^2*(x+-xpost)^(-1)=0&(vpost < 0&xpost < x|vpost>0&xpost>x)|vpost=0&x=xpost))|A()=(v^2+-vpost^2)*(2*x+(-2)*xpost)^(-1)&(v < 0&(xpost < x&(v < vpost&v+vpost < 0|vpost < v)|v+vpost>0&xpost>x)|v>0&(xpost>x&(v+vpost>0&vpost < v|vpost>v)|v+vpost < 0&xpost < x)))|(v+vpost=0&x=xpost)&(v>0&A() < 0|A()>0&v < 0)"
        .asFormula
    val tic = System.currentTimeMillis()
    val (q, proof) = PropositionalTactics.rightAssociate(p)
    val toc = System.currentTimeMillis()
    proof shouldBe Symbol("proved")
    q shouldBe
      "v=vpost&(A()=0&(v < 0&xpost < x|v>0&xpost>x)|x=xpost&v!=0)|v=0&(2*A()+vpost^2*(x+-xpost)^(-1)=0&(vpost < 0&xpost < x|vpost>0&xpost>x)|vpost=0&x=xpost)|A()=(v^2+-vpost^2)*(2*x+(-2)*xpost)^(-1)&(v < 0&(xpost < x&(v < vpost&v+vpost < 0|vpost < v)|v+vpost>0&xpost>x)|v>0&(xpost>x&(v+vpost>0&vpost < v|vpost>v)|v+vpost < 0&xpost < x))|v+vpost=0&x=xpost&(v>0&A() < 0|A()>0&v < 0)"
        .asFormula
    (toc - tic) should be <= 1000L
  }

  "Disjunctive normal form" should "be fast on a robot example" taggedAs IgnoreInBuildTest in withTactics {
    // run with -da -Xss20M
    val fml =
      "(((((((((xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2=0&2*w*xo+Da*xo^2+(-2)*w*xr+(-2)*Da*xo*xr+Da*xr^2+(-2)*v*yo+Da*yo^2+2*v*yr+(-2)*Da*yo*yr+Da*yr^2!=0|Da<=0&xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2=0)|(w*xo+(-1)*w*xr+(-1)*v*yo+v*yr<=0&xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2 < 0)&2*w*xo+Da*xo^2+(-2)*w*xr+(-2)*Da*xo*xr+Da*xr^2+(-2)*v*yo+Da*yo^2+2*v*yr+(-2)*Da*yo*yr+Da*yr^2!=0)|xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2 < 0&(-2)*w*xo+(-1)*Da*xo^2+2*w*xr+2*Da*xo*xr+(-1)*Da*xr^2+2*v*yo+(-1)*Da*yo^2+(-2)*v*yr+2*Da*yo*yr+(-1)*Da*yr^2 < 0)|(-1)*xo^2+2*xo*xr+(-1)*xr^2+(-1)*yo^2+2*yo*yr+(-1)*yr^2 < 0&2*w*xo+Da*xo^2+(-2)*w*xr+(-2)*Da*xo*xr+Da*xr^2+(-2)*v*yo+Da*yo^2+2*v*yr+(-2)*Da*yo*yr+Da*yr^2 < 0)|((-1)*w*xo+w*xr+v*yo+(-1)*v*yr<=0&(-1)*xo^2+2*xo*xr+(-1)*xr^2+(-1)*yo^2+2*yo*yr+(-1)*yr^2 < 0)&2*w*xo+Da*xo^2+(-2)*w*xr+(-2)*Da*xo*xr+Da*xr^2+(-2)*v*yo+Da*yo^2+2*v*yr+(-2)*Da*yo*yr+Da*yr^2!=0)|(Da<=0&w*xo+(-1)*w*xr+(-1)*v*yo+v*yr<=0)&xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2 < 0)|(Da<=0&xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2 < 0)&(-2)*w*xo+(-1)*Da*xo^2+2*w*xr+2*Da*xo*xr+(-1)*Da*xr^2+2*v*yo+(-1)*Da*yo^2+(-2)*v*yr+2*Da*yo*yr+(-1)*Da*yr^2 < 0)|(Da<=0&(-1)*xo^2+2*xo*xr+(-1)*xr^2+(-1)*yo^2+2*yo*yr+(-1)*yr^2 < 0)&2*w*xo+Da*xo^2+(-2)*w*xr+(-2)*Da*xo*xr+Da*xr^2+(-2)*v*yo+Da*yo^2+2*v*yr+(-2)*Da*yo*yr+Da*yr^2 < 0)|(Da<=0&(-1)*w*xo+w*xr+v*yo+(-1)*v*yr<=0)&(-1)*xo^2+2*xo*xr+(-1)*xr^2+(-1)*yo^2+2*yo*yr+(-1)*yr^2 < 0)&(0 < -accpost&-accpost<=Da)&(xr+w/(-accpost)-xo)^2+(yr-v/(-accpost)-yo)^2!=(v^2+w^2)/accpost^2&(xrpost+wpost/(-accpost)-xo)^2+(yrpost-vpost/(-accpost)-yo)^2!=(vpost^2+wpost^2)/accpost^2&yrpost_0=yr&vpost_0=v&xrpost_0=xr&apost=(-1)&wpost_0=w|(((((((((xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2=0&(-2)*w*xo+Da*xo^2+2*w*xr+(-2)*Da*xo*xr+Da*xr^2+2*v*yo+Da*yo^2+(-2)*v*yr+(-2)*Da*yo*yr+Da*yr^2!=0|Da<=0&xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2=0)|(w*xo+(-1)*w*xr+(-1)*v*yo+v*yr<=0&(-1)*xo^2+2*xo*xr+(-1)*xr^2+(-1)*yo^2+2*yo*yr+(-1)*yr^2 < 0)&(-2)*w*xo+Da*xo^2+2*w*xr+(-2)*Da*xo*xr+Da*xr^2+2*v*yo+Da*yo^2+(-2)*v*yr+(-2)*Da*yo*yr+Da*yr^2!=0)|((-1)*w*xo+w*xr+v*yo+(-1)*v*yr<=0&xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2 < 0)&(-2)*w*xo+Da*xo^2+2*w*xr+(-2)*Da*xo*xr+Da*xr^2+2*v*yo+Da*yo^2+(-2)*v*yr+(-2)*Da*yo*yr+Da*yr^2!=0)|xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2 < 0&2*w*xo+(-1)*Da*xo^2+(-2)*w*xr+2*Da*xo*xr+(-1)*Da*xr^2+(-2)*v*yo+(-1)*Da*yo^2+2*v*yr+2*Da*yo*yr+(-1)*Da*yr^2 < 0)|(-1)*xo^2+2*xo*xr+(-1)*xr^2+(-1)*yo^2+2*yo*yr+(-1)*yr^2 < 0&(-2)*w*xo+Da*xo^2+2*w*xr+(-2)*Da*xo*xr+Da*xr^2+2*v*yo+Da*yo^2+(-2)*v*yr+(-2)*Da*yo*yr+Da*yr^2 < 0)|(Da<=0&w*xo+(-1)*w*xr+(-1)*v*yo+v*yr<=0)&(-1)*xo^2+2*xo*xr+(-1)*xr^2+(-1)*yo^2+2*yo*yr+(-1)*yr^2 < 0)|(Da<=0&(-1)*w*xo+w*xr+v*yo+(-1)*v*yr<=0)&xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2 < 0)|(Da<=0&xo^2+(-2)*xo*xr+xr^2+yo^2+(-2)*yo*yr+yr^2 < 0)&2*w*xo+(-1)*Da*xo^2+(-2)*w*xr+2*Da*xo*xr+(-1)*Da*xr^2+(-2)*v*yo+(-1)*Da*yo^2+2*v*yr+2*Da*yo*yr+(-1)*Da*yr^2 < 0)|(Da<=0&(-1)*xo^2+2*xo*xr+(-1)*xr^2+(-1)*yo^2+2*yo*yr+(-1)*yr^2 < 0)&(-2)*w*xo+Da*xo^2+2*w*xr+(-2)*Da*xo*xr+Da*xr^2+2*v*yo+Da*yo^2+(-2)*v*yr+(-2)*Da*yo*yr+Da*yr^2 < 0)&(0 < accpost&accpost<=Da)&(xr+w/accpost-xo)^2+(yr-v/accpost-yo)^2!=(v^2+w^2)/accpost^2&(xrpost+wpost/accpost-xo)^2+(yrpost-vpost/accpost-yo)^2!=(vpost^2+wpost^2)/accpost^2&yrpost_0=yr&vpost_0=v&xrpost_0=xr&apost=1&wpost_0=w"
        .asFormula
    val tic = System.currentTimeMillis()
    val (_, proof) = PropositionalTactics.disjunctiveNormalForm(fml)
    val toc = System.currentTimeMillis()
    proof shouldBe Symbol("proved")
    (toc - tic) should be <= 1000L
  }

}
