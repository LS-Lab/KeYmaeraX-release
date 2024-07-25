/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.Configuration
import org.keymaerax.bellerophon.BelleExpr
import org.keymaerax.btactics.ModelPlex.{createMonitorSpecificationConjecture, INDEXED_POST_VAR}
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.codegen.{CodeGenerator, PythonGenerator, PythonMonitorGenerator}
import org.keymaerax.core._
import org.keymaerax.infrastruct.Augmentors.ExpressionAugmentor
import org.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import org.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import org.keymaerax.parser.StringConverter.StringToStringConverter
import org.keymaerax.parser.{ArchiveParser, ParsedArchiveEntry}
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tagobjects.TodoTest
import org.keymaerax.tags.SlowTest
import org.keymaerax.tools.ext.{QETacticTool, SimplificationTool}
import org.scalatest.LoneElement._

import scala.collection.immutable.ListMap
import scala.io.Source

@SlowTest
class PartialObservableModelplexTests extends TacticTestBase {
  def monitorSize(f: Formula): Int = {
    var numOperators = 0
    ExpressionTraversal.traverse(
      new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
          e match { case _ => numOperators += 1; Left(None) }

        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case _: Variable => Left(None)
          case Number(_) => Left(None)
          case FuncOf(_, _) => Left(None)
          case Nothing => Left(None)
          case _ => numOperators += 1; Left(None)
        }
      },
      f,
    )
    numOperators
  }

  private def report(
      result: Formula,
      qeFreeResult: Formula,
      proof: ProvableSig,
      name: String,
      start: Long = 0,
      approxEnd: Long = 0,
      synthEnd: Long = 0,
      partialQEEnd: Long = 0,
  ): Unit = {
    println("================================")
    println(s"$name quantified monitor size: " + monitorSize(result))
    println(s"$name quantifier-free monitor size: " + monitorSize(qeFreeResult))
    println(s"Proof steps ${proof.steps}")
    println(s"Duration create approximation [s]: ${(approxEnd - start) / 1000}")
    println(s"Duration derive monitor [s]: ${(synthEnd - approxEnd) / 1000}")
    println(s"Duration Partial QE [s]: ${(partialQEEnd - synthEnd) / 1000}")
    println(s"Sum (QE/synthesis duration) [s]: ${(qeDurationListener
        .duration + (partialQEEnd - synthEnd)) / 1000}/${(partialQEEnd - start) / 1000}")
  }

  private def deriveMonitor[K <: NamedSymbol](
      entry: ParsedArchiveEntry,
      tactic: Option[BelleExpr],
      unobservable: ListMap[K, Option[Formula]],
      tool: QETacticTool with SimplificationTool,
      postVarFactory: Variable => Variable = ModelPlex.NAMED_POST_VAR,
      checkFOResult: ProvableSig => Any = (_: ProvableSig) => _,
      checkWitnessResult: ProvableSig => Any = (_: ProvableSig) => _,
  ): Formula = {
    val start = System.currentTimeMillis()
    qeDurationListener.reset()

    val (approx, _) =
      if (tactic.isDefined) ModelPlex.createNonlinearModelApprox(entry.name, tactic.get, entry.defs)(entry.model)
      else (
        entry
          .model
          .exhaustiveSubst(USubst(entry.defs.substs.filter(_.what.isInstanceOf[SystemConst])))
          .asInstanceOf[Formula],
        skip,
      )

    val stateVars = StaticSemantics
      .boundVars(approx)
      .toSet[Variable]
      .filter(_.isInstanceOf[BaseVariable])
      .map(_.asInstanceOf[BaseVariable])

    val intermediate = System.currentTimeMillis()

    val chaseStartPos = List.fill(unobservable.size)(0) ++
      (if (unobservable.values.exists(_.isDefined)) 1 :: Nil else Nil)
    val ModelPlexConjecture(init, modelplexInput, assumptions) =
      createMonitorSpecificationConjecture(approx, stateVars.toList, unobservable, postVarFactory)

    val foResult = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1, chaseStartPos))
    checkFOResult(foResult)

    Configuration.set(Configuration.Keys.MATHEMATICA_QE_METHOD, "Resolve", saveToFile = false)
    val synthResult = proveBy(
      foResult,
      ModelPlex.optimizationOneWithSearch(
        Some(tool),
        assumptions,
        unobservable.keys.toList,
        Some(ModelPlex.mxSimplify),
        postVarFactory,
      )(1),
    )
    checkWitnessResult(synthResult)

    val synthEnd = System.currentTimeMillis()

    val stepwiseQEProof = ModelPlex
      .stepwisePartialQE(synthResult.subgoals.loneElement.succ.loneElement, assumptions, entry.defs, tool)
    stepwiseQEProof shouldBe Symbol("proved")

    val expand = StaticSemantics.symbols(synthResult.subgoals.head) --
      StaticSemantics.symbols(stepwiseQEProof.conclusion)
    val subst = USubst(
      entry
        .defs
        .substs
        .filter({ case SubstitutionPair(what, _) => StaticSemantics.symbols(what).intersect(expand).nonEmpty })
    )

    val qfProof = (synthResult(subst)(useAt(stepwiseQEProof)(SuccPos(0)).computeResult _, 0)(
      PropositionalTactics.rightAssociate(SuccPos(0)).computeResult _,
      0,
    )(SimplifierV3.simplify(SuccPos(0)).computeResult _, 0))
    val qf = qfProof.subgoals.loneElement.succ.loneElement

    val end = System.currentTimeMillis()

    StaticSemantics.boundVars(qf) shouldBe Symbol("empty")
    StaticSemantics
      .freeVars(qf)
      .intersect(unobservable.keySet.filter(_.isInstanceOf[Variable]).map(_.asInstanceOf[Variable])) shouldBe
      Symbol("empty")

    report(synthResult.subgoals.head.succ.head, qf, qfProof, entry.name, start, intermediate, synthEnd, end)

    // transform to test program
    val testPrgProof = qfProof(ModelPlex.chaseToTests(combineTests = false)(SuccPos(0)).computeResult _, 0)
    val testProg = testPrgProof.subgoals.head.succ.head

    // export code
    val Imply(_, Box(Loop(prg), _)) = entry.expandedModel
    val inputs = CodeGenerator.getInputs(prg) --
      unobservable.keySet.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])
    val sensorsForUnobservables = unobservable
      .flatMap({
        case (_, Some(v)) => StaticSemantics.freeVars(v).toSet -- stateVars
        case _ => Set.empty[Variable]
      })
      .toList
    val observable = stateVars
      .diff(unobservable.keySet.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])) ++
      sensorsForUnobservables.map(_.asInstanceOf[BaseVariable])
    println("Exporting code...")
    val (monitorCodeDefs, monitorCodeBody) = (new PythonGenerator(
      new PythonMonitorGenerator(Symbol("resist"), entry.defs),
      init,
      entry.defs,
    ))(testProg, observable, inputs, "Monitor")
    println(monitorCodeDefs + monitorCodeBody)
    println("...done")

    // @todo EulerIntegrationCompiler: compile to a Python simulator

    qf
  }

  "Conjecture generator" should "make a state variable unobservable" in withTactics {
    val fml = "x>=0 -> [{x:=x+1;}*]x>=0".asFormula
    ModelPlex
      .createMonitorSpecificationConjecture(fml, List(Variable("x")), ListMap(Variable("x") -> None))
      .conjecture shouldBe "\\exists x <{x:=x+1;}*>\\exists xpost xpost=x".asFormula
  }

  it should "replace a state variable with a sensor" in withTactics {
    val fml = "x>=0 -> [{x:=x+1;}*]x>=0".asFormula
    ModelPlex
      .createMonitorSpecificationConjecture(
        fml,
        List(Variable("x")),
        ListMap(Variable("x") -> Some("xS-xU()<=x & x<=xS+xU()".asFormula)),
      )
      .conjecture shouldBe
      "\\exists x ((xS-xU()<=x&x<=xS+xU())&<{x:=x+1;}*>\\exists xpost ((xSpost-xU()<=xpost & xpost<=xSpost+xU()) & xpost=x))"
        .asFormula
  }

  it should "existentially quantify an unknown parameter" in withTactics {
    val fml = "x>=0 -> [{x:=f()+1;}*]x>=0".asFormula
    ModelPlex
      .createMonitorSpecificationConjecture(fml, List(Variable("x")), ListMap(Function("f", None, Unit, Real) -> None))
      .conjecture shouldBe "\\exists f <{x:=f+1;}*>xpost=x".asFormula
  }

  it should "existentially quantify an unknown function" in withTactics {
    val fml = "x>=0 -> [{x:=f(y)+1;z:=2*f(y);}*]x>=0".asFormula
    ModelPlex
      .createMonitorSpecificationConjecture(
        fml,
        List(Variable("x"), Variable("z")),
        ListMap(Function("f", None, Real, Real) -> None),
      )
      .conjecture shouldBe "\\exists f <{x:=f+1;z:=2*f;}*>(xpost=x&zpost=z)".asFormula
  }

  it should "complain when function arguments are bound" in withTactics {
    val fml = "x>=0 -> [{x:=f(x)+1;}*]x>=0".asFormula
    the[IllegalArgumentException] thrownBy ModelPlex.createMonitorSpecificationConjecture(
      fml,
      List(Variable("x")),
      ListMap(Function("f", None, Real, Real) -> None),
    ) should have message
      "requirement failed: Unable to make functions f(x) unobservable, because their arguments are bound in program; replace manually with non-deterministic assignments (e.g., replace x:=2; y:=f(x) with x:=2; fx:=*; y:=fx)"
  }

  it should "replace a function with a sensor" in withTactics {
    val fml = "x>=0 & f(x)>=0 -> [{y:=f(x)+1;}*]y>=0".asFormula
    ModelPlex
      .createMonitorSpecificationConjecture(
        fml,
        List(Variable("y")),
        ListMap(Function("f", None, Real, Real) -> Some("fS-fU() <= f(x) & f(x) <= fS+fU()".asFormula)),
      )
      .conjecture shouldBe "\\exists f ((fS-fU()<=f&f<=fS+fU())&<{y:=f+1;}*>ypost=y)".asFormula
  }

  "Partial Observability" should "derive a model monitor from approximated turning behavior" in withMathematica {
    tool =>
      val Some(curvedBot) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Curved Ground Robot Motion is Safe",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )

      checkArchiveEntries(List(curvedBot))

      val tactic = curvedBot.tactics.head._3
      val approx = ModelPlex.createNonlinearModelApprox(curvedBot.name, tactic, curvedBot.defs)(curvedBot.model)
      val Some(approxEntry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Approximated Curved Ground Robot Motion is Safe",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      approx._1 shouldBe approxEntry.defs.exhaustiveSubst(approxEntry.model)

      val monitor = deriveMonitor(curvedBot, Some(curvedBot.tactics.head._3), ListMap.empty, tool)
      val expected =
        "(xr+w/(-1)-xo)^2+(yr-v/(-1)-yo)^2!=v^2+w^2&(xrpost+wpost/(-1)-xo)^2+(yrpost-vpost/(-1)-yo)^2!=vpost^2+wpost^2&apost=(-1)&wpost_0=w&vpost_0=v&xrpost_0=xr&yrpost_0=yr|(xr+w-xo)^2+(yr-v-yo)^2!=v^2+w^2&(xr+w/1-xo)^2+(yr-v/1-yo)^2!=v^2+w^2&(xrpost+wpost/1-xo)^2+(yrpost-vpost/1-yo)^2!=vpost^2+wpost^2&apost=1&wpost_0=w&vpost_0=v&xrpost_0=xr&yrpost_0=yr"
          .asFormula
      proveBy(Equiv(monitor, expected), propClose) shouldBe Symbol("proved")
  }

  it should "derive an approximated model monitor with unobservable parameter" in withMathematica { tool =>
    val Some(curvedBot) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Curved Ground Robot Motion with Curve Disturbance is Safe",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )

    checkArchiveEntries(List(curvedBot))

    val unobservable = ListMap(Function("Da", None, Unit, Real) -> None)
    deriveMonitor(
      curvedBot,
      Some(curvedBot.tactics.head._3),
      unobservable,
      tool,
      checkFOResult = (pr: ProvableSig) =>
        pr.subgoals.loneElement shouldBe
          "==> \\exists Da (\\forall acc (0 < acc&acc<=Da->(xr+w/((-1)*acc)-xo)^2+(yr-v/((-1)*acc)-yo)^2!=(v^2+w^2)/acc^2)&\\exists acc ((0 < acc&acc<=Da)&\\forall v_0 (v_0=v->\\forall w_0 (w_0=w->\\forall xr_0 (xr_0=xr->\\forall yr_0 (yr_0=yr->(xr+w/((-1)*((-1)*acc))-xo)^2+(yr-v/((-1)*((-1)*acc))-yo)^2!=(v^2+w^2)/((-1)*acc)^2&\\exists v \\exists w \\exists xr \\exists yr ((xr+w/((-1)*((-1)*acc))-xo)^2+(yr-v/((-1)*((-1)*acc))-yo)^2!=(v^2+w^2)/((-1)*acc)^2&wpost=w&yrpost_0=yr_0&yrpost=yr&vpost_0=v_0&xrpost_0=xr_0&apost=(-1)&vpost=v&wpost_0=w_0&xrpost=xr&accpost=(-1)*acc))))))|\\forall acc (0 < acc&acc<=Da->(xr+w/acc-xo)^2+(yr-v/acc-yo)^2!=(v^2+w^2)/acc^2)&\\exists acc ((0 < acc&acc<=Da)&\\forall v_0 (v_0=v->\\forall w_0 (w_0=w->\\forall xr_0 (xr_0=xr->\\forall yr_0 (yr_0=yr->(xr+w/(1*(1*acc))-xo)^2+(yr-v/(1*(1*acc))-yo)^2!=(v^2+w^2)/(1*acc)^2&\\exists v \\exists w \\exists xr \\exists yr ((xr+w/(1*(1*acc))-xo)^2+(yr-v/(1*(1*acc))-yo)^2!=(v^2+w^2)/(1*acc)^2&wpost=w&yrpost_0=yr_0&yrpost=yr&vpost_0=v_0&xrpost_0=xr_0&apost=1&vpost=v&wpost_0=w_0&xrpost=xr&accpost=1*acc)))))))"
            .asSequent,
    )
  }

  it should
    "FEATURE_REQUEST: derive a model monitor from approximated turning behavior with actuator disturbance" ignore
    withMathematica { tool =>
      // @todo model is not proved yet
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Curved Ground Robot Motion with Piecewise Constant Actuator Disturbance is Safe",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservable = ListMap[Variable, Option[Formula]](Variable("ad") -> None)
      deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool) shouldBe
        "\\forall d (-1-D()<=d&d<=-1+D()->(xr+w/d-xo)^2+(yr-v/d-yo)^2!=v^2+w^2)&(-1-D()<=adpost&adpost<=-1+D())&(xr+w/adpost-xo)^2+(yr-v/adpost-yo)^2!=v^2+w^2&(xrpost+wpost/adpost-xo)^2+(yrpost-vpost/adpost-yo)^2!=vpost^2+wpost^2&apost=-1&wpost_0=w&vpost_0=v&xrpost_0=xr&yrpost_0=yr|\\forall d (1-D()<=d&d<=1+D()->(xr+w/d-xo)^2+(yr-v/d-yo)^2!=v^2+w^2)&(1-D()<=adpost&adpost<=1+D())&(xr+w/adpost-xo)^2+(yr-v/adpost-yo)^2!=v^2+w^2&(xrpost+wpost/adpost-xo)^2+(yrpost-vpost/adpost-yo)^2!=vpost^2+wpost^2&apost=1&wpost_0=w&vpost_0=v&xrpost_0=xr&yrpost_0=yr"
          .asFormula
    }

  it should "derive a proof-guided water tank model monitor" in withMathematica { tool =>
    // experiment: water tank original
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Water tank is safe",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )

    val unobservable = ListMap[Variable, Option[Formula]]("c_0".asVariable -> None, "l_0".asVariable -> None)

    val monitor =
      deriveMonitor(entry, entry.tactics.find(_._1 == "Proof Water tank is safe").map(_._3), unobservable, tool)
    monitor shouldBe
      "(-1)<=fpost&fpost<=(m()-l)/ep()&0<=l&0<=ep()&0<=lpost&cpost<=ep()&cpost>=0&lpost=l+fpost*cpost".asFormula

    val monitor2 = deriveMonitor(entry, None, unobservable, tool)
    proveBy(Equiv(monitor, monitor2), QE) shouldBe Symbol("proved")

    // @note autoClose uses nilpotentsolve, which introduces internal time_ and so need indexed post-variable instead of named
    val monitor3 = deriveMonitor(
      entry,
      Some(TactixLibrary.autoClose),
      unobservable ++ ListMap[Variable, Option[Formula]]("time_".asVariable -> None),
      tool,
      postVarFactory = (v: Variable) => BaseVariable(v.name, Some(v.index.map(_ + 11).getOrElse(10))),
    )
    monitor3 shouldBe
      "(-1)<=f_10&f_10<=(m()-l)/ep()&0<=l&0<=ep()&-l_10<=0&-c_10<=0&-ep()<=0&c_10+-ep()<=0&c_10*f_10+l+-l_10=0"
        .asFormula
  }

  it should "derive a model monitor from water tank with flow disturbance" in withMathematica { tool =>
    // @note experiment: water tank + actuator
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Water tank with flow disturbance is safe",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )

    val unobservable =
      ListMap[Variable, Option[Formula]]("fd".asVariable -> None, "c_0".asVariable -> None, "l_0".asVariable -> None)
    deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool)
  }

  it should "derive a model monitor from water tank with flow disturbance for unknown disturbance parameter" in
    withMathematica { tool =>
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Water tank with flow disturbance is safe",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val model = entry
        .model
        .exhaustiveSubst(USubst(entry.defs.substs.filter(_.what.isInstanceOf[SystemConst])))
        .asInstanceOf[Formula]

      val allVars = List("c", "f", "fd", "l").map(_.asVariable.asInstanceOf[BaseVariable])
      val unobservable = ListMap("fd".asVariable -> None, Function("D", None, Unit, Real, None) -> None)
      val chaseStartPos = List.fill(unobservable.count(_._1.isInstanceOf[Function]))(0) ++
        (if (unobservable.values.exists(_.isDefined)) 1 :: Nil else Nil)
      val (modelMonitorInput, assumptions) = ModelPlex.createSlidingMonitorSpec(model, allVars, unobservable, 2)

      Configuration.set(Configuration.Keys.MATHEMATICA_QE_METHOD, "Resolve", saveToFile = false)
      val foResult = proveBy(modelMonitorInput, ModelPlex.modelMonitorByChase(1, chaseStartPos))

      val opt1Result = proveBy(
        foResult.subgoals.head,
        ModelPlex.optimizationOneWithSearch(
          Some(tool),
          assumptions,
          unobservable.keySet.toList,
          Some(ModelPlex.mxSimplify),
          INDEXED_POST_VAR,
        )(1),
      )
      StaticSemantics
        .freeVars(opt1Result.subgoals.loneElement)
        .toSet[Variable]
        .map(_.name)
        .intersect(unobservable.keySet.map(_.name)) shouldBe Symbol("empty")
      println(opt1Result.subgoals.loneElement)
    }

  it should "derive a model monitor from water tank with flow disturbance for unknown disturbance parameter (2)" in
    withMathematica { tool =>
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Water tank with flow disturbance is safe",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      // monitor for disturbance: exists 0<=D<=0.2
      val unobservable = ListMap("fd".asVariable -> None, "D()".asFunction -> Some("0 <= D() & D() <= 0.2".asFormula))
      deriveMonitor(entry, None, unobservable, tool)
    }

  it should
    "derive a model monitor from water tank with flow disturbance for unknown disturbance parameter and load measurement uncertainty" ignore
    withMathematica { tool =>
      // @todo extremely long
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Water tank with flow disturbance is safe",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservable = ListMap[NamedSymbol, Option[Formula]](
        Variable("l") -> Some("0 <= lU() & lS-lU() <= l & l <= lS+lU()".asFormula),
        Variable("fd") -> None,
        Function("D", None, Unit, Real) -> None,
      )
      deriveMonitor(entry, None, unobservable, tool)
    }

  it should "derive a model monitor from water tank with load measurement uncertainty" in withMathematica { tool =>
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Water tank with load measurement uncertainty is safe",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )
    val unobservable = ListMap[Variable, Option[Formula]](
      "l".asVariable -> Some("lu-U()<=l&l<=lu+U()".asFormula),
      "c_0".asVariable -> None,
      "l_0".asVariable -> None,
    )
    deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool)
  }

  it should "derive a model monitor from water tank with load measurement uncertainty (control exists)" in
    withMathematica { tool =>
      // @note experiment: water tank + sensor
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Water tank with load measurement uncertainty is safe (control choice exists)",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservable = ListMap[Variable, Option[Formula]](
        "l".asVariable -> Some("lu-U()<=l&l<=lu+U()".asFormula),
        "c_0".asVariable -> None,
        "l_0".asVariable -> None,
      )
      deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool)
    }

  it should "prove planar flight motion" in withMathematica { _ =>
    val entries = ArchiveParser(
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString
    )

    checkArchiveEntries(
      entries
        .find(
          _.name ==
            "ModelPlex/Partial Observability/Planar Flight Motion Safety with Ownship Angular Velocity Disturbance"
        )
        .toList
    )
    checkArchiveEntries(
      entries
        .find(
          _.name == "ModelPlex/Partial Observability/Planar Flight Motion Safety with Intruder Linear Speed Uncertainty"
        )
        .toList
    )
    checkArchiveEntries(
      entries
        .find(
          _.name == "ModelPlex/Partial Observability/Planar Flight Motion Safety with Intruder Velocity Uncertainty"
        )
        .toList
    )
    checkArchiveEntries(
      entries
        .find(
          _.name ==
            "ModelPlex/Partial Observability/Planar Flight Motion Safety with Ownship Angular Velocity Disturbance and Intruder Velocity Uncertainty"
        )
        .toList
    )

    checkArchiveEntries(
      entries.find(_.name == "ModelPlex/Partial Observability/Planar Flight Motion Safety 2 Simple").toList
    )
    checkArchiveEntries(
      entries
        .find(
          _.name ==
            "ModelPlex/Partial Observability/Planar Flight Motion Safety 2 Simple with Ownship Actuator Disturbance"
        )
        .toList
    )
    checkArchiveEntries(
      entries
        .find(
          _.name == "ModelPlex/Partial Observability/Planar Flight Motion Safety 2 Simple with Position Uncertainty"
        )
        .toList
    )
    checkArchiveEntries(
      entries
        .find(
          _.name ==
            "ModelPlex/Partial Observability/Planar Flight Motion Safety 2 Simple with Intruder Linear Velocity Uncertainty"
        )
        .toList
    )

    checkArchiveEntries(
      entries.find(_.name == "ModelPlex/Partial Observability/Planar Flight Motion Safety 3 Simple").toList
    )
    checkArchiveEntries(
      entries
        .find(
          _.name ==
            "ModelPlex/Partial Observability/Planar Flight Motion Safety 3 Simple with Ownship Actuator Disturbance"
        )
        .toList
    )
    checkArchiveEntries(
      entries
        .find(
          _.name ==
            "ModelPlex/Partial Observability/Planar Flight Motion Safety 3 Simple with Intruder Linear Velocity Uncertainty"
        )
        .toList
    )
  }

  it should "derive model monitor from approximated planar flight motion 2 simple" in withMathematica { tool =>
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Planar Flight Motion Safety 2 Simple",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )
    val unobservable =
      ListMap("x_0".asVariable -> None, "y_0".asVariable -> None, "dx_0".asVariable -> None, "dy_0".asVariable -> None)
    deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool) shouldBe
      "I2(v1,v2,1,0,dx,dy,x,y)>2*v1*v2+2*v2&dx^2+dy^2=1&dxpost^2+dypost^2=1&I2(1,1,1,0,dxpost,dypost,xpost,ypost)=I2(1,1,1,0,dx,dy,x,y)&w1post=1&w2post=0"
        .asFormula
  }

  it should "derive model monitor from approximated planar flight motion" in withMathematica { tool =>
    // experiment: horizontal flight original
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Planar Flight Motion Safety 3 Simple",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )
    val unobservable =
      ListMap("x_0".asVariable -> None, "y_0".asVariable -> None, "dx_0".asVariable -> None, "dy_0".asVariable -> None)
    deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool) shouldBe
      "I1(v1,v2,dx,dy,x,y)>v1+v2&(0=1->dx^2+dy^2=1)&(0=1->dxpost^2+dypost^2=1&I2(1,1,1,0,dxpost,dypost,xpost,ypost)=I2(1,1,1,0,dx,dy,x,y))&dxpost=dx&dypost=dy&I1(1,1,dxpost,dypost,xpost,ypost)=I1(1,1,dx,dy,x,y)&w1post=0&w2post=0|I2(v1,v2,1,0,dx,dy,x,y)>2*v1*v2+2*v2&dx^2+dy^2=1&dxpost^2+dypost^2=1&I2(1,1,1,0,dxpost,dypost,xpost,ypost)=I2(1,1,1,0,dx,dy,x,y)&(1=0->dxpost=dx&dypost=dy&I1(1,1,dxpost,dypost,xpost,ypost)=I1(1,1,dx,dy,x,y))&w1post=1&w2post=0"
        .asFormula
  }

  it should "derive model monitor from approximated planar flight motion simple 2 with ownship actuator disturbance" in
    withMathematica { tool =>
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Planar Flight Motion Safety 2 Simple with Ownship Actuator Disturbance",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservableVars = ListMap(
        "w1".asVariable -> None,
        "x_0".asVariable -> None,
        "y_0".asVariable -> None,
        "dx_0".asVariable -> None,
        "dy_0".asVariable -> None,
      )
      deriveMonitor(entry, Some(entry.tactics.head._3), unobservableVars, tool) shouldBe
        "(v2+(-dy)*v2*x+dx*v2*y=0&1+wD() < 0|v2!=0&1+(-dy)*x+dx*y=0&1+wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+v2*wD()+(-dy)*v2*x*wD()+dx*v2*y*wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+(-v2)*wD()+dy*v2*x*wD()+(-dx)*v2*y*wD() < 0|v2+(-dy)*v2*x+dx*v2*y=0&wD() < 0|(-1)+dx!=0&v1!=0&v2!=0&v1*v2+(-dx)*v1*v2 < 0&1+(-dy)*x+dx*y=0&wD() < 0|v2!=0&1+(-dy)*x+dx*y=0&(-1)+wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+v2*wD()+(-dy)*v2*x*wD()+dx*v2*y*wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+(-v2)*wD()+dy*v2*x*wD()+(-dx)*v2*y*wD() < 0|(-1)+dx!=0&v1!=0&v2!=0&v1*v2+(-dx)*v1*v2 < 0&1+(-dy)*x+dx*y=0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+v2*wD()+(-dy)*v2*x*wD()+dx*v2*y*wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+(-v2)*wD()+dy*v2*x*wD()+(-dx)*v2*y*wD() < 0|v2+(-dy)*v2*x+dx*v2*y < 0&wD() < 0&-v2+(-v1)*v2+dx*v1*v2+dy*v2*x+(-dx)*v2*y+(-v2)*wD()+dy*v2*x*wD()+(-dx)*v2*y*wD() < 0|v2!=0&v2+(-dy)*v2*x+dx*v2*y < 0&wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+(-v2)*wD()+dy*v2*x*wD()+(-dx)*v2*y*wD() < 0|v2!=0&v2+(-dy)*v2*x+dx*v2*y < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+v2*wD()+(-dy)*v2*x*wD()+dx*v2*y*wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+(-v2)*wD()+dy*v2*x*wD()+(-dx)*v2*y*wD() < 0|v2!=0&-v2+dy*v2*x+(-dx)*v2*y < 0&wD() < 0&-v2+(-v1)*v2+dx*v1*v2+dy*v2*x+(-dx)*v2*y+v2*wD()+(-dy)*v2*x*wD()+dx*v2*y*wD() < 0|v2!=0&-v2+dy*v2*x+(-dx)*v2*y < 0&wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+v2*wD()+(-dy)*v2*x*wD()+dx*v2*y*wD() < 0|v2!=0&-v2+dy*v2*x+(-dx)*v2*y < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+v2*wD()+(-dy)*v2*x*wD()+dx*v2*y*wD() < 0&v2+v1*v2+(-dx)*v1*v2+(-dy)*v2*x+dx*v2*y+(-v2)*wD()+dy*v2*x*wD()+(-dx)*v2*y*wD() < 0)&(dx+-dxpost=0&(-1)+dx^2+dy^2=0&(-1)+dxpost^2+dypost^2=0&(-1)+w1ppost=0&w2post=0&-wD()<=0&(-dy)*x+dypost*xpost+dx*y+(-dxpost)*ypost=0|(-1)+dx^2+dy^2=0&(-1)+dxpost^2+dypost^2=0&(-1)+w1ppost=0&w2post=0&(-dy)*x+dypost*xpost+dx*y+(-dxpost)*ypost < 0&-dx+dxpost+(-dy)*x+(-dy)*wD()*x+dypost*xpost+dypost*wD()*xpost+dx*y+dx*wD()*y+(-dxpost)*ypost+(-dxpost)*wD()*ypost<=0&dx+-dxpost+dy*x+(-dy)*wD()*x+(-dypost)*xpost+dypost*wD()*xpost+(-dx)*y+dx*wD()*y+dxpost*ypost+(-dxpost)*wD()*ypost<=0|(-1)+dx^2+dy^2=0&(-1)+dxpost^2+dypost^2=0&(-1)+w1ppost=0&w2post=0&dy*x+(-dypost)*xpost+(-dx)*y+dxpost*ypost < 0&dx+-dxpost+dy*x+dy*wD()*x+(-dypost)*xpost+(-dypost)*wD()*xpost+(-dx)*y+(-dx)*wD()*y+dxpost*ypost+dxpost*wD()*ypost<=0&-dx+dxpost+(-dy)*x+dy*wD()*x+dypost*xpost+(-dypost)*wD()*xpost+dx*y+(-dx)*wD()*y+(-dxpost)*ypost+dxpost*wD()*ypost<=0)"
          .asFormula
    }

  it should "derive model monitor from approximated planar flight motion with ownship actuator disturbance" in
    withMathematica { tool =>
      // experiment: horizontal flight + actuator
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Planar Flight Motion Safety 3 Simple with Ownship Actuator Disturbance",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservableVars = ListMap(
        "w1".asVariable -> None,
        "x_0".asVariable -> None,
        "y_0".asVariable -> None,
        "dx_0".asVariable -> None,
        "dy_0".asVariable -> None,
      )
      deriveMonitor(entry, Some(entry.tactics.head._3), unobservableVars, tool)
    }

  it should
    "derive model monitor from approximated planar flight motion simple 2 with intruder linear velocity uncertainty" in
    withMathematica { tool =>
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Planar Flight Motion Safety 2 Simple with Intruder Linear Velocity Uncertainty",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservableVars = ListMap(
        "v2".asVariable -> Some("v2-v2U()<=v2m&v2m<=v2+v2U()".asFormula),
        "x_0".asVariable -> None,
        "y_0".asVariable -> None,
        "dx_0".asVariable -> None,
        "dy_0".asVariable -> None,
      )
      deriveMonitor(entry, Some(entry.tactics.head._3), unobservableVars, tool) shouldBe
        "(-1)+dx^2+dy^2=0&(-1)+dxpost^2+dypost^2=0&v2m < 0&-v2m+v2mpost<=0&v2mpost < 0&v2m+-v2mpost+(-2)*v2U()<=0&-v2U()<=0&v2m+v2U() < 0&(-1)+w1post=0&w2post=0&(-1)+-v1+dx*v1+dy*x+(-dx)*y < 0&2*dypost*xpost+2*(-dxpost)*ypost+2*dxpost+-(2*dy*x+2*(-dx)*y+2*dx)=0|(-1)+dx^2+dy^2=0&(-1)+dxpost^2+dypost^2=0&v2m < 0&v2m+-v2mpost<=0&-v2U()<=0&v2m+v2U() < 0&-v2m+v2mpost+(-2)*v2U()<=0&(-1)+w1post=0&w2post=0&(-1)+-v1+dx*v1+dy*x+(-dx)*y < 0&2*dypost*xpost+2*(-dxpost)*ypost+2*dxpost+-(2*dy*x+2*(-dx)*y+2*dx)=0|(-1)+dx^2+dy^2=0&(-1)+dxpost^2+dypost^2=0&-v2m < 0&-v2m+v2mpost<=0&v2m+-v2mpost+(-2)*v2U()<=0&-v2m+v2U() < 0&-v2U()<=0&(-1)+w1post=0&w2post=0&1+v1+(-dx)*v1+(-dy)*x+dx*y < 0&2*dypost*xpost+2*(-dxpost)*ypost+2*dxpost+-(2*dy*x+2*(-dx)*y+2*dx)=0|(-1)+dx^2+dy^2=0&(-1)+dxpost^2+dypost^2=0&-v2m < 0&v2m+-v2mpost<=0&-v2mpost < 0&-v2m+v2U() < 0&-v2U()<=0&-v2m+v2mpost+(-2)*v2U()<=0&(-1)+w1post=0&w2post=0&1+v1+(-dx)*v1+(-dy)*x+dx*y < 0&2*dypost*xpost+2*(-dxpost)*ypost+2*dxpost+-(2*dy*x+2*(-dx)*y+2*dx)=0"
          .asFormula
    }

  it should "derive model monitor from approximated planar flight motion with intruder linear velocity uncertainty" in
    withMathematica { tool =>
      // experiment: horizontal flight + sensor
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Planar Flight Motion Safety 3 Simple with Intruder Linear Velocity Uncertainty",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservableVars = ListMap(
        "v2".asVariable -> Some("v2-v2U()<=v2m&v2m<=v2+v2U()".asFormula),
        "x_0".asVariable -> None,
        "y_0".asVariable -> None,
        "dx_0".asVariable -> None,
        "dy_0".asVariable -> None,
      )
      // @todo partial QE may not terminate
      deriveMonitor(
        entry,
        Some(entry.tactics.head._3),
        unobservableVars,
        tool,
        checkWitnessResult = _.subgoals.loneElement shouldBe
          "==>  \\exists v2 ((v2-v2U()<=v2m&v2m<=v2+v2U())&(\\forall v2p (v2m-v2U()<=v2p&v2p<=v2m+v2U()->I1(v1,v2p,dx,dy,x,y)>v1+v2p)&(0=1->dx^2+dy^2=1)&((0=1->dxpost^2+dypost^2=1&I2(1,1,1,0,dxpost,dypost,xpost,ypost)=I2(1,1,1,0,dx,dy,x,y))&dxpost=dx&dypost=dy&I1(1,1,dxpost,dypost,xpost,ypost)=I1(1,1,dx,dy,x,y))&(v2-v2U()<=v2mpost&v2mpost<=v2+v2U())&\\exists v2post ((v2post-v2U()<=v2mpost&v2mpost<=v2post+v2U())&w1post=0&w2post=0)|\\forall v2p (v2m-v2U()<=v2p&v2p<=v2m+v2U()->I2(v1,v2p,1,0,dx,dy,x,y)>2*v1*v2p+2*v2p)&dx^2+dy^2=1&((dxpost^2+dypost^2=1&I2(1,1,1,0,dxpost,dypost,xpost,ypost)=I2(1,1,1,0,dx,dy,x,y))&(1=0->dxpost=dx&dypost=dy&I1(1,1,dxpost,dypost,xpost,ypost)=I1(1,1,dx,dy,x,y)))&(v2-v2U()<=v2mpost&v2mpost<=v2+v2U())&\\exists v2post ((v2post-v2U()<=v2mpost&v2mpost<=v2post+v2U())&w1post=1&w2post=0)))"
            .asSequent,
      )
    }

  it should
    "FEATURE_REQUEST: derive model monitor from approximated planar flight motion with ownship velocity disturbance and intruder velocity uncertainty" taggedAs
    TodoTest ignore withMathematica { tool =>
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Planar Flight Motion Safety with Ownship Angular Velocity Disturbance and Intruder Velocity Uncertainty",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservableVars = ListMap(
        "w1".asVariable -> None,
        "v2".asVariable -> Some("0<v2m & v2-vU()<=v2m&v2m<=v2+vU()".asFormula),
        "w2".asVariable -> Some("0<w2m & w2-wU()<=w2m&w2m<=w2+wU()".asFormula),
        "x_0".asVariable -> None,
        "y_0".asVariable -> None,
        "dx_0".asVariable -> None,
        "dy_0".asVariable -> None,
      )
      // @todo partial QE may not terminate
      deriveMonitor(
        entry,
        Some(entry.tactics.head._3),
        unobservableVars,
        tool,
        checkWitnessResult = _.subgoals.loneElement shouldBe
          " ==> \\exists v2 \\exists w2 (((0 < v2m&v2-vU()<=v2m&v2m<=v2+vU())&0 < w2m&w2-wU()<=w2m&w2m<=w2+wU())&w1ppost>0&\\forall w1pd \\forall v2p \\forall w2p (w1ppost<=w1pd&w1pd<=w1ppost+wD()&v2m-vU()<=v2p&v2p<=v2m+vU()&w2m-wU()<=w2p&w2p<=w2m+wU()->-w1pd*w2p*(x^2+y^2)+2*v2p*w1pd*dy*x+2*(v1*w2p-v2p*w1pd*dx)*y+2*v1*v2p*dx>2*v1*v2p+2*(v2p*w1pd+v1*w2p)+w1pd*w2p)&\\exists w1 ((w1ppost<=w1&w1<=w1ppost+wD())&dx^2+dy^2=1&(dxpost^2+dypost^2=1&I2(v1,v2,w1,w2,dxpost,dypost,xpost,ypost)=I2(v1,v2,w1,w2,dx,dy,x,y))&\\exists w2 ((0 < w2&0 < w2mpost&w2-wU()<=w2mpost&w2mpost<=w2+wU())&0 < v2mpost&v2-vU()<=v2mpost&v2mpost<=v2+vU())))"
            .asSequent,
      )
    }

  it should "prove LLC" in withMathematica { _ =>
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Local lane control safety",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )
    checkArchiveEntries(entry :: Nil)
  }

  it should "derive a model monitor from approximated ETCS Essentials" in withMathematica { tool =>
    // experiment: train control original
    val entry = ArchiveParser
      .getEntry(
        "ICFEM09/ETCS Essentials",
        Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/etcs/etcs.kyx")).mkString,
      )
      .get
    val monitor = deriveMonitor(
      entry,
      Some(entry.tactics.find(_._1 == "ETCS Essentials Proof with Differential Invariants").get._3),
      ListMap.empty,
      tool,
    )
    monitor shouldBe
      "m-z<=SB(v)&v>=0&0<=ep()&vpost>=0&tpost<=ep()&tpost>=0&vpost=v-b()*tpost&zpost=z+v*tpost-b()/2*tpost^2&vpost=v+A()*tpost&zpost=z+v*tpost+A()/2*tpost^2&zpost_0=z&vpost_0=v&apost=-b()&tpost_0=0|m-z>=SB(v)&v>=0&0<=ep()&vpost>=0&tpost<=ep()&tpost>=0&vpost=v-b()*tpost&zpost=z+v*tpost-b()/2*tpost^2&vpost=v+A()*tpost&zpost=z+v*tpost+A()/2*tpost^2&zpost_0=z&vpost_0=v&apost=A()&tpost_0=0"
        .asFormula
  }

  it should "derive a model monitor from ETCS essentials with train position measurement" in withMathematica { tool =>
    // experiment: train control + sensor
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/ETCS Essentials with train position uncertainty",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )
    val unobservableVars = ListMap(
      "z".asVariable -> Some("z-zU()<=zm&zm<=z+zU()".asFormula),
      "z_0".asVariable -> None,
      "v_0".asVariable -> None,
      "t_0".asVariable -> None,
    )
    deriveMonitor(entry, Some(entry.tactics.head._3), unobservableVars, tool)
  }

  it should "derive a model monitor from ETCS essentials with train acceleration disturbance" in withMathematica {
    tool =>
      // experiment: train control + actuator
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/ETCS Essentials with train acceleration disturbance",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservableVars =
        ListMap("a".asVariable -> None, "z_0".asVariable -> None, "v_0".asVariable -> None, "t_0".asVariable -> None)
      val monitor = deriveMonitor(entry, Some(entry.tactics.head._3), unobservableVars, tool)
      monitor shouldBe
        "m()-z<=SB(v)&(-aD()<=0&A()+b() < 0&accpost+b()=0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|-aD()<=0&accpost+b()=0&A()+2*aD()+b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|-aD()<=0&A()+b() < 0&accpost+b()=0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|-aD()<=0&accpost+b()=0&A()+2*aD()+b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|-aD()<=0&A()+b() < 0&accpost+b()=0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|-aD()<=0&accpost+b()=0&A()+2*aD()+b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|-aD()<=0&accpost+b()=0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0)|m()-z>=SB(v)&(A()+-accpost=0&-aD()<=0&-A()+-b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|A()+-accpost=0&-aD()<=0&-A()+2*aD()+-b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|A()+-accpost=0&-aD()<=0&-A()+-b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|A()+-accpost=0&-aD()<=0&-A()+2*aD()+-b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|A()+-accpost=0&-aD()<=0&-A()+-b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|A()+-accpost=0&-aD()<=0&-A()+2*aD()+-b() < 0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0|A()+-accpost=0&-aD()<=0&-ep()<=0&-ep()+tpost<=0&-tpost<=0&-v<=0&(-A())*tpost+(-aD())*tpost+-v+vpost<=0&(-aD())*tpost+b()*tpost+-v+vpost<=0&-vpost<=0&(-A())*tpost^2+(-aD())*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0&(-aD())*tpost^2+b()*tpost^2+(-2)*tpost*v+(-2)*z+2*zpost<=0)"
          .asFormula
  }

  it should "derive a model monitor from approximated VSL" in withMathematica { tool =>
    // experiment: road traffic control original
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Variable Speed Limit is Safe",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )
    val unobservable = ListMap("v1_0".asVariable -> None, "t_0".asVariable -> None, "x1_0".asVariable -> None)
    val monitor = deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool)
    monitor shouldBe
      "v1>=0&0<=ep()&v1post>=0&tpost<=ep()&a1post=-B()&vslpost=vsl&xslpost=xsl|vslpost>=0&xslpost>=accCompensation(x1,v1,vslpost)&v1>=0&0<=ep()&v1post>=0&tpost<=ep()&a1post=-B()|xsl>=accCompensation(x1,v1,vsl)&-B()<=a1post&a1post<=A()&(v1>=0&0<=ep()&v1post>=0&tpost<=ep()&vslpost=vsl&xslpost=xsl|vslpost>=0&xslpost>=accCompensation(x1,v1,vslpost)&v1>=0&0<=ep()&v1post>=0&tpost<=ep())|x1>=xsl&-B()<=a1post&a1post<=A()&a1post<=(v1-vsl)/ep()&(v1>=0&0<=ep()&v1post>=0&tpost<=ep()&vslpost=vsl&xslpost=xsl|vslpost>=0&xslpost>=accCompensation(x1,v1,vslpost)&v1>=0&0<=ep()&v1post>=0&tpost<=ep())"
        .asFormula
  }

  it should "derive a model monitor from approximated VSL with car actuator disturbance" in withMathematica { tool =>
    // experiment: road traffic control + actuator
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Variable Speed Limit is Safe with Car Actuator Disturbance",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )
    val unobservable =
      ListMap("a1".asVariable -> None, "v1_0".asVariable -> None, "t_0".asVariable -> None, "x1_0".asVariable -> None)
    val monitor = deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool)
    monitor shouldBe
      "-aD()<=0&acc1post+B()=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0&vsl+-vslpost=0&xsl+-xslpost=0|vslpost>=0&xslpost>=accCompensation(x1,v1,vslpost)&-aD()<=0&acc1post+B()=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0|xsl>=accCompensation(x1,v1,vsl)&-B()<=acc1post&acc1post<=A()&(-aD()<=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0&vsl+-vslpost=0&xsl+-xslpost=0|vslpost>=0&xslpost>=accCompensation(x1,v1,vslpost)&-aD()<=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0)|x1>=xsl&-B()<=acc1post&acc1post<=A()&acc1post<=(v1-vsl)/ep()-aD()&(-aD()<=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0&vsl+-vslpost=0&xsl+-xslpost=0|vslpost>=0&xslpost>=accCompensation(x1,v1,vslpost)&-aD()<=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0)"
        .asFormula
  }

  it should "derive a model monitor from approximated VSL with car position uncertainty" in withMathematica { tool =>
    // experiment: road traffic control + sensor
    val Some(entry) = ArchiveParser.getEntry(
      "ModelPlex/Partial Observability/Variable Speed Limit is Safe with Car Position Uncertainty",
      Source
        .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
        .mkString,
    )
    val unobservable = ListMap(
      "x1".asVariable -> Some("x1m-xU()<=x1&x1<=x1m+xU()".asFormula),
      "v1_0".asVariable -> None,
      "t_0".asVariable -> None,
      "x1_0".asVariable -> None,
    )
    val monitor = deriveMonitor(entry, Some(entry.tactics.head._3), unobservable, tool)
    monitor shouldBe
      "a1post+B()=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0&vsl+-vslpost=0&xsl+-xslpost=0&-xU()<=0|a1post+B()=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0&-vslpost<=0&-xU()<=0&-xslpost+accCompensation(x1m,v1,vslpost)<=0|-A()+a1post<=0&-a1post+-B()<=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0&vsl+-vslpost=0&xsl+-xslpost=0&-xU()<=0&-xsl+accCompensation(x1m,v1,vsl)<=0|-A()+a1post<=0&-a1post+-B()<=0&-ep()<=0&-ep()+tpost<=0&-v1<=0&-v1post<=0&-vslpost<=0&-xU()<=0&-xslpost+accCompensation(x1m,v1,vslpost)<=0&-xsl+accCompensation(x1m,v1,vsl)<=0|-A()+a1post<=0&-a1post+-B()<=0&-ep() < 0&-ep()+tpost<=0&-v1<=0&-v1post<=0&a1post*ep()+-v1+vsl<=0&vsl+-vslpost=0&xsl+-xslpost=0&-x1m+xsl+xU()<=0&-xU()<=0|-A()+a1post<=0&-a1post+-B()<=0&-ep() < 0&-ep()+tpost<=0&-v1<=0&-v1post<=0&a1post*ep()+-v1+vsl<=0&vsl+-vslpost=0&xsl+-xslpost=0&-xU()<=0&-x1m+xsl+-xU()<=0|-A()+a1post<=0&-a1post+-B()<=0&-ep() < 0&-ep()+tpost<=0&-v1<=0&-v1post<=0&a1post*ep()+-v1+vsl<=0&-vslpost<=0&-x1m+xsl+xU()<=0&-xU()<=0&-xslpost+accCompensation(x1m,v1,vslpost)<=0|-A()+a1post<=0&-a1post+-B()<=0&-ep() < 0&-ep()+tpost<=0&-v1<=0&-v1post<=0&a1post*ep()+-v1+vsl<=0&-vslpost<=0&-xU()<=0&-x1m+xsl+-xU()<=0&-xslpost+accCompensation(x1m,v1,vslpost)<=0"
        .asFormula
  }

  it should "derive a model monitor from approximated robix static safety" in withMathematica { tool =>
    val entry = ArchiveParser
      .getEntry(
        "IJRR17/Theorem 1: Static safety",
        Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/ijrr/robix.kyx")).mkString,
      )
      .head
    deriveMonitor(entry, entry.tactics.find(_._1 == "Proof Theorem 1: Static safety").map(_._3), ListMap.empty, tool)
  }

  it should "derive a model monitor from approximated robix passive safety" in withMathematica { tool =>
    // experiment: robot original
    val entry = ArchiveParser
      .getEntry(
        "IJRR17/Theorem 2: Passive safety",
        Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/ijrr/robix.kyx")).mkString,
      )
      .head
    val unobservableVars = ListMap(
      List("dx_0", "t_0", "yo_0", "w_0", "x_0", "y_0", "yo_0", "vo_0", "xo_0", "dy_0", "v_0")
        .map(_.asVariable -> None): _*
    )
    deriveMonitor(entry, Some(entry.tactics.head._3), unobservableVars, tool)
  }

  it should "derive a model monitor from approximated robix passive safety despite location uncertainty" ignore
    withMathematica { tool =>
      // @todo test is too slow
      // experiment: robot + sensor
      val Some(entry) = ArchiveParser.getEntry(
        "ModelPlex/Partial Observability/Theorem 6: Passive safety despite location uncertainty",
        Source
          .fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/modelplex/partialobservability.kyx"))
          .mkString,
      )
      val unobservableVars = ListMap(
        ("mx".asVariable -> Some("true".asFormula)) +:
          ("my".asVariable -> Some("(mx-x)^2+(my-y)^2 <= Dp()^2".asFormula)) +:
          List("x_0", "y_0", "v_0", "dx_0", "dy_0", "w_0", "xo_0", "yo_0", "t_0").map(_.asVariable -> None): _*
      )
      deriveMonitor(entry, Some(entry.tactics.head._3), unobservableVars, tool)
    }

}
