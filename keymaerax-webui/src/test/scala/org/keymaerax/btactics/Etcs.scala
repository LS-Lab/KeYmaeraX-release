/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.parser.BelleParser
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.core.Formula
import org.keymaerax.parser.ArchiveParser
import org.keymaerax.parser.StringConverter._
import org.keymaerax.tags.SlowTest
import org.keymaerax.testhelper.ParserFactory._
import org.scalatest.LoneElement._

import scala.io.Source
import scala.language.postfixOps

/**
 * ETCS test cases. Essentials of European Train Control System (ETCS).
 * @see
 *   "Andre Platzer, Jan-David Quesel. European Train Control System: A case study in formal verification. ICFEM, 2009"
 * @see
 *   "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages
 *   143-189, 2008."
 * @author
 *   Stefan Mitsch
 */
@SlowTest
class Etcs extends TacticTestBase {

  "ETCS controllability" should "prove lemma with master" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/controllability-lemma.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove RBC characterisation with master" in withMathematica { _ =>
    val s = parseToSequent(
      getClass.getResourceAsStream("/examples/casestudies/etcs/rbc-controllability-characterisation.kyx")
    )
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove RBC corollary with tactic" ignore withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rbc-controllability-corollary.kyx"))
    // @todo write tactic
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove RBC lemma with master" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rbc-controllability-lemma.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  "ETCS reactivity" should "prove lemma with tactic" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma.kyt"))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "prove full lemma with tactic" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma-full.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma-full.kyt"))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  "ETCS" should "prove essentials with master" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/ETCS-essentials.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  "Rephrased ETCS models" should "prove controllability lemma with master" in withMathematica { _ =>
    val s =
      parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/controllability-lemma.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove essentials with master" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove essentials with tactic from file" in withQE { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyt"))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "find SB condition in essentials" in withQE { _ =>
    val s =
      parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials-bare.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials-bare.kyt"))
        .mkString
    )
    val result = proveBy(s, tactic)
    result.subgoals.loneElement shouldBe
      "v_0^2<=2*b()*(m()-z_0), b()>0, t>=0, A()>=0, v_0+A()*t>=0, t<=ep(), m()-z_0>=SB ==> (v_0+A()*t)^2<=2*b()*(m()-(z_0+v_0*t+A()/2*t^2))"
        .asSequent
  }

  it should "prove rbc controllability characterization with master" in withMathematica { _ =>
    val s = parseToSequent(
      getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/rbc-controllability-characterisation.kyx")
    )
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove rbc controllability corollary with tactic" in withMathematica { _ =>
    val s = parseToSequent(
      getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/rbc-controllability-corollary.kyx")
    )
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream(
          "/examples/casestudies/etcs/rephrased/rbc-controllability-corollary.kyt"
        ))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "prove rbc controllability lemma with master" in withQE { _ =>
    val s =
      parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/rbc-controllability-lemma.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove reactivity lemma with tactic" in withMathematica { _ =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/reactivity-lemma.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/reactivity-lemma.kyt"))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "prove full reactivity lemma with tactic" in withMathematica { _ =>
    val s =
      parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/reactivity-lemma-full.kyx"))
    val tactic = BelleParser(
      io.Source
        .fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/reactivity-lemma-full.kyt"))
        .mkString
    )
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  it should "prove safety lemma with master" in withMathematica { _ =>
    // @todo gets stuck with Z3
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove safety with piecewise constant actuation disturbance" in withMathematica { _ =>
    // @todo gets stuck with Z3
    val s = parseToSequent(
      getClass
        .getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma-disturbed-simplified-piecewise.kyx")
    )
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove safety with detailed brake model" in withQE { _ =>
    val entry = ArchiveParser
      .parse(
        Source
          .fromInputStream(
            getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma-extendedbraking.kyx")
          )
          .mkString
      )
      .head
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.loneElement._3) shouldBe Symbol("proved")
  }

  it should "prove safety with detailed brake model, no air resistance" in withQE { _ =>
    val entry = ArchiveParser
      .parse(
        Source
          .fromInputStream(
            getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma-brakingnoair.kyx")
          )
          .mkString
      )
      .head
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.loneElement._3) shouldBe Symbol("proved")
  }

//  "ETCS ModelPlex" should "synthesize a ctrl monitor from essentials" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx")
//    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val (modelplexInput, _) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
//      Variable("z"), Variable("t"), Variable("a"))
//    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & SimplifierV2.simpTac(1))
//    foResult.subgoals should have size 1
//    foResult.subgoals.head.ante shouldBe empty
//    foResult.subgoals.head.succ should contain only "m()-z<=v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&(v>=0&0<=ep())&SBpost()=v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost()=v&zpost()=z&tpost()=0&apost()=-b()|m()-z>=v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&(v>=0&0<=ep())&SBpost()=v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost()=v&zpost()=z&tpost()=0&apost()=A()".asFormula
//  }
//
//  it should "synthesize simplified ctrl monitor from essentials" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx")
//    val src = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val (model,proof) = SimplifierV2.rewriteLoopAux(src,List(Variable("SB")))
//    val (modelplexInput, _) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("v"), Variable("z"),
//      Variable("t"), Variable("a"))
//    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & SimplifierV2.simpTac(1))
//    foResult.subgoals should have size 1
//    foResult.subgoals.head.ante shouldBe empty
//    foResult.subgoals.head.succ should contain only "m()-z<=v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&(v>=0&0<=ep())&vpost()=v&zpost()=z&tpost()=0&apost()=-b()|m()-z>=v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&(v>=0&0<=ep())&vpost()=v&zpost()=z&tpost()=0&apost()=A()".asFormula
//  }
//
//  it should "synthesize a ctrl monitor from safety lemma" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma.kyx")
//    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("vdes"), Variable("SB"), Variable("v"),
//      Variable("em"), Variable("do"), Variable("z"), Variable("t"), Variable("mo"), Variable("m"), Variable("d"),
//      Variable("a"))
//
//    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
//      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & SimplifierV2.simpTac(1))
//    foResult.subgoals should have size 1
//    foResult.subgoals.head.ante shouldBe empty
//    foResult.subgoals.head.succ should contain only "((dpost()>=0&d^2-dpost()^2<=2*b()*(mpost()-m)&vdespost()>=0)&SBpost()=SB&vpost()=v&empost()=em&dopost()=d&zpost()=z&tpost()=t&mopost()=m&apost()=a|vdespost()=vdes&SBpost()=SB&vpost()=v&empost()=1&dopost()=do&zpost()=z&tpost()=t&mopost()=mo&mpost()=m&dpost()=d&apost()=a)|v<=vdes&(apost()>=-b()&apost()<=A())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|em=1)&(v>=0&0<=ep())&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&em!=1)&(v>=0&0<=ep())&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|em=1)&(v>=0&0<=ep())&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&em!=1)&(v>=0&0<=ep())&vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d)".asFormula
//  }
//
//  it should "synthesize a simplified ctrl monitor from safety lemma" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma.kyx")
//    val src = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val (model,proof) = SimplifierV2.rewriteLoopAux(src,List(Variable("SB")))
//    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("vdes"), Variable("v"),
//      Variable("em"), Variable("do"), Variable("z"), Variable("t"), Variable("mo"), Variable("m"), Variable("d"),
//      Variable("a"))
//
//    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
//      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & SimplifierV2.simpTac(1))
//
//    foResult.subgoals should have size 1
//    foResult.subgoals.head.ante shouldBe empty
//    foResult.subgoals.head.succ should contain only "((dpost()>=0&d^2-dpost()^2<=2*b()*(mpost()-m)&vdespost()>=0)&vpost()=v&empost()=em&dopost()=d&zpost()=z&tpost()=t&mopost()=m&apost()=a|vdespost()=vdes&vpost()=v&empost()=1&dopost()=do&zpost()=z&tpost()=t&mopost()=mo&mpost()=m&dpost()=d&apost()=a)|v<=vdes&(apost()>=-b()&apost()<=A())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|em=1)&(v>=0&0<=ep())&vdespost()=vdes&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&em!=1)&(v>=0&0<=ep())&vdespost()=vdes&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|em=1)&(v>=0&0<=ep())&vdespost()=vdes&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&em!=1)&(v>=0&0<=ep())&vdespost()=vdes&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d)".asFormula
//  }
//
//  it should "synthesize a model monitor from essentials" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials-explicitode.kyx")
//    val src = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val (model,proof) = SimplifierV2.rewriteLoopAux(src, List(Variable("SB")))
//    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("v"),
//      Variable("z"), Variable("t"), Variable("a"))
//
//    val foResult = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) &
//      DebuggingTactics.print("After chase") & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & DebuggingTactics.print("After Opt. 1")
//      & SimplifierV2.simpTac(1)) //@note simplification rewrites too many equalities into awkward conditions, e.g., ep=0&ep=tpost()&apost()+b=0 becomes apost()+b=tpost()
//
//    foResult.subgoals should have size 1
//    foResult.subgoals.head.ante shouldBe empty
//    foResult.subgoals.head.succ should contain only "m-z<=v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&((ep()=0&0=tpost())&((apost()=0&b()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&z=zpost())&v>0)|(apost()+b()=0&b()!=0)&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0))|ep()>0&((0=tpost()&((apost()=0&b()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&zpost()=z)&v>0)|(apost()+b()=0&b()!=0)&((v=0&vpost()=0)&zpost()=z|(v=vpost()&zpost()=z)&v>0))|(0 < tpost()&tpost() < ep())&(v=0&(((b() < 0&0=b()*tpost()+vpost())&0.5*b()*(-tpost())^2+zpost()=z)&apost()+b()=0|((b()=0&vpost()=0)&z=zpost())&apost()=0)|v>0&(((apost()=0&b()=0)&v=vpost())&zpost()=tpost()*v+z|((apost()+b()=0&v=b()*tpost()+vpost())&0.5*b()*(-tpost())^2+zpost()=tpost()*v+z)&(b()>0&b()+(-tpost())^-1*v<=0|b() < 0))))|ep()=tpost()&(v=0&(((b() < 0&0=b()*tpost()+vpost())&0.5*b()*(-tpost())^2+zpost()=z)&apost()+b()=0|((b()=0&vpost()=0)&z=zpost())&apost()=0)|v>0&(((apost()=0&b()=0)&v=vpost())&zpost()=tpost()*v+z|((apost()+b()=0&v=b()*tpost()+vpost())&0.5*b()*(-tpost())^2+zpost()=tpost()*v+z)&(b()>0&b()<=ep()^-1*v|b() < 0)))))|m-z>=v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&((ep()=0&0=tpost())&((A()=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&z=zpost())&v>0)|(A()=apost()&A()!=0)&((v=0&vpost()=0)&zpost()=z|(v=vpost()&zpost()=z)&v>0))|ep()>0&((0=tpost()&((A()=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&zpost()=z)&v>0)|(A()=apost()&A()!=0)&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0))|(0 < tpost()&tpost() < ep())&(v=0&(((A()=0&vpost()=0)&z=zpost())&apost()=0|((A()>0&vpost()=A()*tpost())&zpost()=0.5*A()*(-tpost())^2+z)&A()=apost())|v>0&(((A()=0&apost()=0)&v=vpost())&zpost()=tpost()*v+z|((A()=apost()&vpost()=A()*tpost()+v)&zpost()=0.5*A()*(-tpost())^2+tpost()*v+z)&(A() < 0&(-tpost())^-1*v<=A()|A()>0))))|ep()=tpost()&(v=0&(((A()=0&vpost()=0)&z=zpost())&apost()=0|((A()>0&vpost()=A()*tpost())&zpost()=0.5*A()*(-tpost())^2+z)&A()=apost())|v>0&(((A()=0&apost()=0)&v=vpost())&zpost()=tpost()*v+z|((A()=apost()&vpost()=A()*tpost()+v)&zpost()=0.5*A()*(-tpost())^2+tpost()*v+z)&(A() < 0&A()+ep()^-1*v>=0|A()>0)))))".asFormula
//  }
//
//  "ETCS Euler ModelPlex" should "extract model monitor from detailed braking" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma-extendedbraking.kyx")
//    val src = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val (model,proof) = SimplifierV2.rewriteLoopAux(src, List(Variable("SB")))
//    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("do"),
//      Variable("mo"), Variable("d"), Variable("m"), Variable("vdes"), Variable("em"), Variable("Ib"), Variable("Tw"),
//      Variable("SB"), Variable("t"), Variable("z"), Variable("v"))
//
//    val tactic = ModelPlex.modelMonitorByChase(ModelPlex.eulerSystemAllIn)(1) &
//      DebuggingTactics.print("Euler-approximate system result") & Idioms.<(
//      ModelPlex.unrollLoop(1)(1) & (ModelPlex.chaseEulerAssignments(1)*),
//      skip, skip, skip, skip)
//
//    val result = proveBy(modelplexInput, tactic)
//    result.subgoals should have size 5 // ignore all but first branch (open because Euler "axiom" is not an axiom)
//    val flipped = ModelPlex.flipUniversalEulerQuantifiers(result.subgoals.head.succ.head)
//    val simplifier = SimplifierV3.simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
//    val simplified = proveBy(flipped, ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1) & simplifier(1))
//    simplified.subgoals should have size 1
//    simplified.subgoals.head.ante shouldBe empty
//    simplified.subgoals.head.succ should contain only "((dpost()>=0&d^2-dpost()^2<=2*(voff()*sbsc()/ms())*(mpost()-m)&vdespost()>=0)&dopost()=d&mopost()=m&empost()=em&Ibpost()=Ib&Twpost()=Tw&SBpost()=SB&tpost()=t&zpost()=z&vpost()=v|dopost()=do&mopost()=mo&dpost()=d&mpost()=m&vdespost()=vdes&empost()=1&Ibpost()=Ib&Twpost()=Tw&SBpost()=SB&tpost()=t&zpost()=z&vpost()=v)|v<=vdes&(0<=Twpost()&Twpost()<=A())&((m-z<=(v^2-d^2)/(2*voff()*sbsc()/ms())+(A()/ms()/(voff()*sbsc()/ms())+1)*(A()/ms()/2*ep()^2+ep()*v)|em=1)&1<=Ibpost()&tpost_0()>=0&epost_0()>0&h0post_0()>0&0 < hpost_0()&hpost_0() < h0post_0()&(z+hpost_0()*v-zpost())^2+(v+hpost_0()*((Ft(0)-Fe(v)-Fb(v*(Ibpost()-1)))/ms())-vpost())^2+(hpost_0()-tpost())^2 < epost_0()^2&dopost()=do&mopost()=mo&dpost()=d&mpost()=m&vdespost()=vdes&empost()=em&Twpost()=0&SBpost()=SB|!(m-z<=(v^2-d^2)/(2*voff()*sbsc()/ms())+(A()/ms()/(voff()*sbsc()/ms())+1)*(A()/ms()/2*ep()^2+ep()*v)|em=1)&tpost_0()>=0&epost_0()>0&h0post_0()>0&0 < hpost_0()&hpost_0() < h0post_0()&(z+hpost_0()*v-zpost())^2+(v+hpost_0()*((Ft(Twpost())-Fe(v)-Fb(0))/ms())-vpost())^2+(hpost_0()-tpost())^2 < epost_0()^2&dopost()=do&mopost()=mo&dpost()=d&mpost()=m&vdespost()=vdes&empost()=em&Ibpost()=1&SBpost()=SB)|v>=vdes&1<=Ibpost()&((m-z<=(v^2-d^2)/(2*voff()*sbsc()/ms())+(A()/ms()/(voff()*sbsc()/ms())+1)*(A()/ms()/2*ep()^2+ep()*v)|em=1)&tpost_0()>=0&epost_0()>0&h0post_0()>0&0 < hpost_0()&hpost_0() < h0post_0()&(z+hpost_0()*v-zpost())^2+(v+hpost_0()*((Ft(0)-Fe(v)-Fb(v*(Ibpost()-1)))/ms())-vpost())^2+(hpost_0()-tpost())^2 < epost_0()^2&dopost()=do&mopost()=mo&dpost()=d&mpost()=m&vdespost()=vdes&empost()=em&Twpost()=0&SBpost()=SB|!(m-z<=(v^2-d^2)/(2*voff()*sbsc()/ms())+(A()/ms()/(voff()*sbsc()/ms())+1)*(A()/ms()/2*ep()^2+ep()*v)|em=1)&tpost_0()>=0&epost_0()>0&h0post_0()>0&0 < hpost_0()&hpost_0() < h0post_0()&(z+hpost_0()*v-zpost())^2+(v+hpost_0()*((Ft(0)-Fe(v)-Fb(v*(Ibpost()-1)))/ms())-vpost())^2+(hpost_0()-tpost())^2 < epost_0()^2&dopost()=do&mopost()=mo&dpost()=d&mpost()=m&vdespost()=vdes&empost()=em&Twpost()=0&SBpost()=SB)".asFormula
//  }
//
//  "ETCS formula metric" should "convert controller monitor" in withMathematica { tool =>
//    val fml = "((dpost()>=0&d^2-dpost()^2<=2*b()*(mpost()-m)&vdespost()>=0)&vpost()=v&empost()=em&dopost()=d&zpost()=z&tpost()=t&mopost()=m&apost()=a|vdespost()=vdes&vpost()=v&empost()=1&dopost()=do&zpost()=z&tpost()=t&mopost()=mo&mpost()=m&dpost()=d&apost()=a)|v<=vdes&(apost()>=-b()&apost()<=A())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|em=1)&(v>=0&0<=ep())&vdespost()=vdes&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&em!=1)&(v>=0&0<=ep())&vdespost()=vdes&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b())&((m-z<=(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)|em=1)&(v>=0&0<=ep())&vdespost()=vdes&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d&apost()=-b()|(m-z>(v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v)&em!=1)&(v>=0&0<=ep())&vdespost()=vdes&vpost()=v&empost()=em&dopost()=do&zpost()=z&tpost()=0&mopost()=mo&mpost()=m&dpost()=d)".asFormula
//    val metric = ModelPlex.toMetric(fml)
//    metric shouldBe "min((min((max((max((0-dpost(),max((d*d+-dpost()*dpost()-2*b()*(mpost()+-m),0-vdespost())))),max((max((vpost()-v,v-vpost())),max((max((empost()-em,em-empost())),max((max((dopost()-d,d-dopost())),max((max((zpost()-z,z-zpost())),max((max((tpost()-t,t-tpost())),max((max((mopost()-m,m-mopost())),max((apost()-a,a-apost())))))))))))))))),max((max((vdespost()-vdes,vdes-vdespost())),max((max((vpost()-v,v-vpost())),max((max((empost()-1,1-empost())),max((max((dopost()-do,do-dopost())),max((max((zpost()-z,z-zpost())),max((max((tpost()-t,t-tpost())),max((max((mopost()-mo,mo-mopost())),max((max((mpost()-m,m-mpost())),max((max((dpost()-d,d-dpost())),max((apost()-a,a-apost())))))))))))))))))))))),min((max((v-vdes,max((max((-b()-apost(),apost()-A())),min((max((min((m+-z-((v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*(ep()*ep())+ep()*v)),max((em-1,1-em)))),max((max((0-v,0-ep())),max((max((vdespost()-vdes,vdes-vdespost())),max((max((vpost()-v,v-vpost())),max((max((empost()-em,em-empost())),max((max((dopost()-do,do-dopost())),max((max((zpost()-z,z-zpost())),max((max((tpost(),0-tpost())),max((max((mopost()-mo,mo-mopost())),max((max((mpost()-m,m-mpost())),max((max((dpost()-d,d-dpost())),max((apost()--b(),-b()-apost())))))))))))))))))))))))),max((max(((v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*(ep()*ep())+ep()*v)-(m+-z),min((1-em,em-1)))),max((max((0-v,0-ep())),max((max((vdespost()-vdes,vdes-vdespost())),max((max((vpost()-v,v-vpost())),max((max((empost()-em,em-empost())),max((max((dopost()-do,do-dopost())),max((max((zpost()-z,z-zpost())),max((max((tpost(),0-tpost())),max((max((mopost()-mo,mo-mopost())),max((max((mpost()-m,m-mpost())),max((dpost()-d,d-dpost())))))))))))))))))))))))))))),max((vdes-v,max((max((apost(),-b()-apost())),min((max((min((m+-z-((v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*(ep()*ep())+ep()*v)),max((em-1,1-em)))),max((max((0-v,0-ep())),max((max((vdespost()-vdes,vdes-vdespost())),max((max((vpost()-v,v-vpost())),max((max((empost()-em,em-empost())),max((max((dopost()-do,do-dopost())),max((max((zpost()-z,z-zpost())),max((max((tpost(),0-tpost())),max((max((mopost()-mo,mo-mopost())),max((max((mpost()-m,m-mpost())),max((max((dpost()-d,d-dpost())),max((apost()--b(),-b()-apost())))))))))))))))))))))))),max((max(((v^2-d^2)/(2*b())+(A()/b()+1)*(A()/2*(ep()*ep())+ep()*v)-(m+-z),min((1-em,em-1)))),max((max((0-v,0-ep())),max((max((vdespost()-vdes,vdes-vdespost())),max((max((vpost()-v,v-vpost())),max((max((empost()-em,em-empost())),max((max((dopost()-do,do-dopost())),max((max((zpost()-z,z-zpost())),max((max((tpost(),0-tpost())),max((max((mopost()-mo,mo-mopost())),max((max((mpost()-m,m-mpost())),max((dpost()-d,d-dpost())))))))))))))))))))))))))))))))) < 0".asFormula
//
//    val ts = new TestSynthesis(tool)
//    // search for sunshine test case values (initial+expected)
//    val testConfig = ts.synthesizeTestConfig(fml, 2, Some(20))
//    testConfig should have size 2
//    testConfig.foreach(_.keys.map({case v: Variable => v case FuncOf(fn, _) => fn})
//      should contain theSameElementsAs StaticSemantics.symbols(fml))
//
//    // compute safety margin of test case
//    val safetyMargin = ts.synthesizeSafetyMarginCheck(fml, testConfig.head)
//    safetyMargin shouldBe "0".asTerm //@note first findInstance result is usually exactly at the boundary
//  }
//
//  it should "convert model monitor" in withMathematica { _ =>
//    val fml = "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(((ep=0&0=tpost())&apost()+b=0)&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0)|(ep>0&apost()+b=0)&(((v=b*tpost()+vpost()&b*(-1*tpost())^2+2*(-1*tpost()*v+-1*z+zpost())=0)&v>0)&((ep=tpost()&b<=ep^-1*v|0=tpost())|(tpost() < ep&0 < tpost())&b*tpost()<=v)|((0=tpost()&v=0)&vpost()=0)&2*zpost()=2*z))|m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((ep=0&0=tpost())&((A=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&z=zpost())&v>0)|(A=apost()&A>0)&((v=0&vpost()=0)&zpost()=z|(v=vpost()&zpost()=z)&v>0))|ep>0&(((A=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&zpost()=tpost()*v+z)&v>0))&((ep=tpost()|0=tpost())|0 < tpost()&tpost() < ep)|(A=apost()&A>0)&(((v=0&vpost()=A*tpost())&zpost()=1/2*A*(-1*tpost())^2+z|(vpost()=A*tpost()+v&zpost()=1/2*A*(-1*tpost())^2+tpost()*v+z)&v>0)&(ep=tpost()|0 < tpost()&tpost() < ep)|0=tpost()&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0))))".asFormula
//    val metric = ModelPlex.toMetric(fml)
//    metric shouldBe "min((max((m+-z-(v^2/(2*b)+(A/b+1)*(A/2*(ep*ep)+ep*v)),min((max((max((max((max((ep,0-ep)),max((0-tpost(),tpost())))),max((apost()+b,0-(apost()+b))))),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((zpost()-z,z-zpost())))),max((max((max((vpost()-v,v-vpost())),max((zpost()-z,z-zpost())))),0-v)))))),max((max((0-ep,max((apost()+b,0-(apost()+b))))),min((max((max((max((max((v-(b*tpost()+vpost()),b*tpost()+vpost()-v)),max((b*(-1*tpost()*(-1*tpost()))+2*(-1*tpost()*v+-1*z+zpost()),0-(b*(-1*tpost()*(-1*tpost()))+2*(-1*tpost()*v+-1*z+zpost())))))),0-v)),min((min((max((max((ep-tpost(),tpost()-ep)),b-ep^-1*v)),max((0-tpost(),tpost())))),max((max((tpost()-ep,0-tpost())),b*tpost()-v)))))),max((max((max((max((0-tpost(),tpost())),max((v,0-v)))),max((vpost(),0-vpost())))),max((2*zpost()-2*z,2*z-2*zpost())))))))))))),max((v^2/(2*b)+(A/b+1)*(A/2*(ep*ep)+ep*v)-(m+-z),min((max((max((max((ep,0-ep)),max((0-tpost(),tpost())))),min((max((max((max((A,0-A)),max((apost(),0-apost())))),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((z-zpost(),zpost()-z)))),max((max((max((v-vpost(),vpost()-v)),max((z-zpost(),zpost()-z)))),0-v)))))),max((max((max((A-apost(),apost()-A)),0-A)),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((zpost()-z,z-zpost())))),max((max((max((v-vpost(),vpost()-v)),max((zpost()-z,z-zpost())))),0-v)))))))))),max((0-ep,min((max((max((max((max((A,0-A)),max((apost(),0-apost())))),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((z-zpost(),zpost()-z)))),max((max((max((v-vpost(),vpost()-v)),max((zpost()-(tpost()*v+z),tpost()*v+z-zpost())))),0-v)))))),min((min((max((ep-tpost(),tpost()-ep)),max((0-tpost(),tpost())))),max((0-tpost(),tpost()-ep)))))),max((max((max((A-apost(),apost()-A)),0-A)),min((max((min((max((max((max((v,0-v)),max((vpost()-A*tpost(),A*tpost()-vpost())))),max((zpost()-(1/2*A*(-1*tpost()*(-1*tpost()))+z),1/2*A*(-1*tpost()*(-1*tpost()))+z-zpost())))),max((max((max((vpost()-(A*tpost()+v),A*tpost()+v-vpost())),max((zpost()-(1/2*A*(-1*tpost()*(-1*tpost()))+tpost()*v+z),1/2*A*(-1*tpost()*(-1*tpost()))+tpost()*v+z-zpost())))),0-v)))),min((max((ep-tpost(),tpost()-ep)),max((0-tpost(),tpost()-ep)))))),max((max((0-tpost(),tpost())),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((zpost()-z,z-zpost())))),max((max((max((vpost()-v,v-vpost())),max((zpost()-z,z-zpost())))),0-v)))))))))))))))))))) < 0".asFormula
//  }
//
//  "ETCS test case synthesis" should "derive controller tests from essentials" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx")
//    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val (modelplexInput, _) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
//      Variable("z"), Variable("t"), Variable("a"))
//    val fml = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
//      //@note do not convert rationals into numbers
//      SimplifierV3.simpTac(Nil, SimplifierV3.defaultFaxs, SimplifierV3.arithBaseIndex)(1)).subgoals.head.succ.head
//
//    val ts = new TestSynthesis(tool)
//    // search for sunshine test case values (initial+expected)
//    val testConfig = ts.synthesizeTestConfig(fml, 2, Some(20))
//    testConfig should have size 2
//    testConfig.foreach(_.keys.map({case v: Variable => v case FuncOf(fn, _) => fn})
//      should contain theSameElementsAs StaticSemantics.symbols(fml))
//  }
//
//  it should "derive model tests from essentials" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials-explicitode.kyx")
//    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val vars = StaticSemantics.boundVars(model).symbols.filter(_.isInstanceOf[BaseVariable]).toList
//    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, vars:_*)
//    val fml = proveBy(modelplexInput,
//      ModelPlex.modelMonitorByChase(1) &
//      SimplifierV3.simpTac(Nil, SimplifierV3.defaultFaxs, SimplifierV3.arithBaseIndex)(1) &
//      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1)
//    ).subgoals.head.succ.head
//
//    val ts = new TestSynthesis(tool)
//    // search for sunshine test case values (initial+expected)
//    val testConfig = ts.synthesizeTestConfig(fml, 1, Some(20))
//    testConfig should have size 1
//    testConfig.foreach(_.keys.map({case v: Variable => v case FuncOf(fn, _) => fn})
//      should contain theSameElementsAs StaticSemantics.symbols(fml))
//
//    val assumptionsCond = assumptions.reduceOption(And).getOrElse(True)
//    val metric = ModelPlex.toMetric(And(assumptionsCond, fml))
//    val synth = new TestSynthesis(tool)
//    // fml divides by tpost() and by ep
//    if (testConfig.head("tpost()".asTerm) == "0".asTerm || testConfig.head("ep".asTerm) == "0".asTerm) {
//      a[ToolException] should be thrownBy synth.synthesizeSafetyMarginCheck(metric, testConfig.head)
//    } else {
//      synth.synthesizeSafetyMarginCheck(metric, testConfig.head) shouldBe a [Number]
//    }
//  }
//
//  "ETCS code generation" should "synthesize C code from essentials ctrl monitor" in withMathematica { tool =>
//    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx")
//    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
//    val (modelplexInput, _) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
//      Variable("z"), Variable("t"), Variable("a"))
//    val monitorCond = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & SimplifierV2.simpTac(1))
//    monitorCond.subgoals should have size 1
//    monitorCond.subgoals.head.ante shouldBe empty
//    monitorCond.subgoals.head.succ should have size 1
//    val code = CGenerator(monitorCond.subgoals.head.succ.head)
//    code should equal ("""
//      |/**************************
//      | * Generated by KeYmaera X
//      | **************************/
//      |
//      |#include <math.h>
//      |#include <stdbool.h>
//      |
//      |/* function declaration */
//      |long double A();
//      |long double SBpost();
//      |long double apost();
//      |long double b();
//      |long double ep();
//      |long double m();
//      |long double tpost();
//      |long double v();
//      |long double vpost();
//      |long double z();
//      |long double zpost();
//      |
//      |/* monitor */
//      |bool monitor () {
//      |  return ((((m()) - (z()))<=(((((v())*(v())))/(((2))*(b()))) + ((((A())/(b())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*(v()))))))&&((((v())>=((0)))&&(((0))<=(ep())))&&(((SBpost())==(((((v())*(v())))/(((2))*(b()))) + ((((A())/(b())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*(v()))))))&&(((vpost())==(v()))&&(((zpost())==(z()))&&(((tpost())==((0)))&&((apost())==(-(b())))))))))||((((m()) - (z()))>=(((((v())*(v())))/(((2))*(b()))) + ((((A())/(b())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*(v()))))))&&((((v())>=((0)))&&(((0))<=(ep())))&&(((SBpost())==(((((v())*(v())))/(((2))*(b()))) + ((((A())/(b())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*(v()))))))&&(((vpost())==(v()))&&(((zpost())==(z()))&&(((tpost())==((0)))&&((apost())==(A()))))))));
//      |}
//      |
//      |""".stripMargin) (after being whiteSpaceRemoved)
//  }

}
