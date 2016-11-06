/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.codegen.CGenerator
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps

/**
  * ETCS test cases.
  * Essentials of European Train Control System (ETCS).
  * @see "Andre Platzer, Jan-David Quesel. European Train Control System: A case study in formal verification. ICFEM, 2009"
  * @see "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages 143-189, 2008."
  * @author Stefan Mitsch
  */
@SlowTest
class Etcs extends TacticTestBase {

  "ETCS controllability" should "prove lemma with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/controllability-lemma.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove RBC characterisation with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rbc-controllability-characterisation.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove RBC corollary with tactic" ignore withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rbc-controllability-corollary.kyx"))
    //@todo write tactic
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove RBC lemma with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rbc-controllability-lemma.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  "ETCS reactivity" should "prove lemma with tactic" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove full lemma with tactic" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma-full.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma-full.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  "ETCS" should "prove essentials with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/ETCS-essentials.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  "Rephrased ETCS models" should "prove controllability lemma with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/controllability-lemma.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove essentials with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove rbc controllability characterization with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/rbc-controllability-characterisation.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove rbc controllability corollary with master" ignore withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/rbc-controllability-corollary.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove rbc controllability lemma with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/rbc-controllability-lemma.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove reactivity lemma with tactic" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/reactivity-lemma.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/reactivity-lemma.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove full reactivity lemma with tactic" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/reactivity-lemma-full.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/reactivity-lemma-full.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove safety lemma with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  "ETCS ModelPlex" should "synthesize a ctrl monitor from essentials" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
      Variable("z"), Variable("t"), Variable("a"))
    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & SimplifierV2.simpTac(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&(((SBpost()=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v)&zpost()=z)&tpost()=0)&apost()=-b|m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&(((SBpost()=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v)&zpost()=z)&tpost()=0)&apost()=A".asFormula
  }

  it should "synthesize simplified ctrl monitor from essentials" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx")
    val src = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (model,proof) = SimplifierV2.rewriteLoopAux(src,List(Variable("SB")))
    val (modelplexInput, _) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("v"), Variable("z"),
      Variable("t"), Variable("a"))
    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & SimplifierV2.simpTac(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only ("m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((vpost()=v&zpost()=z)&tpost()=0)&apost()=-b|" +
      "m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&((vpost()=v&zpost()=z)&tpost()=0)&apost()=A").asFormula
  }

  it should "synthesize a ctrl monitor from safety lemma" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("vdes"), Variable("SB"), Variable("v"),
      Variable("em"), Variable("do"), Variable("z"), Variable("t"), Variable("mo"), Variable("m"), Variable("d"),
      Variable("a"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(tool, assumptions)(1) & SimplifierV2.simpTac(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&((((((SBpost()=SB&vpost()=v)&empost()=em)&dopost()=d)&zpost()=z)&tpost()=t)&mopost()=m)&apost()=a|(((((((((vdespost()=vdes&SBpost()=SB)&vpost()=v)&empost()=1)&dopost()=do)&zpost()=z)&tpost()=t)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|(m-z>(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&em!=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|(m-z>(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&em!=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)".asFormula
  }

  it should "synthesize a simplified ctrl monitor from safety lemma" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma.kyx")
    val src = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (model,proof) = SimplifierV2.rewriteLoopAux(src,List(Variable("SB")))
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("vdes"), Variable("v"),
      Variable("em"), Variable("do"), Variable("z"), Variable("t"), Variable("mo"), Variable("m"), Variable("d"),
      Variable("a"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(tool, assumptions)(1) & SimplifierV2.simpTac(1))

    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&(((((vpost()=v&empost()=em)&dopost()=d)&zpost()=z)&tpost()=t)&mopost()=m)&apost()=a|((((((((vdespost()=vdes&vpost()=v)&empost()=1)&dopost()=do)&zpost()=z)&tpost()=t)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|(m-z>(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&em!=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|(m-z>(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&em!=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)".asFormula
  }

  it should "synthesize a model monitor from essentials" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials-explicitode.kyx")
    val src = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (model,proof) = SimplifierV2.rewriteLoopAux(src, List(Variable("SB")))
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("v"),
      Variable("z"), Variable("t"), Variable("a"))

    val foResult = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) &
      DebuggingTactics.print("After chase") & ModelPlex.optimizationOneWithSearch(tool, assumptions)(1) & DebuggingTactics.print("After Opt. 1")
      & SimplifierV2.simpTac(1)) //@note simplification rewrites too many equalities into awkward conditions, e.g., ep=0&ep=tpost()&apost()+b=0 becomes apost()+b=tpost()

    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(((ep=0&0=tpost())&apost()+b=0)&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0)|(ep>0&apost()+b=0)&(((v=b*tpost()+vpost()&b*(-1*tpost())^2+2*(-1*tpost()*v+-1*z+zpost())=0)&v>0)&((ep=tpost()&b<=ep^-1*v|0=tpost())|(tpost() < ep&0 < tpost())&b*tpost()<=v)|((0=tpost()&v=0)&vpost()=0)&2*zpost()=2*z))|m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((ep=0&0=tpost())&((A=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&z=zpost())&v>0)|(A=apost()&A>0)&((v=0&vpost()=0)&zpost()=z|(v=vpost()&zpost()=z)&v>0))|ep>0&(((A=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&zpost()=tpost()*v+z)&v>0))&((ep=tpost()|0=tpost())|0 < tpost()&tpost() < ep)|(A=apost()&A>0)&(((v=0&vpost()=A*tpost())&zpost()=1/2*A*(-1*tpost())^2+z|(vpost()=A*tpost()+v&zpost()=1/2*A*(-1*tpost())^2+tpost()*v+z)&v>0)&(ep=tpost()|0 < tpost()&tpost() < ep)|0=tpost()&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0))))".asFormula
  }

  "ETCS code generation" should "synthesize C code from essentials ctrl monitor" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
      Variable("z"), Variable("t"), Variable("a"))
    val monitorCond = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & SimplifierV2.simpTac(1))
    monitorCond.subgoals should have size 1
    monitorCond.subgoals.head.ante shouldBe empty
    monitorCond.subgoals.head.succ should have size 1
    val code = CGenerator(monitorCond.subgoals.head.succ.head)
    code should equal ("""
      |/**************************
      | * Generated by KeYmaera X
      | **************************/
      |
      |#include <math.h>
      |#include <stdbool.h>
      |
      |/* function declaration */
      |long double A();
      |long double SBpost();
      |long double apost();
      |long double b();
      |long double ep();
      |long double m();
      |long double tpost();
      |long double v();
      |long double vpost();
      |long double z();
      |long double zpost();
      |
      |/* monitor */
      |bool monitor () {
      |  return ((((m()) - (z()))<=(((((v())*(v())))/(((2))*(b()))) + ((((A())/(b())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*(v()))))))&&((((v())>=((0)))&&(((0))<=(ep())))&&((((((SBpost())==(((((v())*(v())))/(((2))*(b()))) + ((((A())/(b())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*(v()))))))&&((vpost())==(v())))&&((zpost())==(z())))&&((tpost())==((0))))&&((apost())==(-(b()))))))||((((m()) - (z()))>=(((((v())*(v())))/(((2))*(b()))) + ((((A())/(b())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*(v()))))))&&((((v())>=((0)))&&(((0))<=(ep())))&&((((((SBpost())==(((((v())*(v())))/(((2))*(b()))) + ((((A())/(b())) + ((1)))*((((A())/((2)))*(((ep())*(ep())))) + ((ep())*(v()))))))&&((vpost())==(v())))&&((zpost())==(z())))&&((tpost())==((0))))&&((apost())==(A())))));
      |}
      |
      |""".stripMargin) (after being whiteSpaceRemoved)
  }

}
