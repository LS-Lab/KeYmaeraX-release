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
import edu.cmu.cs.ls.keymaerax.tools.TestSynthesis
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

  it should "prove essentials with tactic from file with Mathematica" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove essentials with tactic from file with Z3" in withZ3 { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "find SB condition in essentials" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials-bare.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials-bare.kyt")).mkString)
    val result = proveBy(s, tactic)
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("v_1^2<=2*b*(m-z_0)".asFormula, "b>0".asFormula, "A>=0".asFormula,
      "m-z_0>=SB".asFormula, "t>=0".asFormula, "v_1+A*t>=0".asFormula, "t<=ep".asFormula)
    result.subgoals.head.succ should contain only "(v_1+A*t)^2<=2*b*(m-(z_0+v_1*t+A/2*t^2))".asFormula
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
    foResult.subgoals.head.succ should contain only "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(((ep=0&0=tpost())&apost()+b=0)&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0)|(ep>0&apost()+b=0)&(((v=b*tpost()+vpost()&b*(-tpost())^2+2*((-tpost())*v+-z+zpost())=0)&v>0)&((ep=tpost()&b<=ep^-1*v|0=tpost())|(tpost() < ep&0 < tpost())&b*tpost()<=v)|((0=tpost()&v=0)&vpost()=0)&2*zpost()=2*z))|m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((ep=0&0=tpost())&((A=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&z=zpost())&v>0)|(A=apost()&A>0)&((v=0&vpost()=0)&zpost()=z|(v=vpost()&zpost()=z)&v>0))|ep>0&(((A=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&zpost()=tpost()*v+z)&v>0))&((ep=tpost()|0=tpost())|0 < tpost()&tpost() < ep)|(A=apost()&A>0)&(((v=0&vpost()=A*tpost())&zpost()=0.5*A*(-tpost())^2+z|(vpost()=A*tpost()+v&zpost()=0.5*A*(-tpost())^2+tpost()*v+z)&v>0)&(ep=tpost()|0 < tpost()&tpost() < ep)|0=tpost()&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0))))".asFormula
  }

  "ETCS formula metric" should "convert controller monitor" in withMathematica { tool =>
    val fml = "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&(((((vpost()=v&empost()=em)&dopost()=d)&zpost()=z)&tpost()=t)&mopost()=m)&apost()=a|((((((((vdespost()=vdes&vpost()=v)&empost()=1)&dopost()=do)&zpost()=z)&tpost()=t)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|(m-z>(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&em!=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|(m-z>(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&em!=1)&(v>=0&0<=ep)&(((((((vdespost()=vdes&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)".asFormula
    val metric = ModelPlex.toMetric(fml)
    metric shouldBe "min((min((max((max((0-dpost(),max((d*d+-dpost()*dpost()-2*b*(mpost()+-m),0-vdespost())))),max((max((max((max((max((max((max((vpost()-v,v-vpost())),max((empost()-em,em-empost())))),max((dopost()-d,d-dopost())))),max((zpost()-z,z-zpost())))),max((tpost()-t,t-tpost())))),max((mopost()-m,m-mopost())))),max((apost()-a,a-apost())))))),max((max((max((max((max((max((max((max((max((max((vdespost()-vdes,vdes-vdespost())),max((vpost()-v,v-vpost())))),max((empost()-1,1-empost())))),max((dopost()-do,do-dopost())))),max((zpost()-z,z-zpost())))),max((tpost()-t,t-tpost())))),max((mopost()-mo,mo-mopost())))),max((mpost()-m,m-mpost())))),max((dpost()-d,d-dpost())))),max((apost()-a,a-apost())))))),min((max((v-vdes,max((max((-b-apost(),apost()-A)),min((max((min((m+-z-((v^2-d^2)/(2*b)+(A/b+1)*(A/2*(ep*ep)+ep*v)),max((em-1,1-em)))),max((max((0-v,0-ep)),max((max((max((max((max((max((max((max((max((max((vdespost()-vdes,vdes-vdespost())),max((vpost()-v,v-vpost())))),max((empost()-em,em-empost())))),max((dopost()-do,do-dopost())))),max((zpost()-z,z-zpost())))),max((tpost(),0-tpost())))),max((mopost()-mo,mo-mopost())))),max((mpost()-m,m-mpost())))),max((dpost()-d,d-dpost())))),max((apost()--b,-b-apost())))))))),max((max(((v^2-d^2)/(2*b)+(A/b+1)*(A/2*(ep*ep)+ep*v)-(m+-z),min((1-em,em-1)))),max((max((0-v,0-ep)),max((max((max((max((max((max((max((max((max((vdespost()-vdes,vdes-vdespost())),max((vpost()-v,v-vpost())))),max((empost()-em,em-empost())))),max((dopost()-do,do-dopost())))),max((zpost()-z,z-zpost())))),max((tpost(),0-tpost())))),max((mopost()-mo,mo-mopost())))),max((mpost()-m,m-mpost())))),max((dpost()-d,d-dpost())))))))))))))),max((vdes-v,max((max((apost(),-b-apost())),min((max((min((m+-z-((v^2-d^2)/(2*b)+(A/b+1)*(A/2*(ep*ep)+ep*v)),max((em-1,1-em)))),max((max((0-v,0-ep)),max((max((max((max((max((max((max((max((max((max((vdespost()-vdes,vdes-vdespost())),max((vpost()-v,v-vpost())))),max((empost()-em,em-empost())))),max((dopost()-do,do-dopost())))),max((zpost()-z,z-zpost())))),max((tpost(),0-tpost())))),max((mopost()-mo,mo-mopost())))),max((mpost()-m,m-mpost())))),max((dpost()-d,d-dpost())))),max((apost()--b,-b-apost())))))))),max((max(((v^2-d^2)/(2*b)+(A/b+1)*(A/2*(ep*ep)+ep*v)-(m+-z),min((1-em,em-1)))),max((max((0-v,0-ep)),max((max((max((max((max((max((max((max((max((vdespost()-vdes,vdes-vdespost())),max((vpost()-v,v-vpost())))),max((empost()-em,em-empost())))),max((dopost()-do,do-dopost())))),max((zpost()-z,z-zpost())))),max((tpost(),0-tpost())))),max((mopost()-mo,mo-mopost())))),max((mpost()-m,m-mpost())))),max((dpost()-d,d-dpost())))))))))))))))))) < 0".asFormula

    val ts = new TestSynthesis(tool)
    // search for sunshine test case values (initial+expected)
    val testConfig = ts.synthesizeTestConfig(fml, 2, Some(20))
    testConfig should have size 2
    testConfig.foreach(_.keys.map({case v: Variable => v case FuncOf(fn, _) => fn})
      should contain theSameElementsAs StaticSemantics.symbols(fml))

    // compute safety margin of test case
    val safetyMargin = ts.synthesizeSafetyMarginCheck(fml, testConfig.head)
    safetyMargin shouldBe "0".asTerm //@note first findInstance result is usually exactly at the boundary
  }

  it should "convert model monitor" in withMathematica { tool =>
    val fml = "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(((ep=0&0=tpost())&apost()+b=0)&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0)|(ep>0&apost()+b=0)&(((v=b*tpost()+vpost()&b*(-1*tpost())^2+2*(-1*tpost()*v+-1*z+zpost())=0)&v>0)&((ep=tpost()&b<=ep^-1*v|0=tpost())|(tpost() < ep&0 < tpost())&b*tpost()<=v)|((0=tpost()&v=0)&vpost()=0)&2*zpost()=2*z))|m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&((ep=0&0=tpost())&((A=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&z=zpost())&v>0)|(A=apost()&A>0)&((v=0&vpost()=0)&zpost()=z|(v=vpost()&zpost()=z)&v>0))|ep>0&(((A=0&apost()=0)&((v=0&vpost()=0)&z=zpost()|(v=vpost()&zpost()=tpost()*v+z)&v>0))&((ep=tpost()|0=tpost())|0 < tpost()&tpost() < ep)|(A=apost()&A>0)&(((v=0&vpost()=A*tpost())&zpost()=1/2*A*(-1*tpost())^2+z|(vpost()=A*tpost()+v&zpost()=1/2*A*(-1*tpost())^2+tpost()*v+z)&v>0)&(ep=tpost()|0 < tpost()&tpost() < ep)|0=tpost()&((v=0&vpost()=0)&zpost()=z|(vpost()=v&zpost()=z)&v>0))))".asFormula
    val metric = ModelPlex.toMetric(fml)
    metric shouldBe "min((max((m+-z-(v^2/(2*b)+(A/b+1)*(A/2*(ep*ep)+ep*v)),min((max((max((max((max((ep,0-ep)),max((0-tpost(),tpost())))),max((apost()+b,0-(apost()+b))))),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((zpost()-z,z-zpost())))),max((max((max((vpost()-v,v-vpost())),max((zpost()-z,z-zpost())))),0-v)))))),max((max((0-ep,max((apost()+b,0-(apost()+b))))),min((max((max((max((max((v-(b*tpost()+vpost()),b*tpost()+vpost()-v)),max((b*(-1*tpost()*(-1*tpost()))+2*(-1*tpost()*v+-1*z+zpost()),0-(b*(-1*tpost()*(-1*tpost()))+2*(-1*tpost()*v+-1*z+zpost())))))),0-v)),min((min((max((max((ep-tpost(),tpost()-ep)),b-ep^-1*v)),max((0-tpost(),tpost())))),max((max((tpost()-ep,0-tpost())),b*tpost()-v)))))),max((max((max((max((0-tpost(),tpost())),max((v,0-v)))),max((vpost(),0-vpost())))),max((2*zpost()-2*z,2*z-2*zpost())))))))))))),max((v^2/(2*b)+(A/b+1)*(A/2*(ep*ep)+ep*v)-(m+-z),min((max((max((max((ep,0-ep)),max((0-tpost(),tpost())))),min((max((max((max((A,0-A)),max((apost(),0-apost())))),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((z-zpost(),zpost()-z)))),max((max((max((v-vpost(),vpost()-v)),max((z-zpost(),zpost()-z)))),0-v)))))),max((max((max((A-apost(),apost()-A)),0-A)),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((zpost()-z,z-zpost())))),max((max((max((v-vpost(),vpost()-v)),max((zpost()-z,z-zpost())))),0-v)))))))))),max((0-ep,min((max((max((max((max((A,0-A)),max((apost(),0-apost())))),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((z-zpost(),zpost()-z)))),max((max((max((v-vpost(),vpost()-v)),max((zpost()-(tpost()*v+z),tpost()*v+z-zpost())))),0-v)))))),min((min((max((ep-tpost(),tpost()-ep)),max((0-tpost(),tpost())))),max((0-tpost(),tpost()-ep)))))),max((max((max((A-apost(),apost()-A)),0-A)),min((max((min((max((max((max((v,0-v)),max((vpost()-A*tpost(),A*tpost()-vpost())))),max((zpost()-(1/2*A*(-1*tpost()*(-1*tpost()))+z),1/2*A*(-1*tpost()*(-1*tpost()))+z-zpost())))),max((max((max((vpost()-(A*tpost()+v),A*tpost()+v-vpost())),max((zpost()-(1/2*A*(-1*tpost()*(-1*tpost()))+tpost()*v+z),1/2*A*(-1*tpost()*(-1*tpost()))+tpost()*v+z-zpost())))),0-v)))),min((max((ep-tpost(),tpost()-ep)),max((0-tpost(),tpost()-ep)))))),max((max((0-tpost(),tpost())),min((max((max((max((v,0-v)),max((vpost(),0-vpost())))),max((zpost()-z,z-zpost())))),max((max((max((vpost()-v,v-vpost())),max((zpost()-z,z-zpost())))),0-v)))))))))))))))))))) < 0".asFormula
  }

  "ETCS test case synthesis" should "derive controller tests from Marco's model" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/ETCS-essentials_marco.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, _) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
      Variable("z"), Variable("t"), Variable("a"))
    val fml = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1) & SimplifierV2.simpTac(1)).subgoals.head.succ.head

    val ts = new TestSynthesis(tool)
    // search for sunshine test case values (initial+expected)
    val testConfig = ts.synthesizeTestConfig(fml, 2, Some(20))
    testConfig should have size 2
    testConfig.foreach(_.keys.map({case v: Variable => v case FuncOf(fn, _) => fn})
      should contain theSameElementsAs StaticSemantics.symbols(fml))
  }

  it should "derive model tests from Marco's model" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/ETCS-essentials_marco.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val (modelplexInput, assumptions) = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
      Variable("z"), Variable("t"), Variable("a"))
    val fml = proveBy(modelplexInput,
      ModelPlex.modelMonitorByChase(1) & SimplifierV2.simpTac(1) &
      ModelPlex.optimizationOneWithSearch(tool, assumptions)(1)).subgoals.head.succ.head

    val ts = new TestSynthesis(tool)
    // search for sunshine test case values (initial+expected)
    val testConfig = ts.synthesizeTestConfig(fml, 2, Some(20))
    testConfig should have size 2
    testConfig.foreach(_.keys.map({case v: Variable => v case FuncOf(fn, _) => fn})
      should contain theSameElementsAs StaticSemantics.symbols(fml))
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
