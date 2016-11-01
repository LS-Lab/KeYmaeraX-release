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
    val modelplexInput = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
      Variable("z"), Variable("t"), Variable("a"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1, 1::Nil) & ModelPlex.simplify())
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&(((SBpost()=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v)&zpost()=z)&tpost()=0)&apost()=-b|m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(v>=0&0<=ep)&(((SBpost()=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&vpost()=v)&zpost()=z)&tpost()=0)&apost()=A".asFormula
  }

  it should "synthesize a ctrl monitor from safety lemma" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/safety-lemma.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = ModelPlex.createMonitorSpecificationConjecture(model, Variable("vdes"), Variable("SB"), Variable("v"),
      Variable("em"), Variable("do"), Variable("z"), Variable("t"), Variable("mo"), Variable("m"), Variable("d"),
      Variable("a"))

    val foResult = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1, 1::Nil) &
      ModelPlex.optimizationOneWithSearch(1) & ModelPlex.simplify())
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "((dpost()>=0&d^2-dpost()^2<=2*b*(mpost()-m)&vdespost()>=0)&((((((SBpost()=SB&vpost()=v)&empost()=em)&dopost()=d)&zpost()=z)&tpost()=t)&mopost()=m)&apost()=a|(((((((((vdespost()=vdes&SBpost()=SB)&vpost()=v)&empost()=1)&dopost()=do)&zpost()=z)&tpost()=t)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=a)|v<=vdes&(apost()>=-b&apost()<=A)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)|v>=vdes&(apost() < 0&apost()>=-b)&((m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&(((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)&apost()=-b|!(m-z<=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|em=1)&(v>=0&0<=ep)&((((((((vdespost()=vdes&SBpost()=(v^2-d^2)/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&vpost()=v)&empost()=em)&dopost()=do)&zpost()=z)&tpost()=0)&mopost()=mo)&mpost()=m)&dpost()=d)".asFormula
  }

  it should "synthesize a model monitor from essentials" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials-explicitode.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
      Variable("z"), Variable("t"), Variable("a"))

    val foResult = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1, 1::Nil) &
      DebuggingTactics.print("Before Opt. 1") & ModelPlex.optimizationOneWithSearch(1, 1::Nil) & DebuggingTactics.print("After Opt. 1") &
      SimplifierV2.simpTac(1))
    foResult.subgoals should have size 1
    foResult.subgoals.head.ante shouldBe empty
    foResult.subgoals.head.succ should contain only "m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(0 < ep&(vpost()=0&(((tpost()=0&v=0)&((((b < 0&apost()=-1*b)&z=1/2*(b*0^2+b*tpost()^2+2*zpost()))&SBpost()=0^2/(2*b)+(A/b+1)*(A/2*ep^2)|((b=0&apost()=0)&z=zpost())&SBpost()=0^2/0+(A/0+1)*(A/2*ep^2))|((b>0&apost()=-1*b)&z=1/2*(b*0^2+b*tpost()^2+2*zpost()))&SBpost()=0^2/(2*b)+(A/b+1)*(A/2*ep^2))|(0 < tpost()&tpost() < ep)&((((v=0&b=0)&apost()=0)&z=zpost())&SBpost()=0^2/0+(A/0+1)*(A/2*ep^2)|(((v>0&b=-1*(-1*tpost())^-1*v)&apost()=-1*(-1*(-1*tpost())^-1*v))&z=1/2*(-1*(-1*tpost())^-1*v*0^2+-1*(-1*tpost())^-1*v*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*(-1*(-1*tpost())^-1*v))+(A/(-1*(-1*tpost())^-1*v)+1)*(A/2*ep^2+ep*v)))|tpost()=ep&((((v=0&b=0)&apost()=0)&z=zpost())&SBpost()=0^2/0+(A/0+1)*(A/2*ep^2)|(((v>0&b=ep^-1*v)&apost()=-1*(ep^-1*v))&z=1/2*(ep^-1*v*0^2+ep^-1*v*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*(ep^-1*v))+(A/(ep^-1*v)+1)*(A/2*ep^2+ep*v)))|vpost()>0&(((tpost()=0&v=vpost())&((((b < 0&apost()=-1*b)&z=1/2*(b*0^2+b*tpost()^2+-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vpost())|((b=0&apost()=0)&z=1/2*(-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/0+(A/0+1)*(A/2*ep^2+ep*vpost()))|((b>0&apost()=-1*b)&z=1/2*(b*0^2+b*tpost()^2+-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vpost()))|(0 < tpost()&tpost() < ep)&((((((((0<=v&v < vpost())&b=(-1*tpost())^-1*(-1*v+vpost()))&apost()=-1*((-1*tpost())^-1*(-1*v+vpost())))&z=1/2*((-1*tpost())^-1*(-1*v+vpost())*0^2+(-1*tpost())^-1*(-1*v+vpost())*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*((-1*tpost())^-1*(-1*v+vpost())))+(A/((-1*tpost())^-1*(-1*v+vpost()))+1)*(A/2*ep^2+ep*v)|(((v=vpost()&b=0)&apost()=0)&z=1/2*(-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/0+(A/0+1)*(A/2*ep^2+ep*vpost()))|((((vpost() < v&v < (ep+-1*tpost())^-1*(ep*vpost()))&b=(-1*tpost())^-1*(-1*v+vpost()))&apost()=-1*((-1*tpost())^-1*(-1*v+vpost())))&z=1/2*((-1*tpost())^-1*(-1*v+vpost())*0^2+(-1*tpost())^-1*(-1*v+vpost())*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*((-1*tpost())^-1*(-1*v+vpost())))+(A/((-1*tpost())^-1*(-1*v+vpost()))+1)*(A/2*ep^2+ep*v))|(((v=(ep+-1*tpost())^-1*(ep*vpost())&b=ep^-1*((ep+-1*tpost())^-1*(ep*vpost())))&apost()=-1*(ep^-1*((ep+-1*tpost())^-1*(ep*vpost()))))&z=1/2*(ep^-1*((ep+-1*tpost())^-1*(ep*vpost()))*0^2+ep^-1*((ep+-1*tpost())^-1*(ep*vpost()))*tpost()^2+-2*tpost()*((ep+-1*tpost())^-1*(ep*vpost()))+2*zpost()))&SBpost()=((ep+-1*tpost())^-1*(ep*vpost()))^2/(2*(ep^-1*((ep+-1*tpost())^-1*(ep*vpost()))))+(A/(ep^-1*((ep+-1*tpost())^-1*(ep*vpost())))+1)*(A/2*ep^2+ep*((ep+-1*tpost())^-1*(ep*vpost()))))|(((v>(ep+-1*tpost())^-1*(ep*vpost())&b=(-1*tpost())^-1*(-1*v+vpost()))&apost()=-1*((-1*tpost())^-1*(-1*v+vpost())))&z=1/2*((-1*tpost())^-1*(-1*v+vpost())*0^2+(-1*tpost())^-1*(-1*v+vpost())*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*((-1*tpost())^-1*(-1*v+vpost())))+(A/((-1*tpost())^-1*(-1*v+vpost()))+1)*(A/2*ep^2+ep*v)))|tpost()=ep&((((((0<=v&v < vpost())&b=(-1*tpost())^-1*(-1*v+vpost()))&apost()=-1*((-1*tpost())^-1*(-1*v+vpost())))&z=1/2*((-1*tpost())^-1*(-1*v+vpost())*0^2+(-1*tpost())^-1*(-1*v+vpost())*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*((-1*tpost())^-1*(-1*v+vpost())))+(A/((-1*tpost())^-1*(-1*v+vpost()))+1)*(A/2*ep^2+ep*v)|(((v=vpost()&b=0)&apost()=0)&z=1/2*(-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/0+(A/0+1)*(A/2*ep^2+ep*vpost()))|(((v>vpost()&b=(-1*tpost())^-1*(-1*v+vpost()))&apost()=-1*((-1*tpost())^-1*(-1*v+vpost())))&z=1/2*((-1*tpost())^-1*(-1*v+vpost())*0^2+(-1*tpost())^-1*(-1*v+vpost())*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*((-1*tpost())^-1*(-1*v+vpost())))+(A/((-1*tpost())^-1*(-1*v+vpost()))+1)*(A/2*ep^2+ep*v))))|0=ep&(((vpost()=ep&tpost()=ep)&v=ep)&((((b < ep&apost()=-1*b)&z=1/2*(b*ep^2+-2*b*ep*ep+b*ep^2+2*zpost()))&SBpost()=ep^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*ep)|((b=ep&apost()=ep)&z=zpost())&SBpost()=ep^2/(2*ep)+(A/ep+1)*(A/2*ep^2+ep*ep))|((b>ep&apost()=-1*b)&z=1/2*(b*ep^2+-2*b*ep*ep+b*ep^2+2*zpost()))&SBpost()=ep^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*ep))|((vpost()>ep&tpost()=ep)&v=vpost())&((((b < ep&apost()=-1*b)&z=1/2*(b*ep^2+-2*b*ep*ep+b*ep^2+-2*ep*vpost()+2*ep*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vpost())|((b=ep&apost()=ep)&z=1/2*(-2*ep*vpost()+2*ep*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*ep)+(A/ep+1)*(A/2*ep^2+ep*vpost()))|((b>ep&apost()=-1*b)&z=1/2*(b*ep^2+-2*b*ep*ep+b*ep^2+-2*ep*vpost()+2*ep*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vpost()))))|m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)&(0 < ep&(vpost()=0&(((tpost()=0&v=0)&((((A < 0&apost()=A)&z=1/2*(-1*A*0^2+-1*A*tpost()^2+2*zpost()))&SBpost()=0^2/(2*b)+(A/b+1)*(A/2*ep^2)|((A=0&apost()=0)&z=zpost())&SBpost()=0^2/(2*b)+(0/b+1)*(0/2*ep^2))|((A>0&apost()=A)&z=1/2*(-1*A*0^2+-1*A*tpost()^2+2*zpost()))&SBpost()=0^2/(2*b)+(A/b+1)*(A/2*ep^2))|(0 < tpost()&tpost() < ep)&((((v=0&A=0)&apost()=0)&z=zpost())&SBpost()=0^2/(2*b)+(0/b+1)*(0/2*ep^2)|(((v>0&A=(-1*tpost())^-1*v)&apost()=(-1*tpost())^-1*v)&z=1/2*(-1*((-1*tpost())^-1*v)*0^2+-1*((-1*tpost())^-1*v)*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*b)+((-1*tpost())^-1*v/b+1)*((-1*tpost())^-1*v/2*ep^2+ep*v)))|tpost()=ep&((((v=0&A=0)&apost()=0)&z=zpost())&SBpost()=0^2/(2*b)+(0/b+1)*(0/2*ep^2)|(((v>0&A=-1*ep^-1*v)&apost()=-1*ep^-1*v)&z=1/2*(-1*(-1*ep^-1*v)*0^2+-1*(-1*ep^-1*v)*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*b)+(-1*ep^-1*v/b+1)*(-1*ep^-1*v/2*ep^2+ep*v)))|vpost()>0&(((tpost()=0&v=vpost())&((((A < 0&apost()=A)&z=1/2*(-1*A*0^2+-1*A*tpost()^2+-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vpost())|((A=0&apost()=0)&z=1/2*(-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(0/b+1)*(0/2*ep^2+ep*vpost()))|((A>0&apost()=A)&z=1/2*(-1*A*0^2+-1*A*tpost()^2+-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vpost()))|(0 < tpost()&tpost() < ep)&((((((((0<=v&v < vpost())&A=(-1*tpost())^-1*(v+-1*vpost()))&apost()=(-1*tpost())^-1*(v+-1*vpost()))&z=1/2*(-1*((-1*tpost())^-1*(v+-1*vpost()))*0^2+-1*((-1*tpost())^-1*(v+-1*vpost()))*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*b)+((-1*tpost())^-1*(v+-1*vpost())/b+1)*((-1*tpost())^-1*(v+-1*vpost())/2*ep^2+ep*v)|(((v=vpost()&A=0)&apost()=0)&z=1/2*(-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(0/b+1)*(0/2*ep^2+ep*vpost()))|((((vpost() < v&v < (ep+-1*tpost())^-1*(ep*vpost()))&A=(-1*tpost())^-1*(v+-1*vpost()))&apost()=(-1*tpost())^-1*(v+-1*vpost()))&z=1/2*(-1*((-1*tpost())^-1*(v+-1*vpost()))*0^2+-1*((-1*tpost())^-1*(v+-1*vpost()))*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*b)+((-1*tpost())^-1*(v+-1*vpost())/b+1)*((-1*tpost())^-1*(v+-1*vpost())/2*ep^2+ep*v))|(((v=(ep+-1*tpost())^-1*(ep*vpost())&A=-1*ep^-1*((ep+-1*tpost())^-1*(ep*vpost())))&apost()=-1*ep^-1*((ep+-1*tpost())^-1*(ep*vpost())))&z=1/2*(-1*(-1*ep^-1*((ep+-1*tpost())^-1*(ep*vpost())))*0^2+-1*(-1*ep^-1*((ep+-1*tpost())^-1*(ep*vpost())))*tpost()^2+-2*tpost()*((ep+-1*tpost())^-1*(ep*vpost()))+2*zpost()))&SBpost()=((ep+-1*tpost())^-1*(ep*vpost()))^2/(2*b)+(-1*ep^-1*((ep+-1*tpost())^-1*(ep*vpost()))/b+1)*(-1*ep^-1*((ep+-1*tpost())^-1*(ep*vpost()))/2*ep^2+ep*((ep+-1*tpost())^-1*(ep*vpost()))))|(((v>(ep+-1*tpost())^-1*(ep*vpost())&A=(-1*tpost())^-1*(v+-1*vpost()))&apost()=(-1*tpost())^-1*(v+-1*vpost()))&z=1/2*(-1*((-1*tpost())^-1*(v+-1*vpost()))*0^2+-1*((-1*tpost())^-1*(v+-1*vpost()))*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*b)+((-1*tpost())^-1*(v+-1*vpost())/b+1)*((-1*tpost())^-1*(v+-1*vpost())/2*ep^2+ep*v)))|tpost()=ep&((((((0<=v&v < vpost())&A=(-1*tpost())^-1*(v+-1*vpost()))&apost()=(-1*tpost())^-1*(v+-1*vpost()))&z=1/2*(-1*((-1*tpost())^-1*(v+-1*vpost()))*0^2+-1*((-1*tpost())^-1*(v+-1*vpost()))*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*b)+((-1*tpost())^-1*(v+-1*vpost())/b+1)*((-1*tpost())^-1*(v+-1*vpost())/2*ep^2+ep*v)|(((v=vpost()&A=0)&apost()=0)&z=1/2*(-2*tpost()*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(0/b+1)*(0/2*ep^2+ep*vpost()))|(((v>vpost()&A=(-1*tpost())^-1*(v+-1*vpost()))&apost()=(-1*tpost())^-1*(v+-1*vpost()))&z=1/2*(-1*((-1*tpost())^-1*(v+-1*vpost()))*0^2+-1*((-1*tpost())^-1*(v+-1*vpost()))*tpost()^2+-2*tpost()*v+2*zpost()))&SBpost()=v^2/(2*b)+((-1*tpost())^-1*(v+-1*vpost())/b+1)*((-1*tpost())^-1*(v+-1*vpost())/2*ep^2+ep*v))))|0=ep&(((vpost()=ep&tpost()=ep)&v=ep)&((((A < ep&apost()=A)&z=1/2*(-1*A*ep^2+2*A*ep*ep+-1*A*ep^2+2*zpost()))&SBpost()=ep^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*ep)|((A=ep&apost()=ep)&z=zpost())&SBpost()=ep^2/(2*b)+(ep/b+1)*(ep/2*ep^2+ep*ep))|((A>ep&apost()=A)&z=1/2*(-1*A*ep^2+2*A*ep*ep+-1*A*ep^2+2*zpost()))&SBpost()=ep^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*ep))|((vpost()>ep&tpost()=ep)&v=vpost())&((((A < ep&apost()=A)&z=1/2*(-1*A*ep^2+2*A*ep*ep+-1*A*ep^2+-2*ep*vpost()+2*ep*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vpost())|((A=ep&apost()=ep)&z=1/2*(-2*ep*vpost()+2*ep*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(ep/b+1)*(ep/2*ep^2+ep*vpost()))|((A>ep&apost()=A)&z=1/2*(-1*A*ep^2+2*A*ep*ep+-1*A*ep^2+-2*ep*vpost()+2*ep*vpost()+2*zpost()))&SBpost()=vpost()^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vpost()))))".asFormula
  }

  "ETCS code generation" should "synthesize C code from essentials ctrl monitor" in withMathematica { tool =>
    val in = getClass.getResourceAsStream("/examples/casestudies/etcs/rephrased/ETCS-essentials.kyx")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = ModelPlex.createMonitorSpecificationConjecture(model, Variable("SB"), Variable("v"),
      Variable("z"), Variable("t"), Variable("a"))
    val monitorCond = proveBy(modelplexInput, ModelPlex.controllerMonitorByChase(1, 1::Nil) & ModelPlex.simplify())
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
