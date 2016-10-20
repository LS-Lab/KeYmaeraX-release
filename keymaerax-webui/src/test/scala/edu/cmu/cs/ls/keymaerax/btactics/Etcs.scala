/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.core._
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

  "ETCS reactivity" should "prove lemma with master" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove full lemma with tactic" in withMathematica { tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma-full.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/etcs/reactivity-lemma-full.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  "ETCS essentials" should "be provable with master" in withMathematica { tool =>
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
}
