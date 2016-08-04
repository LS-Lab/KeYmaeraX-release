package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Formula, Provable}
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors.FormulaAugmentor
import edu.cmu.cs.ls.keymaerax.btactics.{AxiomIndex, AxiomInfo, Context, RandomFormula}
import testHelper.CustomAssertions._

/**
  * Test whether unification algorithm can instantiate axioms correctly.
  *
  * @author Andre Platzer
  */
@SummaryTest
class UnifyAxiomInstantiationTest extends FlatSpec with Matchers {
  KeYmaera.init(Map.empty)

  val randomTrials = 100
  val randomComplexity = 4
  val rand = new RandomFormula()

  val unify = UnificationMatch


  private def matchDirect(axiom: String, instance: Formula): Boolean = {
    val ax: Formula = AxiomInfo(axiom).formula
    val u = unify(ax, instance)
    u(ax) shouldBe instance
    true
  }

  private def matchKey(axiom: String, instance: Formula): Boolean = {
    val ax: Formula = AxiomInfo(axiom).formula
    val (keyCtx:Context[_],keyPart) = ax.at(AxiomIndex.axiomIndex(axiom)._1)
    val u = unify(keyPart, instance)
    u(keyPart) shouldBe instance
    true
  }

  "Unification instantiation sample" should "instantiate <>" in {
    matchDirect("<> diamond", "![x:=x+1;{x'=55}]!x>=99 <-> <x:=x+1;{x'=55}>x>=99".asFormula)
  }
  it should "instantiate [:=] assign 1" in {
    matchDirect("[:=] assign", "[x:=z;]x^2>=9 <-> z^2>=9".asFormula)
  }
  it should "instantiate [:=] assign 2" in {
    matchDirect("[:=] assign", "[x:=2*x+1;]x^3>=9*x <-> (2*x+1)^3>=9*(2*x+1)".asFormula)
  }
  it should "instantiate [:=] assign 3" in {
    matchDirect("[:=] assign", "[x:=x+1;]x^2>=9 <-> (x+1)^2>=9".asFormula)
  }
  it should "instantiate [++]" in {
    matchDirect("[++] choice", "[x:=x+1;++{x:=0;{y'=-2}}]x>=y <-> [x:=x+1;]x>=y & [x:=0;{y'=-2}]x>=y".asFormula)
  }
  it should "instantiate [;]" in {
    matchDirect("[;] compose", "[x:=x+1;{x:=0;{y'=-2}}]x>=y <-> [x:=x+1;][x:=0;{y'=-2}]x>=y".asFormula)
  }
  it should "instantiate [*]" in {
    matchDirect("[*] iterate", "[{x:=x+1;{x:=0;{y'=-2}}}*]x>=y <-> x>=y & [x:=x+1;{x:=0;{y'=-2}}][{x:=x+1;{x:=0;{y'=-2}}}*]x>=y".asFormula)
  }

  it should "instantiate [:=] assign exists" in {
    matchDirect("[:=] assign exists", "[y:=22*x+y;]x>=y -> \\exists y x>=y".asFormula)
  }

  it should "DG differential ghost constant" in {
    matchDirect("DG differential ghost constant", "[{q' = 2*55}]x>=z <-> \\exists y_ [{q'=2*55,y_'=1&true}]x>=z".asFormula)
  }
  
  it should "DG differential ghost" in {
    matchDirect("DG differential ghost", "[{x'=v*22+5}]x>=52 <-> \\exists y_ [{x'=v*22+5,y_'=100*y_+-22&true}]x>=52".asFormula)
  }

  "Unification" should "instantiate some schematic axioms" in {
  }

  // random schematic instantiations

  private val schematicAxioms = "<> diamond" :: "[++] choice" :: "[;] compose" :: "[*] iterate" ::
    "DW" :: "DC differential cut" :: "DE differential effect (system)" :: "DI differential invariance" ::
    "DX differential skip" ::
    "-' derive neg" :: "+' derive sum" :: "-' derive minus" :: "*' derive product" :: "/' derive quotient" ::
    "=' derive =" :: ">=' derive >=" :: ">' derive >" :: "<=' derive <=" :: "<' derive <" :: "!=' derive !=" ::
    "&' derive and" :: "|' derive or" :: "forall' derive forall" :: "exists' derive exists" ::
    "K modal modus ponens" :: "I induction" ::
    "all dual" :: "all eliminate" :: "exists eliminate" ::
    Nil

  "Unification" should "instantiate keys of schematic axioms to random schematic instantiations" in {
    for (ax <- schematicAxioms) {
      println("Axiom " + ax)
      for (i <- 1 to randomTrials) {
        val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        if (AxiomInfo(ax).formula.at(AxiomIndex.axiomIndex(ax)._1)._2.isInstanceOf[Formula]) {
          val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
            rand.nextSchematicInstance(Provable.axiom(ax).at(AxiomIndex.axiomIndex(ax)._1)._2.asInstanceOf[Formula], randomComplexity)
          }

          withSafeClue("Random instance " + inst + "\n\n" + randClue) {
            println("match instance: " + inst)
            matchKey(ax, inst)
          }
        }
      }
    }
  }

  it should "instantiate full schematic axioms to random schematic instantiations" in {
    for (ax <- schematicAxioms) {
      println("Axiom " + ax)
      for (i <- 1 to randomTrials/5) {
        val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
          rand.nextSchematicInstance(AxiomInfo(ax).formula, randomComplexity)
        }

        withSafeClue("Random instance " + inst + "\n\n" + randClue) {
          println("match instance: " + inst)
          matchDirect(ax, inst)
        }
      }
    }
  }
}
