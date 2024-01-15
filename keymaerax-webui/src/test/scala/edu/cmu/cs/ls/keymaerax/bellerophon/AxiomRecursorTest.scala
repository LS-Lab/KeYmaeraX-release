/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.{CoreException, Formula}
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import org.scalatest.BeforeAndAfterAll
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.FormulaAugmentor
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.SystemTestBase
import testHelper.CustomAssertions._
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, TodoTest}
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import DerivationInfoAugmentors._

/**
  * Test whether axiom recursors are defined after using their key.
  *
  * @author Andre Platzer
  * @see [[UnificationMatch]]
  * @see [[UnificationMatchTest]]
  * @see [[AxiomInfo.theKey]]
  * @see [[AxiomInfo.theRecursor]]
  * @see [[AxiomInfo.unifier]]
  */
@SummaryTest
class AxiomRecursorTest extends TacticTestBase with BeforeAndAfterAll {

  private val randomTrials = 2
  private val randomComplexity = 4
  private val rand = new RandomFormula()

//  override def beforeAll(): Unit = {
//    // the tests in here rely on a populated lemma database, since otherwise some of them require QE (depends on the queried axiom).
//    new DerivedAxiomsTests().execute("The DerivedAxioms prepopulation procedure should not crash")
//  }

  /** Match the key of a given axiom against the given instance AND check existence of its recursors. */
  private def matchKey(axiom: AxiomInfo, instance: Formula): Boolean = {
    val ax: Formula = axiom.formula
    val (_, keyPart) = ax.at(axiom.key)
    val u = UnifyUSCalculus.matcherFor(axiom)(keyPart, instance)
    println("unify1:  " + keyPart)
    println("unify2:  " + instance)
    println("unifier: " + u)
    u(keyPart) shouldBe instance
    //@todo this might fail when the instance requires semantic renaming
    u.toCore(keyPart) shouldBe instance

    if (axiom.displayLevel != 'internal) {
      println(axiom + "\ndisplayLevel=" + axiom.displayLevel)
      // useAt(axiom) should result in all recursors being well-defined
      println("useAt(" + axiom.codeName + ")(1)")
      val pr = TactixLibrary.proveBy(instance, TactixLibrary.useAt(axiom)(1))
      println(pr)
      for (pos <- axiom.recursor) {
        pr.subgoals.head.succ(0).sub(pos) shouldBe 'defined
      }
    }
    true
  }

  "Unification key instantiation sample" should "instantiate <>" in withQE {_ =>
    matchKey(Ax.diamond, "![x:=x+1;{x'=55}]!x>=99".asFormula)
  }

  it should "instantiate [:=] assign 1" in withTactics {
    matchKey(Ax.assignbAxiom, "[x:=z;]x^2>=9".asFormula)
  }

  it should "instantiate [:=] assign equality 1" in withTactics {
    matchKey(Ax.assignbeq, "[x:=1;][x:=2;]x>0".asFormula)
  }

  it should "instantiate [:=] assign equality 2" in withTactics {
    matchKey(Ax.assignbeq, "[x:=1;][{x:=x+1;}*]x>0".asFormula)
  }

  it should "instantiate [:=] assign equality 3" in withTactics {
    matchKey(Ax.assignbeq, "[z1:=1;]<z1:=*;>1>=1".asFormula)
  }

  it should "instantiate [:=] assign equality 4" in withTactics {
    matchKey(Ax.assignbeq, "[z1:=98+1;][z1:=*;][?true;]true".asFormula)
  }

  it should "instantiate [++]" in withTactics {
    matchKey(Ax.choiceb, "[x:=x+1;++{x:=0;{y'=-2}}]x>=y".asFormula)
  }

  it should "instantiate DI" in withTactics {
    matchKey(Ax.DIequiv, "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DC" in withTactics {
    matchKey(Ax.DC, "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DG" in withTactics {
    matchKey(Ax.DGa, "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DG crazy" in withTactics {
    matchKey(Ax.DGa, "[{z2'=1&<z2:=z2+z1;{{?true;++?true;}++?true;?true;}>(\\forall z1 \\forall z1 true->\\forall z2 (true&true))}]true".asFormula)
  }

  it should "instantiate DG crazy 2" in withTactics {
    matchKey(Ax.DGa, "[{z1'=1&<z2:=z1;>\\exists z1 [z1:=z2+1;]z1>=1}]<z1:=-64;>[?true;?true;++?true;]z2>=1+1".asFormula)
  }

  it should "instantiate DG crazy 3" in withTactics {
    matchKey(Ax.DGa, "[{z1'=1&<z2:=z1;>\\exists z1 z1>=z2}]z1>=5".asFormula)
  }

  it should "instantiate DS&" in withTactics {
    matchKey(Ax.DS, "[{y1'=z0+31&q(y1)}]\\exists z1 z1>y1".asFormula)
  }
  

  /** the names of problematic axioms, e.g., because random generators may unwittingly replace {c,d} to an illegal {z1'=1,z1'=1} with duplicate ODEs */
  private val problematicAxioms = ", commute" :: ", sort" :: ",d commute" ::
    Nil


  // random schematic instantiations

  /** the names of schematic axioms in AxiomInfo, in reality only a subset. */

  //@todo not all arity 1 predicationals will be supported during unification
  "Random Instance Unification" should "FEATURE_REQUEST: instantiate keys of schematic axioms to random schematic instantiations" taggedAs TodoTest in withQE {_ => instantiateRandomSchematic()}

   private def instantiateRandomSchematic() {
    for ((name, ax) <- AxiomInfo.allInfo) {
      println("Axiom " + ax)
      for (i <- 1 to randomTrials) {
        val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        if (ax.formula.at(ax.key)._2.isInstanceOf[Formula]) {
          val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
            rand.nextSchematicInstance(ax.formula.at(ax.key)._2.asInstanceOf[Formula], randomComplexity, false)
          }

          withSafeClue("Random instance " + inst + "\n\n" + randClue) {
            println("match instance: " + inst)
            matchKey(ax, inst)
          }
        }
      }
    }
  }

 "Random Renamed Instance Unification" should "FEATURE_REQUEST: instantiate keys of schematic axioms to random schematic instantiations" taggedAs TodoTest in withQE {_ => instantiateRandomRenamed()}

  private def instantiateRandomRenamed() {
    for ((name, ax) <- AxiomInfo.allInfo) {
      println("Axiom " + ax.canonicalName)
      for (i <- 1 to randomTrials) {
        val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        if (ax.formula.at(ax.key)._2.isInstanceOf[Formula]) {
          val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
            rand.nextSchematicInstance(ax.formula.at(ax.key)._2.asInstanceOf[Formula], randomComplexity)
          }

          withSafeClue("Random instance " + inst + "\n\n" + randClue) {
            println("match instance: " + inst)
            matchKey(ax, inst)
          }
        }
      }
    }
  }


  "Random Renamed Instance Unification optimistic" should "FEATURE_REQUEST: instantiate keys of all axioms to random schematic instantiations" taggedAs TodoTest in withQE {_ => instantiateRandomKey()}

  private def instantiateRandomKey() {
    for ((name, ax) <- AxiomInfo.allInfo) {
      println("Axiom " + ax.canonicalName)
      for (i <- 1 to randomTrials) {
        try {
          val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
            " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

          if (ax.formula.at(ax.key)._2.isInstanceOf[Formula]) {
            val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
              rand.nextSchematicInstance(ax.formula.at(ax.key)._2.asInstanceOf[Formula], randomComplexity)
            }

            withSafeClue("Random instance " + inst + "\n\n" + randClue) {
              println("match instance: " + inst)
              matchKey(ax, inst)
            }
          }
        } catch {
          case e: CoreException if e.getMessage.contains("duplicate differential equations") &&
            problematicAxioms.contains(ax.canonicalName) => /* ignore */
        }
      }
    }
  }


//  /** the names of axioms in AxiomInfo that not quite schematic because compatibility is required, in reality only a subset. */
//  private val limitedSchematicAxioms = Ax.assignbeq :: Ax.assignbAxiom :: "[:=] assign equality exists" ::
//    Ax.selfassignb :: "[':=] differential assign" :: "[:*] assign nondet" :: "[?] test" ::
//    "DE differential effect" :: Ax.DGa :: Ax.DGC ::
//    "DG inverse differential ghost" ::
//    Ax.DS ::
//    //"c()' derive constant fn" :: //@todo would need to avoid all variables here
//    "x' derive var" ::
//    "VK vacuous" :: "V vacuous" :: "vacuous all quantifier" ::
//    "const congruence" :: "const formula congruence" ::
//    Nil

}
