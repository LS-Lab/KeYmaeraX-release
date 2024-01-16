/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.{CoreException, Formula}
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, SummaryTest}
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
  * Test whether unification algorithm can instantiate axioms correctly.
  *
  * @author Andre Platzer
  * @see [[UnificationMatch]]
  * @see [[UnificationMatchTest]]
  * @see [[AxiomInfo.theKey]]
  * @see [[AxiomInfo.unifier]]
  */
@CheckinTest
class AxiomKeyInstantiationTest extends SystemTestBase with BeforeAndAfterAll {

  private val randomTrials = 2
  private val randomComplexity = 4
  private val rand = new RandomFormula()

  override def beforeAll(): Unit = {
    // the tests in here rely on a populated lemma database, since otherwise some of them require QE (depends on the queried axiom).
    new DerivedAxiomsTests().execute("The DerivedAxioms prepopulation procedure should not crash")
  }

  /** Match given axiom directly against the given instance in full. */
  private def matchDirect(axiom: AxiomInfo, instance: Formula): Boolean = {
    val ax: Formula = axiom.formula
    val u = UnifyUSCalculus.matcherFor(axiom)(ax, instance)
    println("unify1:  " + ax)
    println("unify2:  " + instance)
    println("unifier: " + u)
    u(ax) shouldBe instance
    //@todo this might fail when the instance requires semantic renaming
    u.toCore(ax) shouldBe instance
    true
  }

  /** Match the key of a given axiom against the given instance. */
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
    true
  }

  "Unification key instantiation sample" should "instantiate <>" in {
    matchKey(Ax.diamond, "![x:=x+1;{x'=55}]!x>=99".asFormula)
  }

  it should "instantiate [:=] assign 1" in {
    matchKey(Ax.assignbAxiom, "[x:=z;]x^2>=9".asFormula)
  }

  it should "instantiate [:=] assign equality 1" in {
    matchKey(Ax.assignbeq, "[x:=1;][x:=2;]x>0".asFormula)
  }

  it should "instantiate [:=] assign equality 2" in {
    matchKey(Ax.assignbeq, "[x:=1;][{x:=x+1;}*]x>0".asFormula)
  }

  it should "instantiate [:=] assign equality 3" in {
    matchKey(Ax.assignbeq, "[z1:=1;]<z1:=*;>1>=1".asFormula)
  }

  it should "instantiate [:=] assign equality 4" in {
    matchKey(Ax.assignbeq, "[z1:=98+1;][z1:=*;][?true;]true".asFormula)
  }

  it should "instantiate [++]" in {
    matchKey(Ax.choiceb, "[x:=x+1;++{x:=0;{y'=-2}}]x>=y".asFormula)
  }

  it should "instantiate DI" in {
    matchKey(Ax.DIequiv, "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DC" in {
    matchKey(Ax.DC, "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DG" in {
    matchKey(Ax.DGa, "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DG crazy" in {
    matchKey(Ax.DGa, "[{z2'=1&<z2:=z2+z1;{{?true;++?true;}++?true;?true;}>(\\forall z1 \\forall z1 true->\\forall z2 (true&true))}]true".asFormula)
  }

  it should "instantiate DG crazy 2" in {
    matchKey(Ax.DGa, "[{z1'=1&<z2:=z1;>\\exists z1 [z1:=z2+1;]z1>=1}]<z1:=-64;>[?true;?true;++?true;]z2>=1+1".asFormula)
  }

  it should "instantiate DG crazy 3" in {
    matchKey(Ax.DGa, "[{z1'=1&<z2:=z1;>\\exists z1 z1>=z2}]z1>=5".asFormula)
  }

  it should "instantiate DS&" in {
    matchKey(Ax.DS, "[{y1'=z0+31&q(y1)}]\\exists z1 z1>y1".asFormula)
  }
  
  ////////

  "Unification full instantiation sample" should "instantiate <>" in {
    matchDirect(Ax.diamond, "![x:=x+1;{x'=55}]!x>=99 <-> <x:=x+1;{x'=55}>x>=99".asFormula)
  }
  it should "instantiate [:=] assign 1" in {
    matchDirect(Ax.assignbAxiom, "[x:=z;]x^2>=9 <-> z^2>=9".asFormula)
  }
  it should "instantiate [:=] assign 2" in {
    matchDirect(Ax.assignbAxiom, "[x:=2*x+1;]x^3>=9*x <-> (2*x+1)^3>=9*(2*x+1)".asFormula)
  }
  it should "instantiate [:=] assign 3" in {
    matchDirect(Ax.assignbAxiom, "[x:=x+1;]x^2>=9 <-> (x+1)^2>=9".asFormula)
  }
  it should "instantiate [:=] assign equality 1" in {
    matchDirect(Ax.assignbeq, "[y:=22*x+y0;]x>=y <-> \\forall y (y=22*x+y0 -> x>=y)".asFormula)
  }
  it should "instantiate [:=] assign equality 2" in {
    matchDirect(Ax.assignbeq, "[x:=1;][{x:=x+1;}*]x>0 <-> \\forall x (x=1 -> [{x:=x+1;}*]x>0)".asFormula)
  }
  it should "instantiate [++]" in {
    matchDirect(Ax.choiceb, "[x:=x+1;++{x:=0;{y'=-2}}]x>=y <-> [x:=x+1;]x>=y & [x:=0;{y'=-2}]x>=y".asFormula)
  }
  it should "instantiate [;]" in {
    matchDirect(Ax.composeb, "[x:=x+1;{x:=0;{y'=-2}}]x>=y <-> [x:=x+1;][x:=0;{y'=-2}]x>=y".asFormula)
  }
  it should "instantiate [*]" in {
    matchDirect(Ax.iterateb, "[{x:=x+1;{x:=0;{y'=-2}}}*]x>=y <-> x>=y & [x:=x+1;{x:=0;{y'=-2}}][{x:=x+1;{x:=0;{y'=-2}}}*]x>=y".asFormula)
  }

  it should "DG differential ghost constant" in {
    matchDirect(Ax.DGC, "[{q' = 2*55}]x>=z <-> \\exists y_ [{q'=2*55,y_'=1&true}]x>=z".asFormula)
  }
  
  it should "DG differential ghost" in {
    matchDirect(Ax.DGa, "[{x'=v*22+5}]x>=52 <-> \\exists y_ [{x'=v*22+5,y_'=100*y_+-22&true}]x>=52".asFormula)
  }

  it should "[:=] self assign" in {
    matchDirect(Ax.selfassignb, "[x:=x;]x>0 <-> x>0".asFormula)
  }

  it should "[:=] assign 1" in {
    matchDirect(Ax.assignbAxiom, "[y:=1;][y:=2;]y>0 <-> [y:=2;]y>0".asFormula)
  }

  it should "[:=] assign 2" in {
    matchDirect(Ax.assignbAxiom, "[y:=1;][y:=2+y;]y>0 <-> [y:=2+1;]y>0".asFormula)
  }

  it should "[:=] assign 3" in {
    matchDirect(Ax.assignbAxiom, "[y:=y+1;]y>0 <-> y+1>0".asFormula)
  }

  it should "[:=] assign 4" in {
    matchDirect(Ax.assignbAxiom, "[x:=1;](y>2 -> \\forall x [{x'=1}]x>0) <-> (y>2 -> \\forall x [{x'=1}]x>0)".asFormula)
  }

  it should "[:=] assign equality" in {
    matchDirect(Ax.assignbeq, "[x:=1;][{x:=x+1;}*]x>0 <-> \\forall x (x=1 -> [{x:=x+1;}*]x>0)".asFormula)
  }

  it should "[:=] assign equality 2" in {
    matchDirect(Ax.assignbeq, "[x_0:=x;]x_0>0 <-> \\forall x_0 (x_0=x -> x_0>0)".asFormula)
  }

  it should "exists eliminate" ignore {
    matchDirect(Ax.existse, "\\exists z1 \\exists z1 true->\\exists z1 \\exists z1 \\exists z1 true".asFormula)
  }

  it should "[:=] self assign 1" in {
    matchDirect(Ax.selfassignb, "[x:=x;]x>0<->x>0".asFormula)
  }

  it should "[:=] self assign diff" in {
    matchDirect(Ax.selfassignb, "[x:=x;][x':=2;](x>0)'<->[x':=2;](x>0)'".asFormula)
  }

//  it should "[:=] assign exists" in {
//    matchDirect(Ax.assignbequalityexists, "[t:=0;][{x'=1,t'=1&true}]x>0<->\\exists t [{x'=1,t'=1&true}]x>0".asFormula)
//  }

  it should "all eliminate built-in clash crazy" taggedAs IgnoreInBuildTest in {
    matchDirect(Ax.alle, "\\forall z1 \\forall x_ (true<->true)->\\forall x_ (true<->true)".asFormula)
  }

  it should "exists eliminate built-in clash crazy" taggedAs(IgnoreInBuildTest, TodoTest) ignore {
    matchDirect(Ax.existse, "\\forall x_ [?true;]true->\\exists z1 \\forall x_ [?true;]true".asFormula)
  }


  /** the names of problematic axioms, e.g., because random generators may unwittingly replace {c,d} to an illegal {z1'=1,z1'=1} with duplicate ODEs */
  private val problematicAxioms = ", commute" :: ", sort" :: ",d commute" ::
    Nil


  // random schematic instantiations

  /** the names of schematic axioms in AxiomInfo, in reality only a subset. */

  //@todo not all arity 1 predicationals will be supported during unification
  "Random Instance Unification" should "FEATURE_REQUEST: instantiate keys of schematic axioms to random schematic instantiations" taggedAs TodoTest in instantiateRandomSchematic()

   private def instantiateRandomSchematic(): Unit = {
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

  //@todo not all arity 1 predicationals will be supported during unification
  it should "instantiate full schematic axioms to random schematic instantiations" in instantiateFullSchematic()

  private def instantiateFullSchematic(): Unit = {
    for ((name, ax) <- AxiomInfo.allInfo) {
      println("Axiom " + ax.canonicalName)
      for (i <- 1 to randomTrials/5) {
        val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
          rand.nextSchematicInstance(ax.formula, randomComplexity, renamed = false)
        }

        withSafeClue("Random instance " + inst + "\n\n" + randClue) {
          println("match instance: " + inst)
          matchDirect(ax, inst)
        }
      }
    }
  }

 "Random Renamed Instance Unification" should "FEATURE_REQUEST: instantiate keys of schematic axioms to random schematic instantiations" taggedAs TodoTest in instantiateRandomRenamed()

  private def instantiateRandomRenamed(): Unit = {
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

  //@todo not all arity 1 predicationals will be supported during unification
  it should "instantiate full schematic axioms to random schematic instantiations" in instantiateFullRandom()
  //@todo it should "UniformMatcher: instantiate full schematic axioms to random schematic instantiations" in instantiateFullRandom(UniformMatcher)

  private def instantiateFullRandom(): Unit = {
    for ((name, ax) <- AxiomInfo.allInfo) {
      println("Axiom " + ax.canonicalName)
      for (i <- 1 to randomTrials/5) {
        val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
          rand.nextSchematicInstance(ax.formula, randomComplexity)
        }

        withSafeClue("Random instance " + inst + "\n\n" + randClue) {
          println("match instance: " + inst)
          matchDirect(ax, inst)
        }
      }
    }
  }


  "Random Renamed Instance Unification optimistic" should "FEATURE_REQUEST: instantiate keys of all axioms to random schematic instantiations" taggedAs TodoTest in instantiateRandomKey()

  private def instantiateRandomKey(): Unit = {
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
