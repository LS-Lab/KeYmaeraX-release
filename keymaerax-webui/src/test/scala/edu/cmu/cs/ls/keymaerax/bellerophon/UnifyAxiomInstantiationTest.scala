package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{AnyArg, Formula, Provable, UnitPredicational}
import edu.cmu.cs.ls.keymaerax.tags.SummaryTest
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors.FormulaAugmentor
import edu.cmu.cs.ls.keymaerax.btactics.{AxiomIndex, AxiomInfo, Context, RandomFormula}
import testHelper.CustomAssertions._
import testHelper.KeYmaeraXTestTags.IgnoreInBuildTest

/**
  * Test whether unification algorithm can instantiate axioms correctly.
  *
  * @author Andre Platzer
  */
@SummaryTest
class UnifyAxiomInstantiationTest extends FlatSpec with Matchers {
  KeYmaera.init(Map.empty)

  val randomTrials = 20
  val randomComplexity = 2
  val rand = new RandomFormula()

  val unify = UnificationMatch


  private def matchDirect(axiom: String, instance: Formula): Boolean = {
    val ax: Formula = AxiomInfo(axiom).formula
    val u = unify(ax, instance)
    println("unify1:  " + ax)
    println("unify2:  " + instance)
    println("unifier: " + u)
    u(ax) shouldBe instance
    //@todo this might fail when the instance requires semantic renaming
    u.toCore(ax) shouldBe instance
    true
  }

  private def matchKey(axiom: String, instance: Formula): Boolean = {
    val ax: Formula = AxiomInfo(axiom).formula
    val (keyCtx:Context[_],keyPart) = ax.at(AxiomIndex.axiomIndex(axiom)._1)
    val u = unify(keyPart, instance)
    println("unify1:  " + keyPart)
    println("unify2:  " + instance)
    println("unifier: " + u)
    u(keyPart) shouldBe instance
    //@todo this might fail when the instance requires semantic renaming
    u.toCore(keyPart) shouldBe instance
    true
  }

  "Unification key instantiation sample" should "instantiate <>" in {
    matchKey("<> diamond", "![x:=x+1;{x'=55}]!x>=99".asFormula)
  }

  it should "instantiate [:=] assign 1" in {
    matchKey("[:=] assign", "[x:=z;]x^2>=9".asFormula)
  }

  it should "instantiate [:=] assign equality 1" in {
    matchKey("[:=] assign equality", "[x:=1;][x:=2;]x>0".asFormula)
  }

  it should "instantiate [:=] assign equality 2" in {
    matchKey("[:=] assign equality", "[x:=1;][{x:=x+1;}*]x>0".asFormula)
    // it should prepare for renaming transposition
    unify("[x_:=f();]p(||)".asFormula, "[x:=1;][{x:=x+1;}*]x>0".asFormula) shouldBe RenUSubst(
      ("x_".asTerm, "x".asVariable) ::
      ("f()".asTerm, "1".asTerm) ::
      (UnitPredicational("p", AnyArg), "[{x_:=x_+1;}*]x_>0".asFormula) :: Nil
    )
  }

  it should "instantiate [:=] assign equality 3" in {
    matchKey("[:=] assign equality", "[z1:=1;]<z1:=*;>1>=1".asFormula)
  }

  it should "instantiate [:=] assign equality 4" in {
    matchKey("[:=] assign equality", "[z1:=98+1;][z1:=*;][?true;]true".asFormula)
  }

  it should "instantiate [++]" in {
    matchKey("[++] choice", "[x:=x+1;++{x:=0;{y'=-2}}]x>=y".asFormula)
  }

  it should "instantiate DI" in {
    matchKey("DI differential invariance", "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DC" in {
    matchKey("DC differential cut", "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DG" in {
    matchKey("DG differential ghost", "[{x'=5&x>9}]x>=10".asFormula)
  }

  it should "instantiate DG crazy" in {
    matchKey("DG differential ghost", "[{z2'=1&<z2:=z2+z1;{{?true;++?true;}++?true;?true;}>(\\forall z1 \\forall z1 true->\\forall z2 (true&true))}]true".asFormula)
  }

  it should "instantiate DG crazy 2" in {
    matchKey("DG differential ghost", "[{z1'=1&<z2:=z1;>\\exists z1 [z1:=z2+1;]z1>=1}]<z1:=-64;>[?true;?true;++?true;]z2>=1+1".asFormula)
  }

  it should "instantiate DG crazy 3" in {
    matchKey("DG differential ghost", "[{z1'=1&<z2:=z1;>\\exists z1 z1>=z2}]z1>=5".asFormula)
  }

  it should "instantiate DS&" in {
    matchKey("DS& differential equation solution", "[{y1'=z0+31&q(y1)}]\\exists z1 z1>y1".asFormula)
  }

  it should "instantiate DS& crazy built-in clash" taggedAs(IgnoreInBuildTest) in {
    matchKey("DS& differential equation solution", "[{y1'=x_+31&q(y1)}]\\exists z1 true".asFormula)
  }

  ////////

  "Unification full instantiation sample" should "instantiate <>" in {
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
  it should "instantiate [:=] assign equality 1" in {
    matchDirect("[:=] assign equality", "[y:=22*x+y0;]x>=y <-> \\forall y (y=22*x+y0 -> x>=y)".asFormula)
  }
  it should "instantiate [:=] assign equality 2" in {
    matchDirect("[:=] assign equality", "[x:=1;][{x:=x+1;}*]x>0 <-> \\forall x (x=1 -> [{x:=x+1;}*]x>0)".asFormula)
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

  it should "instantiate [:=] assign exists when post-condition binds quantified variable" in {
    matchDirect("[:=] assign exists", "[y:=22*x+y;][{y'=v,v'=a}]x>=y -> \\exists y [{y'=v,v'=a}]x>=y".asFormula)
  }

  it should "work on example from ode solver" in {
    matchDirect("[:=] assign exists", "[kyxtime:=0;][{x'=v,kyxtime'=1&true}]1=1->\\exists kyxtime [{x'=v,kyxtime'=1&true}]1=1".asFormula)
  }

  it should "DG differential ghost constant" in {
    matchDirect("DG differential ghost constant", "[{q' = 2*55}]x>=z <-> \\exists y_ [{q'=2*55,y_'=1&true}]x>=z".asFormula)
  }
  
  it should "DG differential ghost" in {
    matchDirect("DG differential ghost", "[{x'=v*22+5}]x>=52 <-> \\exists y_ [{x'=v*22+5,y_'=100*y_+-22&true}]x>=52".asFormula)
  }

  it should "[:=] self assign" in {
    matchDirect("[:=] self assign", "[x:=x;]x>0 <-> x>0".asFormula)
  }

  it should "[:=] assign 1" in {
    matchDirect("[:=] assign", "[y:=1;][y:=2;]y>0 <-> [y:=2;]y>0".asFormula)
  }

  it should "[:=] assign 2" in {
    matchDirect("[:=] assign", "[y:=1;][y:=2+y;]y>0 <-> [y:=2+1;]y>0".asFormula)
  }

  it should "[:=] assign 3" in {
    matchDirect("[:=] assign", "[y:=y+1;]y>0 <-> y+1>0".asFormula)
  }

  it should "[:=] assign 4" in {
    matchDirect("[:=] assign", "[x:=1;](y>2 -> \\forall x [{x'=1}]x>0) <-> (y>2 -> \\forall x [{x'=1}]x>0)".asFormula)
  }

  it should "[:=] assign equality" in {
    matchDirect("[:=] assign equality", "[x:=1;][{x:=x+1;}*]x>0 <-> \\forall x (x=1 -> [{x:=x+1;}*]x>0)".asFormula)
  }

  it should "[:=] assign equality 2" in {
    matchDirect("[:=] assign equality", "[x_0:=x;]x_0>0 <-> \\forall x_0 (x_0=x -> x_0>0)".asFormula)
  }

  it should "exists eliminate" in {
    matchDirect("exists eliminate", "\\exists z1 \\exists z1 true->\\exists z1 \\exists z1 \\exists z1 true".asFormula)
  }

  it should "[:=] self assign 1" in {
    matchDirect("[:=] self assign", "[x:=x;]x>0<->x>0".asFormula)
  }

  it should "[:=] self assign diff" in {
    matchDirect("[:=] self assign", "[x:=x;][x':=2;](x>0)'<->[x':=2;](x>0)'".asFormula)
  }

  it should "[:=] assign exists" in {
    matchDirect("[:=] assign exists", "[t:=0;][{x'=1,t'=1&true}]x>0->\\exists t [{x'=1,t'=1&true}]x>0".asFormula)
  }

  it should "all eliminate built-in clash crazy" taggedAs(IgnoreInBuildTest) in {
    matchDirect("all eliminate", "\\forall z1 \\forall x_ (true<->true)->\\forall x_ (true<->true)".asFormula)
  }

  it should "exists eliminate built-in clash crazy" taggedAs(IgnoreInBuildTest) in {
    matchDirect("exists eliminate", "\\forall x_ [?true;]true->\\exists z1 \\forall x_ [?true;]true".asFormula)
  }


  // random schematic instantiations

  private val schematicAxioms = "<> diamond" :: "[++] choice" :: "[;] compose" :: "[*] iterate" ::
    "DW" :: "DC differential cut" :: "DE differential effect (system)" :: "DI differential invariance" ::
    "DX differential skip" ::
    //", commute" :: //@todo would need to avoid repeated ODEs
    "-' derive neg" :: "+' derive sum" :: "-' derive minus" :: "*' derive product" :: "/' derive quotient" ::
    "=' derive =" :: ">=' derive >=" :: ">' derive >" :: "<=' derive <=" :: "<' derive <" :: "!=' derive !=" ::
    "&' derive and" :: "|' derive or" :: "forall' derive forall" :: "exists' derive exists" ::
    "K modal modus ponens" :: "I induction" ::
    "all dual" :: "all eliminate" :: "exists eliminate" ::
    Nil
  private val limitedSchematicAxioms = "[:=] assign equality" :: "[:=] assign" :: "[:=] assign equality exists" ::
    "[:=] self assign" :: "[':=] differential assign" :: "[:*] assign nondet" :: "[?] test" ::
    "DE differential effect" :: "DG differential ghost" :: "DG differential ghost constant" ::
    "DG inverse differential ghost system" :: "DG inverse differential ghost" ::
    "DS& differential equation solution" ::
    //"c()' derive constant fn" :: //@todo would need to avoid all variables here
    "x' derive var" ::
    "V vacuous" :: "vacuous all quantifier" ::
    "const congruence" :: "const formula congruence" ::
    Nil


  private val axiomNames = schematicAxioms ++ limitedSchematicAxioms

  //@todo not all arity 1 predicationals will be supported during unification
  "Random Instance Unification" should "instantiate keys of schematic axioms to random schematic instantiations" in {
    for (ax <- axiomNames) {
      println("Axiom " + ax)
      for (i <- 1 to randomTrials) {
        val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        if (AxiomInfo(ax).formula.at(AxiomIndex.axiomIndex(ax)._1)._2.isInstanceOf[Formula]) {
          val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
            rand.nextSchematicInstance(Provable.axiom(ax).at(AxiomIndex.axiomIndex(ax)._1)._2.asInstanceOf[Formula], randomComplexity, false)
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
  it should "instantiate full schematic axioms to random schematic instantiations" in {
    for (ax <- axiomNames) {
      println("Axiom " + ax)
      for (i <- 1 to randomTrials/5) {
        val randClue = "Instance produced for " + ax + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
          rand.nextSchematicInstance(AxiomInfo(ax).formula, randomComplexity, false)
        }

        withSafeClue("Random instance " + inst + "\n\n" + randClue) {
          println("match instance: " + inst)
          matchDirect(ax, inst)
        }
      }
    }
  }

  it should "instantiate random formulas to their random schematic instantiations" in {
    for (k <- 1 to randomTrials) {
      val fml = rand.nextFormula(randomComplexity)
      for (i <- 1 to randomTrials) {
        val randClue = "Instance produced for " + fml + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
          rand.nextSchematicInstance(fml, randomComplexity, false)
        }

        withSafeClue("Random instance " + inst + "\n\n" + randClue) {
          println("match instance: " + inst)
          val u = unify(fml, inst)
          println("unify1:  " + fml)
          println("unify2:  " + inst)
          println("unifier: " + u)
          u(fml) shouldBe inst
          //@todo this might fail when the instance requires semantic renaming
          u.toCore(fml) shouldBe inst
        }
      }
    }
  }

  "Random Renamed Instance Unification" should "instantiate keys of schematic axioms to random schematic instantiations" in {
    for (ax <- axiomNames) {
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

  //@todo not all arity 1 predicationals will be supported during unification
  it should "instantiate full schematic axioms to random schematic instantiations" in {
    for (ax <- axiomNames) {
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

  it should "instantiate random formulas to their random schematic instantiations" in {
    for (k <- 1 to randomTrials) {
      val fml = rand.nextFormula(randomComplexity)
      for (i <- 1 to randomTrials) {
        val randClue = "Instance produced for " + fml + " in\n\t " + i + "th run of " + randomTrials +
          " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

        val inst = withSafeClue("Error generating schematic instance\n\n" + randClue) {
          rand.nextSchematicInstance(fml, randomComplexity)
        }

        withSafeClue("Random instance " + inst + "\n\n" + randClue) {
          println("match instance: " + inst)
          val u = unify(fml, inst)
          println("unify1:  " + fml)
          println("unify2:  " + inst)
          println("unifier: " + u)
          u(fml) shouldBe inst
          //@todo this might fail when the instance requires semantic renaming
          u.toCore(fml) shouldBe inst
        }
      }
    }
  }
}
