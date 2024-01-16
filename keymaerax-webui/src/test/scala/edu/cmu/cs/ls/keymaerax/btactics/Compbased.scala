/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.components.ComponentSystem._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.ModelPlex.createMonitorSpecificationConjecture
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

import scala.language.postfixOps
import org.scalatest.LoneElement._

import scala.collection.immutable.{List, ListMap}

/**
  * Component-based proving test cases (FASE).
  * @author Stefan Mitsch
  */
@SlowTest
class Compbased extends TacticTestBase {

  "Lemma 1" should "work for easy case" in withMathematica { _ =>
    proveBy("[x:=2;][y:=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [y:=3;][x:=2;]x+y>=5".asSequent
    proveBy("[x:=2;][y:=*;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [y:=*;][x:=2;]x+y>=5".asSequent
    proveBy("[x:=*;][y:=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [y:=3;][x:=*;]x+y>=5".asSequent
    proveBy("[x:=2;][?y>=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [?y>=3;][x:=2;]x+y>=5".asSequent
    proveBy("[x:=*;][?y>=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [?y>=3;][x:=*;]x+y>=5".asSequent
    proveBy("[?x>=2;][?y>=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [?y>=3;][?x>=2;]x+y>=5".asSequent
  }

  it should "work in context" in withMathematica { _ =>
    proveBy("[z:=1;][x:=2;][y:=3;]x+y>=5".asFormula, programIndependence()(1, 1::Nil)).subgoals.loneElement shouldBe "==> [z:=1;][y:=3;][x:=2;]x+y>=5".asSequent
    proveBy("[?z>=1;][x:=2;][y:=*;]x+y>=5".asFormula, programIndependence()(1, 1::Nil)).subgoals.loneElement shouldBe "==> [?z>=1;][y:=*;][x:=2;]x+y>=5".asSequent
    proveBy("[?z>=0;][?a<=1;][x:=*;][y:=3;]x+y>=5".asFormula, programIndependence()(1, 1::1::Nil)).subgoals.loneElement shouldBe "==> [?z>=0;][?a<=1;][y:=3;][x:=*;]x+y>=5".asSequent
    proveBy("[?z>=0;][a:=1;][x:=2;][?y>=3;]x+y>=5".asFormula, programIndependence()(1, 1::1::Nil)).subgoals.loneElement shouldBe "==> [?z>=0;][a:=1;][?y>=3;][x:=2;]x+y>=5".asSequent
    proveBy("[?z>=0;][a:=*;][x:=*;][?y>=3;]x+y>=5".asFormula, programIndependence()(1, 1::1::Nil)).subgoals.loneElement shouldBe "==> [?z>=0;][a:=*;][?y>=3;][x:=*;]x+y>=5".asSequent
    proveBy("[?x>=2;][?y>=3;]x+y>=5 -> z>=2".asFormula, programIndependence()(1, 0::Nil)).subgoals.loneElement shouldBe "==> [?y>=3;][?x>=2;]x+y>=5 -> z>=2".asSequent
  }

  it should "work when boxes are not split" in withMathematica { _ =>
    proveBy("[x:=2;y:=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [y:=3;x:=2;]x+y>=5".asSequent
    proveBy("[x:=2;y:=*;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [y:=*;x:=2;]x+y>=5".asSequent
    proveBy("[x:=*;y:=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [y:=3;x:=*;]x+y>=5".asSequent
    proveBy("[x:=2;?y>=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [?y>=3;x:=2;]x+y>=5".asSequent
    proveBy("[x:=*;?y>=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [?y>=3;x:=*;]x+y>=5".asSequent
    proveBy("[?x>=2;?y>=3;]x+y>=5".asFormula, programIndependence()(1)).subgoals.loneElement shouldBe "==> [?y>=3;?x>=2;]x+y>=5".asSequent
    proveBy("[?x>=2;?y>=3;][z:=3;]x+y>=5".asFormula, programIndependence(false)(1)).subgoals.loneElement shouldBe "==> [z:=3;][?x>=2;?y>=3;]x+y>=5".asSequent
  }

  "Lemma 2" should "work for easy case" in withMathematica { _ =>
    proveBy("[x:=2;][y:=3;]y>=3".asFormula, dropControl(1)).subgoals.loneElement shouldBe "==> [y:=3;]y>=3".asSequent
    proveBy("[x:=2;][y:=3;]x>=2".asFormula, dropControl(1)).subgoals.loneElement shouldBe "==> [x:=2;]x>=2".asSequent
  }

  "Lemma 3" should "work for easy case" in withMathematica { _ =>
    proveBy("x>=0 ==> [{x'=1,y'=2}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1}]x>=0".asSequent
    proveBy("x>=0 ==> [{x'=1,y'=2 & x>=-1 & y<=4}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1 & x>=-1}]x>=0".asSequent
    proveBy("x>=0 ==> [{x'=1,y'=2 & y<=4 & x>=-1}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1 & x>=-1}]x>=0".asSequent
    proveBy("x>=0 ==> [{x'=1,y'=2,z'=3}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1}]x>=0".asSequent
    proveBy("x>=0 ==> [{x'=1}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [{x'=1}]x>=0".asSequent
    //proveBy("x>=0 ==> [{y'=1}]x>=0".asSequent, dropPlant(Set("x".asVariable))(1)).subgoals.loneElement shouldBe "x>=0 ==> [?true;]x>=0".asSequent
  }

  "Lemma 4" should "work for easy case" in withMathematica { _ =>
    proveBy("[x:=5;]x>=0".asFormula, overapproximateProgram(1)).subgoals.loneElement shouldBe "==> [x:=*;]x>=0".asSequent
    proveBy("[x:=5;y:=6;z:=7;]x>=0".asFormula, overapproximateProgram(1)).subgoals.loneElement shouldBe "==> [x:=*;]x>=0".asSequent
    proveBy("[x:=5;y:=6;z:=7;]x+y+z>=0".asFormula, overapproximateProgram(1)).subgoals.loneElement shouldBe "==> [x:=*;y:=*;z:=*;]x+y+z>=0".asSequent
  }

  "Lemma 5" should "work" in withMathematica { _ =>
    proveBy("[x:=3;]x>=1".asFormula, introduceTest("x>=2".asFormula)(1) <(skip, master())).subgoals.loneElement shouldBe "==> [x:=3;][?x>=2;]x>=1".asSequent
  }

  "Lemma 6" should "work" in withMathematica { _ =>
    proveBy("[?x>=5;]x>=2".asFormula, weakenTest("x>=2".asFormula)(1)).subgoals.loneElement shouldBe "==> [?x>=2;]x>=2".asSequent
  }

  "STTT Examples" should "prove remote control contract compliance" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("Remote Control Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3, defs = entry.defs) shouldBe Symbol("proved"))
  }

  it should "prove obstacle contract compliance" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("Obstacle Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3, defs = entry.defs) shouldBe Symbol("proved"))
  }

  it should "prove choice implementation" in withMathematica { _ =>
    val s = Variable("s")
    def implementChoice(a: Program, b: Program, p: Formula) = Imply(
      Box(Choice(a,b), p),
      Box(Compose(Choice(Compose(a, Assign(s, Number(1))), Assign(s, Number(0))), Choice(Compose(Test(Equal(s, Number(0))), b), Compose(Test(Not(Equal(s, Number(0)))), Test(True)))), p))

    val equalReflex = proveBy("true <-> s()=s()".asFormula, equivR(1) <(cohideR(1) & byUS(Ax.equalReflexive) & done, prop & done))
    equalReflex shouldBe Symbol("proved")

    val falseImplies = proveBy("true <-> (false -> p())".asFormula, prop & done)
    falseImplies shouldBe Symbol("proved")

    val notTrue = proveBy("false <-> !true".asFormula, prop & done)

    val oneIsNotZero = proveBy("false <-> 1=0".asFormula, QE & done)

    proveBy(implementChoice("x:=2;".asProgram, "x:=3;".asProgram, "x>=2".asFormula),
      implyR(1) & choiceb(-1) & andL(-1) & composeb(1) & choiceb(1) & andR(1) <(
        composeb(1) & assignb(1, 1::Nil) & choiceb(1, 1::Nil) & composeb(1, 1::0::Nil) & testb(1, 1::0::Nil) & chase(1, 1::1::Nil) &
          useAt(oneIsNotZero, PosInExpr(1::Nil))(1, 1::0::0::Nil) & useAt(falseImplies, PosInExpr(1::Nil))(1, 1::0::Nil) &
          useAt(oneIsNotZero, PosInExpr(1::Nil))(1, 1::1::0::0::Nil) & useAt(notTrue, PosInExpr(0::Nil))(1, 1::1::0::0::Nil) &
          useAt(Ax.doubleNegation)(1, 1::1::0::Nil) & useAt(Ax.trueImply, PosInExpr(0::Nil))(1, 1::1::Nil) &
          useAt(Ax.trueAnd, PosInExpr(0::Nil))(1, 1::Nil) & id
        ,
        assignb(1) & choiceb(1) & andR(1) <(
          composeb(1) & testb(1) & useAt(equalReflex, PosInExpr(1::Nil))(1, 0::Nil) & useAt(Ax.trueImply)(1) & id
          ,
          composeb(1) & testb(1) & useAt(equalReflex, PosInExpr(1::Nil))(1, 0::0::Nil) &
            useAt(notTrue, PosInExpr(1::Nil))(1, 0::Nil) &
            useAt(falseImplies, PosInExpr(1::Nil))(1) & close
        )
      )) shouldBe Symbol("proved")
  }

  it should "generate obstacle monitor program" in withMathematica { tool =>
    val compileEqualityTest = proveBy("<?f_()=g_();>p_(||) <-> <if (f_()=g_()) { ?p_(||); } else { ?false; }>true".asFormula, chase(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileEqualityTest shouldBe Symbol("proved")

    val compileTest =  proveBy("<?p_();><a;>q_(||) <-> <if (p_()) { ?<a;>q_(||); } else { ?false; }>true".asFormula, testd(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileTest shouldBe Symbol("proved")

    val compileRegionTest = proveBy("<?p_();>true <-> <if (p_()) { ?true; } else { ?false; }>true".asFormula, testd(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileRegionTest shouldBe Symbol("proved")
    
    //@todo wrong sign (returns a formula with <= safe, > unsafe)
    def toMetric = anon ((pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
      case Some(Diamond(Choice(Compose(Test(p: Equal), _), Compose(Test(Not(q: Equal)), Test(False))), _)) if p==q =>
        val metric = proveBy(Equiv(False, "<margin:=1;>margin<=0".asFormula), assignd(1, 1::Nil) & QE & done)
        useAt(metric, PosInExpr(0::Nil))(pos ++ PosInExpr(0::1::1::0::Nil))
      case Some(Diamond(Choice(Compose(Test(p), Test(True)), Compose(Test(Not(q)), Test(False))), _)) if p==q =>
        val LessEqual(metric, _) = ModelPlex.toMetric(p)
        val margin = Variable("margin")
        val repl = proveBy(Imply(p, Equiv(True, Diamond(Assign(margin, metric), LessEqual(margin, Number(0))))),
          assignd(1, 1::1::Nil) & QE & done)
        useAt(repl, PosInExpr(1::0::Nil))(pos ++ PosInExpr(0::0::1::0::Nil))
      case Some(e) => throw new TacticInapplicableFailure("toMetric only applicable to diamond properties, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    })

    val entry = ArchiveParser.getEntry("Obstacle Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get

    val ModelPlexConjecture(_, modelplexInput, assumptions) = createMonitorSpecificationConjecture(entry.model.asInstanceOf[Formula],
      List("po","po0","so","t","t0").map(Variable(_)), ListMap.empty)
    val monitor = proveBy(modelplexInput, expandAllDefs(entry.defs.substs) & ModelPlex.modelMonitorByChase(1) &
      ModelPlex.optimizationOneWithSearch(Some(tool), assumptions, Nil, Some(ModelPlex.mxSimplify))(1), defs = entry.defs)
    monitor.subgoals.loneElement shouldBe "==> (0<=sopost&sopost<=S())&true&(((t0post<=tpost&t=t0post)&sopost=sopost)&po+sopost*tpost=popost+sopost*t)&po=po0post".asSequent

    val (equalities, inequalities) = FormulaTools.conjuncts(monitor.subgoals.loneElement.succ.loneElement).partition(_.isInstanceOf[Equal])
    val orderedMonitorFml = inequalities.reduceRightOption(And) match {
      case Some(ineqs) => equalities.lastOption match {
        case Some(lastEq) => equalities.updated(equalities.size-1, And(lastEq, ineqs)).reduceRight(And)
        case None => ineqs
      }
      case None => equalities.reduceRightOption(And).getOrElse(True)
    }
    orderedMonitorFml shouldBe "t=t0post&sopost=sopost&po+sopost*tpost=popost+sopost*t&po=po0post&0<=sopost&sopost<=S()&true&t0post<=tpost".asFormula
    val orderedMonitor = proveBy(monitor, useAt(proveBy(Equiv(monitor.subgoals.loneElement.succ.loneElement, orderedMonitorFml), prop & done), PosInExpr(0::Nil))(1))
    orderedMonitor.subgoals should have size 1

    val monitorAsTestsProgram = proveBy(orderedMonitor,
      RepeatTactic(ModelPlex.chaseToTests(combineTests=true)(1, PosInExpr(List.fill(equalities.size)(1))), 2) &
      ModelPlex.chaseToTests(combineTests=false)(1))
    monitorAsTestsProgram.subgoals.loneElement shouldBe "==> <?t=t0post;><?sopost=sopost;><?po+sopost*tpost=popost+sopost*t;><?po=po0post;><?((0<=sopost&sopost<=S())&true)&t0post<=tpost;>true".asSequent

    val compile = chaseCustom({
//      case Diamond(Test(False), _) => (compileFalseTest, PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil) :: Nil
      case Diamond(Test(Equal(_, _)), _) => (compileEqualityTest, PosInExpr(0::Nil), PosInExpr(0::0::1::0::Nil)::PosInExpr(0::1::1::0::Nil)::Nil) :: Nil
      case Diamond(Test(_), True) => (compileRegionTest, PosInExpr(0::Nil), Nil) :: Nil
      case _ => Nil
    })

    proveBy(monitorAsTestsProgram, compile(1) & toMetric(1) /* todo toMetric of all other tests */).subgoals.loneElement shouldBe
      "==> <?t=t0post;?<?sopost=sopost;?<?po+sopost*tpost=popost+sopost*t;?<?po=po0post;?<?((0<=sopost&sopost<=S())&true)&t0post<=tpost;?true;++?!(((0<=sopost&sopost<=S())&true)&t0post<=tpost);?false;>true;++?!po=po0post;?false;>true;++?!po+sopost*tpost=popost+sopost*t;?false;>true;++?!sopost=sopost;?false;>true;++?!t=t0post;?<margin:=1;>margin<=0;>true".asSequent
  }

  it should "prove robot contract compliance" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("Robot Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3, defs = entry.defs) shouldBe Symbol("proved"))
  }

  it should "prove compatibility of obstacle and robot" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("Compatibility of Obstacle and Robot",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3, defs = entry.defs) shouldBe Symbol("proved"))
  }

  it should "prove communication guarantees" in withMathematica { _ =>
    val entry1 = ArchiveParser.getEntry("Communication Guarantee Safety",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry1.tactics.foreach(t => proveBy(entry1.model.asInstanceOf[Formula], t._3, defs = entry1.defs) shouldBe Symbol("proved"))
    val entry2 = ArchiveParser.getEntry("Communication Guarantee Liveness",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry2.tactics.foreach(t => proveBy(entry2.model.asInstanceOf[Formula], t._3, defs = entry2.defs) shouldBe Symbol("proved"))
  }

  it should "prove system safety" in withMathematica { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val entry = ArchiveParser.getEntry("Remote-Controlled Robot System Avoids Obstacles",
        io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
      proveBy(entry.model.asInstanceOf[Formula], expandAllDefs(entry.defs.substs) & proveSystem(
        "robotcomponents/Robot Obstacle",
        "robotcomponents/Robot Base Case",
        "robotcomponents/Robot Use Case",
        "robotcomponents/Robot Step",
        "robotcomponents/Obstacle Base Case",
        "robotcomponents/Obstacle Use Case",
        "robotcomponents/Obstacle Step",
        "robotcomponents/Compatibility of Obstacle and Robot",
        "robotcomponents/Communication Guarantee Safety",
        "robotcomponents/Communication Guarantee Liveness"
      )(1), defs = entry.defs) shouldBe Symbol("proved")

      entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3, defs = entry.defs) shouldBe Symbol("proved"))
    }
  }

  "Robix" should "prove the robot component" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("Robot Component",
      io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/robix/robot.kyx")).mkString).get
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3) shouldBe Symbol("proved")
  }

  it should "prove the obstacle component" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("Obstacle Component",
      io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/robix/obstacle.kyx")).mkString).get
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3) shouldBe Symbol("proved")
  }

  it should "prove compatibility" in withMathematica { _ =>
    val s = ArchiveParser.parseAsFormula(getClass.getResourceAsStream("/examples/casestudies/components/robix/compatibility.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove monolithic model" in withMathematica { _ =>
    val s = ArchiveParser.parseAsFormula(getClass.getResourceAsStream("/examples/casestudies/components/robix/system.kyx"))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & xo = xor & yo = yor
        | & (v = 0 | abs(x-xo) > v^2 / (2*B()) + V()*(v/B())
        |          | abs(y-yo) > v^2 / (2*B()) + V()*(v/B()))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "0<=t".asFormula ::
      "dx^2 + dy^2 = 1".asFormula ::
      s"v = old(v) + $a*t".asFormula ::
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula ::
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula ::
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula ::
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula :: Nil)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)(Symbol("Llast"))*5 /* 5 old(...) in DI */ & SaturateTactic(andL(Symbol("L"))) &
      print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    val simpQE = SaturateTactic(alphaRule) & SimplifierV3.fullSimpTac() & printIndexed("SimpQE") & speculativeQE

    def accArithTactic: BelleExpr = SaturateTactic(alphaRule) & printIndexed("Before replaceTransform") &
      //@todo auto-transform
      replaceTransform("ep()".asTerm, "t".asTerm)(-7) & printIndexed("Transformed") & simpQE & print("Proved acc arithmetic")

    val tactic = implyR(Symbol("_")) & SaturateTactic(andL(Symbol("_"))) & loop(invariant)(Symbol("R")) <(
      /* base case */ print("Base case...") & simpQE & print("Base case done"),
      /* use case */ print("Use case...") & simpQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & unfoldProgramNormalize & printIndexed("After normalize") <(
      print("Braking branch 1") & di("-B()")(1) & dw & prop & OnAll((cohide(1) & byUS(Ax.equalReflexive)) | skip) & OnAll(simpQE) & print("Braking branch 1 done"),
      print("Braking branch 2") & di("-B()")(1) & dw & prop & OnAll((cohide(1) & byUS(Ax.equalReflexive)) | skip) & OnAll(simpQE) & print("Braking branch 2 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll((cohide(1) & byUS(Ax.equalReflexive)) | skip) & OnAll(simpQE) & print("Stopped branch 1 done"),
      print("Acceleration branch 1") & hideL(Symbol("L"), "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("a")(1) & dw & prop & OnAll((cohide(1) & byUS(Ax.equalReflexive)) | skip) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0", "dx_0", "dy_0")) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch 1 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll((cohide(1) & byUS(Ax.equalReflexive)) | skip) & OnAll(simpQE) & print("Stopped branch 2 done"),
      print("Acceleration branch 2") & hideL(Symbol("L"), "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("a")(1) & dw & prop & OnAll((cohide(1) & byUS(Ax.equalReflexive)) | skip) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0", "dx_0", "dy_0")) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch 2 done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  "Multiport local lane control" should "prove the leader component" in withMathematica { _ =>
    val fml = ArchiveParser.parseAsFormula(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_leader.kyx"))
    proveBy(fml, master()) shouldBe Symbol("proved")
  }

  it should "prove the follower component" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("Follower Component",
      io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_follower.kyx")).mkString).get
    proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3) shouldBe Symbol("proved")
  }

  it should "prove compatibility" in withMathematica { _ =>
    val s = ArchiveParser.parseAsFormula(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_compatibility.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove the monolithic system" in withMathematica { _ =>
    val entry = ArchiveParser.getEntry("Full System",
      io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_system.kyx")).mkString).get
    withTacticProgress(entry.tactics.head._3) {
      proveBy(entry.model.asInstanceOf[Formula], _)
    } shouldBe Symbol("proved")
  }

  "ETCS" should "prove RBC component" in withMathematica { _ =>
    val s = ArchiveParser.parseAsFormula(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_rbc.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove train component" in withMathematica { _ =>
    val s = ArchiveParser.parseAsFormula(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_train.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  it should "prove compatibility" in withMathematica { _ =>
    val s = ArchiveParser.parseAsFormula(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_compatibility.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

}
