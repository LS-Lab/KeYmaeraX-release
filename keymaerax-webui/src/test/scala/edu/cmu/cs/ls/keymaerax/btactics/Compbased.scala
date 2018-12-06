/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.components.ComponentSystem._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import edu.cmu.cs.ls.keymaerax.btactics.ModelPlex.createMonitorSpecificationConjecture
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps
import org.scalatest.LoneElement._

import scala.collection.immutable.List

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
    val entry = KeYmaeraXArchiveParser.getEntry("Remote Control Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3) shouldBe 'proved)
  }

  it should "prove obstacle contract compliance" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Obstacle Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3) shouldBe 'proved)
  }

  it should "prove choice implementation" in withMathematica { _ =>
    val s = Variable("s")
    def implementChoice(a: Program, b: Program, p: Formula) = Imply(
      Box(Choice(a,b), p),
      Box(Compose(Choice(Compose(a, Assign(s, Number(1))), Assign(s, Number(0))), Choice(Compose(Test(Equal(s, Number(0))), b), Compose(Test(Not(Equal(s, Number(0)))), Test(True)))), p))

    val equalReflex = proveBy("true <-> s()=s()".asFormula, equivR(1) <(cohideR(1) & byUS("= reflexive") & done, prop & done))
    equalReflex shouldBe 'proved

    val falseImplies = proveBy("true <-> (false -> p())".asFormula, prop & done)
    falseImplies shouldBe 'proved

    val notTrue = proveBy("false <-> !true".asFormula, prop & done)

    val oneIsNotZero = proveBy("false <-> 1=0".asFormula, QE() & done)

    proveBy(implementChoice("x:=2;".asProgram, "x:=3;".asProgram, "x>=2".asFormula),
      implyR(1) & choiceb(-1) & andL(-1) & composeb(1) & choiceb(1) & andR(1) <(
        composeb(1) & assignb(1, 1::Nil) & choiceb(1, 1::Nil) & composeb(1, 1::0::Nil) & testb(1, 1::0::Nil) & chase(1, 1::1::Nil) &
          useAt(oneIsNotZero, PosInExpr(1::Nil))(1, 1::0::0::Nil) & useAt(falseImplies, PosInExpr(1::Nil))(1, 1::0::Nil) &
          useAt(oneIsNotZero, PosInExpr(1::Nil))(1, 1::1::0::0::Nil) & useAt(notTrue, PosInExpr(0::Nil))(1, 1::1::0::0::Nil) &
          useAt("!! double negation")(1, 1::1::0::Nil) & useAt("true->", PosInExpr(0::Nil))(1, 1::1::Nil) &
          useAt("true&", PosInExpr(0::Nil))(1, 1::Nil) & closeId
        ,
        assignb(1) & choiceb(1) & andR(1) <(
          composeb(1) & testb(1) & useAt(equalReflex, PosInExpr(1::Nil))(1, 0::Nil) & useAt("true->")(1) & closeId
          ,
          composeb(1) & testb(1) & useAt(equalReflex, PosInExpr(1::Nil))(1, 0::0::Nil) &
            useAt(notTrue, PosInExpr(1::Nil))(1, 0::Nil) &
            useAt(falseImplies, PosInExpr(1::Nil))(1) & close
        )
      )) shouldBe 'proved
  }

  it should "generate obstacle monitor program" in withMathematica { tool =>
    val compileEqualityTest = proveBy("<?f_()=g_();>p_(||) <-> <if (f_()=g_()) { ?p_(||); } else { ?false; }>true".asFormula, chase(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileEqualityTest shouldBe 'proved

    val compileTest =  proveBy("<?p_();><a;>q_(||) <-> <if (p_()) { ?<a;>q_(||); } else { ?false; }>true".asFormula, testd(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileTest shouldBe 'proved

    val compileRegionTest = proveBy("<?p_();>true <-> <if (p_()) { ?true; } else { ?false; }>true".asFormula, testd(1, 0::Nil) & chase(1, 1::Nil) & prop & done)
    compileRegionTest shouldBe 'proved
    
    //@todo wrong sign (returns a formula with <= safe, > unsafe)
    def toMetric = "toMetric" by ((pos: Position, seq: Sequent) =>
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
    })

    val entry = KeYmaeraXArchiveParser.getEntry("Obstacle Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get

    val (modelplexInput, assumptions) = createMonitorSpecificationConjecture(entry.model.asInstanceOf[Formula],
      ("po"::"po0"::"so"::"t"::"t0"::Nil).map(Variable(_)):_*)
    val monitor = proveBy(modelplexInput, ModelPlex.modelMonitorByChase(1) & ModelPlex.optimizationOneWithSearch(Some(tool), assumptions)(1))
    monitor.subgoals.loneElement shouldBe "==> (0<=sopost&sopost<=S())&S()>=0&(((t0post<=tpost&t=t0post)&sopost=sopost)&po+sopost*tpost=popost+sopost*t)&po=po0post".asSequent

    val (equalities, inequalities) = FormulaTools.conjuncts(monitor.subgoals.loneElement.succ.loneElement).partition(_.isInstanceOf[Equal])
    val orderedMonitorFml = inequalities.reduceRightOption(And) match {
      case Some(ineqs) => equalities.lastOption match {
        case Some(lastEq) => equalities.updated(equalities.size-1, And(lastEq, ineqs)).reduceRight(And)
        case None => ineqs
      }
      case None => equalities.reduceRightOption(And).getOrElse(True)
    }
    orderedMonitorFml shouldBe "t=t0post&sopost=sopost&po+sopost*tpost=popost+sopost*t&po=po0post&0<=sopost&sopost<=S()&S()>=0&t0post<=tpost".asFormula
    val orderedMonitor = proveBy(monitor, useAt(proveBy(Equiv(monitor.subgoals.loneElement.succ.loneElement, orderedMonitorFml), prop & done), PosInExpr(0::Nil))(1))
    orderedMonitor.subgoals should have size 1

    val monitorAsTestsProgram = proveBy(orderedMonitor,
      RepeatTactic(ModelPlex.chaseToTests(combineTests=true)(1, PosInExpr(List.fill(equalities.size)(1))), 2) &
      ModelPlex.chaseToTests(combineTests=false)(1))
    monitorAsTestsProgram.subgoals.loneElement shouldBe "==> <?t=t0post;><?sopost=sopost;><?po+sopost*tpost=popost+sopost*t;><?po=po0post;><?((0<=sopost&sopost<=S())&S()>=0)&t0post<=tpost;>true".asSequent

    val compile = chaseCustom({
//      case Diamond(Test(False), _) => (compileFalseTest, PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil) :: Nil
      case Diamond(Test(Equal(_, _)), _) => (compileEqualityTest, PosInExpr(0::Nil), PosInExpr(0::0::1::0::Nil)::PosInExpr(0::1::1::0::Nil)::Nil) :: Nil
      case Diamond(Test(_), True) => (compileRegionTest, PosInExpr(0::Nil), Nil) :: Nil
      case _ => Nil
    })

    proveBy(monitorAsTestsProgram, compile(1) & toMetric(1) /* todo toMetric of all other tests */).subgoals.loneElement shouldBe
      "==> <?t=t0post;?<?sopost=sopost;?<?po+sopost*tpost=popost+sopost*t;?<?po=po0post;?<?((0<=sopost&sopost<=S())&S()>=0)&t0post<=tpost;?true;++?!(((0<=sopost&sopost<=S())&S()>=0)&t0post<=tpost);?false;>true;++?!po=po0post;?false;>true;++?!po+sopost*tpost=popost+sopost*t;?false;>true;++?!sopost=sopost;?false;>true;++?!t=t0post;?<margin:=1;>margin<=0;>true".asSequent
  }

  it should "prove robot contract compliance" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Robot Contract Compliance",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3) shouldBe 'proved)
  }

  it should "prove compatibility of obstacle and robot" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Compatibility of Obstacle and Robot",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3) shouldBe 'proved)
  }

  it should "prove communication guarantees" in withMathematica { _ =>
    val entry1 = KeYmaeraXArchiveParser.getEntry("Communication Guarantee Safety",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry1.tactics.foreach(t => proveBy(entry1.model.asInstanceOf[Formula], t._3) shouldBe 'proved)
    val entry2 = KeYmaeraXArchiveParser.getEntry("Communication Guarantee Liveness",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    entry2.tactics.foreach(t => proveBy(entry2.model.asInstanceOf[Formula], t._3) shouldBe 'proved)
  }

  it should "prove system safety" in withMathematica { _ =>
    val entry = KeYmaeraXArchiveParser.getEntry("Remote-Controlled Robot System Avoids Obstacles",
      io.Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/components/sttttacticalcomponents.kyx")).mkString).get
    proveBy(entry.model.asInstanceOf[Formula], proveSystem(
      "stttrunning/Robot Obstacle",
      "stttrunning/Robot Base Case",
      "stttrunning/Robot Use Case",
      "stttrunning/Robot Step",
      "stttrunning/Obstacle Base Case",
      "stttrunning/Obstacle Use Case",
      "stttrunning/Obstacle Step",
      "stttrunning/Compatibility of Obstacle and Robot",
      "stttrunning/Communication Guarantee Safety",
      "stttrunning/Communication Guarantee Liveness"
    )(1)) shouldBe 'proved

    entry.tactics.foreach(t => proveBy(entry.model.asInstanceOf[Formula], t._3) shouldBe 'proved)
  }

  "Robix" should "prove the robot component" in withZ3 { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/robix/robot.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/robix/robot.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove the auto-generated robot component" in withZ3 { implicit tool =>
    val model = "(t=0&v>=0&(abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B))&dx^2+dy^2=1&A>=0&B>0&V>=0&ep>0&xoIn0=xoIn&yoIn0=yoIn&t=tOld)&true->[{{{{{{xoIn0:=xoIn;yoIn0:=yoIn;}{a:=-B;++?v=0;a:=0;w:=0;++a:=*;?-B<=a&a<=A;k:=*;w:=*;?v*k=w;?abs(x-xoIn)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V))|abs(y-yoIn)>v^2/(2*B)+V*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V));}}tOld:=t;}{t'=1,x'=v*dx,y'=v*dy,dx'=-w*dy,dy'=w*dx,v'=a,w'=a*k&(t<=ep&v>=0)&t-tOld<=ep}}{xoIn:=*;?-V*(t-tOld)<=xoIn-xoIn0&xoIn-xoIn0<=V*(t-tOld);}yoIn:=*;?-V*(t-tOld)<=yoIn-yoIn0&yoIn-yoIn0<=V*(t-tOld);}?true;}*]((v>0->(x-xoIn)^2+(y-yoIn)^2>0)&true)".asFormula

    def invariant(t: String) =
      s"""v >= 0
        | & dx^2+dy^2 = 1
        | & 0 <= $t & $t <= ep
        | & -V*($t) <= xoIn-xoIn0 & xoIn-xoIn0 <= V*($t) & -V*($t) <= yoIn-yoIn0 & yoIn-yoIn0 <= V*($t)
        | & (v = 0 | abs(x-xoIn) > v^2 / (2*B) + V*(v/B)
        |          | abs(y-yoIn) > v^2 / (2*B) + V*(v/B))""".stripMargin.asFormula

    def di(a: String, t: String): DependentPositionTactic = diffInvariant(
      s"0<=$t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*($t)".asFormula,
      s"-($t) * (v - $a/2*($t)) <= x - old(x) & x - old(x) <= ($t) * (v - $a/2*($t))".asFormula,
      s"-($t) * (v - $a/2*($t)) <= y - old(y) & y - old(y) <= ($t) * (v - $a/2*($t))".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*3 /* 3 old(...) in DI */ & (andL('_)*) &
      print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('R) & (andL('L)*) & loop(invariant("t-tOld"))('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done") & done,
      /* use case */ print("Use case...") & speculativeQE & print("Use case done") & done,
      /* induction step */ print("Induction step") & chase(1) & print("After chase") & normalize(andR) & printIndexed("After normalize") <(
      print("Braking branch") & di("-B", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize(andR) & print("After braking normalize") & OnAll(speculativeQE) & print("Braking branch done") & done,
      print("Stopped branch") & di("0", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize(andR) & OnAll(speculativeQE) & print("Stopped branch done") & done,
      print("Acceleration branch") & hideL('L, "v=0|abs(x-xoIn)>v^2/(2*B)+V*(v/B)|abs(y-yoIn)>v^2/(2*B)+V*(v/B)".asFormula) &
        di("a", "t-tOld")(1) & print("After DI") & dw & print("After DW") & normalize & print("After acc normalize") & OnAll(hideFactsAbout("dx", "dy", "k", "k_0") partial) <(
        hideFactsAbout("y", "yoIn", "yoIn0") & accArithTactic & done,
        hideFactsAbout("x", "xoIn", "xoIn0") & accArithTactic & done
        ) & print("Acceleration branch done")
      ) & print("Induction step done") & done
      ) & print("Proof done") & done
    proveBy(model, tactic) shouldBe 'proved
  }

  it should "prove the obstacle component" in withZ3 { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/robix/obstacle.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/robix/obstacle.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove compatibility" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/robix/compatibility.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove monolithic model" in withZ3 { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/robix/system.kyx"))

    val invariant =
      """v >= 0
        | & dx^2+dy^2 = 1
        | & xo = xor & yo = yor
        | & (v = 0 | abs(x-xo) > v^2 / (2*B()) + V()*(v/B())
        |          | abs(y-yo) > v^2 / (2*B()) + V()*(v/B()))""".stripMargin.asFormula

    def di(a: String): DependentPositionTactic = diffInvariant(
      "0<=t".asFormula,
      "dx^2 + dy^2 = 1".asFormula,
      s"v = old(v) + $a*t".asFormula,
      s"-t * (v - $a/2*t) <= x - old(x) & x - old(x) <= t * (v - $a/2*t)".asFormula,
      s"-t * (v - $a/2*t) <= y - old(y) & y - old(y) <= t * (v - $a/2*t)".asFormula,
      "-t * V() <= xo - old(xo) & xo - old(xo) <= t * V()".asFormula,
      "-t * V() <= yo - old(yo) & yo - old(yo) <= t * V()".asFormula)

    val dw: BelleExpr = exhaustiveEqR2L(hide=true)('Llast)*5 /* 5 old(...) in DI */ & (andL('_)*) &
      print("Before diffWeaken") & dW(1) & print("After diffWeaken")

    def accArithTactic: BelleExpr = (alphaRule*) & printIndexed("Before replaceTransform") &
      //@todo auto-transform
      replaceTransform("ep".asTerm, "t".asTerm)(-8) & speculativeQE & print("Proved acc arithmetic")

    val tactic = implyR('_) & (andL('_)*) & loop(invariant)('R) <(
      /* base case */ print("Base case...") & speculativeQE & print("Base case done"),
      /* use case */ print("Use case...") & speculativeQE & print("Use case done"),
      /* induction step */ print("Induction step") & chase(1) & normalize(andR) & printIndexed("After normalize") <(
      print("Braking branch 1") & di("-B()")(1) & dw & prop & OnAll((cohide(1) & byUS("= reflexive")) | skip) & OnAll(speculativeQE) & print("Braking branch 1 done"),
      print("Braking branch 2") & di("-B()")(1) & dw & prop & OnAll((cohide(1) & byUS("= reflexive")) | skip) & OnAll(speculativeQE) & print("Braking branch 2 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Stopped branch 1 done"),
      print("Acceleration branch 1") & hideL('L, "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("a")(1) & dw & prop & OnAll((cohide(1) & byUS("= reflexive")) | skip) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0")) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch 1 done"),
      print("Stopped branch 1") & di("0")(1) & dw & prop & OnAll(((cohide(1) & byUS("= reflexive")) | skip) partial) & OnAll(speculativeQE) & print("Stopped branch 2 done"),
      print("Acceleration branch 2") & hideL('L, "v=0|abs(x-xo)>v^2/(2*B())+V()*(v/B())|abs(y-yo)>v^2/(2*B())+V()*(v/B())".asFormula) &
        di("a")(1) & dw & prop & OnAll((cohide(1) & byUS("= reflexive")) | skip) & OnAll(hideFactsAbout("dx", "dy", "dxo", "dyo", "k", "k_0")) <(
        hideFactsAbout("y", "yo") & accArithTactic,
        hideFactsAbout("x", "xo") & accArithTactic
        ) & print("Acceleration branch 2 done")
      ) & print("Induction step done")
      ) & print("Proof done")
    proveBy(s, tactic) shouldBe 'proved
  }

  "Multiport local lane control" should "prove the leader component" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_leader.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove the follower component" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_follower.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_follower.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  it should "prove compatibility" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_compatibility.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove the monolithic system" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_system.kyx"))
    val tactic = BelleParser(io.Source.fromInputStream(getClass.getResourceAsStream("/examples/casestudies/components/llc/multiport_system.kyt")).mkString)
    proveBy(s, tactic) shouldBe 'proved
  }

  "ETCS" should "prove RBC component" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_rbc.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove train component" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_train.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

  it should "prove compatibility" in withMathematica { implicit tool =>
    val s = parseToSequent(getClass.getResourceAsStream("/examples/casestudies/components/etcs/multiport_compatibility.kyx"))
    proveBy(s, master()) shouldBe 'proved
  }

}
