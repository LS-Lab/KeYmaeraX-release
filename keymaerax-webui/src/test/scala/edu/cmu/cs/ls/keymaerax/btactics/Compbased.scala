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
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import testHelper.ParserFactory._

import scala.language.postfixOps

/**
  * Component-based proving test cases (FASE).
  * @author Stefan Mitsch
  */
@SlowTest
class Compbased extends TacticTestBase {

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
