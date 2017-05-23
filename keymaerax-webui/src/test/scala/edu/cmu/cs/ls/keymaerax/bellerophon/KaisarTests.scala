package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.Kaisar._
import edu.cmu.cs.ls.keymaerax.btactics.{Kaisar, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._


/**
  * Created by bbohrer on 12/3/16.
  */
class KaisarTests extends TacticTestBase {
  val pq:Formula = "p() & q()".asFormula
  val p:Formula = "p()".asFormula

  "Proof with no programs" should "prove" in {
    withZ3 (qeTool => {
      val pr: Provable = Provable.startProof(Imply(pq, p))
      val up: UP = UP(List(Left("x".asExpr)), Auto())
      val show: Show = Show(p, up)
      val sp: SP = BRule(RBAssume(Variable("x"), pq), List(show))
      Kaisar.eval(sp, History.empty, Context.empty, pr) shouldBe 'proved
    })
  }
  "Proof with one program that modifies nothing" should "prove" in {
    withZ3 (qeTool => {
      val box = "[?p();]p()".asFormula
      val prog = "?p();".asProgram
      val pr:Provable = Provable.startProof(box)
      val sp = BRule(RBAssume(Variable("x"),"p()".asFormula), List(Show("p()".asFormula, UP(List(Left("x".asExpr)), Auto()))))
      Kaisar.eval(sp, History.empty, Context.empty, pr) shouldBe 'proved

    })
  }
  "Proof with one program that modifies a relevant variable" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=1;]x>0".asFormula
      val prog = "x:=1;".asProgram
      val sp =
        BRule(RBAssign(Assign("x".asVariable, "1".asTerm)),
        List(Show("1>0".asFormula, UP(List(), Auto()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }

  "Proof with one program that modifies a relevant variable and time-traveling that variable" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=1;]x>0".asFormula
      val prog = "x:=1;".asProgram
      val sp =
        BRule(RBAssign(Assign("x".asVariable, "1".asTerm)),
        List(Show("x>0".asFormula, UP(List(), Auto()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }

  /* Multiple programs */
  /* This test will pass once we start V()-ing in the appropriate programs after doing a step. */
  "Proof with two programs that independently modify a relevant variable" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=2;][x:= 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=1;".asProgram
      val sp =
        BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
          List(
        BRule(RBAssign(Assign("x".asVariable, "1".asTerm)),
          List(Show("1>0".asFormula, UP(List(), Auto()))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }

  /* Use programs */
  "Proof with using of program" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=x - 1;".asProgram
      val sp:SP =
        BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
          List(
        BRule(RBAssign(Assign("x".asVariable, "2 - 1".asTerm)),
          List(Show("2 - 1>0".asFormula, UP(List(), Auto()))))))
      //val e: BelleExpr = debug("what1") & chase(1) & debug("what2") & QE
      //val proof: Proof = (box, List(Run(Variable("a"), prog1), Run(Variable("b"), prog2), Show(Variable("x"), "x>0".asFormula, (List(ProgramVariable(Variable("a"))), e))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  /* Use facts */
  "Proof with one fact" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=x - 1;".asProgram
      // TODO: Add timestep(e) notation and manage different renaming for assign vs. ODE
      val sp:SP =
        BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
          List(Have("xBig".asVariable, "2 > 1".asFormula, Show("2 > 1".asFormula, UP(List(Left("p(x)".asExpr)), Kaisar.RCF())),
        BRule(RBAssign(Assign("x".asVariable, "2 - 1".asTerm)),
          List(Show("2 - 1>0".asFormula, UP(List(), Auto())))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }

  /* Use facts */
  "Proof with two facts" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=x - 1;".asProgram
      val sp:SP =
        BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
          // TODO: Uniqueness checking for pattern matching should break this
          List(Have("xBig".asVariable, "2 > 1".asFormula, Show("2 > 1".asFormula, UP(List(Left("p(x)".asExpr)), Kaisar.RCF())),
            Have("xNonZero".asVariable, "2 != 0".asFormula, Show("2 != 0".asFormula, UP(List(Left("p(x)".asExpr)), Kaisar.RCF())),
            BRule(RBAssign(Assign("x".asVariable, "2 - 1".asTerm)),
              List(Show("2 - 1>0".asFormula, UP(List(), Auto()))))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with two facts further in future" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x := 3;][x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=3;".asProgram
      val prog2 = "x:=2;".asProgram
      val prog3 = "x:=x - 1;".asProgram
      val sp:SP =
        BRule(RBAssign(Assign("x".asVariable, "3".asTerm)),
          // TODO: Uniqueness checking for pattern matching should break this
          List(
        BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
          List(Have("xBig".asVariable, "x > 1".asFormula, Show("x > 1".asFormula, UP(List(Left("p(x)".asExpr)), Kaisar.RCF())),
            Have("xNonZero".asVariable, "x != 0".asFormula, Show("x != 0".asFormula, UP(List(Left("p(x)".asExpr)), Kaisar.RCF())),
              BRule(RBAssign(Assign("x".asVariable, "2 - 1".asTerm)),
                List(Show("x>0".asFormula, UP(List(), Auto()))))))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with two facts further in future with time travel" should "prove" in {
    withZ3 (qeTool => {
      val box = "[x := 3;][x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=3;".asProgram
      val prog2 = "x:=2;".asProgram
      val prog3 = "x:=x - 1;".asProgram
      val sp:SP =
        BRule(RBAssign(Assign("x".asVariable, "3".asTerm)),
            // TODO: Uniqueness checking for pattern matching should break this
          List(
            PrintGoal("After first assign",
              BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
              List(
                PrintGoal("After second assign",
                Have("xBig".asVariable, "x > 1".asFormula, Show("x > 1".asFormula, UP(List(Left("p(x)".asExpr)), Kaisar.RCF())),
                Have("xNonZero".asVariable, "x != 0".asFormula, Show("x != 0".asFormula, UP(List(Left("p(x)".asExpr)), Kaisar.RCF())),
                  PrintGoal("After third assign",
                    BRule(RBAssign(Assign("x".asVariable, "x - 1".asTerm)),
                    List(Show("2-1>0".asFormula, UP(List(), Auto())))))))))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with loop with one invariant, no constant formulas" should "prove" in {
    withZ3(qeTool => {
      val box = "x = 0 -> [{x:=x+1;}*]x>=0".asFormula
      val sp:SP =
        BRule(RBAssume("x".asVariable, "x = 0".asFormula),
        List(BRule(RBInv(
          Inv("x >= 0".asFormula, Show("x >= 0".asFormula, UP(List(), Auto())),
            BRule(RBAssign(Assign("x".asVariable, "x+1".asTerm)), List(Show("x >= 0".asFormula, UP(List(),Auto())))),
            Finally(Show("x>= 0".asFormula, UP(List(),Auto()))))),
          List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with loop with two successive invariants, no constant formulas" should "prove" in {
    withZ3(qeTool => {
      // TODO: Implement currying conversion rule
      val box = "x = 0 & y = 1 -> [{y:=y+x; x:=x+1;}*]y>=0".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x = 0 & y = 1".asFormula),
          List(BRule(RBInv(
            Inv("x >= 0".asFormula, pre = Show("x >= 0".asFormula, UP(List(), Auto())),
              inv = BRule(RBAssign(Assign("y".asVariable, "y+x".asTerm)),
                List(BRule(RBAssign(Assign("x".asVariable, "x+1".asTerm)),
                  List(Show("x >= 0".asFormula, UP(List(), Auto())))))),
              tail =
                Inv(fml = "y >= 1".asFormula, pre = Show("y >= 1".asFormula, UP(List(), Auto())),
                  inv = BRule(RBAssign(Assign("y".asVariable, "y+x".asTerm)),
                    List(BRule(RBAssign(Assign("x".asVariable, "x+1".asTerm)),
                      List(Show("y >= 1".asFormula, UP(List(), Auto())))))),
                  tail = Finally(Show("y>= 0".asFormula, UP(List(), Auto())))))), tails = List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof of loop where constant proposition matters" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 0 & y > 0 -> [{x := x + y;}*]x>=0".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x > 0 & y > 1".asFormula),
          List(BRule(RBInv(
            Inv("x >= 0".asFormula, pre = Show("x >= 0".asFormula, UP(List(), Auto())),
              inv = BRule(RBAssign(Assign("x".asVariable, "x+y".asTerm)),
                  List(Show("x >= 0".asFormula, UP(List(), Auto())))),
              tail = Finally(Show("x>= 0".asFormula, UP(List(), Auto()))))), tails = List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof of easy differential invariant" should "prove" in {
    withZ3(qeTool => {
      val box = "x = 0 & y = 1 -> [{x' = -y, y' = x}]x^2 + y^2 > 0".asFormula
      val sp:SP =
        BRule(RBAssume("xy".asVariable, "x = 0 & y = 1".asFormula),
          List(BRule(RBInv(
            Inv("x^2 + y^2 = 1".asFormula, pre = Show("x^2 + y^2 = 1".asFormula, UP(List(), Auto())),
              inv = Show("(x^2 + y^2 = 1)'".asFormula, UP(List(), Auto())),
              tail = Finally(Show("x^2 + y^2 > 0".asFormula, UP(List(), Auto()))))
          ), List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with double differential invariant" should "prove" in {
    withZ3(qeTool => {
      val box = "x = 0 & y = 1 & dx = -1 & dy = 0 -> [{x' = dx*v, y'=dy*v, dx' = -dy*v, dy'=dx*v, v'=a}]x^2 + y^2 = 1".asFormula
      val sp:SP =
        BRule(RBAssume("assms".asVariable, "x = 0 & y = 1 & dx = -1 & dy = 0".asFormula),
          List(BRule(RBInv(
            Inv("dx=-y&dy=x".asFormula, Show("dx=-y&dy=x".asFormula, UP(List(), Auto())),
            inv = Show("(x^2 + y^2 = 1)'".asFormula, UP(List(), Auto())),
            tail =
              Inv("x^2 + y^2 = 1".asFormula, Show("x^2 + y^2 = 1".asFormula, UP(List(), Auto())),
                inv = Show("(x^2 + y^2 = 1)'".asFormula, UP(List(), Auto())),
                tail = Finally(Show("x^2 + y^2 = 1".asFormula, UP(List(), Auto()))))
            )
          ), List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with world's easiest diff ghost" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 0 -> [{x' = -x}]x > 0".asFormula
      val sp:SP =
        BRule(RBAssume("x".asVariable, "x > 0".asFormula),
          List(BRule(RBInv(
            Ghost("y".asVariable, "(1/2)*y + 0".asTerm, "x*y^2 = 1".asFormula, "(1/x)^(1/2)".asTerm, Show("x*y^2 = 1".asFormula, UP(List(), Auto())), Show("x*y^2=1".asFormula, UP(List(), Auto())),
              Inv("x*y^2=1".asFormula, Show("x*y^2=1".asFormula, UP(List(), Auto())), Show("x*y^2=1".asFormula, UP(List(), Auto())),
              Finally(Show("x*y^2=1".asFormula, UP(List(), Auto())))))
          ), List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
}
