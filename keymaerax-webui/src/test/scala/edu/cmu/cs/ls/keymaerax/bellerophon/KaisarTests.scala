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
  "DaLi'17 Example 1a" should "prove" in {
    withZ3(qeTool => {
    val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
    val sp:SP =
      BRule(RBAssume("xy".asVariable, "x > 1 & y = 0".asFormula),
        List(Show("(x-1)^2 != (x+1)^2".asFormula, UP(Nil, Kaisar.RCF()))))
    Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
  })}
  "DaLi'17 Example 1b" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
      val sp:SP =
        BRule(RBAssume("xy".asVariable, "x_() & y_()".asFormula), List(
          Show("wild()".asFormula, UP(Nil, Kaisar.RCF()))
        ))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })}
  "DaLi'17 Example 1c" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
      val sp:SP =
        BRule(RBAssume("xy".asVariable, "x_() & y_()".asFormula), List(
          Have("x".asVariable, "x != 0".asFormula, Show("x != 0".asFormula, UP(List(Left("xy".asVariable)), Kaisar.RCF())),
          Show("wild()".asFormula, UP(Nil, Kaisar.RCF())))
        ))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })}

  "DaLi'18 Example 1d" should "prove" in {
    withZ3(qeTool => {
      val box =
        "(x + y + z > 1 & huge = 0 -> (x + y + z -1)^2 != (x + y + z + 1)^2)".asFormula
      val sp:SP =
        SLet("w_()".asTerm, "x + y + z".asTerm,
        BRule(RBAssume("xy".asVariable,"w_() > 1 & wild()".asFormula),List(
          Note("w".asVariable, FMP(FPat("andE1()".asFormula), FPat("xy".asVariable)),
            Show("wild()".asFormula, UP(List(Left("w_()".asFormula)),Kaisar.RCF()))
            )
        )))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
/*# Example 1d
# prove (x + y + z > 1 & huge = 0 ->
# (x + y + z -1)^2 != (x + y + z + 1)^2)
let ?w = (x + y + z)
assume xy:(?w > 1  & _)
note w = (andE1 xy)
show (_)
  using w by R
*/
  "DaLi'18 Example 2a" should "prove" in {
    withZ3(qeTool => {
      ???
    })
  }
/*
* x=2\cdot y\limply \left[\left\{\{?(x<-2);x:=x^2\}\cup y:=\frac{1}{3}\cdot y\right\}x:=x\cdot 2\right]x > 2\cdot y
* # Example 2a
assume xy:(x=2*y)
case (?(x<-2); _)
  assume x:(x<-2)
  assign x:=x^2
  show(x > 2*y)
    by auto
case (y := _)
  assign (y:=(1/3)*y)
  assign x:=x^2
  show (x > 2*y)
    by auto
*/
  "DaLi'18 Example 2b" should "prove" in {
    withZ3(qeTool => {
      ???
    })
  }
  /*# Example 2b
assume xy:(x=2*y)
mid J:(x>y)
  show ([_]x>y) by auto
assign x:=x*2
show (x > 2y) using J by auto
*/
  "DaLi'18 Example 2c" should "prove" in {
    withZ3(qeTool => {
      ???
    })
  }
/*# Example 2c
assume xy:(x=2*y)
mid J:(x>y)
  show ([_]x>y) by auto
state pre-assign
assign x:=x*2
have xs:(x >= 2*pre-assign(x) & pre-assign(x) > y)
  by auto
show _ using J by auto
*/
"DaLi'18 Example 2d" should "prove" in {
    withZ3(qeTool => {
      ???
    })
  }
  // x=0\land{y=1}\limply[\{y:= (1/2)\cdot{y}\}^*;\{x:=x+y;y:=(1/2)\cdot{y}\}^*;\{x:=x+y\}^*]x \geq 0

  /*#Example 3
assume xy:(x=0&y=1)
time init
Inv J1:(y > 0)            { Pre => show _ by R | Inv => show _ by R }
time t1
Inv J2:(y>0 & x>=init(x)) { Pre => show _ by R | Inv => show _ by R }
time t2
Inv J3:(y>0 & x>=t2(x))   { Pre => show _ by R | Inv => show _ by R }
show (y >= 0) using J1 J2 J3 by R
*/
  "DaLi'18 Example 3" should "prove" in {
    withZ3(qeTool => {
      ???
    })
  }
  /*  g>0\land &y\geq H\land H>0\land v_y=0 \limply\\
\Big[\Big\{\big\{  &\{?(y>0\vee v_y\geq 0)\}  \cup  \{?(y\leq 0\wedge v_y < 0); v_y := -v_y\}\big\}\\
          &\{y'=v_y,v_y'=-g \& y\geq 0\}\\
\Big\}^*\Big](&0 \leq y \wedge y \leq H)\\
*/

  /*assume assms:(g>0 & y>=H & H>0 & vy=0)
let ?E(t) = t(v^2/2 + H)
time init
Inv J(y >= 0 & ??E = init(E) {
  Inv =>
   time loop-init
   mid (?E = loop-init(E))
     show [_ U _]_ by auto
   solve {_ & ?dc} t:(t>=0) dc:?dc
     show _ by auto }
show _  using J assms by auto
*/
  "DaLi'18 Example 4" should "prove" in {
    withZ3(qeTool => {
      ???
    })
  }
  // x>0\wedge{y>0}\limply[\{x'=-x,y'=x\}]y>0

  /* assume assms:(x>0 & y>0)
time init
Ghost z'=x/2, z = (1/x)^(1/2)
Inv JG:(x*z^2 = 1)
Inv Jx:(x > 0)
Inv Jy:(y > init(y))
show (Jy > 0) using assms Jy by auto
*/
  "DaLi'18 Example 5" should "prove" in {
    withZ3(qeTool => {
      ???
    })
  }
}
