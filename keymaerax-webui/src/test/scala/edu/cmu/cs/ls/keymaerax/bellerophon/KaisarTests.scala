package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.Kaisar.{BRule, _}
import edu.cmu.cs.ls.keymaerax.btactics.{Kaisar, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.collection.immutable


/**
  * Created by bbohrer on 12/3/16.
  */
class KaisarTests extends TacticTestBase {
  val pq: Formula = "p() & q()".asFormula
  val p: Formula = "p()".asFormula
  val h1 = History(List(HCRename(Variable("x"), Variable("x", Some(1))), HCTimeStep("t2"), HCTimeStep("init")))
  val h2 = History(List(HCAssign(Assign(Variable("x"), "x*2".asTerm)), HCTimeStep("preassign"), HCRename(Variable("x"), Variable("x", Some(0))), HCRename(Variable("y"), Variable("y", Some(0))), HCTimeStep("init")))
  val h3 = History(List(HCRename(Variable("y"), Variable("y", Some(1))), HCRename(Variable("x"), Variable("x", Some(0))), HCTimeStep("t1"), HCRename(Variable("y"), Variable("y", Some(0))), HCTimeStep("init")))
  val h4 = History(List(HCRename(Variable("v"), Variable("v", Some(1))), HCTimeStep("loopinit"), HCRename(Variable("y"), Variable("y", Some(0))), HCRename(Variable("v"), Variable("v", Some(0))), HCTimeStep("init"), HCTimeStep("init")))
  val c1 = Context(Map(), Map(), Map())
  val c2 = Context(Map(), Map(), Map("E" -> ("t", "t(v^2/2 + y)".asTerm)))
  val duh: SP = Show("wild()".asFormula, UP(List(), Kaisar.Auto()))
  //,x>=0, becomes ,x_0>=0, under history ,History(List(HCRename(x,x_0,None), HCTimeStep(init))), and context ,Context(Map(x -> -1),Map()))
  //"Variable resolution" should "notice renaming after new state" in {
  //    val res = h1.resolve("x", "t2")
  //    res shouldBe Variable("x",Some(1))
  //  }

  "Variable resolution" should "notice renaming after new state" in {
    val res = h1.resolve("x", Some("t2"))
    res shouldBe Variable("x", Some(1))
  }

  it should "use current variable for current time even after rename" in {
    h1.resolve("x", None) shouldBe Variable("x")
  }
  it should "work for current-time when combining renames and subs" in {
    h2.resolve("x", None) shouldBe "x*2".asTerm
    //h2.eval("x>=2*preassign(x)&(preassign(y)>0->preassign(x)>y)".asFormula) shouldBe "2*x>=2*x&(y>0->x>y)".asFormula
  }
  it should "work for past-time when combining renames and subs" in {
    h2.resolve("x", Some("preassign")) shouldBe "x".asTerm
  }

  it should "work when multiple variables all get renamed" in {
    h3.resolve("x", Some("init")) shouldBe Variable("x", Some(0))
  }

  "Extended term expansion" should "notice renaming after new state" in {
    Kaisar.expand("t2(x)".asTerm, h1, c1, None) shouldBe Variable("x", Some(1))
    //Kaisar.expand("y>0&x>=t2(x)".asFormula, h, c) shouldBe And(Greater(Variable("y"),Number(0)), GreaterEqual(Variable("x"), Variable("x",Some(1))))
  }

  it should "use current variable for current time even after rename" in {
    Kaisar.expand("x".asTerm, h1, c1, None) shouldBe Variable("x")
  }

  it should "expand functional let" in {
    val c = Context(Map(Variable("assms") -> AntePosition(1)), Map(), Map("E" -> ("t", "t(v^2/2+H)".asTerm)))
    val h = History(List(HCRename(Variable("y"), Variable("y", Some(0))), HCRename(Variable("vy"), Variable("vy", Some(0))), HCTimeStep("init"), HCTimeStep("init")))
    val f = "y>=0&v^2/2+H=E()".asFormula
    val exp = Kaisar.expand(f, h, c, None)
    exp shouldBe "y>=0&v^2/2+H=(v^2/2+H)".asFormula
  }

  it should "expand functional let inside a nominal" in {
    val c = Context(Map(Variable("assms") -> AntePosition(1)), Map(), Map("E" -> ("t", "t(v^2/2+H)".asTerm)))
    val h = History(List(HCRename(Variable("y"), Variable("y", Some(0))), HCRename(Variable("vy"), Variable("vy", Some(0))), HCTimeStep("init"), HCTimeStep("init")))
    val f = "y>=0&E()=init(E())".asFormula
    val exp = Kaisar.expand(f, h, c, None)
    exp shouldBe "y>=0&v^2/2+H=(v^2/2+H)".asFormula
  }

  it should "expand variable across multiple renames" in {
    val exp = Kaisar.expand("v".asTerm, h4, c2, Some("init"))
    exp shouldBe Variable("v", Some(0))
  }

  it should "expand functional let inside nominal even when renaming occurs over multiple variables" in {
    val exp = Kaisar.expand("E() = init(E())".asFormula, h4, c2, None)
    exp shouldBe Equal("v^2/2+y".asTerm, Plus(Divide(Power(Variable("v", Some(0)), Number(2)), Number(2)), Variable("y", Some(0))))
  }

  "Pattern matching" should "match variable dependency pattern" in {
    val pat: Expression = "p(x)".asFormula
    val e: Expression = "x > 2".asExpr
    val dm = Kaisar.doesMatch(pat, e, c1)
    dm shouldBe true
  }

  "Proof with no programs" should "prove" in {
    withZ3(qeTool => {
      val pr: Provable = Provable.startProof(Imply(pq, p))
      val up: UP = UP(List(Left("x".asExpr)), Auto())
      val show: Show = Show(p, up)
      val sp: SP = BRule(RBAssume(Variable("x"), pq), List(show))
      Kaisar.eval(sp, History.empty, Context.empty, pr) shouldBe 'proved
    })
  }
  "Proof with one program that modifies nothing" should "prove" in {
    withZ3(qeTool => {
      val box = "[?p();]p()".asFormula
      val prog = "?p();".asProgram
      val pr: Provable = Provable.startProof(box)
      val sp = BRule(RBAssume(Variable("x"), "p()".asFormula), List(Show("p()".asFormula, UP(List(Left("x".asExpr)), Auto()))))
      Kaisar.eval(sp, History.empty, Context.empty, pr) shouldBe 'proved

    })
  }
  "Proof with one program that modifies a relevant variable" should "prove" in {
    withZ3(qeTool => {
      val box = "[x:=1;]x>0".asFormula
      val prog = "x:=1;".asProgram
      val sp =
        BRule(RBAssign(Assign("x".asVariable, "1".asTerm)),
          List(Show("1>0".asFormula, UP(List(), Auto()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }

  "Proof with one program that modifies a relevant variable and time-traveling that variable" should "prove" in {
    withZ3(qeTool => {
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
    withZ3(qeTool => {
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
    withZ3(qeTool => {
      val box = "[x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=x - 1;".asProgram
      val sp: SP =
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
    withZ3(qeTool => {
      val box = "[x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=x - 1;".asProgram
      // TODO: Add timestep(e) notation and manage different renaming for assign vs. ODE
      val sp: SP =
        BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
          List(Have("xBig".asVariable, "2 > 1".asFormula, Show("2 > 1".asFormula, UP(List(Left("p(x)".asExpr)), Kaisar.RCF())),
            BRule(RBAssign(Assign("x".asVariable, "2 - 1".asTerm)),
              List(Show("2 - 1>0".asFormula, UP(List(), Auto())))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }

  /* Use facts */
  "Proof with two facts" should "prove" in {
    withZ3(qeTool => {
      val box = "[x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=2;".asProgram
      val prog2 = "x:=x - 1;".asProgram
      val sp: SP =
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
    withZ3(qeTool => {
      val box = "[x := 3;][x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=3;".asProgram
      val prog2 = "x:=2;".asProgram
      val prog3 = "x:=x - 1;".asProgram
      val sp: SP =
        BRule(RBAssign(Assign("x".asVariable, "3".asTerm)),
          // TODO: Uniqueness checking for pattern matching should break this
          List(
            BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
              List(Have("xBig".asVariable, "x > 1".asFormula, Show("x > 1".asFormula, UP(List(Left("p(x)".asFormula)), Kaisar.RCF())),
                Have("xNonZero".asVariable, "x != 0".asFormula, Show("x != 0".asFormula, UP(List(Left("p(x)".asFormula)), Kaisar.RCF())),
                  BRule(RBAssign(Assign("x".asVariable, "2 - 1".asTerm)),
                    List(Show("x>0".asFormula, UP(List(), Auto()))))))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with two facts further in future with time travel" should "prove" in {
    withZ3(qeTool => {
      val box = "[x := 3;][x:=2;][x:= x - 1;]x>0".asFormula
      val prog1 = "x:=3;".asProgram
      val prog2 = "x:=2;".asProgram
      val prog3 = "x:=x - 1;".asProgram
      val sp: SP =
        BRule(RBAssign(Assign("x".asVariable, "3".asTerm)),
          // TODO: Uniqueness checking for pattern matching should break this
          List(
            PrintGoal("After first assign",
              BRule(RBAssign(Assign("x".asVariable, "2".asTerm)),
                List(
                  PrintGoal("After second assign",
                    Have("xBig".asVariable, "x > 1".asFormula, Show("x > 1".asFormula, UP(List(Left("p(x)".asFormula)), Kaisar.RCF())),
                      Have("xNonZero".asVariable, "x != 0".asFormula, Show("x != 0".asFormula, UP(List(Left("p(x)".asFormula)), Kaisar.RCF())),
                        PrintGoal("After third assign",
                          BRule(RBAssign(Assign("x".asVariable, "x - 1".asTerm)),
                            List(Show("2-1>0".asFormula, UP(List(), Auto())))))))))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with loop with one invariant, no constant formulas" should "prove" in {
    withZ3(qeTool => {
      val box = "x = 0 -> [{x:=x+1;}*]x>=0".asFormula
      val sp: SP =
        BRule(RBAssume("x".asVariable, "x = 0".asFormula),
          List(BRule(RBInv(
            Inv("J".asVariable, "x >= 0".asFormula, Show("x >= 0".asFormula, UP(List(), Auto())),
              BRule(RBAssign(Assign("x".asVariable, "x+1".asTerm)), List(Show("x >= 0".asFormula, UP(List(), Auto())))),
              Finally(Show("x>= 0".asFormula, UP(List(), Auto()))))),
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
            Inv("J1".asVariable, "x >= 0".asFormula, pre = Show("x >= 0".asFormula, UP(List(), Auto())),
              inv = BRule(RBAssign(Assign("y".asVariable, "y+x".asTerm)),
                List(BRule(RBAssign(Assign("x".asVariable, "x+1".asTerm)),
                  List(Show("x >= 0".asFormula, UP(List(), Auto())))))),
              tail =
                Inv("J2".asVariable, fml = "y >= 1".asFormula, pre = Show("y >= 1".asFormula, UP(List(), Auto())),
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
            Inv("J".asVariable, "x >= 0".asFormula, pre = Show("x >= 0".asFormula, UP(List(), Auto())),
              inv = BRule(RBAssign(Assign("x".asVariable, "x+y".asTerm)),
                List(Show("x >= 0".asFormula, UP(List(), Auto())))),
              tail = Finally(Show("x>= 0".asFormula, UP(List(), Auto()))))), tails = List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof of easy differential invariant" should "prove" in {
    withZ3(qeTool => {
      val box = "x = 0 & y = 1 -> [{x' = -y, y' = x}]x^2 + y^2 > 0".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x = 0 & y = 1".asFormula),
          List(BRule(RBInv(
            Inv("J".asVariable, "x^2 + y^2 = 1".asFormula, pre = Show("x^2 + y^2 = 1".asFormula, UP(List(), Auto())),
              inv = Show("(x^2 + y^2 = 1)'".asFormula, UP(List(), Auto())),
              tail = Finally(Show("x^2 + y^2 > 0".asFormula, UP(List(), Auto()))))
          ), List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "Proof with double differential invariant" should "prove" in {
    withZ3(qeTool => {
      val box = "x = 0 & y = 1 & dx = -1 & dy = 0 -> [{x' = dx*v, y'=dy*v, dx' = -dy*v, dy'=dx*v, v'=a}]x^2 + y^2 = 1".asFormula
      val sp: SP =
        BRule(RBAssume("assms".asVariable, "x = 0 & y = 1 & dx = -1 & dy = 0".asFormula),
          List(BRule(RBInv(
            Inv("J1".asVariable, "dx=-y&dy=x".asFormula, Show("dx=-y&dy=x".asFormula, UP(List(), Auto())),
              inv = Show("(x^2 + y^2 = 1)'".asFormula, UP(List(), Auto())),
              tail =
                Inv("J2".asVariable, "x^2 + y^2 = 1".asFormula, Show("x^2 + y^2 = 1".asFormula, UP(List(), Auto())),
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
      val sp: SP =
        BRule(RBAssume("x".asVariable, "x > 0".asFormula),
          List(BRule(RBInv(
            Ghost("y".asVariable, "(1/2)*y + 0".asTerm, "x*y^2 = 1".asFormula, "(1/x)^(1/2)".asTerm, Show("x*y^2 = 1".asFormula, UP(List(), Auto())), Show("x*y^2=1".asFormula, UP(List(), Auto())),
              Inv("J".asVariable, "x*y^2=1".asFormula, Show("x*y^2=1".asFormula, UP(List(), Auto())), Show("x*y^2=1".asFormula, UP(List(), Auto())),
                Finally(Show("x > 0".asFormula, UP(List(), Auto())))))
          ), List())))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }

  def shouldThrow[T](f: (Unit => T)): Unit = {
    try {
      val x: T = f()
    } catch {
      case _ => return
    }
    false shouldBe true
  }

  "Let bindings" should "not throw out the existing context" in {
    withZ3(qeTool => {
      val box = "x = 0 & y = 0 -> x + y = 0".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x = 0 & y = 0".asFormula),
          List(
            SLet("xD_".asVariable, "x".asTerm,
              SLet("yD_".asVariable, "y".asTerm,
                Show("xD_ + xD_ = 0".asFormula,
                  UP(List(), Auto())
                )
              )
            )
          ))
      shouldThrow { case () => Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) }
    })
  }

  "DaLi'17 Example 1a" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x > 1 & y = 0".asFormula),
          List(Show("(x-1)^2 != (x+1)^2".asFormula, UP(Nil, Kaisar.RCF()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "DaLi'17 Example 1b" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x_() & y_()".asFormula), List(
          Show("wild()".asFormula, UP(Nil, Kaisar.RCF()))
        ))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "DaLi'17 Example 1c" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x_() & y_()".asFormula), List(
          Have("x".asVariable, "x != 0".asFormula, Show("x != 0".asFormula, UP(List(Left("xy".asVariable)), Kaisar.RCF())),
            Show("wild()".asFormula, UP(Nil, Kaisar.RCF())))
        ))
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
  */ "DaLi'17 Example 1d" should "prove" in {
    withZ3(qeTool => {
      val box =
        "(x + y + z > 1 & huge = 0 -> (x + y + z -1)^2 != (x + y + z + 1)^2)".asFormula
      val sp: SP =
        SLet("w_()".asTerm, "x + y + z".asTerm,
          BRule(RBAssume("xy".asVariable, "w_() > 1 & wild()".asFormula), List(
            Note("w".asVariable, FMP(FPat("andE1()".asFormula), FPat("xy".asVariable)),
              Show("wild()".asFormula, UP(List(Left("w()".asFormula)), Kaisar.RCF()))
            )
          )))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }

  /*
   * x=2 * y-> [{{?(x<-2);x:=x^2}++ {?(x >= 0 & y >= 0);y:=1/3*y}}x:=x*2;]x > 2* y
      * # Example 2a
    assume xy:(x=2*y)
    case (?(x<-2); _)
      assume x:(x<-2)
      assign x:=x^2
      show(x > 2*y)
      by auto
      //TODO: Add pattern-matches to case construct
      //TODO: Fix this pattern in paper
    case (y := _)
      assign (y:=(1/3)*y)
      assign x:=x^2
      show (x > 2*y)
      by auto
      */
  "DaLi'17 Example 2a" should "prove" in {
    withZ3(qeTool => {
      val box = "x=2*y -> [{{?(x< -2);x:=x^2;} ++ {?(x >= 0 & y > 0);y:=1/3*y;}}x:=x*2;]x > 2*y".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x=2*y".asFormula), List(
          BRule(RBCase(List("{wild}".asProgram, "{wild}".asProgram)), List(
            BRule(RBAssume("x".asVariable, "x< -2".asFormula), List(
              BRule(RBAssign(Assign("x".asVariable, "x^2".asTerm)), List(
                BRule(RBAssign(Assign("x".asVariable, "(x*2)".asTerm)), List(
                  Show("x > 2*y".asFormula, UP(List(), Auto()))
                )))))),
            BRule(RBAssume("xy".asVariable, "x >= 0 & y > 0".asFormula), List(
              BRule(RBAssign(Assign("y".asVariable, "(1/3)*y".asTerm)), List(
                BRule(RBAssign(Assign("x".asVariable, "(x*2)".asTerm)), List(
                  Show("x > 2*y".asFormula, UP(List(), Auto()))
                ))
              )
              )
            ))
          ))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  /*# Example 2b
assume xy:(x=2*y)
mid J:(x>y)
  show ([_]x>y) by auto
assign x:=x*2
show (x > 2y) using J by auto
*/
  //TODO: Add variables in con rule, also rename con rule
  "DaLi'17 Example 2b" should "prove" in {
    withZ3(qeTool => {
      val box = "x=2*y -> [{{?(x< -2);x:=x^2;} ++ {?(x >= 0 & y > 0);y:=1/3*y;}}x:=x*2;]x > 2*y".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x=2*y".asFormula), List(
          BRule(RBConsequence("J".asVariable, "x>y".asFormula), List(
            Show("[{wild}]x>y".asFormula, UP(List(), Auto()))
            , BRule(RBAssign(Assign("x".asVariable, "x*2".asTerm)), List(
              Show("x>2*y".asFormula, UP(List(), Auto()))))
          ))
        ))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  /*# Example 2c
  assume xy:(x=2*y)
  mid J:(x>y)
    show ([_]x>y) by auto
  state pre-assign
  assign x:=x*2
  //TODO: Fix this in the paper, see test case
  have xs:(x >= 2*pre-assign(x) & pre-assign(x) > y)
    by auto
  show _ using J by auto
  */
  "DaLi'17 Example 2c" should "prove" in {
    withZ3(qeTool => {
      val box = "x=2*y -> [{{?(x< -2);x:=x^2;} ++ {?(x >= 0 & y > 0);y:=1/3*y;}}x:=x*2;]x > 2*y".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x=2*y".asFormula), List(
          BRule(RBConsequence("J".asVariable, "x>y".asFormula), List(
            Show("[{wild}]x>y".asFormula, UP(Nil, Auto())),
            State("preassign",
              BRule(RBAssign(Assign("x".asVariable, "x*2".asTerm)), List(
                Have("xs".asVariable, "x >= 2*preassign(x) & (preassign(y) > 0 -> preassign(x) > y)".asFormula, Show("wild()".asFormula, UP(Nil, Auto())),
                  Show("wild()".asFormula, UP(List(Left("J".asVariable)), Auto())))
              )))
          ))
        ))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  // x=0&y=1->[{{y:= (1/2)*y}*};{{x:=x+y;y:=(1/2)*y}*};{{x:=x+y}*}]x >= 0

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

  "DaLi'17 Example 3 Second Inv Sub-test" should "prove" in {
    withZ3(qeTool => {

      val seq = Sequent(immutable.IndexedSeq[Formula](And("x=0".asFormula, Equal(Variable("y", Some(0)), Number(1))), "y>0".asFormula), immutable.IndexedSeq("[{x:=x+y;y:=1/2*y;}*](y>0 & x>=0)".asFormula))
      val g = Context(Map(Variable("xy") -> AntePosition(1), Variable("J1") -> AntePosition(2)), Map(), Map())
      val h = History(List(HCTimeStep("t1"), HCRename(Variable("y"), Variable("y", Some(0)), None), HCTimeStep("init")))
      val duh: SP = Show("wild()".asFormula, UP(List(), Kaisar.Auto()))
      val sp: SP =
        BRule(
          RBInv(Inv("J2".asVariable, "y>0 & x>=init(x)".asFormula, duh, duh,
            Finally(
              duh))), List())

      //History:History(List(HCTimeStep(t1), HCRename(y,y_0,None), HCTimeStep(init), HCTimeStep(init)))
      Kaisar.eval(sp, h, g, Provable.startProof(seq)) shouldBe 'proved

    })
    /*====== About to second inv ======
      Goal:Provable(==> 1:  x=0&y=1->[{y:=1/2*y;}*{x:=x+y;y:=1/2*y;}*{x:=x+y;}*]x>=0	Imply
      from      -1:  y>0	Greater
      -2:  x=0	Equal
      -3:  y_0=1	Equal
      ==> 1:  [{x:=x+y;y:=1/2*y;}*{x:=x+y;}*]x>=0	Box)

    Context:Context(Map(xy -> -1, J1 -> -4),Map())

    History:History(List(HCTimeStep(t1), HCRename(y,y_0,None), HCTimeStep(init), HCTimeStep(init)))
    (Right now: ,Provable(==> 1:  x=0&y=1->[{y:=1/2*y;}*{x:=x+y;y:=1/2*y;}*{x:=x+y;}*]x>=0	Imply
      from      -1:  y>0	Greater
      -2:  x=0	Equal
      -3:  y_0=1	Equal
      ==> 1:  [{x:=x+y;y:=1/2*y;}*][{x:=x+y;}*]x>=0	Box))

      x=0&y_0=1, y>0  ==>  y>0&x>=x proved)

      Proves
      x=0&y_1=1, y>0  ==>  y>0&x>=x))
*/
  }
  "DaLi'17 Example 3" should "prove" in {
    withMathematica(qeTool => {
      val box = "x=0&y=1->[{{y:= (1/2)*y;}*};{{x:=x+y;y:=(1/2)*y;}*};{{x:=x+y;}*}]x >= 0".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x=0&y=1".asFormula), List(
          State("init",
            PrintGoal("About to first inv",
              BRule(
                RBInv(Inv("J1".asVariable, "y > 0".asFormula, duh, duh,
                  Finally(
                    State("t1",
                      PrintGoal("About to second inv",
                        BRule(
                          RBInv(Inv("J2".asVariable, "y>0 & x>=init(x)".asFormula, duh, duh,
                            Finally(
                              State("t2",
                                PrintGoal("About to third inv",
                                  BRule(
                                    RBInv(Inv("J3".asVariable, "y>0 & x>=t2(x)".asFormula, duh, duh,
                                      Finally(
                                        PrintGoal("About to show final goal",
                                          Show("x >= 0".asFormula, UP(List(), Kaisar.RCF())))))),
                                    List())))))), List())))))), List())))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  /*  g>0&y>=H&H>0&vy=0 ->
[{{{?(y>0 | vy >= 0)}  ++  {?(y<=0 & vy < 0); vy := -vy}}
     {y'=vy,vy'=-g & y >= 0}
  }*](0 <= y & y <= H)
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
  "DaLi'17 Example 4" should "prove" in {
    withMathematica(qeTool => {
      // TODO: End unit gravity
      val box: Formula = "0 <= y & y<=H&H>0&v=0 -> [{{{?(y>0 | v >= 0);} ++ {?(y<=0 & v < 0); v := -v;}}{y'=v,v'=-1 & y >= 0}}*](0 <= y & y <= H)".asFormula
      val sp: SP =
        BRule(
          //TODO this pattern match might be broke, i.e. patmatch didnt fail even when I changed some stuff
          RBAssume("assms".asVariable, "0 <= y & y<=H&H>0&v=0".asFormula),
          List(
            State("init",
              FLet("E", "t", "t(v^2/2 + y)".asExpr,
                BRule(RBInv(
                  Inv("J".asVariable, "y >= 0 & E() = init(E())".asFormula, duh,
                    State("loopinit",
                      BRule(
                        RBConsequence("conserv".asVariable, "E() = loopinit(E())& 1111 = 1111 & E() = init(E())".asFormula), List(
                          Show("[{wild ++ wild}]wild()".asFormula, UP(List(), Auto()))
                          , PrintGoal("Pre-solve",
                            BRule(
                              RBSolve("t".asVariable, "t >= 0".asFormula, "dc".asVariable, "dc_()".asFormula, List())
                              , List(
                                PrintGoal("Almost done", duh)))))))
                    , Finally(
                      PrintGoal("Finish himm!!!!",
                        //
                        Show("wild()".asFormula, UP(List(Left("J".asVariable), Left("assms".asVariable)), Auto())))))), List())))))
        Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  // x>0&y>0 -> [{x'=-x,y'=x}]y>0

  /* assume assms:(x>0 & y>0)
time init
Ghost z'=x/2, z = (1/x)^(1/2)
Inv JG:(x*z^2 = 1)
Inv Jx:(x > 0)
Inv Jy:(y > init(y))
show (Jy > 0) using assms Jy by auto
*/
  "DaLi'17 Example 5" should "prove" in {
    withMathematica(qeTool => {
      val duh: SP = Show("wild()".asFormula, UP(List(), Kaisar.Auto()))

      val box = "x>0&y>0 -> [{x' =-x, y'=x}]y>0".asFormula
      val sp: SP =
        BRule(RBAssume("assms".asVariable, "x>0&y>0".asFormula), List(
          State("init", BRule(RBInv(
            //
            Ghost("z".asVariable, "(1/2)*z + 0".asTerm, "true".asFormula, "(1/x)^(1/2)".asTerm, duh, duh,
              Inv("JG".asVariable, "x*z^2 = 1".asFormula, duh, duh,
                Inv("Jx".asVariable, "x>0".asFormula, duh, duh,
                  Inv("Jy".asVariable, "y >= init(y)".asFormula, duh, duh,
                    // TODO: Fix context management
                    Finally(Show("y > 0".asFormula, UP(List(Left("assms".asVariable), Left("Jy".asVariable)), Auto())))
                  )


                ))
            )
          ), List()))

        ))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  /*  # Example 1a
  assume v:"v >= v0-g*t"
  assume gt:"v0-g*t >= v0-g*T"
  assume gT:"v0-g*T > (g/rp)^(1/2)"
  show "v>(g/rp)^(1/2)"
  by R
*/
  "POPL'18 1a" should "prove" in {
    withMathematica(qeTool => {
      val box = "(m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0) -> (rp > 0 & g > 0) -> (v >= vn-g*t) -> (vn-g*t >= vn-g*T) -> (vn-g*T > -(g/rp)^(1/2)) -> (v > -(g/rp)^(1/2))".asFormula
      val sp: SP =
        BRule(RBAssume("nonsens".asVariable, "m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0".asFormula), List(
          BRule(RBAssume("nz".asVariable, "rp > 0 & g > 0".asFormula), List(
            BRule(RBAssume("v".asVariable, "v >= vn-g*t".asFormula), List(
              BRule(RBAssume("gt".asVariable, "vn-g*t >= vn-g*T".asFormula), List(
                BRule(RBAssume("gT".asVariable, "vn-g*T > -(g/rp)^(1/2)".asFormula), List(
                  Show("v>-(g/rp)^(1/2)".asFormula, UP(List(), Kaisar.RCF()))
                ))
              ))
            ))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }
  /*
  # Example 1b
  assume v:"v >= ?vt"
  assume gt:"?vt >= ?vT"
  assume gT:"?vT > ?vBound"
  show "v > ?vBound"
  by R*/
  "POPL'18 1b" should "prove" in {
    withMathematica(qeTool => {
      val box = "(m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0) -> (rp > 0 & g > 0) -> (v >= vn-g*t) -> (vn-g*t >= vn-g*T) -> (vn-g*T > -(g/rp)^(1/2)) -> (v > -(g/rp)^(1/2))".asFormula
      val sp: SP =
        BRule(RBAssume("nonsens".asVariable, "m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0".asFormula), List(
          BRule(RBAssume("nz".asVariable, "rp > 0 & g > 0".asFormula), List(
            BRule(RBAssume("v".asVariable, "v >= vt_".asFormula), List(
              BRule(RBAssume("gt".asVariable, "vt_ >= vT_".asFormula), List(
                BRule(RBAssume("gT".asVariable, "vT_ > vBound_".asFormula), List(
                  Show("v > vBound_".asFormula, UP(List(), Kaisar.RCF()))
                ))
              ))
            ))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }
  /*
     # Example 1c
     assume v:"v >= ?vt"
     assume gt:"?vt >= ?vT"
     assume gT:"?vT > ?vBound"
     have trans:"\forall w x y z. w>=x
     -> x>=y -> y>z -> w>z"
     by R
       note res =
       trans v ?vt ?vT ?vBound v gt gT
     show "v > ?vBound"
     using res by id
     */
  "POPL'18 1c" should "prove" in {
    withMathematica(qeTool => {
      val box = "(m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0) -> (rp > 0 & g > 0) -> (v >= vn-g*t) -> (vn-g*t >= vn-g*T) -> (vn-g*T > -(g/rp)^(1/2)) -> (v > -(g/rp)^(1/2))".asFormula
      val sp: SP =
        BRule(RBAssume("nonsens".asVariable, "m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0".asFormula), List(
          BRule(RBAssume("nz".asVariable, "rp > 0 & g > 0".asFormula), List(
            BRule(RBAssume("v".asVariable, "v >= vt_".asFormula), List(
              BRule(RBAssume("gt".asVariable, "vt_ >= vT_".asFormula), List(
                BRule(RBAssume("gT".asVariable, "vT_ > vBound_".asFormula), List(
                  Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula,
                    Show("\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, UP(List(), Kaisar.RCF())),
                    Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "vn-g*t".asTerm), "vn-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("v".asExpr)), FPat("gt".asExpr)), FPat("gT".asExpr)),
                      Show("v > vBound_".asFormula, UP(List(Left("res".asVariable)), CloseId())))
                  )))))))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }
  "POPL'18 1cAlt" should "prove" in {
    withMathematica(qeTool => {
      val box = "(m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0) -> (rp > 0 & g > 0) -> (v >= vn-g*t) -> (vn-g*t >= vn-g*T) -> (vn-g*T > -(g/rp)^(1/2)) -> (v > -(g/rp)^(1/2))".asFormula
      val sp: SP =
        BRule(RBAssume("nonsens".asVariable, "m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0".asFormula), List(
          BRule(RBAssume("nz".asVariable, "rp > 0 & g > 0".asFormula), List(
            BRule(RBAssume("v".asVariable, "v >= vn-g*t".asFormula), List(
              BRule(RBAssume("gt".asVariable, "vn-g*t >= vn-g*T".asFormula), List(
                BRule(RBAssume("gT".asVariable, "vn-g*T > -(g/rp)^(1/2)".asFormula), List(
                  //Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula,
                  //             Show("\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, UP(List(),Kaisar.RCF())),
                  //      Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable),"v".asTerm),"vn-g*t".asTerm),"vn-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("v".asExpr)), FPat("gt".asExpr)), FPat("gT".asExpr)),
                  Show("v>-(g/rp)^(1/2)".asFormula, UP(List(Left("nz".asVariable), Left("gT".asVariable), Left("v".asVariable), Left("gt".asVariable)), Kaisar.RCF()))
                ))))))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  /*
    # Example 1d
    assume v:"v >= ?vt"
    assume gt:"?vt >= ?vT"
    assume gT:"?vT > ?vBound"
    have trans:"\forall w x y z. w>=x
    -> x>=y -> y>z -> w>z"
    by R
      note res =
      trans v ?vt ?vT ?vBound v gt gT
    let ?goal = (v > ?vBound)
    show (?goal)
    using res by id*/
  "POPL'18 1d" should "prove" in {
    withMathematica(qeTool => {
      val box = "(m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0) -> (rp > 0 & g > 0) -> (v >= vn-g*t) -> (vn-g*t >= vn-g*T) -> (vn-g*T > -(g/rp)^(1/2)) -> (v > -(g/rp)^(1/2))".asFormula
      val sp: SP =
        BRule(RBAssume("nonsens".asVariable, "m<=0 & pr > ar & pr > 0 & ar > 0 & m < -(g/pr)^(1/2) & T>0 & vn>(g/pr)^(1/2) & vn < 0 & t <= T & x >= 0 & v < 0".asFormula), List(
        BRule(RBAssume("nz".asVariable, "rp > 0 & g > 0".asFormula), List(
        BRule(RBAssume("v".asVariable, "v >= vt_".asFormula), List(
        BRule(RBAssume("gt".asVariable, "vt_ >= vT_".asFormula), List(
        BRule(RBAssume("gT".asVariable, "vT_ > vBound_".asFormula), List(
        Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula,
        Show("\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, UP(List(), Kaisar.RCF())),
        Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "vn-g*t".asTerm), "vn-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("v".asExpr)), FPat("gt".asExpr)), FPat("gT".asExpr)),
        SLet("goal_()".asFormula, "v > vBound_".asFormula,
        Show("goal_()".asFormula, UP(List(Left("res".asVariable)), CloseId())))
                    ))))))))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  private val dc = "x>= 0 & v < 0".asFormula
  private val const = "g > 0 & 0 < ra &  ra < rp & T >= 0".asFormula
  private val dyn = "m < -(g/rp)^(1/2) & -(g/rp)^(1/2) < v ".asFormula
  private val dynInv = "-(g/rp)^(1/2) < v".asFormula
  private val pre = And("r=ra".asFormula, And(And(dc, const), dyn))
  private val ctrl = "{{?(r=ra & v-g*T > -(g/rp)^(1/2));} ++ {r:=rp;}}".asProgram
  private val plant = "t:=0;{x'=v,v'=r*v^2-g, t'=1 & x>=0 & v<0 & t<=T}".asProgram
  private val post = "x=0 -> v>=m".asFormula
  private val safePara = Imply(pre, Box(Loop(Compose(ctrl, plant)), post))
  //private val lowPre = And("x <= xmax".asFormula, pre)
  private val lowPost = "x <= xmax".asFormula
  private val lowPara = Imply("x <= xmax".asFormula, Imply(pre, Box(Loop(Compose(ctrl, plant)), lowPost)))
  //  & v >= init(v)

  "POPL'18 3a" should "prove" in {
    withMathematica(qeTool => {
      val time = System.currentTimeMillis()
      val sp:SP =
        State("init",
        BRule(RBAssume("assms".asVariable,"r=ra & ((dc_() & const_()) & dyn_())".asFormula), List(
        BRule(RBInv(
        Inv("J".asVariable, And(And(dc, const), dyn), duh,
          State("loop",
          BRule(RBCase(List("dc_() & const_()".asFormula, "dyn_()".asFormula)), List(
            BRule(RBCase(List("?(wild());".asProgram, "{wild}".asProgram)), List(
              BRule(RBAssume("slowEnough".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula),  List(
                Show("wild()".asFormula, UP(List(), Kaisar.Auto()))))
             ,BRule(RBAssign(Assign("r".asVariable,"rp".asVariable)), List(
                Show("wild()".asFormula, UP(List(), Kaisar.Auto()))))))
          , BRule(RBCase(List("?(wild());".asProgram, "{wild}".asProgram)), List(
            BRule(RBAssume("slowEnough".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula),  List(
            BRule(RBAssign(Assign("t".asVariable,"0".asTerm)), List(
            BRule(RBInv(
            Inv("rp".asVariable, "g>0 & rp>0".asFormula, duh, duh,
            Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
            Inv("vInitBig".asVariable, "loop(v)-g*T > -(g/rp)^(1/2)".asFormula, duh, duh,
            Inv("dc".asVariable, "t <= T".asFormula, duh, duh,
            Finally(
              Have("tBound".asVariable, "loop(v) -g*t >= loop(v) - g*T".asFormula, Show("wild()".asFormula,
                  UP(List(Left("rp".asVariable), Left("dc".asVariable)), Kaisar.RCF())),
              Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, duh,
              Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "loop(v)-g*t".asTerm), "loop(v)-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("vBig".asExpr)), FPat("tBound".asExpr)), FPat("vInitBig".asExpr)),
              PrintGoal("Almost done goal one ",
              Show("wild()".asFormula, UP(List(Left("res".asVariable),Left("vBig".asVariable), Left("J".asVariable)), Auto())))))))))))),List())))))

          ,BRule(RBAssign(Assign("r".asVariable,"rp".asVariable)), List(
            BRule(RBAssign(Assign("t".asVariable,"0".asTerm)), List(
            BRule(RBInv(
            Inv("consts".asVariable, "rp>0 & g>0".asFormula, duh, duh,
            Ghost("y".asVariable,"-1/2*rp*(v-(g/rp)^(1/2))*y".asTerm,True,"(v+(g/rp)^(1/2))^(-1/2)".asTerm, duh, duh,
            Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
            Inv("ghostInv".asVariable, "(y^2*(v+(g/rp)^(1/2))=1)".asFormula, duh, duh,
            Finally(
            Show("wild()".asFormula, UP(List(Left("ghostInv".asVariable),Left("vBig".asVariable), Left("J".asVariable)), Kaisar.RCF())))))))),List())))))))))),
        Finally(
          PrintGoal("About to conclude",
            //TODO: Badness
            Show(post, UP(List(Left("assms".asVariable), Left("J".asVariable)), Auto())))))),List()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(safePara)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  "POPL'18 3b" should "prove" in {
    withMathematica(qeTool => {
      val time = System.currentTimeMillis()
      val sp:SP =
        State("init",
          BRule(RBAssume("assms".asVariable,"r=ra & ((dc_() & const_()) & dyn_())".asFormula), List(
          BRule(RBInv(
          Inv("J".asVariable, And(And(dc, const), dyn), duh,
          State("loop",
          BRule(RBCase(List("dc_() & const_()".asFormula, "dyn_()".asFormula)), List(
          BRule(RBConsequence("I".asVariable, True), List(
            Show("wild()".asFormula, UP(List(), Kaisar.Auto()))
            ,Show("wild()".asFormula, UP(List(), Kaisar.Auto()))
          ))
        , BRule(RBCase(List("?(wild());".asProgram, "{wild}".asProgram)), List(
                BRule(RBAssume("slowEnough".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula),  List(
                  BRule(RBAssign(Assign("t".asVariable,"0".asTerm)), List(
                  BRule(RBInv(
                  Inv("rp".asVariable, "g>0 & rp>0".asFormula, duh, duh,
                  Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                  Inv("vInitBig".asVariable, "loop(v)-g*T > -(g/rp)^(1/2)".asFormula, duh, duh,
                  Inv("dc".asVariable, "t <= T".asFormula, duh, duh,
                  Finally(
                  Have("tBound".asVariable, "loop(v) -g*t >= loop(v) - g*T".asFormula, Show("wild()".asFormula,
                  UP(List(Left("rp".asVariable), Left("dc".asVariable)), Kaisar.RCF())),
                Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, duh,
                Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "loop(v)-g*t".asTerm), "loop(v)-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("vBig".asExpr)), FPat("tBound".asExpr)), FPat("vInitBig".asExpr)),
                PrintGoal("Almost done goal one ",
                Show("wild()".asFormula, UP(List(Left("res".asVariable),Left("vBig".asVariable), Left("J".asVariable)), Auto())))))))))))),List())))))
                  ,BRule(RBAssign(Assign("r".asVariable,"rp".asVariable)), List(
                  BRule(RBAssign(Assign("t".asVariable,"0".asTerm)), List(
                  BRule(RBInv(
                  Inv("consts".asVariable, "rp>0 & g>0".asFormula, duh, duh,
                  Ghost("y".asVariable,"-1/2*rp*(v-(g/rp)^(1/2))*y".asTerm,True,"(v+(g/rp)^(1/2))^(-1/2)".asTerm, duh, duh,
                  Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                  Inv("ghostInv".asVariable, "(y^2*(v+(g/rp)^(1/2))=1)".asFormula, duh, duh,
                  Finally(
                  Show("wild()".asFormula, UP(List(Left("ghostInv".asVariable),Left("vBig".asVariable), Left("J".asVariable)), Kaisar.RCF())))))))),List())))))))))),
                Finally(
                  PrintGoal("About to conclude",
                    //TODO: Badness
                    Show(post, UP(List(Left("assms".asVariable), Left("J".asVariable)), Auto())))))),List()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(safePara)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }


  "POPL'18 3c" should "prove" in {
    withMathematica(qeTool => {
      val time = System.currentTimeMillis()
      val sp:SP =
      //  PrintGoal("blah",
        State("init",
        BRule(RBAssume("assms".asVariable,pre), List(
        BRule(RBInv(Inv("DCCONST".asVariable, And(dc,const), duh, duh,
        Inv("DYN".asVariable, dynInv, duh,
          // TODO: Add pattern matching
            State("loop",
            BRule(RBCase(List("{wild}".asProgram,"{wild}".asProgram)), List(
            BRule(RBAssume("safe".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula),  List(
            BRule(RBAssign(Assign("t".asVariable,"0".asTerm)), List(
            BRule(RBInv(
              Inv("rp".asVariable, "g>0 & rp>0".asFormula, duh, duh,
              Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
              Inv("vInitBig".asVariable, "loop(v)-g*T > -(g/rp)^(1/2)".asFormula, duh, duh,
              Inv("dc".asVariable, "t <= T".asFormula, duh, duh,
                  Finally(
                Have("tBound".asVariable, "loop(v) -g*t >= loop(v) - g*T".asFormula, Show("wild()".asFormula,
                  //TODO: Should be const not vBig but stuff messed up
                  //UP(List(Left("vBig".asVariable), Left("dc".asVariable)), Kaisar.RCF())
                    UP(List(Left("rp".asVariable), Left("dc".asVariable)), Kaisar.RCF())
                ),
                Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, duh,
                Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "loop(v)-g*t".asTerm), "loop(v)-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("vBig".asExpr)), FPat("tBound".asExpr)), FPat("vInitBig".asExpr)),
                //TODO: Show needs some more stuff about v>=v0 and m < equilib
                  PrintGoal("Almost done goal one ",
                  Show("wild()".asFormula, UP(List(Left("res".asVariable),Left("vBig".asVariable), Left("DYN".asVariable), Left("DCCONST".asVariable)), Auto())))))))))))
            ),List())))
            ))
            ,
            //PrintGoal("Second branch",
            BRule(RBAssign(Assign("r".asVariable,"rp".asVariable)), List(
            BRule(RBAssign(Assign("t".asVariable,"0".asTerm)), List(
            BRule(RBInv(
            Inv("consts".asVariable, "rp>0 & g>0".asFormula, duh, duh,
            Ghost("y".asVariable,"-1/2*rp*(v-(g/rp)^(1/2))*y".asTerm,True,"(v+(g/rp)^(1/2))^(-1/2)".asTerm, duh, duh,
            Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
            Inv("ghostInv".asVariable, "(y^2*(v+(g/rp)^(1/2))=1)".asFormula, duh, duh,
            Finally(
              Show("wild()".asFormula, UP(List(Left("ghostInv".asVariable),Left("vBig".asVariable), Left("DYN".asVariable), Left("DCCONST".asVariable)), Kaisar.RCF())))))))),List())))))))),
        Finally(
          PrintGoal("About to conclude",
            //TODO: Badness
            Show(post, UP(List(Left("assms".asVariable), Left("DCCONST".asVariable), Left("DYN".asVariable)), Auto()))))))), List()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(safePara)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  "POPL'18 3d" should "prove" in {
    withMathematica(qeTool => {
      val time = System.currentTimeMillis()
      val sp:SP =
      //  PrintGoal("blah",
      State("init",
      BRule(RBAssume("niceAssume".asVariable,"x<=xmax".asFormula), List(
      BRule(RBAssume("assms".asVariable,pre), List(
      BRule(RBInv(Inv("DCCONST".asVariable, And(dc,const), duh, duh,
      Inv("DYN".asVariable, dynInv, duh,
        // TODO: Add pattern matching
      State("loop",
      BRule(RBCase(List("{wild}".asProgram,"{wild}".asProgram)), List(
      BRule(RBAssume("safe".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula),  List(
      BRule(RBAssign(Assign("t".asVariable,"0".asTerm)), List(
      BRule(RBInv(
      Inv("rp".asVariable, "g>0 & rp>0".asFormula, duh, duh,
      Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
      Inv("vInitBig".asVariable, "loop(v)-g*T > -(g/rp)^(1/2)".asFormula, duh, duh,
      Inv("dc".asVariable, "t <= T".asFormula, duh, duh,
      Finally(
      Have("tBound".asVariable, "loop(v) -g*t >= loop(v) - g*T".asFormula, Show("wild()".asFormula,
        UP(List(Left("rp".asVariable), Left("dc".asVariable)), Kaisar.RCF())
      ),Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, duh,
      Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "loop(v)-g*t".asTerm), "loop(v)-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("vBig".asExpr)), FPat("tBound".asExpr)), FPat("vInitBig".asExpr)),
      //PrintGoal("WUST Almost done goal one ",
        Show("wild()".asFormula, UP(List(Left("res".asVariable),Left("vBig".asVariable), Left("DYN".asVariable), Left("DCCONST".asVariable)), Auto()))/*)*/))))))))
            ),List())))
        ))
        ,
        //PrintGoal("WUST Second branch",
        BRule(RBAssign(Assign("r".asVariable,"rp".asVariable)), List(
        BRule(RBAssign(Assign("t".asVariable,"0".asTerm)), List(
        BRule(RBInv(
        Inv("consts".asVariable, "rp>0 & g>0".asFormula, duh, duh,
        Ghost("y".asVariable,"-1/2*rp*(v-(g/rp)^(1/2))*y".asTerm,True,"(v+(g/rp)^(1/2))^(-1/2)".asTerm, duh, duh,
        Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
        Inv("ghostInv".asVariable, "(y^2*(v+(g/rp)^(1/2))=1)".asFormula, duh, duh,
        Finally(
          /*PrintGoal("WUST Almost done goal two ",*/
            Show("wild()".asFormula, UP(List(Left("ghostInv".asVariable),Left("vBig".asVariable), Left("DYN".asVariable), Left("DCCONST".asVariable)), Kaisar.RCF()))/*)*/)))))),List())))))/*)*/))),
      Inv("xdown".asVariable, "x <= init(x)".asFormula, PrintGoal("idown BC ",
        duh), /*PrintGoal("WUST idown IS ",*/duh/*)*/,
      Finally(
      PrintGoal("WUST About to conclude",
        // , Left("DYN".asVariable)
      Show(lowPost, UP(List(Left("niceAssume".asVariable), Left("xdown".asVariable)), Auto())))))))), List()))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(lowPara)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }
  /*#Example 3
assume assms:"r = ar & ?dc & ?const & ?dyn"
state init
inv DCCONST:(?dc & ?const) {}
inv DYN:(?dyn) {
Inv => {
case ?(_) =>
assume (vT>?vBound & r=ar)
Inv pr:(g>0 & pr>0) {}
Inv vBig:(v >= init(v) - g*t) {}
Inv vInitBig:(init(v) - g*T > -(g/pr)^(1/2)) {}
TODO: Nicer handling of dC
finally have tBound:(init(v) - g*t >= init(v) - g*T)
using const by R
have trans:(\forall w x y z (w>=x -> x>=y -> y>z -> w>z)) by R
note res = trans v ?vt ?vT ?vBound v gt gT
show _ using res by id
|r := pr =>
assign r := pr
Inv consts:(pr>0&g>0)
Ghost y=0, y'=(-1/2*pr*(v-(g/pr)^(1/2)))
Inv ghostInv:(y^2*(v+(g/pr)^(1/2))=1)
finally show _ using ghostInv by R
}}} finally show (x=0 -> v > m) using DCCONST DYN by auto
  * */

}