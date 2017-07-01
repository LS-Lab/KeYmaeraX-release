package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.Kaisar.{BRule, _}
import edu.cmu.cs.ls.keymaerax.btactics.{Kaisar, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser

import scala.collection.immutable

import edu.cmu.cs.ls.keymaerax.tags.SlowTest

/**
  * Created by bbohrer on 12/3/16.
  */
@SlowTest
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

  "Variable resolution" should "notice renaming after new state" in {
    val res = h1.resolve("x", Some("t2"))
    res shouldBe Variable("x", Some(1))
  }

  it should "use current variable for current time even after rename" in {
    h1.resolve("x", None) shouldBe Variable("x")
  }
  it should "work for current-time when combining renames and subs" in {
    h2.resolve("x", None) shouldBe "x*2".asTerm
  }
  it should "work for past-time when combining renames and subs" in {
    h2.resolve("x", Some("preassign")) shouldBe "x".asTerm
  }

  it should "work when multiple variables all get renamed" in {
    h3.resolve("x", Some("init")) shouldBe Variable("x", Some(0))
  }

  "Extended term expansion" should "notice renaming after new state" in {
    Kaisar.expand("t2(x)".asTerm, h1, c1, None) shouldBe Variable("x", Some(1))
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
    val dm = Kaisar.doesMatch(pat, e, c1, immutable.IndexedSeq())
    dm shouldBe true
  }

  "Proof with no programs" should "prove" in {
    withZ3(qeTool => {
      val pr: Provable = Provable.startProof(Imply(pq, p))
      val up: UP = UP(List(Left("assm(x)".asExpr)), Auto())
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
      val sp = BRule(RBAssume(Variable("x"), "p()".asFormula), List(Show("p()".asFormula, UP(List(Left("assm(x)".asExpr)), Auto()))))
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

  "POPL'18 Old Draft Example 1a" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x > 1 & y = 0".asFormula),
          List(Show("(x-1)^2 != (x+1)^2".asFormula, UP(Nil, Kaisar.RCF()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "POPL'18 Old Draft Example 1b" should "prove" in {
    withZ3(qeTool => {
      val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x_() & y_()".asFormula), List(
          Show("wild()".asFormula, UP(Nil, Kaisar.RCF()))
        ))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(box)) shouldBe 'proved
    })
  }
  "POPL'18 Old Draft Example 1c" should "prove" in {
    withMathematica(qeTool => {
      val box = "x > 1 & y = 0 -> (x-1)^2 != (x+1)^2".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "xfml_() & yfml_()".asFormula), List(
          Have("x".asVariable, "x != 0".asFormula,
            // TODO: Don't treat x and x_() as equal please
            Show("x != 0".asFormula, UP(List(Left("assm(xy)".asExpr)), Kaisar.RCF())),
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
  */ "POPL'18 Old Draft Example 1d" should "prove" in {
    withZ3(qeTool => {
      val box =
        "(x + y + z > 1 & huge = 0 -> (x + y + z -1)^2 != (x + y + z + 1)^2)".asFormula
      val sp: SP =
        SLet("w_()".asTerm, "x + y + z".asTerm,
          BRule(RBAssume("xy".asVariable, "w_() > 1 & wild()".asFormula), List(
            Note("w".asVariable, FMP(FPat("andE1()".asFormula), FPat("xy".asVariable)),
              Show("wild()".asFormula, UP(List(Left("assm(w)".asFormula)), Kaisar.RCF()))
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
  "POPL'18 Old Draft Example 2a" should "prove" in {
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
  "POPL'18 Old Draft Example 2b" should "prove" in {
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
  "POPL'18 Old Draft Example 2c" should "prove" in {
    withZ3(qeTool => {
      val box = "x=2*y -> [{{?(x< -2);x:=x^2;} ++ {?(x >= 0 & y > 0);y:=1/3*y;}}x:=x*2;]x > 2*y".asFormula
      val sp: SP =
        BRule(RBAssume("xy".asVariable, "x=2*y".asFormula), List(
          BRule(RBConsequence("J".asVariable, "x>y".asFormula), List(
            Show("[{wild}]x>y".asFormula, UP(Nil, Auto())),
            State("preassign",
              BRule(RBAssign(Assign("x".asVariable, "x*2".asTerm)), List(
                Have("xs".asVariable, "x >= 2*preassign(x) & (preassign(y) > 0 -> preassign(x) > y)".asFormula, Show("wild()".asFormula, UP(Nil, Auto())),
                  Show("wild()".asFormula, UP(List(Left("assm(J)".asExpr)), Auto())))
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

  "POPL'18 Old Draft Example 3 Second Inv Sub-test" should "prove" in {
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
  "POPL'18 Old Draft Example 3" should "prove" in {
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
  "POPL'18 Old Draft" should "prove" in {
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
                      PrintGoal("End",
                        Show("wild()".asFormula, UP(List(Left("assm(J)".asExpr), Left("assm(assms)".asExpr)), Auto())))))), List())))))
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
  "POPL'18 Old Draft" should "prove" in {
    withMathematica(qeTool => {
      val duh: SP = Show("wild()".asFormula, UP(List(), Kaisar.Auto()))
      val box = "x>0&y>0 -> [{x' =-x, y'=x}]y>0".asFormula
      val sp: SP =
        BRule(RBAssume("assms".asVariable, "x>0&y>0".asFormula), List(
          State("init", BRule(RBInv(
            Ghost("z".asVariable, "(1/2)*z + 0".asTerm, "true".asFormula, "(1/x)^(1/2)".asTerm, duh, duh,
              Inv("JG".asVariable, "x*z^2 = 1".asFormula, duh, duh,
                Inv("Jx".asVariable, "x>0".asFormula, duh, duh,
                  Inv("Jy".asVariable, "y >= init(y)".asFormula, duh, duh,
                    // TODO: Fix context management
                    Finally(Show("y > 0".asFormula, UP(List(Left("assm(assms)".asFormula), Left("assm(Jy)".asFormula)), Auto())))
                  ))))), List()))))
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
                    Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "vn-g*t".asTerm), "vn-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("assm(v)".asExpr)), FPat("assm(gt)".asExpr)), FPat("assm(gT)".asExpr)),
                      Show("v > vBound_".asFormula, UP(List(Left("assm(res)".asExpr)), CloseId())))
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
                  Show("v>-(g/rp)^(1/2)".asFormula, UP(List(Left("assm(nz)".asExpr), Left("assm(gT)".asExpr), Left("assm(v)".asExpr), Left("assm(gt)".asExpr)), Kaisar.RCF()))
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
                    Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "vn-g*t".asTerm), "vn-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("assm(v)".asExpr)), FPat("assm(gt)".asExpr)), FPat("assm(gT)".asExpr)),
                      SLet("goal_()".asFormula, "v > vBound_".asFormula,
                        Show("goal_()".asFormula, UP(List(Left("assm(res)".asFormula)), CloseId())))
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
  private val lowPost = "x <= xmax".asFormula
  private val lowPara = Imply("x <= xmax".asFormula, Imply(pre, Box(Loop(Compose(ctrl, plant)), lowPost)))


  /* @README Reviewer note:
  * Because the proofs in Example 2 are not complete proofs, only partial proofs, we implement them in Kaisar by
  * proving four versions of Example 3, one for each subexample of Example 2, as opposed to the one version of 3 in the paper.*/
  "POPL'18 3a" should "prove" in {
    withMathematica(qeTool => {
      val time = System.currentTimeMillis()
      val sp: SP =
        State("init",
          BRule(RBAssume("assms".asVariable, "r=ra & ((dc_() & const_()) & dyn_())".asFormula), List(
            BRule(RBInv(
              Inv("J".asVariable, And(And(dc, const), dyn), duh,
                State("loop",
                  BRule(RBCase(List("dc_() & const_()".asFormula, "dyn_()".asFormula)), List(
                    BRule(RBCase(List("?(wild());".asProgram, "{wild}".asProgram)), List(
                      BRule(RBAssume("slowEnough".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula), List(
                        Show("wild()".asFormula, UP(List(), Kaisar.Auto()))))
                      , BRule(RBAssign(Assign("r".asVariable, "rp".asVariable)), List(
                        Show("wild()".asFormula, UP(List(), Kaisar.Auto()))))))
                    , BRule(RBCase(List("?(wild());".asProgram, "{wild}".asProgram)), List(
                      BRule(RBAssume("slowEnough".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula), List(
                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                          BRule(RBInv(
                            Inv("rp".asVariable, "g>0 & rp>0".asFormula, duh, duh,
                              Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                                Inv("vInitBig".asVariable, "loop(v)-g*T > -(g/rp)^(1/2)".asFormula, duh, duh,
                                  Inv("dc".asVariable, "t <= T".asFormula, duh, duh,
                                    Finally(
                                      Have("tBound".asVariable, "loop(v) -g*t >= loop(v) - g*T".asFormula, Show("wild()".asFormula,
                                        UP(List(Left("assm(rp)".asExpr), Left("assm(dc)".asExpr)), Kaisar.RCF())),
                                        Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, duh,
                                          Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "loop(v)-g*t".asTerm), "loop(v)-g*T".asTerm), "-(g/rp)^(1/2)".asTerm), FPat("assm(vBig)".asExpr)), FPat("assm(tBound)".asExpr)), FPat("assm(vInitBig)".asExpr)),
                                            PrintGoal("Almost done goal one ",
                                              Show("wild()".asFormula, UP(List(Left("assm(res)".asExpr), Left("assm(vBig)".asExpr), Left("assm(J)".asExpr)), Auto())))))))))))), List())))))

                      , BRule(RBAssign(Assign("r".asVariable, "rp".asVariable)), List(
                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                          BRule(RBInv(
                            Inv("consts".asVariable, "rp>0 & g>0".asFormula, duh, duh,
                              Ghost("y".asVariable, "-1/2*rp*(v-(g/rp)^(1/2))*y".asTerm, True, "(v+(g/rp)^(1/2))^(-1/2)".asTerm, duh, duh,
                                Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                                  Inv("ghostInv".asVariable, "(y^2*(v+(g/rp)^(1/2))=1)".asFormula, duh, duh,
                                    Finally(
                                      Show("wild()".asFormula, UP(List(Left("assm(ghostInv)".asExpr), Left("assm(vBig)".asExpr), Left("assm(J)".asExpr)), Kaisar.RCF())))))))), List())))))))))),
                Finally(
                  PrintGoal("About to conclude",
                    Show(post, UP(List(Left("assm(assms)".asExpr), Left("assm(J)".asExpr)), Auto())))))), List()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(safePara)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  "POPL'18 3b" should "prove" in {
    withMathematica(qeTool => {
      val time = System.currentTimeMillis()
      val sp: SP =
        State("init",
          BRule(RBAssume("assms".asVariable, "r=ra & ((dc_() & const_()) & dyn_())".asFormula), List(
            BRule(RBInv(
              Inv("J".asVariable, And(And(dc, const), dyn), duh,
                State("loop",
                  BRule(RBCase(List("dc_() & const_()".asFormula, "dyn_()".asFormula)), List(
                    BRule(RBConsequence("I".asVariable, True), List(
                      Show("wild()".asFormula, UP(List(), Kaisar.Auto()))
                      , Show("wild()".asFormula, UP(List(), Kaisar.Auto()))
                    ))
                    , BRule(RBCase(List("?(wild());".asProgram, "{wild}".asProgram)), List(
                      BRule(RBAssume("slowEnough".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula), List(
                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                          BRule(RBInv(
                            Inv("rp".asVariable, "g>0 & rp>0".asFormula, duh, duh,
                              Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                                Inv("vInitBig".asVariable, "loop(v)-g*T > -(g/rp)^(1/2)".asFormula, duh, duh,
                                  Inv("dc".asVariable, "t <= T".asFormula, duh, duh,
                                    Finally(
                                      Have("tBound".asVariable, "loop(v) -g*t >= loop(v) - g*T".asFormula, Show("wild()".asFormula,
                                        UP(List(Left("assm(rp)".asExpr), Left("assm(dc)".asExpr)), Kaisar.RCF())),
                                        Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, duh,
                                          Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "loop(v)-g*t".asTerm), "loop(v)-g*T".asTerm), "-(g/rp)^(1/2)".asTerm),
                                            FPat("assm(vBig)".asExpr)), FPat("assm(tBound)".asExpr)), FPat("assm(vInitBig)".asExpr)),
                                            PrintGoal("Almost done goal one ",
                                              Show("wild()".asFormula, UP(List(Left("assm(res)".asExpr), Left("assm(vBig)".asExpr), Left("assm(J)".asExpr)), Auto())))))))))))), List())))))
                      , BRule(RBAssign(Assign("r".asVariable, "rp".asVariable)), List(
                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                          BRule(RBInv(
                            Inv("consts".asVariable, "rp>0 & g>0".asFormula, duh, duh,
                              Ghost("y".asVariable, "-1/2*rp*(v-(g/rp)^(1/2))*y".asTerm, True, "(v+(g/rp)^(1/2))^(-1/2)".asTerm, duh, duh,
                                Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                                  Inv("ghostInv".asVariable, "(y^2*(v+(g/rp)^(1/2))=1)".asFormula, duh, duh,
                                    Finally(
                                      Show("wild()".asFormula, UP(List(Left("assm(ghostInv)".asExpr), Left("assm(vBig)".asExpr), Left("assm(J)".asExpr)), Kaisar.RCF())))))))), List())))))))))),
                Finally(
                  PrintGoal("About to conclude",
                    Show(post, UP(List(Left("assm(assms)".asExpr), Left("assm(J)".asExpr)), Auto())))))), List()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(safePara)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }


  "POPL'18 3c" should "prove" in {
    withMathematica(qeTool => {
      val time = System.currentTimeMillis()
      val sp: SP =
        State("init",
          BRule(RBAssume("assms".asVariable, pre), List(
            BRule(RBInv(Inv("DCCONST".asVariable, And(dc, const), duh, duh,
              Inv("DYN".asVariable, dynInv, duh,
                // TODO: Add pattern matching
                State("loop",
                  BRule(RBCase(List("{wild}".asProgram, "{wild}".asProgram)), List(
                    BRule(RBAssume("safe".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula), List(
                      BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                        BRule(RBInv(
                          Inv("rp".asVariable, "g>0 & rp>0".asFormula, duh, duh,
                            Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                              Inv("vInitBig".asVariable, "loop(v)-g*T > -(g/rp)^(1/2)".asFormula, duh, duh,
                                Inv("dc".asVariable, "t <= T".asFormula, duh, duh,
                                  Finally(
                                    Have("tBound".asVariable, "loop(v) -g*t >= loop(v) - g*T".asFormula, Show("wild()".asFormula,
                                      UP(List(Left("assm(rp)".asExpr), Left("assm(dc)".asExpr)), Kaisar.RCF())
                                    ),
                                      Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, duh,
                                        Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "loop(v)-g*t".asTerm), "loop(v)-g*T".asTerm), "-(g/rp)^(1/2)".asTerm),
                                          FPat("assm(vBig)".asExpr)), FPat("assm(tBound)".asExpr)), FPat("assm(vInitBig)".asExpr)),
                                          PrintGoal("Almost done goal one ",
                                            Show("wild()".asFormula, UP(List(Left("assm(res)".asExpr), Left("assm(vBig)".asExpr), Left("assm(DYN)".asExpr), Left("assm(DCCONST)".asExpr)), Auto())))))))))))
                        ), List())))
                    ))
                    ,
                    BRule(RBAssign(Assign("r".asVariable, "rp".asVariable)), List(
                      BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                        BRule(RBInv(
                          Inv("consts".asVariable, "rp>0 & g>0".asFormula, duh, duh,
                            Ghost("y".asVariable, "-1/2*rp*(v-(g/rp)^(1/2))*y".asTerm, True, "(v+(g/rp)^(1/2))^(-1/2)".asTerm, duh, duh,
                              Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                                Inv("ghostInv".asVariable, "(y^2*(v+(g/rp)^(1/2))=1)".asFormula, duh, duh,
                                  Finally(
                                    Show("wild()".asFormula, UP(List(Left("assm(ghostInv)".asExpr), Left("assm(vBig)".asExpr), Left("assm(DYN)".asExpr), Left("assm(DCCONST)".asExpr)), Kaisar.RCF())))))))), List())))))))),
                Finally(
                  PrintGoal("About to conclude",
                    //TODO: Badness
                    Show(post, UP(List(Left("assm(assms)".asExpr), Left("assm(DCCONST)".asExpr), Left("assm(DYN)".asExpr)), Auto()))))))), List()))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(safePara)) shouldBe 'proved
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
  "POPL'18 3d" should "prove" in {
    withMathematica(qeTool => {
      val time = System.currentTimeMillis()
      val sp: SP =
        State("init",
          BRule(RBAssume("niceAssume".asVariable, "x<=xmax".asFormula), List(
            BRule(RBAssume("assms".asVariable, pre), List(
              BRule(RBInv(Inv("DCCONST".asVariable, And(dc, const), duh, duh,
                Inv("DYN".asVariable, dynInv, duh,
                  // TODO: Add pattern matching
                  State("loop",
                    BRule(RBCase(List("{wild}".asProgram, "{wild}".asProgram)), List(
                      BRule(RBAssume("safe".asVariable, "r=ra & v-g*T > -(g/rp)^(1/2)".asFormula), List(
                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                          BRule(RBInv(
                            Inv("rp".asVariable, "g>0 & rp>0".asFormula, duh, duh,
                              Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                                Inv("vInitBig".asVariable, "loop(v)-g*T > -(g/rp)^(1/2)".asFormula, duh, duh,
                                  Inv("dc".asVariable, "t <= T".asFormula, duh, duh,
                                    Finally(
                                      Have("tBound".asVariable, "loop(v) -g*t >= loop(v) - g*T".asFormula, Show("wild()".asFormula,
                                        UP(List(Left("assm(rp)".asExpr), Left("assm(dc)".asExpr)), Kaisar.RCF())
                                      ), Have("trans".asVariable, "\\forall w \\forall x \\forall y \\forall z (w>=x -> x>=y -> y>z -> w>z)".asFormula, duh,
                                        Note("res".asVariable, FMP(FMP(FMP(FInst(FInst(FInst(FInst(FPat("trans".asVariable), "v".asTerm), "loop(v)-g*t".asTerm), "loop(v)-g*T".asTerm), "-(g/rp)^(1/2)".asTerm),
                                          FPat("assm(vBig)".asExpr)), FPat("assm(tBound)".asExpr)), FPat("assm(vInitBig)".asExpr)),
                                          Show("wild()".asFormula, UP(List(Left("assm(res)".asExpr), Left("assm(vBig)".asExpr), Left("assm(DYN)".asExpr), Left("assm(DCCONST)".asExpr)), Auto())) /*)*/))))))))
                          ), List())))
                      ))
                      ,
                      BRule(RBAssign(Assign("r".asVariable, "rp".asVariable)), List(
                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                          BRule(RBInv(
                            Inv("consts".asVariable, "rp>0 & g>0".asFormula, duh, duh,
                              Ghost("y".asVariable, "-1/2*rp*(v-(g/rp)^(1/2))*y".asTerm, True, "(v+(g/rp)^(1/2))^(-1/2)".asTerm, duh, duh,
                                Inv("vBig".asVariable, "v >= loop(v) - g*t".asFormula, duh, duh,
                                  Inv("ghostInv".asVariable, "(y^2*(v+(g/rp)^(1/2))=1)".asFormula, duh, duh,
                                    Finally(
                                      Show("wild()".asFormula, UP(List(Left("assm(ghostInv)".asExpr), Left("assm(vBig)".asExpr), Left("assm(DYN)".asExpr), Left("assm(DCCONST)".asExpr)), Kaisar.RCF())) /*)*/)))))), List()))))) /*)*/))),
                  Inv("xdown".asVariable, "x <= init(x)".asFormula, PrintGoal("base case ",
                    duh), duh,
                    Finally(
                      Show(lowPost, UP(List(Left("assm(niceAssume)".asExpr), Left("assm(xdown)".asExpr)), Auto()))))))), List()))))))
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(lowPara)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  // Kaisar port of RSS robotics case study
  "RSS Static Safety" should "prove" in {
    withMathematica(qeTool => {
      // Theorem 1
      val b = "b()".asTerm
      val A = "A()".asTerm
      val ep = "ep()".asTerm
      val v = "v".asVariable

      def stopDist(e: Term): Term = Divide(Power(e, Number(2)), Times(Number(2), b))

      def accelComp(e: Term): Term = Times(Plus(Divide(A, b), Number(1)), Plus(Times(Divide(A, Number(2)), Power(ep, Number(2))), Times(ep, e)))

      def admissibleSeparation(e: Term): Term = Plus(stopDist(e), accelComp(e))

      val isWellformedDir = "dx^2 + dy^2 = 1".asFormula

      val bounds = And(GreaterEqual(A, Number(0)), And(Greater(b, Number(0)), Greater(ep, Number(0))))
      val initialState = And("v=0".asFormula, And("(x-xo)^2 - (y-yo)^2 > 0".asFormula, isWellformedDir))
      val assumptions = And(bounds, initialState)
      val loopinv = And("v >= 0".asFormula, And(isWellformedDir, Or(Greater("abs(x-xo)".asTerm, stopDist(v)), Greater("abs(y-yo)".asTerm, stopDist(v)))))
      val accelTest: Program = Test(Or(Greater("abs(x-xo)".asTerm, admissibleSeparation(v)), Greater("abs(y-yo)".asTerm, admissibleSeparation(v))))
      val acclCtrl: Program = Compose(
        """a := A();
           w := *; ?-W()<=w & w<=W();       /* choose steering */
           r := *;
           xo := *; yo := *;            /* measure closest obstacle on the curve */
           /* admissible curve */
           ?r!=0 & r*w = v;""".asProgram, accelTest)
      val ctrl: Program = Compose(Choice(
        "a:=-b();".asProgram, Choice("?v=0; a:=0; w:=0;".asProgram, acclCtrl)),
        "t:=0;".asProgram)
      val plant: Program =
        """ { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
          dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
          t' = 1 & t <= ep() & v >= 0
          }""".asProgram
      val theorem1: Formula = Imply(assumptions, Box(Loop(Compose(ctrl, plant)), "(x-xo)^2 + (y-yo)^2 > 0".asFormula))
      /*assumptions() ->
  [{{{/* brake on current curve or remain stopped */
          { a := -b; }
          ++
          { ?v = 0; a := 0; w := 0; }
      	  ++
          /* or choose a new safe curve */
          { a := A;
            w := *; ?-W<=w & w<=W;       /* choose steering */
            r := *;
            xo := *; yo := *;            /* measure closest obstacle on the curve */

            /* admissible curve */
            ?r!=0 & r*w = v;

            /* use that curve, if it is a safe one (admissible velocities) */
            ? abs(x-xo) > admissibleSeparation(v)
            | abs(y-yo) > admissibleSeparation(v);
          }
        };t := 0;}
      /* dynamics */
      { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
        dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
        t' = 1 & t <= ep & v >= 0}}*@invariant(loopinv())
  ](x - xo)^2 + (y - yo)^2 > 0*/
      /*
* assume assms:"assumptions_()"
* Inv J:(v >= 0 & WFDir_() & (abs(x-xo) > SD_() | abs(y-yo) > SD_() )) {
*   Ind =>
*   state loop
*   // TODO: Support n-ary case
*   Case (a := -b) => {
*     assign a:= -b;
*     assign t:= 0;
*     // Braking case
*     Inv tPos:(t>=0)  {}
*     Inv wfDir:(WDFIR_()) {}
*     Inv vBound:(v = loop(v)-b()*t) {}
*     // TODO: Too sequent-level?
*     Inv xBound:(-t * (v + b()/2*t) <= x - loop(x) & x - loop(x) <= t * (v + b()/2*t))
*     Inv yBound:(-t * (v + b()/2*t) <= y - loop(y) & y - loop(y) <= t * (v + b()/2*t))
*     finally show (_) by QE
*
*   } Case (_ ++ _) => {
*     Case (?v=0; a:=0; w:=0;) {
*       assume stopped:(?v=0)
*       assign a:=0
*       assign w:=0
*       assign t:=0
*       Inv tPos:(t>=0)  {}
*       Inv wfDir:(WDFIR_()) {}
*       Inv vEq:(v = loop(v))
*       Inv xEq:(x = loop(x))
*       Inv yEq:(y = loop(y))
*       finally show (_) by QE
*     }
*       Case(a := A;_) {
*       assign a := A;
*       assign w:= *; assume wGood:(-W<=w & w <=W)
*       assign r:=*; assign xo:=*; assign yo:=*;
*       assume goodCurve:(r!=0 & r*w =v)
*       assume safeCurve:((abs(x-xo) > admitSepV
*              |(abs(y-yo) > admitSepV))
*       Inv tPos:(t>=0)  {}
*       Inv wfDir:(WDFIR_()) {}
*       Inv vBound:(v = loop(v) + A()*t)
*       Inv xBound:(-t * (v - A()/2*t) <= x - loop(x) & x - loop(x) <= t * (v - A()/2*t))
*       Inv yBound:(-t * (v - A()/2*t) <= y - loop(y) & y - loop(y) <= t * (v - A()/2*t))
*       finally show (_) by QE}}
* show ((x-xo)^2 + (y-yo)^2 > 0) using J by auto
* */

      val sp: SP =
        FLet("WFDIR", "t", PredicationalOf(Function("t", None, Bool, Bool), isWellformedDir),
          FLet("SD", "t", FuncOf(Function("t", None, Real, Real), stopDist("v".asVariable)),
            FLet("ASEP", "t", FuncOf(Function("t", None, Real, Real), Plus(stopDist("v".asVariable), accelComp("v".asVariable))),
              BRule(RBAssume("assms".asVariable, "wild()".asFormula), List(
                BRule(RBInv(Inv("J".asVariable, "(v >= 0 & WFDIR() & (abs(x-xo) > SD() | abs(y-yo) > SD() ))".asFormula, duh,
                  State("loop",
                    BRule(RBCase(List("a := -b();".asProgram, "{wild} ++ {wild}".asProgram)), List(
                      // braking
                      BRule(RBAssign(Assign("a".asVariable, "-b()".asTerm)), List(
                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                          BRule(RBInv(
                            Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                              Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                Inv("vBound".asVariable, "v = loop(v)-b()*t".asFormula, duh, duh,
                                  Inv("xBound".asVariable, "-t * (v + b()/2*t) <= x - loop(x) & x - loop(x) <= t * (v + b()/2*t)".asFormula, duh, duh,
                                    Inv("yBound".asVariable, "-t * (v + b()/2*t) <= y - loop(y) & y - loop(y) <= t * (v + b()/2*t)".asFormula, duh, duh,
                                      Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                        Finally(PrintGoal("End first branch",
                                          Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))))))))
                          ), List()) //)
                        ))
                      ))
                      , // stopped + accel
                      BRule(RBCase(List("?v=0; a:=0; w:=0;".asProgram, "{a := A();{wild}}{wild}".asProgram)), List(
                        // stopped
                        BRule(RBAssume("stopped".asVariable, "v=0".asFormula), List(
                          BRule(RBAssign(Assign("a".asVariable, "0".asTerm)), List(
                            BRule(RBAssign(Assign("w".asVariable, "0".asTerm)), List(
                              BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                BRule(RBInv(
                                  Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                    Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                      Inv("vEq".asVariable, "v = loop(v)".asFormula, duh, duh,
                                        Inv("xEq".asVariable, "x = loop(x)".asFormula, duh, duh,
                                          Inv("yEq".asVariable, "y = loop(y)".asFormula, duh, duh,
                                            Inv("dC".asVariable,
                                              "v >= 0 & t <= ep()".asFormula, duh, duh,
                                              Finally(
                                                Show("wild()".asFormula, UP(List(), Kaisar.RCF())) /*)*/)))))))), List())))))))))
                        ,
                        PrintGoal("Starting third case",
                          BRule(RBAssign(Assign("a".asVariable, "A()".asTerm)), List(
                            BRule(RBAssignAny("w".asVariable), List(
                              BRule(RBAssume("wGood".asVariable, "-W()<=w & w<=W()".asFormula), List(
                                BRule(RBAssignAny("r".asVariable), List(
                                  BRule(RBAssignAny("xo".asVariable), List(
                                    BRule(RBAssignAny("yo".asVariable), List(
                                      BRule(RBAssume("goodCurve".asVariable, "r!=0 & r*w=v".asFormula), List(
                                        BRule(RBAssume("safeCurve".asVariable, "(abs(x-xo) > ASEP())|(abs(y-yo)>ASEP())".asFormula), List(
                                          BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                            PrintGoal("Starting third invs",
                                              BRule(RBInv(
                                                Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                                  Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                    Inv("vBound".asVariable, "v = loop(v) + A()*t".asFormula, duh, duh,
                                                      Inv("xBound".asVariable, "-t * (v - A()/2*t) <= x - loop(x) & x - loop(x) <= t * (v - A()/2*t)".asFormula, duh, duh,
                                                        Inv("yBound".asVariable, "-t * (v - A()/2*t) <= y - loop(y) & y - loop(y) <= t * (v - A()/2*t)".asFormula, duh, duh,
                                                          Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                            Finally(
                                                              PrintGoal("End third goal", Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))))))))), List())))))))))))))))))))) /*)*/)) /*)*/)))),
                  Finally(Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))),
                  List()))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(theorem1)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }
  "Final arithmetic subgoal for RSS Theorem 2" should "prove" in {
    withMathematica(qeTool => {
      val pr: Provable = Provable.startProof(
        new Sequent(
          immutable.IndexedSeq[Formula](
            /*-1*/ "(A()>=0&b()>0&ep()>0&V()>0)&v_0=0&(x_0-xo_0)^2-(y_0-yo_0)^2>0&dx_0^2+dy_0^2=1".asFormula,
            /*-2*/ "v_1>=0&dx_1^2+dy_1^2=1&(v_1>0->abs(x_1-xo_1)>v_1^2/(2*b())+V()*(v_1/b())|abs(y_1-yo_1)>v_1^2/(2*b())+V()*(v_1/b()))".asFormula,
            /*-3*/ "vxo^2+vyo^2<=V()^2".asFormula,
            /*-4*/ "-W()<=w_0&w_0<=W()".asFormula,
            /*-5*/ "r!=0&r*w_0=v_1".asFormula,
            /*-6*/ "abs(x_1-xo_2)>v_1^2/(2*b())+V()*(v_1/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_1+V()))|abs(y_1-yo_2)>v_1^2/(2*b())+V()*(v_1/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v_1+V()))".asFormula,
            /*-7*/ "t_0=0".asFormula,
            /*-8*/ "t>=0".asFormula,
            /*-9*/ "dx^2+dy^2=1".asFormula,
            /*-10*/ "-t*V()<=xo-xo_2&xo-xo_2<=t*V()".asFormula,
            /*-11*/ "-t*V()<=yo-yo_2&yo-yo_2<=t*V()".asFormula,
            /*-12*/ "v=v_1+A()*t".asFormula,
            /*-13*/ "-t*(v-A()/2*t)<=x-x_1&x-x_1<=t*(v-A()/2*t)".asFormula,
            /*-14*/ "-t*(v-A()/2*t)<=y-y_1&y-y_1<=t*(v-A()/2*t)".asFormula,
            /*-15*/ "v>=0&t<=ep()".asFormula),
          immutable.IndexedSeq[Formula]("v>=0&dx^2+dy^2=1&(v>0->abs(x-xo)>v^2/(2*b())+V()*(v/b())|abs(y-yo)>v^2/(2*b())+V()*(v/b()))".asFormula)))

      def asBV(s: String): BaseVariable = s.asVariable.asInstanceOf[BaseVariable]

      val h = History(List(HCRename(asBV("x"), asBV("x_1"), None), HCRename(asBV("y"), asBV("y_1"), None), HCRename(asBV("dx"), asBV("dx_1"), None), HCRename(asBV("w"), asBV("w_2"), None), HCRename(asBV("dy"), asBV("dy_1"), None), HCRename(asBV("yo"), asBV("yo_2"), None), HCRename(asBV("xo"), asBV("xo_2"), None), HCRename(asBV("v"), asBV("v_1"), None), HCRename(asBV("t"), asBV("t_2"), None), HCTimeStep("safeCurve"), HCRename(asBV("t"), asBV("t_1"), Some(AntePos(6))), HCRename(asBV("yo"), asBV("yo_1"), None), HCRename(asBV("xo"), asBV("xo_1"), None), HCRename(asBV("r"), asBV("r_1"), None), HCRename(asBV("w"), asBV("w_1"), None), HCAssign("a:=A();".asProgram.asInstanceOf[Assign]), HCRename(asBV("vyo"), asBV("vyo_1"), None), HCRename(asBV("vxo"), asBV("vxo_1"), None), HCTimeStep("loop"), HCRename(asBV("x"), asBV("x_0"), None), HCRename(asBV("y"), asBV("y_0"), None), HCRename(asBV("dx"), asBV("dx_0"), None), HCRename(asBV("w"), asBV("w_0"), None), HCRename(asBV("dy"), asBV("dy_0"), None), HCRename(asBV("a"), asBV("a_0"), None), HCRename(asBV("yo"), asBV("yo_0"), None), HCRename(asBV("r"), asBV("r_0"), None), HCRename(asBV("xo"), asBV("xo_0"), None), HCRename(asBV("vyo"), asBV("vyo_0"), None), HCRename(asBV("v"), asBV("v_0"), None), HCRename(asBV("t"), asBV("t_0"), None), HCRename(asBV("vxo"), asBV("vxo_0"), None), HCTimeStep("init")))
      val c = Context(Map(
        "assms".asVariable -> AntePosition(1),
        "J".asVariable -> AntePosition(2),
        "safeObs".asVariable -> AntePosition(3),
        "wGood".asVariable -> AntePosition(4),
        "goodCurve".asVariable -> AntePosition(5),
        "greatCurve".asVariable -> AntePosition(6),
        "tPos".asVariable -> AntePosition(8),
        "wfDir".asVariable -> AntePosition(9),
        "xoBound".asVariable -> AntePosition(10),
        "yoBound".asVariable -> AntePosition(11),
        "vBound".asVariable -> AntePosition(12),
        "xBound".asVariable -> AntePosition(13),
        "yBound".asVariable -> AntePosition(14),
        "dC".asVariable -> AntePosition(15)
      ),
        Map(),
        Map("WFDIR" -> ("t", "t{dx^2+dy^2=1}".asFormula),
          "SD" -> ("t", "t(v^2/(2*b())+V()*(v/b()))".asTerm),
          "ASEP" -> ("t", "t(v^2/(2*b())+V()*(v/b())+(A()/b()+1)*(A()/2*ep()^2+ep()*(v+V())))".asTerm)))
      // neg{wild() > wild() + wild() + (wild()*(wild()*ep()^2 + wild()))}
      val sp: SP =
        BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(x-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(y-yo)) > wild()".asFormula), List(
          Have("dxep".asVariable, "safeCurve(abs(x-xo)) > safeCurve(v^2)/(2*b()) + V()*(safeCurve(v)/b()) + (A()/b() + 1)*(A()/2*t^2 +t*(safeCurve(v)+V()))".asFormula, duh,
            Show("wild()".asFormula, UP(List(Left("neg(assm(greatCurve))".asExpr)), Kaisar.RCF())))
          , Have("dyep".asVariable, "safeCurve(abs(y-yo)) > safeCurve(v^2)/(2*b()) + V()*(safeCurve(v)/b()) + (A()/b() + 1)*(A()/2*t^2 +t*(safeCurve(v)+V()))".asFormula, duh,
            Show("wild()".asFormula, UP(List(Left("neg(assm(greatCurve))".asExpr)), Kaisar.RCF())))
        ))

      Kaisar.eval(sp, h, c, pr) shouldBe 'proved
    })
  }

  // Kaisar port of RSS robotics case study
  "RSS Passive Safety" should "prove" in {
    withMathematica(qeTool => {
      // Theorem 1
      val b = "b()".asTerm
      val A = "A()".asTerm
      val ep = "ep()".asTerm
      val v = "v".asVariable
      val V = "V()".asTerm

      def stopDist(e: Term): Term = Plus(Divide(Power(e, Number(2)), Times(Number(2), b)), Times(V, Divide(e, b)))

      def accelComp(e: Term): Term = Times(Plus(Divide(A, b), Number(1)), Plus(Times(Divide(A, Number(2)), Power(ep, Number(2))), Times(ep, Plus(e, V))))

      def admissibleSeparation(e: Term): Term = Plus(stopDist(e), accelComp(e))

      val isWellformedDir = "dx^2 + dy^2 = 1".asFormula

      val bounds = And(GreaterEqual(A, Number(0)), And(Greater(b, Number(0)), And(Greater(ep, Number(0)), Greater(V, Number(0)))))
      val initialState = And("v=0".asFormula, And("(x-xo)^2 - (y-yo)^2 > 0".asFormula, isWellformedDir))
      val assumptions = And(bounds, initialState)
      val loopinv = And("v >= 0".asFormula, And(isWellformedDir, Imply(Greater(v, Number(0)), Or(Greater("abs(x-xo)".asTerm, stopDist(v)), Greater("abs(y-yo)".asTerm, stopDist(v))))))
      val accelTest: Program = Test(Or(Greater("abs(x-xo)".asTerm, admissibleSeparation(v)), Greater("abs(y-yo)".asTerm, admissibleSeparation(v))))
      val acclCtrl: Program = Compose(
        """a := A();
           w := *; ?-W()<=w & w<=W();       /* choose steering */
           r := *;
           xo := *; yo := *;            /* measure closest obstacle on the curve */
           /* admissible curve */
           ?r!=0 & r*w = v;""".asProgram, accelTest)
      val obsCtrl: Program = "vxo:=*;vyo:=*;?(vxo^2+vyo^2<=V()^2);".asProgram
      val robCtrl: Program = Compose(Choice(
        "a:=-b();".asProgram, Choice("?v=0; a:=0; w:=0;".asProgram, acclCtrl)),
        "t:=0;".asProgram)
      val plant: Program =
        """ { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
          dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
          xo' = vxo, yo' = vyo,
          t' = 1 & t <= ep() & v >= 0
          }""".asProgram
      val ctrl = Compose(obsCtrl, robCtrl)
      val theorem2: Formula = Imply(assumptions, Box(Loop(Compose(ctrl, plant)), "v>0 -> ((x-xo)^2 + (y-yo)^2 > 0)".asFormula))
      /*assumptions() ->
        [{{{/* brake on current curve or remain stopped */
                { a := -b; }
                ++
                { ?v = 0; a := 0; w := 0; }
                ++
                /* or choose a new safe curve */
                { a := A;
                  w := *; ?-W<=w & w<=W;       /* choose steering */
                  r := *;
                  xo := *; yo := *;            /* measure closest obstacle on the curve */

                  /* admissible curve */
                  ?r!=0 & r*w = v;

                  /* use that curve, if it is a safe one (admissible velocities) */
                  ? abs(x-xo) > admissibleSeparation(v)
                  | abs(y-yo) > admissibleSeparation(v);
                }
              };t := 0;}
            /* dynamics */
            { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
              dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
              t' = 1 & t <= ep & v >= 0}}*@invariant(loopinv())
        ](x - xo)^2 + (y - yo)^2 > 0*/
      /*
* assume assms:"assumptions_()"
* Inv J:(v >= 0 & WFDir_() & (abs(x-xo) > SD_() | abs(y-yo) > SD_() )) {
*   Ind =>
*   state loop
*   // TODO: Support n-ary case
*   Case (a := -b) => {
*     assign a:= -b;
*     assign t:= 0;
*     // Braking case
*     Inv tPos:(t>=0)  {}
*     Inv wfDir:(WDFIR_()) {}
*     Inv vBound:(v = loop(v)-b()*t) {}
*     // TODO: Too sequent-level?
*     Inv xBound:(-t * (v + b()/2*t) <= x - loop(x) & x - loop(x) <= t * (v + b()/2*t))
*     Inv yBound:(-t * (v + b()/2*t) <= y - loop(y) & y - loop(y) <= t * (v + b()/2*t))
*     finally show (_) by QE
*
*   } Case (_ ++ _) => {
*     Case (?v=0; a:=0; w:=0;) {
*       assume stopped:(?v=0)
*       assign a:=0
*       assign w:=0
*       assign t:=0
*       Inv tPos:(t>=0)  {}
*       Inv wfDir:(WDFIR_()) {}
*       Inv vEq:(v = loop(v))
*       Inv xEq:(x = loop(x))
*       Inv yEq:(y = loop(y))
*       finally show (_) by QE
*     }
*       Case(a := A;_) {
*       assign a := A;
*       assign w:= *; assume wGood:(-W<=w & w <=W)
*       assign r:=*; assign xo:=*; assign yo:=*;
*       assume goodCurve:(r!=0 & r*w =v)
*       assume safeCurve:((abs(x-xo) > admitSepV
*              |(abs(y-yo) > admitSepV))
*       Inv tPos:(t>=0)  {}
*       Inv wfDir:(WDFIR_()) {}
*       Inv vBound:(v = loop(v) + A()*t)
*       Inv xBound:(-t * (v - A()/2*t) <= x - loop(x) & x - loop(x) <= t * (v - A()/2*t))
*       Inv yBound:(-t * (v - A()/2*t) <= y - loop(y) & y - loop(y) <= t * (v - A()/2*t))
*       finally show (_) by QE}}
* show ((x-xo)^2 + (y-yo)^2 > 0) using J by auto
* */

      val sp: SP =
        FLet("WFDIR", "t", PredicationalOf(Function("t", None, Bool, Bool), isWellformedDir),
          FLet("SD", "t", FuncOf(Function("t", None, Real, Real), stopDist("v".asVariable)),
            FLet("ASEP", "t", FuncOf(Function("t", None, Real, Real), Plus(stopDist("v".asVariable), accelComp("v".asVariable))),
              BRule(RBAssume("assms".asVariable, "wild()".asFormula), List(
                BRule(RBInv(Inv("J".asVariable, "(v >= 0 & WFDIR() & (v> 0 -> (abs(x-xo) > SD() | abs(y-yo) > SD() )))".asFormula, duh,
                  State("loop",
                    BRule(RBAssignAny("vxo".asVariable), List(
                      BRule(RBAssignAny("vyo".asVariable), List(
                        BRule(RBAssume("safeObs".asVariable, "vxo^2+vyo^2<=V()^2".asFormula), List(
                          BRule(RBCase(List("a := -b();".asProgram, "{wild} ++ {wild}".asProgram)), List(
                            // braking
                            BRule(RBAssign(Assign("a".asVariable, "-b()".asTerm)), List(
                              BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                BRule(RBInv(
                                  Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                    Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                      Inv("vBound".asVariable, "v = loop(v)-b()*t".asFormula, duh, duh,
                                        Inv("xoBound".asVariable, "-t*V() <= xo - loop(xo) & xo - loop(xo) <= t*V()".asFormula, duh, duh,
                                          Inv("yoBound".asVariable, "-t*V() <= yo - loop(yo) & yo - loop(yo) <= t*V()".asFormula, duh, duh,
                                            Inv("xBound".asVariable, "-t * (v + b()/2*t) <= x - loop(x) & x - loop(x) <= t * (v + b()/2*t)".asFormula, duh, duh,
                                              Inv("yBound".asVariable, "-t * (v + b()/2*t) <= y - loop(y) & y - loop(y) <= t * (v + b()/2*t)".asFormula, duh, duh,
                                                Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                  Finally(PrintGoal("End first branch",
                                                    Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))))))))))
                                ), List()) //)
                              ))
                            ))
                            , // stopped + accel
                            PrintGoal("Beginning second branch",
                              BRule(RBCase(List("?v=0; a:=0; w:=0;".asProgram, "{a := A();{wild}}{wild}".asProgram)), List(
                                // stopped
                                BRule(RBAssume("stopped".asVariable, "v=0".asFormula), List(
                                  BRule(RBAssign(Assign("a".asVariable, "0".asTerm)), List(
                                    BRule(RBAssign(Assign("w".asVariable, "0".asTerm)), List(
                                      BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                        PrintGoal("Beginning second inv",
                                          BRule(RBInv(
                                            Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                              Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                Inv("xoBound".asVariable, "-t*V() <= xo - loop(xo) & xo - loop(xo) <= t*V()".asFormula, duh, duh,
                                                  Inv("yoBound".asVariable, "-t*V() <= yo - loop(yo) & yo - loop(yo) <= t*V()".asFormula, duh, duh,
                                                    Inv("vEq".asVariable, "v = loop(v)".asFormula, duh, duh,
                                                      Inv("xEq".asVariable, "x = loop(x)".asFormula, duh, duh,
                                                        Inv("yEq".asVariable, "y = loop(y)".asFormula, duh, duh,
                                                          Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                            Finally(
                                                              PrintGoal("End of second branch",
                                                                Show("wild()".asFormula, UP(List(), Kaisar.RCF()))) /*)*/)))))))))), List()))))))))))
                                ,
                                PrintGoal("Beginning third branch",
                                  BRule(RBAssign(Assign("a".asVariable, "A()".asTerm)), List(
                                    BRule(RBAssignAny("w".asVariable), List(
                                      BRule(RBAssume("wGood".asVariable, "-W()<=w & w<=W()".asFormula), List(
                                        BRule(RBAssignAny("r".asVariable), List(
                                          BRule(RBAssignAny("xo".asVariable), List(
                                            BRule(RBAssignAny("yo".asVariable), List(
                                              BRule(RBAssume("goodCurve".asVariable, "r!=0 & r*w=v".asFormula), List(
                                                BRule(RBAssume("greatCurve".asVariable, "(abs(x-xo) > ASEP())|(abs(y-yo)>ASEP())".asFormula), List(
                                                  BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                                    State("safeCurve",
                                                      PrintGoal("Beginning third invs",
                                                        BRule(RBInv(
                                                          Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                                            Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                              Inv("xoBound".asVariable, "-t*V() <= xo - safeCurve(xo) & xo - safeCurve(xo) <= t*V()".asFormula, duh, duh,
                                                                Inv("yoBound".asVariable, "-t*V() <= yo - safeCurve(yo) & yo - safeCurve(yo) <= t*V()".asFormula, duh, duh,
                                                                  Inv("vBound".asVariable, "v = loop(v) + A()*t".asFormula, duh, duh,
                                                                    Inv("xBound".asVariable, "-t * (v - A()/2*t) <= x - loop(x) & x - loop(x) <= t * (v - A()/2*t)".asFormula, duh, duh,
                                                                      Inv("yBound".asVariable, "-t * (v - A()/2*t) <= y - loop(y) & y - loop(y) <= t * (v - A()/2*t)".asFormula, duh, duh,
                                                                        Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                                          Finally(
                                                                            PrintGoal("End third goal",
                                                                              BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(x-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(y-yo)) > wild()".asFormula), List(
                                                                                Have("dxep".asVariable, "safeCurve(abs(x-xo)) > safeCurve(v^2)/(2*b()) + V()*(safeCurve(v)/b()) + (A()/b() + 1)*(A()/2*t^2 +t*(safeCurve(v)+V()))".asFormula, duh,
                                                                                  Show("wild()".asFormula, UP(List(Left("neg(assm(greatCurve))".asExpr)), Kaisar.RCF())))
                                                                                , Have("dyep".asVariable, "safeCurve(abs(y-yo)) > safeCurve(v^2)/(2*b()) + V()*(safeCurve(v)/b()) + (A()/b() + 1)*(A()/2*t^2 +t*(safeCurve(v)+V()))".asFormula, duh,
                                                                                  Show("wild()".asFormula, UP(List(Left("neg(assm(greatCurve))".asExpr)), Kaisar.RCF())))
                                                                              ))
                                                                            ))))))))))), List())))))))))))))))))))))))))))))))))),
                  Finally(Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))), List()))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(theorem2)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  // Kaisar port of RSS robotics case study
  "RSS Passive Safety with Steering" should "prove" in {
    withMathematica(qeTool => {
      // Theorem 1
      val b = "b()".asTerm
      val A = "A()".asTerm
      val ep = "ep()".asTerm
      val v = "v".asVariable
      val V = "V()".asTerm

      def stopDist(e: Term): Term = Plus(Divide(Power(e, Number(2)), Times(Number(2), b)), Times(V, Divide(e, b)))

      val isWellformedDir = "dx^2 + dy^2 = 1".asFormula

      val bounds = And(GreaterEqual(A, Number(0)), And(Greater(b, Number(0)), And(Greater(ep, Number(0)), Greater(V, Number(0)))))
      val initialState = And("v=0".asFormula, And("(x-xo)^2 - (y-yo)^2 > 0".asFormula, isWellformedDir))
      val assumptions = And(bounds, initialState)
      val loopinv = And("v >= 0".asFormula, And(isWellformedDir, Imply(Greater(v, Number(0)), Or(Greater("abs(x-xo)".asTerm, stopDist(v)), Greater("abs(y-yo)".asTerm, stopDist(v))))))
      val acclCtrl: Program =
        """a :=*; ?(-b()<=a & a <= A());
           w := *; ?(-W()<=w & w<=W());       /* choose steering */
           r := *;
           xo := *; yo := *;            /* measure closest obstacle on the curve */
           /* admissible curve */
           ?r!=0 & r*w = v;

           if (v+a*ep()>=0) { ?abs(x-xo) > (v^2 / (2*b()) + V()*v/b()) + (a/b()+1)*(a/2*ep()^2 + ep()*(v+V())) | abs(y-yo) > (v^2 / (2*b()) + V()*v/b()) + (a/b()+1)*(a/2*ep()^2 + ep()*(v+V())); }
           else          { ?abs(x-xo) > -v^2/(2*a)-V()*v/a | abs(y-yo) > -v^2/(2*a)-V()*v/a;}
       """.asProgram
      val obsCtrl: Program = "vxo:=*;vyo:=*;?(vxo^2+vyo^2<=V()^2);".asProgram
      val robCtrl: Program = Compose(Choice(
        "a:=-b();".asProgram, Choice(
          "?v=0; a:=0; w:=0;".asProgram, acclCtrl)),
        "t:=0;".asProgram)
      val plant: Program =
        """ { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
          dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
          xo' = vxo, yo' = vyo,
          t' = 1 & t <= ep() & v >= 0
          }""".asProgram
      val ctrl = Compose(obsCtrl, robCtrl)
      val theorem5: Formula = Imply(assumptions, Box(Loop(Compose(ctrl, plant)), "v>0 -> ((x-xo)^2 + (y-yo)^2 > 0)".asFormula))


      val sp: SP =
        FLet("WFDIR", "t", PredicationalOf(Function("t", None, Bool, Bool), isWellformedDir),
          FLet("SD", "t", FuncOf(Function("t", None, Real, Real), stopDist("v".asVariable)),
            BRule(RBAssume("assms".asVariable, "wild()".asFormula), List(
              BRule(RBInv(Inv("J".asVariable, "(v >= 0 & WFDIR() & (v> 0 -> (abs(x-xo) > SD() | abs(y-yo) > SD() )))".asFormula, duh,
                State("loop",
                  BRule(RBAssignAny("vxo".asVariable), List(
                    BRule(RBAssignAny("vyo".asVariable), List(
                      BRule(RBAssume("safeObs".asVariable, "vxo^2+vyo^2<=V()^2".asFormula), List(
                        BRule(RBCase(List("a := -b();".asProgram, "{wild} ++ {wild}".asProgram)), List(
                          // braking
                          BRule(RBAssign(Assign("a".asVariable, "-b()".asTerm)), List(
                            BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                              BRule(RBInv(
                                Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                  Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                    Inv("vBound".asVariable, "v = loop(v)-b()*t".asFormula, duh, duh,
                                      Inv("xoBound".asVariable, "-t*V() <= xo - loop(xo) & xo - loop(xo) <= t*V()".asFormula, duh, duh,
                                        Inv("yoBound".asVariable, "-t*V() <= yo - loop(yo) & yo - loop(yo) <= t*V()".asFormula, duh, duh,
                                          Inv("xBound".asVariable, "-t * (v + b()/2*t) <= x - loop(x) & x - loop(x) <= t * (v + b()/2*t)".asFormula, duh, duh,
                                            Inv("yBound".asVariable, "-t * (v + b()/2*t) <= y - loop(y) & y - loop(y) <= t * (v + b()/2*t)".asFormula, duh, duh,
                                              Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                Finally(PrintGoal("End first branch",
                                                  Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))))))))))
                              ), List()) //)
                            ))
                          ))
                          , // stopped + accel
                          PrintGoal("Beginning second branch",
                            BRule(RBCase(List("?v=0; a:=0; w:=0;".asProgram, "{a :=*;{wild}}{wild}".asProgram)), List(
                              // stopped
                              BRule(RBAssume("stopped".asVariable, "v=0".asFormula), List(
                                BRule(RBAssign(Assign("a".asVariable, "0".asTerm)), List(
                                  BRule(RBAssign(Assign("w".asVariable, "0".asTerm)), List(
                                    BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                      PrintGoal("Beginning second inv",
                                        BRule(RBInv(
                                          Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                            Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                              Inv("xoBound".asVariable, "-t*V() <= xo - loop(xo) & xo - loop(xo) <= t*V()".asFormula, duh, duh,
                                                Inv("yoBound".asVariable, "-t*V() <= yo - loop(yo) & yo - loop(yo) <= t*V()".asFormula, duh, duh,
                                                  Inv("vEq".asVariable, "v = loop(v)".asFormula, duh, duh,
                                                    Inv("xEq".asVariable, "x = loop(x)".asFormula, duh, duh,
                                                      Inv("yEq".asVariable, "y = loop(y)".asFormula, duh, duh,
                                                        Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                          Finally(
                                                            PrintGoal("End of second branch",
                                                              Show("wild()".asFormula, UP(List(), Kaisar.RCF()))) /*)*/)))))))))), List())))))))))),
                              //Free Driving cases
                              PrintGoal("Beginning third branch",
                                BRule(RBAssignAny("a".asVariable), List(
                                  BRule(RBAssume("aGood".asVariable, "-b()<=a & a <= A()".asFormula), List(
                                    BRule(RBAssignAny("w".asVariable), List(
                                      BRule(RBAssume("wGood".asVariable, "-W()<=w & w<=W()".asFormula), List(
                                        BRule(RBAssignAny("r".asVariable), List(
                                          BRule(RBAssignAny("xo".asVariable), List(
                                            BRule(RBAssignAny("yo".asVariable), List(
                                              BRule(RBAssume("goodCurve".asVariable, "r!=0 & r*w=v".asFormula), List(
                                                PrintGoal("Beginning third+fourth branching",
                                                  BRule(RBCase(List("{?(v+a*ep()>=0);{wild}}".asProgram, "{?(!(v+a*ep()>=0));{wild}}".asProgram)), List(

                                                    BRule(RBAssume("alrightCurve".asVariable, "(v+a*ep()>=0)".asFormula), List(
                                                      BRule(RBAssume("greatCurve".asVariable, "abs(x-xo) > (v^2 / (2*b()) + V()*v/b()) + (a/b()+1)*(a/2*ep()^2 + ep()*(v+V())) | abs(y-yo) > (v^2 / (2*b()) + V()*v/b()) + (a/b()+1)*(a/2*ep()^2 + ep()*(v+V()))".asFormula), List(
                                                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                                          State("safeCurve",
                                                            PrintGoal("Beginning third invs",
                                                              BRule(RBInv(
                                                                Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                                                  Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                                    Inv("xoBound".asVariable, "-t*V() <= xo - safeCurve(xo) & xo - safeCurve(xo) <= t*V()".asFormula, duh, duh,
                                                                      Inv("yoBound".asVariable, "-t*V() <= yo - safeCurve(yo) & yo - safeCurve(yo) <= t*V()".asFormula, duh, duh,
                                                                        Inv("vBound".asVariable, "v = loop(v) + a*t".asFormula, duh, duh,
                                                                          Inv("xBound".asVariable, "-t * (v - a/2*t) <= x - loop(x) & x - loop(x) <= t * (v - a/2*t)".asFormula, duh, duh,
                                                                            Inv("yBound".asVariable, "-t * (v - a/2*t) <= y - loop(y) & y - loop(y) <= t * (v - a/2*t)".asFormula, duh, duh,
                                                                              Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                                                Finally(
                                                                                  PrintGoal("End third goal",
                                                                                    BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
                                                                                      duh
                                                                                      ,
                                                                                      BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
                                                                                        duh,
                                                                                        BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
                                                                                          BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(x-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(y-yo)) > wild()".asFormula), List(
                                                                                            Have("dxep".asVariable, "abs(safeCurve(x-xo)) > (safeCurve(v)^2 / (2*b()) + V()*safeCurve(v)/b()) + (a/b()+1)*(a/2*t^2 + t*(safeCurve(v) +V()))".asFormula, duh,
                                                                                              BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                                                Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))
                                                                                            , Have("dyep".asVariable, "abs(safeCurve(y-yo)) > (safeCurve(v)^2 / (2*b()) + V()*safeCurve(v)/b()) + (a/b()+1)*(a/2*t^2 + t*(safeCurve(v) +V()))".asFormula, duh,
                                                                                              BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                                                Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))))))
                                                                                      ))))
                                                                                  ))))))))))), List())))))))))
                                                    ,
                                                    BRule(RBAssume("alrightCurve".asVariable, "!(v+a*ep()>=0)".asFormula), List(
                                                      BRule(RBAssume("greatCurve".asVariable, "abs(x-xo) > -v^2/(2*a)-V()*v/a | abs(y-yo) > -v^2/(2*a)-V()*v/a".asFormula), List(
                                                        BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                                          State("safeCurve",
                                                            PrintGoal("Beginning third invs",
                                                              BRule(RBInv(
                                                                Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                                                  Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                                    Inv("xoBound".asVariable, "-t*V() <= xo - safeCurve(xo) & xo - safeCurve(xo) <= t*V()".asFormula, duh, duh,
                                                                      Inv("yoBound".asVariable, "-t*V() <= yo - safeCurve(yo) & yo - safeCurve(yo) <= t*V()".asFormula, duh, duh,
                                                                        Inv("vBound".asVariable, "v = loop(v) + a*t".asFormula, duh, duh,
                                                                          Inv("xBound".asVariable, "-t * (v - a/2*t) <= x - loop(x) & x - loop(x) <= t * (v - a/2*t)".asFormula, duh, duh,
                                                                            Inv("yBound".asVariable, "-t * (v - a/2*t) <= y - loop(y) & y - loop(y) <= t * (v - a/2*t)".asFormula, duh, duh,
                                                                              Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                                                Finally(
                                                                                  PrintGoal("End third goal",
                                                                                    BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
                                                                                      duh
                                                                                      ,
                                                                                      BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
                                                                                        duh,
                                                                                        BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
                                                                                          BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(x-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(y-yo)) > wild()".asFormula), List(
                                                                                            Have("dxep".asVariable, "abs(safeCurve(x-xo)) > (safeCurve(v)^2 / (2*b()) + V()*safeCurve(v)/b()) + (a/b()+1)*(a/2*t^2 + t*(safeCurve(v) +V()))".asFormula, duh,
                                                                                              BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                                                Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))
                                                                                            , Have("dyep".asVariable, "abs(safeCurve(y-yo)) > (safeCurve(v)^2 / (2*b()) + V()*safeCurve(v)/b()) + (a/b()+1)*(a/2*t^2 + t*(safeCurve(v) +V()))".asFormula, duh,
                                                                                              BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                                                Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))))))
                                                                                      ))))))))))))))), List())))))
                                                      ))))))))))))))))))))))))))))))))))))
                , Finally(Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))), List())))))
      //)
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(theorem5)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  "Pattern-matching" should "support patterns for RSS Theorem 5" in {
    val ante = immutable.IndexedSeq[Formula](
      "(A()>=0&b()>0&ep()>0&V()>0)&v_0=0&(x_0-xo_0)^2-(y_0-yo_0)^2>0&dx_0^2+dy_0^2=1".asFormula,
      "v_1>=0&dx_1^2+dy_1^2=1&(v_1>0->abs(x_1-xo_1)>v_1^2/(2*b())+V()*(v_1/b())|abs(y_1-yo_1)>v_1^2/(2*b())+V()*(v_1/b()))".asFormula,
      "vxo^2+vyo^2<=V()^2".asFormula,
      "-b()<=a&a<=A()".asFormula,
      "-W()<=w_0&w_0<=W()".asFormula,
      "r!=0&r*w_0=v_1".asFormula,
      "v_1+a*ep()>=0".asFormula,
      "abs(x_1-xo_2)>v_1^2/(2*b())+V()*v_1/b()+(a/b()+1)*(a/2*ep()^2+ep()*(v_1+V()))|abs(y_1-yo_2)>v_1^2/(2*b())+V()*v_1/b()+(a/b()+1)*(a/2*ep()^2+ep()*(v_1+V()))".asFormula,
      "t_0=0".asFormula,
      "t>=0".asFormula,
      "dx^2+dy^2=1".asFormula,
      "-t*V()<=xo-xo_2&xo-xo_2<=t*V()".asFormula,
      "-t*V()<=yo-yo_2&yo-yo_2<=t*V()".asFormula,
      "v=v_1+a*t".asFormula,
      "-t*(v-a/2*t)<=x-x_1&x-x_1<=t*(v-a/2*t)".asFormula,
      "-t*(v-a/2*t)<=y-y_1&y-y_1<=t*(v-a/2*t)".asFormula,
      "v>=0&t<=ep()".asFormula)

    def asBV(s: String): BaseVariable = s.asVariable.asInstanceOf[BaseVariable]

    val c: Context = Context(Map(
      "assms".asVariable -> AntePosition(1),
      "J".asVariable -> AntePosition(2),
      "safeObs".asVariable -> AntePosition(3),
      "aGood".asVariable -> AntePosition(4),
      "wGood".asVariable -> AntePosition(5),
      "goodCurve".asVariable -> AntePosition(6),
      "alrightCurve".asVariable -> AntePosition(7),
      "greatCurve".asVariable -> AntePosition(8),
      "tPos".asVariable -> AntePosition(10),
      "wfDir".asVariable -> AntePosition(11),
      "xoBound".asVariable -> AntePosition(12),
      "yoBound".asVariable -> AntePosition(13),
      "vBound".asVariable -> AntePosition(14),
      "xBound".asVariable -> AntePosition(15),
      "yBound".asVariable -> AntePosition(16),
      "dC".asVariable -> AntePosition(17)
    ), Map(), Map("WFDIR" -> ("t", "t{dx^2+dy^2=1}".asFormula), "SD" -> ("t", "t(v^2/(2*b())+V()*(v/b()))".asTerm)))

    val p1 = "assm(J)".asExpr
    val p2 = "assm(greatCurve)".asExpr
    val p3 = "union(assm(J), assm(greatCurve))".asExpr
    val p4 = "neg(union(assm(J), assm(greatCurve)))".asExpr

    val e1 = "v_1>=0&dx_1^2+dy_1^2=1&(v_1>0->abs(x_1-xo_1)>v_1^2/(2*b())+V()*(v_1/b())|abs(y_1-yo_1)>v_1^2/(2*b())+V()*(v_1/b()))".asExpr
    val e2 = "abs(x_1-xo_2)>v_1^2/(2*b())+V()*v_1/b()+(a/b()+1)*(a/2*ep()^2+ep()*(v_1+V()))|abs(y_1-yo_2)>v_1^2/(2*b())+V()*v_1/b()+(a/b()+1)*(a/2*ep()^2+ep()*(v_1+V()))".asFormula
    val e3 = "t>=0".asFormula

    val dm1a = doesMatch(p1, e1, c, ante)
    val dm1b = doesMatch(p1, e2, c, ante)
    val dm1c = doesMatch(p1, e3, c, ante)

    val dm2a = doesMatch(p2, e1, c, ante)
    val dm2b = doesMatch(p2, e2, c, ante)
    val dm2c = doesMatch(p2, e3, c, ante)

    val dm3a = doesMatch(p3, e1, c, ante)
    val dm3b = doesMatch(p3, e2, c, ante)
    val dm3c = doesMatch(p3, e3, c, ante)

    val dm4a = doesMatch(p4, e1, c, ante)
    val dm4b = doesMatch(p4, e2, c, ante)
    val dm4c = doesMatch(p4, e3, c, ante)

    dm1a shouldBe true
    dm1b shouldBe false
    dm1c shouldBe false

    dm2a shouldBe false
    dm2b shouldBe true
    dm2c shouldBe false

    dm3a shouldBe true
    dm3b shouldBe true
    dm3c shouldBe false

    dm4a shouldBe false
    dm4b shouldBe false
    dm4c shouldBe true

  }

  "RSS Theorem 5 branch 3/4 arithmetic goal" should "prove" in {
    withMathematica(qeTool => {
      val seq: Sequent = Sequent(immutable.IndexedSeq[Formula](
        "(A()>=0&b()>0&ep()>0&V()>0)&v_0=0&(x_0-xo_0)^2-(y_0-yo_0)^2>0&dx_0^2+dy_0^2=1".asFormula,
        "v_1>=0&dx_1^2+dy_1^2=1&(v_1>0->abs(x_1-xo_1)>v_1^2/(2*b())+V()*(v_1/b())|abs(y_1-yo_1)>v_1^2/(2*b())+V()*(v_1/b()))".asFormula,
        "vxo^2+vyo^2<=V()^2".asFormula,
        "-b()<=a&a<=A()".asFormula,
        "-W()<=w_0&w_0<=W()".asFormula,
        "r!=0&r*w_0=v_1".asFormula,
        "v_1+a*ep()>=0".asFormula,
        "abs(x_1-xo_2)>v_1^2/(2*b())+V()*v_1/b()+(a/b()+1)*(a/2*ep()^2+ep()*(v_1+V()))|abs(y_1-yo_2)>v_1^2/(2*b())+V()*v_1/b()+(a/b()+1)*(a/2*ep()^2+ep()*(v_1+V()))".asFormula,
        "t_0=0".asFormula,
        "t>=0".asFormula,
        "dx^2+dy^2=1".asFormula,
        "-t*V()<=xo-xo_2&xo-xo_2<=t*V()".asFormula,
        "-t*V()<=yo-yo_2&yo-yo_2<=t*V()".asFormula,
        "v=v_1+a*t".asFormula,
        "-t*(v-a/2*t)<=x-x_1&x-x_1<=t*(v-a/2*t)".asFormula,
        "-t*(v-a/2*t)<=y-y_1&y-y_1<=t*(v-a/2*t)".asFormula,
        "v>=0&t<=ep()".asFormula)
        ,
        immutable.IndexedSeq[Formula]("v>=0&dx^2+dy^2=1&(v>0->abs(x-xo)>v^2/(2*b())+V()*(v/b())|abs(y-yo)>v^2/(2*b())+V()*(v/b()))".asFormula))

      def asBV(s: String): BaseVariable = s.asVariable.asInstanceOf[BaseVariable]

      val h: History = History(List(HCRename(asBV("w"), asBV("w_2"), None), HCRename(asBV("t"), asBV("t_2"), None), HCRename(asBV("x"), asBV("x_1"), None), HCRename(asBV("dx"), asBV("dx_1"), None), HCRename(asBV("yo"), asBV("yo_2"), None), HCRename(asBV("v"), asBV("v_1"), None), HCRename(asBV("y"), asBV("y_1"), None), HCRename(asBV("xo"), asBV("xo_2"), None), HCRename(asBV("dy"), asBV("dy_1"), None), HCTimeStep("safeCurve"), HCRename(asBV("t"), asBV("t_1"), Some(AntePos(8))), HCRename(asBV("yo"), asBV("yo_1"), None), HCRename(asBV("xo"), asBV("xo_1"), None), HCRename(asBV("r"), asBV("r_1"), None), HCRename(asBV("w"), asBV("w_1"), None), HCRename(asBV("a"), asBV("a_1"), None), HCRename(asBV("vyo"), asBV("vyo_1"), None), HCRename(asBV("vxo"), asBV("vxo_1"), None), HCTimeStep("loop"), HCRename(asBV("vxo"), asBV("vxo_0"), None), HCRename(asBV("w"), asBV("w_0"), None), HCRename(asBV("t"), asBV("t_0"), None), HCRename(asBV("x"), asBV("x_0"), None), HCRename(asBV("vyo"), asBV("vyo_0"), None), HCRename(asBV("dx"), asBV("dx_0"), None), HCRename(asBV("yo"), asBV("yo_0"), None), HCRename(asBV("a"), asBV("a_0"), None), HCRename(asBV("v"), asBV("v_0"), None), HCRename(asBV("y"), asBV("y_0"), None), HCRename(asBV("xo"), asBV("xo_0"), None), HCRename(asBV("r"), asBV("r_0"), None), HCRename(asBV("dy"), asBV("dy_0"), None), HCTimeStep("init")))
      val c: Context = Context(Map(
        "assms".asVariable -> AntePosition(1),
        "J".asVariable -> AntePosition(2),
        "safeObs".asVariable -> AntePosition(3),
        "aGood".asVariable -> AntePosition(4),
        "wGood".asVariable -> AntePosition(5),
        "goodCurve".asVariable -> AntePosition(6),
        "alrightCurve".asVariable -> AntePosition(7),
        "greatCurve".asVariable -> AntePosition(8),
        "tPos".asVariable -> AntePosition(10),
        "wfDir".asVariable -> AntePosition(11),
        "xoBound".asVariable -> AntePosition(12),
        "yoBound".asVariable -> AntePosition(13),
        "vBound".asVariable -> AntePosition(14),
        "xBound".asVariable -> AntePosition(15),
        "yBound".asVariable -> AntePosition(16),
        "dC".asVariable -> AntePosition(17)
      ), Map(), Map("WFDIR" -> ("t", "t{dx^2+dy^2=1}".asFormula), "SD" -> ("t", "t(v^2/(2*b())+V()*(v/b()))".asTerm)))
      val sp: SP =
        BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
          duh
          ,
          BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
            duh,
            BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
              BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(x-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(y-yo)) > wild()".asFormula), List(
                Have("dxep".asVariable, "abs(safeCurve(x-xo)) > (safeCurve(v)^2 / (2*b()) + V()*safeCurve(v)/b()) + (a/b()+1)*(a/2*t^2 + t*(safeCurve(v) +V()))".asFormula, duh,
                  BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                    Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))
                , Have("dyep".asVariable, "abs(safeCurve(y-yo)) > (safeCurve(v)^2 / (2*b()) + V()*safeCurve(v)/b()) + (a/b()+1)*(a/2*t^2 + t*(safeCurve(v) +V()))".asFormula, duh,
                  BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                    Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))))))
          ))))

      val time = System.currentTimeMillis()
      Kaisar.eval(sp, h, c, Provable.startProof(seq)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }


  "RSS Theorem 7 branch 3 arith" should "prove" in {
    withMathematica(qeTool => {
      val seq = Sequent(
        immutable.IndexedSeq[Formula](
          "(A()>=0&b()>0&ep()>0&V()>0&Dp()>0)&v_0=0&(x_0-xo_0)^2-(y_0-yo_0)^2>0&dx_0^2+dy_0^2=1".asFormula,
          "v_1>=0&dx_1^2+dy_1^2=1&(v_1>0->abs(x_1-xo_1)>v_1^2/(2*b())+V()*(v_1/b())|abs(y_1-yo_1)>v_1^2/(2*b())+V()*(v_1/b()))".asFormula,
          "(mx-x_1)^2+(my-y_1)^2<=Dp()^2".asFormula,
          "vxo^2+vyo^2<=V()^2".asFormula,
          "-W()<=w_0&w_0<=W()".asFormula,
          "r!=0&r*w_0=v_1".asFormula,
          "abs(mx-xo_2)>v_1^2/(2*b())+V()*v_1/b()+((A()/b()+1)*(A()/2*ep()^2+ep()*(v_1+V()))+Dp())|abs(my-yo_2)>v_1^2/(2*b())+V()*v_1/b()+((A()/b()+1)*(A()/2*ep()^2+ep()*(v_1+V()))+Dp())".asFormula,
          "t_0=0".asFormula,
          "t>=0".asFormula,
          "dx^2+dy^2=1".asFormula,
          "-t*V()<=xo-xo_2&xo-xo_2<=t*V()".asFormula,
          "-t*V()<=yo-yo_2&yo-yo_2<=t*V()".asFormula,
          "v=v_1+A()*t".asFormula,
          "-t*(v-A()/2*t)<=x-x_1&x-x_1<=t*(v-A()/2*t)".asFormula,
          "-t*(v-A()/2*t)<=y-y_1&y-y_1<=t*(v-A()/2*t)".asFormula,
          "v>=0&t<=ep()".asFormula
        ),
        immutable.IndexedSeq[Formula]("v>=0&dx^2+dy^2=1&(v>0->abs(x-xo)>v^2/(2*b())+V()*(v/b())|abs(y-yo)>v^2/(2*b())+V()*(v/b()))".asFormula)
      )

      def asBV(s: String): BaseVariable = s.asVariable.asInstanceOf[BaseVariable]

      val c = Context(Map(
        "safeObs".asVariable -> AntePosition(4),
        "yBound".asVariable -> AntePosition(15),
        "uncertain".asVariable -> AntePosition(3),
        "xoBound".asVariable -> AntePosition(11),
        "xBound".asVariable -> AntePosition(14),
        "wfDir".asVariable -> AntePosition(10), "yoBound".asVariable -> AntePosition(12), "vBound".asVariable -> AntePosition(13), "goodCurve".asVariable -> AntePosition(6), "assms".asVariable -> AntePosition(1), "greatCurve".asVariable -> AntePosition(7), "J".asVariable -> AntePosition(2), "dC".asVariable -> AntePosition(16), "tPos".asVariable -> AntePosition(9), "wGood".asVariable -> AntePosition(5)), Map(), Map("WFDIR" -> ("t", "t{dx^2+dy^2=1}".asFormula), "SD" -> ("t", "t(v^2/(2*b())+V()*(v/b()))".asTerm), "ASEP" -> ("t", "t(v^2/(2*b())+V()*(v/b())+((A()/b()+1)*(A()/2*ep()^2+ep()*(v+V()))+Dp()))".asTerm)))
      val h = History(List(HCRename(asBV("y"), asBV("y_1"), None), HCRename(asBV("dx"), asBV("dx_1"), None), HCRename(asBV("t"), asBV("t_2"), None), HCRename(asBV("xo"), asBV("xo_2"), None), HCRename(asBV("dy"), asBV("dy_1"), None), HCRename(asBV("x"), asBV("x_1"), None), HCRename(asBV("v"), asBV("v_1"), None), HCRename(asBV("yo"), asBV("yo_2"), None), HCRename(asBV("w"), asBV("w_2"), None), HCTimeStep("safeCurve"), HCRename(asBV("t"), asBV("t_1"), Some(AntePos(-7))), HCRename(asBV("yo"), asBV("yo_1"), None), HCRename(asBV("xo"), asBV("xo_1"), None), HCRename(asBV("r"), asBV("r_1"), None), HCRename(asBV("w"), asBV("w_1"), None), HCAssign(Assign(asBV("a"), "A()".asTerm)), HCRename(asBV("vyo"), asBV("vyo_1"), None), HCRename(asBV("vxo"), asBV("vxo_1"), None), HCRename(asBV("my"), asBV("my_1"), None), HCRename(asBV("mx"), asBV("mx_1"), None), HCTimeStep("loop"), HCRename(asBV("y"), asBV("y_0"), None), HCRename(asBV("dx"), asBV("dx_0"), None), HCRename(asBV("t"), asBV("t_0"), None), HCRename(asBV("a"), asBV("a_0"), None), HCRename(asBV("xo"), asBV("xo_0"), None), HCRename(asBV("vyo"), asBV("vyo_0"), None), HCRename(asBV("dy"), asBV("dy_0"), None), HCRename(asBV("x"), asBV("x_0"), None), HCRename(asBV("v"), asBV("v_0"), None), HCRename(asBV("my"), asBV("my_0"), None), HCRename(asBV("yo"), asBV("yo_0"), None), HCRename(asBV("w"), asBV("w_0"), None), HCRename(asBV("r"), asBV("r_0"), None), HCRename(asBV("mx"), asBV("mx_0"), None), HCRename(asBV("vxo"), asBV("vxo_0"), None), HCTimeStep("init")))
      val sp = BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
        duh
        ,
        BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
          duh,
          BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
            BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(mx-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(my-yo)) > wild()".asFormula), List(
              Have("dxep".asVariable, "abs(safeCurve(mx)-safeCurve(xo))>safeCurve(v)^2/(2*b())+V()*safeCurve(v)/b()+(A()/b()+1)*(A()/2*t^2+t*(safeCurve(v)+V()))+ Dp()".asFormula,
                Show("wild()".asFormula, UP(List(Left("neg(union(union(assm(xBound),assm(J)),union(assm(yBound),assm(wfDir))))".asExpr)), Kaisar.RCF())),
                BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                  Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))
              , Have("dyep".asVariable, "abs(safeCurve(my)-safeCurve(yo))>safeCurve(v)^2/(2*b())+V()*safeCurve(v)/b()+(A()/b()+1)*(A()/2*t^2+t*(safeCurve(v)+V()))+ Dp()".asFormula,
                Show("wild()".asFormula, UP(List(Left("neg(union(union(assm(xBound),assm(J)),union(assm(yBound),assm(wfDir))))".asExpr)), Kaisar.RCF())),
                BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                  Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))))))
        ))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, h, c, Provable.startProof(seq)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }
  // Kaisar port of RSS robotics case study
  "RSS Passive Safety with Position Uncertainty" should "prove" in {
    withMathematica(qeTool => {
      // Theorem 1
      val b = "b()".asTerm
      val A = "A()".asTerm
      val ep = "ep()".asTerm
      val v = "v".asVariable
      val V = "V()".asTerm
      val Dp = "Dp()".asTerm

      def stopDist(e: Term): Term = Plus(Divide(Power(e, Number(2)), Times(Number(2), b)), Times(V, Divide(e, b)))

      def accelComp(e: Term): Term = Plus(Times(Plus(Divide(A, b), Number(1)), Plus(Times(Divide(A, Number(2)), Power(ep, Number(2))), Times(ep, Plus(e, V)))), Dp)

      def admissibleSeparation(e: Term): Term = Plus(stopDist(e), accelComp(e))

      val isWellformedDir = "dx^2 + dy^2 = 1".asFormula
      val bounds = And(GreaterEqual(A, Number(0)), And(Greater(b, Number(0)), And(Greater(ep, Number(0)), And(Greater(V, Number(0)), Greater(Dp, Number(0))))))
      val initialState = And("v=0".asFormula, And("(x-xo)^2 - (y-yo)^2 > 0".asFormula, isWellformedDir))
      val assumptions = And(bounds, initialState)
      val loopinv = And("v >= 0".asFormula, And(isWellformedDir, Imply(Greater(v, Number(0)), Or(Greater("abs(x-xo)".asTerm, stopDist(v)), Greater("abs(y-yo)".asTerm, stopDist(v))))))
      val acclCtrl: Program =
        """a :=A();
         w := *; ?(-W()<=w & w<=W());       /* choose steering */
           r := *; xo := *; yo := *;            /* measure closest obstacle on the curve */
           /* admissible curve */
           ?r!=0 & r*w = v;
          ? (abs(mx-xo) > (v^2 / (2*b()) + V()*v/b()) + ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V())) + Dp())
           | abs(my-yo) > (v^2 / (2*b()) + V()*v/b()) + ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V())) + Dp()));

       """.asProgram
      val obsCtrl: Program = "mx:=*;my:=*;?((mx-x)^2+(my-y)^2<=Dp()^2);vxo:=*;vyo:=*;?(vxo^2+vyo^2<=V()^2);".asProgram
      val robCtrl: Program = Compose(Choice(
        "a:=-b();".asProgram, Choice(
          "?v=0; a:=0; w:=0;".asProgram, acclCtrl)),
        "t:=0;".asProgram)
      val plant: Program =
        """ { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
          dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
          xo' = vxo, yo' = vyo,
          t' = 1 & t <= ep() & v >= 0
          }""".asProgram
      val ctrl = Compose(obsCtrl, robCtrl)
      val theorem5: Formula = Imply(assumptions, Box(Loop(Compose(ctrl, plant)), "v>0 -> ((x-xo)^2 + (y-yo)^2 > 0)".asFormula))


      val sp: SP =
        FLet("WFDIR", "t", PredicationalOf(Function("t", None, Bool, Bool), isWellformedDir),
          FLet("SD", "t", FuncOf(Function("t", None, Real, Real), stopDist("v".asVariable)),
            FLet("ASEP", "t", FuncOf(Function("t", None, Real, Real), Plus(stopDist("v".asVariable), accelComp("v".asVariable))),
              BRule(RBAssume("assms".asVariable, "wild()".asFormula), List(
                BRule(RBInv(Inv("J".asVariable, "(v >= 0 & WFDIR() & (v> 0 -> (abs(x-xo) > SD() | abs(y-yo) > SD() )))".asFormula, duh,
                  State("loop",
                    BRule(RBAssignAny("mx".asVariable), List(
                      BRule(RBAssignAny("my".asVariable), List(
                        BRule(RBAssume("uncertain".asVariable, "(mx-x)^2+(my-y)^2 <= Dp()^2".asFormula), List(
                          BRule(RBAssignAny("vxo".asVariable), List(
                            BRule(RBAssignAny("vyo".asVariable), List(
                              BRule(RBAssume("safeObs".asVariable, "vxo^2+vyo^2<=V()^2".asFormula), List(
                                BRule(RBCase(List("a := -b();".asProgram, "{wild} ++ {wild}".asProgram)), List(
                                  // braking
                                  BRule(RBAssign(Assign("a".asVariable, "-b()".asTerm)), List(
                                    BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                      BRule(RBInv(
                                        Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                          Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                            Inv("vBound".asVariable, "v = loop(v)-b()*t".asFormula, duh, duh,
                                              Inv("xoBound".asVariable, "-t*V() <= xo - loop(xo) & xo - loop(xo) <= t*V()".asFormula, duh, duh,
                                                Inv("yoBound".asVariable, "-t*V() <= yo - loop(yo) & yo - loop(yo) <= t*V()".asFormula, duh, duh,
                                                  Inv("xBound".asVariable, "-t * (v + b()/2*t) <= x - loop(x) & x - loop(x) <= t * (v + b()/2*t)".asFormula, duh, duh,
                                                    Inv("yBound".asVariable, "-t * (v + b()/2*t) <= y - loop(y) & y - loop(y) <= t * (v + b()/2*t)".asFormula, duh, duh,
                                                      Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                        Finally(PrintGoal("End first branch",
                                                          Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))))))))))), List())))))
                                  , // stopped + accel
                                  PrintGoal("Beginning second branch",
                                    BRule(RBCase(List("?v=0; a:=0; w:=0;".asProgram, "{a :=A();{wild}}".asProgram)), List(
                                      // stopped
                                      BRule(RBAssume("stopped".asVariable, "v=0".asFormula), List(
                                        BRule(RBAssign(Assign("a".asVariable, "0".asTerm)), List(
                                          BRule(RBAssign(Assign("w".asVariable, "0".asTerm)), List(
                                            BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                              PrintGoal("Beginning second inv",
                                                BRule(RBInv(
                                                  Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                                    Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                      Inv("xoBound".asVariable, "-t*V() <= xo - loop(xo) & xo - loop(xo) <= t*V()".asFormula, duh, duh,
                                                        Inv("yoBound".asVariable, "-t*V() <= yo - loop(yo) & yo - loop(yo) <= t*V()".asFormula, duh, duh,
                                                          Inv("vEq".asVariable, "v = loop(v)".asFormula, duh, duh,
                                                            Inv("xEq".asVariable, "x = loop(x)".asFormula, duh, duh,
                                                              Inv("yEq".asVariable, "y = loop(y)".asFormula, duh, duh,
                                                                Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                                  Finally(
                                                                    PrintGoal("End of second branch",
                                                                      Show("wild()".asFormula, UP(List(), Kaisar.RCF()))) /*)*/)))))))))), List())))))))))),
                                      //Free Driving cases
                                      PrintGoal("Beginning third branch",
                                        BRule(RBAssign("a:=A();".asProgram.asInstanceOf[Assign]), List(
                                          BRule(RBAssignAny("w".asVariable), List(
                                            BRule(RBAssume("wGood".asVariable, "-W()<=w & w<=W()".asFormula), List(
                                              BRule(RBAssignAny("r".asVariable), List(
                                                BRule(RBAssignAny("xo".asVariable), List(
                                                  BRule(RBAssignAny("yo".asVariable), List(
                                                    BRule(RBAssume("goodCurve".asVariable, "r!=0 & r*w=v".asFormula), List(
                                                      PrintGoal("Beginning thirdbranching",
                                                        BRule(RBAssume("greatCurve".asVariable, "abs(mx-xo) > (v^2 / (2*b()) + V()*v/b()) + ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V())) + Dp()) | abs(my-yo) > (v^2 / (2*b()) + V()*v/b()) + ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V())) + Dp())".asFormula), List(
                                                          BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                                            State("safeCurve",
                                                              PrintGoal("Beginning third invs",
                                                                BRule(RBInv(
                                                                  Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                                                    Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                                      Inv("xoBound".asVariable, "-t*V() <= xo - safeCurve(xo) & xo - safeCurve(xo) <= t*V()".asFormula, duh, duh,
                                                                        Inv("yoBound".asVariable, "-t*V() <= yo - safeCurve(yo) & yo - safeCurve(yo) <= t*V()".asFormula, duh, duh,
                                                                          Inv("vBound".asVariable, "v = loop(v) + A()*t".asFormula, duh, duh,
                                                                            Inv("xBound".asVariable, "-t * (v - A()/2*t) <= x - loop(x) & x - loop(x) <= t * (v - A()/2*t)".asFormula, duh, duh,
                                                                              Inv("yBound".asVariable, "-t * (v - A()/2*t) <= y - loop(y) & y - loop(y) <= t * (v - A()/2*t)".asFormula, duh, duh,
                                                                                Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                                                  Finally(
                                                                                    PrintGoal("End third goal",
                                                                                      BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
                                                                                        duh
                                                                                        ,
                                                                                        BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
                                                                                          duh,
                                                                                          BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
                                                                                            BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(mx-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(my-yo)) > wild()".asFormula), List(
                                                                                              Have("dxep".asVariable, "abs(safeCurve(mx)-safeCurve(xo))>safeCurve(v)^2/(2*b())+V()*safeCurve(v)/b()+(A()/b()+1)*(A()/2*t^2+t*(safeCurve(v)+V()))+ Dp()".asFormula,
                                                                                                Show("wild()".asFormula, UP(List(Left("neg(union(union(assm(xBound),assm(J)),union(assm(yBound),assm(wfDir))))".asExpr)), Kaisar.RCF())),
                                                                                                BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                                                  Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))
                                                                                              , Have("dyep".asVariable, "abs(safeCurve(my)-safeCurve(yo))>safeCurve(v)^2/(2*b())+V()*safeCurve(v)/b()+(A()/b()+1)*(A()/2*t^2+t*(safeCurve(v)+V()))+ Dp()".asFormula,
                                                                                                Show("wild()".asFormula, UP(List(Left("neg(union(union(assm(xBound),assm(J)),union(assm(yBound),assm(wfDir))))".asExpr)), Kaisar.RCF())),
                                                                                                BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                                                  Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))))))
                                                                                        ))))
                                                                                    ))))))))))), List())))))))))

                                                    ))))))))))))))))))))))))))))))))
                  , Finally(Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))), List()))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(theorem5)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }


  "RSS Passive Safety with Actuator uncertainty" should "prove" in {
    withMathematica(qeTool => {
      // Theorem 1
      val b = "b()".asTerm
      val A = "A()".asTerm
      val ep = "ep()".asTerm
      val v = "v".asVariable
      val V = "V()".asTerm
      val Da = "Da()".asTerm

      def stopDist(e: Term): Term = Plus(Divide(Power(e, Number(2)), Times(Number(2), Times(b, Da))), Divide(Times(V, e), Times(b, Da)))

      def accelComp(e: Term): Term = Times(Plus(Divide(A, Times(b, Da)), Number(1)), Plus(Times(Divide(A, Number(2)), Power(ep, Number(2))), Times(ep, Plus(e, V))))

      def admissibleSeparation(e: Term): Term = Plus(stopDist(e), accelComp(e))

      val isWellformedDir = "dx^2 + dy^2 = 1".asFormula
      val bounds = And(GreaterEqual(A, Number(0)), And(Greater(b, Number(0)), And(Greater(ep, Number(0)), And(Greater(V, Number(0)), And(Less(Number(0), Da), LessEqual(Da, Number(1)))))))
      val initialState = And("v=0".asFormula, And("(x-xo)^2 - (y-yo)^2 > 0".asFormula, isWellformedDir))
      val assumptions = And(bounds, initialState)
      val loopinv = And("v >= 0".asFormula, And(isWellformedDir, Imply(Greater(v, Number(0)), Or(Greater("abs(x-xo)".asTerm, stopDist(v)), Greater("abs(y-yo)".asTerm, stopDist(v))))))
      val acclCtrl: Program =
        """a :=A();
         w := *; ?(-W()<=w & w<=W());       /* choose steering */
           r := *; xo := *; yo := *;            /* measure closest obstacle on the curve */
           /* admissible curve */
           ?r!=0 & r*w = v;
          ? (abs(x-xo) > ( v^2 / (2*(b()*Da())) + V()*v/(b()*Da()) ) + ( (A()/(b()*Da()) + 1) * (A()/2 * ep()^2 + ep()*(v+V())))
           | abs(y-yo) > ( v^2 / (2*(b()*Da())) + V()*v/(b()*Da()) ) + ( (A()/(b()*Da()) + 1) * (A()/2 * ep()^2 + ep()*(v+V()))));
       """.asProgram
      val obsCtrl: Program = "vxo:=*;vyo:=*;?(vxo^2+vyo^2<=V()^2);".asProgram
      val robCtrl: Program = Compose(Choice(
        "a:=-b();".asProgram, Choice(
          "?v=0; a:=0; w:=0;".asProgram,
          acclCtrl)),
        "da :=*; ?(Da() <= da & da <= 1); acc := da*a;t:=0;".asProgram)
      val plant: Program =
        """ { x' = v * dx, y' = v * dy, v' = acc,        /* accelerate/decelerate and move */
          dx' = -w * dy, dy' = w * dx, w' = acc/r,   /* follow curve */
          xo' = vxo, yo' = vyo,
          t' = 1 & t <= ep() & v >= 0
          }""".asProgram
      val ctrl = Compose(obsCtrl, robCtrl)
      val theorem77: Formula = Imply(assumptions, Box(Loop(Compose(ctrl, plant)), "v>0 -> ((x-xo)^2 + (y-yo)^2 > 0)".asFormula))
      val sp: SP =
        FLet("WFDIR", "t", PredicationalOf(Function("t", None, Bool, Bool), isWellformedDir),
          FLet("SD", "t", FuncOf(Function("t", None, Real, Real), stopDist("v".asVariable)),
            FLet("ASEP", "t", FuncOf(Function("t", None, Real, Real), Plus(stopDist("v".asVariable), accelComp("v".asVariable))),
              BRule(RBAssume("assms".asVariable, "wild()".asFormula), List(
                BRule(RBInv(Inv("J".asVariable, "(v >= 0 & WFDIR() & (v> 0 -> (abs(x-xo) > SD() | abs(y-yo) > SD() )))".asFormula, duh,
                  State("loop",
                    BRule(RBAssignAny("vxo".asVariable), List(
                      BRule(RBAssignAny("vyo".asVariable), List(
                        BRule(RBAssume("safeObs".asVariable, "vxo^2+vyo^2<=V()^2".asFormula), List(
                          BRule(RBCase(List("a := -b();".asProgram, "{wild} ++ {wild}".asProgram)), List(
                            // braking
                            BRule(RBAssign(Assign("a".asVariable, "-b()".asTerm)), List(
                              BRule(RBAssignAny("da".asVariable), List(
                                BRule(RBAssume("perturb".asVariable, "Da()<=da & da<=1".asFormula), List(
                                  BRule(RBAssign(Assign("acc".asVariable, "da*a".asTerm)), List(
                                    BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                      BRule(RBInv(
                                        Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                          Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                            Inv("xoBound".asVariable, "-t*V() <= xo - loop(xo) & xo - loop(xo) <= t*V()".asFormula, duh, duh,
                                              Inv("yoBound".asVariable, "-t*V() <= yo - loop(yo) & yo - loop(yo) <= t*V()".asFormula, duh, duh,
                                                Inv("vBound".asVariable, "v <= loop(v)- (b()*Da())*t".asFormula, duh, duh,
                                                  Inv("xBound".asVariable, "-t * (loop(v) - (b()*Da())/2*t) <= x - loop(x) & x - loop(x) <= t * (loop(v) - (b()*Da())/2*t)".asFormula, duh, duh,
                                                    Inv("yBound".asVariable, "-t * (loop(v) - (b()*Da())/2*t) <= y - loop(y) & y - loop(y) <= t * (loop(v) - (b()*Da())/2*t)".asFormula, duh, duh,
                                                      Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                        Finally(PrintGoal("End first branch",

                                                          BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
                                                            Show("wild()".asFormula, UP(List(Left("assm(dC)".asExpr)), Kaisar.RCF()))
                                                            ,
                                                            BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
                                                              Show("wild()".asFormula, UP(List(), CloseId())),
                                                              BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
                                                                Have("imp".asVariable, "loop{v> 0 -> (abs(x-xo) > SD_() | abs(y-yo) > SD_())}".asFormula,
                                                                  Show("wild()".asFormula, UP(List(Left("assm(J)".asExpr)), Kaisar.RCF()))
                                                                  ,
                                                                  BRule(RBAbbrev("actBEq".asVariable, "actB".asVariable, "b()*Da()".asTerm), List(
                                                                    Have("actBPos".asVariable, "actB>0".asFormula, Show("wild()".asFormula, UP(List(Left("assm(assms)".asExpr), Left("assm(actBEq)".asExpr)), Kaisar.RCF())),

                                                                      BRule(RBCaseImplyL("oldVPos".asVariable, "loop(v)>0 ".asFormula, "disj".asVariable, "wild()".asFormula), List(
                                                                        Show("loop(v)>0".asFormula, UP(List(), Kaisar.SmartQE())),
                                                                        BRule(RBCaseOrL("xxo".asVariable, "loop(abs(x-xo)) > wild()".asFormula, "yyo".asVariable, "loop(abs(y-yo)) > wild()".asFormula), List(
                                                                          PrintGoal("SG1",
                                                                            BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                              Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE()))))
                                                                          ),
                                                                          PrintGoal("SG2",
                                                                            BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                              Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))))))))))))))))

                                                        ))))))))))), List())))))))))))
                            , // stopped + accel
                            PrintGoal("Beginning second branch",
                              BRule(RBCase(List("?v=0; a:=0; w:=0;".asProgram, "{a :=A();{wild}}".asProgram)), List(
                                // stopped
                                BRule(RBAssume("stopped".asVariable, "v=0".asFormula), List(
                                  BRule(RBAssign(Assign("a".asVariable, "0".asTerm)), List(
                                    BRule(RBAssign(Assign("w".asVariable, "0".asTerm)), List(
                                      BRule(RBAssignAny("da".asVariable), List(
                                        BRule(RBAssume("perturb".asVariable, "Da()<=da & da<=1".asFormula), List(
                                          BRule(RBAssign(Assign("acc".asVariable, "da*a".asTerm)), List(
                                            BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                              PrintGoal("Beginning second inv",
                                                BRule(RBInv(
                                                  Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                                    Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                      Inv("xoBound".asVariable, "-t*V() <= xo - loop(xo) & xo - loop(xo) <= t*V()".asFormula, duh, duh,
                                                        Inv("yoBound".asVariable, "-t*V() <= yo - loop(yo) & yo - loop(yo) <= t*V()".asFormula, duh, duh,
                                                          Inv("vEq".asVariable, "v = loop(v)".asFormula, duh, duh,
                                                            Inv("xEq".asVariable, "x = loop(x)".asFormula, duh, duh,
                                                              Inv("yEq".asVariable, "y = loop(y)".asFormula, duh, duh,
                                                                Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                                  Finally(
                                                                    PrintGoal("End of second branch",
                                                                      Show("wild()".asFormula, UP(List(), Kaisar.SmartQE()))) /*)*/)))))))))), List())))))))))))))))),
                                //Free Driving cases
                                PrintGoal("Beginning third branch",
                                  BRule(RBAssign("a:=A();".asProgram.asInstanceOf[Assign]), List(
                                    BRule(RBAssignAny("w".asVariable), List(
                                      BRule(RBAssume("wGood".asVariable, "-W()<=w & w<=W()".asFormula), List(
                                        BRule(RBAssignAny("r".asVariable), List(
                                          BRule(RBAssignAny("xo".asVariable), List(
                                            BRule(RBAssignAny("yo".asVariable), List(
                                              BRule(RBAssume("goodCurve".asVariable, "r!=0 & r*w=v".asFormula), List(
                                                PrintGoal("Beginning thirdbranching",
                                                  // TODO: update this assumption
                                                  BRule(RBAssume("greatCurve".asVariable, "abs(x-xo) > (v^2/(2*(b()*Da())) + V()*v/(b()*Da())) + ( (A()/(b()*Da()) + 1) * (A()/2 * ep()^2 + ep()*(v+V())) )\n| abs(y-yo) > (v^2/(2*(b()*Da())) + V()*v/(b()*Da())) + ( (A()/(b()*Da()) + 1) * (A()/2 * ep()^2 + ep()*(v+V())))".asFormula), List(
                                                    BRule(RBAssignAny("da".asVariable), List(
                                                      BRule(RBAssume("perturb".asVariable, "Da()<=da & da<=1".asFormula), List(
                                                        BRule(RBAssign(Assign("acc".asVariable, "da*a".asTerm)), List(
                                                          BRule(RBAssign(Assign("t".asVariable, "0".asTerm)), List(
                                                            State("safeCurve",
                                                              PrintGoal("Beginning third invs",
                                                                BRule(RBInv(
                                                                  Inv("tPos".asVariable, "t>=0".asFormula, duh, duh,
                                                                    Inv("wfDir".asVariable, "WFDIR()".asFormula, duh, duh,
                                                                      Inv("xoBound".asVariable, "-t*V() <= xo - safeCurve(xo) & xo - safeCurve(xo) <= t*V()".asFormula, duh, duh,
                                                                        Inv("yoBound".asVariable, "-t*V() <= yo - safeCurve(yo) & yo - safeCurve(yo) <= t*V()".asFormula, duh, duh,
                                                                          Inv("vBound".asVariable, "v <= loop(v) + A()*t".asFormula, duh, duh,
                                                                            Inv("xBound".asVariable, "-t * (loop(v) + A()/2*t) <= x - loop(x) & x - loop(x) <= t * (loop(v) + A()/2*t)".asFormula, duh, duh,
                                                                              Inv("yBound".asVariable, "-t * (loop(v) + A()/2*t) <= y - loop(y) & y - loop(y) <= t * (loop(v) + A()/2*t)".asFormula, duh, duh,
                                                                                Inv("dC".asVariable, "v >= 0 & t <= ep()".asFormula, duh, duh,
                                                                                  Finally(
                                                                                    PrintGoal("End third goal",
                                                                                      BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
                                                                                        duh
                                                                                        ,
                                                                                        BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
                                                                                          duh,
                                                                                          BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
                                                                                            BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(x-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(y-yo)) > wild()".asFormula), List(
                                                                                              Have("dxep".asVariable, "safeCurve(abs(x-xo))>safeCurve(v)^2/(2*(b()*Da()))+V()*safeCurve(v)/(b()*Da())+(A()/(b()*Da())+1)*(A()/2*t^2+t*(safeCurve(v)+V()))".asFormula,
                                                                                                Show("wild()".asFormula, UP(List(Left("assm(dC)".asExpr), Left("assm(greatCurve)".asExpr), Left("assm(assms)".asExpr), Left("assm(tPos)".asExpr), Left("assm(J)".asExpr)), Kaisar.RCF())),
                                                                                                PrintGoal("got through dxep",
                                                                                                  BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                                                    BRule(RBAbbrev("actBEq".asVariable, "actB".asVariable, "b()*Da()".asTerm), List(
                                                                                                      Have("actBPos".asVariable, "actB>0".asFormula, Show("actB>0".asFormula, UP(List(Left("union(assm(assms),assm(actBEq))".asExpr)), Kaisar.RCF())),
                                                                                                        Have("someAssms".asVariable, "A() >= 0 & V() > 0 & Da()<=1".asFormula, Show("wild()".asFormula, UP(List(Left("assm(assms)".asExpr), Left("assm(goodCurve)".asExpr)), Kaisar.Auto())),
                                                                                                          Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),union(assm(J),union(assm(yBound),union(assm(yoBound),union(assm(safeObs),union(assm(perturb),union(assm(wfDir),union(assm(assms),union(assm(goodCurve),union(assm(dC),assm(actBEq))))))))))))".asExpr)),
                                                                                                            Kaisar.SmartQE()))))))))))
                                                                                              ,
                                                                                              Have("dxep".asVariable, "safeCurve(abs(y-yo))>safeCurve(v)^2/(2*(b()*Da()))+V()*safeCurve(v)/(b()*Da())+(A()/(b()*Da())+1)*(A()/2*t^2+t*(safeCurve(v)+V()))".asFormula,
                                                                                                Show("wild()".asFormula, UP(List(Left("assm(dC)".asExpr), Left("assm(greatCurve)".asExpr), Left("assm(assms)".asExpr), Left("assm(tPos)".asExpr), Left("assm(J)".asExpr)), Kaisar.RCF())),
                                                                                                PrintGoal("got through dxep",
                                                                                                  BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                                                                                                    BRule(RBAbbrev("actBEq".asVariable, "actB".asVariable, "b()*Da()".asTerm), List(
                                                                                                      Have("actBPos".asVariable, "actB>0".asFormula, Show("actB>0".asFormula, UP(List(Left("union(assm(assms),assm(actBEq))".asExpr)), Kaisar.RCF())),
                                                                                                        Have("someAssms".asVariable, "A() >= 0 & V() > 0 & Da()<=1".asFormula, Show("wild()".asFormula, UP(List(Left("assm(assms)".asExpr), Left("assm(goodCurve)".asExpr)), Kaisar.Auto())),
                                                                                                          Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),union(assm(J),union(assm(xBound),union(assm(xoBound),union(assm(safeObs),union(assm(perturb),union(assm(wfDir),union(assm(assms),union(assm(goodCurve),union(assm(dC),assm(actBEq))))))))))))".asExpr)),
                                                                                                            Kaisar.SmartQE()))))))))))))))))))))))))))))), List())))))))))))))))))))))))))))))))))))))))))
                  , Finally(Show("wild()".asFormula, UP(List(), Kaisar.RCF()))))), List()))))))
      val time = System.currentTimeMillis()
      Kaisar.eval(sp, History.empty, Context.empty, Provable.startProof(theorem77)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }


  "ijrr thm 7 first arith" should "prove" in {
    withMathematica(qeTool => {
      val seq = Sequent(immutable.IndexedSeq[Formula](
        "(A()>=0&b()>0&ep()>0&V()>0&0 < Da()&Da()<=1)&v_0=0&(x_0-xo_0)^2-(y_0-yo_0)^2>0&dx_0^2+dy_0^2=1".asFormula,
        "v_1>=0&dx_1^2+dy_1^2=1&(v_1>0->abs(x_1-xo_1)>v_1^2/(2*(b()*Da()))+V()*v_1/(b()*Da())|abs(y_1-yo_1)>v_1^2/(2*(b()*Da()))+V()*v_1/(b()*Da()))".asFormula,
        "vxo^2+vyo^2<=V()^2".asFormula,
        "Da()<=da&da<=1".asFormula,
        "t_0=0".asFormula,
        "t>=0".asFormula,
        "dx^2+dy^2=1".asFormula,
        "-t*V()<=xo-xo_1&xo-xo_1<=t*V()".asFormula,
        "-t*V()<=yo-yo_1&yo-yo_1<=t*V()".asFormula,
        " v<=v_1-b()*Da()*t".asFormula,
        " -t*(v_1-b()*Da()/2*t)<=x-x_1&x-x_1<=t*(v_1-b()*Da()/2*t)".asFormula,
        " -t*(v_1-b()*Da()/2*t)<=y-y_1&y-y_1<=t*(v_1-b()*Da()/2*t)".asFormula,
        " v>=0&t<=ep()".asFormula)
        ,
        immutable.IndexedSeq[Formula]("v>=0&dx^2+dy^2=1&(v>0->abs(x-xo)>v^2/(2*(b()*Da()))+V()*v/(b()*Da())|abs(y-yo)>v^2/(2*(b()*Da()))+V()*v/(b()*Da()))".asFormula))

      def asBV(s: String): BaseVariable = s.asVariable.asInstanceOf[BaseVariable]

      val h = History(List(HCRename(asBV("w"), asBV("w_1"), None), HCRename(asBV("x"), asBV("x_1"), None), HCRename(asBV("dx"), asBV("dx_1"), None), HCRename(asBV("v"), asBV("v_1"), None), HCRename(asBV("xo"), asBV("xo_1"), None), HCRename(asBV("t"), asBV("t_2"), None), HCRename(asBV("dy"), asBV("dy_1"), None), HCRename(asBV("yo"), asBV("yo_1"), None), HCRename(asBV("y"), asBV("y_1"), None), HCRename(asBV("t"), asBV("t_1"), Some(AntePos(4))), HCAssign("acc:=da*(-b());".asProgram.asInstanceOf[Assign]), HCRename(asBV("da"), asBV("da_1"), None), HCAssign("a:=-b();".asProgram.asInstanceOf[Assign]), HCRename(asBV("vyo"), asBV("vyo_1"), None), HCRename(asBV("vxo"), asBV("vxo_1"), None), HCTimeStep("loop"), HCRename(asBV("w"), asBV("w_0"), None), HCRename(asBV("acc"), asBV("acc_0"), None), HCRename(asBV("a"), asBV("a_0"), None), HCRename(asBV("x"), asBV("x_0"), None), HCRename(asBV("dx"), asBV("dx_0"), None), HCRename(asBV("v"), asBV("v_0"), None), HCRename(asBV("vyo"), asBV("vyo_0"), None), HCRename(asBV("da"), asBV("da_0"), None), HCRename(asBV("r"), asBV("r_0"), None), HCRename(asBV("xo"), asBV("xo_0"), None), HCRename(asBV("t"), asBV("t_0"), None), HCRename(asBV("dy"), asBV("dy_0"), None), HCRename(asBV("yo"), asBV("yo_0"), None), HCRename(asBV("vxo"), asBV("vxo_0"), None), HCRename(asBV("y"), asBV("y_0"), None), HCTimeStep("init")))
      val c = Context(Map("dC".asVariable -> AntePosition(13), "perturb".asVariable -> AntePosition(4), "safeObs".asVariable -> AntePosition(3), "J".asVariable -> AntePosition(2), "wfDir".asVariable -> AntePosition(7), "vBound".asVariable -> AntePosition(10), "yBound".asVariable -> AntePosition(12), "yoBound".asVariable -> AntePosition(9), "xBound".asVariable -> AntePosition(11), "xoBound".asVariable -> AntePosition(8), "assms".asVariable -> AntePosition(1), "tPos".asVariable -> AntePosition(6)),
        Map(),
        Map("WFDIR" -> ("t", "t{dx^2+dy^2=1}".asFormula), "SD" -> ("t", "t(v^2/(2*(b()*Da()))+V()*v/(b()*Da()))".asTerm), "ASEP" -> ("t", "t(v^2/(2*(b()*Da()))+V()*v/(b()*Da())+(A()/(b()*Da())+1)*(A()/2*ep()^2+ep()*(v+V())))".asFormula)))
      val time = System.currentTimeMillis()
      val sp: SP =
      // TODO: Pick right assumptions for each subproof
        BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
          Show("wild()".asFormula, UP(List(Left("assm(dC)".asExpr)), Kaisar.RCF()))
          ,
          BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
            Show("wild()".asFormula, UP(List(), CloseId())),
            BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
              Have("imp".asVariable, "loop{v> 0 -> (abs(x-xo) > SD_() | abs(y-yo) > SD_())}".asFormula,
                Show("wild()".asFormula, UP(List(Left("assm(J)".asExpr)), Kaisar.RCF()))
                ,
                BRule(RBAbbrev("actBEq".asVariable, "actB".asVariable, "b()*Da()".asTerm), List(
                  Have("actBPos".asVariable, "actB>0".asFormula, Show("wild()".asFormula, UP(List(Left("assm(assms)".asExpr), Left("assm(actBEq)".asExpr)), Kaisar.RCF())),

                    BRule(RBCaseImplyL("oldVPos".asVariable, "loop(v)>0 ".asFormula, "disj".asVariable, "wild()".asFormula), List(
                      Show("loop(v)>0".asFormula, UP(List(), Kaisar.SmartQE())),
                      BRule(RBCaseOrL("xxo".asVariable, "loop(abs(x-xo)) > wild()".asFormula, "yyo".asVariable, "loop(abs(y-yo)) > wild()".asFormula), List(
                        PrintGoal("SG1",
                          BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                            Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE()))))
                        ),
                        PrintGoal("SG2",
                          BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                            Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),assm(J)))".asExpr)), Kaisar.SmartQE())))))))))))))))))))
      Kaisar.eval(sp, h, c, Provable.startProof(seq)) shouldBe 'proved
      println("Time taken (millis): " + (System.currentTimeMillis() - time))
    })
  }

  "ijrr theorem 7 third arith" should "prove" in {
    withMathematica(qeTool => {
      val seq = Sequent(
        immutable.IndexedSeq[Formula](
          "(A()>=0&b()>0&ep()>0&V()>0&0 < Da()&Da()<=1)&v_0=0&(x_0-xo_0)^2-(y_0-yo_0)^2>0&dx_0^2+dy_0^2=1".asFormula,
          "v_1>=0&dx_1^2+dy_1^2=1&(v_1>0->abs(x_1-xo_1)>v_1^2/(2*(b()*Da()))+V()*v_1/(b()*Da())|abs(y_1-yo_1)>v_1^2/(2*(b()*Da()))+V()*v_1/(b()*Da()))".asFormula,
          "vxo^2+vyo^2<=V()^2".asFormula,
          "-W()<=w_0&w_0<=W()".asFormula,
          "r!=0&r*w_0=v_1".asFormula,
          "abs(x_1-xo_2)>v_1^2/(2*(b()*Da()))+V()*v_1/(b()*Da())+(A()/(b()*Da())+1)*(A()/2*ep()^2+ep()*(v_1+V()))|abs(y_1-yo_2)>v_1^2/(2*(b()*Da()))+V()*v_1/(b()*Da())+(A()/(b()*Da())+1)*(A()/2*ep()^2+ep()*(v_1+V()))".asFormula,
          "Da()<=da&da<=1".asFormula,
          "t_0=0".asFormula,
          "t>=0".asFormula,
          " dx^2+dy^2=1".asFormula,
          "-t*V()<=xo-xo_2&xo-xo_2<=t*V()".asFormula,
          "-t*V()<=yo-yo_2&yo-yo_2<=t*V()".asFormula,
          " v<=v_1+A()*t".asFormula,
          "-t*(v_1+A()/2*t)<=x-x_1&x-x_1<=t*(v_1+A()/2*t)".asFormula, "-t*(v_1+A()/2*t)<=y-y_1&y-y_1<=t*(v_1+A()/2*t)".asFormula,
          "v>=0&t<=ep()".asFormula),
        immutable.IndexedSeq[Formula]("v>=0&dx^2+dy^2=1&(v>0->abs(x-xo)>v^2/(2*(b()*Da()))+V()*v/(b()*Da())|abs(y-yo)>v^2/(2*(b()*Da()))+V()*v/(b()*Da()))".asFormula))
      val c = Context(Map(
        "assms".asVariable -> AntePosition(1),
        "J".asVariable -> AntePosition(2),
        "safeObs".asVariable -> AntePosition(3),
        "wGood".asVariable -> AntePosition(4),
        "goodCurve".asVariable -> AntePosition(5),
        "greatCurve".asVariable -> AntePosition(6),
        "perturb".asVariable -> AntePosition(7),
        "tPos".asVariable -> AntePosition(9),
        "wfDir".asVariable -> AntePosition(10),
        "xoBound".asVariable -> AntePosition(11),
        "yoBound".asVariable -> AntePosition(12),
        "vBound".asVariable -> AntePosition(13),
        "xBound".asVariable -> AntePosition(14),
        "yBound".asVariable -> AntePosition(15),
        "dC".asVariable -> AntePosition(16)
      ), Map(), Map("WFDIR" -> ("t", "t{dx^2+dy^2=1}".asFormula), "SD" -> ("t", "t(v^2/(2*(b()*Da()))+V()*v/(b()*Da()))".asTerm), "ASEP" -> ("t", "t(v^2/(2*(b()*Da()))+V()*v/(b()*Da())+(A()/(b()*Da())+1)*(A()/2*ep()^2+ep()*(v+V())))".asFormula)))

      def asBV(s: String): BaseVariable = s.asVariable.asInstanceOf[BaseVariable]

      val h = History(List(HCRename(asBV("w"), asBV("w_2"), None), HCRename(asBV("x"), asBV("x_1"), None), HCRename(asBV("dx"), asBV("dx_1"), None), HCRename(asBV("v"), asBV("v_1"), None), HCRename(asBV("xo"), asBV("xo_2"), None), HCRename(asBV("t"), asBV("t_2"), None), HCRename(asBV("dy"), asBV("dy_1"), None), HCRename(asBV("yo"), asBV("yo_2"), None), HCRename(asBV("y"), asBV("y_1"), None), HCTimeStep("safeCurve"), HCRename(asBV("t"), asBV("t_1"), Some(AntePos(7))), HCAssign("acc:=da*A();".asProgram.asInstanceOf[Assign]), HCRename(asBV("da"), asBV("da_1"), None), HCRename(asBV("yo"), asBV("yo_1"), None), HCRename(asBV("xo"), asBV("xo_1"), None), HCRename(asBV("r"), asBV("r_1"), None), HCRename(asBV("w"), asBV("w_1"), None), HCAssign("a:=A();".asProgram.asInstanceOf[Assign]), HCRename(asBV("vyo"), asBV("vyo_1"), None), HCRename(asBV("vxo"), asBV("vxo_1"), None), HCTimeStep("loop"), HCRename(asBV("w"), asBV("w_0"), None), HCRename(asBV("acc"), asBV("acc_0"), None), HCRename(asBV("a"), asBV("a_0"), None), HCRename(asBV("x"), asBV("x_0"), None), HCRename(asBV("dx"), asBV("dx_0"), None), HCRename(asBV("v"), asBV("v_0"), None), HCRename(asBV("vyo"), asBV("vyo_0"), None), HCRename(asBV("da"), asBV("da_0"), None), HCRename(asBV("r"), asBV("r_0"), None), HCRename(asBV("xo"), asBV("xo_0"), None), HCRename(asBV("t"), asBV("t_0"), None), HCRename(asBV("dy"), asBV("dy_0"), None), HCRename(asBV("yo"), asBV("yo_0"), None), HCRename(asBV("vxo"), asBV("vxo_0"), None), HCRename(asBV("y"), asBV("y_0"), None), HCTimeStep("init")))
      val sp: SP =
        BRule(RBCase(List("v>=0".asFormula, "wild()".asFormula)), List(
          duh
          ,
          BRule(RBCase(List("dx^2+dy^2=1".asFormula, "wild()".asFormula)), List(
            duh,
            BRule(RBAssume("vPos".asVariable, "v>0".asFormula), List(
              BRule(RBCaseOrL("absdx".asVariable, "safeCurve(abs(x-xo)) > wild()".asFormula, "absyx".asVariable, "safeCurve(abs(y-yo)) > wild()".asFormula), List(
                Have("dxep".asVariable, "safeCurve(abs(x-xo))>safeCurve(v)^2/(2*(b()*Da()))+V()*safeCurve(v)/(b()*Da())+(A()/(b()*Da())+1)*(A()/2*t^2+t*(safeCurve(v)+V()))".asFormula,
                  Show("wild()".asFormula, UP(List(Left("assm(dC)".asExpr), Left("assm(greatCurve)".asExpr), Left("assm(assms)".asExpr), Left("assm(tPos)".asExpr), Left("assm(J)".asExpr)), Kaisar.RCF())),
                  PrintGoal("got through dxep",
                    BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                      BRule(RBAbbrev("actBEq".asVariable, "actB".asVariable, "b()*Da()".asTerm), List(
                        Have("actBPos".asVariable, "actB>0".asFormula, Show("actB>0".asFormula, UP(List(Left("union(assm(assms),assm(actBEq))".asExpr)), Kaisar.RCF())),
                          Have("someAssms".asVariable, "A() >= 0 & V() > 0 & Da()<=1".asFormula, Show("wild()".asFormula, UP(List(Left("assm(assms)".asExpr), Left("assm(goodCurve)".asExpr)), Kaisar.Auto())),
                            Show("abs(x-xo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),union(assm(J),union(assm(yBound),union(assm(yoBound),union(assm(safeObs),union(assm(perturb),union(assm(wfDir),union(assm(assms),union(assm(goodCurve),union(assm(dC),assm(actBEq))))))))))))".asExpr)),
                              Kaisar.SmartQE()))))))))))
                ,
                Have("dxep".asVariable, "safeCurve(abs(y-yo))>safeCurve(v)^2/(2*(b()*Da()))+V()*safeCurve(v)/(b()*Da())+(A()/(b()*Da())+1)*(A()/2*t^2+t*(safeCurve(v)+V()))".asFormula,
                  Show("wild()".asFormula, UP(List(Left("assm(dC)".asExpr), Left("assm(greatCurve)".asExpr), Left("assm(assms)".asExpr), Left("assm(tPos)".asExpr), Left("assm(J)".asExpr)), Kaisar.RCF())),
                  PrintGoal("got through dxep",
                    BRule(RBCaseOrR("goal1".asVariable, "goal2".asVariable), List(
                      BRule(RBAbbrev("actBEq".asVariable, "actB".asVariable, "b()*Da()".asTerm), List(
                        Have("actBPos".asVariable, "actB>0".asFormula, Show("actB>0".asFormula, UP(List(Left("union(assm(assms),assm(actBEq))".asExpr)), Kaisar.RCF())),
                          Have("someAssms".asVariable, "A() >= 0 & V() > 0 & Da()<=1".asFormula, Show("wild()".asFormula, UP(List(Left("assm(assms)".asExpr), Left("assm(goodCurve)".asExpr)), Kaisar.Auto())),
                            Show("abs(y-yo) > wild()".asFormula, UP(List(Left("neg(union(assm(greatCurve),union(assm(J),union(assm(xBound),union(assm(xoBound),union(assm(safeObs),union(assm(perturb),union(assm(wfDir),union(assm(assms),union(assm(goodCurve),union(assm(dC),assm(actBEq))))))))))))".asExpr)),
                              Kaisar.SmartQE()))))))))))))))))))
      Kaisar.eval(sp, h, c, Provable.startProof(seq)) shouldBe 'proved
 {}   })
  }
}