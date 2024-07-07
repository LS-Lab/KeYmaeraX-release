/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.parser.BelleParser
import org.keymaerax.bellerophon.{OnAll, SaturateTactic}
import org.keymaerax.btactics.ArithmeticSimplification._
import org.keymaerax.btactics.DebuggingTactics.{print, printIndexed}
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification._
import org.keymaerax.core._
import org.keymaerax.parser.ArchiveParser
import org.keymaerax.parser.StringConverter._
import org.keymaerax.tags.SlowTest
import org.keymaerax.testhelper.ParserFactory._
import org.scalatest.LoneElement._

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Tutorial test cases.
 *
 * @author
 *   Stefan Mitsch
 */
@SlowTest
class StttTutorial extends TacticTestBase {

  "Example 1" should "be provable" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 1",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      val tactic = implyR(Symbol("_")) & andL(Symbol("_")) &
        dC("v>=0".asFormula)(1) <
        (
          /* use */ dW(1) & prop,
          /* show */ dI()(1),
        )
      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  it should "be provable with diffSolve" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 1",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      val tactic = implyR(Symbol("_")) & andL(Symbol("_")) & solve(1) & QE
      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  it should "be provable with master" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 1",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  it should "be provable with diffInvariant" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 1",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      val tactic = implyR(Symbol("_")) & andL(Symbol("_")) & diffInvariant("v>=0".asFormula)(Symbol("R")) &
        dW(Symbol("R")) & prop
      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  "Example 1a" should "be provable" in withQE { _ =>
    withDatabase { db =>
      val modelContent =
        io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.kyx")).mkString
      val tactic = implyR(Symbol("_")) & SaturateTactic(andL(Symbol("_"))) & dC("v>=0".asFormula)(1) & Idioms.<(
        dC("x>=old(x)".asFormula)(1) &
          Idioms
            .<(dW(1) & SaturateTactic(alphaRule) & exhaustiveEqL2R(Symbol("L"), "x0=x_0".asFormula) & prop, dI()(1)),
        dI()(1),
      )

      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  it should "be provable with multi-arg invariant" in withQE { _ =>
    withDatabase { _ =>
      val modelContent =
        io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example1a.kyx")).mkString
      val tactic = implyR(Symbol("_")) & SaturateTactic(andL(Symbol("_"))) &
        diffInvariant("v>=0".asFormula :: "x>=old(x)".asFormula :: Nil)(1) & dW(1) & SaturateTactic(alphaRule) &
        exhaustiveEqL2R(Symbol("L"), "x0=x_0".asFormula) & prop

      // @todo multi-argument diffInvariant not yet supported by TacticExtraction/BelleParser
//    db.proveBy(modelContent, tactic) shouldBe 'proved
      proveBy(ArchiveParser.parseAsFormula(modelContent), tactic) shouldBe Symbol("proved")
    }
  }

  "Example 2" should "be provable with master and custom loop invariant" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 2",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      val Imply(_, Box(loop, _)) = ArchiveParser.parseAsFormula(modelContent)
      db.proveBy(modelContent, master(new ConfigurableGenerator(Map((loop, ("v>=0".asFormula, None) :: Nil))))) shouldBe
        Symbol("proved")
    }
  }

  it should "be provable with master and loop invariant from file" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 2",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  it should "be provable with abstract loop invariant" in withMathematica { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 2",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent

      val tactic = BelleParser(
        """
          |implyR('R);
          |andL('L)*;
          |loop("J(v)",'R); <(
          |  nil,
          |  nil,
          |  chase('R); prop; doall(solve('R))
          |);
          |US("J(.) ~> .>=0");
          |doall(QE);
          |done
          |""".stripMargin
      )

      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  "Example 3a" should "be provable with master and loop invariant from file" in withQE { _ =>
    withDatabase { db =>
      // // needs evolution domain at time 0
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 3a",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  "Example3b" should "find correct safety condition" in withMathematica { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 3b",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent

      val tactic = BelleParser("implyR('R); andL('L)*; chase('R); unfold; doall(solve('R))")
      val intermediate = db.proveBy(modelContent, tactic)
      intermediate.subgoals should have size 3
      intermediate.subgoals(0) shouldBe
        "v>=0, A()>0, B()>0, true, x<=S(), true ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> A()*s_+v>=0) -> A()*(t_^2/2)+v*t_+x<=S())"
          .asSequent
      intermediate.subgoals(1) shouldBe
        "v>=0, A()>0, B()>0, true, x<=S(), v=0 ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> v>=0) -> v*t_+x<=S())"
          .asSequent
      intermediate.subgoals(2) shouldBe
        "v>=0, A()>0, B()>0, true, x<=S() ==> \\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> (-B())*s_+v>=0) -> (-B())*(t_^2/2)+v*t_+x<=S())"
          .asSequent

      val brake = proveBy(intermediate.subgoals(2), TactixLibrary.partialQE)
      // here is the most interesting condition of our invariant candidate --------------------v
      brake.subgoals.loneElement shouldBe
        "v>=0, A()>0, B()>0, x<=S() ==> x < S()&(v<=0|v>0&B()>=(-v^2)*(2*x+-2*S())^-1)|x=S()&v<=0".asSequent
      // transform into nicer shape
      val result = proveBy(brake, TactixLibrary.transform("x + v^2/(2*B()) <= S()".asFormula)(1))
      result.subgoals.loneElement shouldBe "v>=0, A()>0, B()>0, x<=S() ==> x + v^2/(2*B()) <= S()".asSequent
    }
  }

  it should "stop at correct spot when tactic is parsed from file" in withQE { _ =>
    withDatabase { db =>
      val entry = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 3b",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
      val modelContent = entry.fileContent
      val tactic = entry.tactics.head._3
      val intermediate = db.proveBy(modelContent, tactic)
      intermediate.subgoals should have size 3
      intermediate.subgoals(0) shouldBe Sequent(
        IndexedSeq(
          "v>=0".asFormula,
          "A()>0".asFormula,
          "B()>0".asFormula,
          "true".asFormula,
          "x<=S()".asFormula,
          "true".asFormula,
        ),
        IndexedSeq(
          "\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> A()*s_+v>=0) -> A()*(t_^2/2)+v*t_+x<=S())".asFormula
        ),
      )
      intermediate.subgoals(1) shouldBe Sequent(
        IndexedSeq(
          "v>=0".asFormula,
          "A()>0".asFormula,
          "B()>0".asFormula,
          "true".asFormula,
          "x<=S()".asFormula,
          "v=0".asFormula,
        ),
        IndexedSeq("\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> v>=0) -> v*t_+x<=S())".asFormula),
      )
      intermediate.subgoals(2) shouldBe Sequent(
        IndexedSeq("v>=0".asFormula, "A()>0".asFormula, "B()>0".asFormula, "true".asFormula, "x<=S()".asFormula),
        IndexedSeq(
          "\\forall t_ (t_>=0 -> \\forall s_ (0<=s_ & s_<=t_ -> (-B())*s_+v>=0) -> (-B())*(t_^2/2)+v*t_+x<=S())"
            .asFormula
        ),
      )
    }
  }

  "Example 4a" should "be provable with master and loop invariant from file" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 4a",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  "Example 4b" should "be provable with master and loop invariant from file" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 4b",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  "Example 4c" should "be provable with master and loop invariant from file" in withQE { _ =>
    withDatabase { db =>
      // needs evolution domain at time 0
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 4c",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  "Example 5 with simple control" should "be provable" in withQE { _ =>
    withDatabase { db =>
      val modelContent = io
        .Source
        .fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.kyx"))
        .mkString

      val plant = print("plant") & composeb(Symbol("R")) & assignb(Symbol("R")) & solveEnd(Symbol("R"))

      val tactic = implyR(Symbol("R")) & SaturateTactic(andL(Symbol("L"))) &
        loop("v >= 0 & x+v^2/(2*B()) <= S()".asFormula)(Symbol("R")) <
        (
          print("Base Case") & andR(Symbol("R")) & OnAll(id),
          print("Use Case") & QE,
          print("Step") & andL(Symbol("L")) & composeb(Symbol("R")) & assignb(Symbol("R")) & plant & QE,
        )

      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  it should "be provable automatically" in withQE { _ =>
    withDatabase { db =>
      val modelContent = io
        .Source
        .fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/example5_simplectrl.kyx"))
        .mkString
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  "Example 5" should "be provable automatically" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 5",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  it should "be provable with chase etc" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 5",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent

      val tactic = implyR(Symbol("R")) & SaturateTactic(andL(Symbol("L"))) &
        loop("v >= 0 & x+v^2/(2*B()) <= S()".asFormula)(Symbol("R")) <
        (
          printIndexed("Base case") & andR(Symbol("R")) & OnAll(id),
          printIndexed("Use case") & QE,
          printIndexed("Step") & chase(Symbol("R")) & printIndexed("After chase") & normalize &
            printIndexed("Normalized") & OnAll(solveEnd(Symbol("R"))) & printIndexed("After diffSolve") & OnAll(QE),
        )

      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  it should "be provable with abstract loop invariant" in withMathematica { _ =>
    val s = ArchiveParser
      .getEntry(
        "STTT16/Tutorial Example 5",
        io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
      )
      .get
      .model
      .asInstanceOf[Formula]

    val tactic = BelleParser(
      """implyR(1);
        |andL('L)*;
        |loop("J(v,x,B(),S())",1); <(
        |  nil,
        |  nil,
        |  chase(1); unfold; doall(solve('R))
        |);
        |US("J(v,x,B,S) ~> v>=0 & x+v^2/(2*B) <= S");
        |doall(QE);
        |done
        |""".stripMargin
    )

    proveBy(s, tactic) shouldBe Symbol("proved")
  }

  "Example 6" should "be provable automatically" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 6",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  "Example 7" should "be provable automatically" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 7",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      db.proveBy(modelContent, master()) shouldBe Symbol("proved")
    }
  }

  "Example 8" should "be provable automatically with Mathematica" ignore withMathematica { _ =>
    // x' <= a*d
    val s = parseToSequent(getClass.getResourceAsStream("/examples/tutorials/sttt/example8.kyx"))
    proveBy(s, master()) shouldBe Symbol("proved")
  }

  "Example 9a" should "be provable" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 9a",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent
      val tactic = implyR(Symbol("R")) & SaturateTactic(andL(Symbol("L"))) & dI()(Symbol("R"))
      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  "Example 9b" should "be provable" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 9b",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent

      val ode =
        // xr = (xm+S)/2
        diffInvariant("xm<=x".asFormula)(Symbol("R")) &
          diffInvariant("5/4*(x-(xm+S())/2)^2 + (x-(xm+S())/2)*v/2 + v^2/4 < ((S()-xm)/2)^2".asFormula)(Symbol("R")) &
          dW(Symbol("R"))

      val tactic = implyR(Symbol("R")) & SaturateTactic(andL(Symbol("L"))) &
        loop("v >= 0 & xm <= x & xr = (xm + S())/2 & 5/4*(x-xr)^2 + (x-xr)*v/2 + v^2/4 < ((S() - xm)/2)^2".asFormula)(
          Symbol("R")
        ) <
        (
          print("Base case") & SaturateTactic(andR(Symbol("R")) < (id, skip)) & id,
          print("Use case") & QE,
          print("Step") & SaturateTactic(andL(Symbol("L"))) & chase(Symbol("R")) &
            andR(Symbol("R")) <
            (allR(Symbol("R")) & SaturateTactic(implyR(Symbol("R"))) & ode & QE, implyR(Symbol("R")) & ode & QE),
        )

      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  "Example 10" should "FEATURE_REQUEST: be provable" in withQE { _ =>
    withDatabase { db =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 10",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent

      def ode(a: String) = dC("c>=0".asFormula)(1) & Idioms.<(
        dC("dx^2+dy^2=1".asFormula)(1) & Idioms.<(
          dC(s"v=old(v)+$a*c".asFormula)(1) & Idioms.<(
            dC(s"-c*(v-$a/2*c) <= y - old(y) & y - old(y) <= c*(v-$a/2*c)".asFormula)(1) & Idioms.<(skip, dI()(1)),
            dI()(1),
          ),
          dI()(1),
        ),
        dI()(1),
      ) & SaturateTactic(andL(Symbol("L"))) & dW(Symbol("R"))

      def hideQE = SaturateTactic(hideL(Symbol("Llike"), "dx_0^2+dy_0^2=1".asFormula)) &
        hideL(Symbol("L"), "c<=ep()".asFormula) & hideL(Symbol("L"), "r!=0".asFormula)

      val tactic = implyR(Symbol("R")) & SaturateTactic(andL(Symbol("L"))) &
        loop("v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly()) + v^2/(2*b()) < lw()".asFormula)(Symbol("R")) <
        (
          print("Base case") & speculativeQE, // @todo speculativeQE with Z3 fails but QE works
          print("Use case") & speculativeQE,
          print("Step") & chase(Symbol("R")) & normalize &
            printIndexed("Normalized") <
            (
              printIndexed("Acc") & hideL(-15, "abs(y-ly())+v^2/(2*b()) < lw()".asFormula) & ode("a") &
                SaturateTactic(alphaRule) & printIndexed("Before replaceTransform") & replaceTransform(
                  "ep()".asTerm,
                  "c".asTerm,
                )(-13, "abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()".asFormula) & prop &
                OnAll(speculativeQE),
              printIndexed("Stop") & ode("0") & prop & OnAll(hideQE & speculativeQE),
              printIndexed("Brake") & ode("a") & prop & OnAll(hideQE & speculativeQE),
            ),
        )

      db.proveBy(modelContent, tactic) shouldBe Symbol("proved")
    }
  }

  it should "be provable with multi-arg diff. invariant" in withQE { _ =>
    withDatabase { _ =>
      val modelContent = ArchiveParser
        .getEntry(
          "STTT16/Tutorial Example 10",
          io.Source.fromInputStream(getClass.getResourceAsStream("/examples/tutorials/sttt/sttt.kyx")).mkString,
        )
        .get
        .fileContent

      def ode(a: String) = diffInvariant(
        "c>=0".asFormula :: "dx^2+dy^2=1".asFormula :: s"v=old(v)+$a*c".asFormula ::
          s"-c*(v-$a/2*c) <= y - old(y) & y - old(y) <= c*(v-$a/2*c)".asFormula :: Nil
      )(Symbol("R")) & dW(Symbol("R"))

      def hideQE = SaturateTactic(hideL(Symbol("Llike"), "dx_0^2+dy_0^2=1".asFormula)) &
        hideL(Symbol("L"), "c<=ep()".asFormula) & hideL(Symbol("L"), "r!=0".asFormula)

      val tactic = implyR(Symbol("R")) & SaturateTactic(andL(Symbol("L"))) &
        loop("v >= 0 & dx^2+dy^2 = 1 & r != 0 & abs(y-ly()) + v^2/(2*b()) < lw()".asFormula)(Symbol("R")) <
        (
          print("Base case") & speculativeQE,
          print("Use case") & speculativeQE,
          print("Step") & chase(Symbol("R")) & normalize &
            printIndexed("Normalized") <
            (
              printIndexed("Acc") & hideL(-15, "abs(y-ly())+v^2/(2*b()) < lw()".asFormula) & ode("a") &
                SaturateTactic(alphaRule) & printIndexed("Before replaceTransform") & replaceTransform(
                  "ep()".asTerm,
                  "c".asTerm,
                )(-13, "abs(y_0-ly())+v_0^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v_0) < lw()".asFormula) & prop &
                OnAll(speculativeQE),
              printIndexed("Stop") & ode("0") & prop & OnAll(hideQE & speculativeQE),
              printIndexed("Brake") & ode("a") & prop & OnAll(hideQE & speculativeQE),
            ),
        )

      // @todo multi-argument diffInvariant not yet supported by TacticExtraction/BelleParser
      // db.proveBy(modelContent, tactic) shouldBe 'proved
      proveBy(ArchiveParser.parseAsFormula(modelContent), tactic) shouldBe Symbol("proved")
    }
  }

}
