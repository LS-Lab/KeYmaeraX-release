/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon.pptests

import org.keymaerax.bellerophon._
import org.keymaerax.bellerophon.parser.{BellePrettyPrinter, TacticParser}
import org.keymaerax.btactics._
import org.keymaerax.infrastruct.PosInExpr
import org.keymaerax.parser.ParseExceptionMatchers.{mention, pointAt}
import org.keymaerax.parser.StringConverter._
import org.keymaerax.parser.{ArchiveParser, BuiltinSymbols, ParseException}
import org.keymaerax.pt.ProvableSig
import org.scalatest.Inside._

/**
 * These are probably unnecessary now that SimpleBelleParserTests is around, but they are very fast so additional
 * coverage can't hurt.
 * @author
 *   Nathan Fulton
 */
class MoreSimpleBelleParserTests extends TacticTestBase {

  /** The parsing function to use for these test cases. */
  private lazy val parser: TacticParser = ArchiveParser.tacticParser

  "The Bellerophon Tactics Parser" should "parse nil; nil" in withTactics {
    val result = parser("nil; nil").asInstanceOf[SeqTactic]
    parser("nil & nil") shouldBe result
    val expected = SeqTactic(TactixLibrary.nil, TactixLibrary.nil).asInstanceOf[SeqTactic]
    result.seq should contain theSameElementsInOrderAs expected.seq
  }

  it should "parse nil; <(nil, nil, nil)" in withTactics {
    val result = parser("nil; <(nil, nil, nil)").asInstanceOf[SeqTactic]
    val expected =
      SeqTactic(TactixLibrary.nil, BranchTactic(Seq(TactixLibrary.nil, TactixLibrary.nil, TactixLibrary.nil)))
        .asInstanceOf[SeqTactic]
    result.seq.head shouldBe expected.seq.head
    result
      .seq
      .last
      .asInstanceOf[BranchTactic]
      .children
      .zip(expected.seq.last.asInstanceOf[BranchTactic].children)
      .map(x => x._1 shouldBe x._2)
  }

  it should "parse expression arguments with {} in them" in withTactics {
    inside(parser("""loop("[{x' = v, v' = -b}]x <= m", 1)""")) {
      case t: AppliedDependentPositionTacticWithAppliedInput =>
        t.name shouldBe "loop"
        inside(t.pt) { case dpt: DependentPositionWithAppliedInputTactic =>
          dpt.inputs shouldBe List("[{x' = v, v' = -b}]x <= m".asFormula)
        }
        t.locator shouldBe Fixed(1)
    }

  }

  it should "parse partials and built-ins" in withTactics {
    inside(parser("partial(implyR(1))")) { case PartialTactic(t, _) => t shouldBe TactixLibrary.implyR(1) }
  }

  it should "parse post-fix partials and built-ins" in withTactics {
    inside(parser("implyR(1) partial")) { case PartialTactic(t, _) => t shouldBe TactixLibrary.implyR(1) }
  }

  it should "parse either" in withTactics {
    val EitherTactic(alts) = parser("nil | implyR(1)")
    alts should contain theSameElementsInOrderAs List(TactixLibrary.nil, TactixLibrary.implyR(1))
  }

  it should "parse *" in withTactics {
    inside(parser("implyR(1)*")) {
      case SaturateTactic(t) => t shouldBe TactixLibrary.implyR(1)
      case r => fail("Unexpected tactic kind " + r.getClass)
    }
  }

  it should "parse positional tactics" in withTactics {
    inside(parser("implyR(1)")) { case t @ AppliedPositionTactic(pt, loc) =>
      loc shouldBe Fixed(1)
      pt shouldBe TactixLibrary.implyR
      t shouldBe TactixLibrary.implyR(1)
    }
  }

  it should "parse formula tactics" in withTactics {
    val t = parser("""loop("v >= 0",1)""").asInstanceOf[AppliedDependentPositionTactic]
    t should have(Symbol("name")("loop"))
    t.pt should have(Symbol("inputs")(List("v>=0".asFormula)))
  }

  it should "parse j(x) as a term or a formula depending on ArgInfo." in withTactics {
    parser("""loop("j(x)",1)""") shouldBe TactixLibrary.loop("j(x)".asFormula)(1)
    parser("""allL("j(x)",1)""") shouldBe TactixLibrary.allL("j(x)".asTerm)(1)
  }

  it should "parse exact matching search" in withTactics {
    parser("""implyR('R=="x>0->x>=0")""") shouldBe TactixLibrary.implyR(Symbol("R"), "x>0->x>=0".asFormula)
    parser("""andL('L=="x>0&x>=0")""") shouldBe TactixLibrary.andL(Symbol("L"), "x>0&x>=0".asFormula)
    parser("""absExp('L=="#abs(x*y)#=2")""") shouldBe
      TactixLibrary
        .abs(Find.FindL(0, Some("abs(x*y)=2".asFormula), PosInExpr(0 :: Nil), exact = true, BuiltinSymbols.all))
  }

  it should "parse unifiable matching search" in withTactics {
    parser("""implyR('R~="x>0->x>=0")""") shouldBe TactixLibrary.implyR(Symbol("Rlike"), "x>0->x>=0".asFormula)
    parser("""andL('L~="x>0&x>=0")""") shouldBe TactixLibrary.andL(Symbol("Llike"), "x>0&x>=0".asFormula)
    parser("""absExp('L~="#abs(x)#=3")""") shouldBe
      TactixLibrary
        .abs(Find.FindL(0, Some("abs(x)=3".asFormula), PosInExpr(0 :: Nil), exact = false, BuiltinSymbols.all))
  }

  it should "parse fancy dG" in withTactics {
    parser("""dG("y' = 0",1)""") should
      (be(TactixLibrary.dG("y'=0".asDifferentialProgram, None)(1)) or be(TactixLibrary.dG("y'=0".asFormula, None)(1)))
    parser("""dG("y' = 0", "1=1",1)""") should
      (be(TactixLibrary.dG("y'=0".asDifferentialProgram, Some("1=1".asFormula))(1)) or
        be(TactixLibrary.dG("y'=0".asFormula, Some("1=1".asFormula))(1)))
  }

  it should "parse multiple nested arguments" in withTactics {
    val t = DebuggingTactics.pending("""andR(1) ; <( QE("Mathematica"), QE("Mathematica") )""")
    parser(t.prettyString) shouldBe t
  }

  it should "parse deeply nested arguments" in withTactics {
    val t = DebuggingTactics.pending("""pending("QE("Mathematica")")""")
    parser(t.prettyString) shouldBe t
  }

  "Using" should "parse" in withTactics {
    parser(""" QE using "x>=0::x>0::nil" """) shouldBe
      Using("x>=0".asFormula :: "x>0".asFormula :: Nil, TactixLibrary.QE)
    parser(""" ODE(1) using "x>=0::x>0::nil" """) shouldBe
      Using("x>=0".asFormula :: "x>0".asFormula :: Nil, TactixLibrary.ODE(1))
    parser(""" ODE(1) using "nil" """) shouldBe Using(Nil, TactixLibrary.ODE(1))
    parser(""" unfold using "x>=0 | x<=0"; doall(QE using "x>=0::x>0::nil") """) shouldBe
      Using("x>=0 | x<=0".asFormula :: Nil, TactixLibrary.unfoldProgramNormalize) &
      OnAll(Using("x>=0".asFormula :: "x>0".asFormula :: Nil, TactixLibrary.QE))
    the[ParseException] thrownBy parser(""" unfold using "x>0::y>0" """) should
      (pointAt(1, 24) and mention("Error parsing argList at 1:16"))
  }

  it should "bind strong" in withTactics {
    parser(""" implyR(1); id using "x>=0" """) shouldBe
      TactixLibrary.implyR(1) & Using("x>=0".asFormula :: Nil, TactixLibrary.id)
    parser(""" (implyR(1); id) using "x>=0" """) shouldBe
      Using("x>=0".asFormula :: Nil, TactixLibrary.implyR(1) & TactixLibrary.id)
    parser(""" implyR(1) | id using "x>=0" """) shouldBe
      TactixLibrary.implyR(1) | Using("x>=0".asFormula :: Nil, TactixLibrary.id)
  }

  it should "parse empty lists" in withTactics {
    parser(""" id using "nil" """) shouldBe Using(Nil, TactixLibrary.id)
    BellePrettyPrinter(Using(Nil, TactixLibrary.id)) shouldBe """id using "nil""""
  }

  it should "pretty print binding strong" in withTactics {
    BellePrettyPrinter(parser(""" implyR(1); id using "x>=0" """)).trim shouldBe
      """ implyR(1) ; id using "x>=0" """.trim
    BellePrettyPrinter(parser(""" (implyR(1); id) using "x>=0::y>=0::nil" """)).trim shouldBe
      """ (implyR(1) ; id) using "x>=0 :: y>=0 :: nil" """.trim
    BellePrettyPrinter(parser(""" (implyR(1) | implyR(2)); id using "x>=0" """)).trim shouldBe
      """ (implyR(1) | implyR(2)) ; id using "x>=0" """.trim
  }

  "Propositional Examples" should "close p() -> p()" in withTactics {
    val tactic = parser("implyR(1); id")
    val value = BelleProvable.plain(ProvableSig.startPlainProof("p() -> p()".asFormula))
    val result = BelleInterpreter(tactic, value)
    result match {
      case BelleProvable(resultingProvable, _) => resultingProvable.isProved shouldBe true
      case _ => throw new Exception("Expected a BelleProvable.")
    }
  }
}
