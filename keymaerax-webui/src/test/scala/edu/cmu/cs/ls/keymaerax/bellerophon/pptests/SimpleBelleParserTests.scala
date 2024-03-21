/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.{
  ArchiveParser,
  Declaration,
  Name,
  ParseException,
  Region,
  Signature,
  TacticReservedSymbols,
  UnknownLocation,
}
import edu.cmu.cs.ls.keymaerax.tagobjects.TodoTest
import edu.cmu.cs.ls.keymaerax.tags.UsualTest
import org.scalatest.Inside._
import org.scalatest.matchers.MatchResult

import java.io.File
import scala.language.postfixOps

/**
 * Very simple positive unit tests for the Bellerophon parser. Useful for TDD and bug isolation but probably not so
 * useful for anything else.
 *
 * @note
 *   It may be useful to turn on BelleParser.DEBUG if you're actually debugging.
 * @author
 *   Nathan Fulton
 */
@UsualTest
class SimpleBelleParserTests extends TacticTestBase(registerAxTactics = Some("z3")) {
  private lazy val tacticParser = ArchiveParser.tacticParser

  private object round {
    def trip(t: BelleExpr): BelleExpr = {
      roundTrip(t) shouldBe t
      t
    }
    def roundTrip(t: BelleExpr): BelleExpr = tacticParser(BellePrettyPrinter(t))
  }

  private object print {
    def as(right: String): org.scalatest.matchers.Matcher[BelleExpr] = new org.scalatest.matchers.Matcher[BelleExpr]() {
      def apply(left: BelleExpr): MatchResult = {
        MatchResult(
          BellePrettyPrinter(left) == right,
          "pretty-printing tactic failed", // @note can't print tactics since {} are reserved characters in match result message
          "pretty-printing succeeded",
          Vector(left, right),
        )
      }
      override def toString: String = "Print as " + right
    }
  }

  private object reparse {
    def fromPrint: org.scalatest.matchers.Matcher[BelleExpr] = new org.scalatest.matchers.Matcher[BelleExpr]() {
      def apply(left: BelleExpr): MatchResult = {
        MatchResult(
          tacticParser(BellePrettyPrinter(left)) == left,
          "re-parsing pretty-printed tactic failed",
          "re-parsing pretty-printed tactic succeeded",
          Vector(left),
        )
      }
      override def toString: String = "reparse"
    }
  }

  // region Atomic tactics with arguments

  "Atomic / Argument Parser" should "parse a built-in tactic" in {
    tacticParser("nil") shouldBe (round trip TactixLibrary.nil)
  }

  it should "accept id as well as closeId" in {
    tacticParser("closeId(-1, 1)") shouldBe (round trip TactixLibrary.closeId(-1, 1))
    tacticParser("id") shouldBe (round trip TactixLibrary.id)
  }

  it should "parse a built-in tactic with arguments" in {
    tacticParser("cut(\"1=1\")") shouldBe (round trip TactixLibrary.cut("1=1".asFormula))
  }

  it should "parse a built-in argument with an absolute top-level postion" in {
    tacticParser("andR(1)") shouldBe (round trip andR(1))
  }

  it should "parse a built-in argument with an absolute non-top-level postion" in {
    tacticParser("boxAnd(1.1)") shouldBe (round trip HilbertCalculus.boxAnd(Fixed(1, List(1), None, exact = true)))
  }

  it should "parse a built-in argument with a position locator" in {
    tacticParser("boxAnd('L)") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindLFirst))
  }

  it should "parse a built-in argument with a searchy position locator" in {
    tacticParser("boxAnd('L==\"[x:=2;](x>0&x>1)\")") shouldBe (round trip HilbertCalculus
      .boxAnd(Find.FindLPlain("[x:=2;](x>0&x>1)".asFormula)))
  }

  it should "parse a built-in argument with a searchy sub-position locator" in {
    tacticParser("boxAnd('L==\"[y:=3;]#[x:=2;](x>0&x>1)#\")") shouldBe (round trip HilbertCalculus
      .boxAnd(Find.FindLPlain("[y:=3;][x:=2;](x>0&x>1)".asFormula, PosInExpr(1 :: Nil))))
    BellePrettyPrinter(
      tacticParser("boxAnd('L==\"[y:=3;]#[x:=2;](x>0&x>1)#\")")
    ) shouldBe "boxAnd('L==\"[y:=3;]#[x:=2;](x>0&x>1)#\")"
  }

  it should "parse a built-in argument with a searchy formula sub-position locator in new notation" in {
    tacticParser("boxAnd('L==\"[y:=3;]#[x:=2;](x>0&x>1)#\")") shouldBe (round trip HilbertCalculus
      .boxAnd(Find.FindLPlain("[y:=3;][x:=2;](x>0&x>1)".asFormula, PosInExpr(1 :: Nil))))
  }

  it should "parse a built-in argument with a searchy term sub-position locator in new notation" in {
    tacticParser("simplify('L==\"[x:=2;](x>#0+0#&x>1)\")") shouldBe (round trip SimplifierV3
      .simplify(Find.FindLPlain("[x:=2;](x>0+0&x>1)".asFormula, PosInExpr(1 :: 0 :: 1 :: Nil))))
  }

  it should "parse a built-in argument with a searchy program sub-position locator in new notation" in {
    tacticParser("simplify('L==\"[#x:=2+0;#y:=3;](x>0&x>1)\")") shouldBe (round trip SimplifierV3
      .simplify(Find.FindLPlain("[x:=2+0;y:=3;](x>0&x>1)".asFormula, PosInExpr(0 :: 0 :: Nil))))
    BellePrettyPrinter(
      SimplifierV3.simplify(Find.FindLPlain("[x:=2+0;y:=3;](x>0&x>1)".asFormula, PosInExpr(0 :: 0 :: Nil)))
    ) shouldBe "simplify('L==\"[#x:=2+0;#y:=3;](x>0&x>1)\")"
  }

  it should "parse a built-in argument with a searchy term sub-position locator in new notation (term occurs thrice)" in {
    // tacticParser("simplify('L==\"[x:=#1+0#;](x>1+0&x>1+0)\")") shouldBe (round trip SimplifierV3.simplify(Find.FindLPlain("[x:=1+0;](x>1+0&x>1+0)".asFormula, PosInExpr(0::1::Nil))))
    tacticParser("simplify('L==\"[x:=1+0;](x>#1+0#&x>1+0)\")") shouldBe (round trip SimplifierV3
      .simplify(Find.FindLPlain("[x:=1+0;](x>1+0&x>1+0)".asFormula, PosInExpr(1 :: 0 :: 1 :: Nil))))
    tacticParser("simplify('L==\"[x:=1+0;](x>1+0&x>#1+0#)\")") shouldBe (round trip SimplifierV3
      .simplify(Find.FindLPlain("[x:=1+0;](x>1+0&x>1+0)".asFormula, PosInExpr(1 :: 1 :: 1 :: Nil))))
  }

  it should "correctly parenthesize postconditions with a searchy formula sub-position locator in new notation" in {
    tacticParser("trueAnd('L==\"[x:=2;](#true&x>1#)\")") shouldBe (round trip TactixLibrary
      .useAt(Ax.trueAnd)(Find.FindLPlain("[x:=2;](true&x>1)".asFormula, PosInExpr(1 :: Nil))))
    tacticParser("trueAnd('L==\"[x:=2;]#(true&x>1)#\")") shouldBe (round trip TactixLibrary
      .useAt(Ax.trueAnd)(Find.FindLPlain("[x:=2;](true&x>1)".asFormula, PosInExpr(1 :: Nil))))
    // @note allow more concise notation with # forming parentheses
    tacticParser("trueAnd('L==\"[x:=2;]#true&x>1#\")") shouldBe (round trip TactixLibrary
      .useAt(Ax.trueAnd)(Find.FindLPlain("[x:=2;](true&x>1)".asFormula, PosInExpr(1 :: Nil))))
    tacticParser("trueAnd('L==\"(true&x>1)&[x:=2;]#true&x>1#\")") shouldBe (round trip TactixLibrary
      .useAt(Ax.trueAnd)(Find.FindLPlain("(true&x>1)&[x:=2;](true&x>1)".asFormula, PosInExpr(1 :: 1 :: Nil))))
  }

  it should "correctly parenthesize programs with a searchy formula sub-position locator in new notation" in {
    tacticParser("chase('L==\"[{#x:=1; ++ x:=2;#};ode;]x>1\")") shouldBe (round trip TactixLibrary
      .chase(Find.FindLPlain("[{x:=1; ++ x:=2;};ode;]x>1".asFormula, PosInExpr(0 :: 0 :: Nil))))
    tacticParser("chase('L==\"[#{x:=1; ++ x:=2;}#;ode;]x>1\")") shouldBe (round trip TactixLibrary
      .chase(Find.FindLPlain("[{x:=1; ++ x:=2;};ode;]x>1".asFormula, PosInExpr(0 :: 0 :: Nil))))
    // @note allow more concise notation with # forming braces
    tacticParser("chase('L==\"[#x:=1; ++ x:=2;#;ode;]x>1\")") shouldBe (round trip TactixLibrary
      .chase(Find.FindLPlain("[{x:=1; ++ x:=2;};ode;]x>1".asFormula, PosInExpr(0 :: 0 :: Nil))))
    tacticParser("chase('L==\"[{x:=1; ++ x:=2;};#x:=1; ++ x:=2;#;ode;]x>1\")") shouldBe (round trip TactixLibrary
      .chase(Find.FindLPlain("[{x:=1; ++ x:=2;};{x:=1; ++ x:=2;};ode;]x>1".asFormula, PosInExpr(0 :: 1 :: 0 :: Nil))))
  }

  it should "parse a built-in argument with a searchy unification position locator" in {
    tacticParser("boxAnd('L~=\"[x:=2;](x>0&x>1)\")") shouldBe (round trip HilbertCalculus
      .boxAnd(Find.FindLMatch("[x:=2;](x>0&x>1)".asFormula)))
  }

  it should "parse a built-in argument with a check position locator" in {
    tacticParser("boxAnd(2==\"[x:=2;](x>0&x>1)\")") shouldBe (round trip HilbertCalculus
      .boxAnd(Fixed(2, Nil, Some("[x:=2;](x>0&x>1)".asFormula))))
  }

  it should "parse a built-in argument with a unification check position locator" in {
    tacticParser("boxAnd(2~=\"[x:=2;](x>0&x>1)\")") shouldBe (round trip HilbertCalculus
      .boxAnd(Fixed(2, Nil, Some("[x:=2;](x>0&x>1)".asFormula), exact = false)))
  }

  it should "parse a built-in argument with a 'R position locator" in {
    tacticParser("boxAnd('R)") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindRFirst))
  }

  it should "parse a built-in argument with a 'Rlast position locator" in {
    tacticParser("boxAnd('Rlast)") shouldBe (round trip HilbertCalculus.boxAnd(LastSucc(0)))
  }

  it should "parse a built-in argument with a 'Rlast subposition locator" in {
    tacticParser("boxAnd('Rlast.1)") shouldBe (round trip HilbertCalculus.boxAnd(LastSucc(0, PosInExpr(1 :: Nil))))
  }

  it should "parse a built-in argument with a 'Llast position locator" in {
    tacticParser("boxAnd('Llast)") shouldBe (round trip HilbertCalculus.boxAnd(LastAnte(0)))
  }

  it should "parse a built-in argument with a 'Llast subposition locator" in {
    tacticParser("boxAnd('Llast.0.1)") shouldBe (round trip HilbertCalculus
      .boxAnd(LastAnte(0, PosInExpr(0 :: 1 :: Nil))))
  }

  it should "parse a built-in tactic that takes a whole list of arguments" in {
    tacticParser("diffInvariant(\"1=1\", 1)") shouldBe (round trip TactixLibrary.diffInvariant("1=1".asFormula)(1))
  }

  it should "Parse a loop tactic and print it back out" in {
    tacticParser("loop(\"1=1\", 1)") shouldBe (round trip TactixLibrary.loop("1=1".asFormula)(1))
  }

  it should "parse a tactic with optional argument specified" in {
    val t = TactixLibrary.discreteGhost("5".asTerm, Some("x".asVariable))(1)
    tacticParser("discreteGhost(\"5\", \"x\", 1)") shouldBe (round trip t)
  }

  it should "parse a tactic without optional argument specified" in {
    val t = TactixLibrary.discreteGhost("5".asTerm, None)(1)
    tacticParser("discreteGhost(\"5\", 1)") shouldBe (round trip t)
  }

  it should "parse OptionArg arguments when option unspecified" in {
    val s = "dbx(1)"
    val t = tacticParser(s)
    tacticParser(s) shouldBe (round trip t)
  }

  it should "parse OptionArg arguments with option specified" in {
    val s = "dbx(\"x\", 1)"
    val t = tacticParser(s)
    tacticParser(s) shouldBe (round trip t)
  }

  it should "parse a tactic without sole list argument specified" in {
    tacticParser("dC(\"nil\", 1)") shouldBe (round trip TactixLibrary.dC(List.empty)(1))
    tacticParser("dC(1)") shouldBe tacticParser("dC(\"nil\", 1)")
  }

  it should "parse nested arguments" in {
    // @note new syntax needs escaping inner " for nesting
    tacticParser("""pending("loop(\"x>=0\", 1)")""") shouldBe (round trip DebuggingTactics.pending("loop(\"x>=0\", 1)"))
  }

  it should "parse nested arguments with line breaks" in {
    val s = "pending(\"<(\n nil,\n nil\n, nil)\")"
    val t = tacticParser(s)
    tacticParser(s) shouldBe (round trip t)
    tacticParser("pending(\"<(\n nil,\n nil\n, nil)\")") shouldBe (round trip t)
  }

  // endregion

  // region Sequential combinator

  "Sequential parser" should "parse e; e" in {
    val result = tacticParser("andR(1); andR(2)").asInstanceOf[SeqTactic]
    result.seq should contain theSameElementsInOrderAs List(andR(1), andR(2))
    result shouldBe (round trip result)
  }

  it should "parse n-ary seq -- e; e; e parses to Seq(e, e, e)" in {
    val result = tacticParser("andR(1) & andR(2) & andR(3)").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(andR(1), andR(2), andR(3))
  }

  it should "parse n-ary seq when there are a bunch of parens" in {
    val result = tacticParser("(andR(1)); (andR(2)); (andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(andR(1), andR(2), andR(3))
  }

  it should "parse e; (e; e)" in {
    val result = tacticParser("andR(1); (andR(2); andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(andR(1), SeqTactic(andR(2), andR(3)))
  }

  it should "parse e; e; e" in {
    val result = tacticParser("andR(1); andR(2); andR(3)").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(andR(1), andR(2), andR(3))
  }

  it should "parse (e; e); e" in {
    val result = tacticParser("(andR(1); andR(2)); andR(3)").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(SeqTactic(andR(1), andR(2)), andR(3))
  }

  it should "parse compositions of things that parse to partials" in {
    val tactic = tacticParser("nil; nil").asInstanceOf[SeqTactic]
    tactic shouldBe (round trip tactic)
    tactic.seq should contain theSameElementsInOrderAs List(nil, nil)
  }

  it should "print anonymous tactics empty and reparse without them" in {
    val t1 = tacticParser(BellePrettyPrinter(TactixLibrary.assertT(_ => false, "Fail") & implyR(1)))
    t1 shouldBe implyR(1)
    BellePrettyPrinter(t1) shouldBe "implyR(1)"

    val t2 = tacticParser(BellePrettyPrinter(implyR(1) & TactixLibrary.assertT(_ => false, "Fail")))
    t2 shouldBe implyR(1)
    BellePrettyPrinter(t2) shouldBe "implyR(1)"

    BellePrettyPrinter(
      TactixLibrary.assertT(_ => true, "Succeed") & TactixLibrary.assertT(_ => false, "Fail")
    ) shouldBe ""
    BellePrettyPrinter(
      implyR(1) & TactixLibrary.assertT(_ => true, "Succeed") & andL(-1)
    ) shouldBe "implyR(1) ; andL(-1)"
  }

  it should "parse simple assert" in {
    tacticParser("""assert("x>0", "Unexpected", 1)""") shouldBe assertE("x>0".asExpr, "Unexpected")(1)
  }

  // endregion

  // region Either combinator

  "Either parser" should "parse e | e" in {
    val result = tacticParser("andR(1) | andR(2)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(andR(1), andR(2))
  }

  it should "parse n-ary either -- e | e | e parses to Either(e, e, e)" in {
    val result = tacticParser("andR(1) | andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(andR(1), andR(2), andR(3))
  }

  it should "parse n-ary either when there are a bunch of parens" in {
    val result = tacticParser("(andR(1)) | (andR(2)) | (andR(3))").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(andR(1), andR(2), andR(3))
  }

  it should "parse e | (e | e)" in {
    val result = tacticParser("andR(1) | (andR(2) | andR(3))").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(andR(1), EitherTactic(andR(2), andR(3)))
  }

  it should "parse (e | e) | e" in {
    val result = tacticParser("(andR(1) | andR(2)) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(EitherTactic(andR(1), andR(2)), andR(3))
  }

  it should "parse e; b | c" in {
    val result = tacticParser("andR(1); andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(SeqTactic(andR(1), andR(2)), andR(3))
  }

  it should "parse e | b; c" in {
    val result = tacticParser("andR(1) | andR(2); andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(andR(1), SeqTactic(andR(2), andR(3)))
  }

  // endregion

  // region Branching combinator

  "Branch combinator parser" should "parse e; <(e,e)" in {
    val result = tacticParser("andR(1); <(andR(2), andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(andR(1), BranchTactic(Seq(andR(2), andR(3))))
  }

  it should "print indented" in {
    BellePrettyPrinter(tacticParser("andR(1); <(andR(2), andR(3))")) shouldBe
      """andR(1) ; <(
        |  andR(2),
        |  andR(3)
        |)""".stripMargin

    BellePrettyPrinter(tacticParser("andR(1); <(andR(2); <(andR(3), andR(4)), andR(5))")) shouldBe
      """andR(1) ; <(
        |  andR(2) ; <(
        |    andR(3),
        |    andR(4)
        |  ),
        |  andR(5)
        |)""".stripMargin
  }

  it should "not parse e; <()" in {
    the[ParseException] thrownBy tacticParser("andR(1); <()") should have message
      """1:12 Error parsing <(tactic,tactic,...) at 1:10
        |Found:    ")" at 1:12
        |Expected: (tactic|tactic.rep(2) | string.rep(2))
        |Hint: Try ("?" | "<" | "(" | "doall" | "partial" | "let" | "tactic" | "USMatch" | [a-zA-Z] | "\"")"""
        .stripMargin
  }

  it should "report an error on e; <(e)" in {
    the[ParseException] thrownBy tacticParser("andR(1); <(andR(1))") should
      (have message """1:9 Branch tactic has only a single child
                      |Found:    <unknown> at 1:9
                      |Expected: <unknown>""".stripMargin
        or have message
        """1:19 Error parsing <(tactic,tactic,...) at 1:10
          |Found:    ")" at 1:19
          |Expected: ("*" | "+" | blank | [;&] | "|" | ",")
          |Hint: Try ("*" | "+" | [ \t\r\n] | [;&] | "|" | ",")""".stripMargin)
  }

  it should "parse as case tactic when labels are present" in {
    val result @ SeqTactic(loop +: CaseTactic(children) +: Nil) =
      tacticParser("loop(\"x>=0\",1); <(\"Init\": andL(-1), \"Step\": andL(-2), \"Post\": andL(-3))")
    result shouldBe (round trip result)
    loop shouldBe TactixLibrary.loop("x>=0".asFormula)(1)
    children should contain theSameElementsAs List(
      BelleLabels.initCase -> andL(-1),
      BelleLabels.indStep -> andL(-2),
      BelleLabels.useCase -> andL(-3),
    )
  }

  it should "print as cases indented" in {
    BellePrettyPrinter(
      tacticParser("loop(\"x>=0\",1); <(\"Init\": andL(-1), \"Step\": andL(-2), \"Post\": andL(-3))")
    ) shouldBe
      """loop("x>=0", 1) ; <(
        |  "Init": andL(-1),
        |  "Step": andL(-2),
        |  "Post": andL(-3)
        |)""".stripMargin
    BellePrettyPrinter(
      tacticParser("""loop("x>=0",1); <("Init":cut("x>=0");<("Use":nil,"Show":nil), "Step":nil, "Post":nil)""")
    ) shouldBe
      """loop("x>=0", 1) ; <(
        |  "Init": cut("x>=0") ; <(
        |      "Use": nil,
        |      "Show": nil
        |    ),
        |  "Step": nil,
        |  "Post": nil
        |)""".stripMargin
  }

  it should "parse as case tactic when labels are present on nested tactics" in {
    val result @ SeqTactic(loop +: CaseTactic(children) +: Nil) = tacticParser(
      "loop(\"x>=0\",1); <(\"Init\": andL(-1); orL(-1), \"Step\": orL(-2); <(andL(-2), orR(2)), \"Post\": andL(-3) using \"x=2\" | andR(3))"
    )
    result shouldBe (round trip result)
    loop shouldBe TactixLibrary.loop("x>=0".asFormula)(1)
    children should contain theSameElementsAs List(
      BelleLabels.initCase -> (andL(-1) & orL(-1)),
      BelleLabels.indStep -> (orL(-2) < (andL(-2), orR(2))),
      BelleLabels.useCase -> (Using("x=2".asFormula :: Nil, andL(-3)) | andR(3)),
    )
  }

  it should "parse nested case tactics" in {
    val result @ SeqTactic(loop +: CaseTactic(children) +: Nil) = tacticParser(
      "loop(\"x>=0\",1); <(\"Init\": andL(-1), \"Step\": orL(-2); <(\"LHS\": andL(-2), \"RHS\": orR(2)), \"Post\": andL(-3))"
    )
    result shouldBe (round trip result)
    loop shouldBe TactixLibrary.loop("x>=0".asFormula)(1)
    children should contain theSameElementsAs List(
      BelleLabels.initCase -> andL(-1),
      BelleLabels.indStep -> orL(-2).switch("LHS".asLabel -> andL(-2), "RHS".asLabel -> orR(2)),
      BelleLabels.useCase -> andL(-3),
    )
  }

  it should "require case labels on all branches" in {
    the[ParseException] thrownBy tacticParser(
      "loop(\"x>=0\",1); <(andL(-1), \"Step\": andL(-2), \"Post\": andL(-3))"
    ) should
      (have message """1:19 Not all branches have labels. Please provide labels for the branches marked <missing>
                      |  "<missing>": andL(-1),
                      |  "Step": andL(-2),
                      |  "Post": andL(-3)
                      |resulting from
                      |loop("x>=0", 1)
                      |Found:    <missing> at 1:19
                      |Expected: "A label":""".stripMargin
      // @todo improve error message
        or have message
        """1:29 Error parsing baseTac at 1:29
          |Found:    "\"Step\": an" at 1:29
          |Expected: ("?" | <(tactic,tactic,...) | (tactic) | "doall" | "partial" | "let" | "tactic" | "USMatch" | tactic(...) | atomicTactic)
          |Hint: Try ("?" | "<" | "(" | "doall" | "partial" | "let" | "tactic" | "USMatch" | [a-zA-Z])""".stripMargin)
  }

  // endregion

  // region Kleene Star Comabinator

  "Kleene star parser" should "parse e*" in {
    val tactic = tacticParser("andR(1)*").asInstanceOf[SaturateTactic]
    tactic shouldBe (round trip tactic)
    tactic.child shouldBe andR(1)
  }

  it should "parse (e&e)*" in {
    val tactic = tacticParser("(andR(1) & andR(2))*").asInstanceOf[SaturateTactic]
    tactic shouldBe (round trip tactic)
    tactic.child.asInstanceOf[SeqTactic].seq should contain theSameElementsInOrderAs List(andR(1), andR(2))
  }

  it should "get precedence right" in {
    val tactic = tacticParser("andR(1) & andR(2)*")
    tactic shouldBe (round trip tactic)
    tactic shouldBe a[SeqTactic]
    tactic shouldBe andR(1) & SaturateTactic(andR(2))
  }

  it should "parse fully parenthesized" in {
    val tactic = tacticParser("andR(1) & (andR(2)*)")
    tactic shouldBe (round trip andR(1) & SaturateTactic(andR(2)))
  }

  "NTIMES repeat combinator parser" should "parse e*22" in {
    val tactic = tacticParser("andR(1)*22").asInstanceOf[RepeatTactic]
    tactic shouldBe (round trip tactic)
    tactic.child shouldBe andR(1)
    tactic.times shouldBe 22
  }

  it should "get precedence right" in {
    val tactic = tacticParser("andR(1) & andR(2)*3")
    tactic shouldBe a[SeqTactic]
    tactic shouldBe (round trip andR(1) & (andR(2) * 3))
  }

  "saturate parser" should "parse e+" in {
    val tactic = tacticParser("andR(1)+").asInstanceOf[SeqTactic]
    tactic shouldBe (round trip tactic)
    tactic.seq should contain theSameElementsInOrderAs List(andR(1), SaturateTactic(andR(1)))
  }

  it should "get precedence right" in {
    val tactic = tacticParser("andR(1); andR(2)*")
    tactic shouldBe a[SeqTactic]
    tactic shouldBe (round trip andR(1) & SaturateTactic(andR(2)))
  }

  "doall combinator parser" should "parse doall(closeId)" in {
    val tactic = tacticParser("doall(id)")
    tactic shouldBe (round trip OnAll(TactixLibrary.id))
  }

  it should "parse combined tactics with parameters doall(closeId | closeTrue | andL(1))" in {
    val tactic = tacticParser("doall(id | closeT | andL(1))")
    tactic shouldBe (round trip OnAll(TactixLibrary.id | (TactixLibrary.closeT | TactixLibrary.andL(1))))
  }

  "Optional combinator" should "parse ?(closeId)" in {
    val tactic = tacticParser("?(id)")
    tactic shouldBe (round trip Idioms.?(TactixLibrary.id))
  }

  it should "bind stronger than seq. combinator" in {
    val tactic = tacticParser("andR(1) & ?(id)")
    tactic shouldBe (round trip SeqTactic(Seq(andR(1), Idioms.?(TactixLibrary.id))))
  }

  it should "bind stronger than alt. combinator" in {
    val tactic = tacticParser("andR(1) | ?(id)")
    tactic shouldBe (round trip EitherTactic(Seq(andR(1), Idioms.?(TactixLibrary.id))))
  }

  it should "bind weaker than saturation" in {
    // @note this is debatable, but was easier to implement the moment
    val tactic = tacticParser("?(andR(1))*")
    tactic shouldBe (round trip Idioms.?(SaturateTactic(andR(1))))
  }

  it should "work in the beginning of a branch" in {
    val tactic = tacticParser("andR(1) & <(?(id), ?(orR(1)))")
    tactic shouldBe (round trip andR(1) & Idioms
      .<(Idioms.?(TactixLibrary.id.asInstanceOf[BelleExpr]), Idioms.?(TactixLibrary.orR(1))))
  }

  // endregion

  // region Comma lists

  "comma separated list folding" should "work" in {
    val t = "nil; <(nil, nil)"
    tacticParser(t) shouldBe (round trip tacticParser(t))
  }

  it should "work for a tactic (e)" in {
    val t = "nil; <((nil), nil)"
    tacticParser(t) shouldBe (round trip tacticParser(t))
  }

  it should "work for a tactic (e) in the final position" in {
    val t = "nil; <(nil, (nil))"
    tacticParser(t) shouldBe (round trip tacticParser(t))
  }

  it should "work on tactic that caused original bug" in withMathematica { _ =>
    val t = """implyR(1);
              |loop("x<=m", 1); <(
              |  QE,
              |  QE,
              |  composeb(1); choiceb(1); andR(1); <(
              |    assignb(1); solve(1); nil,
              |    testb(1); implyR(1); solve(1); nil
              |  )
              |)""".stripMargin
    tacticParser(t) shouldBe (round trip tacticParser(t))
  }

  // endregion

  // region Partial tactics

  "partial tactic parser" should "parse partial(e)" in {
    val tactic = tacticParser("partial(andR(1))").asInstanceOf[PartialTactic]
    tactic shouldBe (round trip tactic)
    tactic.child shouldBe andR(1)
  }

  it should "parse e partial" in {
    val tactic = tacticParser("andR(1) partial").asInstanceOf[PartialTactic]
    tactic shouldBe (round trip tactic)
    tactic.child shouldBe andR(1)
  }

  it should "parse with expected precedence" in {
    tacticParser("andL(-1) & (andR(1) partial)") shouldBe (round trip SeqTactic(
      Seq(TactixLibrary.andL(-1), PartialTactic(andR(1)))
    ))
    tacticParser("andL(-1) & andR(1) partial") shouldBe (round trip PartialTactic(
      SeqTactic(Seq(TactixLibrary.andL(-1), andR(1)))
    ))
  }

  // endregion

  // region Done tactics

  "done tactic parser" should "parse closeId & done" in {
    val tactic = tacticParser("id & done")
    tactic shouldBe (round trip TactixLibrary.id & TactixLibrary.done)
  }

  it should "parse done" in {
    val tactic = tacticParser("done")
    tactic shouldBe (round trip TactixLibrary.done)
  }

  it should "parse empty-argument done" in {
    val tactic = tacticParser("done()")
    tactic shouldBe (round trip TactixLibrary.done)
  }

  it should "parse done with message" in {
    val tactic = tacticParser("done(\"Message\")")
    tactic shouldBe (round trip DebuggingTactics.done("Message", None))
  }

  it should "parse done with message and lemma name" in {
    val tactic = tacticParser("done(\"Message\",\"My Lemma\")")
    tactic shouldBe (round trip DebuggingTactics.done("Message", Some("My Lemma")))
  }

  it should "parse in a branch" in {
    val tactic = tacticParser("andR(1) & <(id & done, done)")
    tactic shouldBe (round trip andR(1) & Idioms.<(TactixLibrary.id & TactixLibrary.done, TactixLibrary.done))
  }

  // endregion

  // region let

  "let tactic parser" should "parse a simple example" in {
    val tactic = tacticParser("let (\"a()=a\") in (done)")
    tactic shouldBe (round trip Let("a()".asTerm, "a".asTerm, TactixLibrary.done))
  }

  it should "parse dI" in withMathematica { _ =>
    val inner = """
                  |DI(1) ; implyR(1) ; andR(1) ; <(
                  |  QE,
                  |  derive(1.1) ; DE(1) ; Dassignb(1.1) ; GV(1) ; QE
                  |)
      """.stripMargin
    val tactic = tacticParser(s"""let ("a()=a") in ($inner)""")
    tactic shouldBe (round trip Let("a()".asTerm, "a".asTerm, round trip tacticParser(inner)))
  }

  it should "parse let as part of a larger tactic" in {
    val tactic = tacticParser("implyR(1) ; let (\"a()=a\") in (nil) ; id")
    tactic shouldBe (round trip TactixLibrary
      .implyR(1) & (Let("a()".asTerm, "a".asTerm, TactixLibrary.nil) & TactixLibrary.id))
  }

  "def tactic parser" should "parse a simple example" in {
    val tactic = tacticParser("tactic t as (assignb('R))")
    tactic shouldBe (round trip DefTactic("t", TactixLibrary.assignb(Symbol("R"))))
  }

  it should "print indented" in {
    BellePrettyPrinter(tacticParser("tactic t as (assignb('R))")) shouldBe
      """tactic t as (
        |  assignb('R)
        |)""".stripMargin
    BellePrettyPrinter(tacticParser("""tactic t as (cut("x>=0"); <(nil,nil))""")) shouldBe
      """tactic t as (
        |  cut("x>=0") ; <(
        |    nil,
        |    nil
        |  )
        |)""".stripMargin
  }

  it should "parse multipe tactic defs" in {
    val tactic = tacticParser("tactic t as (assignb('R)) ; tactic s as (implyR(1))")
    tactic shouldBe (round trip DefTactic("t", TactixLibrary.assignb(Symbol("R"))) & DefTactic(
      "s",
      TactixLibrary.implyR(1),
    ))
  }

  it should "parse a simple example with application" in {
    val tactic = tacticParser("tactic t as (assignb('R)) ; implyR(1) ; t")
    val tDef = DefTactic("t", TactixLibrary.assignb(Symbol("R")))
    tactic shouldBe (round trip tDef & (TactixLibrary.implyR(1) & ApplyDefTactic(tDef)))
  }

  it should "parse with multiple application" in {
    val tactic = tacticParser("tactic t as (assignb('R)) ; andR(1) ; <(t ; prop ; done, prop ; doall(t))")
    val tDef = DefTactic("t", TactixLibrary.assignb(Symbol("R")))
    tactic shouldBe (round trip tDef & (andR(1) < (
      ApplyDefTactic(tDef) & (TactixLibrary.prop & TactixLibrary.done),
      TactixLibrary.prop & OnAll(ApplyDefTactic(tDef))
    )))
  }

  it should "reject duplicate definitions" in {
    a[ParseException] should be thrownBy tacticParser("tactic t as (assignb('R)) ; tactic t as (implyR(1))")
  }

  it should "FEATURE_REQUEST: scoped definitions" taggedAs TodoTest in {
    val tactic = tacticParser(
      "tactic t as (assignb('R)) ; andR(1) ; <(t ; prop ; done, prop ; doall(tactic t as (unfold) ; t); t)"
    )
    val tDef1 = DefTactic("t", TactixLibrary.assignb(Symbol("R")))
    val tDef2 = DefTactic("t", TactixLibrary.unfoldProgramNormalize)
    tactic shouldBe (round trip tDef1 & (andR(1) < (
      ApplyDefTactic(tDef1) & (TactixLibrary.prop & TactixLibrary.done),
      TactixLibrary.prop & (OnAll(tDef2 & ApplyDefTactic(tDef2)) & ApplyDefTactic(tDef1))
    )))
  }

  it should "allow nested defs" in {
    val tactic = tacticParser("tactic t as (tactic s as (assignb('R)) ; andR(1) ; <(s, s)) ; t")
    val sDef = DefTactic("s", TactixLibrary.assignb(Symbol("R")))
    val tDef = DefTactic("t", sDef & andR(1) < (ApplyDefTactic(sDef), ApplyDefTactic(sDef)))
    tactic shouldBe (round trip tDef & ApplyDefTactic(tDef))
  }

  "Expand" should "parse a simple definition expand" in {
    tacticParser(
      "implyR(1) ; expand(\"f()\")",
      Declaration(Map((Name("f", None), Signature(Some(Unit), Real, None, Right(Some("3*2".asExpr)), UnknownLocation)))),
    ) shouldBe
      TactixLibrary.implyR(1) & expand("f()")
  }

  it should "elaborate variables to functions" in {
    tacticParser(
      "implyR(1) ; expand(\"f\")",
      Declaration(
        scala
          .collection
          .immutable
          .Map(
            (Name("f", None), Signature(Some(Unit), Real, None, Right(Some("g*2".asExpr)), UnknownLocation)),
            (Name("g", None), Signature(Some(Unit), Real, None, Right(Some("3*2".asExpr)), UnknownLocation)),
          )
      ),
    ) shouldBe TactixLibrary.implyR(1) & expand("f")
  }

  it should "elaborate variables to functions in tactic arguments" in {
    val defs = Declaration(
      scala
        .collection
        .immutable
        .Map(
          (Name("f", None), Signature(Some(Unit), Real, None, Right(None), UnknownLocation)),
          (Name("g", None), Signature(Some(Unit), Real, None, Right(Some("1*f".asExpr)), UnknownLocation)),
        )
    )
    tacticParser("hideL('L==\"f=g\")", defs) shouldBe
      TactixLibrary.hideL(Find.FindLDef("f()=g()".asFormula, PosInExpr.HereP, defs ++ TacticReservedSymbols.asDecl))
  }

  it should "elaborate variables to functions per declarations" in {
    val tactic = tacticParser(
      "implyR(1) ; expand(\"f\")",
      Declaration(
        scala
          .collection
          .immutable
          .Map(
            (Name("f", None), Signature(Some(Unit), Real, None, Right(Some("g".asExpr)), UnknownLocation)),
            (Name("g", None), Signature(Some(Unit), Real, None, Right(Some("0".asExpr)), UnknownLocation)),
          )
      ),
    )
    tactic shouldBe TactixLibrary.implyR(1) & expand("f")
  }

  it should "elaborate functions to predicates per declarations" in {
    val tactic = tacticParser(
      "implyR(1) ; expand(\"f\")",
      Declaration(
        scala
          .collection
          .immutable
          .Map(
            (Name("f", None), Signature(Some(Unit), Bool, None, Right(Some("g".asExpr)), UnknownLocation)),
            (Name("g", None), Signature(Some(Unit), Bool, None, Right(Some("3*2>=0".asExpr)), UnknownLocation)),
          )
      ),
    )
    tactic shouldBe TactixLibrary.implyR(1) & expand("f")
  }

  it should "elaborate programconsts to systemconsts" in {
    val defs = Declaration(
      scala
        .collection
        .immutable
        .Map(
          (Name("p", None), Signature(Some(Unit), Bool, None, Right(Some("3*2>=0".asExpr)), UnknownLocation)),
          (Name("a", None), Signature(Some(Unit), Trafo, None, Right(Some("x:=x+1;".asExpr)), UnknownLocation)),
        )
    )
    tacticParser("implyR(1) ; cut(\"[a;]p\")", defs) shouldBe TactixLibrary.implyR(1) & cut("[a{|^@|};]p()".asFormula)
  }

  it should "not collide with expandAll" in { BellePrettyPrinter(tacticParser("expandAll")) shouldBe "expandAll" }

  "ExpandAllDefs" should "expand model definitions with expandAllDefs" in {
    val tactic = tacticParser(
      "expandAllDefs(\"nil\")",
      Declaration(
        scala
          .collection
          .immutable
          .Map(
            // @note UnknownLocation identifies proof definitions, known locations identify model definitions
            (Name("f", None), Signature(Some(Unit), Real, None, Right(Some("g*2".asExpr)), UnknownLocation)),
            (Name("g", None), Signature(Some(Unit), Real, None, Right(Some("4".asExpr)), Region(0, 0, 0, 0))),
          )
      ),
    )
    tactic shouldBe expandAllDefs(Nil)
  }

  it should "expand and elaborate proof definitions in US" in {
    val tactic = tacticParser(
      "US(\"f(x)~>g(x)::nil\"); expandAllDefs(\"nil\")",
      Declaration(
        scala
          .collection
          .immutable
          .Map(
            // @note UnknownLocation identifies proof definitions, known locations identify model definitions
            (
              Name("f", None),
              Signature(Some(Real), Bool, Some(List((Name("x"), Real))), Right(Some("g(x)".asExpr)), UnknownLocation),
            ),
            (
              Name("g", None),
              Signature(Some(Real), Bool, Some(List((Name("x"), Real))), Right(Some("x>0".asExpr)), Region(0, 0, 0, 0)),
            ),
          )
      ),
    )
    tactic shouldBe TactixLibrary.USX(
      SubstitutionPair(
        PredOf(Function("f", None, Real, Bool), DotTerm(Real, Some(0))),
        PredOf(Function("g", None, Real, Bool), DotTerm(Real, Some(0))),
      ) :: Nil
    ) &
      expandAllDefs(Nil)
  }

  it should "not default expand and elaborate model definitions with expandAllDefs" in {
    val tactic = tacticParser(
      """dC("f(x)", 1)""",
      Declaration(
        scala
          .collection
          .immutable
          .Map(
            // @note Known locations identify model definitions
            (
              Name("f", None),
              Signature(Some(Real), Bool, Some(List(Name("x") -> Real)), Right(Some("x>g".asExpr)), Region(0, 0, 0, 0)),
            ),
            (Name("g", None), Signature(Some(Unit), Real, None, Right(None), Region(0, 0, 0, 0))),
          )
      ),
    )
    tactic shouldBe TactixLibrary.dC("f(x)".asFormula)(1)
  }

  it should "not default expand but elaborate model definitions in tactics" in {
    val tactic = tacticParser(
      """dC("x>g", 1)""",
      Declaration(
        scala
          .collection
          .immutable
          .Map(
            // @note Known locations identify model definitions
            (
              Name("f", None),
              Signature(Some(Real), Bool, Some(List(Name("x") -> Real)), Right(Some("x>g".asExpr)), Region(0, 0, 0, 0)),
            ),
            (Name("g", None), Signature(Some(Unit), Real, None, Right(None), Region(0, 0, 0, 0))),
          )
      ),
    )
    tactic shouldBe TactixLibrary.dC("x>g()".asFormula)(1)
  }

  // endregion

  // region argument parser

  "Tactic argument parser" should "parse string arguments" in {
    tacticParser("debug(\"a message\")") shouldBe (round trip DebuggingTactics.debugX("a message"))
    tacticParser("print(\"a message\")") shouldBe (round trip DebuggingTactics.printX("a message"))
  }

  it should "parse formula arguments" in {
    tacticParser("dC(\"x>0\",1)") shouldBe (round trip TactixLibrary.dC("x>0".asFormula)(1))
  }

  it should "parse list formula arguments" in {
    tacticParser("dC(\"x>0 :: y<1 :: nil\",1)") shouldBe (round trip TactixLibrary
      .dC("x>0".asFormula :: "y<1".asFormula :: Nil)(1))
  }

  it should "parse term arguments" in {
    tacticParser("transform(\"x+2\",1)") shouldBe (round trip TactixLibrary.transform("x+2".asTerm)(1))
  }

  it should "parse substitution arguments" in {
    tacticParser("US(\"init(x) ~> x=0\")") shouldBe (round trip TactixLibrary
      .USX(SubstitutionPair("init(._0)".asFormula, "._0=0".asFormula) :: Nil))
  }

  it should "parse list substitution arguments" in {
    tacticParser("US(\"init(x) ~> x=0 :: a;~>{x'=v,t'=1&true} :: nil\")") shouldBe (round trip TactixLibrary.USX(
      SubstitutionPair("init(._0)".asFormula, "._0=0".asFormula) :: SubstitutionPair(
        "a;".asProgram,
        "{x'=v,t'=1}".asProgram,
      ) :: Nil
    ))
  }

  it should "parse mixed arguments" in {
    tacticParser("dG(\"{z'=-1*z+0}\",\"x*z^2=1\",1)") shouldBe (round trip TactixLibrary
      .dG("{z'=-1*z+0}".asProgram, Some("x*z^2=1".asFormula))(1))
  }

  it should "parse predicates in locators" in {
    tacticParser("hideL(1==\"p(x)\")") shouldBe (round trip TactixLibrary.hideL(Fixed(1, Nil, Some("p(x)".asFormula))))
  }

  it should "expand definitions when parsing arguments only when asked to" in {
    inside(tacticParser("MR(\"safeDist()>0\",1)")) { case adpt: AppliedDependentPositionTactic =>
      adpt.pt should have(Symbol("inputs")("safeDist()>0".asFormula :: Nil))
    }

    inside(tacticParser(
      "MR(\"safeDist()>0\",1)",
      Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Right(Some("y".asTerm)), null))),
    )) { case adpt: AppliedDependentPositionTactic =>
      adpt.pt should have(Symbol("inputs")("safeDist()>0".asFormula :: Nil))
    }
  }

  it should "expand definitions in the middle of parsing only when asked to" in {
    val SeqTactic(_ +: (adpt: AppliedDependentPositionTactic) +: Nil) = tacticParser(
      "useLemma(\"Lemma\",\"prop\"); MR(\"safeDist()>0\",1)",
      Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Right(Some("y".asTerm)), null))),
    )
    adpt.pt should have(Symbol("inputs")("safeDist()>0".asFormula :: Nil))
  }

  it should "expand definitions when parsing locators only when asked to" in {
    val defs = "safeDist() ~> y".asDeclaration
    tacticParser("hideL('L==\"s=safeDist()\")") should have(
      Symbol("locator")(Find.FindLPlain("s=safeDist()".asFormula))
    )
    tacticParser("hideL('L==\"s=safeDist()\")", defs) should have(
      Symbol("locator")(Find.FindLDef("s=safeDist()".asFormula, PosInExpr.HereP, defs ++ TacticReservedSymbols.asDecl))
    )
  }

  it should "expand definitions when parsing position check locators only when asked to" in {
    inside(tacticParser("hideL(-2==\"s=safeDist()\")")) { case apt: AppliedPositionTactic =>
      apt.locator shouldBe Fixed(-2, Nil, Some("s=safeDist()".asFormula))
    }

    inside(tacticParser(
      "hideL(-2==\"s=safeDist()\")",
      Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Right(Some("y".asTerm)), null))),
    )) { case apt: AppliedPositionTactic => apt.locator shouldBe Fixed(-2, Nil, Some("s=safeDist()".asFormula)) }
  }

  it should "allow escaped quotation marks in arguments" in {
    tacticParser(""" useLemma("Lemma 1", "dC(\"x>=0\",1)") """) shouldBe
      useLemmaX("Lemma 1", Some("""dC(\"x>=0\",1)"""))
  }

  it should "lex backslash followed by any character" in {
    tacticParser(""" hideR('R=="\exists x x=0") """) shouldBe hideR(Symbol("R"), "\\exists x x=0".asFormula)
    tacticParser(""" hideR('R=="\forall x x^2>=0") """) shouldBe hideR(Symbol("R"), "\\forall x x^2>=0".asFormula)
    the[ParseException] thrownBy tacticParser(""" hideR('R=="\x x^2=1") """) should
      (have message """1:1 Unexpected token cannot be parsed
                      |Found:    \\ at 1:1 to 1:2
                      |Expected: <BeginningOfExpression>""".stripMargin
        or have message
        """1:12 Error parsing shape at 1:10
          |Found:    "\"\x x^2=1\"" at 1:12
          |Expected: escaped expression string
          |Hint: Try escaped expression string""".stripMargin)
  }

  // endregion

  // region Lemmas

  "Using lemmas" should "work in exactly matching open goal" in {
    val f = "x>0&y>1 -> y>1&x>0".asFormula
    val lemma = proveBy(f, TactixLibrary.prop)
    LemmaDBFactory
      .lemmaDB
      .add(new Lemma(lemma, Lemma.requiredEvidence(lemma, Nil), Some(s"user${File.separator}testPropLemma")))
    proveBy(f, "useLemma(\"testPropLemma\")".asTactic) shouldBe Symbol("proved")
  }

  it should "work with tactic adaptation" in {
    val f = "x>0&y>1 -> y>1&x>0".asFormula
    val lemma = proveBy(f, TactixLibrary.prop)
    LemmaDBFactory
      .lemmaDB
      .add(new Lemma(lemma, Lemma.requiredEvidence(lemma, Nil), Some(s"user${File.separator}testPropLemma")))
    proveBy("x>0, y>1, z>2 ==> y>1&x>0".asSequent, "useLemma(\"testPropLemma\", \"prop\")".asTactic) shouldBe Symbol(
      "proved"
    )
  }

  // endregion

  // region New dG syntax

  "new dG syntax" should "round trip ghosts" in {
    "dG(\"y'=1\", 1)"
      .asTactic should (be(dG("y'=1".asFormula, None)(1)) and (print as "dG(\"y'=1\", 1)") and (reparse fromPrint))
    "dG(\"{y'=1}\", \"x*y=5\", 1)".asTactic should (be(dG("{y'=1}".asProgram, Some("x*y=5".asFormula))(1)) and (
      print as "dG(\"{y'=1}\", \"x*y=5\", 1)"
    ) and (reparse fromPrint))
    "dG(\"y'=0*y+1\", \"x*y^2=1\", 1)".asTactic should (be(dG("y'=0*y+1".asFormula, Some("x*y^2=1".asFormula))(1)) and (
      print as "dG(\"y'=0*y+1\", \"x*y^2=1\", 1)"
    ) and (reparse fromPrint))
    "dG(\"y'=1/2*y\", 1)".asTactic should (
      be(dG("y'=1/2*y".asFormula, None)(1)) and (print as "dG(\"y'=1/2*y\", 1)") and (reparse fromPrint)
    )
    "dG(\"{y'=1/2*y}\", \"x*y^2=1\", 1)".asTactic should (be(
      dG("{y'=1/2*y}".asProgram, Some("x*y^2=1".asFormula))(1)
    ) and (print as "dG(\"{y'=1/2*y}\", \"x*y^2=1\", 1)") and (reparse fromPrint))
  }

  // endregion

  // region interpreted functions

  "Interpreted function" should "be parsed as arguments in cuts" in {
    // @note don't print interpretation because surrounding archive is expected to provide the definition
    "cut(\"exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1\")".asTactic should (be(
      cut("exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1".asFormula)
    )
      and (print as "cut(\"exp(x)<=1\")")
      and (reparse fromPrint))
  }

  it should "be parsed in position locators" in {
    // @note don't print because surrounding archive is expected to provide the definition
    "hideR('R==\"exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1\")"
      .asTactic should (be(hideR(
      Find.FindRPlain("exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1".asFormula)
    ))
      and (print as "hideR('R==\"exp(x)<=1\")")
      and (reparse fromPrint))
  }

  // endregion
}
