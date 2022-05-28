package bellerophon.pptests

import java.io.File
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Name, ParseException, Region, Signature, UnknownLocation}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

import scala.language.postfixOps
import org.scalatest.Inside._
import org.scalatest.matchers.MatchResult

/**
  * Very simple positive unit tests for the Bellerophon parser. Useful for TDD and bug isolation but probably not
  * so useful for anything else.
  *
  * @note It may be useful to turn on BelleParser.DEBUG if you're actually debugging.
  * @author Nathan Fulton
  */
@UsualTest
class SimpleBelleParserTests extends TacticTestBase(registerAxTactics=Some("z3")) {
  private object round {
    def trip(t: BelleExpr): BelleExpr = { roundTrip(t) shouldBe t; t }
    def roundTrip(t: BelleExpr): BelleExpr = BelleParser(BellePrettyPrinter(t))
  }

  private object print {
    def as(right: String): org.scalatest.matchers.Matcher[BelleExpr] = new org.scalatest.matchers.Matcher[BelleExpr]() {
      def apply(left: BelleExpr): MatchResult = {
        MatchResult(
          BellePrettyPrinter(left) == right,
          "pretty-printing tactic failed", //@note can't print tactics since {} are reserved characters in match result message
          "pretty-printing succeeded",
          Vector(left, right)
        )
      }
      override def toString: String = "Print as " + right
    }
  }

  private object reparse {
    def fromPrint: org.scalatest.matchers.Matcher[BelleExpr] = new org.scalatest.matchers.Matcher[BelleExpr]() {
      def apply(left: BelleExpr): MatchResult = {
        MatchResult(
          BelleParser(BellePrettyPrinter(left)) == left,
          "re-parsing pretty-printed tactic failed",
          "re-parsing pretty-printed tactic succeeded",
          Vector(left)
        )
      }
      override def toString: String = "reparse"
    }
  }

  //region Atomic tactics with arguments

  "Atomic / Argument Parser" should "parse a built-in tactic" in {
    BelleParser("nil") shouldBe (round trip TactixLibrary.nil)
  }
  
  it should "accept id as well as closeId" in {
    BelleParser("closeId") shouldBe (round trip TactixLibrary.closeId)
    BelleParser("id") shouldBe (round trip TactixLibrary.id)
  }

  it should "parse a built-in tactic with arguments" in {
    BelleParser("cut({`1=1`})") shouldBe (round trip TactixLibrary.cut("1=1".asFormula))
  }

  it should "parse a built-in argument with an absolute top-level postion" in {
    BelleParser("andR(1)") shouldBe (round trip TactixLibrary.andR(1))
  }

  it should "parse a built-in argument with an absolute non-top-level postion" in {
    val pos = BelleParser.parsePositionLocator("1.1", UnknownLocation, None, exact=true, Declaration(Map.empty))
    BelleParser("boxAnd(1.1)") shouldBe (round trip HilbertCalculus.boxAnd(pos))
  }

  it should "parse a built-in argument with a position locator" in {
    BelleParser("boxAnd('L)") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindLFirst))
  }

  it should "parse a built-in argument with a searchy position locator" in {
    BelleParser("boxAnd('L=={`[x:=2;](x>0&x>1)`})") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindLPlain("[x:=2;](x>0&x>1)".asFormula)))
  }

  it should "parse a built-in argument with a searchy sub-position locator" in {
    BelleParser("boxAnd('L.1==\"[y:=3;][x:=2;](x>0&x>1)\")") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindLPlain("[y:=3;][x:=2;](x>0&x>1)".asFormula, PosInExpr(1::Nil))))
    BellePrettyPrinter(BelleParser("boxAnd('L.1==\"[y:=3;][x:=2;](x>0&x>1)\")")) shouldBe "boxAnd('L==\"[y:=3;]#[x:=2;](x>0&x>1)#\")"
  }

  it should "parse a built-in argument with a searchy formula sub-position locator in new notation" in {
    BelleParser("boxAnd('L==\"[y:=3;]#[x:=2;](x>0&x>1)#\")") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindLPlain("[y:=3;][x:=2;](x>0&x>1)".asFormula, PosInExpr(1::Nil))))
  }

  it should "parse a built-in argument with a searchy term sub-position locator in new notation" in {
    BelleParser("simplify('L==\"[x:=2;](x>#0+0#&x>1)\")") shouldBe (round trip SimplifierV3.simplify(Find.FindLPlain("[x:=2;](x>0+0&x>1)".asFormula, PosInExpr(1::0::1::Nil))))
  }

  it should "parse a built-in argument with a searchy program sub-position locator in new notation" in {
    BelleParser("simplify('L==\"[#x:=2+0;#y:=3;](x>0&x>1)\")") shouldBe (round trip SimplifierV3.simplify(Find.FindLPlain("[x:=2+0;y:=3;](x>0&x>1)".asFormula, PosInExpr(0::0::Nil))))
    BellePrettyPrinter(SimplifierV3.simplify(Find.FindLPlain("[x:=2+0;y:=3;](x>0&x>1)".asFormula, PosInExpr(0::0::Nil)))) shouldBe "simplify('L==\"[#x:=2+0;#y:=3;](x>0&x>1)\")"
  }

  it should "parse a built-in argument with a searchy term sub-position locator in new notation (term occurs thrice)" in {
    BelleParser("simplify('L==\"[x:=#1+0#;](x>1+0&x>1+0)\")") shouldBe (round trip SimplifierV3.simplify(Find.FindLPlain("[x:=1+0;](x>1+0&x>1+0)".asFormula, PosInExpr(0::1::Nil))))
    BelleParser("simplify('L==\"[x:=1+0;](x>#1+0#&x>1+0)\")") shouldBe (round trip SimplifierV3.simplify(Find.FindLPlain("[x:=1+0;](x>1+0&x>1+0)".asFormula, PosInExpr(1::0::1::Nil))))
    BelleParser("simplify('L==\"[x:=1+0;](x>1+0&x>#1+0#)\")") shouldBe (round trip SimplifierV3.simplify(Find.FindLPlain("[x:=1+0;](x>1+0&x>1+0)".asFormula, PosInExpr(1::1::1::Nil))))
  }

  it should "correctly parenthesize postconditions with a searchy formula sub-position locator in new notation" in {
    BelleParser("trueAnd('L==\"[x:=2;](#true&x>1#)\")") shouldBe (round trip TactixLibrary.useAt(Ax.trueAnd)(Find.FindLPlain("[x:=2;](true&x>1)".asFormula, PosInExpr(1::Nil))))
    BelleParser("trueAnd('L==\"[x:=2;]#(true&x>1)#\")") shouldBe (round trip TactixLibrary.useAt(Ax.trueAnd)(Find.FindLPlain("[x:=2;](true&x>1)".asFormula, PosInExpr(1::Nil))))
    //@note allow more concise notation with # forming parentheses
    BelleParser("trueAnd('L==\"[x:=2;]#true&x>1#\")") shouldBe (round trip TactixLibrary.useAt(Ax.trueAnd)(Find.FindLPlain("[x:=2;](true&x>1)".asFormula, PosInExpr(1::Nil))))
    BelleParser("trueAnd('L==\"(true&x>1)&[x:=2;]#true&x>1#\")") shouldBe (round trip TactixLibrary.useAt(Ax.trueAnd)(Find.FindLPlain("(true&x>1)&[x:=2;](true&x>1)".asFormula, PosInExpr(1::1::Nil))))
  }

  it should "correctly parenthesize programs with a searchy formula sub-position locator in new notation" in {
    BelleParser("chase('L==\"[{#x:=1; ++ x:=2;#};ode;]x>1\")") shouldBe (round trip TactixLibrary.chase(Find.FindLPlain("[{x:=1; ++ x:=2;};ode;]x>1".asFormula, PosInExpr(0::0::Nil))))
    BelleParser("chase('L==\"[#{x:=1; ++ x:=2;}#;ode;]x>1\")") shouldBe (round trip TactixLibrary.chase(Find.FindLPlain("[{x:=1; ++ x:=2;};ode;]x>1".asFormula, PosInExpr(0::0::Nil))))
    //@note allow more concise notation with # forming braces
    BelleParser("chase('L==\"[#x:=1; ++ x:=2;#;ode;]x>1\")") shouldBe (round trip TactixLibrary.chase(Find.FindLPlain("[{x:=1; ++ x:=2;};ode;]x>1".asFormula, PosInExpr(0::0::Nil))))
    BelleParser("chase('L==\"[{x:=1; ++ x:=2;};#x:=1; ++ x:=2;#;ode;]x>1\")") shouldBe (round trip TactixLibrary.chase(Find.FindLPlain("[{x:=1; ++ x:=2;};{x:=1; ++ x:=2;};ode;]x>1".asFormula, PosInExpr(0::1::0::Nil))))
  }

  it should "parse a built-in argument with a searchy unification position locator" in {
    BelleParser("boxAnd('L~={`[x:=2;](x>0&x>1)`})") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindLMatch("[x:=2;](x>0&x>1)".asFormula)))
  }

  it should "parse a built-in argument with a check position locator" in {
    BelleParser("boxAnd(2=={`[x:=2;](x>0&x>1)`})") shouldBe (round trip HilbertCalculus.boxAnd(Fixed(2, Nil, Some("[x:=2;](x>0&x>1)".asFormula))))
  }

  it should "parse a built-in argument with a unification check position locator" in {
    BelleParser("boxAnd(2~={`[x:=2;](x>0&x>1)`})") shouldBe (round trip HilbertCalculus.boxAnd(Fixed(2, Nil, Some("[x:=2;](x>0&x>1)".asFormula), exact=false)))
  }

  it should "parse a built-in argument with a 'R position locator" in {
    BelleParser("boxAnd('R)") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindRFirst))
  }

  it should "parse a built-in argument with a 'Rlast position locator" in {
    BelleParser("boxAnd('Rlast)") shouldBe (round trip HilbertCalculus.boxAnd(LastSucc(0)))
  }

  it should "parse a built-in argument with a 'Rlast subposition locator" in {
    BelleParser("boxAnd('Rlast.1)") shouldBe (round trip HilbertCalculus.boxAnd(LastSucc(0, PosInExpr(1::Nil))))
  }

  it should "parse a built-in argument with a 'Llast position locator" in {
    BelleParser("boxAnd('Llast)") shouldBe (round trip HilbertCalculus.boxAnd(LastAnte(0)))
  }

  it should "parse a built-in argument with a 'Llast subposition locator" in {
    BelleParser("boxAnd('Llast.0.1)") shouldBe (round trip HilbertCalculus.boxAnd(LastAnte(0, PosInExpr(0::1::Nil))))
  }

  it should "parse a built-in argument with a '_ position locator" in {
    BelleParser("boxAnd('_)") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindLFirst))
  }

  it should "parse a built-in tactic that takes a whole list of arguments" in {
    BelleParser("diffInvariant({`1=1`}, 1)") shouldBe (round trip TactixLibrary.diffInvariant("1=1".asFormula)(1))
  }

  it should "Parse a loop tactic and print it back out" in {
    BelleParser("loop({`1=1`}, 1)") shouldBe (round trip TactixLibrary.loop("1=1".asFormula)(1))
    BelleParser("loop(\"1=1\", 1)") shouldBe (round trip TactixLibrary.loop("1=1".asFormula)(1))
  }

  it should "parse a tactic with optional argument specified" in {
    val t = TactixLibrary.discreteGhost("5".asTerm, Some("x".asVariable))(1)
    BelleParser("discreteGhost({`5`}, {`x`}, 1)") shouldBe (round trip t)
    BelleParser("discreteGhost(\"5\", \"x\", 1)") shouldBe (round trip t)
  }

  it should "parse a tactic without optional argument specified" in {
    val t = TactixLibrary.discreteGhost("5".asTerm, None)(1)
    BelleParser("discreteGhost({`5`}, 1)") shouldBe (round trip t)
    BelleParser("discreteGhost(\"5\", 1)") shouldBe (round trip t)
  }

  it should "parse OptionArg arguments when option unspecified" in {
    val s = "dbx(1)"
    val t = BelleParser(s)
    BelleParser(s) shouldBe (round trip t)
  }

  it should "parse OptionArg arguments with option specified" in {
    val s = "dbx({`x`}, 1)"
    val t = BelleParser(s)
    BelleParser(s) shouldBe (round trip t)
  }

  it should "parse a tactic without list argument specified" in {
    BelleParser("universalClosure(1)") shouldBe (round trip FOQuantifierTactics.universalClosure(List.empty)(1))
  }

  it should "parse nested arguments" in {
    BelleParser("pending({`loop({`x>=0`}, 1)`})") shouldBe (round trip DebuggingTactics.pending("loop({`x>=0`}, 1)"))
    //@note new syntax needs escaping inner " for nesting
    BelleParser("""pending("loop(\"x>=0\", 1)")""") shouldBe (round trip DebuggingTactics.pending("loop(\"x>=0\", 1)"))
  }

  it should "parse nested arguments with line breaks" in {
    val s = "pending({`<(\n nil,\n nil\n, nil)`})"
    val t = BelleParser(s)
    BelleParser(s) shouldBe (round trip t)
    BelleParser("pending(\"<(\n nil,\n nil\n, nil)\")") shouldBe (round trip t)
  }

  //endregion

  //region Sequential combinator

  "Sequential parser" should "parse e & e" in {
    val result = BelleParser("andR(1) & andR(2)").asInstanceOf[SeqTactic]
    result.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2))
    result shouldBe (round trip result)
  }

  it should "parse seq right-associative -- e & e & e parses to e & (e & e)" in {
    val result = BelleParser("andR(1) & andR(2) & andR(3)").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse seq right-associative when there are a bunch of parens" in {
    val result = BelleParser("(andR(1)) & (andR(2)) & (andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse e & (e & e)" in {
    val result = BelleParser("andR(1) & (andR(2) & andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse (e & e) & e" in {
    val result = BelleParser("(andR(1) & andR(2)) & andR(3)").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2), TactixLibrary.andR(3))
  }


  it should "parse compositions of things that parse to partials" in {
    val tactic = BelleParser("nil & nil").asInstanceOf[SeqTactic]
    tactic shouldBe (round trip tactic)
    tactic.seq should contain theSameElementsInOrderAs List(TactixLibrary.nil, TactixLibrary.nil)
  }

  it should "print anonymous tactics empty and reparse without them" in {
    val t1 = BelleParser(BellePrettyPrinter(TactixLibrary.assertT(_ => false, "Fail") & implyR(1)))
    t1 shouldBe implyR(1)
    BellePrettyPrinter(t1) shouldBe "implyR(1)"

    val t2 = BelleParser(BellePrettyPrinter(implyR(1) & TactixLibrary.assertT(_ => false, "Fail")))
    t2 shouldBe implyR(1)
    BellePrettyPrinter(t2) shouldBe "implyR(1)"

    BellePrettyPrinter(TactixLibrary.assertT(_ => true, "Succeed") & TactixLibrary.assertT(_ => false, "Fail")) shouldBe ""
    BellePrettyPrinter(implyR(1) & TactixLibrary.assertT(_ => true, "Succeed") & andL(-1)) shouldBe "implyR(1) ; andL(-1)"
  }

  it should "parse simple assert" in {
    BelleParser("""assert("x>0", "Unexpected", 1)""") shouldBe assertE("x>0".asExpr, "Unexpected")(1)
  }

  //endregion

  //region Either combinator

  "Either parser" should "parse e | e" in {
    val result = BelleParser("andR(1) | andR(2)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2))
  }

  it should "parse either right-associative -- e | e | e parses to e | (e | e)" in {
    val result = BelleParser("andR(1) | andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse either right-associative when there are a bunch of parens" in {
    val result = BelleParser("(andR(1)) | (andR(2)) | (andR(3))").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse e | (e | e)" in {
    val result = BelleParser("andR(1) | (andR(2) | andR(3))").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse (e | e) | e" in {
    val result = BelleParser("(andR(1) | andR(2)) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse e & b | c" in {
    val result = BelleParser("andR(1) & andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(SeqTactic(TactixLibrary.andR(1), TactixLibrary.andR(2)), TactixLibrary.andR(3))
  }

  it should "parse e | b & c" in {
    val result = BelleParser("andR(1) | andR(2) & andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.alts should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), SeqTactic(TactixLibrary.andR(2), TactixLibrary.andR(3)))
  }

  //endregion

  //region Branching combinator

  "Branch combinator parser" should "parse e <(e,e)" in {
    val result = BelleParser("andR(1) <(andR(2), andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), BranchTactic(Seq(TactixLibrary.andR(2), TactixLibrary.andR(3))))
  }

  it should "print indented" in {
    BellePrettyPrinter(BelleParser("andR(1); <(andR(2), andR(3))")) shouldBe
      """andR(1) ; <(
        |  andR(2),
        |  andR(3)
        |)""".stripMargin

    BellePrettyPrinter(BelleParser("andR(1); <(andR(2); <(andR(3), andR(4)), andR(5))")) shouldBe
      """andR(1) ; <(
        |  andR(2) ; <(
        |    andR(3),
        |    andR(4)
        |  ),
        |  andR(5)
        |)""".stripMargin
  }

  it should "parse e <()" in {
    val result = BelleParser("andR(1) <()").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), BranchTactic(Seq.empty))
  }

  it should "report an error on e <(e)" in {
    the [ParseException] thrownBy BelleParser("andR(1) <(andR(1))") should
      have message """1:9 Branch tactic has only a single child
                     |Found:    <unknown> at 1:9
                     |Expected: <unknown>""".stripMargin
  }

  it should "parse e & <(e,e)" in {
    val result = BelleParser("andR(1) & <(andR(1), andR(1))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), BranchTactic(Seq(TactixLibrary.andR(1), TactixLibrary.andR(1))))
  }

  it should "parse as case tactic when labels are present" in {
    val result@SeqTactic(loop :: CaseTactic(children) :: Nil) = BelleParser("loop(\"x>=0\",1); <(\"Init\": andL(-1), \"Step\": andL(-2), \"Post\": andL(-3))")
    result shouldBe (round trip result)
    loop shouldBe TactixLibrary.loop("x>=0".asFormula)(1)
    children should contain theSameElementsAs List(
      BelleLabels.initCase -> andL(-1),
      BelleLabels.indStep -> andL(-2),
      BelleLabels.useCase -> andL(-3)
    )
  }

  it should "print as cases indented" in {
    BellePrettyPrinter(BelleParser("loop(\"x>=0\",1); <(\"Init\": andL(-1), \"Step\": andL(-2), \"Post\": andL(-3))")) shouldBe
      """loop("x>=0", 1) ; <(
        |  "Init": andL(-1),
        |  "Step": andL(-2),
        |  "Post": andL(-3)
        |)""".stripMargin
    BellePrettyPrinter(BelleParser("""loop("x>=0",1); <("Init":cut("x>=0");<("Use":nil,"Show":nil), "Step":nil, "Post":nil)""")) shouldBe
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
    val result@SeqTactic(loop :: CaseTactic(children) :: Nil) = BelleParser("loop(\"x>=0\",1); <(\"Init\": andL(-1); orL(-1), \"Step\": orL(-2); <(andL(-2), orR(2)), \"Post\": andL(-3) using \"x=2\" | andR(3))")
    result shouldBe (round trip result)
    loop shouldBe TactixLibrary.loop("x>=0".asFormula)(1)
    children should contain theSameElementsAs List(
      BelleLabels.initCase -> (andL(-1) & orL(-1)),
      BelleLabels.indStep -> (orL(-2) <(andL(-2), orR(2))),
      BelleLabels.useCase -> (Using("x=2".asFormula::Nil, andL(-3)) | andR(3))
    )
  }

  it should "parse nested case tactics" in {
    val result@SeqTactic(loop :: CaseTactic(children) :: Nil) = BelleParser("loop(\"x>=0\",1); <(\"Init\": andL(-1), \"Step\": orL(-2); <(\"LHS\": andL(-2), \"RHS\": orR(2)), \"Post\": andL(-3))")
    result shouldBe (round trip result)
    loop shouldBe TactixLibrary.loop("x>=0".asFormula)(1)
    children should contain theSameElementsAs List(
      BelleLabels.initCase -> andL(-1),
      BelleLabels.indStep -> orL(-2).switch("LHS".asLabel -> andL(-2), "RHS".asLabel -> orR(2)),
      BelleLabels.useCase -> andL(-3)
    )
  }

  it should "require case labels on all branches" in {
    the [ParseException] thrownBy BelleParser("loop(\"x>=0\",1); <(andL(-1), \"Step\": andL(-2), \"Post\": andL(-3))") should
      have message """1:19 Not all branches have labels. Please provide labels for the branches marked <missing>
                     |  "<missing>": andL(-1),
                     |  "Step": andL(-2),
                     |  "Post": andL(-3)
                     |resulting from
                     |loop("x>=0", 1)
                     |Found:    <missing> at 1:19
                     |Expected: "A label":""".stripMargin
  }


  //endregion

  //region Kleene Star Comabinator

  "Kleene star parser" should "parse e*" in {
    val tactic = BelleParser("andR(1)*").asInstanceOf[SaturateTactic]
    tactic shouldBe (round trip tactic)
    tactic.child shouldBe TactixLibrary.andR(1)
  }

  it should "parse (e&e)*" in {
    val tactic = BelleParser("(andR(1) & andR(2))*").asInstanceOf[SaturateTactic]
    tactic shouldBe (round trip tactic)
    tactic.child.asInstanceOf[SeqTactic].seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), TactixLibrary.andR(2))
  }

  it should "get precedence right" in {
    val tactic = BelleParser("andR(1) & andR(2)*")
    tactic shouldBe (round trip tactic)
    tactic shouldBe a [SeqTactic]
    tactic shouldBe TactixLibrary.andR(1) & SaturateTactic(TactixLibrary.andR(2))
  }

  it should "parse fully parenthesized" in {
    val tactic = BelleParser("andR(1) & (andR(2)*)")
    tactic shouldBe (round trip TactixLibrary.andR(1) & SaturateTactic(TactixLibrary.andR(2)))
  }

  "NTIMES repeat combinator parser" should "parse e*22" in {
    val tactic = BelleParser("andR(1)*22").asInstanceOf[RepeatTactic]
    tactic shouldBe (round trip tactic)
    tactic.child shouldBe TactixLibrary.andR(1)
    tactic.times shouldBe 22
  }

  it should "get precedence right" in {
    val tactic = BelleParser("andR(1) & andR(2)*3")
    tactic shouldBe a [SeqTactic]
    tactic shouldBe (round trip TactixLibrary.andR(1) & (TactixLibrary.andR(2)*3))
  }

  "saturate parser" should "parse e+" in {
    val tactic = BelleParser("andR(1)+").asInstanceOf[SeqTactic]
    tactic shouldBe (round trip tactic)
    tactic.seq should contain theSameElementsInOrderAs List(TactixLibrary.andR(1), SaturateTactic(TactixLibrary.andR(1)))
  }

  it should "get precedence right" in {
    val tactic = BelleParser("andR(1) & andR(2)*")
    tactic shouldBe a [SeqTactic]
    tactic shouldBe (round trip TactixLibrary.andR(1) & SaturateTactic(TactixLibrary.andR(2)))
  }

  "doall combinator parser" should "parse doall(closeId)" in {
    val tactic = BelleParser("doall(id)")
    tactic shouldBe (round trip OnAll(TactixLibrary.id))
  }

  it should "parse combined tactics with parameters doall(closeId | closeTrue | andL(1))" in {
    val tactic = BelleParser("doall(id | closeT | andL(1))")
    tactic shouldBe (round trip OnAll(TactixLibrary.id | (TactixLibrary.closeT | TactixLibrary.andL(1))))
  }

  "Optional combinator" should "parse ?(closeId)" in {
    val tactic = BelleParser("?(id)")
    tactic shouldBe (round trip Idioms.?(TactixLibrary.id))
  }

  it should "bind stronger than seq. combinator" in {
    val tactic = BelleParser("andR(1) & ?(id)")
    tactic shouldBe (round trip SeqTactic(Seq(TactixLibrary.andR(1), Idioms.?(TactixLibrary.id))))
  }

  it should "bind stronger than alt. combinator" in {
    val tactic = BelleParser("andR(1) | ?(id)")
    tactic shouldBe (round trip EitherTactic(TactixLibrary.andR(1), Idioms.?(TactixLibrary.id)))
  }

  it should "bind stronger than saturation" in {
    //@note this is debatable, but was easier to implement the moment
    val tactic = BelleParser("?(andR(1))*")
    tactic shouldBe (round trip SaturateTactic(Idioms.?(TactixLibrary.andR(1))))
  }

  it should "work in the beginning of a branch" in {
    val tactic = BelleParser("andR(1) & <(?(id), ?(orR(1)))")
    tactic shouldBe (round trip TactixLibrary.andR(1) & Idioms.<(Idioms.?(TactixLibrary.id.asInstanceOf[BelleExpr]), Idioms.?(TactixLibrary.orR(1))))
  }


  //endregion

  //region Comma lists

  "comma separated list folding" should "work" in {
    val t =
      """
        |nil<(nil, nil)
      """.stripMargin
    BelleParser(t) shouldBe (round trip BelleParser(t))
  }

  it should "work for a tactic (e)" in {
    val t =
      """
        |nil<((nil), nil)
      """.stripMargin
    BelleParser(t) shouldBe (round trip BelleParser(t))
  }

  it should "work for a tactic (e) in the final position" in {
    val t =
      """
        |nil<(nil, (nil))
      """.stripMargin
    BelleParser(t) shouldBe (round trip BelleParser(t))
  }

  it should "work on tactic that caused original bug" in withMathematica { _ =>
    val t = """implyR(1) &
              |loop({`x<=m`}, 1) <(
              |  QE,
              |  QE,
              |  partial(composeb(1) & choiceb(1) & andR(1) <(
              |    assignb(1) & solve(1) & nil,
              |    testb(1) & implyR(1) & solve(1) & nil
              |  ))
              |)""".stripMargin
    BelleParser(t) shouldBe (round trip BelleParser(t))
  }

  //endregion

  //region Partial tactics

  "partial tactic parser" should "parse partial(e)" in {
    val tactic = BelleParser("partial(andR(1))").asInstanceOf[PartialTactic]
    tactic shouldBe (round trip tactic)
    tactic.child shouldBe TactixLibrary.andR(1)
  }

  it should "parse e partial" in {
    val tactic = BelleParser("andR(1) partial").asInstanceOf[PartialTactic]
    tactic shouldBe (round trip tactic)
    tactic.child shouldBe TactixLibrary.andR(1)
  }

  it should "parse with expected precedence" in {
    BelleParser("andL(-1) & (andR(1) partial)") shouldBe (round trip SeqTactic(Seq(TactixLibrary.andL(-1), PartialTactic(TactixLibrary.andR(1)))))
    BelleParser("andL(-1) & andR(1) partial") shouldBe (round trip PartialTactic(SeqTactic(Seq(TactixLibrary.andL(-1), TactixLibrary.andR(1)))))
  }

  //endregion

  //region Done tactics

  "done tactic parser" should "parse closeId & done" in {
    val tactic = BelleParser("id & done")
    tactic shouldBe (round trip TactixLibrary.id & TactixLibrary.done)
  }

  it should "parse done" in {
    val tactic = BelleParser("done")
    tactic shouldBe (round trip TactixLibrary.done)
  }

  it should "parse empty-argument done" in {
    val tactic = BelleParser("done()")
    tactic shouldBe (round trip TactixLibrary.done)
  }

  it should "parse done with message" in {
    val tactic = BelleParser("done({`Message`})")
    tactic shouldBe (round trip DebuggingTactics.done("Message", None))
  }

  it should "parse done with message and lemma name" in {
    val tactic = BelleParser("done({`Message`},{`My Lemma`})")
    tactic shouldBe (round trip DebuggingTactics.done("Message", Some("My Lemma")))
  }

  it should "parse in a branch" in {
    val tactic = BelleParser("andR(1) & <(id & done, done)")
    tactic shouldBe (round trip TactixLibrary.andR(1) & Idioms.<(TactixLibrary.id & TactixLibrary.done, TactixLibrary.done))
  }

  //endregion

  //region let

  "let tactic parser" should "parse a simple example" in {
    val tactic = BelleParser("let ({`a()=a`}) in (done)")
    tactic shouldBe (round trip Let("a()".asTerm, "a".asTerm, TactixLibrary.done))
  }

  it should "parse dI" in withMathematica { _ =>
    val inner =
      """
        |DI(1) ; implyR(1) ; andR(1) ; <(
        |  QE,
        |  derive(1.1) ; DE(1) ; Dassignb(1.1) ; GV(1) ; QE
        |)
      """.stripMargin
    val tactic = BelleParser(s"let ({`a()=a`}) in ($inner)")
    tactic shouldBe (round trip Let("a()".asTerm, "a".asTerm, round trip BelleParser(inner)))
  }

  it should "parse let as part of a larger tactic" in {
    val tactic = BelleParser("implyR(1) ; let ({`a()=a`}) in (nil) ; id")
    tactic shouldBe (round trip TactixLibrary.implyR(1) & (Let("a()".asTerm, "a".asTerm, TactixLibrary.nil) & TactixLibrary.id))
  }

  "def tactic parser" should "parse a simple example" in {
    val tactic = BelleParser("tactic t as (assignb('R))")
    tactic shouldBe (round trip DefTactic("t", TactixLibrary.assignb('R)))

  }

  it should "print indented" in {
    BellePrettyPrinter(BelleParser("tactic t as (assignb('R))")) shouldBe
      """tactic t as (
        |  assignb('R)
        |)""".stripMargin
    BellePrettyPrinter(BelleParser("""tactic t as (cut("x>=0"); <(nil,nil))""")) shouldBe
      """tactic t as (
        |  cut("x>=0") ; <(
        |    nil,
        |    nil
        |  )
        |)""".stripMargin
  }

  it should "parse multipe tactic defs" in {
    val tactic = BelleParser("tactic t as (assignb('R)) ; tactic s as (implyR(1))")
    tactic shouldBe (round trip DefTactic("t", TactixLibrary.assignb('R)) & DefTactic("s", TactixLibrary.implyR(1)))
  }

  it should "parse a simple example with application" in {
    val tactic = BelleParser("tactic t as (assignb('R)) ; implyR(1) ; t")
    val tDef = DefTactic("t", TactixLibrary.assignb('R))
    tactic shouldBe (round trip tDef & (TactixLibrary.implyR(1) & ApplyDefTactic(tDef)))
  }

  it should "parse with multiple application" in {
    val tactic = BelleParser("tactic t as (assignb('R)) ; andR(1) ; <(t ; prop ; done, prop ; doall(t))")
    val tDef = DefTactic("t", TactixLibrary.assignb('R))
    tactic shouldBe (round trip tDef & (TactixLibrary.andR(1) <(
      ApplyDefTactic(tDef) & (TactixLibrary.prop & TactixLibrary.done),
      TactixLibrary.prop & OnAll(ApplyDefTactic(tDef)))))
  }

  it should "reject duplicate definitions" in {
    a [ParseException] should be thrownBy BelleParser("tactic t as (assignb('R)) ; tactic t as (implyR(1))")
  }

  it should "allow scoped definitions" in {
    val tactic = BelleParser("tactic t as (assignb('R)) ; andR(1) ; <(t ; prop ; done, prop ; doall(tactic t as (unfold) ; t); t)")
    val tDef1 = DefTactic("t", TactixLibrary.assignb('R))
    val tDef2 = DefTactic("t", TactixLibrary.unfoldProgramNormalize)
    tactic shouldBe (round trip tDef1 & (TactixLibrary.andR(1) <(
      ApplyDefTactic(tDef1) & (TactixLibrary.prop & TactixLibrary.done),
      TactixLibrary.prop & (OnAll(tDef2 & ApplyDefTactic(tDef2)) & ApplyDefTactic(tDef1)))))
  }

  it should "allow nested defs" in {
    val tactic = BelleParser("tactic t as (tactic s as (assignb('R)) ; andR(1) ; <(s, s)) ; t")
    val sDef = DefTactic("s", TactixLibrary.assignb('R))
    val tDef = DefTactic("t", sDef & TactixLibrary.andR(1) <(ApplyDefTactic(sDef), ApplyDefTactic(sDef)))
    tactic shouldBe (round trip tDef & ApplyDefTactic(tDef))
  }

  "Expand" should "parse a simple definition expand" in {
    val tactic = BelleParser.parseWithInvGen("implyR(1) ; expand \"f()\"", None,
      Declaration(scala.collection.immutable.Map((Name("f", None), Signature(Some(Unit), Real, None, Some("3*2".asExpr), UnknownLocation)))))
    tactic shouldBe TactixLibrary.implyR(1) & expand("f()")
  }

  it should "elaborate variables to functions" in {
    val tactic = BelleParser.parseWithInvGen("implyR(1) ; expand \"f\"", None,
      Declaration(scala.collection.immutable.Map(
        (Name("f", None), Signature(Some(Unit), Real, None, Some("g*2".asExpr), UnknownLocation)),
        (Name("g", None), Signature(Some(Unit), Real, None, Some("3*2".asExpr), UnknownLocation))
      )
    ))
    tactic shouldBe TactixLibrary.implyR(1) & expand("f")
  }

  it should "elaborate variables to functions in tactic arguments" in {
    val defs = Declaration(scala.collection.immutable.Map(
      (Name("f", None), Signature(Some(Unit), Real, None, None, UnknownLocation)),
      (Name("g", None), Signature(Some(Unit), Real, None, Some("1*f".asExpr), UnknownLocation))
    ))
    BelleParser.parseWithInvGen("hideL('L==\"f=g\")", None, defs, expandAll=true) shouldBe
      expandAllDefs("g() ~> 1*f()".asSubstitutionPair :: Nil) & TactixLibrary.hideL(
        Find.FindLDef("f()=1*f()".asFormula, PosInExpr.HereP, defs))
    BelleParser.parseWithInvGen("hideL('L==\"f=g\")", None, defs, expandAll=false) shouldBe
      TactixLibrary.hideL(Find.FindLDef("f()=g()".asFormula, PosInExpr.HereP, defs))
  }

  it should "elaborate variables to functions per declarations" in {
    val tactic = BelleParser.parseWithInvGen("implyR(1) ; expand \"f\"", None,
      Declaration(scala.collection.immutable.Map(
        (Name("f", None), Signature(Some(Unit), Real, None, Some("g".asExpr), UnknownLocation)),
        (Name("g", None), Signature(Some(Unit), Real, None, Some("0".asExpr), UnknownLocation))
      )
      ))
    tactic shouldBe TactixLibrary.implyR(1) & expand("f")
  }

  it should "elaborate functions to predicates per declarations" in {
    val tactic = BelleParser.parseWithInvGen("implyR(1) ; expand \"f\"", None,
      Declaration(scala.collection.immutable.Map(
        (Name("f", None), Signature(Some(Unit), Bool, None, Some("g".asExpr), UnknownLocation)),
        (Name("g", None), Signature(Some(Unit), Bool, None, Some("3*2>=0".asExpr), UnknownLocation))
      )
      ))
    tactic shouldBe TactixLibrary.implyR(1) & expand("f")
  }

  it should "elaborate programconsts to systemconsts" in {
    val decls = Declaration(scala.collection.immutable.Map(
      (Name("p", None), Signature(Some(Unit), Bool, None, Some("3*2>=0".asExpr), UnknownLocation)),
      (Name("a", None), Signature(Some(Unit), Trafo, None, Some("x:=x+1;".asExpr), UnknownLocation))
    ))
    BelleParser.parseWithInvGen("implyR(1) ; cut(\"[a;]p\")", None, decls) shouldBe
      TactixLibrary.implyR(1) & cut("[a{|^@|};]p()".asFormula)
    BelleParser.parseWithInvGen("implyR(1) ; cut(\"[a;]p\")", None, decls, expandAll=true) shouldBe
      expandAllDefs(decls.substs) & (TactixLibrary.implyR(1) & cut("[x:=x+1;]3*2>=0".asFormula))
  }

  it should "not collide with expandAll" in {
    BellePrettyPrinter(BelleParser.parseWithInvGen("expandAll")) shouldBe "expandAll"
  }

  "ExpandAllDefs" should "expand multiple definitions" in {
    val tactic = BelleParser.parseWithInvGen("expandAllDefs", None,
      Declaration(scala.collection.immutable.Map(
        //@note locations just so that parser knows the definitions are supposed to originate from a file
        (Name("f", None), Signature(Some(Unit), Real, None, Some("3*2".asExpr), Region(0, 0, 0, 0))),
        (Name("g", None), Signature(Some(Unit), Real, None, Some("4".asExpr), Region(0, 0, 0, 0)))
      )))
    tactic match {
      case InputTactic("expandAllDefs", (substs: List[SubstitutionPair]) :: Nil) =>
        substs should contain theSameElementsAs("f() ~> 3*2".asSubstitutionPair :: "g() ~> 4".asSubstitutionPair :: Nil)
    }
  }

  it should "expand proof definitions with US and model definitions after with expandAllDefs" in {
    val tactic = BelleParser.parseWithInvGen("expandAllDefs", None,
      Declaration(scala.collection.immutable.Map(
        //@note UnknownLocation identifies proof definitions, known locations identify model definitions
        (Name("f", None), Signature(Some(Unit), Real, None, Some("g*2".asExpr), UnknownLocation)),
        (Name("g", None), Signature(Some(Unit), Real, None, Some("4".asExpr), Region(0, 0, 0, 0)))
      )))
    tactic shouldBe TactixLibrary.uniformSubstitute(
      USubst(SubstitutionPair(FuncOf(Function("f", None, Unit, Real), Nothing),
             Times(FuncOf(Function("g", None, Unit, Real), Nothing), Number(2))) :: Nil)) &
        expandAllDefs(SubstitutionPair(FuncOf(Function("g", None, Unit, Real), Nothing), Number(4)) :: Nil)
  }

  it should "expand and elaborate proof definitions with US and model definitions after with expandAllDefs" in {
    val tactic = BelleParser.parseWithInvGen("expandAllDefs", None,
      Declaration(scala.collection.immutable.Map(
        //@note UnknownLocation identifies proof definitions, known locations identify model definitions
        (Name("f", None), Signature(Some(Real), Bool, None, Some("g(.)".asExpr), UnknownLocation)),
        (Name("g", None), Signature(Some(Real), Bool, None, Some(".>0".asExpr), Region(0, 0, 0, 0)))
      )))
    tactic shouldBe TactixLibrary.uniformSubstitute(USubst(
      SubstitutionPair(PredOf(Function("f", None, Real, Bool), DotTerm()), PredOf(Function("g", None, Real, Bool), DotTerm())) :: Nil)) &
      expandAllDefs(SubstitutionPair(PredOf(Function("g", None, Real, Bool), DotTerm()), Greater(DotTerm(), Number(0))) :: Nil)
  }

  it should "default expand and elaborate model definitions with expandAllDefs" in {
    val tactic = BelleParser.parseWithInvGen("""dC("f(x)", 1)""", None,
      Declaration(scala.collection.immutable.Map(
        //@note Known locations identify model definitions
        (Name("f", None), Signature(Some(Real), Bool, None, Some(".>g".asExpr), Region(0, 0, 0, 0))),
        (Name("g", None), Signature(Some(Unit), Real, None, None, Region(0, 0, 0, 0)))
      )), expandAll = true)
    tactic shouldBe expandAllDefs(
      SubstitutionPair(PredOf(Function("f", None, Real, Bool), DotTerm()), Greater(DotTerm(), FuncOf(Function("g", None, Unit, Real), Nothing))) :: Nil) &
      TactixLibrary.dC("x>g()".asFormula)(1)
  }

  it should "default expand and elaborate model definitions with expandAllDefs and in tactics" in {
    val tactic = BelleParser.parseWithInvGen("""dC("x>g", 1)""", None,
      Declaration(scala.collection.immutable.Map(
        //@note Known locations identify model definitions
        (Name("f", None), Signature(Some(Real), Bool, None, Some(".>g".asExpr), Region(0, 0, 0, 0))),
        (Name("g", None), Signature(Some(Unit), Real, None, None, Region(0, 0, 0, 0)))
      )), expandAll = true)
    tactic shouldBe expandAllDefs(
      SubstitutionPair(PredOf(Function("f", None, Real, Bool), DotTerm()), Greater(DotTerm(), FuncOf(Function("g", None, Unit, Real), Nothing))) :: Nil) &
      TactixLibrary.dC("x>g()".asFormula)(1)
  }

  it should "topologically sort definitions" in {
    val tactic = BelleParser.parseWithInvGen("expandAllDefs", None,
      Declaration(scala.collection.immutable.Map(
        (Name("h", None), Signature(Some(Unit), Real, None, Some("g()*2".asTerm), Region(0, 0, 0, 0))),
        (Name("i", None), Signature(Some(Unit), Real, None, Some("1".asTerm), Region(0, 0, 0, 0))),
        (Name("f", None), Signature(Some(Unit), Real, None, Some("3*2".asTerm), Region(0, 0, 0, 0))),
        (Name("g", None), Signature(Some(Unit), Real, None, Some("f()+4".asTerm), Region(0, 0, 0, 0))),
        (Name("j", None), Signature(Some(Unit), Trafo, None, Some("x:=g()+i();".asProgram), Region(0, 0, 0, 0)))
      )))
    tactic match {
      case InputTactic("expandAllDefs", (defs: List[SubstitutionPair]) :: Nil) =>
        defs should contain theSameElementsAs("h() ~> g()*2".asSubstitutionPair :: "j{|^@|}; ~> x:=g()+i();".asSubstitutionPair ::
          "i() ~> 1".asSubstitutionPair :: "g() ~> f()+4".asSubstitutionPair :: "f() ~> 3*2".asSubstitutionPair :: Nil)
        val hi = defs.indexOf("h() ~> g()*2".asSubstitutionPair)
        val ji = defs.indexOf("j; ~> x:=g()+i();".asSubstitutionPair)
        val ii = defs.indexOf("i() ~> 1".asSubstitutionPair)
        val gi = defs.indexOf("g() ~> f()+4".asSubstitutionPair)
        val fi = defs.indexOf("f() ~> 3*2".asSubstitutionPair)
        hi should be < gi
        ji should (be < gi and be < ii)
        gi should be < fi
    }
  }

  //endregion

  //region argument parser

  "Tactic argument parser" should "parse string arguments" in {
    BelleParser("debug({`a message`})") shouldBe (round trip DebuggingTactics.debugX("a message"))
    BelleParser("print({`a message`})") shouldBe (round trip DebuggingTactics.printX("a message"))
  }

  it should "parse formula arguments" in {
    BelleParser("dC({`x>0`},1)") shouldBe (round trip TactixLibrary.dC("x>0".asFormula)(1))
  }

  it should "parse list formula arguments" in {
    BelleParser("dC(\"x>0 :: y<1 :: nil\",1)") shouldBe (round trip TactixLibrary.dC("x>0".asFormula :: "y<1".asFormula :: Nil)(1))
  }

  it should "parse term arguments" in {
    BelleParser("transform({`x+2`},1)") shouldBe (round trip TactixLibrary.transform("x+2".asTerm)(1))
  }

  it should "parse substitution arguments" in {
    BelleParser("US({`init(.) ~> .=0`})") shouldBe (round trip TactixLibrary.USX(
      SubstitutionPair("init(.)".asFormula, ".=0".asFormula) :: Nil))
  }

  it should "parse list substitution arguments" in {
    BelleParser("US(\"init(.) ~> .=0 :: a;~>{x'=v,t'=1&true} :: nil\")") shouldBe (round trip TactixLibrary.USX(
      SubstitutionPair("init(.)".asFormula, ".=0".asFormula) :: SubstitutionPair("a;".asProgram, "{x'=v,t'=1}".asProgram) :: Nil))
  }

  it should "parse mixed arguments" in {
    BelleParser("dG({`{z'=-1*z+0}`},{`x*z^2=1`},1)") shouldBe (round trip TactixLibrary.dG("{z'=-1*z+0}".asProgram, Some("x*z^2=1".asFormula))(1))
  }

  it should "parse predicates in locators" in {
    BelleParser("hideL(1==\"p(x)\")") shouldBe (round trip TactixLibrary.hideL(Fixed(1, Nil, Some("p(x)".asFormula))))
  }

  it should "expand definitions when parsing arguments only when asked to" in {
    inside(BelleParser.parseWithInvGen("MR({`safeDist()>0`},1)", None, Declaration(Map()))) {
      case adpt: AppliedDependentPositionTactic => adpt.pt should have (
        'inputs ("safeDist()>0".asFormula::Nil)
      )
    }

    inside(BelleParser.parseWithInvGen("MR({`safeDist()>0`},1)", None,
        Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Some("y".asTerm), null))))) {
      case adpt: AppliedDependentPositionTactic => adpt.pt should have (
        'inputs ("safeDist()>0".asFormula::Nil)
      )
    }

    inside(BelleParser.parseWithInvGen("MR({`safeDist()>0`},1)", None,
      Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Some("y".asTerm), null))), expandAll = true)) {
      case SeqTactic(InputTactic("expandAllDefs", (substs: List[SubstitutionPair]) :: Nil) :: (adpt: AppliedDependentPositionTactic) :: Nil) =>
        substs should contain theSameElementsAs "safeDist() ~> y".asSubstitutionPair :: Nil
        adpt.pt should have ('inputs ("y>0".asFormula::Nil))
    }
  }

  it should "expand definitions in the middle of parsing only when asked to" in {
    inside(BelleParser.parseWithInvGen("useLemma({`Lemma`},{`prop`}); MR({`safeDist()>0`},1)", None,
      Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Some("y".asTerm), null))))) {
      case SeqTactic(_ :: (adpt: AppliedDependentPositionTactic) :: Nil) => adpt.pt should have (
        'inputs ("safeDist()>0".asFormula::Nil)
      )
    }

    inside(BelleParser.parseWithInvGen("useLemma({`Lemma`},{`prop`}); MR({`safeDist()>0`},1)", None,
      Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Some("y".asTerm), null))), expandAll = true)) {
      case SeqTactic(InputTactic("expandAllDefs", (substs: List[SubstitutionPair]) :: Nil) :: _ :: (adpt: AppliedDependentPositionTactic) :: Nil) =>
        substs should contain theSameElementsAs "safeDist() ~> y".asSubstitutionPair :: Nil
        adpt.pt should have ('inputs ("y>0".asFormula::Nil))
    }
  }

  it should "expand definitions when parsing locators only when asked to" in {
    inside(BelleParser.parseWithInvGen("hideL('L=={`s=safeDist()`})", None, Declaration(Map()))) {
      case apt: AppliedPositionTactic => apt.locator shouldBe Find.FindLPlain("s=safeDist()".asFormula)
    }

    val defs = "safeDist() ~> y".asDeclaration
    inside(BelleParser.parseWithInvGen("hideL('L=={`s=safeDist()`})", None, defs)) {
      case apt: AppliedPositionTactic => apt.locator shouldBe
        Find.FindLDef("s=safeDist()".asFormula, PosInExpr.HereP, defs)
    }

    inside(BelleParser.parseWithInvGen("hideL('L=={`s=safeDist()`})", None, defs, expandAll = true)) {
      case SeqTactic(InputTactic("expandAllDefs", (substs: List[SubstitutionPair]) :: Nil) :: (apt: AppliedPositionTactic) :: Nil) =>
        substs should contain theSameElementsAs "safeDist() ~> y".asSubstitutionPair :: Nil
        apt.locator shouldBe Find.FindLDef("s=y".asFormula, PosInExpr.HereP, defs)
    }
  }

  it should "expand definitions when parsing position check locators only when asked to" in {
    inside(BelleParser.parseWithInvGen("hideL(-2=={`s=safeDist()`})", None, Declaration(Map()))) {
      case apt: AppliedPositionTactic => apt.locator shouldBe Fixed(-2, Nil, Some("s=safeDist()".asFormula))
    }

    inside(BelleParser.parseWithInvGen("hideL(-2=={`s=safeDist()`})", None,
      Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Some("y".asTerm), null))))) {
      case apt: AppliedPositionTactic => apt.locator shouldBe Fixed(-2, Nil, Some("s=safeDist()".asFormula))
    }

    inside(BelleParser.parseWithInvGen("hideL(-2=={`s=safeDist()`})", None,
      Declaration(Map(Name("safeDist", None) -> Signature(None, Real, None, Some("y".asTerm), null))), expandAll = true)) {
      case SeqTactic(InputTactic("expandAllDefs", (substs: List[SubstitutionPair]) :: Nil) :: (apt: AppliedPositionTactic) :: Nil) =>
        substs should contain theSameElementsAs "safeDist() ~> y".asSubstitutionPair :: Nil
        apt.locator shouldBe Fixed(-2, Nil, Some("s=y".asFormula))
    }
  }

  it should "allow escaped quotation marks in arguments" in {
    BelleParser(""" useLemma("Lemma 1", "dC(\"x>=0\",1)") """) shouldBe
      useLemmaX("Lemma 1", Some("dC(\"x>=0\",1)"))
  }

  it should "lex backslash followed by any character" in {
    BelleParser(""" hideR('R=="\exists x x=0") """) shouldBe hideR('R, "\\exists x x=0".asFormula)
    BelleParser(""" hideR('R=="\forall x x^2>=0") """) shouldBe hideR('R, "\\forall x x^2>=0".asFormula)
    the [ParseException] thrownBy BelleParser(""" hideR('R=="\x x^2=1") """) should
      have message """1:1 Unexpected token cannot be parsed
                     |Found:    \\ at 1:1 to 1:2
                     |Expected: <BeginningOfExpression>""".stripMargin
  }

  //endregion

  //region Lemmas

  "Using lemmas" should "work in exactly matching open goal" in {
    val f = "x>0&y>1 -> y>1&x>0".asFormula
    val lemma = proveBy(f, TactixLibrary.prop)
    LemmaDBFactory.lemmaDB.add(new Lemma(lemma, Lemma.requiredEvidence(lemma, Nil), Some(s"user${File.separator}testPropLemma")))
    proveBy(f, "useLemma({`testPropLemma`})".asTactic) shouldBe 'proved
  }

  it should "work with tactic adaptation" in {
    val f = "x>0&y>1 -> y>1&x>0".asFormula
    val lemma = proveBy(f, TactixLibrary.prop)
    LemmaDBFactory.lemmaDB.add(new Lemma(lemma, Lemma.requiredEvidence(lemma, Nil), Some(s"user${File.separator}testPropLemma")))
    proveBy("x>0, y>1, z>2 ==> y>1&x>0".asSequent, "useLemma({`testPropLemma`}, {`prop`})".asTactic) shouldBe 'proved
  }

  //endregion

  //region New dG syntax

  "new dG syntax" should "round trip ghosts" in {
    "dG({`y'=1`}, 1)".asTactic should (be (dG("y'=1".asFormula, None)(1)) and (print as "dG(\"y'=1\", 1)") and (reparse fromPrint))
    "dG({`{y'=1}`}, {`x*y=5`}, 1)".asTactic should (be (dG("{y'=1}".asProgram, Some("x*y=5".asFormula))(1)) and (print as "dG(\"{y'=1}\", \"x*y=5\", 1)") and (reparse fromPrint))
    "dG({`y'=0*y+1`}, {`x*y^2=1`}, 1)".asTactic should (be (dG("y'=0*y+1".asFormula, Some("x*y^2=1".asFormula))(1)) and (print as "dG(\"y'=0*y+1\", \"x*y^2=1\", 1)") and (reparse fromPrint))
    "dG({`y'=1/2*y`}, 1)".asTactic should (be (dG("y'=1/2*y".asFormula, None)(1)) and (print as "dG(\"y'=1/2*y\", 1)") and (reparse fromPrint))
    "dG({`{y'=1/2*y}`}, {`x*y^2=1`}, 1)".asTactic should (be (dG("{y'=1/2*y}".asProgram, Some("x*y^2=1".asFormula))(1)) and (print as "dG(\"{y'=1/2*y}\", \"x*y^2=1\", 1)") and (reparse fromPrint))
  }

  //endregion

  //region interpreted functions

  "Interpreted function" should "be parsed as arguments in cuts" in {
    "cut(\"exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1\")".asTactic should (
      be (cut("exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1".asFormula))
        and (print as "cut(\"exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1\")")
        and (reparse fromPrint))
  }

  it should "be parsed in position locators" in {
    "hideR('R==\"exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1\")".asTactic should (
      be (hideR(Find.FindRPlain("exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1".asFormula)))
        and (print as "hideR('R==\"exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(x)<=1\")")
        and (reparse fromPrint)
    )
  }

  //endregion
}
