package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.Real
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXDeclarationsParser.Declaration
import edu.cmu.cs.ls.keymaerax.parser.{ParseException, UnknownLocation}
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
class SimpleBelleParserTests extends TacticTestBase {
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

  it should "parse a built-in tactic with arguments" in {
    BelleParser("cut({`1=1`})") shouldBe (round trip TactixLibrary.cut("1=1".asFormula))
  }

  it should "parse a built-in argument with an absolute top-level postion" in {
    BelleParser("andR(1)") shouldBe (round trip TactixLibrary.andR(1))
  }

  it should "parse a built-in argument with an absolute non-top-level postion" in {
    val pos = BelleParser.parseAbsolutePosition("1.1", UnknownLocation)
    BelleParser("boxAnd(1.1)") shouldBe (round trip HilbertCalculus.boxAnd(pos))
  }

  it should "parse a built-in argument with a position locator" in {
    BelleParser("boxAnd('L)") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindL(0, None)))
  }

  it should "parse a built-in argument with a searchy position locator" in {
    BelleParser("boxAnd('L=={`[x:=2;](x>0&x>1)`})") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindL(0, Some("[x:=2;](x>0&x>1)".asFormula))))
  }

  it should "parse a built-in argument with a searchy unification position locator" in {
    BelleParser("boxAnd('L~={`[x:=2;](x>0&x>1)`})") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindL(0, Some("[x:=2;](x>0&x>1)".asFormula), exact=false)))
  }

  it should "parse a built-in argument with a check position locator" in {
    BelleParser("boxAnd(2=={`[x:=2;](x>0&x>1)`})") shouldBe (round trip HilbertCalculus.boxAnd(Fixed(2, Nil, Some("[x:=2;](x>0&x>1)".asFormula))))
  }

  it should "parse a built-in argument with a unification check position locator" in {
    BelleParser("boxAnd(2~={`[x:=2;](x>0&x>1)`})") shouldBe (round trip HilbertCalculus.boxAnd(Fixed(2, Nil, Some("[x:=2;](x>0&x>1)".asFormula), exact=false)))
  }

  it should "parse a built-in argument with a 'R position locator" in {
    BelleParser("boxAnd('R)") shouldBe (round trip HilbertCalculus.boxAnd(Find.FindR(0, None)))
  }

  it should "parse a built-in argument with a 'Rlast position locator" in {
    BelleParser("boxAnd('Rlast)") shouldBe (round trip HilbertCalculus.boxAnd(LastSucc(0)))
  }

  it should "parse a built-in argument with a 'Llast position locator" in {
    BelleParser("boxAnd('Llast)") shouldBe (round trip HilbertCalculus.boxAnd(LastAnte(0)))
  }

  it should "parse a built-in argument with a '_ position locator" in {
    BelleParser("boxAnd('_)") shouldBe (round trip HilbertCalculus.boxAnd(new Find(0, None, AntePosition(1), exact=true)))
  }

  it should "parse a built-in tactic that takes a whole list of arguments" in {
    BelleParser("diffInvariant({`1=1`}, 1)") shouldBe (round trip TactixLibrary.diffInvariant(Seq("1=1".asFormula) : _*)(1))
  }

  it should "Parse a loop tactic and print it back out" in {
    BelleParser("loop({`1=1`}, 1)") shouldBe (round trip TactixLibrary.loop("1=1".asFormula)(1))
  }

  it should "parse a tactic with optional argument specified" in {
    val t = TactixLibrary.discreteGhost("5".asTerm, Some("x".asVariable))(1)
    val s = "discreteGhost({`5`}, {`x`}, 1)"
    BelleParser(s) shouldBe (round trip t)
  }

  it should "parse a tactic without optional argument specified" in {
    val t = TactixLibrary.discreteGhost("5".asTerm, None)(1)
    val s = "discreteGhost({`5`}, 1)"
    BelleParser(s) shouldBe (round trip t)
  }

  //endregion

  //region Sequential combinator

  "Sequential parser" should "parse e & e" in {
    val result = BelleParser("andR(1) & andR(2)").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right shouldBe TactixLibrary.andR(2)
    result shouldBe (round trip result)
  }

  it should "parse seq right-associative -- e & e & e parses to e & (e & e)" in {
    val result = BelleParser("andR(1) & andR(2) & andR(3)").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse seq right-associative when there are a bunch of parens" in {
    val result = BelleParser("(andR(1)) & (andR(2)) & (andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e & (e & e)" in {
    val result = BelleParser("andR(1) & (andR(2) & andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse (e & e) & e" in {
    val result = BelleParser("(andR(1) & andR(2)) & andR(3)").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }


  it should "parse compositions of things that parse to partials" in {
    val tactic = BelleParser("nil & nil").asInstanceOf[SeqTactic]
    tactic shouldBe (round trip tactic)
    tactic.left shouldBe TactixLibrary.nil
    tactic.right shouldBe TactixLibrary.nil
  }

  //endregion

  //region Either combinator

  "Either parser" should "parse e | e" in {
    val result = BelleParser("andR(1) | andR(2)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right shouldBe TactixLibrary.andR(2)
  }

  it should "parse either right-associative -- e | e | e parses to e | (e | e)" in {
    val result = BelleParser("andR(1) | andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse either right-associative when there are a bunch of parens" in {
    val result = BelleParser("(andR(1)) | (andR(2)) | (andR(3))").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e | (e | e)" in {
    val result = BelleParser("andR(1) | (andR(2) | andR(3))").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse (e | e) | e" in {
    val result = BelleParser("(andR(1) | andR(2)) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.left.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e & b | c" in {
    val result = BelleParser("andR(1) & andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.left.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e | b & c" in {
    val result = BelleParser("andR(1) | andR(2) & andR(3)").asInstanceOf[EitherTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  //endregion

  //region Branching combinator

  "Branch combinator parser" should "parse e <(e,e)" in {
    val result = BelleParser("andR(1) <(andR(2), andR(3))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse e <()" in {
    val result = BelleParser("andR(1) <()").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq()
  }

  it should "parse e <(e)" in {
    val result = BelleParser("andR(1) <(andR(1))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(1))
  }

  it should "parse e & <(e) as well" in {
    val result = BelleParser("andR(1) & <(andR(1))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(1))
  }

  it should "parse e & <(e,e)" in {
    val result = BelleParser("andR(1) & <(andR(1), andR(1))").asInstanceOf[SeqTactic]
    result shouldBe (round trip result)
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(1), TactixLibrary.andR(1))
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
    tactic.child.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    tactic.child.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
  }

  it should "get precedence right" in {
    val tactic = BelleParser("andR(1) & andR(2)*")
    tactic shouldBe (round trip tactic)
    tactic shouldBe a [SeqTactic]
    tactic shouldBe TactixLibrary.andR(1) & (TactixLibrary.andR(2)*)
  }

  it should "parse fully parenthesized" in {
    val tactic = BelleParser("andR(1) & (andR(2)*)")
    tactic shouldBe (round trip TactixLibrary.andR(1) & (TactixLibrary.andR(2)*))
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
    tactic.left shouldBe TactixLibrary.andR(1)
    tactic.right.asInstanceOf[SaturateTactic].child shouldBe TactixLibrary.andR(1)
  }

  it should "get precedence right" in {
    val tactic = BelleParser("andR(1) & andR(2)*")
    tactic shouldBe a [SeqTactic]
    tactic shouldBe (round trip TactixLibrary.andR(1) & (TactixLibrary.andR(2)*))
  }

  "doall combinator parser" should "parse doall(closeId)" in {
    val tactic = BelleParser("doall(closeId)")
    tactic shouldBe (round trip OnAll(TactixLibrary.closeId))
  }

  it should "parse combined tactics with parameters doall(closeId | closeTrue | andL(1))" in {
    val tactic = BelleParser("doall(closeId | closeTrue | andL(1))")
    tactic shouldBe (round trip OnAll(TactixLibrary.closeId | (TactixLibrary.closeT | TactixLibrary.andL(1))))
  }

  "Optional combinator" should "parse ?(closeId)" in {
    val tactic = BelleParser("?(closeId)")
    tactic shouldBe (round trip Idioms.?(TactixLibrary.closeId))
  }

  it should "bind stronger than seq. combinator" in {
    val tactic = BelleParser("andR(1) & ?(closeId)")
    tactic shouldBe (round trip SeqTactic(TactixLibrary.andR(1), Idioms.?(TactixLibrary.closeId)))
  }

  it should "bind stronger than alt. combinator" in {
    val tactic = BelleParser("andR(1) | ?(closeId)")
    tactic shouldBe (round trip EitherTactic(TactixLibrary.andR(1), Idioms.?(TactixLibrary.closeId)))
  }

  it should "bind stronger than saturation" in {
    //@note this is debatable, but was easier to implement the moment
    val tactic = BelleParser("?(andR(1))*")
    tactic shouldBe (round trip SaturateTactic(Idioms.?(TactixLibrary.andR(1))))
  }

  it should "work in the beginning of a branch" in {
    val tactic = BelleParser("andR(1) & <(?(closeId), ?(orR(1)))")
    tactic shouldBe (round trip TactixLibrary.andR(1) & Idioms.<(Idioms.?(TactixLibrary.closeId), Idioms.?(TactixLibrary.orR(1))))
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
    BelleParser("andL(-1) & (andR(1) partial)") shouldBe (round trip SeqTactic(TactixLibrary.andL(-1), PartialTactic(TactixLibrary.andR(1))))
    BelleParser("andL(-1) & andR(1) partial") shouldBe (round trip PartialTactic(SeqTactic(TactixLibrary.andL(-1), TactixLibrary.andR(1))))
  }

  //endregion

  //region Done tactics

  "done tactic parser" should "parse closeId & done" in {
    val tactic = BelleParser("closeId & done")
    tactic shouldBe (round trip TactixLibrary.closeId & TactixLibrary.done)
  }

  it should "parse done" in {
    val tactic = BelleParser("done")
    tactic shouldBe (round trip TactixLibrary.done)
  }

  it should "parse in a branch" in {
    val tactic = BelleParser("andR(1) & <(closeId & done, done)")
    tactic shouldBe (round trip TactixLibrary.andR(1) & Idioms.<(TactixLibrary.closeId & TactixLibrary.done, TactixLibrary.done))
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
    val tactic = BelleParser("implyR(1) ; let ({`a()=a`}) in (nil) ; closeId")
    tactic shouldBe (round trip TactixLibrary.implyR(1) & (Let("a()".asTerm, "a".asTerm, TactixLibrary.skip) & TactixLibrary.closeId))
  }

  "def tactic parser" should "parse a simple example" in {
    val tactic = BelleParser("tactic t as (assignb('R))")
    tactic shouldBe (round trip DefTactic("t", TactixLibrary.assignb('R)))
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

  //@todo delete from parser
  "def function" should "parse a simple definition" in {
    val tactic = BelleParser("def {`f(x)=x^2+1`} ; implyR(1) ; expand {`f(x)`}")
    val fDef = DefExpression("f(x)=x^2+1".asFormula)
    tactic shouldBe fDef & (TactixLibrary.implyR(1) & ExpandDef(fDef))
  }

  it should "parse multiple defs" in {
    val tactic = BelleParser("def {`f(x)=x^2+1`} ; def {`g(x)=x+1`} ; implyR(1) ; expand {`f(x)`}")
    val fDef = DefExpression("f(x)=x^2+1".asFormula)
    val gDef = DefExpression("g(x)=x+1".asFormula)
    tactic shouldBe fDef & (gDef & (TactixLibrary.implyR(1) & ExpandDef(fDef)))
  }

  //endregion

  //region argument parser

  "Tactic argument parser" should "parse string arguments" in {
    BelleParser("print({`a message`})") shouldBe (round trip DebuggingTactics.print("a message"))
  }

  it should "parse formula arguments" in {
    BelleParser("dC({`x>0`},1)") shouldBe (round trip TactixLibrary.dC("x>0".asFormula)(1))
  }

  it should "parse term arguments" in {
    BelleParser("transform({`x+2`},1)") shouldBe (round trip TactixLibrary.transform("x+2".asTerm)(1))
  }

  it should "parse mixed arguments" in {
    BelleParser("dG({`{z'=-1*z+0}`},{`x*z^2=1`},1)") shouldBe (round trip TactixLibrary.dG("z'=-1*z+0".asDifferentialProgram, Some("x*z^2=1".asFormula))(1))
  }

  it should "expand definitions when parsing arguments" in {
    inside(BelleParser.parseWithInvGen("MR({`safeDist()>0`},1)", None, Declaration(Map()))) {
      case adpt: AppliedDependentPositionTactic => adpt.pt should have (
        'inputs ("safeDist()>0".asFormula::Nil)
      )
    }

    inside(BelleParser.parseWithInvGen("MR({`safeDist()>0`},1)", None,
        Declaration(Map(("safeDist", None) -> (None, Real, Some("y".asTerm), null))))) {
      case adpt: AppliedDependentPositionTactic => adpt.pt should have (
        'inputs ("y>0".asFormula::Nil)
      )
    }
  }

  it should "expand definitions when parsing locators" in {
    inside(BelleParser.parseWithInvGen("hideL('L=={`s=safeDist()`})", None, Declaration(Map()))) {
      case apt: AppliedPositionTactic => apt.locator shouldBe Find.FindL(0, Some("s=safeDist()".asFormula))
    }

    inside(BelleParser.parseWithInvGen("hideL('L=={`s=safeDist()`})", None,
        Declaration(Map(("safeDist", None) -> (None, Real, Some("y".asTerm), null))))) {
      case apt: AppliedPositionTactic => apt.locator shouldBe Find.FindL(0, Some("s=y".asFormula))
    }
  }

  it should "expand definitions when parsing position check locators" in {
    inside(BelleParser.parseWithInvGen("hideL(-2=={`s=safeDist()`})", None, Declaration(Map()))) {
      case apt: AppliedPositionTactic => apt.locator shouldBe Fixed(-2, Nil, Some("s=safeDist()".asFormula))
    }

    inside(BelleParser.parseWithInvGen("hideL(-2=={`s=safeDist()`})", None,
      Declaration(Map(("safeDist", None) -> (None, Real, Some("y".asTerm), null))))) {
      case apt: AppliedPositionTactic => apt.locator shouldBe Fixed(-2, Nil, Some("s=y".asFormula))
    }
  }

  //endregion

  //region New dG syntax

  "new dG syntax" should "work" in {
    val f = "x>1 -> [{x'=-x}]x>0".asFormula
    val t = "implyR(1) ; dG({`y'=1/2*y`}, {`x*y^2=1`}, 1) ; dI(1.0) ".asTactic
  }

  it should "round trip ghosts" in {
    //@todo should be on tactics is meaningless (compares names, but not arguments)
    "dG({`y'=1`}, 1)".asTactic should (be (dG("y'=1".asDifferentialProgram, None)(1)) and (print as "dG({`{y'=1}`}, 1)") and (reparse fromPrint))
    "dG({`y'=1`}, {`x*y=5`}, 1)".asTactic should (be (dG("y'=1".asDifferentialProgram, Some("x*y=5".asFormula))(1)) and (print as "dG({`{y'=1}`}, {`x*y=5`}, 1)") and (reparse fromPrint))
    "dG({`y'=0*y+1`}, {`x*y^2=1`}, 1)".asTactic should (be (dG("y'=0*y+1".asDifferentialProgram, Some("x*y^2=1".asFormula))(1)) and (print as "dG({`{y'=0*y+1}`}, {`x*y^2=1`}, 1)") and (reparse fromPrint))
    "dG({`y'=1/2*y`}, 1)".asTactic should (be (dG("y'=1/2*y".asDifferentialProgram, None)(1)) and (print as "dG({`{y'=1/2*y}`}, 1)") and (reparse fromPrint))
    "dG({`y'=1/2*y`}, {`x*y^2=1`}, 1)".asTactic should (be (dG("y'=1/2*y".asDifferentialProgram, Some("x*y^2=1".asFormula))(1)) and (print as "dG({`{y'=1/2*y}`}, {`x*y^2=1`}, 1)") and (reparse fromPrint))
  }

  //endregion
}
