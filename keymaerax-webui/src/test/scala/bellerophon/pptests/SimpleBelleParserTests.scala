package bellerophon.pptests

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.UnknownLocation
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

import scala.language.postfixOps

/**
  * Very simple positive unit tests for the Bellerophon parser. Useful for TDD and bug isolation but probably not
  * so useful for anything else.
  *
  * @note It may be useful to turn on BelleParser.DEBUG if you're actually debugging.
  * @author Nathan Fulton
  */
@UsualTest
class SimpleBelleParserTests extends TacticTestBase {
  //region Atomic tactics with arguments

  "Atomic / Argument Parser" should "parse a built-in tactic" in {
    BelleParser("nil") shouldBe TactixLibrary.nil
  }

  it should "parse a built-in tactic with arguments" in {
    BelleParser("cut({`1=1`})")
  }

  it should "parse a built-in argument with an absolute top-level postion" in {
    BelleParser("andR(1)") shouldBe TactixLibrary.andR(1)
  }

  //endregion

  //region Sequential combinator

  "Sequential parser" should "parse e & e" in {
    val result = BelleParser("andR(1) & andR(2)").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right shouldBe TactixLibrary.andR(2)
  }

  it should "parse seq right-associative -- e & e & e parses to e & (e & e)" in {
    val result = BelleParser("andR(1) & andR(2) & andR(3)").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse seq right-associative when there are a bunch of parens" in {
    val result = BelleParser("(andR(1)) & (andR(2)) & (andR(3))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e & (e & e)" in {
    val result = BelleParser("andR(1) & (andR(2) & andR(3))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse (e & e) & e" in {
    val result = BelleParser("(andR(1) & andR(2)) & andR(3)").asInstanceOf[SeqTactic]
    result.left.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }


  it should "parse compositions of things that parse to partials" in {
    val tactic = BelleParser("nil & nil").asInstanceOf[SeqTactic]
    tactic.left shouldBe TactixLibrary.nil
    tactic.right shouldBe TactixLibrary.nil
  }

  //endregion

  //region Either combinator

  "Either parser" should "parse e | e" in {
    val result = BelleParser("andR(1) | andR(2)").asInstanceOf[EitherTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right shouldBe TactixLibrary.andR(2)
  }

  it should "parse either right-associative -- e | e | e parses to e | (e | e)" in {
    val result = BelleParser("andR(1) | andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse either right-associative when there are a bunch of parens" in {
    val result = BelleParser("(andR(1)) | (andR(2)) | (andR(3))").asInstanceOf[EitherTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e | (e | e)" in {
    val result = BelleParser("andR(1) | (andR(2) | andR(3))").asInstanceOf[EitherTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(3)
  }

  it should "parse (e | e) | e" in {
    val result = BelleParser("(andR(1) | andR(2)) | andR(3)").asInstanceOf[EitherTactic]
    result.left.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }

  it should "parse e & b | c" in {
    val result = BelleParser("andR(1) & andR(2) | andR(3)").asInstanceOf[EitherTactic]
    result.left.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    result.left.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
    result.right shouldBe TactixLibrary.andR(3)
  }

  //@todo fix or decide on a precedence of | and &...
  ignore should "parse e | b & c" in {
    val result = BelleParser("andR(1) | andR(2) & andR(3)").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[EitherTactic].right shouldBe TactixLibrary.andR(2)
    result.right.asInstanceOf[EitherTactic].left shouldBe TactixLibrary.andR(3)
  }

  //endregion

  //region Branching combinator

  "Branch combinator parser" should "parse e <(e,e)" in {
    val result = BelleParser("andR(1) <(andR(2), andR(3))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(2), TactixLibrary.andR(3))
  }

  it should "parse e <()" in {
    val result = BelleParser("andR(1) <()").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq()
  }

  it should "parse e <(e)" in {
    val result = BelleParser("andR(1) <(andR(1))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(1))
  }

  it should "parse e & <(e) as well" in {
    val result = BelleParser("andR(1) & <(andR(1))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(1))
  }

  it should "parse e & <(e,e)" in {
    val result = BelleParser("andR(1) & <(andR(1), andR(1))").asInstanceOf[SeqTactic]
    result.left shouldBe TactixLibrary.andR(1)
    result.right.asInstanceOf[BranchTactic].children shouldBe Seq(TactixLibrary.andR(1), TactixLibrary.andR(1))
  }



  //endregion

  //region Kleene Star Comabinator

  "Kleene star parser" should "parse e*" in {
    val tactic = BelleParser("andR(1)*").asInstanceOf[SaturateTactic]
    tactic.child shouldBe   TactixLibrary.andR(1)
  }

  it should "parse (e&e)*" in {
    val tactic = BelleParser("(andR(1) & andR(2))*").asInstanceOf[SaturateTactic]
    tactic.child.asInstanceOf[SeqTactic].left shouldBe TactixLibrary.andR(1)
    tactic.child.asInstanceOf[SeqTactic].right shouldBe TactixLibrary.andR(2)
  }

  ignore should "get precedence right" in {
    //@todo parser get's it wrong
    val tactic = BelleParser("andR(1) & andR(2)*")
    tactic shouldBe a [SaturateTactic]
    tactic shouldBe TactixLibrary.andR(1) & (TactixLibrary.andR(2)*)
  }

  it should "parse fully parenthesized" in {
    val tactic = BelleParser("andR(1) & (andR(2)*)")
    tactic shouldBe TactixLibrary.andR(1) & (TactixLibrary.andR(2)*)
  }

  "NTIMES repeat combinator parser" should "parse e*22" in {
    val tactic = BelleParser("andR(1)*22").asInstanceOf[RepeatTactic]
    tactic.child shouldBe   TactixLibrary.andR(1)
    tactic.times shouldBe 22
  }

  "saturate parser" should "parse e+" in {
    val tactic = BelleParser("andR(1)+").asInstanceOf[SeqTactic]
    tactic.left shouldBe TactixLibrary.andR(1)
    tactic.right.asInstanceOf[SaturateTactic].child shouldBe   TactixLibrary.andR(1)
  }

  "doall combinator parser" should "parse doall(closeId)" in {
    val tactic = BelleParser("doall(closeId)")
    tactic shouldBe OnAll(TactixLibrary.closeId)
  }

  it should "parse combined tactics with parameters doall(closeId | closeTrue | andL(1))" in {
    val tactic = BelleParser("doall(closeId | closeTrue | andL(1))")
    tactic shouldBe OnAll(TactixLibrary.closeId | (TactixLibrary.closeT | TactixLibrary.andL(1)))
  }

  "Optional combinator" should "parse ?(closeId)" in {
    val tactic = BelleParser("?(closeId)")
    tactic shouldBe Idioms.?(TactixLibrary.closeId)
  }

  it should "bind stronger than seq. combinator" in {
    val tactic = BelleParser("andR(1) & ?(closeId)")
    tactic shouldBe SeqTactic(TactixLibrary.andR(1), Idioms.?(TactixLibrary.closeId))
  }

  it should "bind stronger than alt. combinator" in {
    val tactic = BelleParser("andR(1) | ?(closeId)")
    tactic shouldBe EitherTactic(TactixLibrary.andR(1), Idioms.?(TactixLibrary.closeId))
  }

  it should "bind stronger than saturation" in {
    //@note this is debatable, but was easier to implement the moment
    val tactic = BelleParser("?(andR(1))*")
    tactic shouldBe SaturateTactic(Idioms.?(TactixLibrary.andR(1)))
  }

  it should "work in the beginning of a branch" in {
    val tactic = BelleParser("andR(1) & <(?(closeId), ?(orR(1)))")
    tactic shouldBe TactixLibrary.andR(1) & Idioms.<(Idioms.?(TactixLibrary.closeId), Idioms.?(TactixLibrary.orR(1)))
  }


  //endregion

  //region Partial tactics

  "partial tactic parser" should "parse partial(e)" in {
    val tactic = BelleParser("partial(andR(1))").asInstanceOf[PartialTactic]
    tactic.child shouldBe TactixLibrary.andR(1)
  }

  it should "parse e partial" in {
    val tactic = BelleParser("andR(1) partial").asInstanceOf[PartialTactic]
    tactic.child shouldBe TactixLibrary.andR(1)
  }

  it should "parse with expected precedence" in {
    BelleParser("andL(-1) & (andR(1) partial)") shouldBe SeqTactic(TactixLibrary.andL(-1), PartialTactic(TactixLibrary.andR(1)))
    BelleParser("andL(-1) & andR(1) partial") shouldBe PartialTactic(SeqTactic(TactixLibrary.andL(-1), TactixLibrary.andR(1)))
  }

  //endregion

  //region Done tactics

  "done tactic parser" should "parse closeId & done" in {
    val tactic = BelleParser("closeId & done")
    tactic shouldBe TactixLibrary.closeId & TactixLibrary.done
  }

  it should "parse done" in {
    val tactic = BelleParser("done")
    tactic shouldBe TactixLibrary.done
  }

  it should "parse in a branch" in {
    val tactic = BelleParser("andR(1) & <(closeId & done, done)")
    tactic shouldBe TactixLibrary.andR(1) & Idioms.<(TactixLibrary.closeId & TactixLibrary.done, TactixLibrary.done)
  }

  //endregion
}
