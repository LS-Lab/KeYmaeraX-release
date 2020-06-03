package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.error
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{Position, RenUSubst}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.time.SpanSugar._
import testHelper.KeYmaeraXTestTags.SlowTest

import scala.collection.immutable.IndexedSeq
import scala.collection.mutable
import scala.language.postfixOps

import org.scalatest.Inside._
import org.scalatest.LoneElement._

/**
 * Very fine-grained tests of the sequential interpreter.
 * These tests are all I/O tests, so it should be possible to switch out
 * theInterpreter when other interpreters are implemented.
 * @author Nathan Fulton
 */
class SequentialInterpreterTests extends TacticTestBase {

  "AndR" should "prove |- 1=1 ^ 2=2" in {
    inside (theInterpreter(andR(1), BelleProvable(ProvableSig.startProof("1=1 & 2=2".asFormula)))) {
      case BelleProvable(p, _) =>
        p.subgoals should contain theSameElementsInOrderAs "==> 1=1".asSequent :: "==> 2=2".asSequent :: Nil
    }
  }

  "Sequential Combinator" should "prove |- 1=2 -> 1=2" in {
    inside (theInterpreter(implyR(1) & close, BelleProvable(ProvableSig.startProof("1=2 -> 1=2".asFormula)))) {
      case BelleProvable(p, _) => p shouldBe 'proved
    }
  }

  "Either combinator" should "prove |- 1=2 -> 1=2 by AndR | (ImplyR & Close)" in {
    inside (theInterpreter(andR(1) | (implyR(1) & close), BelleProvable(ProvableSig.startProof("1=2 -> 1=2".asFormula)))) {
      case BelleProvable(p, _) => p shouldBe 'proved
    }
  }

  it should "prove |- 1=2 -> 1=2 by (ImplyR & Close) | AndR" in {
    inside (theInterpreter((implyR(1) & close) | andR(1), BelleProvable(ProvableSig.startProof("1=2 -> 1=2".asFormula)))) {
      case BelleProvable(p, _) => p shouldBe 'proved
    }
  }

  it should "failover to right whenever a non-closing and non-partial tactic is provided on the left" in {
    val tactic = implyR(1) & DebuggingTactics.done | skip
    inside (theInterpreter(tactic, BelleProvable(ProvableSig.startProof("1=2 -> 1=2".asFormula)))) {
      case BelleProvable(p, _) => p.subgoals.loneElement shouldBe "==> 1=2 -> 1=2".asSequent
    }
  }

  it should "fail when neither tactic manages to close the goal and also neither is partial" in {
    val tactic = implyR(1) & DebuggingTactics.done | (skip & skip) & DebuggingTactics.done
    val f = "1=2 -> 1=2".asFormula
    a [BelleThrowable] should be thrownBy theInterpreter(tactic, BelleProvable(ProvableSig.startProof(f))
    )
  }

  it should "run right if left makes no progress" in {
    proveBy("x>=0 ==> \\forall y (y=x -> y>=0)".asSequent, prop | allR(1)).subgoals.loneElement shouldBe "x>=0 ==> y=x -> y>=0".asSequent
    proveBy("x>=0 -> \\forall y (y=x -> y>=0)".asFormula, SaturateTactic(prop | allR('R) | exhaustiveEqL2R('Llast))) shouldBe 'proved
  }

  "OnAll combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = andR(SuccPos(0)) & OnAll (implyR(SuccPos(0)) & close)
    proveBy(f, expr) shouldBe 'proved
  }

  it should "move inside Eithers correctly" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = andR(SuccPos(0)) & OnAll (andR(SuccPos(0)) | (implyR(SuccPos(0)) & close))
    proveBy(f, expr) shouldBe 'proved
  }

  it should "support 'Rlike unification matching" in {
    val result = proveBy("(a=0&b=1 -> c=2) | (d=3 -> e=4) | (f=5&g=6 -> h=7)".asFormula,
      SaturateTactic(orR('R)) & SaturateTactic(onAll(implyR('Rlike, "p_()&q_()->r_()".asFormula))))
    result.subgoals.loneElement shouldBe "a=0&b=1, f=5&g=6 ==> d=3->e=4, c=2, h=7".asSequent
  }

  it should "report when no unification found with 'Rlike unification matching" in {
    the [BelleProofSearchControl] thrownBy proveBy("==> a=0, b=1, c=2->d=3".asSequent,
      onAll(implyR('Rlike, "p_()&q_()->r_()".asFormula))) should have message "Position tactic implyR('R~=\"p_()&q_()->r_()\") is not applicable anywhere in succedent"

  }

  it should "support 'Llike unification matching" in {
    val result = proveBy("(a=0&b=1 -> c=2) & (d=3 -> e=4) & (f=5&g=6 -> h=7) -> i=8".asFormula,
      implyR('R) & SaturateTactic(andL('L)) & SaturateTactic(onAll(implyL('Llike, "p_()&q_()->r_()".asFormula)))
    )
    result.subgoals should have size 4
    result.subgoals(0) shouldBe "d=3->e=4 ==> i=8, a=0&b=1, f=5&g=6".asSequent
    result.subgoals(1) shouldBe "c=2, d=3->e=4 ==> i=8, f=5&g=6".asSequent
    result.subgoals(2) shouldBe "d=3->e=4, h=7 ==> i=8, a=0&b=1".asSequent
    result.subgoals(3) shouldBe "c=2, d=3->e=4, h=7 ==> i=8".asSequent
  }

  it should "fail inapplicable builtin-rules with legible error messages" in {
    the [BelleThrowable] thrownBy proveBy("x=5".asFormula, andR(1)) should have message
      """Tactic andR applied at 1 on a non-matching expression in ElidingProvable(Provable{
        |==> 1:  x=5	Equal
        |  from
        |==> 1:  x=5	Equal})""".stripMargin
  }

  "Saturate combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = SaturateTactic(
          OnAll(andR(SuccPos(0))) |
          OnAll(implyR(SuccPos(0)) & close)
        )
    proveBy(f, expr) shouldBe 'proved
  }

  it should "prove x=2&y=3&z=4 |- z=4" in {
    proveBy("x=2&y=3&z=4 ==> z=4".asSequent, SaturateTactic(andL('_)) &
      assertE("x=2".asFormula, "x=2 not at -1")(-1) & assertE("y=3".asFormula, "y=3 not at -2")(-2) &
      assertE("z=4".asFormula, "z=4 not at -3")(-3) & close) shouldBe 'proved
  }

  it should "repeat 0 times if not applicable" in {
    proveBy("x=2 ==> x=2".asSequent, SaturateTactic(andL('_)) & close) shouldBe 'proved
  }

  it should "saturate until no longer applicable" in {
    proveBy("x=2&y=3&(z=4|z=5) ==> x=2".asSequent, SaturateTactic(andL('Llast)) &
      assertE("x=2".asFormula, "x=2 not at -1")(-1) & assertE("y=3".asFormula, "y=3 not at -2")(-2) &
      assertE("z=4|z=5".asFormula, "z=4|z=5 not at -3")(-3) & close) shouldBe 'proved
  }

  it should "try right branch when used in combination with either combinator" in {
    proveBy("x=2&y=3&(z=4|z=5) ==> x=2".asSequent,
      SaturateTactic(SaturateTactic(andL('Llast)) | close)) shouldBe 'proved
  }

  it should "saturate 'Rlike' unification matching" in {
    val result = proveBy("(a=0&b=1 -> c=2) | (d=3 -> e=4) | (f=5&g=6 -> h=7)".asFormula,
      SaturateTactic(orR('R)) & SaturateTactic(implyR('Rlike, "p_()&q_()->r_()".asFormula))
      )
    result.subgoals.loneElement shouldBe "a=0&b=1, f=5&g=6 ==> d=3->e=4, c=2, h=7".asSequent
  }

  it should "trace in the database" in withDatabase { db => withMathematica { _ =>
    val fml = "[x:=3;](x>0 & x>1 & x>2)".asFormula
    val modelContent = s"ProgramVariables Real x; End.\n Problem ${fml.prettyString} End."
    db.createProof(modelContent, "saturateTest")
    db.proveBy(modelContent, SaturateTactic(onAll(boxAnd('R) & andR('R))) & master()) shouldBe 'proved
  }}

  it should "not endless repeat on new labels" in {
    failAfter(1 second) {
      proveBy("x>=0 ==> x>=0".asSequent, SaturateTactic(label("A label"))).subgoals.loneElement shouldBe "x>=0 ==> x>=0".asSequent
    }
  }

  "Repeat combinator" should "repeat the specified number of times" in {
    proveBy("x=2&y=3&z=4 ==> x=2".asSequent, andL('L)*0).subgoals.loneElement shouldBe "x=2&y=3&z=4 ==> x=2".asSequent
    proveBy("x=2&y=3&z=4 ==> x=2".asSequent, andL('L)*1).subgoals.loneElement shouldBe "x=2, y=3&z=4 ==> x=2".asSequent
    proveBy("x=2&y=3&z=4 ==> x=2".asSequent, andL('L)*2).subgoals.loneElement shouldBe "x=2, y=3, z=4 ==> x=2".asSequent
    val ex = the [IllFormedTacticApplicationException] thrownBy proveBy("x=2&y=3&z=4 ==> x=2".asSequent, andL('L)*3)
    ex should have message "RepeatTactic failed on repetition 3"
    ex.getCause should have message "Position tactic andL('L) is not applicable anywhere in antecedent"
  }

  "+ combinator" should "saturate with at least 1 repetition" in {
    val result = proveBy("x=2&y=3&(z=4|z=5) ==> x=2".asSequent, andL('Llast) & SaturateTactic(andL('Llast)))
    result.subgoals.loneElement shouldBe "x=2, y=3, z=4 | z=5 ==> x=2".asSequent
  }

  it should "fail when not at least 1 repetition is possible" in {
    a [BelleThrowable] should be thrownBy proveBy("z=4|z=5 ==> x=2".asSequent,
      andL('Llast) & SaturateTactic(andL('Llast)))
  }

  it should "saturate with at least 1 repetition and try right branch in combination with either combinator" in {
    proveBy("x=2&y=3&(z=4|z=5) ==> x=2".asSequent,
      SaturateTactic((andL('Llast) & SaturateTactic(andL('Llast))) | close)) shouldBe 'proved
  }

  "must idiom" should "fail when no change occurs" in {
    a [BelleThrowable] should be thrownBy proveBy("x=2".asFormula, Idioms.must(skip))
  }

  it should "do nothing when change occurred" in {
    val result = proveBy("x=2|x=3".asFormula, Idioms.must(orR(1)))
    result.subgoals.loneElement shouldBe " ==> x=2, x=3".asSequent
  }

  "Branch Combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val tactic = andR(SuccPos(0)) < (
      implyR(SuccPos(0)) & close,
      implyR(SuccPos(0)) & close
    )
    inside (theInterpreter.apply(tactic, BelleProvable(ProvableSig.startProof("(1=1->1=1) & (2=2->2=2)".asFormula)))) {
      case BelleProvable(p, _) => p shouldBe 'proved
    }
  }

  it should "prove |- (1=1->1=1) & (2=2->2=2) with new < combinator" in {
    //@note cannot use < in unit tests without fully qualifying the name, because Matchers also knows < operator
    val tactic = andR(SuccPos(0)) & Idioms.<(
      implyR(SuccPos(0)) & close,
      implyR(SuccPos(0)) & close
      )
    inside (theInterpreter.apply(tactic, BelleProvable(ProvableSig.startProof("(1=1->1=1) & (2=2->2=2)".asFormula)))) {
      case BelleProvable(p, _) => p shouldBe 'proved
    }
  }

  it should "handle cases were subgoals are added." in {
    val tactic = andR(SuccPos(0)) < (
      andR(SuccPos(0)),
      implyR(SuccPos(0)) & close
    )
    proveBy("(2=2 & 3=3) & (1=1->1=1)".asFormula, tactic).subgoals should contain
      theSameElementsInOrderAs("==> 2=2".asSequent :: "==> 3=3".asSequent :: Nil)
  }

  it should "fail whenever there's a non-partial tactic that doesn't close its goal." in {
    val tactic = andR(SuccPos(0)) < (
      andR(SuccPos(0)) & DebuggingTactics.done,
      implyR(SuccPos(0)) & close & DebuggingTactics.done
      )
    val f = "(2=2 & 3=3) & (1=1->1=1)".asFormula
    a [BelleThrowable] shouldBe thrownBy(
      theInterpreter.apply(tactic, BelleProvable(ProvableSig.startProof(f)))
    )
  }

  it should "handle cases were subgoals are added -- switch order" in {
    val tactic = andR(SuccPos(0)) <(
      implyR(SuccPos(0)) & close,
      andR(SuccPos(0))
      )
    proveBy("(1=1->1=1) & (2=2 & 3=3)".asFormula, tactic).subgoals should contain
      theSameElementsInOrderAs("==> 2=2".asSequent :: "==> 3=3".asSequent :: Nil)
  }

  it should "prove |- (1=1->1=1) & (!2=2  | 2=2) with labels out of order" in {
    val tactic = andR(1) & Idioms.<(label("foo"), label("bar")) & Idioms.<(
      (BelleTopLevelLabel("bar"), orR(1) & notR(1) & close),
      (BelleTopLevelLabel("foo"), implyR(1) & close)
    )
    inside (theInterpreter.apply(tactic, BelleProvable(ProvableSig.startProof("(1=1->1=1) & (!2=2 | 2=2)".asFormula)))) {
      case BelleProvable(p, _) => p shouldBe 'proved
    }
  }

  it should "work with loop labels" in {
    val tactic = implyR(1) & loop("x>1".asFormula)(1)
    val v = BelleProvable(ProvableSig.startProof("x>2 -> [{x:=x+1;}*]x>0".asFormula))
    inside (theInterpreter.apply(tactic, v)) {
      case BelleProvable(p, Some(l)) =>
        p.subgoals should have size 3
        l should contain theSameElementsInOrderAs(BelleLabels.initCase :: BelleLabels.useCase :: BelleLabels.indStep :: Nil)
    }
  }

  it should "not screw up empty labels" in {
    proveBy(
      "((P_() <-> F_()) & (F_() -> (Q_() <-> G_()))) ->(P_() & Q_() <-> F_() & G_())".asFormula, prop) shouldBe 'proved
  }

  it should "finish working branches before failing" in {
    BelleInterpreter.setInterpreter(registerInterpreter(ExhaustiveSequentialInterpreter()))

    var finishedBranches = Seq.empty[Int]
    def logDone(branch: Int) = new DependentTactic("ANON") {
      override def computeExpr(provable: ProvableSig): BelleExpr = {
        finishedBranches = finishedBranches :+ branch
        skip
      }
    }

    a [BelleThrowable] should be thrownBy proveBy("x>0 -> x>5 & x>0 & [?x>1;]x>1".asFormula, implyR(1) & andR(1) <(
      DebuggingTactics.printIndexed("Branch 1") & closeId & /* not reached */ logDone(1),
      andR(1) <(
        DebuggingTactics.printIndexed("Branch 2") & closeId & logDone(2)
        ,
        DebuggingTactics.printIndexed("Branch 3") & testb(1) & prop & logDone(3)
      )
    ))

    finishedBranches should contain theSameElementsAs Seq(2, 3)
  }

  it should "finish working branches before failing with combined error message" in {
    BelleInterpreter.setInterpreter(registerInterpreter(ExhaustiveSequentialInterpreter()))

    var finishedBranches = Seq.empty[Int]
    def logDone(branch: Int) = new DependentTactic("ANON") {
      override def computeExpr(provable: ProvableSig): BelleExpr = {
        finishedBranches = finishedBranches :+ branch
        skip
      }
    }

    the [BelleThrowable] thrownBy proveBy("x>0 -> x>5 & x>2 & [?x>1;]x>1".asFormula, implyR(1) & andR(1) <(
      DebuggingTactics.printIndexed("Branch 1") & closeId & /* not reached */ logDone(1),
      andR(1) <(
        DebuggingTactics.printIndexed("Branch 2") & closeId & /* not reached */ logDone(2)
        ,
        DebuggingTactics.printIndexed("Branch 3") & testb(1) & prop & logDone(3)
      )
    )) should have message
      """Left: Unable to create dependent tactic 'id', cause: requirement failed: Expects same formula in antecedent and succedent. Found:
        |   -1:  x>0	Greater
        |==> 1:  x>5	Greater
        |Right: Unable to create dependent tactic 'id', cause: requirement failed: Expects same formula in antecedent and succedent. Found:
        |   -1:  x>0	Greater
        |==> 1:  x>2	Greater)""".stripMargin

    finishedBranches should contain theSameElementsAs Seq(3)
  }

  it should "assign labels correctly to remaining open subgoals" in withMathematica { _ =>
    proveBy("x>=0 -> [{x:=x+1; ++ x:=x+2;}*]x>0".asFormula, implyR(1) &
      loop("x>=0".asFormula)(1) <(
        QE,
        QE,
        choiceb(1) & andR(1) <(
          assignb(1) & label("1"),
          assignb(1)
        )
      ), (labels: Option[List[BelleLabel]]) => {
      labels shouldBe Some(
        BelleLabels.useCase.append(BelleLabels.QECEX) ::
        BelleSubLabel(BelleLabels.indStep, "1") ::
        BelleLabels.indStep :: Nil)
    })
  }

  "Let" should "fail (but not horribly) when inner proof cannot be started" in {
    val fml = "[{f'=g}][{g'=5}]f>=0".asFormula
    the [Throwable] thrownBy proveBy(fml, BelleParser("let ({`f()=f`}) in (nil)")) should have message
      "Unable to start inner proof in let: edu.cmu.cs.ls.keymaerax.core.FuncOf cannot be cast to edu.cmu.cs.ls.keymaerax.core.Variable"
    val result = proveBy(fml, BelleParser("let ({`f()=f`}) in (nil) | nil"))
    result.subgoals.loneElement shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
  }

  "Unification" should "work on 1=1->1=1" in {
    val pattern = SequentType("==> p() -> p()".asSequent)
    val e = USubstPatternTactic(Seq((pattern, (x:RenUSubst) => implyR(SuccPos(0)) & close)))
    proveBy("1=1->1=1".asFormula, e) shouldBe 'proved
  }

  it should "work when there are non-working patterns" in {
    val pattern1 = SequentType("==> p() -> p()".asSequent)
    val pattern2 = SequentType("==> p() & q()".asSequent)
    val e = USubstPatternTactic(Seq(
      (pattern2, (_: RenUSubst) => error("Should never get here.")),
      (pattern1, (_: RenUSubst) => implyR(SuccPos(0)) & close)
    ))
    proveBy("1=1->1=1".asFormula, e) shouldBe 'proved
  }

  it should "work when there are non-working patterns -- flipped order." in {
    val pattern1 = SequentType("==> p() -> p()".asSequent)
    val pattern2 = SequentType("==> p() & q()".asSequent)
    val e = USubstPatternTactic(Seq(
      (pattern1, (_: RenUSubst) => implyR(1) & close),
      (pattern2, (_: RenUSubst) => error("Should never get here."))
    ))
    proveBy("1=1->1=1".asFormula, e) shouldBe 'proved
  }

  it should "choose the first applicable unification when there are many options" in {
    val pattern1 = SequentType("==> p() -> p()".asSequent)
    val pattern2 = SequentType("==> p() -> q()".asSequent)
    val e = USubstPatternTactic(Seq(
      (pattern1, (_: RenUSubst) => implyR(1) & close),
      (pattern2, (_: RenUSubst) => error("Should never get here."))
    ))
    proveBy("1=1->1=1".asFormula, e) shouldBe 'proved
  }

  it should "choose the first applicable unification when there are many options -- flipped order" in {
    val pattern1 = SequentType("==> p() -> p()".asSequent)
    val pattern2 = SequentType("==> p() -> q()".asSequent)
    val e = USubstPatternTactic(Seq(
      (pattern2, (_: RenUSubst) => error("Should never get here.")),
      (pattern1, (_: RenUSubst) => implyR(1) & close)
    ))
    a [BelleThrowable] shouldBe thrownBy (proveBy("1=1->1=1".asFormula, e))
  }

  "AtSubgoal" should "work" in {
    val t = andR(1) &
      Idioms.atSubgoal(0, implyR(1) & close) &
      Idioms.atSubgoal(0, implyR(1) & close)
    proveBy("(1=1->1=1) & (2=2->2=2)".asFormula, t) shouldBe 'proved
  }

  //@todo would need DerivationInfo entry
  //@note: DifferentialTests."ODE" should "prove FM tutorial 4" acts as a smoke test for this
  "ChooseSome" should "record in the database" ignore withDatabase { db => withMathematica { _ =>
    val fml = "x>0 -> [{x:=3;}*]x>0".asFormula
    val modelContent = s"Variables. R x. End.\n Problem. ${fml.prettyString} End."
    db.createProof(modelContent, "chooseSomeTest")

    import TacticFactory._

    val tactic = "chooseSomeTest" by ((pos: Position, seq: Sequent) => { ChooseSome(
        () => ("x>0".asFormula::Nil).iterator,
        (inv: Formula) => loop(inv)(pos)
      ) & Idioms.<(close, close, master())
    })

    db.proveBy(modelContent, tactic(1)) shouldBe 'proved
  }}

  def testTimeoutAlternatives(fml: Formula, t: Seq[BelleExpr], timeout: Long): (ProvableSig, Seq[String]) = {
    val namesToRecord = t.map(_.prettyString)
    val listener = new IOListener {
      val calls: mutable.Buffer[String] = mutable.Buffer[String]()
      override def begin(input: BelleValue, expr: BelleExpr): Unit = {
        val name = expr.prettyString
        if (namesToRecord.contains(name)) calls += name
      }
      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
      override def kill(): Unit = {}
    }

    val BelleProvable(result, _) = ExhaustiveSequentialInterpreter(listener::Nil)(
      TimeoutAlternatives(t, timeout),
      BelleProvable(ProvableSig.startProof(fml))
    )
    (result, listener.calls)
  }

  "TimeoutAlternatives" should "succeed sole alternative" in {
    val (result, recorded) = testTimeoutAlternatives("x>=0 -> x>=0".asFormula, prop::Nil, 1000)
    result shouldBe 'proved
    recorded should contain theSameElementsInOrderAs("prop" :: Nil)
  }

  it should "fail on timeout" in {
    val wait: BuiltInTactic = new BuiltInTactic("wait") {
      def result(p: ProvableSig): ProvableSig = { Thread.sleep(5000); p }
    }
    the [BelleNoProgress] thrownBy testTimeoutAlternatives("x>=0 -> x>=0".asFormula, wait::Nil, 1000) should have message "Alternative timed out"
  }

  it should "succeed the first succeeding alternative" in {
    val (result, recorded) = testTimeoutAlternatives("x>=0 -> x>=0".asFormula,
      prop::DebuggingTactics.error("Should not be executed")::Nil, 1000)
    result shouldBe 'proved
    recorded should contain theSameElementsInOrderAs("prop" :: Nil)
  }

  it should "try until one succeeds" in {
    val (result, recorded) = testTimeoutAlternatives("x>=0 -> x>=0".asFormula, (implyR(1)&done)::prop::Nil, 1000)
    result shouldBe 'proved
    recorded should contain theSameElementsInOrderAs("(implyR(1)&done())" :: "prop" :: Nil)
  }

  it should "stop trying on timeout" in {
    val wait: BuiltInTactic = new BuiltInTactic("wait") {
      def result(p: ProvableSig): ProvableSig = { Thread.sleep(5000); p }
    }
    the [BelleThrowable] thrownBy testTimeoutAlternatives("x>=0 -> x>=0".asFormula,
      wait::DebuggingTactics.error("Should not be executed")::Nil, 1000) should have message "Alternative timed out"
  }

  "Def tactic" should "define a tactic and apply it later" in {
    val fml = "x>0 -> [x:=2;++x:=x+1;]x>0".asFormula
    val tDef = DefTactic("myAssign", assignb('R))
    val tactic = tDef & implyR(1) & choiceb(1) & andR(1) & OnAll(ApplyDefTactic(tDef))
    val result = proveBy(fml, tactic)
    result.subgoals should have size 2
    result.subgoals.head shouldBe "x>0 ==> 2>0".asSequent
    result.subgoals.last shouldBe "x>0 ==> x+1>0".asSequent
  }

//  "Scheduled tactics" should "work" in {
//    val legacyTactic = tactics.TacticLibrary.arithmeticT
//    val t = Legacy.initializedScheduledTactic(DefaultConfiguration.defaultMathematicaConfig, legacyTactic)
//    shouldClose(t, "1=1".asFormula)
//  }
//
//  it should "work again" in {
//    val legacyTactic = tactics.TacticLibrary.arithmeticT
//    val t = Legacy.initializedScheduledTactic(DefaultConfiguration.defaultMathematicaConfig, legacyTactic)
//    shouldClose(t, "x = 0 -> x^2 = 0".asFormula)
//  }
//
//
//  it should "work for non-arith things" in {
//    val legacyTactic = tactics.PropositionalTacticsImpl.AndRightT(SuccPos(0))
//    val t = Legacy.initializedScheduledTactic(DefaultConfiguration.defaultMathematicaConfig, legacyTactic) < (
//      implyR(SuccPos(0)) & close,
//      implyR(SuccPos(0)) & close
//      )
//    shouldClose(t, "(1=1->1=1) & (1=2->1=2)".asFormula)
//  }

  /*"A failing tactic"*/
  it should "print nice errors and provide a stack trace" ignore {
    val itFails: BelleExpr = new BuiltInTactic("fails") {
      override def result(provable: ProvableSig) = throw new ProverException("Fails...")
    }

    val conj = Idioms.nil & (itFails | itFails)

    // now try with defs
    def repTwo = conj*2

    def split = andR(1) <(
        repTwo,
        skip)

    val thrown = intercept[Throwable] {
      theInterpreter.apply(Idioms.nil
        & Idioms.nil
        & split
        & Idioms.nil
        & Idioms.nil, BelleProvable(ProvableSig.startProof("1=1 & 2=2".asFormula)))
    }
    thrown.printStackTrace()
    thrown.getMessage should include ("Fails...")
    val s = thrown.getCause.getStackTrace
    //@todo works in isolation, but when run with other tests, we pick up stack trace elements of those too
    s.filter(_.getFileName == "SequentialInterpreterTests.scala").slice(0, 11).map(_.getLineNumber) shouldBe Array(280, 279, 278, 271, 271, 269, 266, 266, 263, 262, 276)
  }

  "Lazy interpreter" should "fail on the first failing branch" in {
    val listener = new IOListener {
      val calls: mutable.Buffer[BelleExpr] = mutable.Buffer[BelleExpr]()
      override def begin(input: BelleValue, expr: BelleExpr): Unit = calls += expr
      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
      override def kill(): Unit = {}
    }
    the [BelleThrowable] thrownBy LazySequentialInterpreter(listener::Nil)(
      "andR(1) & <(close, close)".asTactic,
      BelleProvable(ProvableSig.startProof("false & true".asFormula))) should have message
        """Inapplicable close
          |Provable{
          |==> 1:  false	False$
          |  from
          |==> 1:  false	False$}""".stripMargin

    listener.calls should have size 5
    listener.calls should contain theSameElementsInOrderAs(
      "andR(1) & <(close, close)".asTactic :: "andR(1)".asTactic ::
      BranchTactic("close".asTactic :: "close".asTactic :: Nil) :: "close".asTactic ::
      DebuggingTactics.error("Inapplicable close") :: Nil)
  }

  "Exhaustive interpreter" should "explore all branches regardless of failing ones" in {
    val listener = new IOListener {
      val calls: mutable.Buffer[BelleExpr] = mutable.Buffer[BelleExpr]()
      override def begin(input: BelleValue, expr: BelleExpr): Unit = calls += expr
      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
      override def kill(): Unit = {}
    }
    the [BelleThrowable] thrownBy ExhaustiveSequentialInterpreter(listener::Nil)(
      "andR(1) & <(close, close)".asTactic,
      BelleProvable(ProvableSig.startProof("false & true".asFormula))) should have message
        """Inapplicable close
          |Provable{
          |==> 1:  false	False$
          |  from
          |==> 1:  false	False$}""".stripMargin

    listener.calls should have size 7
    listener.calls should contain theSameElementsInOrderAs(
      "andR(1) & <(close, close)".asTactic :: "andR(1)".asTactic ::
      BranchTactic("close".asTactic :: "close".asTactic :: Nil) :: "close".asTactic ::
      DebuggingTactics.error("Inapplicable close") :: "close".asTactic :: ProofRuleTactics.closeTrue(1) :: Nil)
  }

  it should "confirm that interpreter debug information slows down search" taggedAs SlowTest in {
    val ante = (1 to 100).map(i => Equal(Variable("x", Some(i)), Number(1))).reduce(And)
    val succ = (1 to 50).map(i => Box(Assign(Variable("y", Some(i)), Number(2)), Greater(Variable("y", Some(i)), Number(1)))).reduce(Or)

    // should take about 1min
    failAfter(2 minutes) {
      val BelleProvable(result, _) = ExhaustiveSequentialInterpreter(Nil, throwWithDebugInfo = true)(
        SaturateTactic(implyR('R) | andL('L) | orR('R) | assignb('R)),
        BelleProvable(ProvableSig.startProof(Imply(ante, succ)))
      )
      result.subgoals.head.ante should have size 100
      result.subgoals.head.succ should have size 50
      result.subgoals.head.succ.foreach(_ shouldBe a [Greater])
    }
  }

  it should "not spend extensive time searching positions without debug information" in {
    val ante = (1 to 100).map(i => Equal(Variable("x", Some(i)), Number(1))).reduce(And)
    val succ = (1 to 50).map(i => Box(Assign(Variable("y", Some(i)), Number(2)), Greater(Variable("y", Some(i)), Number(1)))).reduce(Or)

    // should take about 500ms
    failAfter(2 seconds) {
      val BelleProvable(result, _) = ExhaustiveSequentialInterpreter(Nil)(
        SaturateTactic(implyR('R) | andL('L) | orR('R) | assignb('R)),
        BelleProvable(ProvableSig.startProof(Imply(ante, succ)))
      )
      result.subgoals.head.ante should have size 100
      result.subgoals.head.succ should have size 50
      result.subgoals.head.succ.foreach(_ shouldBe a [Greater])
    }
  }

  it should "stop saturation when proof is closed" in {
    val listener = new IOListener {
      val calls: mutable.Buffer[BelleExpr] = mutable.Buffer[BelleExpr]()
      override def begin(input: BelleValue, expr: BelleExpr): Unit = expr match {
        case NamedTactic(name, _) if name == "prop" => calls += expr
        case _ =>
      }
      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
      override def kill(): Unit = {}
    }
    ExhaustiveSequentialInterpreter(listener :: Nil)(
      SaturateTactic(prop),
      BelleProvable(ProvableSig.startProof("x>0 -> x>0".asFormula))
    ) match {
      case BelleProvable(pr, _) => pr shouldBe 'proved
    }
    listener.calls should have size 1
  }

  "Tactics with delayed substitution" should "replay expandAll" in {
    val entry = KeYmaeraXArchiveParser(
      """ArchiveEntry "Delayed Substitution"
        |Definitions Bool p(Real x) <-> x>0; Bool q(Real y) <-> y>0; End.
        |ProgramVariables Real x; Real y; End.
        |Problem p(x) -> [y:=x;]q(y) End.
        |End.""".stripMargin).head

    proveBy(entry.model.asInstanceOf[Formula],
      ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "==> x>0 -> [y:=x;]y>0".asSequent, "Unexpected expand result") &
        implyR(1) & assignb(1) & closeId) shouldBe 'proved

    proveBy(entry.model.asInstanceOf[Formula],
      implyR(1) & assignb(1) &
        DebuggingTactics.assert(_ == "p(x) ==> q(x)".asSequent, "Unexpected result prior to expand") &
        ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "x>0 ==> x>0".asSequent, "Unexpected expand result") &
        closeId) shouldBe 'proved
  }

  it should "replay when expanded on branches" in {
    val entry = KeYmaeraXArchiveParser(
      """ArchiveEntry "Delayed Substitution"
        |Definitions Bool p(Real x) <-> x>0; Bool q(Real y) <-> y>0; End.
        |ProgramVariables Real x; Real y; End.
        |Problem p(x) -> [y:=x; ++ ?q(y);]q(y) End.
        |End.""".stripMargin).head

    proveBy(entry.model.asInstanceOf[Formula],
      ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "==> x>0 -> [y:=x; ++ ?y>0;]y>0".asSequent, "Unexpected expand result") &
        implyR(1) & choiceb(1) & andR(1) <(assignb(1) & closeId, testb(1) & implyR(1) & closeId)) shouldBe 'proved

    proveBy(entry.model.asInstanceOf[Formula],
      implyR(1) & choiceb(1) & andR(1) <(
        assignb(1) &
        DebuggingTactics.assert(_ == "p(x) ==> q(x)".asSequent, "Unexpected result prior to expand") &
        ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "x>0 ==> x>0".asSequent, "Unexpected expand result") &
        closeId
        ,
        testb(1) & implyR(1) &
        DebuggingTactics.assert(_ == "p(x),q(y) ==> q(y)".asSequent, "Unexpected result prior to expand") &
        ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "x>0,y>0 ==> y>0".asSequent, "Unexpected expand result") &
        closeId)
        ) shouldBe 'proved
  }

  it should "replay when expanded only on some branches" in {
    val entry = KeYmaeraXArchiveParser(
      """ArchiveEntry "Delayed Substitution"
        |Definitions Bool p(Real x) <-> x>0; Bool q(Real y) <-> y>0; End.
        |ProgramVariables Real x; Real y; End.
        |Problem p(x) -> [y:=x; ++ ?q(y);]q(y) End.
        |End.""".stripMargin).head

    proveBy(entry.model.asInstanceOf[Formula],
      implyR(1) & choiceb(1) & andR(1) <(
        assignb(1) &
          DebuggingTactics.assert(_ == "p(x) ==> q(x)".asSequent, "Unexpected result prior to expand") &
          ExpandAll(entry.defs.substs) &
          DebuggingTactics.assert(_ == "x>0 ==> x>0".asSequent, "Unexpected expand result") &
          closeId
        ,
        testb(1) & implyR(1) & closeId)
    ) shouldBe 'proved

    // branches in reverse order
    proveBy(entry.model.asInstanceOf[Formula],
      implyR(1) & choiceb(1) & useAt(Ax.andCommute)(1) & andR(1) <(
        testb(1) & implyR(1) & closeId
        ,
        assignb(1) &
        DebuggingTactics.assert(_ == "p(x) ==> q(x)".asSequent, "Unexpected result prior to expand") &
        ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "x>0 ==> x>0".asSequent, "Unexpected expand result") &
        closeId)
    ) shouldBe 'proved
  }
}
