package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.error
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.anon
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position, RenUSubst}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.time.SpanSugar._
import testHelper.KeYmaeraXTestTags.{SlowTest, TodoTest}

import scala.collection.mutable
import scala.language.postfixOps
import org.scalatest.Inside._
import org.scalatest.LoneElement._
import org.scalatest.OptionValues._

/**
 * Very fine-grained tests of the sequential interpreter.
 * These tests are all I/O tests, so it should be possible to switch out
 * theInterpreter when other interpreters are implemented.
 * @author Nathan Fulton
 */
class SequentialInterpreterTests extends TacticTestBase {

  "Locators" should "apply searchy with sub-positions" in withTactics {
    inside(theInterpreter(composeb(Find.FindRPlain("[x:=2;][y:=*;?y>=x;]y>=2".asFormula, PosInExpr(1::Nil))),
      BelleProvable.plain(ProvableSig.startProof("==> [x:=2;][y:=*;?y>=x;]y>=2".asSequent)))) {
      case BelleProvable(p, _, _) =>
        p.subgoals.loneElement shouldBe "==> [x:=2;][y:=*;][?y>=x;]y>=2".asSequent
    }
  }

  "AndR" should "prove |- 1=1 ^ 2=2" in withMathematica { _ =>
    inside (theInterpreter(andR(1), BelleProvable.plain(ProvableSig.startProof("1=1 & 2=2".asFormula)))) {
      case BelleProvable(p, _, _) =>
        p.subgoals should contain theSameElementsInOrderAs "==> 1=1".asSequent :: "==> 2=2".asSequent :: Nil
    }
  }

  "Sequential Combinator" should "prove |- 1=2 -> 1=2" in withMathematica { _ =>
    inside (theInterpreter(implyR(1) & close, BelleProvable.plain(ProvableSig.startProof("1=2 -> 1=2".asFormula)))) {
      case BelleProvable(p, _, _) => p shouldBe 'proved
    }
  }

  "Either combinator" should "prove |- 1=2 -> 1=2 by AndR | (ImplyR & Close)" in withMathematica { _ =>
    inside (theInterpreter(andR(1) | (implyR(1) & close), BelleProvable.plain(ProvableSig.startProof("1=2 -> 1=2".asFormula)))) {
      case BelleProvable(p, _, _) => p shouldBe 'proved
    }
  }

  it should "prove |- 1=2 -> 1=2 by (ImplyR & Close) | AndR" in withMathematica { _ =>
    inside (theInterpreter((implyR(1) & close) | andR(1), BelleProvable.plain(ProvableSig.startProof("1=2 -> 1=2".asFormula)))) {
      case BelleProvable(p, _, _) => p shouldBe 'proved
    }
  }

  it should "failover to right whenever a non-closing and non-partial tactic is provided on the left" in withMathematica { _ =>
    val tactic = implyR(1) & DebuggingTactics.done | skip
    inside (theInterpreter(tactic, BelleProvable.plain(ProvableSig.startProof("1=2 -> 1=2".asFormula)))) {
      case BelleProvable(p, _, _) => p.subgoals.loneElement shouldBe "==> 1=2 -> 1=2".asSequent
    }
  }

  it should "fail when neither tactic manages to close the goal and also neither is partial" in withMathematica { _ =>
    val tactic = implyR(1) & DebuggingTactics.done | (skip & skip) & DebuggingTactics.done
    val f = "1=2 -> 1=2".asFormula
    a [BelleThrowable] should be thrownBy theInterpreter(tactic, BelleProvable.plain(ProvableSig.startProof(f))
    )
  }

  it should "run right if left makes no progress" in withMathematica { _ =>
    proveBy("x>=0 ==> \\forall y (y=x -> y>=0)".asSequent, prop | allR(1)).subgoals.loneElement shouldBe "x>=0 ==> y=x -> y>=0".asSequent
    proveBy("x>=0 -> \\forall y (y=x -> y>=0)".asFormula, SaturateTactic(prop | allR('R) | exhaustiveEqL2R('Llast))) shouldBe 'proved
  }

  "OnAll combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in withMathematica { _ =>
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = andR(SuccPos(0)) & OnAll (implyR(SuccPos(0)) & close)
    proveBy(f, expr) shouldBe 'proved
  }

  it should "move inside Eithers correctly" in withMathematica { _ =>
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = andR(SuccPos(0)) & OnAll (andR(SuccPos(0)) | (implyR(SuccPos(0)) & close))
    proveBy(f, expr) shouldBe 'proved
  }

  it should "support 'Rlike unification matching" in withMathematica { _ =>
    val result = proveBy("(a=0&b=1 -> c=2) | (d=3 -> e=4) | (f=5&g=6 -> h=7)".asFormula,
      SaturateTactic(orR('R)) & SaturateTactic(onAll(implyR('Rlike, "p_()&q_()->r_()".asFormula))))
    result.subgoals.loneElement shouldBe "a=0&b=1, f=5&g=6 ==> d=3->e=4, c=2, h=7".asSequent
  }

  it should "report when no unification found with 'Rlike unification matching" in withMathematica { _ =>
    the [BelleProofSearchControl] thrownBy proveBy("==> a=0, b=1, c=2->d=3".asSequent,
      onAll(implyR('Rlike, "p_()&q_()->r_()".asFormula))) should have message
      """Not found: locator 'R~="p_()&q_()->r_()"
        |of position tactic implyR('R~="p_()&q_()->r_()")
        |does not match anywhere in succedent of
        |ElidingProvable(Provable{
        |==> 1:  a=0	Equal
        |    2:  b=1	Equal
        |    3:  c=2->d=3	Imply
        |  from
        |==> 1:  a=0	Equal
        |    2:  b=1	Equal
        |    3:  c=2->d=3	Imply})""".stripMargin

  }

  it should "support 'Llike unification matching" in withMathematica { _ =>
    val result = proveBy("(a=0&b=1 -> c=2) & (d=3 -> e=4) & (f=5&g=6 -> h=7) -> i=8".asFormula,
      implyR('R) & SaturateTactic(andL('L)) & SaturateTactic(onAll(implyL('Llike, "p_()&q_()->r_()".asFormula)))
    )
    result.subgoals should have size 4
    result.subgoals(0) shouldBe "d=3->e=4 ==> i=8, a=0&b=1, f=5&g=6".asSequent
    result.subgoals(1) shouldBe "c=2, d=3->e=4 ==> i=8, f=5&g=6".asSequent
    result.subgoals(2) shouldBe "d=3->e=4, h=7 ==> i=8, a=0&b=1".asSequent
    result.subgoals(3) shouldBe "c=2, d=3->e=4, h=7 ==> i=8".asSequent
  }

  it should "fail inapplicable builtin-rules with legible error messages" in withMathematica { _ =>
    the [BelleThrowable] thrownBy proveBy("x=5".asFormula, andR(1)) should
      have message "Tactic andR applied at 1 on a non-matching expression in ==> 1:  x=5\tEqual"
  }

  "Saturate combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in withMathematica { _ =>
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = SaturateTactic(
          OnAll(andR(SuccPos(0))) |
          OnAll(implyR(SuccPos(0)) & close)
        )
    proveBy(f, expr) shouldBe 'proved
  }

  it should "prove x=2&y=3&z=4 |- z=4" in withMathematica { _ =>
    proveBy("x=2&y=3&z=4 ==> z=4".asSequent, SaturateTactic(andL('_)) &
      assertE("x=2".asFormula, "x=2 not at -1")(-1) & assertE("y=3".asFormula, "y=3 not at -2")(-2) &
      assertE("z=4".asFormula, "z=4 not at -3")(-3) & close) shouldBe 'proved
  }

  it should "repeat 0 times if not applicable" in withMathematica { _ =>
    proveBy("x=2 ==> x=2".asSequent, SaturateTactic(andL('_)) & close) shouldBe 'proved
  }

  it should "saturate until no longer applicable" in withMathematica { _ =>
    proveBy("x=2&y=3&(z=4|z=5) ==> x=2".asSequent, SaturateTactic(andL('Llast)) &
      assertE("x=2".asFormula, "x=2 not at -1")(-1) & assertE("y=3".asFormula, "y=3 not at -2")(-2) &
      assertE("z=4|z=5".asFormula, "z=4|z=5 not at -3")(-3) & close) shouldBe 'proved
  }

  it should "try right branch when used in combination with either combinator" in withMathematica { _ =>
    proveBy("x=2&y=3&(z=4|z=5) ==> x=2".asSequent,
      SaturateTactic(SaturateTactic(andL('Llast)) | close)) shouldBe 'proved
  }

  it should "saturate 'Rlike' unification matching" in withMathematica { _ =>
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

  it should "not endless repeat on new labels" in withMathematica { _ =>
    failAfter(1 second) {
      proveBy("x>=0 ==> x>=0".asSequent, SaturateTactic(label("A label"))).subgoals.loneElement shouldBe "x>=0 ==> x>=0".asSequent
    }
  }

  "Repeat combinator" should "repeat the specified number of times" in withMathematica { _ =>
    proveBy("x=2&y=3&z=4 ==> x=2".asSequent, andL('L)*0).subgoals.loneElement shouldBe "x=2&y=3&z=4 ==> x=2".asSequent
    proveBy("x=2&y=3&z=4 ==> x=2".asSequent, andL('L)*1).subgoals.loneElement shouldBe "x=2, y=3&z=4 ==> x=2".asSequent
    proveBy("x=2&y=3&z=4 ==> x=2".asSequent, andL('L)*2).subgoals.loneElement shouldBe "x=2, y=3, z=4 ==> x=2".asSequent
    val ex = the [IllFormedTacticApplicationException] thrownBy proveBy("x=2&y=3&z=4 ==> x=2".asSequent, andL('L)*3)
    ex should have message "RepeatTactic failed on repetition 3"
    ex.getCause should have message
      """Not found: locator 'L
        |of position tactic andL('L)
        |does not match anywhere in antecedent of
        |ElidingProvable(Provable{
        |   -1:  x=2&y=3&z=4	And
        |==> 1:  x=2	Equal
        |  from
        |   -1:  x=2	Equal
        |   -2:  y=3	Equal
        |   -3:  z=4	Equal
        |==> 1:  x=2	Equal})""".stripMargin
  }

  "+ combinator" should "saturate with at least 1 repetition" in withMathematica { _ =>
    val result = proveBy("x=2&y=3&(z=4|z=5) ==> x=2".asSequent, andL('Llast) & SaturateTactic(andL('Llast)))
    result.subgoals.loneElement shouldBe "x=2, y=3, z=4 | z=5 ==> x=2".asSequent
  }

  it should "fail when not at least 1 repetition is possible" in withMathematica { _ =>
    a [BelleThrowable] should be thrownBy proveBy("z=4|z=5 ==> x=2".asSequent,
      andL('Llast) & SaturateTactic(andL('Llast)))
  }

  it should "saturate with at least 1 repetition and try right branch in combination with either combinator" in withMathematica { _ =>
    proveBy("x=2&y=3&(z=4|z=5) ==> x=2".asSequent,
      SaturateTactic((andL('Llast) & SaturateTactic(andL('Llast))) | close)) shouldBe 'proved
  }

  "must idiom" should "fail when no change occurs" in withMathematica { _ =>
    a [BelleThrowable] should be thrownBy proveBy("x=2".asFormula, Idioms.must(skip))
  }

  it should "do nothing when change occurred" in withMathematica { _ =>
    val result = proveBy("x=2|x=3".asFormula, Idioms.must(orR(1)))
    result.subgoals.loneElement shouldBe " ==> x=2, x=3".asSequent
  }

  "Label simplification" should "retain necessary leading labels" in withTactics {
    proveByS("==> 0<=x&x<=2, 3<=y&y<=4".asSequent, prop, (labels: Option[List[BelleLabel]]) => labels match {
      case Some(l) => l should contain theSameElementsAs BelleLabel.fromString("0<=x//3<=y::0<=x//y<=4::x<=2//3<=y::x<=2//y<=4")
      case None => fail("Labels expected, but got None")
    })
  }

  it should "FEATURE_REQUEST: drop redundant leading labels" taggedAs TodoTest in withTactics {
    proveByS("x<=0|0<=x&x<=2|2<=x ==>".asSequent, prop, (labels: Option[List[BelleLabel]]) => labels match {
      case Some(l) => l should contain theSameElementsAs BelleLabel.fromString("x<=0::0<=x&x<=2::2<=x")
      case None => fail("Labels expected, but got None")
    })
  }

  "Branch Combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in withMathematica { _ =>
    val tactic = andR(SuccPos(0)) < (
      implyR(SuccPos(0)) & close,
      implyR(SuccPos(0)) & close
    )
    inside (theInterpreter.apply(tactic, BelleProvable.plain(ProvableSig.startProof("(1=1->1=1) & (2=2->2=2)".asFormula)))) {
      case BelleProvable(p, _, _) => p shouldBe 'proved
    }
  }

  it should "prove |- (1=1->1=1) & (2=2->2=2) with new < combinator" in withMathematica { _ =>
    //@note cannot use < in unit tests without fully qualifying the name, because Matchers also knows < operator
    val tactic = andR(SuccPos(0)) & Idioms.<(
      implyR(SuccPos(0)) & close,
      implyR(SuccPos(0)) & close
      )
    inside (theInterpreter.apply(tactic, BelleProvable.plain(ProvableSig.startProof("(1=1->1=1) & (2=2->2=2)".asFormula)))) {
      case BelleProvable(p, _, _) => p shouldBe 'proved
    }
  }

  it should "handle cases were subgoals are added." in withMathematica { _ =>
    val tactic = andR(SuccPos(0)) < (
      andR(SuccPos(0)),
      implyR(SuccPos(0)) & close
    )
    proveBy("(2=2 & 3=3) & (1=1->1=1)".asFormula, tactic).subgoals should contain
      theSameElementsInOrderAs("==> 2=2".asSequent :: "==> 3=3".asSequent :: Nil)
  }

  it should "fail whenever there's a non-partial tactic that doesn't close its goal." in withMathematica { _ =>
    val tactic = andR(SuccPos(0)) < (
      andR(SuccPos(0)) & DebuggingTactics.done,
      implyR(SuccPos(0)) & close & DebuggingTactics.done
      )
    val f = "(2=2 & 3=3) & (1=1->1=1)".asFormula
    a [BelleThrowable] shouldBe thrownBy(
      theInterpreter.apply(tactic, BelleProvable.plain(ProvableSig.startProof(f)))
    )
  }

  it should "handle cases were subgoals are added -- switch order" in withMathematica { _ =>
    val tactic = andR(SuccPos(0)) <(
      implyR(SuccPos(0)) & close,
      andR(SuccPos(0))
      )
    proveBy("(1=1->1=1) & (2=2 & 3=3)".asFormula, tactic).subgoals should contain
      theSameElementsInOrderAs("==> 2=2".asSequent :: "==> 3=3".asSequent :: Nil)
  }

  it should "prove |- (1=1->1=1) & (!2=2  | 2=2) with labels out of order" in withMathematica { _ =>
    val tactic = andR(1) & Idioms.<(label("foo"), label("bar")) & Idioms.<(
      (BelleTopLevelLabel("bar"), orR(1) & notR(1) & close),
      (BelleTopLevelLabel("foo"), implyR(1) & close)
    )
    inside (theInterpreter.apply(tactic, BelleProvable.plain(ProvableSig.startProof("(1=1->1=1) & (!2=2 | 2=2)".asFormula)))) {
      case BelleProvable(p, _, _) => p shouldBe 'proved
    }
  }

  it should "work with loop labels" in withMathematica { _ =>
    val tactic = implyR(1) & loop("x>1".asFormula)(1)
    val v = BelleProvable.plain(ProvableSig.startProof("x>2 -> [{x:=x+1;}*]x>0".asFormula))
    inside (theInterpreter.apply(tactic, v)) {
      case BelleProvable(p, Some(l), _) =>
        p.subgoals should have size 3
        l should contain theSameElementsInOrderAs(BelleLabels.initCase :: BelleLabels.useCase :: BelleLabels.indStep :: Nil)
    }
  }

  it should "not screw up empty labels" in withMathematica { _ =>
    proveBy(
      "((P_() <-> F_()) & (F_() -> (Q_() <-> G_()))) ->(P_() & Q_() <-> F_() & G_())".asFormula, prop) shouldBe 'proved
  }

  it should "finish working branches before failing" in withMathematica { _ =>
    BelleInterpreter.setInterpreter(registerInterpreter(ExhaustiveSequentialInterpreter()))

    var finishedBranches = Seq.empty[Int]
    def logDone(branch: Int) = anon ((provable: ProvableSig) => {
      finishedBranches = finishedBranches :+ branch
      provable
    })

    a [BelleThrowable] should be thrownBy proveBy("x>0 -> x>5 & x>0 & [?x>1;]x>1".asFormula, implyR(1) & andR(1) <(
      DebuggingTactics.printIndexed("Branch 1") & id & /* not reached */ logDone(1),
      andR(1) <(
        DebuggingTactics.printIndexed("Branch 2") & id & logDone(2)
        ,
        DebuggingTactics.printIndexed("Branch 3") & testb(1) & prop & logDone(3)
      )
    ))

    finishedBranches should contain theSameElementsAs Seq(2, 3)
  }

  it should "finish working branches before failing with combined error message" in withMathematica { _ =>
    BelleInterpreter.setInterpreter(registerInterpreter(ExhaustiveSequentialInterpreter()))

    var finishedBranches = Seq.empty[Int]
    def logDone(branch: Int) = anon ((provable: ProvableSig) => {
      finishedBranches = finishedBranches :+ branch
      provable
    })

    the [BelleThrowable] thrownBy proveBy("x>0 -> x>5 & x>2 & [?x>1;]x>1".asFormula, implyR(1) & andR(1) <(
      DebuggingTactics.printIndexed("Branch 1") & id & /* not reached */ logDone(1),
      andR(1) <(
        DebuggingTactics.printIndexed("Branch 2") & id & /* not reached */ logDone(2)
        ,
        DebuggingTactics.printIndexed("Branch 3") & testb(1) & prop & logDone(3)
      )
    )) should have message
      """Left: Expects same formula in antecedent and succedent. Found:
        |   -1:  x>0	Greater
        |==> 1:  x>5	Greater
        |Right: Expects same formula in antecedent and succedent. Found:
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
        BelleLabels.indStep.append("[x:=x+1;]x>=0".asLabel).append("1".asLabel) ::
        BelleLabels.indStep.append("[x:=x+2;]x>=0".asLabel) :: Nil)
    })
  }

  "Case combinator" should "match tactics with labels" in withMathematica { _ =>
    val ts = List(
      BelleLabels.initCase -> nil,
      BelleLabels.useCase -> id,
      BelleLabels.indStep -> assignb(1)
    ).permutations.map(t => implyR(1) & loop("x>1".asFormula)(1) & CaseTactic(t))
    val v = BelleProvable.plain(ProvableSig.startProof("x>2 -> [{x:=x+1;}*]x>1".asFormula))
    for (t <- ts) {
      inside(theInterpreter.apply(t, v)) {
        case BelleProvable(p, _, _) =>
          p.subgoals should contain theSameElementsAs List(
            "x>2 ==> x>1".asSequent,
            "x>1 ==> x+1>1".asSequent)
      }
    }
  }

  it should "match tactics with label suffixes" in withMathematica { _ =>
    val ts = List(
      BelleLabels.initCase -> nil,
      BelleLabels.useCase -> id,
      BelleLabels.indStep -> assignb(1)
    ).permutations.map(t => implyR(1) & andR(1) /* creates labels that become parents of loop labels */ <(
      loop("x>1".asFormula)(1) & CaseTactic(t), id))
    val v = BelleProvable.plain(ProvableSig.startProof("x>2 -> [{x:=x+1;}*]x>1 & x>2".asFormula))
    for (t <- ts) {
      inside(theInterpreter.apply(t, v)) {
        case BelleProvable(p, _, _) =>
          p.subgoals should contain theSameElementsAs List(
            "x>2 ==> x>1".asSequent,
            "x>1 ==> x+1>1".asSequent)
      }
    }
  }

  it should "match tactics with label suffixes (2)" in withMathematica { _ =>
    val ts = List(
      "[x:=1;][{x:=x+1;}*]x>=1".asLabel.append(BelleLabels.initCase) -> nil,
      "[x:=1;][{x:=x+1;}*]x>=1".asLabel.append(BelleLabels.useCase) -> id,
      "[x:=1;][{x:=x+1;}*]x>=1".asLabel.append(BelleLabels.indStep) -> assignb(1),
      "[x:=x-1;][{x:=x+1;}*]x>=1".asLabel.append(BelleLabels.initCase) -> QE,
      "[x:=x-1;][{x:=x+1;}*]x>=1".asLabel.append(BelleLabels.useCase) -> label("A manual label"),
      "[x:=x-1;][{x:=x+1;}*]x>=1".asLabel.append(BelleLabels.indStep) -> assignb(1)
    ).permutations.map(t => prop & unfoldProgramNormalize /* create labels that become parents of loop labels */ &
      onAll(loop("x>=1".asFormula)(1)) & CaseTactic(t))
    val v = BelleProvable.plain(ProvableSig.startProof("x>2 -> [x:=1;++x:=x-1;][{x:=x+1;}*]x>=1 & x>2".asFormula))
    for (t <- ts) {
      inside(theInterpreter.apply(t, v)) {
        case BelleProvable(p, labels, _) =>
          p.subgoals should contain theSameElementsAs List(
            "x_0>2, x=1 ==> x>=1".asSequent,
            "x>=1, x_0>2 ==> x>=1".asSequent,
            "x>=1, x_0>2 ==> x+1>=1".asSequent,
            "x>=1, x_0>2 ==> x+1>=1".asSequent
          )
          labels.value should contain theSameElementsAs List(
            "[x:=1;++x:=x-1;][{x:=x+1;}*]x>=1//[x:=1;][{x:=x+1;}*]x>=1//Init".asLabel,
            "[x:=1;++x:=x-1;][{x:=x+1;}*]x>=1//[x:=x-1;][{x:=x+1;}*]x>=1//Post//A manual label".asLabel,
            "[x:=1;++x:=x-1;][{x:=x+1;}*]x>=1//[x:=x-1;][{x:=x+1;}*]x>=1//Step".asLabel,
            "[x:=1;++x:=x-1;][{x:=x+1;}*]x>=1//[x:=1;][{x:=x+1;}*]x>=1//Step".asLabel)
      }
    }
  }

  "Let" should "fail (but not horribly) when inner proof cannot be started" in withMathematica { _ =>
    val fml = "[{f'=g}][{g'=5}]f>=0".asFormula
    the [IllFormedTacticApplicationException] thrownBy proveBy(fml, BelleParser("let ({`f()=f`}) in (nil)")) should have message
      "Unable to start inner proof in let: edu.cmu.cs.ls.keymaerax.core.FuncOf cannot be cast to edu.cmu.cs.ls.keymaerax.core.Variable"
  }

  "Unification" should "work on 1=1->1=1" in withMathematica { _ =>
    val pattern = SequentType("==> p() -> p()".asSequent)
    val e = USubstPatternTactic(Seq((pattern, (x:RenUSubst) => implyR(SuccPos(0)) & close)))
    proveBy("1=1->1=1".asFormula, e) shouldBe 'proved
  }

  it should "work when there are non-working patterns" in withMathematica { _ =>
    val pattern1 = SequentType("==> p() -> p()".asSequent)
    val pattern2 = SequentType("==> p() & q()".asSequent)
    val e = USubstPatternTactic(Seq(
      (pattern2, (_: RenUSubst) => error("Should never get here.")),
      (pattern1, (_: RenUSubst) => implyR(SuccPos(0)) & close)
    ))
    proveBy("1=1->1=1".asFormula, e) shouldBe 'proved
  }

  it should "work when there are non-working patterns -- flipped order." in withMathematica { _ =>
    val pattern1 = SequentType("==> p() -> p()".asSequent)
    val pattern2 = SequentType("==> p() & q()".asSequent)
    val e = USubstPatternTactic(Seq(
      (pattern1, (_: RenUSubst) => implyR(1) & close),
      (pattern2, (_: RenUSubst) => error("Should never get here."))
    ))
    proveBy("1=1->1=1".asFormula, e) shouldBe 'proved
  }

  it should "choose the first applicable unification when there are many options" in withMathematica { _ =>
    val pattern1 = SequentType("==> p() -> p()".asSequent)
    val pattern2 = SequentType("==> p() -> q()".asSequent)
    val e = USubstPatternTactic(Seq(
      (pattern1, (_: RenUSubst) => implyR(1) & close),
      (pattern2, (_: RenUSubst) => error("Should never get here."))
    ))
    proveBy("1=1->1=1".asFormula, e) shouldBe 'proved
  }

  it should "choose the first applicable unification when there are many options -- flipped order" in withMathematica { _ =>
    val pattern1 = SequentType("==> p() -> p()".asSequent)
    val pattern2 = SequentType("==> p() -> q()".asSequent)
    val e = USubstPatternTactic(Seq(
      (pattern2, (_: RenUSubst) => error("Should never get here.")),
      (pattern1, (_: RenUSubst) => implyR(1) & close)
    ))
    a [BelleThrowable] shouldBe thrownBy (proveBy("1=1->1=1".asFormula, e))
  }

  //@todo would need DerivationInfo entry
  //@note: DifferentialTests."ODE" should "prove FM tutorial 4" acts as a smoke test for this
  "ChooseSome" should "record in the database" ignore withDatabase { db => withMathematica { _ =>
    val fml = "x>0 -> [{x:=3;}*]x>0".asFormula
    val modelContent = s"Variables. R x. End.\n Problem. ${fml.prettyString} End."
    db.createProof(modelContent, "chooseSomeTest")

    import TacticFactory._

    val tactic = anon ((pos: Position, seq: Sequent) => { ChooseSome(
        () => ("x>0".asFormula::Nil).iterator,
        (inv: Formula) => loop(inv)(pos)
      ) & Idioms.<(close, close, master())
    })

    db.proveBy(modelContent, tactic(1)) shouldBe 'proved
  }}
  
  "Def tactic" should "define a tactic and apply it later" in withMathematica { _ =>
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
  it should "print nice errors and provide a stack trace" ignore withMathematica { _ =>
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
        & Idioms.nil, BelleProvable.plain(ProvableSig.startProof("1=1 & 2=2".asFormula)))
    }
    thrown.printStackTrace()
    thrown.getMessage should include ("Fails...")
    val s = thrown.getCause.getStackTrace
    //@todo works in isolation, but when run with other tests, we pick up stack trace elements of those too
    s.filter(_.getFileName == "SequentialInterpreterTests.scala").slice(0, 11).map(_.getLineNumber) shouldBe Array(280, 279, 278, 271, 271, 269, 266, 266, 263, 262, 276)
  }

  "Lazy interpreter" should "fail on the first failing branch" in withMathematica { _ =>
    val listener = new IOListener {
      val calls: mutable.Buffer[BelleExpr] = mutable.Buffer[BelleExpr]()
      override def begin(input: BelleValue, expr: BelleExpr): Unit = calls += expr
      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
      override def kill(): Unit = {}
    }
    the [BelleThrowable] thrownBy LazySequentialInterpreter(listener::Nil)(
      "andR(1); <(close, close)".asTactic,
      BelleProvable.plain(ProvableSig.startProof("false & true".asFormula))) should have message
        """Inapplicable close
          |Provable{
          |==> 1:  false	False$
          |  from
          |==> 1:  false	False$}""".stripMargin

    listener.calls should have size 10
    val andT@SeqTactic(andRRule, labelT@BranchTactic(labels)) = andR(1).
      computeExpr(BelleProvable.plain(ProvableSig.startProof("==> false & true".asSequent)))

    listener.calls should contain theSameElementsInOrderAs(
      "andR(1); <(close, close)".asTactic :: "andR(1)".asTactic ::
      andT :: andRRule :: labelT :: labels(0) :: labels(1) ::
      BranchTactic("close".asTactic :: "close".asTactic :: Nil) :: "close".asTactic ::
      DebuggingTactics.error("Inapplicable close") :: Nil)
  }

  "Exhaustive interpreter" should "explore all branches regardless of failing ones" in withMathematica { _ =>
    val listener = new IOListener {
      val calls: mutable.Buffer[BelleExpr] = mutable.Buffer[BelleExpr]()
      override def begin(input: BelleValue, expr: BelleExpr): Unit = calls += expr
      override def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue, Throwable]): Unit = {}
      override def kill(): Unit = {}
    }
    the [BelleThrowable] thrownBy ExhaustiveSequentialInterpreter(listener::Nil)(
      "andR(1); <(close, close)".asTactic,
      BelleProvable.plain(ProvableSig.startProof("false & true".asFormula))) should have message
        """Inapplicable close
          |Provable{
          |==> 1:  false	False$
          |  from
          |==> 1:  false	False$}""".stripMargin

    val andT@SeqTactic(andRRule, labelT@BranchTactic(labels)) = andR(1).
      computeExpr(BelleProvable.plain(ProvableSig.startProof("==> false & true".asSequent)))

    listener.calls should have size 12
    listener.calls should contain theSameElementsInOrderAs(
      "andR(1); <(close, close)".asTactic :: "andR(1)".asTactic ::
      andT :: andRRule :: labelT :: labels(0) :: labels(1) ::
      BranchTactic("close".asTactic :: "close".asTactic :: Nil) :: "close".asTactic ::
      DebuggingTactics.error("Inapplicable close") :: "close".asTactic :: ProofRuleTactics.closeTrue(1) :: Nil)
  }

  it should "confirm that interpreter debug information slows down search" taggedAs SlowTest in withMathematica { _ =>
    val ante = (1 to 100).map(i => Equal(Variable("x", Some(i)), Number(1))).reduce(And)
    val succ = (1 to 50).map(i => Box(Assign(Variable("y", Some(i)), Number(2)), Greater(Variable("y", Some(i)), Number(1)))).reduce(Or)

    // should take about 1min
    failAfter(2 minutes) {
      val BelleProvable(result, _, _) = ExhaustiveSequentialInterpreter(Nil, throwWithDebugInfo = true)(
        SaturateTactic(implyR('R) | andL('L) | orR('R) | assignb('R)),
        BelleProvable.plain(ProvableSig.startProof(Imply(ante, succ)))
      )
      result.subgoals.head.ante should have size 100
      result.subgoals.head.succ should have size 50
      result.subgoals.head.succ.foreach(_ shouldBe a [Greater])
    }
  }

  it should "not spend extensive time searching positions without debug information" in withMathematica { _ =>
    val ante = (1 to 100).map(i => Equal(Variable("x", Some(i)), Number(1))).reduce(And)
    val succ = (1 to 50).map(i => Box(Assign(Variable("y", Some(i)), Number(2)), Greater(Variable("y", Some(i)), Number(1)))).reduce(Or)

    // should take about 500ms
    failAfter(2 seconds) {
      val BelleProvable(result, _, _) = ExhaustiveSequentialInterpreter(Nil)(
        SaturateTactic(implyR('R) | andL('L) | orR('R) | assignb('R)),
        BelleProvable.plain(ProvableSig.startProof(Imply(ante, succ)))
      )
      result.subgoals.head.ante should have size 100
      result.subgoals.head.succ should have size 50
      result.subgoals.head.succ.foreach(_ shouldBe a [Greater])
    }
  }

  it should "stop saturation when proof is closed" in withMathematica { _ =>
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
      BelleProvable.plain(ProvableSig.startProof("x>0 -> x>0".asFormula))
    ) match {
      case BelleProvable(pr, _, _) => pr shouldBe 'proved
    }
    listener.calls should have size 1
  }

  "Tactics with delayed substitution" should "replay expandAll" in withMathematica { _ =>
    val entry = ArchiveParser.parser(
      """ArchiveEntry "Delayed Substitution"
        |Definitions Bool p(Real x) <-> x>0; Bool q(Real y) <-> y>0; End.
        |ProgramVariables Real x; Real y; End.
        |Problem p(x) -> [y:=x;]q(y) End.
        |End.""".stripMargin).head

    proveBy(entry.model.asInstanceOf[Formula],
      ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "==> x>0 -> [y:=x;]y>0".asSequent, "Unexpected expand result") &
        implyR(1) & assignb(1) & id) shouldBe 'proved

    proveBy(entry.model.asInstanceOf[Formula],
      implyR(1) & assignb(1) &
        DebuggingTactics.assert(_ == "p(x) ==> q(x)".asSequent, "Unexpected result prior to expand") &
        ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "x>0 ==> x>0".asSequent, "Unexpected expand result") &
        id) shouldBe 'proved
  }

  it should "replay when expanded on branches" in withMathematica { _ =>
    val entry = ArchiveParser.parser(
      """ArchiveEntry "Delayed Substitution"
        |Definitions Bool p(Real x) <-> x>0; Bool q(Real y) <-> y>0; End.
        |ProgramVariables Real x; Real y; End.
        |Problem p(x) -> [y:=x; ++ ?q(y);]q(y) End.
        |End.""".stripMargin).head

    proveBy(entry.model.asInstanceOf[Formula],
      ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "==> x>0 -> [y:=x; ++ ?y>0;]y>0".asSequent, "Unexpected expand result") &
        implyR(1) & choiceb(1) & andR(1) <(assignb(1) & id, testb(1) & implyR(1) & id)) shouldBe 'proved

    proveBy(entry.model.asInstanceOf[Formula],
      implyR(1) & choiceb(1) & andR(1) <(
        assignb(1) &
        DebuggingTactics.assert(_ == "p(x) ==> q(x)".asSequent, "Unexpected result prior to expand") &
        ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "x>0 ==> x>0".asSequent, "Unexpected expand result") &
        id
        ,
        testb(1) & implyR(1) &
        DebuggingTactics.assert(_ == "p(x),q(y) ==> q(y)".asSequent, "Unexpected result prior to expand") &
        ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "x>0,y>0 ==> y>0".asSequent, "Unexpected expand result") &
        id)
        ) shouldBe 'proved
  }

  it should "replay when expanded only on some branches" in withMathematica { _ =>
    val entry = ArchiveParser.parser(
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
          id
        ,
        testb(1) & implyR(1) & id)
    ) shouldBe 'proved

    // branches in reverse order
    proveBy(entry.model.asInstanceOf[Formula],
      implyR(1) & choiceb(1) & useAt(Ax.andCommute)(1) & andR(1) <(
        testb(1) & implyR(1) & id
        ,
        assignb(1) &
        DebuggingTactics.assert(_ == "p(x) ==> q(x)".asSequent, "Unexpected result prior to expand") &
        ExpandAll(entry.defs.substs) &
        DebuggingTactics.assert(_ == "x>0 ==> x>0".asSequent, "Unexpected expand result") &
        id)
    ) shouldBe 'proved
  }

  it should "support introducing variables for function symbols of closed provables" in withMathematica { _ =>
    val entry = ArchiveParser.parser(
      """ArchiveEntry "Delayed Substitution from dIRule"
        |ProgramVariables Real x, y, r; End.
        |Problem x^2+y^2=r -> [{x'=r*y,y'=-r*x}]x^2+y^2=r End.
        |End.""".stripMargin).head

    proveBy(entry.model.asInstanceOf[Formula],
      implyR(1) & cut("r>0".asFormula) <(
        dC("x^2+y^2=r".asFormula)(1) <(
          cut("r>1".asFormula)
          ,
          dIRule(1) <(QE, unfoldProgramNormalize & QE)
        ),
        ODE(1)
      )
    ).subgoals should contain theSameElementsInOrderAs List(
      "x^2+y^2=r, r>0, r>1 ==> [{x'=r*y,y'=-r*x&true&x^2+y^2=r}]x^2+y^2=r".asSequent,
      "x^2+y^2=r, r>0 ==> [{x'=r*y,y'=-r*x&true&x^2+y^2=r}]x^2+y^2=r, r>1".asSequent
    )

    proveBy(entry.model.asInstanceOf[Formula], let("r()".asTerm, "r".asTerm, by(
      proveBy("x^2+y^2=r() -> [{x'=r()*y,y'=-r()*x}]x^2+y^2=r()".asFormula, implyR(1) & ODE(1))))) shouldBe 'proved
  }

  it should "detect expanded definitions when stitching together provables" in withMathematica { _ =>
    val defs = "g(x) ~> -x^2".asDeclaration
    proveByS("p(x) ==> [{x'=g(y)}]p(x)".asSequent,
      dC("x<=old(x)".asFormula)(1) <(
        skip,
        dIClose(1)
      ),
      defs
    ).subgoals.loneElement shouldBe "p(x_0), x_0=x ==> [{x'=-y^2 & true&x<=x_0}]p(x)".asSequent

    proveByS("p(x) ==> [{x'=g(y)}]p(x)".asSequent, diffInvariant("x<=old(x)".asFormula)(1), defs).subgoals.
      loneElement shouldBe "p(x_0), x_0=x ==> [{x'=-y^2 & true&x<=x_0}]p(x)".asSequent
  }

  "Using" should "keep mentioned and abbreviate unmentioned formulas" in withMathematica { _ =>
    def check(expected: Sequent) = anon ((seq: Sequent) => {
      seq shouldBe expected
      skip
    })

    proveBy("x>y, y>=0, x>0 ==> y>=0, x>=0".asSequent, Using("x>0".asFormula:: "x>=0".asFormula :: Nil,
      check("p__0(x,y), p__1(y), x>0 ==> q__0(y), x>=0".asSequent)) // restricted inside
    ).subgoals.loneElement shouldBe "x>y, y>=0, x>0 ==> y>=0, x>=0".asSequent // back to full outside
  }

  it should "abbreviate only temporarily" in withMathematica { _ =>
    proveBy("x>0 | x>y, y=0 | y>0 ==> x>0".asSequent,
      Using("x>0 | x>y".asFormula :: Nil, SaturateTactic(orL('L)))).subgoals shouldBe List(
      "x>0, y=0 | y>0 ==> x>0".asSequent, "x>y, y=0 | y>0 ==> x>0".asSequent)
  }

  it should "work nested" in withMathematica { _ =>
    proveBy("x>0 | x>y, y=0 | y>0 ==> x>0".asSequent,
      Using("x>0 | x>y".asFormula :: Nil, SaturateTactic(orL('L))) <(
        Using("x>0".asFormula :: "x>0".asFormula :: Nil, id),
        skip
      )).subgoals.loneElement shouldBe "x>y, y=0 | y>0 ==> x>0".asSequent
  }

  it should "work with QE" in withQE { _ =>
    proveBy("x>0, y=0 | y>0 ==> x^2>0".asSequent, Using("x>0".asFormula :: "x^2>0".asFormula :: Nil, QE)) shouldBe 'proved
  }

  it should "work with loops" in withTactics {
    proveBy("x>0, y=0 | y>0, z=0 | z=1 ==> [{x:=x+z;}*]x>0".asSequent, Using("z=0 | z=1".asFormula :: Nil, SaturateTactic(orL('L)))).
      subgoals shouldBe List(
        "x>0, y=0 | y>0, z=0 ==> [{x:=x+z;}*]x>0".asSequent,
        "x>0, y=0 | y>0, z=1 ==> [{x:=x+z;}*]x>0".asSequent
    )
  }

  it should "work with ODEs" in withTactics {
    proveBy("x>0, y=0 | y>0, z=0 | z=1 ==> [{x'=z*x}]x>0".asSequent, Using("z=0 | z=1".asFormula :: Nil, SaturateTactic(orL('L)))).
      subgoals shouldBe List(
      "x>0, y=0 | y>0, z=0 ==> [{x'=z*x}]x>0".asSequent,
      "x>0, y=0 | y>0, z=1 ==> [{x'=z*x}]x>0".asSequent
    )
  }

  it should "keep track of original values" in withTactics {
    proveBy("x=2, c()=3 ==> [x:=c();]x=2".asSequent,
      Using("c()=3".asFormula :: "[x:=c();]x=2".asFormula :: Nil, DLBySubst.assignEquality(1))).
      subgoals.loneElement shouldBe "x_0=2, c()=3, x=c() ==> x=2".asSequent
    proveBy("x=2, [{x'=x}]x>=0, c()=3 ==> [x:=c();]x=2".asSequent,
      Using("c()=3".asFormula :: "[x:=c();]x=2".asFormula :: Nil, DLBySubst.assignEquality(1))).
      subgoals.loneElement shouldBe "x_0=2, c()=3, x_1=c(), x=x_0, [{x'=x}]x>=0 ==> x_1=2".asSequent
    proveBy("x=1 | x=2, c()=3 | c()=4 ==> [x:=c();]x<=2, [{x'=x}]x>=0".asSequent,
      Using("c()=3 | c()=4".asFormula :: "[x:=c();]x<=2".asFormula :: Nil,
        TactixLibrary.prop <(DLBySubst.assignEquality(1), skip))).
      subgoals should contain theSameElementsInOrderAs List(
        "x_0=1 | x_0=2, c()=3, x_1=c(), x=x_0 ==> x_1<=2, [{x'=x}]x>=0".asSequent,
        "x=1 | x=2, c()=4 ==> [x:=c();]x<=2, [{x'=x}]x>=0".asSequent
      )
  }

  it should "be allowed but optional to mention formulas of position tactics" in withQE { _ =>
    proveBy("x=2, c()=3 ==> [x:=c();]x=2".asSequent,
      Using("c()=3".asFormula :: "[x:=c();]x=2".asFormula :: Nil, DLBySubst.assignEquality(1))).
      subgoals.loneElement shouldBe "x_0=2, c()=3, x=c() ==> x=2".asSequent
    proveBy("x=2, c()=3 ==> [x:=c();]x=2".asSequent,
      Using("c()=3".asFormula :: Nil, DLBySubst.assignEquality(1))).
      subgoals.loneElement shouldBe "x_0=2, c()=3, x=c() ==> x=2".asSequent
    proveBy("x=2, c()=3 ==> [{x'=c()}]x>=2".asSequent,
      Using("c()=3".asFormula :: Nil, diffInvariant("x>=old(x)".asFormula)(1))).
      subgoals.loneElement shouldBe "x_0=2, c()=3, x_0=x ==> [{x'=c() & true & x>=x_0}]x>=2".asSequent
  }

  it should "be allowed but optional to mention formulas of searchy position locators" in withTactics {
    proveBy("x=2, c()=3 ==> [x:=4;]x=4, [x:=c();]x=2".asSequent,
      Using("c()=3".asFormula :: "[x:=c();]x=2".asFormula :: Nil, DLBySubst.assignEquality('R, "[x:=c();]x=2".asFormula))).
      subgoals.loneElement shouldBe "x_0=2, c()=3, x=c() ==> [x:=4;]x=4, x=2".asSequent
    proveBy("x=2, c()=3 ==> [x:=4;]x=4, [x:=c();]x=2".asSequent,
      Using("c()=3".asFormula :: "[x:=c();]x=2".asFormula :: Nil, DLBySubst.assignEquality('Rlike, "[x:=c();]x=c()".asFormula))).
      //@todo undesired renaming
      subgoals.loneElement shouldBe "x_0=2, c()=3, x=4 ==> [x_0:=c();]x_0=2, x=4".asSequent
  }

  it should "be allowed but optional to mention formulas of two-position tactics" in withTactics {
    proveBy("x=2, c()=3 ==> [x:=4;]x=4, [x:=c();]x=2".asSequent,
      Using(Nil, SequentCalculus.exchangeL(-1, -2))).
      subgoals.loneElement shouldBe "c()=3, x=2 ==> [x:=4;]x=4, [x:=c();]x=2".asSequent
    proveBy("x=2, c()=3 ==> [x:=4;]x=4, [x:=c();]x=2".asSequent,
      Using(Nil, SequentCalculus.exchangeR(1, 2))).
      subgoals.loneElement shouldBe "x=2, c()=3 ==> [x:=c();]x=2, [x:=4;]x=4".asSequent
  }

  it should "retain labels" in withTactics {
    proveByS("y<=0 -> x=2, 0<=y&y<=1 -> x=3, 1<=y -> x=4, y<=0 | 0<=y&y<=1 | 1<=y ==> 2<=x & x<=4".asSequent,
      Using(List("y<=0 | 0<=y&y<=1 | 1<=y".asFormula), prop), (labels: Option[List[BelleLabel]]) => labels match {
        case Some(l) => l should contain theSameElementsAs
          //@todo simplify labels
          BelleLabel.fromString("y<=0") ++ BelleLabel.fromString("0<=y&y<=1|1<=y//0<=y&y<=1") ++ BelleLabel.fromString("0<=y&y<=1|1<=y//1<=y")
        case None => fail("Expected labels, but got None")
      }).subgoals should contain theSameElementsAs List(
      "y<=0 -> x=2, 0<=y&y<=1 -> x=3, 1<=y -> x=4, y<=0 ==> 2<=x & x<=4".asSequent,
      "y<=0 -> x=2, 0<=y&y<=1 -> x=3, 1<=y -> x=4, 0<=y, y<=1 ==> 2<=x & x<=4".asSequent,
      "y<=0 -> x=2, 0<=y&y<=1 -> x=3, 1<=y -> x=4, 1<=y ==> 2<=x & x<=4".asSequent
    )
  }

  it should "create useful labels" in withTactics {
    val s = """init(rv)&(w=wUp()|w=wLo()), C(w,dhf,dhd,r,rv,h)
              |  ==>  (w*dhf>=0->(case1(w,dhd,r,rv)->bounds1(w,dhd,r,rv,h))&(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h)))&(w*dhf < 0->(case5(w,dhf,dhd,r,rv)->bounds5(w,dhd,r,rv,h))&(case6(w,dhf,dhd,r,rv)->bounds6(w,dhf,dhd,r,rv,h)))
              |""".stripMargin.asSequent
    val t = "prop using \"(w*dhf>=0->(case1(w,dhd,r,rv)->bounds1(w,dhd,r,rv,h))&(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h)))&(w*dhf < 0->(case5(w,dhf,dhd,r,rv)->bounds5(w,dhd,r,rv,h))&(case6(w,dhf,dhd,r,rv)->bounds6(w,dhf,dhd,r,rv,h)))\"".asTactic
    proveByS(s, t, (labels: Option[List[BelleLabel]]) => labels match {
      case Some(l) =>
        println(BelleLabel.toPrettyString(l))
        l should contain theSameElementsAs
          BelleLabel.fromString("w*dhf>=0->(case1(w,dhd,r,rv)->bounds1(w,dhd,r,rv,h))&(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//case1(w,dhd,r,rv)->bounds1(w,dhd,r,rv,h)") ++
          BelleLabel.fromString("w*dhf>=0->(case1(w,dhd,r,rv)->bounds1(w,dhd,r,rv,h))&(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//case2(w,dhd,r,rv)->bounds2(w,dhd,h)") ++
          BelleLabel.fromString("w*dhf>=0->(case1(w,dhd,r,rv)->bounds1(w,dhd,r,rv,h))&(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h)") ++
          BelleLabel.fromString("w*dhf>=0->(case1(w,dhd,r,rv)->bounds1(w,dhd,r,rv,h))&(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//(case2(w,dhd,r,rv)->bounds2(w,dhd,h))&(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//(case3(w,dhf,dhd,r,rv)->bounds3(w,dhd,r,rv,h))&(case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h))//case4(w,dhf,dhd,r,rv)->bounds4(w,dhf,dhd,r,rv,h)") ++
          BelleLabel.fromString("w*dhf < 0->(case5(w,dhf,dhd,r,rv)->bounds5(w,dhd,r,rv,h))&(case6(w,dhf,dhd,r,rv)->bounds6(w,dhf,dhd,r,rv,h))//case5(w,dhf,dhd,r,rv)->bounds5(w,dhd,r,rv,h)") ++
          BelleLabel.fromString("w*dhf < 0->(case5(w,dhf,dhd,r,rv)->bounds5(w,dhd,r,rv,h))&(case6(w,dhf,dhd,r,rv)->bounds6(w,dhf,dhd,r,rv,h))//case6(w,dhf,dhd,r,rv)->bounds6(w,dhf,dhd,r,rv,h)")
      case None => fail("Expected labels, but got None")
    })
  }
}
