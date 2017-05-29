/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon


import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}

import scala.collection.immutable._

import org.scalatest.Inside._


/**
  * Tests tactic diff.
  * @author Stefan Mitsch
  */
@SummaryTest
@UsualTest
class TacticDiffTest extends TacticTestBase {

  "Tactic diff" should "match same builtin tactics" in {
    val t = BelleParser("hideR(1)")
    TacticDiff.diff(t, t) shouldBe (ReplacementBelleContext(t), Map(), Map())
  }

  it should "find difference in builtin tactics" in {
    val t1 = BelleParser("hideR(1)")
    val t2 = BelleParser("hideL(-1)")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t shouldBe a[BelleDot]
    diff._2 should contain theSameElementsAs List((diff._1.t, t1))
    diff._3 should contain theSameElementsAs List((diff._1.t, t2))
  }

  it should "find difference with nil" in {
    val t1 = BelleParser("nil")
    val t2 = BelleParser("hideR(1)")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t shouldBe a[BelleDot]
    diff._2 should contain theSameElementsAs List((diff._1.t, t1))
    diff._3 should contain theSameElementsAs List((diff._1.t, t2))
  }

  it should "match same sequential tactics" in {
    val t = BelleParser("notL(-1) & hideR(1)")
    TacticDiff.diff(t, t) shouldBe (ReplacementBelleContext(t), Map(), Map())
  }

  it should "find difference in sequential tactics" in {
    val t1 = BelleParser("notL(-1) & hideR(1)")
    val t2 = BelleParser("hideL(-1)")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t shouldBe a[BelleDot]
    diff._2 should contain theSameElementsAs List((diff._1.t, t1))
    diff._3 should contain theSameElementsAs List((diff._1.t, t2))
  }

  it should "find difference in left child of sequential tactics" in {
    val t1 = BelleParser("notL(-1) & hideR(1)")
    val t2 = BelleParser("notR(1)  & hideR(1)")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t match {
      case SeqTactic(c1: BelleDot, c2) =>
        c2 shouldBe BelleParser("hideR(1)")
        diff._2 should contain theSameElementsAs List((c1, BelleParser("notL(-1)")))
        diff._3 should contain theSameElementsAs List((c1, BelleParser("notR(1)")))
    }
  }

  it should "find difference in right child of sequential tactics" in {
    val t1 = BelleParser("notL(-1) & hideR(1)")
    val t2 = BelleParser("notL(-1) & hideR(2)")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t match {
      case SeqTactic(c1, c2: BelleDot) =>
        c1 shouldBe BelleParser("notL(-1)")
        diff._2 should contain theSameElementsAs List((c2, BelleParser("hideR(1)")))
        diff._3 should contain theSameElementsAs List((c2, BelleParser("hideR(2)")))
    }
  }

  it should "find difference with sequential nil" in {
    val t1 = BelleParser("hideR(1) & nil")
    val t2 = BelleParser("hideR(1) & hideL(-1)")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t match {
      case SeqTactic(c1, c2: BelleDot) =>
        c1 shouldBe BelleParser("hideR(1)")
        diff._2 should contain theSameElementsAs List((c2, BelleParser("nil")))
        diff._3 should contain theSameElementsAs List((c2, BelleParser("hideL(-1)")))
    }
  }

  it should "match same branching tactics" in {
    val t = BelleParser("notL(-1) & <(hideR(1), hideR(2), hideR(3))")
    TacticDiff.diff(t, t) shouldBe (ReplacementBelleContext(t), Map(), Map())
  }

  it should "find difference in first child of branching tactics" in {
    val t1 = BelleParser("notL(-1) & <(hideR(1), hideR(2), hideR(3))")
    val t2 = BelleParser("notL(-1) & <(hideL(-1), hideR(2), hideR(3))")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t match {
      case SeqTactic(_, BranchTactic((ch: BelleDot) :: ct)) =>
        ct shouldBe Seq(BelleParser("hideR(2)"), BelleParser("hideR(3)"))
        diff._2 should contain theSameElementsAs List((ch, BelleParser("hideR(1)")))
        diff._3 should contain theSameElementsAs List((ch, BelleParser("hideL(-1)")))
    }
  }

  it should "find difference in all children of branching tactics" in {
    val t1 = BelleParser("notL(-1) & <(hideR(1), hideR(2), hideR(3))")
    val t2 = BelleParser("notL(-1) & <(hideL(-1), hideL(-2), hideL(-3))")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t match {
      case SeqTactic(_, BranchTactic((c1: BelleDot) :: (c2: BelleDot) :: (c3: BelleDot) :: Nil)) =>
        diff._2 should contain theSameElementsAs List((c1, BelleParser("hideR(1)")), (c2, BelleParser("hideR(2)")), (c3, BelleParser("hideR(3)")))
        diff._3 should contain theSameElementsAs List((c1, BelleParser("hideL(-1)")), (c2, BelleParser("hideL(-2)")), (c3, BelleParser("hideL(-3)")))
    }
  }

  it should "match same input tactics" in {
    val t = BelleParser("cut({`x>0`})")
    TacticDiff.diff(t, t) shouldBe (ReplacementBelleContext(t), Map(), Map())
  }

  it should "find difference of input tactics" in {
    val t1 = BelleParser("cut({`x>0`})")
    val t2 = BelleParser("cut({`y<0`})")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t shouldBe a[BelleDot]
    diff._2 should contain theSameElementsAs List((diff._1.t, t1))
    diff._3 should contain theSameElementsAs List((diff._1.t, t2))
  }

  it should "find difference of input position tactics" in {
    val t1 = BelleParser("andL(-1) & nil")
    val t2 = BelleParser("andL(-1) & loop({`x>0`},1)")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t match {
      case SeqTactic(c1, c2: BelleDot) =>
        diff._2 should contain theSameElementsAs List((c2, BelleParser("nil")))
        diff._3 should contain theSameElementsAs List((c2, BelleParser("loop({`x>0`},1)")))
    }
  }

  it should "find multiple differences" in {
    val t1 = BelleParser("notL(-1) & <(nil, hideR(2), hideR(3))")
    val t2 = BelleParser("notR(1) & <(hideL(-1), hideR(2), andR(1) & <(hideR(3), hideR(4)))")
    val diff = TacticDiff.diff(t1, t2)
    diff._1.t match {
      case SeqTactic(c0: BelleDot, BranchTactic((c1: BelleDot) :: c2 :: (c3: BelleDot) :: Nil)) =>
        c2 shouldBe BelleParser("hideR(2)")
        diff._2 should contain theSameElementsAs List((c0, BelleParser("notL(-1)")), (c1, BelleParser("nil")), (c3, BelleParser("hideR(3)")))
        diff._3 should contain theSameElementsAs List((c0, BelleParser("notR(1)")), (c1, BelleParser("hideL(-1)")), (c3, BelleParser("andR(1) & <(hideR(3), hideR(4))")))
    }
  }

  it should "extend a sequential composition" in {
    val t1 = BelleParser("implyR(1) ; andL(-1)")
    val t2 = BelleParser("implyR(1) ; andL(-1) ; orR(1)")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case SeqTactic(c0, SeqTactic(c1, c2: BelleDot)) =>
        c0 shouldBe BelleParser("implyR(1)")
        c1 shouldBe BelleParser("andL(-1)")
        diff._2 should contain theSameElementsAs (c2, BelleParser("nil")) :: Nil
        diff._3 should contain theSameElementsAs (c2, BelleParser("orR(1)")) :: Nil
    }
  }

  it should "extend a sequential composition 2" in {
    val t1 = BelleParser("implyR(1) ; andL(-1)")
    val t2 = BelleParser("(implyR(1) ; andL(-1)) ; orR(1)")
    val diff = TacticDiff.diff(t1, t2)
    //@todo strange result, but irrelevant
    inside (diff._1.t) {
      case SeqTactic(SeqTactic(c0, c1: BelleDot), c2: BelleDot) =>
        c0 shouldBe BelleParser("implyR(1)")
        diff._2 should contain theSameElementsAs (c1, BelleParser("nil")) :: (c2, BelleParser("andL(-1)")) :: Nil
        diff._3 should contain theSameElementsAs (c1, BelleParser("andL(-1)")) :: (c2, BelleParser("orR(1)")) :: Nil
    }
  }

  it should "extend an atom underneath a branch" in {
    val t1 = BelleParser("orL(-1) ; <(nil, andL(-1))")
    val t2 = BelleParser("orL(-1) ; <(nil, andL(-1) ; orR(1))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case SeqTactic(c0, BranchTactic(c1 :: SeqTactic(c2, c3: BelleDot) :: Nil)) =>
        c0 shouldBe BelleParser("orL(-1)")
        c1 shouldBe BelleParser("nil")
        c2 shouldBe BelleParser("andL(-1)")
        diff._2 should contain theSameElementsAs (c3, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c3, BelleParser("orR(1)"))::Nil
    }
  }

  it should "extend a sequential composition underneath a branch" in {
    val t1 = BelleParser("orL(-1) ; <(nil, andL(-1) ; andL(-2))")
    val t2 = BelleParser("orL(-1) ; <(nil, andL(-1) ; andL(-2) ; orR(1))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case SeqTactic(c0, BranchTactic(c1 :: SeqTactic(c2, SeqTactic(c3, (c4: BelleDot))) :: Nil)) =>
        c0 shouldBe BelleParser("orL(-1)")
        c1 shouldBe BelleParser("nil")
        c2 shouldBe BelleParser("andL(-1)")
        c3 shouldBe BelleParser("andL(-2)")
        diff._2 should contain theSameElementsAs (c4, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c4, BelleParser("orR(1)"))::Nil
    }
  }

  it should "extend an atom inside either" in {
    val t1 = BelleParser("andL(-1) | andL(-2) ")
    val t2 = BelleParser("andL(-1) | (andL(-2) ; andL(-3))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case EitherTactic(c0, SeqTactic(c1, c2: BelleDot)) =>
        c0 shouldBe BelleParser("andL(-1)")
        c1 shouldBe BelleParser("andL(-2)")
        diff._2 should contain theSameElementsAs (c2, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c2, BelleParser("andL(-3)"))::Nil
    }
  }

  it should "extend a sequential inside either" in {
    val t1 = BelleParser("andL(-1) | (andL(-2) ; andL(-3))")
    val t2 = BelleParser("andL(-1) | (andL(-2) ; andL(-3) ; andL(-4))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case EitherTactic(c0, SeqTactic(c1, SeqTactic(c2, c3: BelleDot))) =>
        c0 shouldBe BelleParser("andL(-1)")
        c1 shouldBe BelleParser("andL(-2)")
        c2 shouldBe BelleParser("andL(-3)")
        diff._2 should contain theSameElementsAs (c3, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c3, BelleParser("andL(-4)"))::Nil
    }
  }

  it should "extend an atom inside saturate" in {
    val t1 = BelleParser("andL(-1)*")
    val t2 = BelleParser("(andL(-1) ; andL(-2))*")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case SaturateTactic(SeqTactic(c0, c1: BelleDot)) =>
        c0 shouldBe BelleParser("andL(-1)")
        diff._2 should contain theSameElementsAs (c1, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c1, BelleParser("andL(-2)"))::Nil
    }
  }

  it should "extend a sequential inside saturate" in {
    val t1 = BelleParser("(andL(-1) ; andL(-2))*")
    val t2 = BelleParser("(andL(-1) ; andL(-2) ; andL(-3))*")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case SaturateTactic(SeqTactic(c0, SeqTactic(c1, c2: BelleDot))) =>
        c0 shouldBe BelleParser("andL(-1)")
        c1 shouldBe BelleParser("andL(-2)")
        diff._2 should contain theSameElementsAs (c2, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c2, BelleParser("andL(-3)"))::Nil
    }
  }

  it should "extend an atom inside repeat" in {
    val t1 = BelleParser("andL(-1)*3")
    val t2 = BelleParser("(andL(-1) ; andL(-2))*3")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case RepeatTactic(SeqTactic(c0, c1: BelleDot), _) =>
        c0 shouldBe BelleParser("andL(-1)")
        diff._2 should contain theSameElementsAs (c1, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c1, BelleParser("andL(-2)"))::Nil
    }
  }

  it should "extend a sequential inside repeat" in {
    val t1 = BelleParser("(andL(-1) ; andL(-2))*3")
    val t2 = BelleParser("(andL(-1) ; andL(-2) ; andL(-3))*3")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case RepeatTactic(SeqTactic(c0, SeqTactic(c1, c2: BelleDot)), _) =>
        c0 shouldBe BelleParser("andL(-1)")
        c1 shouldBe BelleParser("andL(-2)")
        diff._2 should contain theSameElementsAs (c2, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c2, BelleParser("andL(-3)"))::Nil
    }
  }

  it should "extend an atom inside onall" in {
    val t1 = BelleParser("doall(andL(-1))")
    val t2 = BelleParser("doall(andL(-1) ; andL(-2))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case OnAll(SeqTactic(c0, c1: BelleDot)) =>
        c0 shouldBe BelleParser("andL(-1)")
        diff._2 should contain theSameElementsAs (c1, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c1, BelleParser("andL(-2)"))::Nil
    }
  }

  it should "extend a sequential inside onall" in {
    val t1 = BelleParser("doall(andL(-1) ; andL(-2))")
    val t2 = BelleParser("doall(andL(-1) ; andL(-2) ; andL(-3))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case OnAll(SeqTactic(c0, SeqTactic(c1, c2: BelleDot))) =>
        c0 shouldBe BelleParser("andL(-1)")
        c1 shouldBe BelleParser("andL(-2)")
        diff._2 should contain theSameElementsAs (c2, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c2, BelleParser("andL(-3)"))::Nil
    }
  }

  //@todo not yet supported in diff
  it should "extend an atom inside let" ignore {
    val t1 = BelleParser("let ({`x=y`}) in (andL(-1))")
    val t2 = BelleParser("let ({`x=y`}) in (andL(-1) ; andL(-2))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case Let(_, _, SeqTactic(c0, c1: BelleDot)) =>
        c0 shouldBe BelleParser("andL(-1)")
        diff._2 should contain theSameElementsAs (c1, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c1, BelleParser("andL(-2)"))::Nil
    }
  }

  //@note not yet supported in diff
  it should "extend a sequential inside let" ignore {
    val t1 = BelleParser("let ({`x=y`}) in (andL(-1) ; andL(-2))")
    val t2 = BelleParser("let ({`x=y`}) in (andL(-1) ; andL(-2) ; andL(-3))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case Let(_, _, SeqTactic(c0, SeqTactic(c1, c2: BelleDot))) =>
        c0 shouldBe BelleParser("andL(-1)")
        c1 shouldBe BelleParser("andL(-2)")
        diff._2 should contain theSameElementsAs (c2, BelleParser("nil"))::Nil
        diff._3 should contain theSameElementsAs (c2, BelleParser("andL(-3)"))::Nil
    }
  }

  it should "match tactic definitions" in {
    val t1 = BelleParser("tactic t as (implyR(1))")
    val t2 = BelleParser("tactic t as (implyR(1))")
    TacticDiff.diff(t1, t2)._1.t shouldBe DefTactic("t", BelleParser("implyR(1)"))
  }

  it should "match inside tactic definitions" in {
    val t1 = BelleParser("tactic t as (implyR(1))")
    val t2 = BelleParser("tactic t as (andR(1))")
    val diff = TacticDiff.diff(t1, t2)
    inside (diff._1.t) {
      case DefTactic(n, c: BelleDot) =>
        diff._2 should contain theSameElementsAs (c, BelleParser("implyR(1)"))::Nil
        diff._3 should contain theSameElementsAs (c, BelleParser("andR(1)"))::Nil
    }
  }

}
