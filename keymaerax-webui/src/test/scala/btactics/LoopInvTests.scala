/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import testHelper.KeYmaeraXTestTags.{SlowTest, TodoTest}

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Loop invariant checking and generation tests etc.
 * @author
 *   Andre Platzer
 */
class LoopInvTests extends TacticTestBase {
  "loopPostMaster" should "find an invariant for x=5-> [{x:=x+2;{x'=1}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;{x'=1}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x=5-> [{{x'=2}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{{x'=2}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "prove x>=5 & y>=0 -> [{{x'=x+y};}*]x>=0 by invariant x>=0 & y>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{{x'=x+y}}*]x>=0".asFormula
    proveBy(fml, implyR(1) & loop("x>=0 & y>=0".asFormula)(1) < (QE, QE, odeInvariant(1))) shouldBe Symbol("proved")
  }

  it should "prove x>=5 & y>=0 -> [{{x'=x+y};}*]x>=0 by invariant x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{{x'=x+y}}*]x>=0".asFormula
    proveBy(fml, implyR(1) & loop("x>=0".asFormula)(1) < (QE, QE, odeInvariant(1))) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=0 -> [{{x'=x+y};}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{{x'=x+y}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find a invariant for x=4-> [{{x'=-x};}*]x>=0 with other init" in withMathematica { _ =>
    val fml = "x=4 -> [{{x'=-x}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find a invariant for x=5-> [{{x'=-x};}*]x>=0" in withMathematica { _ =>
    val fml = "x=5 -> [{{x'=-x}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find a invariant for x=5-> [{{x'=-x};}*]x>0" in withMathematica { _ =>
    val fml = "x=5 -> [{{x'=-x}}*]x>0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x>0".asFormula, "x=7".asFormula)
      .map(_ -> None)
      .to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  // todo: fails with no ODEs
  it should "at least not loop forever when finding an invariant for x=5-> [{x:=x+2;}*]x>=0" ignore withMathematica {
    _ =>
      val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
      val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).map(_ -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
      // @note postcondition is invariant, loopPostMaster won't ask invariant generator
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x=5-> [{{x'=0} ++ {x'=5}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{{x'=0} ++ {x'=5}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x=5-> [{x:=x+1;{x'=x}}*]x>=4 by counting up" in withMathematica { _ =>
    val fml = "x=5-> [{x:=x+1;{x'=x}}*]x>=4".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x>=-5".asFormula).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "prove x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]v>=0 by invariant v>=0" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]v>=0".asFormula
    proveBy(
      fml,
      implyR(1) & loop("v>=0".asFormula)(1) < (QE, QE, chase(1) & unfoldProgramNormalize & OnAll(ODE(1))),
    ) shouldBe Symbol("proved")
  }

  it should "find an invariant for x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]v>=0" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]v>=0".asFormula
    val invs = List(
      "x>=-1".asFormula,
      "v>=1".asFormula,
      "x>=0&v>1".asFormula,
      "v>=-1".asFormula,
      "v>=0".asFormula,
      "x=7".asFormula,
    ).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]x>=0" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{v:=-1; ++ v:=1;};{x'=v&v>=0}}*]x>=0".asFormula
    val invs = List(
      "x>=-1".asFormula,
      "v>=1".asFormula,
      "x>=0&v>1".asFormula,
      "v>=-1".asFormula,
      "v>=0".asFormula,
      "x>=0&v>=0".asFormula,
      "x=7".asFormula,
    ).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  // @todo time not in inv so odeInvariant won't work
  it should "prove x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10 by invariant x<=10" ignore
    withMathematica { _ =>
      val fml = "x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      proveBy(
        fml,
        implyR(1) & loop("x<=10".asFormula)(1) < (QE, QE, chase(1) & unfoldProgramNormalize & OnAll(solve(1) & QE)),
      ) shouldBe Symbol("proved")
      proveBy(
        fml,
        implyR(1) & loop("x<=10".asFormula)(1) < (QE, QE, chase(1) & unfoldProgramNormalize & OnAll(odeInvariant(1))),
      ) shouldBe Symbol("proved")
    }

  // @todo time not in inv so odeInvariant won't work
  it should
    "find an invariant for x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" ignore
    withMathematica { _ =>
      val fml = "x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      val invs = List(
        "x>=-1".asFormula,
        "v>=1".asFormula,
        "x>=0&v>1".asFormula,
        "v>=-1".asFormula,
        "v>=0".asFormula,
        "v<=5".asFormula,
        "x<=10".asFormula,
        "v<=5 & x<=10".asFormula,
        "x>=0&v>=0".asFormula,
        "v*v<10-x".asFormula,
        "x=7".asFormula,
      ).map(_ -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    }

  it should "find one invariant for x=0&v=0-> [{{?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in withMathematica { _ =>
    val fml = "x=0&v=0-> [{{?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula, "x<10".asFormula).map(_ -> None)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should
    "find one invariant for x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;t:=t; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in
    withMathematica { _ =>
      val fml =
        "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;t:=t; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula).map(_ -> None)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
    }

  it should
    "find one invariant for x=0&v=0&t=0-> [{{?x<9;v:=1; ++ ?false;t:=t; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in
    withMathematica { _ =>
      val fml = "x=0&v=0&t=0-> [{{?x<9;v:=1; ++ ?false;t:=t; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula).map(_ -> None)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
    }

  it should "find one invariant for x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in
    withMathematica { _ =>
      val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula).map(_ -> None)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
    }

  it should "find one invariant for x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" in
    withMathematica { _ =>
      val fml = "x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      val invs = List("x<=9+t&t>=0".asFormula, "x<=10".asFormula).map(_ -> None)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
    }

  // @todo time not in inv so odeInvariant won't work
  it should "find an invariant for x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10" ignore
    withMathematica { _ =>
      val fml = "x=0&v=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      val invs = List(
        "x>=-1".asFormula,
        "v>=1".asFormula,
        "x>=0&v>1".asFormula,
        "v>=-1".asFormula,
        "v>=0".asFormula,
        "v<=5".asFormula,
        "x<=10".asFormula,
        "v<=5 & x<=10".asFormula,
        "x>=0&v>=0".asFormula,
        "v*v<10-x".asFormula,
        "x=7".asFormula,
      ).map(_ -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    }

  it should "prove x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10 by invariant x<=10" in
    withMathematica { _ =>
      val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      // proveBy(fml, implyR(1) & loop("x<=10".asFormula)(1) <(QE,QE, chase(1) & unfoldProgramNormalize & OnAll(solve(1) & QE))) shouldBe 'proved
      proveBy(
        fml,
        implyR(1) &
          loop("x<=10".asFormula)(1) <
          (
            QE,
            QE,
            chase(1) &
              unfoldProgramNormalize < (odeInvariant(1), dC("x<=9+t".asFormula)(1) < (dW(1) & QE, odeInvariant(1))),
          ),
      ) shouldBe Symbol("proved")
    }

  it should "prove x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10 by invariant x<=10-t" ignore
    withMathematica { _ =>
      val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      proveBy(
        fml,
        implyR(1) &
          loop("x<=10-t&t>=0".asFormula)(1) < (QE, QE, chase(1) & unfoldProgramNormalize & OnAll(solve(1) & QE)),
      ) shouldBe Symbol("proved")
      // x<=10-t&t>=0 not an ODE invariant
      proveBy(
        fml,
        implyR(1) &
          loop("x<=10-t&t>=0".asFormula)(1) < (QE, QE, chase(1) & unfoldProgramNormalize & OnAll(odeInvariant(1))),
      ) shouldBe Symbol("proved")
    }

  it should
    "find an invariant for x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10 with more invariants" ignore
    withMathematica { _ =>
      val fml = "x=0&v=0&t=0-> [{{v:=-1; ++ ?x<9;v:=1; ++ ?false;v:=v;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
      // x<=10-t&t>=0 not an ODE invariant
      val invs = List(
        "x>=-1".asFormula,
        "v>=1".asFormula,
        "x>=0&v>1".asFormula,
        "v>=-1".asFormula,
        "v>=0".asFormula,
        "v<=5".asFormula,
        "x<=10".asFormula,
        "v<=5 & x<=10".asFormula,
        "x>=0&v>=0".asFormula,
        "x<=10-t".asFormula,
        "x<=10-t&t>=0".asFormula,
        "v*v<10-x".asFormula,
        "x=7".asFormula,
      ).map(_ -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;{x'=x^2+y}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;{x'=x^2+y}}*]x>=0".asFormula
    val invs =
      List("x>=-1".asFormula, "y>=1".asFormula, "x>=0&y>=0".asFormula, "x=7".asFormula).map(_ -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => Nil.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for circular motion" in withMathematica { _ =>
    val fml = "x=0 & y=1 -> [{{x'=y,y'=-x}}*]x<=1".asFormula
    val invs = ("x=0" :: "x^2+y^2=1" :: "x^2+y^2=2" :: Nil).map(_.asFormula -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    // @todo not yet supported
    // proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariantCandidates)(1)) shouldBe 'proved
  }

  it should "find an invariant when first branch informative" in withMathematica { _ =>
    val fml = "x=0&v=0 -> [{{?x<9;v:=1; ++ v:=-1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "y=0" :: Nil)
      .map(_.asFormula)
      .map(_ -> None)
      .to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    println("Prove again because it was so much fun")
    // todo: should be calling pegasusInvariants
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusCandidates)(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant when first branch uninformative" in withMathematica { _ =>
    val fml = "x=0&v=0 -> [{{v:=0; ++ ?x<9;v:=1;};t:=0;{x'=v,t'=1&t<=1}}*]x<=10".asFormula
    val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "y=0" :: Nil).map(_.asFormula -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    println("Prove again because it was so much fun")
    // todo: should be calling pegasusInvariants
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusCandidates)(1)) shouldBe Symbol("proved")
  }

  it should "directly prove with solve" in withMathematica { _ =>
    val fml =
      "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1&t<=1 & v>=0}}*]x<=10"
        .asFormula
    val pr = proveBy(
      fml,
      implyR(1) & loop("10-x>=v*v".asFormula)(1) < (QE, QE, chase(1) & unfoldProgramNormalize & OnAll(solve(1) & QE)),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove using invariants" in withMathematica { _ =>
    // This controller is tighter: 10-x>=v^2/2 +2*v+1
    // The v>=0 in domain constraint is not necessary, but makes the invariance argument easier
    val fml =
      "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1&t<=1 & v>=0}}*]x<=10"
        .asFormula
    val pr = proveBy(
      fml,
      implyR(1) &
        loop("10-x>=v*v".asFormula)(1) <
        (
          QE,
          QE,
          chase(1) &
            unfoldProgramNormalize <
            (
              dC("t>=0&(10-x>=2*(1-t)^2+(4*(1-t)+v)*v)".asFormula)(1) < (dW(1) & QE, odeInvariant(1)),
              dC("v=0".asFormula)(1) < (odeInvariant(1), odeInvariant(1)),
              odeInvariant(1),
            ),
        ),
    )
    println(pr)
    pr shouldBe Symbol("proved")
  }

  it should "prove the invariants of first a branch informative (scripted)" in withMathematica { _ =>
    // todo: These are getting proved directly with solve
    val fml =
      "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{{x'=v,v'=a,t'=1&t<=1&v>=0}@invariant((10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0),(v*v<=10-x),(v=0&x<=10))}}*]x<=10"
        .asFormula
    proveBy(fml, implyR(1) & loop("v*v<=10-x".asFormula)(1) < (QE, QE, auto(TactixLibrary.invGenerator, None))) shouldBe
      Symbol("proved")
  }

  it should "prove the invariants of first a branch informative (scripted) nosolve" in withMathematica { _ =>
    val fml =
      "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{{x'=v,v'=a,t'=1,z'=z&t<=1&v>=0}@invariant((v'=1->10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0),(v'=-1->v*v<=10-x),(v'=0->v=0&x<=10))}}*]x<=10"
        .asFormula
    proveBy(fml, implyR(1) & loop("v*v<=10-x".asFormula)(1) < (QE, QE, auto(TactixLibrary.invGenerator, None))) shouldBe
      Symbol("proved")
  }

  it should "prove the invariants of first a branch informative (scripted) 2" in withMathematica { _ =>
    // todo: These are getting proved directly with solve
    val fml =
      "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{{x'=v,v'=a,t'=1&t<=1&v>=0}@invariant((a=1->10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0),(a=-1->v*v<=10-x),(a=0->v=0&x<=10))}}*]x<=10"
        .asFormula
    proveBy(fml, implyR(1) & loop("v*v<=10-x".asFormula)(1) < (QE, QE, auto(TactixLibrary.invGenerator, None))) shouldBe
      Symbol("proved")
  }

  it should "prove the invariants of first a branch informative (scripted) 2 nosolve" in withMathematica { _ =>
    val fml =
      "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{{x'=v,v'=a,t'=1,z'=z&t<=1&v>=0}@invariant((v'=1->10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0),(v'=-1->v*v<=10-x),(v'=0->v=0&x<=10))}}*]x<=10"
        .asFormula
    proveBy(fml, implyR(1) & loop("v*v<=10-x".asFormula)(1) < (QE, QE, auto(TactixLibrary.invGenerator, None))) shouldBe
      Symbol("proved")
  }

  it should "find an invariant when first a branch informative (scripted)" taggedAs SlowTest in withMathematica { _ =>
    val fml =
      "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1&t<=1&v>=0}}*]x<=10"
        .asFormula
    val invs = ("10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0" :: "v*v<=10-x" :: "v=0&x<=10" :: "x<=10" :: "x=0" :: Nil)
      .map(_.asFormula -> None)
      .to(LazyList)
    // todo: this fails with the default (fast) odeInvariance setting because of DC chain v=0 & x<=10
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant when first a branch informative (scripted) nosolve" taggedAs SlowTest ignore
    withMathematica { _ =>
      val fml =
        "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1,z'=z&t<=1&v>=0}}*]x<=10"
          .asFormula
      val invs = ("10-x>=2*(1-t)^2+(4*(1-t)+v)*v&t>=0" :: "v*v<=10-x" :: "v=0&x<=10" :: "x<=10" :: "x=0" :: Nil)
        .map(_.asFormula -> None)
        .to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    }

  it should "FEATURE_REQUEST: find an invariant when first a branch informative" taggedAs TodoTest in withMathematica {
    _ =>
      // todo: Pegasus doesn't generate the invariant for a:=1 case
      val fml =
        "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1&t<=1&v>=0}}*]x<=10"
          .asFormula
      proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: find an invariant when first a branch informative nosolve" taggedAs TodoTest in
    withMathematica { _ =>
      // todo: Pegasus doesn't generate the invariant for a:=1 case
      val fml =
        "x=0&v=0&a=0 -> [{{?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0; ++ a:=-1;};t:=0;{x'=v,v'=a,t'=1,z'=z&t<=1&v>=0}}*]x<=10"
          .asFormula
      proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe Symbol("proved")
    }

  it should "FEATURE_REQUEST: find an invariant when middle branch informative" taggedAs TodoTest in withMathematica {
    _ =>
      // todo: Pegasus doesn't generate the invariant for a:=1 case
      val fml =
        "x=0&v=0&a=0 -> [{{a:=-1; ++ ?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0;};t:=0;{x'=v,v'=a,t'=1&t<=1&v>=0}}*]x<=10"
          .asFormula
      val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "x=0" :: Nil).map(_.asFormula -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe Symbol("proved")
      println("Prove again because it was so much fun")
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: find an invariant when middle branch informative nosolve" taggedAs TodoTest in
    withMathematica { _ =>
      // todo: Pegasus doesn't generate the invariant for a:=1 case
      val fml =
        "x=0&v=0&a=0 -> [{{a:=-1; ++ ?10-x>=2+(4+v)*v; a:=1; ++ v:=0;a:=0;};t:=0;{x'=v,v'=a,t'=1,z'=z&t<=1&v>=0}}*]x<=10"
          .asFormula
      val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "x=0" :: Nil).map(_.asFormula -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe Symbol("proved")
      println("Prove again because it was so much fun")
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    }

  it should "FEATURE_REQUEST: find an invariant when first a branch uninformative" taggedAs TodoTest in
    withMathematica { _ =>
      // todo: Pegasus doesn't generate the invariant for a:=1 case
      val fml =
        "x=0&v=0&a=0 -> [{{v:=0;a:=0; ++ a:=-1; ++ ?10-x>=2+(4+v)*v; a:=1;};t:=0;{x'=v,v'=a,t'=1&t<=1&v>=0}}*]x<=10"
          .asFormula
      val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "x=0" :: Nil).map(_.asFormula -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe Symbol("proved")
      println("Prove again because it was so much fun")
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    }

  it should "FEATURE_REQUEST: find an invariant when first a branch uninformative nosolve" taggedAs TodoTest in
    withMathematica { _ =>
      // todo: Pegasus doesn't generate the invariant for a:=1 case
      val fml =
        "x=0&v=0&a=0 -> [{{v:=0;a:=0; ++ a:=-1; ++ ?10-x>=2+(4+v)*v; a:=1;};t:=0;{x'=v,v'=a,t'=1,z'=z&t<=1&v>=0}}*]x<=10"
          .asFormula
      val invs = ("x<9+t&t>=0" :: "v<=1" :: "v>=0" :: "x<=10" :: "x=0" :: Nil).map(_.asFormula -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe Symbol("proved")
      println("Prove again because it was so much fun")
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    }

  it should "find an invariant for the Ahmadi Parillo Kristic benchmark example" in withMathematica { _ =>
    val fml =
      "1/2*x<=x & x<=7/10 & 0<=y & y<=3/10 -> [{{x'=-x+x*y, y'=-y}}*]!(-8/10>=x & x>=-1 & -7/10>=y & y>=-1)".asFormula
    val invs = ("y<=0" :: "y>=0" :: "y=0" :: Nil).map(_.asFormula -> None).to(LazyList)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
    println("Prove again because it was so much fun")
    proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: find an invariant for a simple time-triggered example" taggedAs TodoTest in
    withMathematica { _ =>
      val fml = """v=0 & A>=0 & b>0 & x<=m & ep>=0
                  | -> [
                  |      {
                  |        {?(2*b*(m-x) >= v^2+(A+b)*(A*ep^2+2*ep*v)); a:=A; ++ a:=-b; }
                  |        t := 0;
                  |        {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
                  |      }*
                  |    ] x <= m
      """.stripMargin.asFormula
      val invs = ("v<=0" :: "v^2<=2*b*(m-x)" :: Nil).map(_.asFormula).map(_ -> None).to(LazyList)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs)(1)) shouldBe Symbol("proved")
      // todo generate invariant candidates
      proveBy(fml, implyR(1) & loopPostMaster(InvariantGenerator.pegasusInvariants)(1)) shouldBe Symbol("proved")
    }

  it should "find an invariant for x>=5 & y>=0 -> [{y:=y+1;{x'=x+y}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{y:=y+1;{x'=x+y}}*]x>=1".asFormula
    val invs = List(
      "x>=-1".asFormula,
      "y>=1".asFormula,
      "x>=0&y>=0".asFormula,
      "x>=1&y>=1".asFormula,
      "x>=1&y>=0".asFormula,
      "x=7".asFormula,
    ).map(_ -> None)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x+y}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x+y}}*]x>=1".asFormula
    val invs = List(
      "x>=-1".asFormula,
      "y>=1".asFormula,
      "x>=0&y>=0".asFormula,
      "x>=1&y>=1".asFormula,
      "x>=1&y>=0".asFormula,
      "x=7".asFormula,
    ).map(_ -> None)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=0 -> [{y:=y+1;{x'=x+y,y'=5}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{y:=y+1;{x'=x+y,y'=5}}*]x>=1".asFormula
    val invs = List(
      "x>=-1".asFormula,
      "y>=1".asFormula,
      "x>=0&y>=0".asFormula,
      "x>=1&y>=1".asFormula,
      "x>=1&y>=0".asFormula,
      "x=7".asFormula,
    ).map(_ -> None)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x+y,y'=5}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x+y,y'=5}}*]x>=1".asFormula
    val invs = List(
      "x>=-1".asFormula,
      "y>=1".asFormula,
      "x>=0&y>=0".asFormula,
      "x>=1&y>=1".asFormula,
      "x>=1&y>=0".asFormula,
      "x=7".asFormula,
    ).map(_ -> None)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=1 -> [{y:=y+1;{x'=x^2+2*y+x,y'=y^2+y}}*]x>=1" in withMathematica { _ =>
    val fml = "x>=5 & y>=1 -> [{y:=y+1;{x'=x^2+2*y+x,y'=y^2+y}}*]x>=1".asFormula
    val invs = List(
      "x>=-1".asFormula,
      "y>=1".asFormula,
      "x>=0&y>=0".asFormula,
      "x>=1&y>=1".asFormula,
      "x>=1&y>=0".asFormula,
      "x=7".asFormula,
    ).map(_ -> None)
    proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=1 -> [{x:=x+y;y:=y+1;{x'=x^2+2*y+x,y'=y^2+y}}*]x>=1" taggedAs SlowTest in
    withMathematica { _ =>
      val fml = "x>=5 & y>=1 -> [{x:=x+y;y:=y+1;{x'=x^2+2*y+x,y'=y^2+y}}*]x>=1".asFormula
      val invs = List(
        "x>=-1".asFormula,
        "y>=1".asFormula,
        "x>=0&y>=0".asFormula,
        "x>=1&y>=1".asFormula,
        "x>=1&y>=0".asFormula,
        "x=7".asFormula,
      ).map(_ -> None)
      proveBy(fml, implyR(1) & loopPostMaster((_, _, _) => invs.to(LazyList))(1)) shouldBe Symbol("proved")
    }

  def feedOneAfterTheOther[A <: Expression](list: List[A]): (ProvableSig, ProverException) => Seq[Expression] = {
    var rem = list
    (_, e) =>
      println("SnR loop status " + e)
      rem match {
        case hd :: tail => rem = tail; hd :: Nil
        case Nil => throw new BelleNoProgress("SearchAndRescueAgain ran out of alternatives among: " + list)
      }
  }

  "SnR Loop Invariant" should "find an invariant for x=5-> [{x:=x+2;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val jj = "j(.)".asFormula
    val proof = proveBy(
      fml,
      implyR(1) & SearchAndRescueAgain(
        jj :: Nil,
        loop(USubst(Seq(SubstitutionPair(".".asTerm, "x".asTerm)))(jj))(1) < (nil, nil, chase(1)),
        feedOneAfterTheOther(invs),
        OnAll(auto(TactixLibrary.invGenerator, None)) & done,
      ),
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe Symbol("proved")
    proveBy(fml, implyR(1) & loopSR((_, _, _) => invs.map(_ -> None).to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val jj = "j(.)".asFormula
    val proof = proveBy(
      fml,
      implyR(1) & SearchAndRescueAgain(
        jj :: Nil,
        loop(USubst(Seq(SubstitutionPair(".".asTerm, "x".asTerm)))(jj))(1) < (nil, nil, chase(1)),
        feedOneAfterTheOther(invs),
        OnAll(auto(TactixLibrary.invGenerator, None)) & done,
      ),
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe Symbol("proved")
    // Note: dependency analysis generates (x,y) instead of just x
    val invs2 = invs.map(USubst(Seq(SubstitutionPair(DotTerm(), DotTerm(Real, Some(0)))))(_) -> None)
    proveBy(fml, implyR(1) & loopSR((_, _, _) => invs2.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;y:=y+1;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;}*]x>=0".asFormula
    val invs = List("._0>=-1 & ._1>=0".asFormula, "._0=5  & ._1>=0".asFormula, "._0>=0 & ._1>=0".asFormula)
    val jj = "j(._0,._1)".asFormula
    val proof = proveBy(
      fml,
      implyR(1) & SearchAndRescueAgain(
        jj :: Nil,
        loop(USubst(Seq(SubstitutionPair("._0".asTerm, "x".asTerm), SubstitutionPair("._1".asTerm, "y".asTerm)))(jj))(
          1
        ) < (nil, nil, chase(1)),
        feedOneAfterTheOther(invs),
        OnAll(auto(TactixLibrary.invGenerator, None)) & done,
      ),
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe Symbol("proved")
    proveBy(fml, implyR(1) & loopSR((_, _, _) => invs.map(_ -> None).to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;{x'=x^2+y}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 & y>=0 -> [{x:=x+y;{x'=x^2+y}}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val jj = "j(.)".asFormula
    val proof = proveBy(
      fml,
      implyR(1) & SearchAndRescueAgain(
        jj :: Nil,
        loop(USubst(Seq(SubstitutionPair(".".asTerm, "x".asTerm)))(jj))(1) < (nil, nil, chase(1)),
        feedOneAfterTheOther(invs),
        OnAll(auto(TactixLibrary.invGenerator, None)) & done,
      ),
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe Symbol("proved")
    val invs2 = invs.map(USubst(Seq(SubstitutionPair(DotTerm(), DotTerm(Real, Some(0)))))(_) -> None)
    proveBy(fml, implyR(1) & loopSR((_, _, _) => invs2.to(LazyList))(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: prove x>=5 & y>=0 -> [{{x'=x^2+y,y'=x+1}}*]x>=0 by invariant x>=0&y>=0" taggedAs
    TodoTest in withMathematica { _ =>
      val fml = "x>=5 & y>=0 -> [{{x'=x^2+y,y'=x+1}}*]x>=0".asFormula
      proveBy(fml, implyR(1) & loop("x>=0&y>=0".asFormula)(1) < (QE, QE, odeInvariant(1))) shouldBe Symbol("proved")
    }

  it should
    "FEATURE_REQUEST: prove x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x+1}}*]x>=0 by invariant x>=0&y>=0" taggedAs
    TodoTest in withMathematica { _ =>
      val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x+1}}*]x>=0".asFormula
      proveBy(
        fml,
        implyR(1) &
          loop("x>=0&y>=0".asFormula)(1) <
          (QE, QE, composeb(1) & assignb(1) & composeb(1) & assignb(1) & odeInvariant(1)),
      ) shouldBe Symbol("proved")
    }

  it should
    "FEATURE_REQUEST: prove x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x}}*]x>=0 by invariant x>=0&y>=0" taggedAs
    TodoTest in withMathematica { _ =>
      // Failing test case because of equilibrium at x=0,y=0
      val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x}}*]x>=0".asFormula
      proveBy(
        fml,
        implyR(1) &
          loop("x>=0&y>=0".asFormula)(1) <
          (QE, QE, composeb(1) & assignb(1) & composeb(1) & assignb(1) & odeInvariant(1)),
      ) shouldBe Symbol("proved")
    }

  it should "find an invariant for x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x}}*]x>=0" taggedAs SlowTest in
    withMathematica { _ =>
      val fml = "x>=5 & y>=0 -> [{x:=x+y;y:=y+1;{x'=x^2+y,y'=x}}*]x>=0".asFormula
      val invs = List("._0>=-1 & ._1>=0".asFormula, "._0=5  & ._1>=0".asFormula, "._0>=0 & ._1>=0".asFormula)
      proveBy(fml, implyR(1) & loopSR((_, _, _) => invs.map(_ -> None).to(LazyList))(1)) shouldBe Symbol("proved")

      val jj = "j(._0,._1)".asFormula
      val proof = proveBy(
        fml,
        implyR(1) & SearchAndRescueAgain(
          jj :: Nil,
          loop(USubst(Seq(SubstitutionPair("._0".asTerm, "x".asTerm), SubstitutionPair("._1".asTerm, "y".asTerm)))(jj))(
            1
          ) < (nil, nil, chase(1)),
          feedOneAfterTheOther(invs),
          OnAll(auto(TactixLibrary.invGenerator, None)) & done,
        ),
      )
      proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
      proof shouldBe Symbol("proved")
      proveBy(fml, implyR(1) & loopSR((_, _, _) => invs.map(_ -> None).to(LazyList))(1)) shouldBe Symbol("proved")
    }

}
