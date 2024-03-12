/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.SlowTest

@SlowTest
class SCUBATests extends TacticTestBase {
  "tApprox" should "prove with statistics" in withMathematica(_ => {
    val modelString = """ProgramVariables.
                        |  R a.
                        |  R b.
                        |  R x.
                        |  R xinit.
                        |  R tau.
                        |  R t.
                        |  R tApprox.
                        |
                        |  R d.
                        |  R v.
                        |  R vAsc.
                        |  R vDesc.
                        |
                        |  R c.
                        |  R C.
                        |
                        |  R x0.
                        |  R d0.
                        |  R t0.
                        |
                        |  R HRmin.
                        |  R HRmax.
                        |End.
                        |Problem.
                        |(
                        |  0 < HRmin & HRmin < HRmax &
                        |  HRmin <= a & a <= HRmax &
                        |  HRmin <= x & x <= HRmax &
                        |  b>0 & tau>0 & t>=0 & vAsc < 0 & vDesc > 0 & d >= 0 & d0 = d & c=0 & C>0 &
                        |  t > tau * HRmax * -d/vAsc &
                        |  tApprox = t
                        |)
                        |->
                        |[
                        |{
                        |  /* Reset discrete ghosts aka take sensor measurements. */
                        |  x0 := x;
                        |  d0 := d;
                        |  t0 := t;
                        |  {
                        |    /* Case 1: Descend. */
                        |    {
                        |      ?tApprox > tau*HRmax*-(d + vDesc*C)/vAsc + tau*HRmax*C;
                        |      a := *;
                        |      ?(HRmin <= a & a <= HRmax);
                        |      v := vDesc;
                        |    }
                        |    ++
                        |    /* Case 2: Horizontal movement at varying intensity. */
                        |    {
                        |      a := *;
                        |      ?(HRmin <= a & a <= HRmax);
                        |      ?tApprox > tau*HRmax*-d/vAsc + tau*HRmax*C;
                        |      v := 0;
                        |    }
                        |    ++
                        |    /* Case 3: Ascend (emergency action) */
                        |    {
                        |      a := *;
                        |      ?(HRmin <= a & a <= HRmax);
                        |      /* note: at this point in the code we need that x<=a via a loop invariant */
                        |      v := vAsc;
                        |    }
                        |  }
                        |  c := 0;
                        |  {
                        |    x' = -(x-a)*b,
                        |    t' = -tau*x,
                        |    d' = v,
                        |    c' = 1
                        |    & d >= 0
                        |    & c <= C
                        |  };
                        |  tApprox := tApprox - tau*HRmax*c;
                        |}*@invariant(
                        |  (0 < HRmin & HRmin < HRmax &
                        |   HRmin <= a & a <= HRmax &
                        |   b>0 & tau>0 & vAsc < 0 & vDesc > 0 & d = d0 + v*c & c>=0 & C>0
                        |  ) &
                        |  (d >= 0 & HRmin <= x & x <= HRmax) &
                        |  tau*HRmax*-d/vAsc < t &
                        |  tApprox <= t
                        |)]t>0
                        |End.""".stripMargin

    val model = ArchiveParser.parseAsFormula(modelString)

//    val tacticDefns = scala.io.Source.fromFile("/home/nfulton/dev/scuba-release/tApprox/human_readable.kyt").mkString
//    val tactic = BelleParserLinker(tacticDefns, "main").asTactic

    val tactic =
      """unfold ; loop({`(0 < HRmin&HRmin < HRmax&HRmin<=a&a<=HRmax&b>0&tau>0&vAsc < 0&vDesc>0&d=d0+v*c&c>=0&C>0)&(d>=0&HRmin<=x&x<=HRmax)&tau*HRmax*(-d/vAsc) < t&tApprox<=t`}, 1) ; <(
        |  QE,
        |  QE,
        |  composeb(1) ; assignb(1) ; composeb(1) ; assignb(1) ; composeb(1) ; assignb(1) ; composeb(1) ; composeb(1.1) ; composeb(1.1.1) ; assignb(1.1.1.1) ; dC({`HRmin<=x&x<=HRmax`}, 1.1.1) ; <(
        |unfold,
        |nil
        |) ; <(
        |    (boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |(boxAnd(1) ; andR(1)) ; <(
        |dW(1) ; QE,
        |  (boxAnd(1) ; andR(1)) ; <(
        |  nil,
        |    nil
        |  )
        |)
        |) ; <(
        |      dC({`d=old(d)+vDesc*c`}, 1) ; <(
        |nil,
        |dI(1)
        |) ; dC({`t>=old(t)-tau*HRmax*c`}, 1) ; <(
        |        dC({`t>=tApprox-tau*HRmax*c`}, 1) ; <(
        |nil,
        |dI(1)
        |) ; dC({`tApprox>tau*HRmax*(-(d_0+vDesc*C)/vAsc)+tau*HRmax*C`}, 1) ; <(
        |nil,
        |dW(1) ; QE
        |) ; dW(1) ; QE,
        |        dI(1)
        |        ),
        |      dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |dW(1) ; QE,
        |dI(1)
        |)
        |      ),
        |    MR({`HRmin<=x&x<=HRmax&HRmin<=a&a<=HRmax`}, 1) ; <(
        |master,
        |assignb(1) ; boxAnd(1) ; andR(1) ; <(
        |unfold ; ((cut({`x>=a|x < a`}) ; <(
        |  nil,
        |    hideR(1) ; QE
        |  )) ; orL('Llast)) ; <(
        |  ((((MR({`x>=a`}, 1) ; <(
        |    nil,
        |      QE
        |    )) ; cut({`x=a|x>a`})) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; orL('Llast)) ; <(
        |    ((MR({`x=a`}, 1) ; <(
        |      nil,
        |        QE
        |      )) ; dG({`{y'=b*y}`}, {`y*(x-a)=0&y>0`}, 1) ; (cut({`\exists y (y*(x-a)=0&y>0)`}) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; boxAnd(1) ; andR(1)) ; <(
        |      dI(1),
        |        ((dG({`{z'=(-b/2)*z}`}, {`y*z^2=1`}, 1) ; cut({`\exists z y*z^2=1`})) ; <(
        |        nil,
        |          hideR(1) ; QE
        |        )) ; existsL('Llast) ; existsR({`z`}, 1) ; dI(1)
        |      ),
        |      dG({`{y'=b/2*y}`}, {`y^2*(x-a)=1`}, 1) ; (cut({`\exists y y^2*(x-a)=1`}) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1)
        |    ),
        |    (((dC({`x < a`}, 1) ; <(
        |    dI(1),
        |      nil
        |    )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=-1`}, 1) ; cut({`\exists y y^2*(x-a)=-1`})) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1) ; QE
        |  ),
        |  unfold ; ((cut({`x<=a|x>a`}) ; <(
        |  nil,
        |    hideR(1) ; QE
        |  )) ; orL('Llast)) ; <(
        |  ((((MR({`x<=a`}, 1) ; <(
        |    nil,
        |      QE
        |    )) ; cut({`x=a|x < a`})) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; orL('Llast)) ; <(
        |    ((MR({`x=a`}, 1) ; <(
        |      nil,
        |        QE
        |      )) ; dG({`{y'=b*y}`}, {`y*(x-a)=0&y>0`}, 1) ; (cut({`\exists y (y*(x-a)=0&y>0)`}) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; boxAnd(1) ; andR(1)) ; <(
        |      dI(1),
        |        ((dG({`{z'=(-b/2)*z}`}, {`y*z^2=1`}, 1) ; cut({`\exists z y*z^2=1`})) ; <(
        |        nil,
        |          hideR(1) ; QE
        |        )) ; existsL('Llast) ; existsR({`z`}, 1) ; dI(1)
        |      ),
        |      (((MR({`x < a`}, 1) ; <(
        |      nil,
        |        QE
        |      )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=-1`}, 1) ; cut({`\exists y y^2*(x-a)=-1`})) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1) ; QE
        |    ),
        |    (dC({`x>a`}, 1) ; <(
        |    dI(1),
        |      nil
        |    )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=1`}, 1) ; (cut({`\exists y y^2*(x-a)=1`}) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1)
        |  )
        |)
        |),
        |    (boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |(boxAnd(1) ; andR(1)) ; <(
        |dW(1) ; QE,
        |  (boxAnd(1) ; andR(1)) ; <(
        |  nil,
        |    nil
        |  )
        |)
        |) ; <(
        |      dC({`t>=old(t)-tau*HRmax*c&tApprox-tau*HRmax*c>tau*HRmax*(-d/vAsc)+tau*HRmax*C-tau*HRmax*c`}, 1) ; <(
        |dC({`old(t)-tau*HRmax*c>=tApprox-tau*HRmax*c`}, 1) ; <(
        |dW(1) ; QE,
        |  dW(1) ; QE
        |),
        |dI(1)
        |),
        |      dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |dW(1) ; QE,
        |dI(1)
        |)
        |      ),
        |    (boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |(boxAnd(1) ; andR(1)) ; <(
        |dW(1) ; QE,
        |  (boxAnd(1) ; andR(1)) ; <(
        |  nil,
        |    nil
        |  )
        |)
        |) ; <(
        |      ((((dC({`d=vAsc*c+old(d)`}, 1) ; <(
        |nil,
        |dI(1)
        |)) ; dC({`t>=old(t)-tau*HRmax*c`}, 1)) ; <(
        |nil,
        |dI(1)
        |)) ; dC({`old(t)>tau*HRmax*(-old(d)/vAsc)`}, 1)) ; <(
        |nil,
        |dW(1) ; QE
        |) ; dW(1) ; QE,
        |      dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |dW(1) ; QE,
        |dI(1)
        |)
        |      )
        |    )
        |  )""".stripMargin.asTactic

    val tactic2 =
      """unfold ; loop({`(0 < HRmin&HRmin < HRmax&HRmin<=a&a<=HRmax&b>0&tau>0&vAsc < 0&vDesc>0&d=d0+v*c&c>=0&C>0)&(d>=0&HRmin<=x&x<=HRmax)&tau*HRmax*(-d/vAsc) < t&tApprox<=t`}, 1) ; <(
        |  QE,
        |  QE,
        |  composeb(1) ; assignb(1) ; composeb(1) ; assignb(1) ; composeb(1) ; assignb(1) ; composeb(1) ; MR({`tApprox<=t`}, 1) ; <(
        |    master,
        |    composeb(1) ; composeb(1.1) ; composeb(1.1.1) ; assignb(1.1.1.1) ; (dC({`HRmin<=x&x<=HRmax`}, 1.1.1) ; <(
        |unfold,
        |nil
        |)) ; <(
        |((boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |  (boxAnd(1) ; andR(1)) ; <(
        |  dW(1) ; QE,
        |    (boxAnd(1) ; andR(1)) ; <(
        |    nil,
        |      nil
        |    )
        |  )
        |)) ; <(
        |(dC({`d=old(d)+vDesc*c`}, 1) ; <(
        |  nil,
        |    dI(1)
        |  )) ; dC({`t>=old(t)-tau*HRmax*c`}, 1) ; <(
        |  (dC({`t>=tApprox-tau*HRmax*c`}, 1) ; <(
        |    nil,
        |      dI(1)
        |    )) ; (dC({`tApprox>tau*HRmax*(-(d_0+vDesc*C)/vAsc)+tau*HRmax*C`}, 1) ; <(
        |    nil,
        |      dW(1) ; QE
        |    )) ; dW(1) ; QE,
        |    dI(1)
        |  ),
        |  dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |  dW(1) ; QE,
        |    dI(1)
        |  )
        |),
        |MR({`HRmin<=x&x<=HRmax&HRmin<=a&a<=HRmax`}, 1) ; <(
        |master,
        |  assignb(1) ; boxAnd(1) ; andR(1) ; <(
        |  unfold ; ((cut({`x>=a|x < a`}) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; orL('Llast)) ; <(
        |    ((((MR({`x>=a`}, 1) ; <(
        |      nil,
        |        QE
        |      )) ; cut({`x=a|x>a`})) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; orL('Llast)) ; <(
        |      ((MR({`x=a`}, 1) ; <(
        |        nil,
        |          QE
        |        )) ; dG({`{y'=b*y}`}, {`y*(x-a)=0&y>0`}, 1) ; (cut({`\exists y (y*(x-a)=0&y>0)`}) ; <(
        |        nil,
        |          hideR(1) ; QE
        |        )) ; existsL('Llast) ; existsR({`y`}, 1) ; boxAnd(1) ; andR(1)) ; <(
        |        dI(1),
        |          ((dG({`{z'=(-b/2)*z}`}, {`y*z^2=1`}, 1) ; cut({`\exists z y*z^2=1`})) ; <(
        |          nil,
        |            hideR(1) ; QE
        |          )) ; existsL('Llast) ; existsR({`z`}, 1) ; dI(1)
        |        ),
        |        dG({`{y'=b/2*y}`}, {`y^2*(x-a)=1`}, 1) ; (cut({`\exists y y^2*(x-a)=1`}) ; <(
        |        nil,
        |          hideR(1) ; QE
        |        )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1)
        |      ),
        |      (((dC({`x < a`}, 1) ; <(
        |      dI(1),
        |        nil
        |      )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=-1`}, 1) ; cut({`\exists y y^2*(x-a)=-1`})) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1) ; QE
        |    ),
        |    unfold ; ((cut({`x<=a|x>a`}) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; orL('Llast)) ; <(
        |    ((((MR({`x<=a`}, 1) ; <(
        |      nil,
        |        QE
        |      )) ; cut({`x=a|x < a`})) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; orL('Llast)) ; <(
        |      ((MR({`x=a`}, 1) ; <(
        |        nil,
        |          QE
        |        )) ; dG({`{y'=b*y}`}, {`y*(x-a)=0&y>0`}, 1) ; (cut({`\exists y (y*(x-a)=0&y>0)`}) ; <(
        |        nil,
        |          hideR(1) ; QE
        |        )) ; existsL('Llast) ; existsR({`y`}, 1) ; boxAnd(1) ; andR(1)) ; <(
        |        dI(1),
        |          ((dG({`{z'=(-b/2)*z}`}, {`y*z^2=1`}, 1) ; cut({`\exists z y*z^2=1`})) ; <(
        |          nil,
        |            hideR(1) ; QE
        |          )) ; existsL('Llast) ; existsR({`z`}, 1) ; dI(1)
        |        ),
        |        (((MR({`x < a`}, 1) ; <(
        |        nil,
        |          QE
        |        )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=-1`}, 1) ; cut({`\exists y y^2*(x-a)=-1`})) ; <(
        |        nil,
        |          hideR(1) ; QE
        |        )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1) ; QE
        |      ),
        |      (dC({`x>a`}, 1) ; <(
        |      dI(1),
        |        nil
        |      )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=1`}, 1) ; (cut({`\exists y y^2*(x-a)=1`}) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1)
        |    )
        |  )
        |),
        |((boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |  (boxAnd(1) ; andR(1)) ; <(
        |  dW(1) ; QE,
        |    (boxAnd(1) ; andR(1)) ; <(
        |    nil,
        |      nil
        |    )
        |  )
        |)) ; <(
        |dC({`t>=old(t)-tau*HRmax*c&tApprox-tau*HRmax*c>tau*HRmax*(-d/vAsc)+tau*HRmax*C-tau*HRmax*c`}, 1) ; <(
        |  dC({`old(t)-tau*HRmax*c>=tApprox-tau*HRmax*c`}, 1) ; <(
        |    dW(1) ; QE,
        |      dW(1) ; QE
        |    ),
        |    dI(1)
        |  ),
        |  dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |  dW(1) ; QE,
        |    dI(1)
        |  )
        |),
        |((boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |  (boxAnd(1) ; andR(1)) ; <(
        |  dW(1) ; QE,
        |    (boxAnd(1) ; andR(1)) ; <(
        |    nil,
        |      nil
        |    )
        |  )
        |)) ; <(
        |(((((dC({`d=vAsc*c+old(d)`}, 1) ; <(
        |  nil,
        |    dI(1)
        |  )) ; dC({`t>=old(t)-tau*HRmax*c`}, 1)) ; <(
        |  nil,
        |    dI(1)
        |  )) ; dC({`old(t)>tau*HRmax*(-old(d)/vAsc)`}, 1)) ; <(
        |  nil,
        |    dW(1) ; QE
        |  )) ; dW(1) ; QE,
        |  dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |  dW(1) ; QE,
        |    dI(1)
        |  )
        |)
        |)
        |    )
        |  )""".stripMargin.asTactic

    val full =
      """unfold ; loop({`(0 < HRmin&HRmin < HRmax&HRmin<=a&a<=HRmax&b>0&tau>0&vAsc < 0&vDesc>0&d=d0+v*c&c>=0&C>0&stopTime>0&stopDepth>0)&(d>=0&HRmin<=x&x<=HRmax)&tau*HRmax*(-d/vAsc)+tau*HRmax*(stopTime-stoppedTimer) < t&tApprox<=t&stopTime>=stoppedTimer&(d>=stopDepth|stoppedTimer>=stopTime)`}, 1) ; <(
        |QE,
        |QE,
        |composeb(1) ; assignb(1) ; composeb(1) ; assignb(1) ; composeb(1) ; assignb(1) ; composeb(1) ; MR({`tApprox<=t`}, 1) ; <(
        |master,
        |  (andL('L)* ; composeb(1) ; composeb(1.1) ; composeb(1.1.1) ; assignb(1.1.1.1) ; dC({`HRmin<=x&x<=HRmax`}, 1.1.1)) ; <(
        |  unfold,
        |    nil
        |  )
        |)
        |) ; <(
        |  (boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |(boxAnd(1) ; andR(1)) ; <(
        |dW(1) ; QE,
        |  (boxAnd(1) ; andR(1)) ; <(
        |  nil,
        |    (boxAnd(1) ; andR(1)) ; <(
        |    nil,
        |      (boxAnd(1) ; andR(1)) ; <(
        |      dW(1) ; QE,
        |        nil
        |      )
        |    )
        |  )
        |)
        |) ; <(
        |    dC({`t>=old(t)-tau*HRmax*c&d=old(d)+vDesc*c`}, 1) ; <(
        |dC({`old(t)-tau*HRmax*c>=tApprox-tau*HRmax*c&tApprox-tau*HRmax*c>tau*HRmax*(-(d_0+vDesc*C)/vAsc)+tau*HRmax*C+tau*HRmax*(stopTime-stoppedTimer)-tau*HRmax*c&tau*HRmax*(-(d_0+vDesc*C)/vAsc)+tau*HRmax*C+tau*HRmax*(stopTime-stoppedTimer)-tau*HRmax*c>=tau*HRmax*(-d/vAsc)+tau*HRmax*C+tau*HRmax*(stopTime-stoppedTimer)-tau*HRmax*c&tau*HRmax*(-d/vAsc)+tau*HRmax*C+tau*HRmax*(stopTime-stoppedTimer)-tau*HRmax*c>=tau*HRmax*(-d/vAsc)+tau*HRmax*(stopTime-stoppedTimer)`}, 1) ; <(
        |dW(1) ; QE,
        |  boxAnd(1) ; andR(1) ; <(
        |  dI(1),
        |    boxAnd(1) ; andR(1) ; <(
        |    dI(1),
        |      boxAnd(1) ; andR(1) ; <(
        |      dW(1) ; QE,
        |        dW(1) ; QE
        |      )
        |    )
        |  )
        |),
        |dI(1)
        |),
        |    dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |dW(1) ; QE,
        |dI(1)
        |),
        |    orL('L) ; <(
        |ODE(1),
        |ODE(1)
        |)
        |    ),
        |  MR({`HRmin<=x&x<=HRmax&HRmin<=a&a<=HRmax`}, 1) ; <(
        |master,
        |assignb(1) ; boxAnd(1) ; andR(1) ; <(
        |unfold ; ((cut({`x>=a|x < a`}) ; <(
        |  nil,
        |    hideR(1) ; QE
        |  )) ; orL('Llast)) ; <(
        |  ((((MR({`x>=a`}, 1) ; <(
        |    nil,
        |      QE
        |    )) ; cut({`x=a|x>a`})) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; orL('Llast)) ; <(
        |    ((MR({`x=a`}, 1) ; <(
        |      nil,
        |        QE
        |      )) ; dG({`{y'=b*y}`}, {`y*(x-a)=0&y>0`}, 1) ; (cut({`\exists y (y*(x-a)=0&y>0)`}) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; boxAnd(1) ; andR(1)) ; <(
        |      dI(1),
        |        ((dG({`{z'=(-b/2)*z}`}, {`y*z^2=1`}, 1) ; cut({`\exists z y*z^2=1`})) ; <(
        |        nil,
        |          hideR(1) ; QE
        |        )) ; existsL('Llast) ; existsR({`z`}, 1) ; dI(1)
        |      ),
        |      dG({`{y'=b/2*y}`}, {`y^2*(x-a)=1`}, 1) ; (cut({`\exists y y^2*(x-a)=1`}) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1)
        |    ),
        |    (((dC({`x < a`}, 1) ; <(
        |    dI(1),
        |      nil
        |    )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=-1`}, 1) ; cut({`\exists y y^2*(x-a)=-1`})) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1) ; QE
        |  ),
        |  unfold ; ((cut({`x<=a|x>a`}) ; <(
        |  nil,
        |    hideR(1) ; QE
        |  )) ; orL('Llast)) ; <(
        |  ((((MR({`x<=a`}, 1) ; <(
        |    nil,
        |      QE
        |    )) ; cut({`x=a|x < a`})) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; orL('Llast)) ; <(
        |    ((MR({`x=a`}, 1) ; <(
        |      nil,
        |        QE
        |      )) ; dG({`{y'=b*y}`}, {`y*(x-a)=0&y>0`}, 1) ; (cut({`\exists y (y*(x-a)=0&y>0)`}) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; boxAnd(1) ; andR(1)) ; <(
        |      dI(1),
        |        ((dG({`{z'=(-b/2)*z}`}, {`y*z^2=1`}, 1) ; cut({`\exists z y*z^2=1`})) ; <(
        |        nil,
        |          hideR(1) ; QE
        |        )) ; existsL('Llast) ; existsR({`z`}, 1) ; dI(1)
        |      ),
        |      (((MR({`x < a`}, 1) ; <(
        |      nil,
        |        QE
        |      )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=-1`}, 1) ; cut({`\exists y y^2*(x-a)=-1`})) ; <(
        |      nil,
        |        hideR(1) ; QE
        |      )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1) ; QE
        |    ),
        |    (dC({`x>a`}, 1) ; <(
        |    dI(1),
        |      nil
        |    )) ; dG({`{y'=b/2*y}`}, {`y^2*(x-a)=1`}, 1) ; (cut({`\exists y y^2*(x-a)=1`}) ; <(
        |    nil,
        |      hideR(1) ; QE
        |    )) ; existsL('Llast) ; existsR({`y`}, 1) ; dI(1)
        |  )
        |)
        |),
        |  (boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |(boxAnd(1) ; andR(1)) ; <(
        |dW(1) ; QE,
        |  (boxAnd(1) ; andR(1)) ; <(
        |  nil,
        |    (boxAnd(1) ; andR(1)) ; <(
        |    nil,
        |      (boxAnd(1) ; andR(1)) ; <(
        |      dW(1) ; QE,
        |        nil
        |      )
        |    )
        |  )
        |)
        |) ; <(
        |    dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |dI(1),
        |dI(1)
        |),
        |    dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |dW(1) ; QE,
        |dI(1)
        |),
        |    master
        |    ),
        |  (boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |(boxAnd(1) ; andR(1)) ; <(
        |dW(1) ; QE,
        |  (boxAnd(1) ; andR(1)) ; <(
        |  nil,
        |    (boxAnd(1) ; andR(1)) ; <(
        |    nil,
        |      (boxAnd(1) ; andR(1)) ; <(
        |      dW(1) ; QE,
        |        nil
        |      )
        |    )
        |  )
        |)
        |) ; <(
        |    dC({`d=old(d)+vAsc*c`}, 1) ; <(
        |dC({`t>=old(t)-tau*HRmax*c`}, 1) ; <(
        |dI(1),
        |  dI(1)
        |),
        |dI(1)
        |),
        |    dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |dW(1) ; QE,
        |dI(1)
        |),
        |    orL(-31) ; <(
        |dC({`stoppedTimer=stopTime`}, 1) ; <(
        |dW(1) ; QE,
        |  dC({`stoppedTimer=old(stoppedTimer)`}, 1) ; <(
        |  dW(1) ; QE,
        |    dI(1)
        |  )
        |),
        |dC({`d0=old(d)&old(d)>stopDepth`}, 1) ; <(
        |dW(1) ; QE,
        |  dI(1)
        |)
        |)
        |    ),
        |  (boxAnd(1) ; andR(1)) ; <(
        |dI(1),
        |(boxAnd(1) ; andR(1)) ; <(
        |dW(1) ; QE,
        |  (boxAnd(1) ; andR(1)) ; <(
        |  nil,
        |    (boxAnd(1) ; andR(1)) ; <(
        |    nil,
        |      (boxAnd(1) ; andR(1)) ; <(
        |      dW(1) ; QE,
        |        nil
        |      )
        |    )
        |  )
        |)
        |) ; <(
        |    dC({`t>=old(t)-tau*HRmax*c&old(t)-tau*HRmax*c>=tApprox-tau*HRmax*c&tApprox>tau*HRmax*(-d/vAsc)+tau*HRmax*C+tau*HRmax*(stopTime-stoppedTimer)`}, 1) ; <(
        |dW(1) ; QE,
        |ODE(1)
        |),
        |    dC({`tApprox<=old(t)&old(t)-tau*HRmax*c<=t`}, 1) ; <(
        |dW(1) ; QE,
        |dI(1)
        |),
        |    master
        |    )
        |  )""".stripMargin.asTactic

    println(TacticStatistics.size(full))
//    println(tactic)
//    println(
//      proveBy(model, tactic).prettyString
//    )

//    proveBy(model, tactic) shouldBe 'proved
  })
}
