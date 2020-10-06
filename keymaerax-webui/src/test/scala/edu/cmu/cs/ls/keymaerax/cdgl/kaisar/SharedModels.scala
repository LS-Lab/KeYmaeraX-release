package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

// @TODO: Probably want top-level file format that can factor out definition of  ODE, declare rigids, detect wrong or undefined rigid names
// @TODO: Optimize loop checking case to fail early if loop body doesn't assert or note inductive statement as final step
// @TODO: ODE proof checking should include past cuts by default
// @TODO: Elaboration of abs, min, max should use intuitive auto-generated names, recover high-level messages if possible
// @TODO: Double-check abs, min, max elaboration to avoid needless branching
// @TODO: Use new contexts for all-around smart QE, which substitutes variables wherever possible (may need dependency analysis)
//   and which hides old irrelevant max, min, abs to reduce branching factor.
/** Kaisar models/proofs which are used in multiple test suites, e.g. Kaisar and ProofPlex. */
object SharedModels {
  val essentialsSafeCar1D: String =
    "?(xInit, vInit):(x:=0;v:=0); ?(acc, brk, tstep, separate):(A > 0 & B > 0 & T > 0 & x < d);" +
    "!inv:(v^2/(2*B) <= (d - x) & v >= 0) using xInit vInit brk separate by auto;" +
    "{{switch {" +
    "case accel: ((v + T*A)^2/(2*B) <= (d - (x + v*T + (A*T^2)/2))) =>" +
    "  ?accval:(a := A);" +
    "  !safeCtrl:((v + T*a)^2/(2*B) <= (d - (x + v*T + (a*T^2)/2))) using accel acc accval inv brk tstep ... by auto;" +
    "case brake: ((v + T*A)^2/(2*B)  + 1 >= (d - (x + v*T + (A*T^2)/2))) =>" +
    "  ?accval:(a := -B);" +
    "  ?fast:(v >= B*T);" +
    "  !safeCtrl:((v + T*a)^2/(2*B) <= (d - (x + v*T + (a*T^2)/2))) using brake acc accval brk inv tstep fast ... by auto;" +
    "}}" +
    "t:= 0;" +
    "{xSol: x' = v, vSol: v' = a, tSol: t' = 1 & ?dc: (t <= T & v>=0);};" +
    "!invStep: (v^2/(2*B) <= (d - x) & v>= 0) " +
    "using xSol vSol tSol safeCtrl accval inv dc acc brk tstep by auto;" +
    "}*" +
    "!safe:(x <= d & v >= 0) using inv brk  by auto;"

  // Language examples from Kaisar chapter of thesis. These are not meant to prove interesting theorems, but it's
  // important that the language presented in the thesis actually works in the implementation

  val assertOnePos: String =
  """?xValue:(x=1);
    |!xPositive:(x > 0);
    |""".stripMargin

  val assertBranchesNonzero: String =
    """{?xNeg:(x < 0); ++ ?xPos:(x > 0);}
      |!xNonzero:(x != 0);
      |""".stripMargin

  val switchLiterals: String =
    """switch {
      |  case xLow:(x <= 1) =>  !result:(x <= 2);
      |  case xHigh:(x >= 0) =>  !result:(x + 1 > 0);
      |}
      |""".stripMargin

  val noteAnd: String =
    """?left:(x < 0);
      |?right:(y < 0);
      |note both = andI(left, right);
      |!sign:(x + y <= (x + y)^2);
      |""".stripMargin

  val squareNonneg: String =
    """let square(x) = x*x;
      |!allSquaresNonneg:(square(y) >= 0);
      |""".stripMargin

  /** Carefully check speed. Should use simple prop proof, not slow QE */
  val propSkipsQE: String =
    """?a:(x = 0 -> y=1);
      |?b:(x = 0 &  ((z - x*w^2/(2 - w))^42 >= 6));
      |!c: ( y=1) using a b by prop;
      |""".stripMargin

  val annotatedAssign: String =
    """x := *;
      |y := x + 1;
      |?xFact:(z := y);
      |!compare:(z > x) using xFact ... by auto;
      |""".stripMargin

  val demonicLoop: String =
    """?yZero:(y := 0);
      |?xZero:(x := 0);
      |!inv: (x >= 0);
      |{x:=x+1;
      | !inductiveStep: (x >= 0);
      |}*
      |!geq:(x >= y) using inv yZero by auto;
      |""".stripMargin

  val straightODE: String =
    """x:= 0; y := 2;
      |{x' = 2, y' = -1 & ?dc:(y >= 0);};
      |!xFinal:(x <= 4) using dc x y by auto;
      |""".stripMargin

  val assertODE: String =
    """x:= 0; y := 2;
      |{x' = 2, y' = -1 & ?dc:(y >= 0); & !xEq:(x =  2*(2 - y))};
      |!xFinal:(x >= 0) using xEq dc by auto;
      |""".stripMargin

  val inductODE: String =
    """x := 0; y := 1;
      |{x' = y,  y' = -x  & !circle:(x^2 + y^2 = 1) by induction;};
      |""".stripMargin

  val inductODEBC: String =
    """x := 0; y := 1;
      |!bc:(x^2 + y^2 = 1);
      |{x' = y,  y' = -x  & !circle:(x^2 + y^2 = 1) by induction;};
      |""".stripMargin

  val durationODE: String =
    """?(T > 0); ?accel:(acc > 0);
      |x:= 0; v := 0; t := 0;
      |{t' = 1, x' = v, v' = acc
      |  & !vel:(v >= 0) using accel by induction;
      |  & !vSol: (v = t * acc) by solution;
      |  & !xSol:(x = acc*(t^2)/2) by induction;
      |  & ?dur:(t := T);};
      |!finalV:(x = acc*(t^2)/2) using dur xSol by auto;
      |""".stripMargin

  val ghostAssert: String =
    """?xSign: (x = 0 | x > 0);
      |/++
      |  !xZero: (x = 0 -> abs(x) = x);
      |  !xPos: (x > 0 -> abs(x) = x);
      |++/
      |!absEq:(abs(x) = x)  using orE(xSign, xZero, xPos) by hypothesis;
      |""".stripMargin

  val ghostAssign: String =
    """?xInit:(x > 0);
      |/++
      |    ?yInit:(y := x);
      |    !inv:(x >= y);
      | ++/
      |{x := x + 1;
      |/++ !(x >= y) using inv by auto; ++/
      |}*
      |!(x > 0) using inv yInit xInit by auto;
      |""".stripMargin

  val ghostODE: String =
    """x := 1;
      |/++
      |  y := (1/x)^(1/2);
      |  !inv:(x*y^2 = 1) by auto;
      |++/
      |{x' = -x, /++ y' = y * (1/2) ++/ & !inv:(x*y^2 = 1) by induction;}
      |!nonZero:(x > 0) using inv by auto;
      |""".stripMargin

  val inverseGhostODE: String =
    """z := 0;
      |{/-- x' = y, y' = -1 --/ ,  z'=1 & !zPos:(z >= 0) by solution;}
      |""".stripMargin


  val superfluousGhost: String =
    """x:=0; /-- y := 25; z := -10; --/
      |{x' = 3}
      |!(x >= 0);
      |""".stripMargin

  val labelInit: String =
    """init:
      |?(y = 0);
      |!bc:(y = 2*(x - x@init));
      |{ x := x + 1; y := y + 2;
      |  !step:(y = 2*(x - x@init));
      |}*
      |""".stripMargin

  val labelOld: String =
    """old:
      |{x' = 1 & !greater:(x >= x@old);}
      |""".stripMargin

  val unwindBlock: String =
    """x := 0;
      |init:
      |!(x < x@final);
      |x := x + 1;
      |x := x + 2;
      |final:
      |""".stripMargin

  val intoChoice: String =
    """x := 0;
      |y := x@mid;
      |init:
      |     {{ x := x + 3; mid: x := x * x;}
      |++ { x := 5;}}
      |""".stripMargin

  val outOfChoice: String =
    """{      y:= x@final; x := 2;
      | ++  x := 5;}
      |x := x + 1;
      |final:
      |""".stripMargin

  // @TODO: More obvious / better errors for match vs letfun
  val printSolution: String =
    """?(B > 0);
      |let ST() = v / B;
      |!stopTime:(v@ode(ST()) = 0);
      |let safe() <-> x@ode(ST()) <= d;
      |print(safe());
      |t:= 0;
      |{t' = 1, x' = v, v' = -B  & ?(v >= 0);};
      |ode(t):
      |""".stripMargin

  val basicReachAvoid: String =
    """?(eps > 0 &  x = 0 & T > 0);
      |while (x >= 0 & x + eps <= goal) {
      |  vel := (goal - (x + eps))/T;
      |  t := 0;
      |  {t' = 1, x' = vel & ?time:(t <= T);};
      |  /-- !safe:(x >= 0) using time ... by auto;  --/
      |  ?(t >= T/2);
      |  !live:(x >= 0 & x + eps <= goal) using time ... by auto;
      |}
      |""".stripMargin

  // @TODO: Check SB() vs SB parenthesis... hmm...
  val forwardHypothetical: String =
    """?init:(T > 0 & A > 0 & B > 0);
      |let SB() = v^2/(2*B);
      |let safe() <-> SB() <= (d-x) & v >= 0;
      |?initSafe:(safe());
      |{
      |  {acc := *; ?env:(-B <= acc & acc <= A & safe()@ode(T));}
      |   t:= 0;
      |  {tSol: t' = 1, xSol: x' = v, vSol: v' = acc & ?time:(t <= T); & ?vel:(v >= 0);};
      |ode(t):
      |   !step:(safe()) using env init initSafe time vel xSol vSol tSol by auto;
      |}*
      |""".stripMargin


  // @TODO: use less assumptions because I was just guessing at the end
  val sandboxExample: String =
    """?init:(T > 0 & A > 0 & B > 0);
      |let SB() = v^2/(2*B);
      |let safe() <-> SB() <= (d-x) & v >= 0;
      |?initSafe:(safe());
      |{
      |  accCand := *;
      |  let admiss() <-> -B <= accCand & accCand <= A;
      |  let env()    <->  safe()@ode(T, accCand);
      |  switch {
      |    case inEnv:(env()) =>
      |      ?theAcc:(acc := accCand);
      |      !predictSafe:(safe()@ode(T, acc)) using inEnv theAcc init by auto;
      |    case true =>
      |      ?theAcc:(acc := -B);
      |      ?fast:(v@ode(T, acc) >= 0);
      |      !predictSafe:(safe()@ode(T, acc)) using initSafe fast init theAcc by auto;
      |  }
      |  t:= 0;
      |  {tSol: t' = 1, xSol: x' = v, vSol: v' = acc & ?time:(0 <= t & t <= T); & ?vel:(v >= 0);};
      |ode(t, acc):
      |  !step:(safe()) using predictSafe init initSafe tSol xSol vSol time vel by auto;
      |}*
      |""".stripMargin

  val pldiModelSafe: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  {?(d >= eps*V); v:=*; ?(0<=v & v<=V); ++ v:=0;}
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps);};}
      |  !(inv());
      | }*
      | !(d >= 0);
      |""".stripMargin

  val pldiSandboxSafe: String =
    """
      |  let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | { v :=*;
      |   switch {
      |     case (inv()@mid) =>
      |     case (true) => v := 0;
      |   }
      |   t := 0;
      |   mid:
      |   {d' = -v, t' = 1 & ?(t <= eps);
      |    & !tSign:(t>=0);
      |    & !dBound:(d>=v*(eps-t));
      |   };
      |   !(inv());
      | }*
      |""".stripMargin

  /** @TODO:Discuss whether we should just cheat and use classical arithmetic.
    *       Original proof also should have been broken but it already contained a soundness issue: current reduction of abs/max is only
    *       sound on left where we can maybe assume ability to case-analyze, but not on right where case analysis must be proved not assumed.
    *       */
  val ijrrStaticSafetyRough: String =
    """pragma option "time=true";
      |pragma option "trace=true";
      |pragma option "debugArith=true";
      |let stopDist(v) = (v^2 / (2*b));
      |let accelComp(v) = ((A/b + 1) * (A/2 * T^2 + T*v));
      |let admissibleSeparation(v) = (stopDist(v) + accelComp(v));
      |let bounds() <-> A >= 0 & b > 0 & T > 0;
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let dist(xl, yl, xr, yr) = norm (xl - xr, yl - yr);
      |let initialState() <-> (v = 0 & dist(x,y,xo,yo) > 1 & norm(dx, dy) = 1);
      |let infdistGr(x1, y1, x2, y2, z) <-> (x1-x2 > z | x2 - x1 > z | y1 - y2 > z | y2 - y1 > z);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let goal() <-> (dist(x,y,xo,yo) > 0); /* @TODO: Need to expand more aggressively dist(x, y, xo, yo) > 0;*/
      |?(bnds, st):(bounds() & initialState());
      |        let d1() <-> (x-xo > stopDist(v));
      |        let d2() <-> (xo-x > stopDist(v));
      |        let d3() <-> (y-yo > stopDist(v));
      |        let d4() <-> (yo-y > stopDist(v));
      |switch {
      |  case xhi:(x-xo >= 0.25) =>
      |    !cs:(x-xo > stopDist(v)) using xhi bnds st by auto;
      |    note sd = orIL(cs, "d2() | d3() | d4()");
      |  case xlo:(x-xo <= 0.35) =>
      |    switch {
      |      case xohi:(xo-x >= 0.25) =>
      |        !cs:(xo-x > stopDist(v)) using xohi bnds st by auto;
      |        note sd = orIR("d1()", orIL(cs, " d3() | d4()"));
      |      case xolo:(xo-x <= 0.35) =>
      |        switch {
      |          case yhi:(y-yo >= 0.25) =>
      |            !cs:(y-yo > stopDist(v)) using yhi bnds st by auto;
      |            note sd = orIR("d1()", orIR("d2()", orIL(cs, "d4()")));
      |          case ylo:(y-yo <= 0.35) =>
      |            !cs:(yo-y > stopDist(v)) using ylo xolo xlo bnds st by auto;
      |            note sd = orIR("d1()", orIR("d2()", orIR("d3()", cs)));
      |        }
      |    }
      |}
      |!(vSign, dxyNorm, safeDist):(v >= 0 & norm(dx, dy) = 1 & infdistGr(x, y, xo, yo, stopDist(v))) using bnds st sd by auto;
      |{body:
      |  {
      |    {
      |      { ?aB:(a := -b); ?tZ:(t := 0);
      |        { x' = v * dx, y' = v * dy, v' = a,
      |          dx' = -w * dy, dy' = w * dx, w' = a/r,
      |          t' = 1 & ?dc:(t <= T & v >= 0);
      |         & !tSign:(t >= 0) using tZ by induction;
      |         & !dir:(norm(dx, dy) =  1) using dxyNorm by induction;
      |         & !vSol:(v = v@body - b*t) using aB tZ by induction;
      |         & !xBound:(-t * (v@body - b/2*t) <= x - x@body & x - x@body <= t * (v@body - b/2*t)) using bnds aB vSol dir tSign dc tZ by induction;
      |         & !yBound:(-t * (v@body - b/2*t) <= y - y@body & y - y@body <= t * (v@body - b/2*t)) using bnds aB vSol dir tSign dc tZ by induction;
      |        };
      |        let b1() <-> (x-xo > stopDist(v));
      |        let b2() <-> (xo-x > stopDist(v));
      |        let b3() <-> (y-yo > stopDist(v));
      |        let b4() <-> (yo-y > stopDist(v));
      |        switch (safeDist) {
      |          case far:((x - xo > stopDist(v))@body) =>
      |            !prog:(x-xo >= stopDist(v)) using far andEL(xBound) vSol dc bnds tSign by auto;
      |            note infInd = orIL(prog, "b2() | b3() | b4()");
      |          case far:((xo-x > stopDist(v))@body) =>
      |            !prog:(xo-x > stopDist(v)) using far andER(xBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIL(orIL(prog, "b3()"), "b4()"));
      |          case far:((y-yo > stopDist(v))@body) =>
      |            !prog:(y-yo > stopDist(v)) using far andEL(yBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIL(far, "b4()")));
      |         case far:((yo-y > stopDist(v))@body) =>
      |            !prog:(yo-y > stopDist(v)) using far andER(yBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIR("b3()", far)));
      |        }
      |        /*!infInd: (infdistGr(x, y, xo, yo, stopDist(v))) using safeDist xBound yBound vSol dc bnds tSign aB tZ by auto;  vSign */
      |      }
      |      ++
      |      { ?vZ:(v = 0); ?aZ:(a := 0); w := 0; ?tZ:(t := 0);
      |        { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
      |          dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
      |          t' = 1 & ?dc:(t <= T & v >= 0);
      |         & !tSign:(t >= 0) using tZ by induction;
      |         & !dir:(norm(dx, dy) = 1) using dxyNorm by induction;
      |         & !vSol:(v = v@body) using aZ by induction;
      |         & !xSol:(x = x@body) using vZ vSol dir tSign dc by induction;
      |         & !ySol:(y = y@body) using vZ vSol dir tSign dc by induction;
      |         };
      |        let b1() <-> (x-xo > stopDist(v));
      |        let b2() <-> (xo-x > stopDist(v));
      |        let b3() <-> (y-yo > stopDist(v));
      |        let b4() <-> (yo-y > stopDist(v));
      |        switch (safeDist) {
      |          case far:((x - xo > stopDist(v))@body) =>
      |            !prog:(x-xo > stopDist(v)) using far xSol vSol dc bnds tSign by auto;
      |            note infInd = orIL(prog, "b2() | b3() | b4()");
      |          case far:((xo-x > stopDist(v))@body) =>
      |            !prog:(xo-x > stopDist(v)) using far xSol vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIL(orIL(prog, "b3()"), "b4()"));
      |          case far:((y-yo > stopDist(v))@body) =>
      |            !prog:(y-yo > stopDist(v)) using far ySol vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIL(far, "b4()")));
      |          case far:((yo-y > stopDist(v))@body) =>
      |            !prog:(yo-y > stopDist(v)) using far ySol vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIR("b3()", far)));
      |        }
      |      }
      |        ++
      |        /* or choose a new safe curve */
      |      { ?aA:(a := A);
      |        w := *; ?(-W<=w & w<=W);
      |        r := *;
      |        xo := *; yo := *;
      |        monitor:
      |        ?(r!=0 & r*w = v);
      |        ?admiss:(infdistGr(x, y, xo, yo,  admissibleSeparation(v)));
      |        ?tZ:(t := 0);
      |        { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
      |          dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
      |          t' = 1 & ?dc:(t <= T & v >= 0);
      |         & !tSign:(t >= 0) using tZ aA by induction;
      |         & !dir:(norm(dx, dy) = 1) using dxyNorm by induction;
      |         & !vSol:(v = v@body + A*t) using aA tZ by induction;
      |         & !xBound:(-t * (v@body + A/2*t) <= x - x@body & x - x@body <= t * (v@body + A/2*t)) using bnds aA vSol dir tSign dc tZ by induction; /* got here after 20 mins -> reduced to 4 secs */
      |         & !yBound:(-t * (v@body + A/2*t) <= y - y@body & y - y@body <= t * (v@body + A/2*t)) using bnds aA vSol dir tSign dc tZ by induction;
      |        };
      |        let b1() <-> (x-xo > stopDist(v));
      |        let b2() <-> (xo-x > stopDist(v));
      |        let b3() <-> (y-yo > stopDist(v));
      |        let b4() <-> (yo-y > stopDist(v));
      |        switch (admiss) {
      |          case far:((x - xo > admissibleSeparation(v))@monitor) =>
      |            !prog:(x-xo > stopDist(v)) using far andEL(xBound) vSol dc bnds tSign by auto;
      |            note infInd = orIL(prog, "b2() | b3() | b4()");
      |          case far:((xo-x > admissibleSeparation(v))@monitor) =>
      |            !prog:(xo-x > stopDist(v)) using far andER(xBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIL(orIL(prog, "b3()"), "b4()"));
      |          case far:((y-yo > admissibleSeparation(v))@monitor) =>
      |            !prog:(y-yo > stopDist(v)) using far andEL(yBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIL(far, "b4()")));
      |          case far:((yo-y > admissibleSeparation(v))@monitor) =>
      |            !prog:(yo-y > stopDist(v)) using far andER(yBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIR("b3()", far)));
      |        }
      |      }
      |    }
      |  }
      |  !vInv: (v >= 0) using dc by auto;
      |  note indStep = andI(vInv, andI(dir, infInd));
      |}*
      |        switch (safeDist) {
      |          case far:((x - xo > stopDist(v))) =>
      |            !prog:(goal()) using far bnds  by auto;
      |          case far:((xo-x > stopDist(v))) =>
      |            !prog:(goal()) using far bnds  by auto;
      |          case far:((y-yo > stopDist(v))) =>
      |            !prog:(goal()) using far bnds  by auto;
      |          case far:((yo-y > stopDist(v))) =>
      |            !prog:(goal()) using far bnds  by auto;
      |        }
      |""".stripMargin


  /* @TODO: vInv had unsound lookup of SSA assignments  if using vSol vSign, check whether still broke after recent change */
  /* @TODO: Remove need for stutters in branching */
  val ijrrStaticSafetySimplified: String =
    """pragma option "time=true";
      |pragma option "trace=true";
      |pragma option "debugArith=true";
      |let stopDist(v) = (v^2 / (2*b));
      |let accelComp(v,a) = ((a/b + 1) * (a/2 * T^2 + T*v));
      |let admissibleSeparation(v,a) = (stopDist(v) + accelComp(v,a));
      |let bounds() <-> A >= 0 & b > 0 & T > 0;
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let dist(xl, yl, xr, yr) = norm (xl - xr, yl - yr);
      |let initialState() <-> (v = 0 & dist(x,y,xo,yo) > 1 & norm(dx, dy) = 1);
      |let infdistGr(x1, y1, x2, y2, z) <-> (x1-x2 > z | x2 - x1 > z | y1 - y2 > z | y2 - y1 > z);
      |/* Disjuncts of infdistGr predicate, useful in case analysis */
      |let goal() <-> (dist(x,y,xo,yo) > 0);
      |?(bnds, st):(bounds() & initialState());
      |/* Prove infdist > 0 in base case by case-analyzing x,y and using assumption on euclidean distance > 1*/
      |!splitX:(x-xo >= 0.25 | x-xo <= 0.35) by exhaustion;
      |!splitXO:(xo-x >= 0.25 | xo-x <= 0.35) by exhaustion;
      |!splitY:(y-yo >= 0.25 | y-yo <= 0.35) by exhaustion;
      |!sd:(infdistGr(x, y, xo, yo, stopDist(v))) using splitX splitXO splitY bnds st by auto;
      |/* Base case invariant */
      |!(vSign, dxyNorm, safeDist):(v >= 0 & norm(dx, dy) = 1 & infdistGr(x, y, xo, yo, stopDist(v))) using bnds st sd by auto;
      |{body:
      |  {
      |    {
      |     let monCond() <-> ((a = -b | (a = 0 & v = 0)) & infdistGr(x, y, xo, yo,  stopDist(v)) | a = A & infdistGr(x, y, xo, yo,  admissibleSeparation(v,A)));
      |      { {  {?aB:(a := -b);
      |           xo := xo; yo := yo;
      |           !admiss:(monCond()) using safeDist vSign bnds aB by auto; }
      |        ++ {?vZ:(v = 0); ?aZ:(a := 0); w := 0;
      |           xo := xo; yo := yo;
      |           !admiss:(monCond()) using safeDist vSign bnds aZ vZ by auto; }
      |        ++ {?aA:(a := A); w := *; ?(-W<=w & w<=W);
      |            r := *;
      |            xo := *; yo := *;
      |            ?(r!=0 & r*w = v);
      |            ?admiss:(monCond());}
      |        }
      |  monitor:
      |        ?tZ:(t := 0);
      |        { x' = v * dx, y' = v * dy, v' = a,
      |          dx' = -w * dy, dy' = w * dx, w' = a/r,
      |          t' = 1 & ?dom:(t <= T & v >= 0);
      |         & !tSign:(t >= 0) using tZ by induction;
      |         & !dir:(norm(dx, dy) =  1) using dxyNorm by induction;
      |         & !vSol:(v = v@body + a*t) using tZ by induction;
      |         & !xBound:(-t * (v@body + a/2*t) <= x - x@body & x - x@body <= t * (v@body + a/2*t)) using bnds vSol dir tSign dom tZ by induction;
      |         & !yBound:(-t * (v@body + a/2*t) <= y - y@body & y - y@body <= t * (v@body + a/2*t)) using bnds vSol dir tSign dom tZ by induction;
      |        };
      |        !infInd:(infdistGr(x,y,xo,yo, stopDist(v))) using admiss xBound yBound vSol dom bnds tSign by auto;
      |      }
      |    }
      |  }
      |  !vInv: (v >= 0) using dom by auto;
      |  note indStep = andI(vInv, andI(dir, infInd));
      |}*
      |!(goal()) using safeDist bnds by auto;
      |""".stripMargin

  val ijrrVelocityPassiveSafety: String =
    """
      |let stopDist(v) = (0);
      |let accelComp(v) = (ep()*(v+V()));
      |let admissibleSeparation(v) = (stopDist(v) + accelComp(v)).
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> ( ep() > 0  & V() >= 0);
      |let initialState() <-> ( v = 0 & dist(x,y,xo,yo) > 0 & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 & (v>0 -> infdist(x, y, xo, yo) > stopDist(v)));
      |?(assumptions());
      |!(loopinv());
      |    {body:
      |      {
      |        {
      |          vxo := *; vyo := *;
      |          ?vxo^2+vyo^2<=V^2;
      |        }
      |        {
      |          { v := 0; w := 0; }
      |          ++
      |          { v := *; ?0<=v;
      |            w := *; ?-W<=w & w<=W;
      |            r := *;
      |            xo := *; yo := *;      |
      |            ?r!=0 & r*w = v;
      |            ?(infdist(x, y, xo, yo) > admissibleSeparation(v));
      |          }
      |        };
      |    	  t := 0;
      |      }
      |
      |      /* dynamics */
      |      {
      |      { x' = v * dx, y' = v * dy,                /* move */
      |        dx' = -w * dy, dy' = w * dx,             /* follow curve */
      |        xo' = vxo, yo' = vyo,                    /* obstacle moves */
      |        ?(t' = 1 & t <= ep & v >= 0);
      |        !tSign:(t>=0);
      |        !xBound:(-t*v <= xo - xo@loop & xo - xo@loop <= t*v);
      |        !yBound:(-t*v <= yo - yo@loop & yo - yo@loop <= t*v);
      |      };
      |      }
      |    !(loopinv());
      |    }*
      | !(v>0 -> dist(x,y,xo,yo) > 0);
      |""".stripMargin

  val ijrrPassiveSafety: String =
    """
      |let stopDist(v) = (v^2 / (2*b()) + V()*v/b());
      |let accelComp(v) = ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V)));
      |let admissibleSeparation(v) = (stopDist(v) + accelComp(v));
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> (A() >= 0 & b() > 0 & ep() > 0  & V() >= 0);
      |let initialState() <-> (v = 0 & dist(x,y,xo,yo) > 0 & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 & (v>0 -> infdist(x, y, xo, yo) > stopDist(v)));
      |?(assumptions());
      |!(loopinv());
      |    {loop:
      |      {vxo := *; vyo := *; ?(norm(vxo, vyo) <= V^2);}
      |      {
      |        { a := -b; }
               ++
      |        { ?v = 0; a := 0; w := 0; }
      |        ++
      |        {
      |          a := A;
      |          w := *; ?-W<=w & w<=W;
      |          r := *;
      |          xo := *; yo := *;      |
      |          ?r!=0 & r*w = v;
      |          ?(infdist(x, y, xo, yo) > admissibleSeparation(v));
      |          }
      |        };
      |    	  t := 0;
      |      }
      |      {
      |      { x' = v * dx, y' = v * dy, v' = a,
      |        dx' = -w * dy, dy' = w * dx, w' = a/r,
      |        ?(t' = 1 & t <= ep & v >= 0);
      |        !tSign:(t>=0);
      |        !dir:(norm(dx, dy) = 1);
      |        !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V());
      |        !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V());
      |        !vSol:(v = v@loop + a*t);
      |        !xBound:(-t*(v@loop - a/2*t) <= xo - xo@loop & xo - xo@loop <= t*(v@loop - a/2*t));
      |        !yBound:(-t*(v@loop - a/2*t) <= yo - yo@loop & yo - yo@loop <= t*(v@loop - a/2*t));
      |      };
      |      }
      |    !(loopinv());
      |    }*
      | !(dist(x,y,xo,yo) > 0);
      |""".stripMargin

  val ijrrPassiveFriendlySafety: String =
    """
      |let friendlyMargin(v) = (v^2/(2*bo()) + tau()*v);
      |let stopDist(v) = (v^2 / (2*b()) + V()*v/b());
      |let accelComp(v) = ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V)));
      |let admissibleSeparation(v) = (stopDist(v) + friendlyMargin() + accelComp(v));
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> (A() >= 0 & b() > 0 & ep() > 0  & V() >= 0 & tau() >= 0 & bo() > 0);
      |let initialState() <-> (v = 0 & infdist(x,y,xo,yo) >= friendlyMargin(V()) & norm(vxo,vyo) <= V() & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 & (v>0 -> infdist(x, y, xo, yo) > stopDist(v) + friendlyMargin(V())));
      |?(assumptions());
      |!(loopinv());
      |    {loop:
      |      {vxo := *; vyo := *; ?(norm(vxo, vyo) <= V);}
      |      {
      |        { a := -b; }
               ++
      |        { ?v = 0; a := 0; w := 0; }
      |        ++
      |        {
      |          a := A;
      |          w := *; ?-W<=w & w<=W;
      |          r := *;
      |          xo := *; yo := *;
      |          ?r!=0 & r*w = v;
      |          ?(infdist(x, y, xo, yo) > admissibleSeparation(v));
      |          }
      |        };
      |    	  t := 0;
      |      }
      |      {
      |      { x' = v * dx, y' = v * dy, v' = a,
      |        dx' = -w * dy, dy' = w * dx, w' = a/r,
      |        xo' = vxo, yo' = vyo,
      |        ?(t' = 1 & t <= ep() & v >= 0);
      |        !tSign:(t>=0);
      |        !dir:(norm(dx, dy) = 1);
      |        !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V());
      |        !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V());
      |        !vSol:(v = v@loop + a*t);
      |        !xBound:(-t*(v@loop - a/2*t) <= xo - xo@loop & xo - xo@loop <= t*(v@loop - a/2*t));
      |        !yBound:(-t*(v@loop - a/2*t) <= yo - yo@loop & yo - yo@loop <= t*(v@loop - a/2*t));
      |      };
      |      }
      |    !(loopinv());
      |    }*
      | !(v>0 -> dist(x,y,xo,yo) > friendlyMargin(V()));
      | ?(0 <= vo & vo = norm(vxo, vyo) & dxo*vo = vxo & dyo*vo=vyo);
      | ?(dist(x,y,xo,yo) > friendlyMargin(V()));
      | ao := todo(); !(-bo() <= ao & vo + ao*ep() <= V());
      | t := 0;
      | {xo'=vo*dxo, yo'=vo*dyo, vo'=ao, t'=1,
      |    ?(vo>= 0 & t<= ep());
      |  & ?(t := todo());
      | };
      | !(dist(x,y,xo,yo) > 0 & vo = 0);
      |""".stripMargin


  val ijrrPassiveOrientationSafety: String =
    """
      |let stopDist(v) = (v^2 / (2*b()));
      |let stopMargin(v) = stopDist(v) + V()*v/b();
      |let accelComp(v) = ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*v));
      |let accelMargin(v) = (accelComp(v) + (A()/b() + 1) * (ep()*V()));
      |let admissibleSeparation(v) = (stopMargin(v) + accelMargin(v));
      |let admissibleTurnLength(v) = (stopDist(v) + accelComp(v));
      |let isVisible(x) <-> x > 0;
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> (A() >= 0 & b() > 0 & ep() > 0  & V() >= 0 & Gamma() > 0);
      |let initialState() <-> (v = 0 & beta = 0 & r != 0 & dist(x,y,xo,yo) > 0 & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 & r != 0 &
      |    (v>0 -> infdist(x, y, xo, yo) > stopMargin(v)
      |  |  !isVisible(visDeg) & abs(beta) + stopDist(v)/abs(r) < Gamma()));
      |?(assumptions());
      |!(loopinv());
      |    {loop:
      |      {vxo := *; vyo := *; ?(norm(vxo, vyo) <= V);}
      |      {
      |        { a := -b(); }
               ++
      |        { ?v = 0; a := 0; w := 0; }
      |        ++
      |        {
      |          a := A();
      |          beta := 0;
      |          r := *; ?r!=0;
      |          xo := *; yo := *; visDeg := *;
      |          ?(isVisible(visDeg) -> infdist(x,y,xo,yo) > admissibleSeparation(v));
      |          ?(admissibleTurnLength(v) < Gamma()*abs(r);
      |          }
      |        };
      |       w := *; ?w*r = v;
      |      }
      |      {
      |      t := 0;
      |      { x' = v * dx, y' = v * dy, v' = a,
      |        dx' = -w * dy, dy' = w * dx, w' = a/r,
      |        beta' = w,
      |        xo' = vxo, yo' = vyo, t' = 1 &
      |        ?(t <= ep() & v >= 0);
      |        !tSign:(t>=0);
      |        !dir:(norm(dx, dy) = 1);
      |        !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V());
      |        !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V());
      |        !vSol:(v = v@loop + a*t);
      |        !betaSol:(beta = beta@loop + t/r*(v + a/2*t));
      |        !xBound:(-t*(v@loop - a/2*t) <= xo - xo@loop & xo - xo@loop <= t*(v@loop - a/2*t));
      |        !yBound:(-t*(v@loop - a/2*t) <= yo - yo@loop & yo - yo@loop <= t*(v@loop - a/2*t));
      |      };
      |      }
      |    !(loopinv());
      |    }*
      | !(v > 0 -> ((x - xo)^2 + (y - yo)^2 > 0 | (!isVisible(visDeg) & (abs(beta) < Gamma()))));
      |""".stripMargin

  // Theorem 5
  val ijrrPassiveSafetyActualAcceleration: String =
    """
      |let stopDist(v) = (v^2 / (2*b()));
      |let stopMargin(v) = stopDist(v) + V()*v/b();
      |let accelComp(v) = ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*v));
      |let accelMargin(v) = (accelComp(v) + (A()/b() + 1) * (ep()*V()));
      |let admissibleSeparation(v) = (stopMargin(v) + accelMargin(v));
      |let admissibleTurnLength(v) = (stopDist(v) + accelComp(v));
      |let isVisible(x) <-> x > 0;
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> (A() >= 0 & b() > 0 & ep() > 0  & V() >= 0 & Gamma() > 0);
      |let initialState() <-> (v = 0 & beta = 0 & r != 0 & dist(x,y,xo,yo) > 0 & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 & r != 0 &
      |    (v>0 -> infdist(x, y, xo, yo) > stopMargin(v)
      |  |  !isVisible(visDeg) & abs(beta) + stopDist(v)/abs(r) < Gamma()));
      |?(assumptions());
      |!(loopinv());
      |    {loop:
      |      {vxo := *; vyo := *; ?(norm(vxo, vyo) <= V);}
      |      {
      |        { a := -b(); }
               ++
      |        { ?v = 0; a := 0; w := 0; }
      |        ++
      |        {
      |          a := *; ?(-b() <= a & a <= A());
      |          w := *; ?-W <= w & w <= W;
      |          r := *; ?(r!=0 & r*w = v);
      |          xo := *; yo := *;
      |          ?(((v+a*ep>=0) & infdist(x,y,xo,yo) > admissibleSeparationG(v,a))
      |           | (infdist(x,y,xo,yo) &infdist(x,y,xo,yo) > admissibleSeparationL(v,a)));
      |        }
      |      }
      |      {
      |      t := 0;
      |      { x' = v * dx, y' = v * dy, v' = a,
      |        dx' = -w * dy, dy' = w * dx, w' = a/r,
      |        xo' = vxo, yo' = vyo, t' = 1 &
      |        ?(t <= ep() & v >= 0);
      |        !tSign:(t>=0);
      |        !dir:(norm(dx, dy) = 1);
      |        !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V());
      |        !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V());
      |        !vSol:(v = v@loop + a*t);
      |        !xBound:(-t*(v@loop - a/2*t) <= xo - xo@loop & xo - xo@loop <= t*(v@loop - a/2*t));
      |        !yBound:(-t*(v@loop - a/2*t) <= yo - yo@loop & yo - yo@loop <= t*(v@loop - a/2*t));
      |      };
      |      }
      |    !(loopinv());
      |    }*
      | !(v > 0 -> (dist(x,y,xo,yo) > 0));
      |""".stripMargin

  // Theorem 6
  val ijrrPassiveSafetyLocationUncertainty: String =
    """
      |let stopDist(v) = (v^2 / (2*b())+ V()*v/b());
      |let stopMargin(v) = stopDist(v) ;
      |let accelComp(v) = ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V())) + Dp());
      |let accelMargin(v) = (accelComp(v) + (A()/b() + 1) * (ep()*V()));
      |let admissibleSeparation(v) = (stopDist(v) + accelComp(v));
      |let isVisible(x) <-> x > 0;
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> (A() >= 0 & b() > 0 & ep() > 0  & V() >= 0 & Dp() >= 0);
      |let initialState() <-> (v = 0  & dist(x,y,xo,yo) > 0 & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 & r != 0 &
      |    (v>0 -> infdist(x, y, xo, yo) > stopMargin(v)
      |  |  !isVisible(visDeg) & abs(beta) + stopDist(v)/abs(r) < Gamma()));
      |?(assumptions());
      |!(loopinv());
      |{
      |      {
      |        {
      |          mx := *; my := *;
      |          ?(mx-x)^2+(my-y)^2 <= Dp()^2;
      |        }
      |        {
      |          vxo := *; vyo := *;
      |          ?vxo^2+vyo^2<=V^2;
      |        }
      |        {
      |          { a := -b; }
      |          ++
      |          { ?v = 0; a := 0; w := 0; }
      |      	  ++
      |          /* or choose a new safe curve */
      |          { a := A;
      |            w := *; ?-W<=w & w<=W;       /* choose steering */
      |            r := *;
      |            xo := *; yo := *;            /* measure closest obstacle on the curve */
      |
      |            /* admissible curve */
      |            ?r!=0 & r*w = v;
      |
      |            /* use that curve, if it is a safe one (admissible velocities) */
      |            ? abs(mx-xo) > admissibleSeparation(v)
      |            | abs(my-yo) > admissibleSeparation(v);
      |          }
      |        };
      |    	  t := 0;
      |      }
      |
      |      /* dynamics */
      |      { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
      |        dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
      |        xo' = vxo, yo' = vyo,                    /* obstacle moves */
      |        t' = 1 & t <= ep & v >= 0
      |       & !tSign:(t>=0);
      |       & !dir:(norm(dx, dy) = 1);
      |       & !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V());
      |       & !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V());
      |       & !vBound:(v <= v@loop - a**t);
      |       & !xBound:(-t * (v - a/2*t) <= x - x@loop & x - x@loop <= t * (v - a/2*t));
      |       & !yBound:-(t * (v - a/2*t) <= y - y@loop & y - y@loop <= t * (v - a/2*t));
      |      }
      |    !(loopinv());
      |    }*
      |  !(v>0 -> dist(x,y,xo,yo) > 0);
      |""".stripMargin

  val ijrrPassiveSafetyActuatorDisturbance: String =
    """let stopDist(v) = (v^2 / (2*(b()*Da()))+ V()*v/(b()*Da()));
      |let accelComp(v) = ((A()/(b()*Da()) + 1) * (A()/2 * ep()^2 + ep()*(v+V())));
      |let admissibleSeparation(v) = (stopDist(v) + accelComp(v));
      |let isVisible(x) <-> x > 0;
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> (A() >= 0 & b() > 0 & ep() > 0  & V() >= 0 & 0 < Da() & Da() <= 1);
      |let initialState() <-> (v = 0  & dist(x,y,xo,yo) > 0 & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 &
      |    (v>0 -> infdist(x, y, xo, yo) > stopDist(v));
      | ?(assumptions());
      | !(loopinv());
      | {loop:
      |      {
      |        {
      |          vxo := *; vyo := *;
      |          ?vxo^2+vyo^2<=V^2;
      |        }
      |        {
      |          { a := -b; }
      |          ++
      |          { ?v = 0; a := 0; w := 0; }
      |      	  ++
      |          { a := A;
      |            w := *; ?-W<=w & w<=W;       /* choose steering */
      |            r := *;
      |            xo := *; yo := *;            /* measure closest obstacle on the curve */
      |
      |            ?r!=0 & r*w = v;
      |
      |            ? abs(x-xo) > admissibleSeparation(v)
      |            | abs(y-yo) > admissibleSeparation(v);
      |          }
      |        };
      |        {
      |          da := *; ?(Da<=da & da<=1); acc := da*a;
      |        };
      |    	  t := 0;
      |      }
      |      { x' = v * dx, y' = v * dy, v' = acc,      /* accelerate/decelerate and move */
      |        dx' = -w * dy, dy' = w * dx, w' = acc/r, /* follow curve */
      |        xo' = vxo, yo' = vyo,                    /* obstacle moves */
      |        t' = 1 & ?(t <= ep & v >= 0);
      |       & !tSign:(t>=0);
      |       & !dir:(norm(dx, dy) = 1);
      |       & !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V());
      |       & !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V());
      |       & !vBound:(v <= v@loop - (b()*Da())*t);
      |       & !xBound:(-t * (v@loop - (b()*Da())/2*t) <= x - x@loop & x - x@loop <= t * (v@loop - (b()*Da())/2*t));
      |       & !yBound:-(t * (v@loop - (b()*Da())/2*t) <= y - y@loop & y - y@loop <= t * (v@loop - (b()*Da())/2*t));
      |      }
      |    !(loopinv());
      |    }
      | !(v>0 -> dist(x,y,xo,yo) > 0);
      |""".stripMargin

  val ijrrPassiveSafetyVelocityUncertainty: String =
    """let stopDist(v) = (v^2 / (2*b()) + V()*v/b());
      |let accelComp(v) = ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V())));
      |let admissibleSeparation(v) = (stopDist(v) + accelComp(v));
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> (A() >= 0 & b() > 0 & ep() > 0  & V() >= 0 & Dv() > 0);
      |let initialState() <-> (v = 0  & dist(x,y,xo,yo) > 0 & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 & (v>0 -> infdist(x, y, xo, yo) > stopDist(v));
      |   ?(assumptions());
      |   !(loopinv());
      |    {
      |      {
      |        {
      |          mv := *; ?0<=mv & v-Dv()<=mv & mv<=v+Dv();
      |        }
      |        {
      |          vxo := *; vyo := *;
      |          ?vxo^2+vyo^2<=V^2;
      |        }
      |        {
      |          { a := -b; }
      |          ++
      |          { ?v = 0; a := 0; w := 0; }
      |      	  ++
      |          { a := A;
      |            w := *; ?-W<=w & w<=W;
      |            r := *;
      |            xo := *; yo := *;
      |
      |            ?r!=0 & r*w = v;
      |
      |            ? abs(x-xo) > admissibleSeparation(mv+Dv())
      |            | abs(y-yo) > admissibleSeparation(mv+Dv());
      |          }
      |        };
      |    	  t := 0;
      |      }
      |
      |      { x' = v * dx, y' = v * dy, v' = a,
      |        dx' = -w * dy, dy' = w * dx, w' = a/r,
      |        xo' = vxo, yo' = vyo,
      |        t' = 1 & ?(t <= ep & v >= 0);
      |       & !tSign:(t>=0);
      |       & !dir:(norm(dx, dy) = 1);
      |       & !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V());
      |       & !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V());
      |       & !vBound:(v <= v@loop - a*t);
      |       & !xBound:(-t * (v@loop - a/2*t) <= x - x@loop & x - x@loop <= t * (v@loop - a/2*t));
      |       & !yBound:-(t * (v@loop - a/2*t) <= y - y@loop & y - y@loop <= t * (v@loop - a/2*t));
      |      }
      |    !(loopinv());
      |    }*
      |    !(v>0 -> dist(x,y,xo,yo) > 0);
      |""".stripMargin

  // theorem 9
  val ijrrPassiveAsync: String =
    """
      |let stopDist(v) = (v^2 / (2*b()) + V()*v/b());
      |let accelComp(v) = ((A()/b() + 1) * (A()/2 * ep()^2 + ep()*(v+V())));
      |let admissibleSeparation(v) = (stopDist(v) + accelComp(v));
      |let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let bounds() <-> (A() >= 0 & b() > 0 & ep() > 0  & V() >= 0);
      |let initialState() <-> (v = 0  & dist(x,y,xo,yo) > 0 & norm(dx, dy) = 1);
      |let assumptions() <-> (bounds() & initialState());
      |let loopinv() <-> (v >= 0 & norm(dx, dy) = 1 & (v>0 -> infdist(x, y, xo, yo) > stopDist(v));
      |?(assumptions());
      |!(loopinv());
      |
      |{outer:
      |      {
      |        {
      |          { a := -b; }
      |          ++
      |          { ?v = 0; a := 0; w := 0; }
      |      	  ++
      |          { a := A;
      |            w := *; ?-W<=w & w<=W;       /* choose steering */
      |            r := *;
      |            xo := *; yo := *;            /* measure closest obstacle on the curve */
      |
      |            ?r!=0 & r*w = v;
      |
      |            ? abs(x-xo) > admissibleSeparation(v)
      |            | abs(y-yo) > admissibleSeparation(v);
      |          }
      |        };
      |    	  t := 0;
      |      }
      |      inner:
      |      let innerloopinv(xoo, yoo) <-> 0<=t & t<=ep()
      |        & v >= 0
      |        & norm(dx, dy) = 1
      |        & -t*V() <= xo - xo@inner & xo - xo@inner <= t*V()
      |        & -t*V() <= yo - yo@inner & yo - yo@inner <= t*V()
      |        & -t * (v - a/2*t) <= x - x@inner & x - x@inner) <= t * (v - a/2*t)
      |        & -t * (v - a/2*t) <= y - y@inner & y - y@inner <= t * (v - a/2*t)
      |      !(innerloopinv());
      |      {body:
      |        /* obstacle control */
      |        {
      |          vxo := *; vyo := *;
      |          ?vxo^2+vyo^2<=V^2;
      |        };
      |        /* dynamics */
      |        { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
      |          dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
      |          xo' = vxo, yo' = vyo,                    /* obstacle moves */
      |          t' = 1 & ?(t <= ep & v >= 0);
      |        & !(t>=t@body);
      |        & !(norm(dx, dy) = 1);
      |        & !(-(t-t@body)*V() <= xo - xo@body & xo - xo@body <= (t-t@body)*V());
      |        & !(-(t-t@body)*V() <= yo - yo@body & yo - yo@body <= (t-t@body)*V());
      |        & !(v = v@body + a*(t-t@body));
      |        & !(-(t-t@body) * (v - a/2*(t-t@body)) <= x - x@body & x - x@body <= (t-t@body) * (v - a/2*(t-t@body)));
      |        & !(-(t-t@body) * (v - a/2*(t-t@body)) <= y - y@body & y - y@body <= (t-t@body) * (v - a/2*(t-t@body)));
      |        }
      |       !(innerloopinv());
      |      }*
      |      !(loopinv());
      |    }*
      | !(v>0 -> dist(x,y,xo,yo) > 0);
      |""".stripMargin

  // thm 11
  val ijrrReachWaypoint: String =
    """
      |
      |	let waypointStartDist(xg) = ( xg-GDelta() );
      |	let waypointEndDist(xg)   = ( xg+GDelta() );
      | let minV() = ( A()*ep() );
      |	let stopDist(v) = ( v^2/(2*b()) );
      |	let accComp(v)  = ( (A()/b() + 1)*(A()/2*ep()^2 + ep()*v) );
      |	let bounds() <-> (
      |      A() > 0
      |    & b() > 0
      |    & ep() > 0
      |    & Vmax() >= 2*A()*ep()
      |    & GDelta() > Vmax()*ep() + Vmax()^2/(2*b())
      |  );
      | let initialState() <-> (
      |    vr = 0
      |    & xr < waypointStartDist(xg)
      |  ).
      | let assumptions() <-> (bounds() & initialState());
      |	let loopinv() <-> (
      |	  0 <= vr & vr <= Vmax & xr + stopDist(vr) < waypointEndDist(xg)
      |	);
      |  ?(assumptions());
      |  !(loopinv());
      |	  { { { {
      |      ar := -b();
      |   ++ ?vr = 0; ar := 0;
      |   ++ ?xr + stopDist(vr) + accComp(vr) < waypointEndDist(xg) & vr+A()*ep()<=Vmax(); ar := A();
      |   ++ ?xr <= waypointStartDist(xg) & vr <= Vmax(); ar := *; ?-b() <= ar & ar <= (Vmax()-vr)/ep() & ar <= A();
      |	} t:=0; }
      | {xr' = vr, vr' = ar, t' = 1 & t <= ep() & vr >= 0};
      | !(loopinv());
      | }*
      | !(xr < waypointEndDist(xg));
      | !(loopinv());
      |	{ { { {
      |      ar := -b();
      |   ++ ?vr = 0; ar := 0;
      |   ++ ?xr + stopDist(vr) + accComp(vr) < waypointEndDist(xg) & vr+A()*ep()<=Vmax(); ar := A();
      |   ++ ?xr <= waypointStartDist(xg) & vr <= Vmax(); ar := *; ?-b() <= ar & ar <= (Vmax()-vr)/ep() & ar <= A();
      |	} t:=0; } xr' = vr, vr' = ar, t' = 1 & t <= ep() & vr >= 0};
      | !(loopinv());
      | }*
      | !(waypointStartDist(xg) < xr);
      |""".stripMargin

  val ijrrModels: List[String] = List(ijrrPassiveFriendlySafety, ijrrPassiveSafety, ijrrStaticSafetyRough, ijrrStaticSafetySimplified, ijrrVelocityPassiveSafety)
  val robixDynamicWindowPassive: String =
    """let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let goal() <-> vr = 0 | dist(prx, pry, pox, poy) > vr^2/(2*b) + V*(vr/b)
      |let pre() <-> goal() & dist(prx,pry,pcx,pcy) > 0 ^ norm(drx, dry) = 1
      |let curve() <-> dist(prx, pry, pcx, pcy) > 0 & wr*dist(prx, pry, pcx, pcy) = vr;
      |let safe() <-> infdist(prx, pry, pcx, pcy) > vr^2 /(2*b) + ((A/b) + 1)*(T^2*A/2 + T*vr) + V*(T + (vr + A*T)/b);
      |?(pre());
      |{  {vox := *; voy := *; ?(norm(vx, vy) <= V);
      |  {  {ar := -b;}
      |  ++ {?vr = 0; ar := 0; wr := 0;}
      |  ++ {ar := *; ?-b <= ar & ar <= A;
      |      wr := *; ?-W <= wr & wr <= W;
      |      pcx := *; pcy := *; drx := *; dry := *;
      |      pox := *; poy := *; ?curve() & safe();}}
      |  }
      | t:=0;
      | {prx' = vr*drx, pxy' = vr*dry, drx' = -wr*dry, dry' = wr*drx, pox' = vox, poy' = voy, vr' - ar, 
      |  vwr' = ar/dist(prx, pry, pcx, pcy, t' = 1
      |  & ?vr >= 0 & t <= T}
      |}*
      |!(goal());
      |""".stripMargin

  // @TODO: Basically has to be wrong. Check kyx artifact
  val robixDynamicWindowFriendly: String =
    """let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let goal() <-> vr = 0 | dist(prx, pry, pox, poy) > vr^2/(2*b) + V*(vr/b)
      |let pre() <-> goal() & dist(prx,pry,pcx,pcy) > 0 ^ norm(drx, dry) = 1
      |let curve() <-> dist(prx, pry, pcx, pcy) > 0 & wr*dist(prx, pry, pcx, pcy) = vr;
      |let safe() <-> infdist(prx, pry, pcx, pcy) > vr^2 /(2*b) + V^2/(2*b) + tau*V + ((A/b) + 1)*(T^2*A/2 + T*vr) + V*(T + (vr + A*T)/b);
      |?(pre());
      |{ {vox := *; voy := *; ?(norm(vx, vy) <= V);
      |  {  {ar := -b;}
      |  ++ {?vr = 0; ar := 0; wr := 0;}
      |  ++ {ar := *; ?-b <= ar & ar <= A;
      |      wr := *; ?-W <= wr & wr <= W;
      |      pcx := *; pcy := *; drx := *; dry := *;
      |      pox := *; poy := *; ?curve() & safe();}}
      |  }
      | t:=0;
      | {prx' = vr*drx, pxy' = vr*dry, drx' = -wr*dry, dry' = wr*drx, pox' = vox, poy' = voy, vr' - ar,
      |  vwr' = ar/dist(prx, pry, pcx, pcy, t' = 1
      |  & ?(vr >= 0 & t <= T);}
      |}*
      |!(goal());
      |""".stripMargin

  // @TODO: Refine to actual magic, also rpobably quite wrong
  val robixRefinedObstacle: String =
    """let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let goal() <-> vr = 0 | dist(prx, pry, pox, poy) > vr^2/(2*b) + V*(vr/b)
      |let pre() <-> goal() & dist(prx,pry,pcx,pcy) > 0 ^ norm(drx, dry) = 1
      |let curve() <-> dist(prx, pry, pcx, pcy) > 0 & wr*dist(prx, pry, pcx, pcy) = vr;
      |let safe() <-> infdist(prx, pry, pcx, pcy) > vr^2 /(2*b) + V^2/(2*b) + tau*V + ((A/b) + 1)*(T^2*A/2 + T*vr) + V*(T + (vr + A*T)/b);
      |?(vr = 0 & (dist(prx, pry, pox, poy) > V^2/(2*bo) + tau*V) & 0 <= vo & vo <= V);
      |{
      | {dox := *; doy := *; ?norm(dox, doy) = 1;
      |  aox := *; aoy := *; ?vo + ao*To <= V;}
      | t:= 0;
      | {pox' = vo*dox, poy' = vo*doy, vo' = ao, t' = 1 & t <= To & ?(vo > = 0);}
      |}*
      |!(dist(prx, pry, pox, poy) > 0 & vo = 0);
      |""".stripMargin

  val robixSensorUncertainty: String =
    """let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let goal() <-> vr = 0 | dist(prx, pry, pox, poy) > vr^2/(2*b) + V*(vr/b)
      |let pre() <-> goal() & dist(prx,pry,pcx,pcy) > 0 ^ norm(drx, dry) = 1
      |let perp(x, y) = todo();
      |let curve() <-> dist(ptrx, ptry, pcx, pcy) > 0 & wr*dist(ptrx, ptry, pcx, pcy) = vr & dr = perp(ptrx - pcx, ptry - pcy)/dist(ptrx, ptry, pcx, pcy);
      |let safe() <-> infdist(ptrx, ptry, pox, poy) > vr^2 /(2*b)  + ((A/b) + 1)*(T^2*A/2 + T*vr) + V*(T + (vr + A*T)/b) + Up;
      |{{ptrx := *; ptry := *; ?(dist(ptrx, ptry, prx, pry) <= Up);}
      | {vox := *; voy := *; ?(norm(vx, vy) <= V);
      |  {  {ar := -b;}
      |  ++ {?vr = 0; ar := 0; wr := 0;}
      |  ++ {ar := *; ?-b <= ar & ar <= A;
      |      wr := *; ?-W <= wr & wr <= W;
      |      pcx := *; pcy := *; drx := *; dry := *;
      |      pox := *; poy := *; ?curve() & safe();}}
      |  }
      | t:=0;
      | {prx' = vr*drx, pxy' = vr*dry, drx' = -wr*dry, dry' = wr*drx, pox' = vox, poy' = voy, vr' - ar,
      |  vwr' = ar/dist(prx, pry, pcx, pcy, t' = 1
      |  & ?(vr >= 0 & t <= T);}
      |}*
      |
      |""".stripMargin

  val robixActuatorUncertainty: String =
    """let norm(x, y) = (x^2 + y^2)^(1/2);
      |let infdist(xl, yl, xr, yr) = max(abs(xl - xr), abs(yl - yr));
      |let dist(xl, xr, yl, yr) = norm (xl - xr, yl - yr);
      |let goal() <-> vr = 0 | dist(prx, pry, pox, poy) > vr^2/(2*b) + V*(vr/b)
      |let pre() <-> goal() & dist(prx,pry,pcx,pcy) > 0 ^ norm(drx, dry) = 1
      |let curve() <-> dist(prx, pry, pcx, pcy) > 0 & wr*dist(prx, pry, pcx, pcy) = vr;
      |let safe() <-> infdist(prx, pry, pox, poy) > vr^2 /(2*b*Um) +  ((A/(b*Um)) + 1)*((A/2)*T^2 + T*vr) + V*(T + (vr + A*T)/(b*Um));
      |?(pre());
      |{
      | {{vox := *; voy := *; ?(norm(vx, vy) <= V);
      |  {  {ar := -b;}
      |  ++ {?vr = 0; ar := 0; wr := 0;}
      |  ++ {ar := *; ?-b <= ar & ar <= A;
      |      wr := *; ?-W <= wr & wr <= W;
      |      pcx := *; pcy := *; drx := *; dry := *;
      |      pox := *; poy := *; ?curve() & safe();}}
      |  }}
      | {um := *; atr := um*ar; ?(0 <= Um & Um <= um & um <= 1);}
      | t:=0;
      | {prx' = vr*drx, pxy' = vr*dry, drx' = -wr*dry, dry' = wr*drx, pox' = vox, poy' = voy, vr' - atr,
      |  vwr' = atr/dist(prx, pry, pcx, pcy, t' = 1
      |  & ?(vr >= 0 & t <= T);}
      |}*
      |
      |""".stripMargin

  val rssExamples: List[String] = List(robixDynamicWindowPassive, robixDynamicWindowFriendly, robixRefinedObstacle,
    robixSensorUncertainty, robixActuatorUncertainty)

  val thesisExamples: List[String] = List(assertOnePos, assertBranchesNonzero, switchLiterals, noteAnd, squareNonneg,
    propSkipsQE, annotatedAssign, demonicLoop, straightODE, inductODE, inductODEBC, durationODE, ghostAssert,
    ghostAssign, ghostODE, inverseGhostODE,  superfluousGhost, labelInit, labelOld, unwindBlock,
    intoChoice, outOfChoice, printSolution, forwardHypothetical, sandboxExample, basicReachAvoid,
    )

  val allExamples: List[String] = rssExamples ++ ijrrModels ++ thesisExamples


  // @TODO implement file format
  /**
    * proof exampleProof = <proof> end
    * game exampleGame = ....
    *
    * proves exampleProof ``[exampleGame](<formula>)''
    **/


  // Counterexamples from thesis. Should fail to parse or fail to check
  val cyclicLabel: String =
    """x:= x@two; one:
      |x:= x@one; two:
      |""".stripMargin

  val referenceOverChoice: String =
    """y:=x@end;
    |{x:= 1; ++ x := 2;}
    |end:""".stripMargin

  val referenceOverStar: String =
    """ x := y@end;
      | y := *;
      | end:
      |""".stripMargin

  val referenceOverODE: String =
    """x := y@end;
      |y := 0;
      |{y' = 2 & y <= 5}
      |end:""".stripMargin

  val thesisCounterexamples: List[String] = List(cyclicLabel, referenceOverChoice, referenceOverStar, referenceOverODE)
}
