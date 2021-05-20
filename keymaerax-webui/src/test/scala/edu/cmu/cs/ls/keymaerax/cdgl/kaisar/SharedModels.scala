package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

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

  val letEvalAtUse: String =
    """
      | x:=0;
      | let thing() = x;
      | x:=1;
      | !(thing() = 1);
      |""".stripMargin

  val assertOnePos: String =
  """?xValue:(x=1);
    |!xPositive:(x > 0);
    |""".stripMargin

  val assertBranchesNonzero: String =
    """{?xNeg:(x < 0); ++ ?xPos:(x > 0);}
      |!xNonzero:(x != 0);
      |""".stripMargin

  val assertBranchesNonzeroProgram: String =
    """{?(x<0); ++ ?(x>0);}{?(x != 0);}^@"""

  val switchLiterals: String =
    """switch {
      |  case xLow:(x <= 1) =>  !result:(x <= 2);
      |  case xHigh:(x >= 0) =>  !result:(x + 1 > 0);
      |}
      |""".stripMargin
  val switchLiteralArg:String =
    """?bit:(x =  0 | x = 1);
      |switch (bit) {
      | case (x = 0) => !nonneg:(x >= 0);
      | case (x = 1) => !nonneg:(x >= 0);
      |}
      |""".stripMargin

  val switchLiteralArgAlternate:String =
 """{?bit:(x = 0); ++ ?bit:(x = 1);}
  |switch (bit) {
  |  case (x = 0) => !nonneg:(x >= 0);
  |  case (x = 1) => !nonneg:(x >= 0);
  |}""".stripMargin


  val switchLiteralsProgram: String =
    "{{?(x <= 1); ?(x <= 2);} ++ {?(x >= 0);?(x + 1 > 0);}}^@"

  val noteAnd: String =
    """?left:(x < 0);
      |?right:(y < 0);
      |note both = andI(left, right);
      |!sign:(x + y <= (x + y)^2);
      |""".stripMargin

  val noteAndProgram: String =
    """?(x<0);?(y<0);{?(x<0&y<0);}^@{?(x + y <= (x + y)^2);}^@"""

  val squareNonneg: String =
    """let square(x) = x*x;
      |let nonneg(x) <-> x >= 0;
      |!allSquaresNonneg:(nonneg(square(y)));
      |""".stripMargin

  /** Carefully check speed. Should use simple prop proof, not slow QE */
  val propSkipsQE: String =
    """?a:(x = 0 -> y=1);
      |?b:(x = 0 & ((z - x*w^2/(w^2+1))^42 >= 6));
      |!c: ( y=1) using a b by prop;
      |""".stripMargin

  val annotatedAssign: String =
    """x := *;
      |y := x + 1;
      |?zFact:(z := y);
      |!compare:(z > x) using zFact ... by auto;
      |""".stripMargin

  val annotatedAssignProgram: String =
    """x := *;
      |y := x + 1;
      |z := y;
      |{?(z>x);}^@
      |""".stripMargin

  val annotatedAssignGame: String =
    """x := *;
      |y := x + 1;
      |{z := *;}^@
      |{?(z>x);}^@
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


  /* Program which demonicLoop refines */
  val demonicLoopProgram: String =
    """
      |y:=0;
      |x:=0;
      |{?(x>=0);}^@
      |{ x:=x+1;
      | {?(x>=0);}^@
      |}*
      |{?(x>=y);}^@
      |""".stripMargin

  val demonicLoopConst: String =
    """?yZero:(y := 0);
      |?xZero:(x := 0);
      |?cPos:(c = 3);
      |!inv: (x >= 0);
      |{x:=x+c;
      | !inductiveStep:(x >= 0) using cPos inv by auto;
      |}*
      |!geq:(x >= y) using inv yZero by auto;
      |""".stripMargin


  val demonicLoopGhostly: String =
    """?yZero:(y := 0);
      |?xZero:(x := 0);
      |/++ !inv: (x >= 0); ++/
      |{x:=x+1;
      | /++ !inductiveStep: (x >= 0); ++/
      |}*
      |/++ !geq:(x >= y) using inv yZero by auto; ++/
      |""".stripMargin

  /* Program which demonicLoop refines */
  val demonicLoopGhostlyProgram: String =
    """
      |y:=0;
      |x:=0;
      |{ x:=x+1;
      |}*
      |""".stripMargin

  val straightODE: String =
    """x:= 0; y := 2;
      |{x' = 2, y' = -1 & ?dc:(y >= 0)};
      |!xFinal:(x <= 4) using dc x y by auto;
      |""".stripMargin

  val assertODE: String =
    """x:= 0; y := 2;
      |{x' = 2, y' = -1 & ?dc:(y >= 0) & !xEq:(x =  2*(2 - y))};
      |!xFinal:(x >= 0) using xEq dc by auto;
      |""".stripMargin

  val justxSolODE: String =
    """?xInit:(x:=0); y:=2;
      |{xSol: x' = 2, y' = 1 & ?dc:(y >= 0)};
      |!xFinal:(x >= 0) using  xSol xInit by auto;
      |""".stripMargin

  val inductODE: String =
    """x := 0; y := 1;
      |{x' = y,  y' = -x  & !circle:(x^2 + y^2 = 1) by induction};
      |""".stripMargin

  val solAgainODE: String =
    """?xInit:(x := 2); y := 0;
      |{y' = 1, xSol: x' = -2 & ?dc:(x >= 0) & !xSolAgain:(x = 2*(1 - y))};
      |!xHi:(x <= 2) using xInit xSol by auto;
      |!xLo:(x >= 0) using dc by auto;
      |""".stripMargin

  val inductODEBC: String =
    """x := 0; y := 1;
      |!bc:(x^2 + y^2 = 1);
      |{x' = y,  y' = -x  & !circle:(x^2 + y^2 = 1) by induction};
      |""".stripMargin

  val durationODE: String =
    """?(T > 0); ?accel:(acc > 0);
      |x:= 0; v := 0; t := 0;
      |{t' = 1, x' = v, v' = acc
      |  & !vel:(v >= 0) using accel by induction
      |  & !vSol: (v = t * acc) by solution
      |  & !xSol:(x = acc*(t^2)/2) by induction
      |  & ?dur:(t := T)};
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
      |!positive:(x > 0) using inv yInit xInit by auto;
      |""".stripMargin

  val ghostODE: String =
    """x := 1;
      |/++
      |  y := (1/x)^(1/2);
      |  !inv:(x*y^2 = 1) by auto;
      |++/
      |{x' = -x, /++ y' = y * (1/2) ++/ & !inv:(x*y^2 = 1) by induction}
      |!positive:(x > 0) using inv by auto;
      |""".stripMargin

  /** Program which the ghost ODE refines */
  val ghostODEProgram: String =
  "x := 1; {x' = -x}; {?(x > 0);}^@ "

  val inverseGhostODE: String =
    """z := 0;
      |{/-- x' = y, y' = -1 --/ ,  z'=1 & !zPos:(z >= 0) by solution}
      |""".stripMargin

  val inverseGhostODECircle: String =
    """z := 0;
      |{/-- x' = y, y' = -x --/ ,  z'=1 & !zPos:(z >= 0) by solution}
      |""".stripMargin

  /** Program which the inverse ghost ODE refines */
  val inverseGhostODEProgram: String =
    """z := 0;
      |{x' = y, y' = -1,  z'=1}
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
      |{x' = 1 & !greater:(x >= x@old)}
      |""".stripMargin

  val labelOldEq: String =
    """x:=0; y:=0; old:
      |{x' = 1, y' = -1 & !greater:(x+y = (x+y)@old)};
    |""".stripMargin

  //@TODO: Reveals terrible bug in solution expression that doesn't account for nonzero initial values?
  val labelOldestEq: String =
    """old:
      |{x' = 1, y' = -1 & !greater:(x+y = (x+y)@old)};
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
      |{t' = 1, x' = v, v' = -B  & ?(v >= 0)};
      |ode(t):
      |""".stripMargin

  val basicReachAvoid: String =
    """?(eps > 0 &  x = 0 & T > 0);
      |while (x >= 0 & x + eps <= goal) {
      |  vel := (goal - (x + eps))/T;
      |  t := 0;
      |  {t' = 1, x' = vel & ?time:(t <= T)};
      |  /-- !safe:(x >= 0) using time ... by auto;  --/
      |  ?(t >= T/2);
      |  !live:(x >= 0 & x + eps <= goal) using time ... by auto;
      |}
      |""".stripMargin


  // Note: not supposed to work. Is for historical purposes to remember early design
  val proposedReachAvoidFor: String =
    """?(eps > 0 &  x = 0 & T > 0 & d > 0);
      |let J(pos) <-> (pos <= d);
      |!conv:(J(0));
      |for (pos = 0; ?guard:(pos <= d - eps); pos := pos + eps*T/2;) {
      |prev:
      |  vel := (d - (x + eps))/T;
      |  t := 0;
      |  {t' = 1, x' = vel & ?time:(t <= T)};
      |  !safe:(J(x)) using conv guard vel time by auto;
      |  ?(t >= T/2);
      |  !prog:(pos >= pos@prev + eps*T/2);
      |}
      |!(d >= x & x >= d - eps) using guard conv by auto;
      |""".stripMargin

  // @TODO: Best way to handle refinement: allow ghost around /++ pos := 0 ++/ to give back existential statement in pos
  val basicForNoConv: String =
    """pragma option "time=true";
      |pragma option "trace=true";
      |pragma option "debugArith=true";
      | sum := 0;
      | for (pos := 0; ?(pos <= 10); pos := (pos + 1);) {
      |    sum := sum + 1;
      | }
      |""".stripMargin

  val basicForNoConvProg: String =
    """sum := 0;
      |pos := 0;
      |{{{sum := sum + 1;}^@ pos := pos + 1;}*}^@
      |{?(pos >= 10);}^@
      |""".stripMargin

  // gauss formula for triangle number
  val basicForConv: String =
    """
      | ?deltaLo:(delta > 0);
      | ?deltaHi:(delta < 1);
      | let sol(x) = x*(x+1)/2;
      | sum := 1;
      | for (x := 1; !(sum = sol(x)); ?(x <= 11); x := x + 1) {
      |    sum := sum + (x+1);
      |   !cnv:(sum = sol(x+1));
      | }
      | !done:(x >= 11 - delta) by guard(delta);
      | !total:(sum >= 50) using done sum x deltaHi by auto;
      |""".stripMargin


  // may be less popular but may be easier to implement / test
  val revisedReachAvoidFor: String =
    """pragma option "time=true";
      |pragma option "trace=true";
      |pragma option "debugArith=true";
      |?epsPos:(eps > 0);
      |?consts:(x = 0 & T > 0 & d > eps);
      |init:
      |for (pos := 0;
      |    !conv:(pos <= (x - x@init) & x <= d) using epsPos consts ... by auto;
      |    ?guard:(pos <= d - (eps + x@init) & x <= d - eps);
      |    pos := pos + eps/2) {
      |  vel := (d - x)/T;
      |  t := 0;
      |  {t' = 1, x' = vel & ?time:(t <= T)};
      |  !safe:(x <= d) using conv guard vel time by auto;
      |  ?high:(t >= T/2);
      |  !prog:(pos + eps/2 <= (x - x@init)) using high ... by auto;
      |  note step = andI(prog, safe);
      |}
      |!done:(pos >= d - (eps + x@init) - eps | x >= d - eps - eps) by guard;
      |!(x <= d & x + 2 * eps >= d) using done conv  by auto;
      |""".stripMargin

  // @TODO: Check SB() vs SB parenthesis... hmm...
  val forwardHypothetical: String =
    """let SB() = v^2/(2*B); let safe() <-> (SB() <= (d-x) & v >= 0);
      |?init:(T > 0 & A > 0 & B > 0); ?initSafe:(safe());
      |{{acc := *; ?env:(-B <= acc & acc <= A & safe()@ode(T));}
      | t:= 0; {ts: t' = 1, xs: x' = v, vs: v' = acc & ?time:(t <= T) & ?vel:(v >= 0)};
      |ode(t): !step:(safe()) using env init time vel xs vs ts by auto;
      |}*
      |""".stripMargin

  val forwardHypotheticalUnsolvable: String =
    """
      |!good:((y=1)@ode(T,0,1));
      |t:=0;x:=1;y:=0;
      |{t'=1,x'=-y,y'=x & ?(t<=T)};
      |ode(t,x,y):
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
      |  {tSol: t' = 1, xSol: x' = v, vSol: v' = acc & ?time:(0 <= t & t <= T) & ?vel:(v >= 0)};
      |ode(t, acc):
      |  !step:(safe()) using predictSafe init initSafe tSol xSol vSol time vel by auto;
      |}*
      |""".stripMargin

  val pldiModelSafeFull: String =
    """
      |pragma option "time=true";
      |pragma option "trace=true";
      |pragma option "debugArith=true";
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  {?(d >= eps*V); v:=*; ?(0<=v & v<=V); ++ v:=0;}
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps)};}
      |  !brk:(inv());
      | }*
      | !(d >= 0);
      |""".stripMargin

  val pldiModelSafeFullProgram: String =
    """?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      |{?((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V));}^@
      |{{?(d >= eps*V); v:=*; ?(0<=v & v<=V); ++ v:=0;}
      |{t := 0; {d' = -v, t' = 1 & (t <= eps)}}
      |{?((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V));}^@
      |}*
      |{?(d>=0);}^@
      |""".stripMargin

  // only needed for testing early versions of refinement checker
  val pldiModelSafeSimple: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V));
      | {
      |  {?before: (d >= eps*V); v:=*; ?range:(0<=v & v<=V);}
      |  {t := 0; {dSol: d' = -v, tSol: t' = 1 & ?(t <= eps)};}
      |  !((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V)) using v dSol tSol range before ... by auto ;
      | }*
      | !(d >= 0);
      |""".stripMargin

  val pldiModelSafeSimpleProgram: String =
    """?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      |{?((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V));}^@
      |{{?(d >= eps*V); v:=*; ?(0<=v & v<=V);}
      |{t := 0; {d' = -v, t' = 1 & (t <= eps)}}
      |{?((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V));}^@
      |}*
      |{?(d>=0);}^@
      |""".stripMargin

  val pldiStreamlined: String =
    """
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V));
      | {
      |  {v:=*; ?admiss:(d >= eps*v & 0<=v & v<=V);}
      |  {t := 0; {dSol: d' = -v, tSol: t' = 1 & ?(t <= eps)};}
      |  !((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V)) using v dSol tSol admiss ... by auto ;
      | }*
      | !(d >= 0);
      |""".stripMargin

  val pldiStreamlinedSandbox: String =
    """
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V));
      | {
      |  {  {v:=*; ?admiss:(d >= eps*v & 0<=v & v<=V);}
      |  ++
      |     {v:=0; !admiss:(d >= eps*v & 0<=v & v<=V);}
      |  }
      |  {t := 0; {dSol: d' = -v, tSol: t' = 1 & ?(t <= eps)};}
      |  !((d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V)) using v dSol tSol admiss ... by auto ;
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
      |   {d' = -v, t' = 1 & ?(t <= eps)
      |    & !tSign:(t>=0)
      |    & !dBound:(d>=v*(eps-t))
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
      |      { ?aB:(a := -b); ?tZ:(t := 0); xo := xo; yo := yo;
      |        { x' = v * dx, y' = v * dy, v' = a,
      |          dx' = -w * dy, dy' = w * dx, w' = a/r,
      |          t' = 1 & ?dc:(t <= T & v >= 0)
      |         & !tSign:(t >= 0) using tZ by induction
      |         & !dir:(norm(dx, dy) =  1) using dxyNorm by induction
      |         & !vSol:(v = v@body - b*t) using aB tZ by induction
      |         & !xBound:(-t * (v@body - b/2*t) <= x - x@body & x - x@body <= t * (v@body - b/2*t)) using bnds aB vSol dir tSign dc tZ by induction
      |         & !yBound:(-t * (v@body - b/2*t) <= y - y@body & y - y@body <= t * (v@body - b/2*t)) using bnds aB vSol dir tSign dc tZ by induction
      |        };
      |        let b1() <-> (x-xo > stopDist(v));
      |        let b2() <-> (xo-x > stopDist(v));
      |        let b3() <-> (y-yo > stopDist(v));
      |        let b4() <-> (yo-y > stopDist(v));
      |        switch (safeDist) {
      |          case far:((x - xo > stopDist(v))@body) =>
      |            !prog:(x-xo > stopDist(v)) using far andEL(xBound) vSol dc bnds tSign by auto;
      |            note infInd = orIL(prog, "b2() | b3() | b4()");
      |          case far:((xo-x > stopDist(v))@body) =>
      |            !prog:(xo-x > stopDist(v)) using far andER(xBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIL(prog, "b3()| b4()"));
      |          case far:((y-yo > stopDist(v))@body) =>
      |            !prog:(y-yo > stopDist(v)) using far andEL(yBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIL(prog, "b4()")));
      |         case far:((yo-y > stopDist(v))@body) =>
      |            !prog:(yo-y > stopDist(v)) using far andER(yBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIR("b3()", prog)));
      |        }
      |        /*!infInd: (infdistGr(x, y, xo, yo, stopDist(v))) using safeDist xBound yBound vSol dc bnds tSign aB tZ by auto;  vSign */
      |      }
      |      ++
      |      { ?vZ:(v = 0); ?aZ:(a := 0); w := 0; ?tZ:(t := 0); xo := xo; yo := yo; /* @TODO: Better SSA phi rename handling */
      |        { x' = v * dx, y' = v * dy, v' = a,        /* accelerate/decelerate and move */
      |          dx' = -w * dy, dy' = w * dx, w' = a/r,   /* follow curve */
      |          t' = 1 & ?dc:(t <= T & v >= 0)
      |         & !tSign:(t >= 0) using tZ by induction
      |         & !dir:(norm(dx, dy) = 1) using dxyNorm by induction
      |         & !vSol:(v = v@body) using aZ by induction
      |         & !xSol:(x = x@body) using vZ vSol dir tSign dc by induction
      |         & !ySol:(y = y@body) using vZ vSol dir tSign dc by induction
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
      |            note infInd = orIR("b1()", orIL(prog, "b3()|b4()"));
      |          case far:((y-yo > stopDist(v))@body) =>
      |            !prog:(y-yo > stopDist(v)) using far ySol vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIL(prog, "b4()")));
      |          case far:((yo-y > stopDist(v))@body) =>
      |            !prog:(yo-y > stopDist(v)) using far ySol vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIR("b3()", prog)));
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
      |          t' = 1 & ?dc:(t <= T & v >= 0)
      |         & !tSign:(t >= 0) using tZ aA by induction
      |         & !dir:(norm(dx, dy) = 1) using dxyNorm by induction
      |         & !vSol:(v = v@body + A*t) using aA tZ by induction
      |         & !xBound:(-t * (v@body + A/2*t) <= x - x@body & x - x@body <= t * (v@body + A/2*t)) using bnds aA vSol dir tSign dc tZ by induction /* got here after 20 mins -> reduced to 4 secs */
      |         & !yBound:(-t * (v@body + A/2*t) <= y - y@body & y - y@body <= t * (v@body + A/2*t)) using bnds aA vSol dir tSign dc tZ by induction
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
      |            note infInd = orIR("b1()", orIL(prog, "b3()|b4()"));
      |          case far:((y-yo > admissibleSeparation(v))@monitor) =>
      |            !prog:(y-yo > stopDist(v)) using far andEL(yBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIL(prog, "b4()")));
      |          case far:((yo-y > admissibleSeparation(v))@monitor) =>
      |            !prog:(yo-y > stopDist(v)) using far andER(yBound) vSol dc bnds tSign by auto;
      |            note infInd = orIR("b1()", orIR("b2()", orIR("b3()", prog)));
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
      |         & !tSign:(t >= 0) using tZ by induction
      |         & !dir:(norm(dx, dy) =  1) using dxyNorm by induction
      |         & !vSol:(v = v@body + a*t) using tZ by induction
      |         & !xBound:(-t * (v@body + a/2*t) <= x - x@body & x - x@body <= t * (v@body + a/2*t)) using bnds vSol dir tSign dom tZ by induction
      |         & !yBound:(-t * (v@body + a/2*t) <= y - y@body & y - y@body <= t * (v@body + a/2*t)) using bnds vSol dir tSign dom tZ by induction
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
      |        ?(t' = 1 & t <= ep & v >= 0)
      |        !tSign:(t>=0)
      |        !xBound:(-t*v <= xo - xo@loop & xo - xo@loop <= t*v)
      |        !yBound:(-t*v <= yo - yo@loop & yo - yo@loop <= t*v)
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
      |        ?(t' = 1 & t <= ep & v >= 0)
      |        !tSign:(t>=0)
      |        !dir:(norm(dx, dy) = 1)
      |        !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V())
      |        !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V())
      |        !vSol:(v = v@loop + a*t)
      |        !xBound:(-t*(v@loop - a/2*t) <= xo - xo@loop & xo - xo@loop <= t*(v@loop - a/2*t))
      |        !yBound:(-t*(v@loop - a/2*t) <= yo - yo@loop & yo - yo@loop <= t*(v@loop - a/2*t))
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
      |        ?(t' = 1 & t <= ep() & v >= 0)
      |        !tSign:(t>=0)
      |        !dir:(norm(dx, dy) = 1)
      |        !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V())
      |        !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V())
      |        !vSol:(v = v@loop + a*t)
      |        !xBound:(-t*(v@loop - a/2*t) <= xo - xo@loop & xo - xo@loop <= t*(v@loop - a/2*t))
      |        !yBound:(-t*(v@loop - a/2*t) <= yo - yo@loop & yo - yo@loop <= t*(v@loop - a/2*t))
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
      |  & ?(t := todo())
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
      |        ?(t <= ep() & v >= 0)
      |        !tSign:(t>=0)
      |        !dir:(norm(dx, dy) = 1)
      |        !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V())
      |        !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V())
      |        !vSol:(v = v@loop + a*t)
      |        !betaSol:(beta = beta@loop + t/r*(v + a/2*t))
      |        !xBound:(-t*(v@loop - a/2*t) <= xo - xo@loop & xo - xo@loop <= t*(v@loop - a/2*t))
      |        !yBound:(-t*(v@loop - a/2*t) <= yo - yo@loop & yo - yo@loop <= t*(v@loop - a/2*t))
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
      |        !tSign:(t>=0)
      |        !dir:(norm(dx, dy) = 1)
      |        !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V())
      |        !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V())
      |        !vSol:(v = v@loop + a*t)
      |        !xBound:(-t*(v@loop - a/2*t) <= xo - xo@loop & xo - xo@loop <= t*(v@loop - a/2*t))
      |        !yBound:(-t*(v@loop - a/2*t) <= yo - yo@loop & yo - yo@loop <= t*(v@loop - a/2*t))
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
      |       & !tSign:(t>=0)
      |       & !dir:(norm(dx, dy) = 1)
      |       & !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V())
      |       & !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V())
      |       & !vBound:(v <= v@loop - a**t)
      |       & !xBound:(-t * (v - a/2*t) <= x - x@loop & x - x@loop <= t * (v - a/2*t))
      |       & !yBound:-(t * (v - a/2*t) <= y - y@loop & y - y@loop <= t * (v - a/2*t))
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
      |       & !tSign:(t>=0)
      |       & !dir:(norm(dx, dy) = 1)
      |       & !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V())
      |       & !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V())
      |       & !vBound:(v <= v@loop - (b()*Da())*t)
      |       & !xBound:(-t * (v@loop - (b()*Da())/2*t) <= x - x@loop & x - x@loop <= t * (v@loop - (b()*Da())/2*t))
      |       & !yBound:-(t * (v@loop - (b()*Da())/2*t) <= y - y@loop & y - y@loop <= t * (v@loop - (b()*Da())/2*t))
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
      |       & !tSign:(t>=0)
      |       & !dir:(norm(dx, dy) = 1)
      |       & !xoBound:(-t*V() <= xo - xo@loop & xo - xo@loop <= t*V())
      |       & !yoBound:(-t*V() <= yo - yo@loop & yo - yo@loop <= t*V())
      |       & !vBound:(v <= v@loop - a*t)
      |       & !xBound:(-t * (v@loop - a/2*t) <= x - x@loop & x - x@loop <= t * (v@loop - a/2*t))
      |       & !yBound:-(t * (v@loop - a/2*t) <= y - y@loop & y - y@loop <= t * (v@loop - a/2*t))
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
      |          t' = 1 & ?(t <= ep & v >= 0)
      |        & !(t>=t@body)
      |        & !(norm(dx, dy) = 1)
      |        & !(-(t-t@body)*V() <= xo - xo@body & xo - xo@body <= (t-t@body)*V())
      |        & !(-(t-t@body)*V() <= yo - yo@body & yo - yo@body <= (t-t@body)*V())
      |        & !(v = v@body + a*(t-t@body))
      |        & !(-(t-t@body) * (v - a/2*(t-t@body)) <= x - x@body & x - x@body <= (t-t@body) * (v - a/2*(t-t@body)))
      |        & !(-(t-t@body) * (v - a/2*(t-t@body)) <= y - y@body & y - y@body <= (t-t@body) * (v - a/2*(t-t@body)))
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
      | {xr' = vr, vr' = ar, t' = 1 & ?(t <= ep() & vr >= 0)};
      | !(loopinv());
      | }*
      | !(xr < waypointEndDist(xg));
      | !(loopinv());
      |	{ { { {
      |      ar := -b();
      |   ++ ?vr = 0; ar := 0;
      |   ++ ?xr + stopDist(vr) + accComp(vr) < waypointEndDist(xg) & vr+A()*ep()<=Vmax(); ar := A();
      |   ++ ?xr <= waypointStartDist(xg) & vr <= Vmax(); ar := *; ?-b() <= ar & ar <= (Vmax()-vr)/ep() & ar <= A();
      |	} t:=0; } xr' = vr, vr' = ar, t' = 1 & ?(t <= ep() & vr >= 0)};
      | !(loopinv());
      | }*
      | !(waypointStartDist(xg) < xr);
      |""".stripMargin

  val ijrrModels: List[String] = List(ijrrStaticSafetySimplified, ijrrStaticSafetyRough /*, ijrrPassiveFriendlySafety, ijrrPassiveSafety, ijrrVelocityPassiveSafety*/)
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
      |  & ?(vr >= 0 & t <= T)}
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
      |  & ?(vr >= 0 & t <= T)}
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
      | {pox' = vo*dox, poy' = vo*doy, vo' = ao, t' = 1 & t <= To & ?(vo > = 0)}
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
      |  & ?(vr >= 0 & t <= T)}
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
      |  & ?(vr >= 0 & t <= T)}
      |}*
      |
      |""".stripMargin

  val rssExamples: List[String] = List(/*robixRefinedObstacle,robixRefinedObstacle, robixDynamicWindowFriendly,
    robixSensorUncertainty, robixRefinedObstacle, robixActuatorUncertainty*/)

  val thesisExamples: List[String] = List(switchLiteralArg, justxSolODE, assertOnePos, assertBranchesNonzero, switchLiterals, noteAnd, squareNonneg,
    propSkipsQE, annotatedAssign, demonicLoop, straightODE, inductODE, inductODEBC, durationODE, ghostAssert,
    ghostAssign, ghostODE, inverseGhostODE,  superfluousGhost, labelInit, labelOld, labelOldEq, unwindBlock, basicForConv,
    intoChoice, outOfChoice, printSolution, forwardHypothetical, sandboxExample, basicReachAvoid,
    switchLiteralArgAlternate, solAgainODE, inverseGhostODECircle, letEvalAtUse, demonicLoopConst, solAgainODE,
    labelOldestEq, forwardHypotheticalUnsolvable
    )

  val pldiExamples: List[String] = List(pldiModelSafeFull, pldiModelSafeSimple, pldiSandboxSafe)

  val thesisCaseStudies: List[String] = pldiExamples ++ rssExamples ++ ijrrModels
  val allExamples: List[String] = pldiExamples ++ rssExamples ++ ijrrModels ++ thesisExamples


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
