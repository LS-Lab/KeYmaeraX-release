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

  val noteAndSquare: String =
    """let square(z) = z * z;
      |?left:(x < 0); ?right:(square(y) > 0);
      |note both = andI(left, right);
      |""".stripMargin

  val noteAndFull: String =
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

  val squareNonnegAlt: String =
    """let squareX() = x*x;
      |let nonnegX() <-> squareX() >= 0;
      |!squareXNonneg:(nonnegX());
      |""".stripMargin

  /** Carefully check speed. Should use simple prop proof, not slow QE */
  val propSkipsQE: String =
    """?a:(x = 0 -> y=1);
      |?b:(x = 0 & ((z - x*w^2/(w^2+1))^42 >= 6));
      |!c:(y=1) using a b by prop;
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
      |{x' = 2, y' = -1 & ?dom:(y >= 0)};
      |!xFinal:(x + y <= 4);
      |""".stripMargin

  //  using dc x y by auto
  val assertODE: String =
    """x:= 0; y := 2;
      |{x' = 2, y' = -1 & ?dom:(y >= 0) & !xEq:(x =  2*(2 - y))};
      |!xFinal:(x >= 0) using xEq dom by auto;
      |""".stripMargin

  val justxSolODE: String =
    """?xInit:(x:=0); y:=2;
      |{xSol: x' = 2, y' = 1 & ?dom:(y >= 0)};
      |!xFinal:(x >= 0) using xInit xSol by auto;
      |""".stripMargin

  val inductODE: String =
    """x := 0; y := 1;
      |{x' = y,  y' = -x  & !circle:(x^2 + y^2 = 1) by induction};
      |""".stripMargin

  val solAgainODE: String =
    """?xInit:(x := 2); y := 0;
      |{y' = 1, xSol: x' = -2 & ?dom:(x >= 0) & !xSolAgain:(x = 2*(1 - y))};
      |!xHi:(x <= 2) using xInit xSol by auto;
      |!xLo:(x >= 0) using dom by auto;
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
      |!finalV:(x = acc*(T^2)/2) using dur xSol by auto;
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
      |{x' = -x, /++ y' = y * (1/2) ++/ & !inv:(x*y^2 = 1) by induction};
      |!positive:(x > 0) using inv by auto;
      |""".stripMargin

  /** Program which the ghost ODE refines */
  val ghostODEProgram: String =
  "x := 1; {x' = -x}; {?(x > 0);}^@ "

  val inverseGhostODE: String =
    """z := 0;
      |{/-- x' = y, y' = (-1) --/ ,  z'=1 & !zPos:(z >= 0) by solution}
      |""".stripMargin

  val inverseGhostODECircle: String =
    """z := 0;
      |{/-- x' = y, y' = -x --/ ,  z'=1 & !zPos:(z >= 0) by solution}
      |""".stripMargin

  /** Program which the inverse ghost ODE refines */
  val inverseGhostODEProgram: String =
    """z := 0;
      |{x' = y, y' = (-1),  z'=1}
      |""".stripMargin

  // Correctly rejected
  val ghostBothWays: String =
    """x:=0;  y:=0; /++?foo:(z:=0);++/
      |{x' = 1, /-- y'=1 --/, /++ z'=1 ++/
      |& !inv:(x=y);};
      |!atEnd:(x=y);
      |""".stripMargin

  val discreteInverseGhostInsideForward: String =
    """/++ /-- x:= 0; --/ ++/
      |
      |""".stripMargin

  val discreteForwardGhostInsideInverse: String =
    """/-- /++ x:= 0; ++/ --/
      |
      |""".stripMargin

  val odeInverseGhostInsideForward: String =
    """/++y:=0;++/
      |{x'=1, /++ /-- y'=0 --/ ++/};
      |
      |""".stripMargin

  val odeForwardGhostInsideInverse: String =
    """{x'=1, /-- /++ y'=0 ++/ --/};
      |
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
    """?xInit:(x:=0); y:=0; old:
      |{x' = 1, y' = -1 & !greater:(x+y = (x+y)@old) using xInit ... by auto};
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
      |     { x := x + 3; mid: x := x * x;
      |++  x := 5;}
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
      |  !safe:(x <= d) using time ... by auto;
      |  ?high:(t >= T/2);
      |  !prog:(pos + eps/2 <= (x - x@init)) using high ... by auto;
      |  note step = andI(prog, safe);
      |}
      |!done:(pos >= d - (eps + x@init) - eps | x >= d - eps - eps) by guard;
      |!(x <= d & x + 2 * eps >= d) using done conv  by auto;
      |""".stripMargin

  val brokenStoppingReachAvoidFor:String =
    """
      |pragma option "time=true";
      |pragma option "trace=true";
      |pragma option "debugArith=true";
      |let liveFactor() = 4;
      |let liveIncr() = V*eps/(liveFactor()*liveFactor());
      |let inv(pos) <-> (d >= 0 & ((done = 0 & (d@init - d) >= pos) | (done=1  & d<=V*eps)));
      |?(d >= 0 & V > 0 & eps > 0 & v=0 & t=0 & done=0);
      |init:
      |for (pos := 0; !conv:(inv(pos));
      | ?guard:(pos <= d@init & (d >= V*eps | done=0)); pos := pos + liveIncr()) {
      |body:
      |  did:=done;
      |  switch (andER(conv)) {
      |    case (done = 1 & d<=V*eps) => v:=0; done:=1; !br:(v=0&done=1&d<=V*eps);
      |    case (done = 0 & (d@init - d) >= pos) =>
      |    switch {
      |      case (d >= V*eps) => v:=V; done:=0; !br:(v=V&done=0&did=0);
      |      case (true) => v:=0; done:=1; !br:(v=0&done=1&did=0);
      |    }
      |  }
      |  mid:
      |  t:=0; { d'=-v, t'=1 & ?(t <= eps) & !(d >= v*(eps-t))
      |    & !(d <= d@body - v*t/liveFactor())};
      |  ?(t >= eps/liveFactor());
      |  switch (br) {
      |    case (v=0&done=1&d@body<=V*eps) => !(inv(pos + liveIncr()));
      |    case (v=V&done=0&did=0) => !(inv(pos + liveIncr()));
      |    case (v=0&done=1&did=0) => !(inv(pos + liveIncr()));
      |  }
      |}
      |!(pos >= d@init - eps | d <= V*eps + eps) by guard(eps);
      |!(d >= 0 & d <= (V+1)*eps);
      |""".stripMargin

  val pldiReachAvoidDisturbance:String =
    """
      |let inv(pos) <-> (d >= 0 & (d@init - d) >= pos);
      |let liveFactor() = 4;
      |let liveIncr() = V*eps/(4*liveFactor()*liveFactor());
      |?(d >= 0 & V > 0 & eps > 0 & v=0 & t=0);
      |init:
      |for (pos := 0; !conv:(d >= 0 & (d@init - d) >= pos);
      | ?guard:(pos <= d@init & d >= V*eps); pos := pos + liveIncr()) {
      |body:
      |   v:=V;
      |   c:=*; ?dstrb:(0.5 <= c & c <= 1.0); ?vd:(v:=v*c);
      |   {t:=0; { d'=-v, t'=1 & ?(t <= eps) & !(d >= v*(eps-t))
      |     using dstrb ... by auto;
      |    & !(d <= d@body - v*t/liveFactor()) using dstrb ... by auto};}
      | ?(t >= eps/liveFactor());
      | !(inv(pos + liveIncr())) using dstrb vd ... by auto;
      |}
      |!(pos >= d@init - eps | d <= V*eps + eps) by guard(eps);
      |!(d >= 0 & d <= (V+1)*eps);
      |
      |""".stripMargin

  // @TODO: Check SB() vs SB parenthesis... hmm...
  val forwardHypothetical: String = // in safe: .. & v >= 0
    """let SB() = v^2/(2*B); let safe() <-> (SB() <= (d-x));
      |?bnds:(T > 0 & A > 0 & B > 0); ?initSafe:(safe());
      |{acc := *; ?env:(-B <= acc & acc <= A & (safe() & v >= 0)@ode(T));
      | t:= 0; {t' = 1, x' = v, v' = acc & ?time:(t <= T) & ?vel:(v >= 0)};
      |ode(t): !step:(safe()) using env bnds time vel ... by auto;
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
    """let SB() = v^2/(2*B);
      |let safe() <-> SB() <= (d-x);
      |?bnds:(T > 0 & A > 0 & B > 0);
      |?initSafe:(safe());
      |{
      |  accCand := *;
      |  let admiss() <-> -B <= accCand & accCand <= A;
      |  let env()    <->  (safe() & v >= 0)@ode(T, accCand);
      |  switch {
      |    case inEnv:(env()) =>
      |      ?theAcc:(acc := accCand);
      |      !predictSafe:((safe() & v >= 0)@ode(T, acc));
      |    case true =>
      |      ?theAcc:(acc := -B);
      |      !predictSafe:((safe() & v >= 0)@ode(min(T,v/B), acc));
      |  }
      |  t:= 0;
      |  {t' = 1, x' = v, v' = acc & ?time:(0 <= t & t <= T) & ?vel:(v >= 0)};
      |ode(t, acc):
      |  !step:(safe()) using predictSafe bnds initSafe time vel ... by auto;
      |}*
      |""".stripMargin

  val pldiModelSafeFull: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  {?(d >= eps*V); v:=*; ?(0<=v & v<=V); ++ v:=0;}
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps)};}
      |  !(inv());
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

  val pldiAngelicSandbox: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | !(inv());
      | {
      |  vCand :=*;
      |  switch {
      |    case (d>=eps*V & 0 <=vCand & vCand <= V) => v:=vCand;
      |    case (true) => v:=0;
      |  }
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps); & !(d >= v*(eps-t));};}
      |  !(inv());
      | }*
      | !(d >= 0);
      |""".stripMargin

  val pldiTimedAngelicControl: String =
    """
      | let inv() <-> (d>=v*(eps-t) & t>=0 & t<=eps & 0<=v&v<=V);
      | ?(d >= 0 & V >= 0 & eps >= 0 & v=0 & t=0);
      | for (time := 0; !(inv()); ?(time <= 10000); time := (time + 600);) {
      |  switch {
      |    case (d>=eps*V) => v:=V; ?(0<=v&v<=V);
      |    case (true) => v:=0;
      |  }
      |  {t := 0; {d' = -v, t' = 1 & ?(t <= eps); & !(d >= v*(eps-t));};}
      |  !(inv());
      | }
      | !(d >= 0);
      |""".stripMargin

  val pldiReachAvoid: String =
    """
      |let inv(pos) <-> (d >= 0 & (d@init - d) >= pos);
      |let liveFactor() = 4;
      |let liveIncr() = V*eps/(liveFactor()*liveFactor());
      |?(d >= 0 & V > 0 & eps > 0 & v=0 & t=0);
      |init:
      |for (pos := 0; !conv:(d >= 0 & (d@init - d) >= pos);
      | ?guard:(pos <= d@init & d >= V*eps); pos := pos + liveIncr()) {
      |body:
      |   v:=V;
      |   {t:=0; { d'=-v, t'=1 & ?(t <= eps) & !(d >= v*(eps-t))
      |    & !(d <= d@body - v*t/liveFactor())};}
      | ?(t >= eps/liveFactor());
      | !(inv(pos + liveIncr()));
      |}
      |!(pos >= d@init - eps | d <= V*eps + eps) by guard(eps);
      |!(d >= 0 & d <= (V+1)*eps);
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
      |let initialState() <->
      |  (v = 0 & dist(x,y,xo,yo) > 1 & norm(dx, dy) = 1);
      |let infdistGr(x1, y1, x2, y2, z) <->
      |  (x1-x2 > z | x2 - x1 > z | y1 - y2 > z | y2 - y1 > z);
      |/* Disjuncts of infdistGr predicate, useful in case analysis */
      |let goal() <-> (dist(x,y,xo,yo) > 0);
      |?(bnds, st):(bounds() & initialState());
      |/* Prove infdist > 0 in base case by case-analyzing x,y and
      |   using assumption on euclidean distance > 1*/
      |!splitX:(x-xo >= 0.25 | x-xo <= 0.35) by exhaustion;
      |!splitXO:(xo-x >= 0.25 | xo-x <= 0.35) by exhaustion;
      |!splitY:(y-yo >= 0.25 | y-yo <= 0.35) by exhaustion;
      |!sd:(infdistGr(x, y, xo, yo, stopDist(v)))
      |  using splitX splitXO splitY bnds st by auto;
      |/* Base case invariant */
      |!(vSign, dxyNorm, safeDist):
      |  (  v >= 0
      |   & norm(dx, dy) = 1
      |   & infdistGr(x, y, xo, yo, stopDist(v)))
      |   using bnds st sd by auto;
      |{body:
      |  {
      |    {
      |     let monCond() <->
      |       ( (a = -b
      |       | (a = 0 & v = 0)) & infdistGr(x, y, xo, yo,  stopDist(v))
      |       | a = A & infdistGr(x, y, xo, yo,  admissibleSeparation(v,A)));
      |      { {  {?aB:(a := -b);
      |           xo := xo; yo := yo;
      |           !admiss:(monCond())
      |             using safeDist vSign bnds aB by auto; }
      |        ++ {?vZ:(v = 0); ?aZ:(a := 0); w := 0;
      |           xo := xo; yo := yo;
      |           !admiss:(monCond())
      |             using safeDist vSign bnds aZ vZ by auto; }
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
      |          t' = 1 & ?dom:(t <= T & v >= 0)
      |         & !tSign:(t >= 0) using tZ by induction
      |         & !dir:(norm(dx, dy) =  1) using dxyNorm by induction
      |         & !vSol:(v = v@body + a*t) using tZ by induction
      |         & !xBound:(-t * (v@body + a/2*t) <= x - x@body
      |             & x - x@body <= t * (v@body + a/2*t))
      |             using bnds vSol dir tSign dom tZ by induction
      |         & !yBound:(-t * (v@body + a/2*t) <= y - y@body
      |            & y - y@body <= t * (v@body + a/2*t))
      |            using bnds vSol dir tSign dom tZ by induction
      |        };
      |        !infInd:(infdistGr(x,y,xo,yo, stopDist(v)))
      |        using admiss xBound yBound vSol dom bnds tSign by auto;
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


  val ralWaypointSafety: String =
    """
      |let sq(x) = (x*x);
      |let onUpperHalfPlane(x, y) <-> (y > 0);
      |let circle(x, y, k) = (k*(sq(x)+sq(y)) - 2*x);
      |let isAnnulus(k) <-> (abs(k)*eps <= 1);
      |let onAnnulus(x, y, k) <-> (
      |                    (k*sq(eps) - 2*eps) < circle(x,y,k)
      |  & circle(x,y,k) < (k*sq(eps) + 2*eps));
      |let isIvl(vl, vh) <-> (0 <= vl & vl < vh);
      |let loCSG(vl, vh) <-> (A * T <=  (vh - vl));
      |let hiCSG(vl, vh) <-> (B * T <=  (vh - vl));
      |let controllableSpeedGoal(vl, vh) <-> (
      |  isIvl(vl, vh) &
      |  loCSG(vl, vh) &
      |  hiCSG(vl, vh));
      |let controllableGoalDist(v1, v2, a, xg, yg, k) <-> (
      |    v1 <= v2 |
      |    (xg>=0&k>=0 &
      |     ((1 + 2*eps*  k + sq(eps*k)) * (sq(v1)-sq(v2)) <= (2*a) *
      |     (yg-eps) |
      |      (1 + 2*eps*k + sq(eps*k)) * (sq(v1)-sq(v2)) <= (2*a) * (xg-eps))
      |   | xg<=0&k<=0 &
      |     ((1 + 2*eps*(-k) + sq(eps*k)) * (sq(v1)-sq(v2)) <= (2*a) *
      |     (yg-eps) |
      |      (1 + 2*eps*(-k) + sq(eps*k)) * (sq(v1)-sq(v2)) <= (2*a) *
      |      (-xg-eps))));
      |let J(xg, yg, k, v, vl, vh) <-> (
      |  v >= 0 &
      |  isAnnulus(k) &
      |  onAnnulus(xg,yg,k) &
      |  controllableSpeedGoal(vl,vh) &
      |  controllableGoalDist(v,vh,B,xg,yg,k) &
      |  controllableGoalDist(vl,v,A,xg,yg,k));
      |let admRange(a) <-> (-B <= a & a <= A);
      |let admBrake(v,a) <-> (v + a*T >= 0);
      |let negBounds(xg,yg,v,vl,vh,a,k) <->
      |   ((xg<=0&k<=0) &
      |     ((vl <= v & vl <= v+a*T
      |     |  (1 + 2*eps*(-k) + sq(eps*k)) * (A*(2*v*T+a*sq(T)) + (sq(vl) -
      |     sq(v+a*T))) <= (2*A) * (-xg-eps)
      |     |  (1 + 2*eps*(-k) + sq(eps*k)) * (A*(2*v*T+a*sq(T)) + (sq(vl) -
      |     sq(v+a*T))) <= (2*A) * (yg-eps))
      |   & (v <= vh & v+a*T <= vh
      |     | (1 + 2*eps*(-k) + sq(eps*k)) * (B*(2*v*T+a*sq(T)) + (sq(v+a*T)
      |     - sq(vh))) <= (2*B) * (-xg-eps)
      |     | (1 + 2*eps*(-k) + sq(eps*k)) * (B*(2*v*T+a*sq(T)) + (sq(v+a*T)
      |     - sq(vh))) <= (2*B) * (yg-eps))));
      |let posBounds(xg,yg,v,vl,vh,a,k) <->
      |   ((xg>=0&k>=0) &
      |     (( vl <= v & vl <= v+a*T
      |     | (1 + 2*eps*(k) + sq(eps*k)) * (A*(2*v*T+a*sq(T)) + (sq(vl) - sq
      |     (v+a*T))) <= (2*A) * (xg-eps)
      |     | (1 + 2*eps*(k) + sq(eps*k)) * (A*(2*v*T+a*sq(T)) + (sq(vl) - sq
      |     (v+a*T))) <= (2*A) * (yg-eps))
      |   & (v <= vh & v+a*T <= vh
      |     | (1 + 2*eps*(k) + sq(eps*k)) * (B*(2*v*T+a*sq(T)) + (sq(v+a*T)
      |     - sq(vh))) <= (2*B) * (xg-eps)
      |     | (1 + 2*eps*(k) + sq(eps*k)) * (B*(2*v*T+a*sq(T)) + (sq(v+a*T)
      |     - sq(vh))) <= (2*B) * (yg-eps))));
      |let anyBounds(xg,yg,v,vl,vh,a,k) <-> (vl <= v & v+a*T >= vl & v <= vh
      |& v+a*T <= vh);
      |let admBounds(xg,yg,v,vl,vh,a,k) <-> (
      |   negBounds(xg,yg,v,vl,vh,a,k)
      | | posBounds(xg,yg,v,vl,vh,a,k)
      | | anyBounds(xg,yg,v,vl,vh,a,k));
      |let admissibleAcc(xg, yg, v, vl, vh, a, k) <-> (
      |  admRange(a) &
      |  admBrake(v,a) &
      |  admBounds(xg,yg,v,vl,vh,a,k));
      |?(const, bc):((T > 0 & eps > 0 & A > 0 & B > 0) & J(xg,yg,k,v,vl,vh));
      |!constA:(T > 0 & eps > 0 & A > 0) using const by prop;
      |!constB:(T > 0 & eps > 0 & B > 0) using const by prop;
      |!inv:(J(xg, yg, k, v, vl, vh));
      |{body:
      | !ihV:(v >= 0) using inv by prop;
      | !ihCgdL:(controllableGoalDist(vl,v,A,xg,yg,k)) using inv by prop;
      | !ihCgdU:(controllableGoalDist(v,vh,B,xg,yg,k)) using inv by prop;
      | {xg:=*;yg:=*;vl:=*;vh:=*;k:=*;a:=*;
      |  ?dir:(xg>=0&k>=0|xg<=0&k<=0);
      |  ?(uhp, isAnn, onAnn, csgIvl, csgLo, csgHi):
      |   (onUpperHalfPlane(xg,yg) &
      |    isAnnulus(k) &
      |    onAnnulus(xg,yg,k) &
      |    isIvl(vl, vh) &
      |    loCSG(vl, vh) &
      |    hiCSG(vl, vh));
      |  note csg = andI(csgIvl, andI(csgLo, csgHi));
      |  adm:
      |  ?(accLo, accHi, noBrake, admBounds):(-B <= a & a <= A & admBrake
      |  (v,a) & admBounds(xg,yg,v,vl,vh,a,k));
      |  note accRange = andI(accLo, accHi);
      |  ?accSgn:(a <= 0 | a >= 0);}
      | switch (admBounds) {
      | case kAnyAdm:(anyBounds(xg,yg,v,vl,vh,a,k)) =>
      |   print("CASE sgn(k) irrelevant");
      |   switch (accSgn) {
      |     case accNeg:(a<=0) =>
      |      print("subcase a<=0");
      |       t:=0;
      |       { xg'=-v*k*yg, yg'=v*(k*xg-1), v'=a, t'=1
      |       & ?dom:(v >= 0 & t <= T);
      |       & !tPos:(t>=0);
      |       & !dLo:((k*(eps*eps)-2*eps) < k*(sq(xg)+sq(yg))-2*xg)
      |       using isAnn onAnn by induction;
      |       & !dHi:(k*(xg*xg+yg*yg)-2*xg < (k*sq(eps)+2*eps))
      |       using isAnn onAnn by induction;
      |       & !vBound:(v+a*(T-t)>=0) using tPos noBrake by induction;
      |       & !vLoInd:(v + a*(T-t) >= vl)
      |using  accSgn  kAnyAdm dLo dHi dom tPos vBound const by induction;
      |       & !vHiInd:(v + a*(T-t) <= vh)
      |using  accSgn  kAnyAdm dLo dHi dom tPos vBound const by induction;
      |       & !vDec:(v <= v@adm) using accNeg by induction;
      |       & !vDecSlo:(v >= v@adm + a*t) using accNeg by induction;};
      |       ?xgSgnC:(xg<=0);
      |       !indVPos:(v >= 0) using dom by auto;
      |       !indIsAnn:(isAnnulus(k)) using isAnn by auto;
      |       !indOnAnn:(onAnnulus(xg,yg,k)) using onAnn dLo dHi by auto;
      |       print("After ODE, CASE sgn(k), irrelevant, a <= 0");
      |       !indCGDHBndA:(v <= vh)
      |using vDec vHiInd kAnyAdm dom tPos accRange by auto;
      |       !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |       using indCGDHBndA by auto;
      |       !indCGDLBndA:(vl <= v)
      |using vDec vDecSlo vLoInd kAnyAdm dom tPos accRange csg by auto;
      |       !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |       using indCGDLBndA by auto;
      |       !indCSG:(controllableSpeedGoal(vl,vh)) using vDec csg by auto;
      |       note indStepA = andI(andI(andI(andI(andI(indVPos, indIsAnn),
      |       indOnAnn), indCSG), indCGDH), indCGDL);
      |       !indAssert:(J(xg, yg, k, v, vl, vh)) using indStepA by auto;
      |     case accPos:(a>=0) =>
      |       print("subcase a>=0");
      |       t:=0;
      |       { xg'=-v*k*yg, yg'=v*(k*xg-1), v'=a, t'=1
      |       & ?dom:(v >= 0 & t <= T);
      |       & !tPos:(t>=0);
      |       & !dLo:((k*(eps*eps)-2*eps) < k*(sq(xg)+sq(yg))-2*xg)
      |       using isAnn onAnn by induction;
      |       & !dHi:(k*(xg*xg+yg*yg)-2*xg < (k*sq(eps)+2*eps))
      |       using isAnn onAnn by induction;
      |       & !vBound:(v+a*(T-t)>=0) using tPos noBrake by induction;
      |       & !vLoInd:(v + a*(T-t) >= vl)
      |using  accSgn  kAnyAdm dLo dHi dom tPos vBound const by induction;
      |       & !vHiInd:(v + a*(T-t) <= vh)
      |using  accSgn  kAnyAdm dLo dHi dom tPos vBound const by induction;
      |       & !vInc:(v >= v@adm) using accPos by induction;
      |       & !vIncSlo:(v <= v@adm + a*t) using accPos by induction;};
      |       ?xgSgnC:(xg<=0);
      |       !indVPos:(v >= 0) using dom by auto;
      |       !indIsAnn:(isAnnulus(k)) using isAnn by auto;
      |       !indOnAnn:(onAnnulus(xg,yg,k)) using onAnn dLo dHi by auto;
      |       print("After ODE, CASE sgn(k), irrelevant, a >= 0");
      |       !indCGDHBndA:(v <= vh)
      |       using vInc vIncSlo vHiInd kAnyAdm dom tPos accRange by auto;
      |       !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |       using indCGDHBndA by auto;
      |       !indCGDLBndA:(vl <= v)
      |       using vInc vLoInd kAnyAdm dom tPos accRange csg by auto;
      |       !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |       using indCGDLBndA by auto;
      |       !indCSG:(controllableSpeedGoal(vl,vh))
      |       using vInc vIncSlo csg by auto;
      |       note indStepA = andI(andI(andI(andI(andI(indVPos, indIsAnn),
      |       indOnAnn), indCSG), indCGDH), indCGDL);
      |       !indAssert:(J(xg, yg, k, v, vl, vh)) using indStepA by auto;}
      | case kNegAdm:(negBounds(xg,yg,v,vl,vh,a,k)) =>
      |   note kSgn = andEL(kNegAdm);
      |   note admL = andEL(andER(kNegAdm));
      |   note admH = andER(andER(kNegAdm));
      |   switch (accSgn) {
      |     case accNeg:(a<=0) =>
      |        print("CASE k<=0,a<=0");
      |        t := 0;
      |        { xg'=-v*k*yg, yg'=v*(k*xg-1), v'=a, t'=1
      |        & ?dom:(v >= 0 & t <= T);
      |        & !tPos:(t>=0) by induction;
      |        & !dLo:((k*(eps*eps)-2*eps) < k*(sq(xg)+sq(yg))-2*xg)
      |	using isAnn onAnn by induction;
      |        & !dHi:(k*(xg*xg+yg*yg)-2*xg < (k*sq(eps)+2*eps))
      |	using isAnn onAnn by induction;
      |        & !vBound:(v+a*(T-t)>=0) using tPos noBrake by induction;
      |        & !bigL:(((a<=0&vl<=v+a*(T-t))
      |                  |(1+2*eps*(-k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(vl)-sq(v+a*(T-t))))<=2*A*(yg-eps)
      |                  |(1+2*eps*(-k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(vl)-sq(v+a*(T-t))))<=2*A*((-xg)-eps)))
      |          using constA dom tPos dLo dHi vBound accHi noBrake csgIvl
      |	  csgHi uhp isAnn onAnn accSgn kSgn admL accNeg by induction;
      |        & !bigH:(((a<=0&v<=vh)
      |                  |(1+2*eps*(-k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(v+a*(T-t))-sq(vh)))<=2*B*(yg-eps)
      |                  |(1+2*eps*(-k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(v+a*(T-t))-sq(vh)))<=2*B*((-xg)-eps)))
      |using constB dom tPos dLo dHi vBound accRange noBrake csgIvl csgLo
      |uhp isAnn onAnn accSgn kSgn admH accNeg by induction;};
      |        ?xgSgnC:(xg<=0);
      |        !indVPos:(v >= 0) using dom by auto;
      |        !indIsAnn:(isAnnulus(k)) using isAnn by auto;
      |        !indOnAnn:(onAnnulus(xg,yg,k)) using onAnn dLo dHi by auto;
      |        print("After ODE, CASE k<=0,a<=0");
      |        switch(bigL) {
      |          case loA:((a<=0&vl<=v+a*(T-t))) =>
      |            print("loA<<");
      |            !lem:(vl <= v) using loA accNeg dom tPos by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn by auto;
      |          case loB:((1+2*eps*(-k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t))
      |	  )+(sq(vl)-sq(v+a*(T-t))))<=2*A*(yg-eps)) =>
      |            print("loB<<");
      |            !lem:((1 + 2*eps*(-k) + sq(eps*k)) * (sq(vl)-sq(v)) <=
      |	    (2*A) * (yg-eps))
      |              using const csgLo accRange vBound dom loB by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |          case loC:((1+2*eps*(-k)+sq(eps*k))*(A*(2*v*(T-t)+a*
      |	  (sq(T-t)))+(sq(vl)-sq(v+a*(T-t))))<=2*A*((-xg)-eps)) =>
      |            print("loC<<");
      |            !lem:((1 + 2*eps*(-k) + sq(eps*k)) * (sq(vl)-sq(v)) <=
      |	    (2*A) * (-xg-eps))
      |              using const csgLo accRange vBound  dom  loC by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |        }
      |        switch(bigH) {
      |          case hiA:((a<=0&v<=vh)) =>
      |            print("hiA<<");
      |            !lem:(v <= vh) using hiA by prop;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn by auto;
      |          case hiB:((1+2*eps*(-k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t))
      |	  )+(sq(v+a*(T-t))-sq(vh)))<=2*B*(yg-eps)) =>
      |            print("hiB<<");
      |            !lem:((1 + 2*eps*(-k) + sq(eps*k)) * (sq(v)-sq(vh)) <=
      |	    (2*B) * (yg-eps))
      |              using const csgHi accRange vBound dom  hiB by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |          case hiC:((1+2*eps*(-k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t))
      |	  )+(sq(v+a*(T-t))-sq(vh)))<=2*B*((-xg)-eps)) =>
      |            print("hiC<<");
      |            !lem:((1 + 2*eps*(-k) + sq(eps*k)) * (sq(v)-sq(vh)) <=
      |	    (2*B) * (-xg-eps))
      |              using const csgHi accRange vBound dom hiC by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;}
      |        !indCSG:(controllableSpeedGoal(vl,vh)) using csg by auto;
      |        note indStepC = andI(andI(andI(andI(andI(indVPos, indIsAnn),
      |	indOnAnn), indCSG), indCGDH), indCGDL);
      |        !indAssert:(J(xg, yg, k, v, vl, vh)) using indStepC by auto;
      |     case accPos:(a>=0) =>
      |        print("CASE k<=0,a>=0");
      |        t := 0;
      |        { xg'=-v*k*yg, yg'=v*(k*xg-1), v'=a, t'=1
      |        & ?dom:(v >= 0 & t <= T);
      |        & !tPos:(t>=0) by induction;
      |        & !dLo:((k*(eps*eps)-2*eps) < k*(sq(xg)+sq(yg))-2*xg)
      |	using isAnn onAnn by induction;
      |        & !dHi:(k*(xg*xg+yg*yg)-2*xg < (k*sq(eps)+2*eps))
      |	using isAnn onAnn by induction;
      |        & !vBound:(v+a*(T-t)>=0) using tPos noBrake by induction;
      |        & !bigL:(((a>=0&v>=vl)
      |                  |(1+2*eps*(-k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(vl)-sq(v+a*(T-t))))<=2*A*(yg-eps)
      |                  |(1+2*eps*(-k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(vl)-sq(v+a*(T-t))))<=2*A*((-xg)-eps)))
      |using constA dom tPos dLo dHi vBound accHi noBrake csgIvl csgHi uhp
      |isAnn onAnn accSgn kSgn admL accPos by induction;
      |        & !bigH:(((a>=0&v+a*(T-t)<=vh)
      |                  |(1+2*eps*(-k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(v+a*(T-t))-sq(vh)))<=2*B*(yg-eps)
      |                  |(1+2*eps*(-k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(v+a*(T-t))-sq(vh)))<=2*B*((-xg)-eps)))
      |using constB dom tPos dLo dHi vBound accRange noBrake csgIvl csgLo
      |uhp isAnn onAnn accSgn kSgn admH accPos by induction;};
      |        ?xgSgnC:(xg<=0);
      |        !indVPos:(v >= 0) using dom by auto;
      |        !indIsAnn:(isAnnulus(k)) using isAnn by auto;
      |        !indOnAnn:(onAnnulus(xg,yg,k)) using onAnn dLo dHi by auto;
      |        print("After ODE, CASE k<=0,a>=0");
      |        switch(bigL) {
      |          case loA:(a>=0& v>= vl) =>
      |            print("loA<>");
      |            !lem:(vl <= v) using loA by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn by auto;
      |          case loB:((1+2*eps*(-k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)
      |	  ))+(sq(vl)-sq(v+a*(T-t))))<=2*A*(yg-eps)) =>
      |            print("loB<>");
      |            !lem:((1 + 2*eps*(-k) + sq(eps*k)) * (sq(vl)-sq(v)) <=
      |	    (2*A) * (yg-eps))
      |              using constA csgLo accRange vBound  dom  loB by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |          case loC:((1+2*eps*(-k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)
      |	  ))+(sq(vl)-sq(v+a*(T-t))))<=2*A*((-xg)-eps)) =>
      |            print("loC<>");
      |            !lem:((1 + 2*eps*(-k) + sq(eps*k)) * (sq(vl)-sq(v)) <=
      |	    (2*A) * (-xg-eps))
      |              using constA csgLo accRange vBound  dom  loC by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;}
      |        switch(bigH) {
      |          case hiA:(a>=0&v+a*(T-t)<=vh) =>
      |            print("hiA<>");
      |            !lem:(v <= vh)
      |            using hiA accPos dom tPos by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn by auto;
      |          case hiB:((1+2*eps*(-k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t))
      |	  )+(sq(v+a*(T-t))-sq(vh)))<=2*B*(yg-eps)) =>
      |            print("hiB<>");
      |            !lem:((1 + 2*eps*(-k) + sq(eps*k)) * (sq(v)-sq(vh)) <=
      |	    (2*B) * (yg-eps))
      |              using constB csgHi accRange vBound dom  hiB by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |          case hiC:((1+2*eps*(-k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t))
      |	  )+(sq(v+a*(T-t))-sq(vh)))<=2*B*((-xg)-eps)) =>
      |            print("hiC");
      |            !lem:((1 + 2*eps*(-k) + sq(eps*k)) * (sq(v)-sq(vh)) <=
      |	    (2*B) * (-xg-eps))
      |              using constB csgHi accRange vBound dom hiC by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;}
      |        !indCSG:(controllableSpeedGoal(vl,vh)) using csg by auto;
      |        note indStepC = andI(andI(andI(andI(andI(indVPos, indIsAnn),
      |	indOnAnn), indCSG), indCGDH), indCGDL);
      |        !indAssert:(J(xg, yg, k, v, vl, vh)) using indStepC by auto;}
      | case kPosAdm:(posBounds(xg,yg,v,vl,vh,a,k)) =>
      |   note kSgn = andEL(kPosAdm);
      |   note admL = andEL(andER(kPosAdm));
      |   note admH = andER(andER(kPosAdm));
      |   switch (accSgn) {
      |     case accNeg:(a<=0) =>
      |        print("CASE k>=0,a<=0");
      |        t := 0;
      |        { xg'=-v*k*yg, yg'=v*(k*xg-1), v'=a, t'=1
      |        & ?dom:(v >= 0 & t <= T);
      |        & !tPos:(t>=0) by induction;
      |        & !dLo:((k*(eps*eps)-2*eps) < k*(sq(xg)+sq(yg))-2*xg)
      |	using isAnn onAnn by induction;
      |        & !dHi:(k*(xg*xg+yg*yg)-2*xg < (k*sq(eps)+2*eps))
      |	using isAnn onAnn by induction;
      |        & !vBound:(v+a*(T-t)>=0) using tPos noBrake by induction;
      |        & !bigL:(((a<=0&vl<=v+a*(T-t))
      |                  |(1+2*eps*(k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(vl)-sq(v+a*(T-t))))<=2*A*(yg-eps)
      |                  |(1+2*eps*(k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |		  +(sq(vl)-sq(v+a*(T-t))))<=2*A*((xg)-eps)))
      |          using constA dom tPos dLo dHi vBound accHi noBrake csgIvl
      |	  csgHi uhp isAnn onAnn accSgn kSgn admL accNeg by induction;
      |        & !bigH:(((a<=0&v<=vh)
      |                  |(1+2*eps*(k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))+
      |		  (sq(v+a*(T-t))-sq(vh)))<=2*B*(yg-eps)
      |                  |(1+2*eps*(k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))+
      |		  (sq(v+a*(T-t))-sq(vh)))<=2*B*((xg)-eps)))
      |          using constB dom tPos dLo dHi vBound accRange noBrake csgIvl
      |csgLo uhp isAnn onAnn accSgn kSgn admH accNeg by induction;};
      |        ?xgSgnC:(xg>=0);
      |        !indVPos:(v >= 0) using dom by auto;
      |        !indIsAnn:(isAnnulus(k)) using isAnn by auto;
      |        !indOnAnn:(onAnnulus(xg,yg,k)) using onAnn dLo dHi by auto;
      |        print("After ODE, CASE k>=0,a<=0");
      |        switch(bigL) {
      |          case loA:((a<=0&vl<=v+a*(T-t))) =>
      |            print("loA><");
      |            !lem:(vl <= v) using loA accNeg dom tPos by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn by auto;
      |          case loB:((1+2*eps*(k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |	  +(sq(vl)-sq(v+a*(T-t))))<=2*A*(yg-eps)) =>
      |            print("loB><");
      |            !lem:((1 + 2*eps*(k) + sq(eps*k)) * (sq(vl)-sq(v)) <=
      |	    (2*A) * (yg-eps))
      |              using constA csgLo accRange vBound  dom  loB by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |          case loC:((1+2*eps*(k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |	  +(sq(vl)-sq(v+a*(T-t))))<=2*A*((xg)-eps)) =>
      |            print("loC><");
      |            !lem:((1 + 2*eps*(k) + sq(eps*k)) * (sq(vl)-sq(v)) <=
      |	    (2*A) * (xg-eps))
      |              using constA csgLo accRange vBound  dom  loC by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;}
      |        switch(bigH) {
      |          case hiA:((a<=0&v<=vh)) =>
      |            print("hiA<<");
      |            !lem:(v <= vh) using hiA by prop;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn by auto;
      |          case hiB:((1+2*eps*(k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))
      |	  +(sq(v+a*(T-t))-sq(vh)))<=2*B*(yg-eps)) =>
      |            print("hiB<<");
      |            !lem:((1 + 2*eps*(k) + sq(eps*k)) * (sq(v)-sq(vh)) <=
      |	    (2*B) * (yg-eps))
      |              using constB csgHi accRange vBound dom  hiB by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |          case hiC:((1+2*eps*(k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))
      |	  +(sq(v+a*(T-t))-sq(vh)))<=2*B*((xg)-eps)) =>
      |            print("hiC<<");
      |            !lem:((1 + 2*eps*(k) + sq(eps*k)) * (sq(v)-sq(vh)) <=
      |	    (2*B) * (xg-eps))
      |              using constB csgHi accRange vBound dom hiC by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;}
      |        !indCSG:(controllableSpeedGoal(vl,vh)) using csg by auto;
      |        note indStepC = andI(andI(andI(andI(andI(indVPos, indIsAnn),
      |	indOnAnn), indCSG), indCGDH), indCGDL);
      |        !indAssert:(J(xg, yg, k, v, vl, vh)) using indStepC by auto;
      |     case accPos:(a>=0) =>
      |        print("CASE k>=0,a>=0");
      |        t := 0;
      |        { xg'=-v*k*yg, yg'=v*(k*xg-1), v'=a, t'=1
      |        & ?dom:(v >= 0 & t <= T);
      |        & !tPos:(t>=0) by induction;
      |        & !dLo:((k*(eps*eps)-2*eps) < k*(sq(xg)+sq(yg))-2*xg)
      |	using isAnn onAnn by induction;
      |        & !dHi:(k*(xg*xg+yg*yg)-2*xg < (k*sq(eps)+2*eps))
      |	using isAnn onAnn by induction;
      |        & !vBound:(v+a*(T-t)>=0) using tPos noBrake by induction;
      |        & !bigL:(((a>=0&v>=vl)
      |                  |(1+2*eps*(k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))+
      |		  (sq(vl)-sq(v+a*(T-t))))<=2*A*(yg-eps)
      |                  |(1+2*eps*(k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))+
      |		  (sq(vl)-sq(v+a*(T-t))))<=2*A*((xg)-eps)))
      |          using constA dom tPos dLo dHi vBound accHi noBrake csgIvl
      |	  csgHi uhp isAnn onAnn accSgn kSgn admL accPos by induction;
      |        & !bigH:(((a>=0&v+a*(T-t)<=vh)
      |                  |(1+2*eps*(k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))+
      |		  (sq(v+a*(T-t))-sq(vh)))<=2*B*(yg-eps)
      |                  |(1+2*eps*(k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))+
      |		  (sq(v+a*(T-t))-sq(vh)))<=2*B*((xg)-eps)))
      |          using constB dom tPos dLo dHi vBound accRange noBrake
      |csgIvl csgLo uhp isAnn onAnn accSgn kSgn admH accPos by induction;};
      |        ?xgSgnC:(xg>=0);
      |        !indVPos:(v >= 0) using dom by auto;
      |        !indIsAnn:(isAnnulus(k)) using isAnn by auto;
      |        !indOnAnn:(onAnnulus(xg,yg,k)) using onAnn dLo dHi by auto;
      |        print("After ODE, CASE k<=0,a<=0");
      |        switch(bigL) {
      |          case loA:(a>=0&v>=vl) =>
      |            print("loA><");
      |            !lem:(vl <= v) using loA by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn by auto;
      |          case loB:((1+2*eps*(k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |	  +(sq(vl)-sq(v+a*(T-t))))<=2*A*(yg-eps)) =>
      |            print("loB><");
      |            !lem:((1 + 2*eps*(k) + sq(eps*k)) * (sq(vl)-sq(v)) <=
      |	    (2*A) * (yg-eps))
      |              using constA csgLo accRange vBound dom  loB by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |          case loC:((1+2*eps*(k)+sq(eps*k))*(A*(2*v*(T-t)+a*(sq(T-t)))
      |	  +(sq(vl)-sq(v+a*(T-t))))<=2*A*((xg)-eps)) =>
      |            print("loC><");
      |            !lem:((1 + 2*eps*(k) + sq(eps*k)) * (sq(vl)-sq(v)) <=
      |	    (2*A) * (xg-eps))
      |              using constA csgLo accRange vBound dom  loC by auto;
      |            !indCGDL:(controllableGoalDist(vl,v,A,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;}
      |        switch(bigH) {
      |          case hiA:(a>=0&v+a*(T-t)<=vh) =>
      |            print("hiA><");
      |            !lem:(v <= vh)
      |            using hiA accPos dom tPos by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn by auto;
      |          case hiB:((1+2*eps*(k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))
      |	  +(sq(v+a*(T-t))-sq(vh)))<=2*B*(yg-eps)) =>
      |            print("hiB><");
      |            !lem:((1 + 2*eps*(k) + sq(eps*k)) * (sq(v)-sq(vh))
      |	    <= (2*B) * (yg-eps))
      |              using constB csgHi accRange vBound dom  hiB by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;
      |          case hiC:((1+2*eps*(k)+sq(eps*k))*(B*(2*v*(T-t)+a*(sq(T-t)))
      |	  +(sq(v+a*(T-t))-sq(vh)))<=2*B*((xg)-eps)) =>
      |            print("hiC><");
      |            !lem:((1 + 2*eps*(k) + sq(eps*k)) * (sq(v)-sq(vh))
      |	    <= (2*B) * (xg-eps))
      |              using constB csgHi accRange vBound dom hiC by auto;
      |            !indCGDH:(controllableGoalDist(v,vh,B,xg,yg,k))
      |	    using lem kSgn xgSgnC by auto;}
      |        !indCSG:(controllableSpeedGoal(vl,vh)) using csg by auto;
      |        note indStepC = andI(andI(andI(andI(andI(indVPos, indIsAnn),
      |	indOnAnn), indCSG), indCGDH), indCGDL);
      |        !indAssert:(J(xg, yg, k, v, vl, vh)) using indStepC by auto;}}
      | !fullIndStep:(J(xg, yg, k, v, vl, vh)) using indAssert by prop;}*
      |!safe:(sq(xg) + sq(yg) <= sq(eps) -> vl <= v & v <= vh)
      |using inv const by auto;
      |
      |""".stripMargin

  val knownFeatureRequests: List[String] = List(labelOldEq)
  val knownBugs: List[String] = List(labelOldestEq)
  val maybeBugs: List[String] = List(
    odeForwardGhostInsideInverse,
    odeInverseGhostInsideForward,
    discreteForwardGhostInsideInverse,
    discreteInverseGhostInsideForward
  )

  val thesisExtra: List[String] = List(
    basicForConv,
    basicReachAvoid,
    letEvalAtUse, demonicLoopConst,
    forwardHypotheticalUnsolvable,switchLiteralArg,  switchLiterals
    , inverseGhostODE,  superfluousGhost
  )

  val thesisExamples: List[String] = List(
    assertOnePos,
    assertBranchesNonzero,
    switchLiteralArgAlternate,
    noteAndSquare,
    squareNonneg,
    squareNonnegAlt,
    propSkipsQE,
    annotatedAssign,
    demonicLoop,
    straightODE,
    justxSolODE,
    solAgainODE,
    inductODE,
    inductODEBC,
    durationODE,
    ghostAssert,
    ghostAssign,
    ghostODE,
    inverseGhostODECircle,
    labelInit,
    labelOld,
    unwindBlock,
    intoChoice,
    outOfChoice,
    forwardHypothetical,
    printSolution,
    sandboxExample,
    revisedReachAvoidFor)


  val pldiExamples: List[String] = List(pldiModelSafeFull, pldiModelSafeSimple, pldiSandboxSafe)

  val thesisCaseStudies: List[String] =
    List(
      pldiModelSafeFull,
      pldiAngelicSandbox,
      pldiTimedAngelicControl,
      pldiReachAvoid,
      pldiReachAvoidDisturbance,
      ijrrStaticSafetySimplified,
      ralWaypointSafety
    )

  val allThesis = thesisExamples ++ thesisCaseStudies
  //pldiExamples ++ rssExamples ++ ijrrModels
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
    """y:=x@theEnd;
    |{x:= 1; ++ x := 2;}
    |theEnd:""".stripMargin

  val referenceOverStar: String =
    """ x := y@theEnd;
      | y := *;
      | theEnd:
      |""".stripMargin

  val referenceOverODE: String =
    """x := y@theEnd;
      |y := 0;
      |{y' = 2 & y <= 5}
      |theEnd:""".stripMargin

  val thesisCounterexamples: List[String] = List(cyclicLabel, referenceOverChoice, referenceOverStar, referenceOverODE)
}
