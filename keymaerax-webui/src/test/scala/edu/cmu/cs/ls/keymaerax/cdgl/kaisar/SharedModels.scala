package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

/** Kaisar models/proofs which are used in multiple test suites, e.g. Kaisar and ProofPlex. */
object SharedModels {
  val essentialsSafeCar1D: String =
    "?(xInit, vInit):(x:=0;v:=0); ?(acc, brk, tstep, separate):(A > 0 & B > 0 & T > 0 & x < d);" +
    "!inv:(v^2/(2*B) <= (d - x) & v >= 0) using xInit vInit brk separate by auto;" +
    "{{switch {" +
    "case accel: ((v + T*A)^2/(2*B) <= (d - (x + v*T + (A*T^2)/2))) =>" +
    "  ?accA:(a := A);" +
    "  !safe1:((v + T*a)^2/(2*B) <= (d - (x + v*T + (a*T^2)/2))) using accel acc accA inv brk tstep ... by auto;" +
    "  note safeAcc = andI(safe1, accA);" +
    "case brake: ((v + T*A)^2/(2*B)  + 1 >= (d - (x + v*T + (A*T^2)/2))) =>" +
    "  ?accB:(a := -B);" +
    "  ?fast:(v >= B*T);" +
    "  !safe2:((v + T*a)^2/(2*B) <= (d - (x + v*T + (a*T^2)/2))) using brake acc accB brk inv tstep fast ... by auto;" +
    "  note safeAcc = andI(safe2, andI(accB, fast));" +
    "}}" +
    "t:= 0;" +
    "{xSol: x' = v, vSol: v' = a, tSol: t' = 1 & ?dc: (t <= T & v>=0);};" +
    "!invStep: (v^2/(2*B) <= (d - x) & v>= 0) " +
    "using xSol vSol tSol safeAcc inv dc acc brk tstep by auto;" +
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
      |!xFinal:(x <= 4);
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


  // @TODO: Fails because we need to look up IH during While() checking, which requires WhileProgress constructor
  val basicReachAvoid: String =
    """?(eps > 0 &  x = 0 & T > 0);
      |while (x + eps <= goal) {
      |  vel := (goal - (x + eps))/T;
      |  t := 0;
      |  {t' = 1, x' = vel & ?time:(t <= T);};
      |  /-- !safe:(x >= 0);  --/
      |  ?(t >= T/2);
      |  !live:(x + eps <= goal) using time ... by auto;
      |}
      |""".stripMargin

  // @TODO: something is super unsound with x1 = x0


  // @TODO: Check SB() vs SB parenthesis... hmm...
  // @TODO: DefaultSelector needs to be smarter when mixed with defined symbols like safe()
  val forwardHypothetical: String =
    """?init:(T > 0 & A > 0 & B > 0);
      |let SB() = v^2/(2*B);
      |let safe() <-> SB() <= (d-x);
      |?initSafe:(safe());
      |{
      |  {acc := *; ?env:(-B <= acc & acc <= A & safe()@ode(T));}
      |   t:= 0;
      |  {tSol: t' = 1, xSol: x' = v, vSol: v' = acc & ?time:(t <= T); & ?vel:(v >= 0);};
      |ode(t):
      |   !step:(safe()) using env init time vel xSol vSol tSol by auto;
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

  val thesisExamples: List[String] = List(assertOnePos, assertBranchesNonzero, switchLiterals, noteAnd, squareNonneg,
    propSkipsQE, annotatedAssign, demonicLoop, straightODE, inductODE, inductODEBC, durationODE, ghostAssert,
    ghostAssign, ghostODE, inverseGhostODE,  superfluousGhost, labelInit, labelOld, unwindBlock,
    intoChoice, outOfChoice, printSolution, forwardHypothetical, sandboxExample, basicReachAvoid)


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
