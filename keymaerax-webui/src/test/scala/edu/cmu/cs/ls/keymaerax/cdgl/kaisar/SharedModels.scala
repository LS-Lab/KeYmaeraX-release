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
    "{xSol: x' = v, vSol: v' = a, tSol: t' = 1 & ?dc: (t <= T & v>=0)};" +
    "!invStep: (v^2/(2*B) <= (d - x) & v>= 0) " +
    "using xSol vSol tSol safeAcc inv dc acc brk tstep ... by auto;" +
    "}*" +
    "!safe:(x <= d & v >= 0) using inv brk  by auto;"
}
