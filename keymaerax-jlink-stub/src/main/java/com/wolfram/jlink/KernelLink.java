package com.wolfram.jlink;

/**
 * Compile-only stub of the com.wolfram.jlink.KernelLink interface. See Expr.java
 * for an explanation. The API surface mirrors exactly what KeYmaera X's main
 * sources use; it is never exercised at runtime.
 */
public interface KernelLink {
  void connect() throws MathLinkException;
  void disconnect() throws MathLinkException;
  void close() throws MathLinkException;
  void discardAnswer() throws MathLinkException;
  void abortEvaluation() throws MathLinkException;
  void abandonEvaluation() throws MathLinkException;
  void terminateKernel();
  int newPacket() throws MathLinkException;
  void evaluate(String cmd) throws MathLinkException;
  void evaluate(Expr cmd) throws MathLinkException;
  int waitForAnswer() throws MathLinkException;
  Expr getExpr() throws MathLinkException;
}
