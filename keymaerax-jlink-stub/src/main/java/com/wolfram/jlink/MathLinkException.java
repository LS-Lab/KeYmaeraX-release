package com.wolfram.jlink;

/**
 * Compile-only stub of the com.wolfram.jlink.MathLinkException class. See
 * Expr.java for an explanation. It is used by KeYmaera X only in catch clauses
 * and as a cause for tool exceptions, so a trivial Exception subclass suffices.
 */
public class MathLinkException extends Exception {
  public MathLinkException() { super(); }
  public MathLinkException(String message) { super(message); }
  public MathLinkException(String message, Throwable cause) { super(message, cause); }

  public int getErrCode() { return 0; }
}
