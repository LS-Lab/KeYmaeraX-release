package com.wolfram.jlink;

import java.math.BigDecimal;
import java.math.BigInteger;

/**
 * Compile-only stub of com.wolfram.jlink.Expr, used to build KeYmaera X without
 * a Mathematica/Wolfram Engine installation. Any real JLink dependency should be
 * avoided: these classes are never meant to be exercised at runtime.
 *
 * The API surface mirrors exactly what KeYmaera X's main sources use.
 */
public class Expr {
  // Type code constants (as in the real JLink API)
  public static final int SYMBOL = 1;
  public static final int INTEGER = 2;
  public static final int REAL = 3;
  public static final int STRING = 4;
  public static final int BOOLEAN = 5;
  public static final int FUNCTION = 6;
  public static final int COMPLEX = 7;
  public static final int INVALID = 8;
  public static final int BIGINT = 9;
  public static final int BIGREAL = 10;

  // Expression-valued constants (used directly as Expr values by KeYmaera X)
  public static final Expr SYM_TRUE = new Expr(BOOLEAN, true);
  public static final Expr SYM_FALSE = new Expr(BOOLEAN, false);
  public static final Expr SYM_LIST = new Expr(FUNCTION, "List");
  public static final Expr SYM_RATIONAL = new Expr(COMPLEX, "Rational");

  public Expr() {}

  public Expr(int head, String value) {}

  public Expr(int head, boolean value) {}

  public Expr(int i) {}

  public Expr(long l) {}

  public Expr(double d) {}

  public Expr(boolean b) {}

  public Expr(String s) {}

  public Expr(BigInteger bi) {}

  public Expr(BigDecimal bd) {}

  public Expr(Expr head, Expr[] args) {}

  // Type tests
  public boolean symbolQ() { return false; }
  public boolean numberQ() { return false; }
  public boolean integerQ() { return false; }
  public boolean realQ() { return false; }
  public boolean rationalQ() { return false; }
  public boolean complexQ() { return false; }
  public boolean stringQ() { return false; }
  public boolean booleanQ() { return false; }
  public boolean listQ() { return false; }
  public boolean vectorQ() { return false; }
  public boolean matrixQ() { return false; }

  // Accessors
  public int asInt() { return 0; }
  public long asLong() { return 0L; }
  public double asDouble() { return 0.0; }
  public boolean asBoolean() { return false; }
  public String asString() { return ""; }
  public java.math.BigDecimal asBigDecimal() { return java.math.BigDecimal.ZERO; }
  public java.math.BigInteger asBigInteger() { return java.math.BigInteger.ZERO; }

  public Expr head() { return this; }

  public Expr[] args() { return new Expr[0]; }

  public void dispose() {}

  // Type tests (continued)
  public boolean bigDecimalQ() { return false; }
  public boolean bigIntegerQ() { return false; }

  @Override
  public boolean equals(Object that) { return this == that; }

  @Override
  public int hashCode() { return 0; }

  @Override
  public String toString() { return ""; }
}
