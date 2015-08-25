/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tools


class ConversionException(s:String)
  extends Exception(s)
class MathematicaComputationFailedException(e:com.wolfram.jlink.Expr)
  extends ConversionException(e.toString)
class MathematicaComputationAbortedException(e:com.wolfram.jlink.Expr)
  extends ConversionException(e.toString)

