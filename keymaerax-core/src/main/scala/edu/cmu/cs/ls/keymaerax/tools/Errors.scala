/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.ProverException

/** Arithmetic tool exceptions */
case class ToolException(msg: String, cause: Throwable = null) extends ProverException(msg, cause)

/** Reports errors converting to/from a tool. */
class ConversionException(s: String) extends Exception(s)

/** Reports Mathematica computation failures ($Failed). */
class MathematicaComputationFailedException(msg: String) extends ConversionException(msg)

/** Internal abort of computations (e.g., by TimeConstrained, by $Abort). */
class MathematicaComputationAbortedException(msg: String) extends ConversionException(msg)

/** Externally triggered abort (e.g., by stopping from the UI). */
class MathematicaComputationExternalAbortException(msg: String) extends ConversionException(msg)

/** Reports errors converting to/from SMTLib format. */
class SMTConversionException(s: String) extends ConversionException(s)

/** Reports errors on QE. */
//@todo improve exception hierarchy
class SMTQeException(s: String) extends Exception(s)
