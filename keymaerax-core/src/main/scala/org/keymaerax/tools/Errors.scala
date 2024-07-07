/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tools

import org.keymaerax.core.ProverException

/** Tool exceptions. */
abstract class ToolException(msg: String, cause: Throwable) extends ProverException(msg, cause)

/** Errors raised from the KeYmaera X side of the tool interaction. */
abstract class ToolInternalException(msg: String, cause: Throwable) extends ToolException(msg, cause)

/** Errors raised from the external tool. */
abstract class ToolExternalException(msg: String, cause: Throwable) extends ToolException(msg, cause)

/** Critical errors requiring the external tool or even KeYmaera X to be restarted. */
abstract class ToolCriticalException(msg: String, cause: Throwable) extends ToolException(msg, cause)

/** Reports internal errors converting to/from a tool. */
case class ConversionException(msg: String, cause: Throwable = null) extends ToolInternalException(msg, cause)

/** Internal errors when setting up tools, communicating commands, etc. */
case class ToolCommunicationException(msg: String, cause: Throwable = null) extends ToolInternalException(msg, cause)

/** External execution errors when setting up tool, starting, executing commands, shutdown etc. */
case class ToolExecutionException(msg: String, cause: Throwable = null) extends ToolExternalException(msg, cause)

/** User-triggered abort (e.g., by stopping from the UI). */
case class MathematicaComputationUserAbortException(msg: String) extends ToolInternalException(msg, null)

/** Abort of external computations (e.g. by $Abort). */
case class MathematicaComputationAbortedException(msg: String, cause: Throwable = null)
    extends ToolExternalException(msg, cause)

/** Time out of external computations (e.g. by TimeConstrained) */
case class MathematicaComputationTimedOutException(msg: String, cause: Throwable = null)
    extends ToolInternalException(msg, cause)

/** Abort of external computation due to inapplicable methods. */
case class MathematicaInapplicableMethodException(msg: String, cause: Throwable = null)
    extends ToolExternalException(msg, cause)

/** Reports external Mathematica computation failures ($Failed). */
case class MathematicaComputationFailedException(msg: String, cause: Throwable = null)
    extends ToolExternalException(msg, cause)

/** Critical Mathlink errors that require restarting Mathematica. */
case class MathematicaMathlinkException(msg: String, cause: Throwable = null) extends ToolCriticalException(msg, cause)

/** Critical Mathematica exceptions that require restarting due to unknown external cause. */
case class MathematicaUnknownCauseCriticalException(msg: String) extends ToolCriticalException(msg, null)

/** Reports QE errors from Z3. */
case class SMTQeException(msg: String, cause: Throwable = null) extends ToolExternalException(msg, cause)

/** Reports timeouts from Z3. */
case class SMTTimeoutException(msg: String, cause: Throwable = null) extends ToolInternalException(msg, cause)
