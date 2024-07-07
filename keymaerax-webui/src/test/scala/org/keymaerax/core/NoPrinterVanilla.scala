/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.core

import org.scalatest.flatspec.AnyFlatSpec

/**
 * Tests printing for no pretty printer in vanilla configuration.
 *
 * @author
 *   Andre Platzer
 */
class NoPrinterVanilla extends AnyFlatSpec {
  "No Pretty Printer" should "use default printer" in { PrettyPrinter.printer(Number(42)) }
}
