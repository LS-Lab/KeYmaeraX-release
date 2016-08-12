/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import org.scalatest.FlatSpec

/**
 * Tests printing for no pretty printer in vanilla configuration.
  *
 * @author Andre Platzer
 */
class NoPrinterVanilla extends FlatSpec {
  "No Pretty Printer" should "use default printer" in {PrettyPrinter.printer(Number(42))}
}
