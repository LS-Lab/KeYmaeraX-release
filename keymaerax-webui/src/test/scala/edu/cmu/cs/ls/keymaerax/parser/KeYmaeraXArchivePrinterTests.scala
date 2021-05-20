/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * Tests the archive printer.
  * Created by smitsch on 11/05/18.
  */
class KeYmaeraXArchivePrinterTests extends TacticTestBase {

  "Archive printer" should "not strip disjunctions at line beginning" in {
    val entry = ParsedArchiveEntry("Entry 1", "theorem",
      "Theorem \"Entry 1\" ProgramVariables Real A; Real b; Real x; End. Problem A>0\n|b>0 -> [x:=1;]x>=0 End. End.",
      "A>0\n|b>0 -> [x:=1;]x>=0", Declaration(Map.empty),
      "A>0 | b>0 -> [x:=1;]x>=0".asFormula, Nil, Nil, Map.empty)
    new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments=true)(entry) shouldBe
      s"""/* Exported from KeYmaera X v${edu.cmu.cs.ls.keymaerax.core.VERSION} */
        #
        #Theorem "Entry 1"
        #
        #ProgramVariables
        #  Real A;
        #  Real b;
        #  Real x;
        #End.
        #
        #Problem
        #  A>0
        #|b>0 -> [x:=1;]x>=0
        #End.
        #
        #
        #
        #End.""".stripMargin('#')
  }

}
