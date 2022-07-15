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

  it should "print and reparse interpreted function definitions" in {
    val entry = ArchiveParser(
      """ArchiveEntry "exp"
        |Definitions implicit Real e(Real t) = {{e:=1;t:=2;}; {e'=-e,t'=1}};
        |End.
        |ProgramVariables Real x; End.
        |Problem e(x) > 0
        |End.
        |End.""".stripMargin).head
    val printed = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments=false)(entry)
    printed shouldBe
      s"""/* Exported from KeYmaera X v${edu.cmu.cs.ls.keymaerax.core.VERSION} */
        |
        |Theorem "exp"
        |Definitions
        |  Real e(Real x_0) = ( e<< <{e:=._0;t:=._1;}{{e'=--e,t'=-1}++{e'=-e,t'=1}}>(e=1&t=2) >>(x_0) );
        |End.
        |
        |ProgramVariables
        |  Real x;
        |End.
        |
        |Problem
        |  e(x)>0
        |End.
        |
        |
        |End.""".stripMargin
    ArchiveParser(printed).head.expandedModel shouldBe entry.expandedModel
  }

  it should "not repeat builtin interpreted function definitions" in {
    val entry = ArchiveParser(
      """ArchiveEntry "arctan"
        |Definitions
        |  implicit Real arctan(Real t) = {{arctan:=0;t:=0;}; {arctan'=1/(1+t^2),t'=1}};
        |  Real tan(Real x) = sin(x)/cos(x);
        |  Real x;
        |End.
        |
        |Problem
        |  arctan(tan(x)) = x
        |End.
        |End.""".stripMargin).head
    val printed = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80), withComments=false)(entry)
    printed should equal (
      s"""/* Exported from KeYmaera X v${edu.cmu.cs.ls.keymaerax.core.VERSION} */
         |Theorem "arctan"
         |Definitions
         |  Real arctan(Real x_0) = ( arctan<< <{arctan:=._0;t:=._1;}{{arctan'=-1/(1+t^2),t'=-1}++{arctan'=1/(1+t^2),t'=1}}>(arctan=0&t=0) >>(x_0) );
         |  Real tan(Real x_0) = ( sin(x_0)/cos(x_0) );
         |  Real x();
         |End.
         |
         |Problem
         |  arctan(tan(x()))=x()
         |End.
         |End.
         |""".stripMargin) (after being whiteSpaceRemoved)
    ArchiveParser(printed).head.expandedModel shouldBe entry.expandedModel
  }

}
