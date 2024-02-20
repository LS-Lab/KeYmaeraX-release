/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.AdvocatusTest

/**
 * Interpreted functions / defined functions substitution tests.
 * @author Andre Platzer
 */
@AdvocatusTest
class InterpretedFunctionTest extends TacticTestBase {
  import TactixLibrary._

  "Interpreted / defined functions" should "not substitute abs" taggedAs(SummaryTest) in withMathematica { qeTool =>
    val wrong = "f(-1)=1".asFormula
    val intbase = "abs(-1)=1".asFormula
    val pr = proveBy(intbase, QE)
    pr shouldBe Symbol("proved")
    //@todo Either SubstitutionClashException or a result that isn't proved or isn't of the form wrong
    val pr2 = pr(USubst(SubstitutionPair(FuncOf(Function("abs",None,Real,Real,None),DotTerm()), FuncOf(Function("f",None,Real,Real),DotTerm())) :: Nil))
    pr2.conclusion shouldBe pr.conclusion
    pr2 shouldBe Symbol("proved")
    a [CoreException] shouldBe thrownBy (pr(USubst(SubstitutionPair(FuncOf(InterpretedSymbols.absF,DotTerm()), FuncOf(Function("f",None,Real,Real),DotTerm())) :: Nil)))
  }

  it should "not prove false 0=1 via substitution of abs" in withMathematica { qeTool =>
    val wrong = "0=1".asFormula
    val intbase = "abs(-1)=1".asFormula
    val pr = proveBy(intbase, QE)
    pr shouldBe Symbol("proved")
    //@todo Either SubstitutionClashException or a result that isn't proved or isn't of the form wrong
    val pr2 = pr(USubst(SubstitutionPair(FuncOf(Function("abs",None,Real,Real,None),DotTerm()), Number(0)) :: Nil))
    pr2.conclusion shouldBe pr.conclusion
    a [CoreException] shouldBe thrownBy(pr(USubst(SubstitutionPair(FuncOf(InterpretedSymbols.absF,DotTerm()), Number(0)) :: Nil)))
  }

  //@todo similarly for min, max
}
