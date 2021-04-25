/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.macros.{Axiom, AxiomDisplayInfo, AxiomInfo, DifferentialAxiomInfo, DisplayInfo, SimpleDisplayInfo}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig}
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.ToolOperationManagement
import org.scalatest.LoneElement._
import org.scalatest.time.SpanSugar._
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, SlowTest, TodoTest}

import scala.collection.immutable._
import scala.language.postfixOps
import scala.reflect.io.File

/**
 * Tests for implicit function definitions & the involved substitutions.
 * @author James Gallicchio
 */
class ImplicitFunctionTests extends TacticTestBase {


  """
  Axiom "exp' derive exp"
  (exp(f(||)))' = f(||)' * exp(f(||))
  End.

  sqrt(2)=a <-> a^2 = 2


  ----
  \forall x \exists e exp(e,x)
  """

  "chase" should "use registered implicit differentials" in withMathematica { _ =>
    val exp = "e(x)".asTerm.asInstanceOf[FuncOf]
    val diff = "e(x)*(x)'".asTerm
    AxIndex.implFuncDiffs(Function("e", None, Real, Real)) =
      DifferentialAxiomInfo(
        funcName = "e",
        funcOf = exp,
        diff = diff,
        theRecursor = (1::Nil)::Nil
      )
    /* (e(x))' = e(x) * (x)' */
    val fml = "[y':=1;](e(y))' = e(y)*y'".asFormula
    val proof = proveBy(fml, chase(1,1::0::Nil) & chase(1) & QE)
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
  }

}
