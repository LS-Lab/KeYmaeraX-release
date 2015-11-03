/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, PosInExpr, RootNode, SuccPosition, FOQuantifierTacticsImpl,
  Interpreter, Tactics}
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.ProofFactory._
import testHelper.SequentFactory._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{locateSucc,locateAnte,NotLeftT,NotRightT}
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.{uniquify,instantiateExistentialQuanT,
  instantiateUniversalQuanT,instantiateT,existentialGenT,existentialGenPosT,existSubstitute,vacuousExistentialQuanT,
  vacuousUniversalQuanT,decomposeQuanT,allEliminateT}

import scala.collection.immutable.Map

/**
 * @author Stefan Mitsch
 */
class FooTests extends FlatSpec with Matchers with BeforeAndAfterEach {

 val theInterpreter = SequentialInterpreter()

 override def beforeEach() = {
   PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
 }

 "A failing tactic" should "print nice errors" in {
   val itFails = new BuiltInTactic("fails") {
     override def result(provable: Provable) = throw new BelleError("I don't want to compute today...")
   }

   theInterpreter.apply(Idioms.nil
     & itFails
     & Idioms.nil, BelleProvable(Provable.startProof("1=1".asFormula)))
 }
}