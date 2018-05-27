package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.SuccPos
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.UsualTest

/**
 * Tests invariant generators.
 * [[edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator]].
 */
@UsualTest
class InvariantGeneratorTests extends TacticTestBase {

  "Loop invariants" should "be generated from pre and postconditions" in {
    InvariantGenerator.loopInvariantGenerator("x>=1 ==> [{x:=x+1;}*][x:=x+1;]x>=2".asSequent, SuccPos(0)).toList should
      contain theSameElementsAs("[x:=x+1;]x>=2".asFormula::"x>=1".asFormula::Nil)
  }

  "Differential invariant generator" should "use Pegasus lazily" in {
    //@note pegasusInvariantGenerator asks ToolProvider.invGenTool

    val mockProvider = new NoneToolProvider {
      var requestedInvGenerators: List[Option[String]] = Nil
      override def invGenTool(name: Option[String]): Option[InvGenTool] = {
        requestedInvGenerators = requestedInvGenerators :+ name
        super.invGenTool(name)
      }
    }

    ToolProvider.setProvider(mockProvider)

    val gen = InvariantGenerator.differentialInvariantGenerator("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0))
    mockProvider.requestedInvGenerators shouldBe 'empty
    gen should not be 'empty
    gen.head shouldBe "x>0".asFormula
  }

  it should "not fail if Mathematica is unavailable" in {
    val gen = InvariantGenerator.pegasusInvariants("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0))
    gen shouldBe 'empty
  }

  it should "use Pegasus if available" in withMathematica { _ =>
    val gen = InvariantGenerator.pegasusInvariants("x>0 ==> [{x'=x^2&true}]x>=0".asSequent, SuccPos(0))
    gen should not be 'empty
    gen.head shouldBe "x>=0".asFormula
  }

  "Auto with invariant generator" should "prove simple loop from precondition invariant" in withQE { _ =>
    proveBy("x=0 -> [{x:=-x;}*]x>=0".asFormula, auto) shouldBe 'proved
  }

  it should "prove simple loop from postcondition invariant" in withQE { _ =>
    proveBy("x=1 -> [{x:=x+1;}*]x>=1".asFormula, auto) shouldBe 'proved
  }

}
