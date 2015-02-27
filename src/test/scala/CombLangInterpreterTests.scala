import edu.cmu.cs.ls.keymaera.core.{Sequent, RootNode}
import edu.cmu.cs.ls.keymaera.tacticsinterface.{CLInterpreter, CLParser}
import testHelper.StringConverter._

/**
 * Created by nfulton on 2/26/15.
 */
class CombLangInterpreterTests extends TacticTestSuite {
  "CLInterpreter" should "not choke" in {
    val t = CLInterpreter.construct(CLParser("NilT & NilT").get)
    val n = new RootNode(
      Sequent(Nil, scala.collection.immutable.IndexedSeq("1=1".asFormula), scala.collection.immutable.IndexedSeq("1=1".asFormula))
    )
    helper.runTactic(t,n)
  }

  "CLInterpreter" should "hello, world!" in {
    val t = CLInterpreter.construct(CLParser("NilT & NilT & AxiomCloseT").get)
    val n = new RootNode(
      Sequent(Nil, scala.collection.immutable.IndexedSeq("1=1".asFormula), scala.collection.immutable.IndexedSeq("1=1".asFormula))
    )
    helper.runTactic(t,n)
    n.isClosed() shouldBe true
  }
}
