import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic
import edu.cmu.cs.ls.keymaerax.tactics.{RootNode, Interpreter, Config}
import edu.cmu.cs.ls.keymaerax.tacticsinterface.{CLInterpreter, CLParser}

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

  it should "hello, world!" in {
    val t = CLInterpreter.construct(CLParser("NilT & NilT & AxiomCloseT").get)
    val n = new RootNode(
      Sequent(Nil, scala.collection.immutable.IndexedSeq("1=1".asFormula), scala.collection.immutable.IndexedSeq("1=1".asFormula))
    )
    helper.runTactic(t,n)
    n.isClosed() shouldBe true
  }

  it should "cut" in {
    val t = CLInterpreter.construct(CLParser("cutT(\"1 > 0\")").get)
    val n = new RootNode(Sequent(Nil,scala.collection.immutable.IndexedSeq("x>1".asFormula),scala.collection.immutable.IndexedSeq("x>0".asFormula)))
    helper.runTactic(t, n)
    helper.report(n)
  }

  it should "parse onLabel in the paper's format" in {
    val tactic = "onLabel((\"example 1\", Master))"
    CLParser(tactic).getOrElse(fail("failed to parse!"))
  }

  it should "paper example" in {
    val paperTactic = """ImplyRight & Loop("v>=0") & onLabel(
                        ("base case", Master),
                        ("induction step", ImplyRight & Seq & Choice & AndRight &&
                        (Assign & ODESolve & Master,
                        Assign & ODESolve & Master) ),
                        ("use case", Master)
                        )"""
    val t : Tactic = CLInterpreter.construct(CLParser(paperTactic).get)
  }

}
