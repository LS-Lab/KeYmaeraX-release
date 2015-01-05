import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.locateSucc
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tests
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{Matchers, FlatSpec}

/**
 * Created by nfulton on 12/1/14.
 *
 */
class DifferentialTests extends FlatSpec with Matchers {
  val helper = new ProvabilityTestHelper((x) => println(x))

  //Constants
  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  def d(e : Variable) = Derivative(Real, e)
  val one = Number(1)


  //Helper functions
  def parse(s:String) = new KeYmaeraParser().parseBareExpression(s).get.asInstanceOf[Formula]

  def formulaToSequent(formula : Formula) = {
    new Sequent(Nil, scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(formula))
  }

  def formulaToNode(formula : Formula) = {
    val sequent = new Sequent(Nil, scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(formula))
    new RootNode(sequent)
  }

  def report(pn : ProofNode) : Unit = {
    val report = pn.openGoals().map(goal => {
      "Open Goal: " + goal.sequent.toString() + "\n"
    })

    println(report.reduce(_ + _))
  }

  def checkResult(expectedFormula : Formula, result : ProofNode) = {
    val openGoals = result.openGoals()
    openGoals.length should be (1)
    val goal = openGoals.last

    goal.sequent.succ.length should be (1)
    println("Testing expected result against " + goal.sequent.succ.last.prettyString())
    goal.sequent.succ.last.equals(expectedFormula) should be (true)
  }

  def runDefault(pn : ProofNode) = runTactic(TacticLibrary.default, pn)

  //Running tactics
  val tool = new Mathematica()

  def runTactic(tactic : Tactic, rootNode : ProofNode) = {
    if(!tactic.applicable(rootNode)) {
      fail("runTactic was called on tactic " + tactic.name + ", but is not applicable on the node.")
    }

    //Dispatching the tactic.
    println("Dispatching tactic " + tactic.name)
    tactic.apply(tool, rootNode)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))

    println("beginning wait sequence for " + tactic.name)
    tactic.synchronized {
      tactic.registerCompletionEventListener(_ => tactic.synchronized(tactic.notifyAll));
      tactic.wait();
      tactic.unregister;
    }

    println("Ending wait sequence for " + tactic.name)
    println("Proof is closed: " + rootNode.isClosed())

    rootNode
  }

//  "The Scheduler" should "initialize without an ExceptionInInitializerError" in {
//    val asdf = new Scheduler(Seq.fill(Config.maxCPUs)(KeYmaera));
//    asdf
//
//    Tactics.KeYmaeraScheduler
//  }

  "True" should "close trivially" in {
    val formula = True

    val node = helper.formulaToNode(formula)
    runDefault(node)

    node.isClosed() should be (true)
  }

//  "Normal Assignment" should "work" in {
//    val formula = BoxModality(
//      Assign(
//        x,
//        one
//      ),
//      Equals(Real, x , one)
//    )
//
//    val node = helper.formulaToNode(formula)
//    runTactic(defaultNoArith, node)
//  }
}
