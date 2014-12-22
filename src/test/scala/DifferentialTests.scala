import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl.locateSucc
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.{TacticLibrary, TacticWrapper, Tactics}
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tests
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{Matchers, FlatSpec}

/**
 * Created by nfulton on 12/1/14.
 */
class DifferentialTests extends FlatSpec with Matchers {
  val helper = new ProvabilityTestHelper((x) => println(x))

  //Constants
  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  def d(e : Variable) = Derivative(Real, e)


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
  // TODO test configuration
  tool.init(Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel"))

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

//  /**
//   * runs the position tactic pt on the sequent * |- formula
//   * @param pt
//   * @param formula
//   */
//  def runPositionTacticOnFormula(pt : PositionTactic, formula : Formula) = {
//    val theTactic = pt.apply(new SuccPosition(0))
//    runTactic(theTactic, formulaToNode(formula))
//  }

  "Normal assignment" should "work" in {
//    val formula = BoxModality(
//      Assign(
//        Variable("x",None,Real),
//        Number(1)
//      ),
//      Equals(Real, Variable("x",None,Real), Number(1))
//    )

//    val node = formulaToNode(ProvabilityTestHelper.parseFormula("x^4 + 2*y^2 = 2*y^2 + x^4"))
//
//    ProvabilityTestHelper.tacticClosesProof(
//      TacticLibrary.default,
//      node) should be (true)
//
//    ProvabilityTestHelper.runTacticWithTimeout(999999, TacticLibrary.default, node) should not be (None)

//    val formula = new KeYmaeraParser().parseBareExpression("[x:=1]x=1").asInstanceOf[Formula]
//    val result = runTactic(TacticLibrary.default, formulaToNode(formula))
//    result.isClosed() should be (true)
  }

  "Assignment using assignT" should "Not throw initialization exceptions" in {
    val formula = BoxModality(
      Assign(
        Variable("x",None,Real),
        Number(1)
      ),
      Equals(Real, Variable("x",None,Real), Number(1))
    )

    val result = runTactic(TacticLibrary.locateSucc(TacticLibrary.assignment), formulaToNode(formula))


    runDefault(runDefault(result)).isClosed() should be (true)
  }

  /**
   * ignored atm while we make sure all the other pieces fit together.
   */
  "Assignment to derivatives" should "ignore me" in {}

  ignore should "work" in {
    val formula = BoxModality(
      Assign(Derivative(Real, x), Number(2)),
      GreaterThan(Real, Derivative(Real, x), Number(0))
    )
//    val formula = parse("[ x' := 2 ] x' > 0")

    val result = runTactic(TacticLibrary.locateSucc(TacticLibrary.derivativeAssignment), formulaToNode(formula))

    val anOpenNode = result.openGoals().last

    val resultOnOpenNode = runDefault(anOpenNode)

    report(resultOnOpenNode)

    runDefault(resultOnOpenNode).isClosed() should be (true)
  }

  "differential induction" should "work" in {
    val formula = parse("[x' = 1;] x>=0")
    val expectedFormula = parse("1 >= 0") //?

    //apply the di rule
    val di = runTactic(TacticLibrary.locateSucc(TacticLibrary.differentialInduction), formulaToNode(formula))
    //apply the assign rule.
    val assign = runTactic(TacticLibrary.locateSucc(TacticLibrary.derivativeAssignment), runDefault(di))

    val result = assign
    report(result)
  }

  "induction with invariant input" should "work with a bit of help" in {
    val sequent = new Sequent(Nil,
      scala.collection.immutable.IndexedSeq(helper.parseFormula("x>0")),
      scala.collection.immutable.IndexedSeq(helper.parseFormula("[x' = 1;]x>-1")))

    val node = new RootNode(sequent)
    val invariant = helper.parseFormula("x > 0")

    val positionTactic = differentialInvariant(Some(invariant))
    val tactic = helper.positionTacticToTactic(positionTactic)

    helper.runTactic(tactic, node)
    val diffInductionTactic = helper.positionTacticToTactic(TacticLibrary.differentialInduction)
    helper.runTactic(diffInductionTactic*, node) //saturate?
    helper.runTactic(TacticLibrary.default, node)
    helper.runTactic(TacticLibrary.default, node)

    helper.report(node)
  }





  //First class of tests.
//  {
//    val formula = parse("[x'=1;]x >= 0")
//    val expectedFormula = parse("1 >= 0")
//
//    "DiffInd" should "step when there is no evolution domain constraint" in {
//      val result = runTactic(TacticLibrary.locateSucc(TacticLibrary.differentialInduction), formulaToNode(formula))
//      val secondResult = runTactic(TacticLibrary.locateSucc(TacticLibrary.boxAssignT), result)
//      println(secondResult.openGoals().map(g => g.sequent.toString() + "\n"))
//    }
//
////    "default" should "close when there is no evolution domai nconstraint" in {
////      val result = runTactic(TacticLibrary.default, formulaToNode(formula))
////      report(result)
////    }
//
//  }




}
