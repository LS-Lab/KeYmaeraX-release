import edu.cmu.cs.ls.keymaerax.tactics.{TacticToolBinding, Scheduler}
import edu.cmu.cs.ls.keymaerax.tools.Tool
import org.scalamock.scalatest.MockFactory
import org.scalatest.{Matchers, FlatSpec}

/**
 * Tests the scheduler.
 * Created by smitsch on 1/2/15.
 * @author Stefan Mitsch
 */
class SchedulerTests extends FlatSpec with Matchers with MockFactory  {

  private var scheduler: Scheduler = null
  private val tool = mock[Tool]
  private val tactic = mock[TacticToolBinding]

  it should "shutdown tool upon scheduler shutdown" in {
    scheduler = new Scheduler(List(tool))
    (tool.init _).expects(Map[String, String]()).once()
    (tool.isInitialized _).expects()
    scheduler.init(Map())
    (tool.shutdown _).expects().once()
    scheduler.shutdown()
  }

  it should "schedule tactic to tool upon dispatch" in {
    scheduler = new Scheduler(List(tool))
    (tool.init _).expects(Map[String, String]()).once()
    (tool.isInitialized _).expects()
    scheduler.init(Map())
    (tactic.execute _).expects(tool).once()
    scheduler.dispatch(tactic)
    // ScalaMock requires that all interaction is complete before the test ends,
    // so wait for threads to run to completion (shutdown)
    (tool.shutdown _).expects().once()
    scheduler.shutdown()
  }

  it should "dispatch to next available tool" in {
    val tool2 = mock[Tool]
    scheduler = new Scheduler(List(tool, tool2))
    (tool.init _).expects(Map[String, String]()).once()
    (tool.isInitialized _).expects()
    (tool2.init _).expects(Map[String, String]()).once()
    (tool2.isInitialized _).expects()
    scheduler.init(Map())
    // delay tool so that it is not available when next tactic is dispatched
    (tactic.execute _).expects(tool).once().onCall{ x: Tool => Thread.sleep(2000) }
    scheduler.dispatch(tactic)
    (tactic.compareTo _).expects(*).anyNumberOfTimes()
    (tactic.execute _).expects(tool2).once()
    scheduler.dispatch(tactic)
    // ScalaMock requires that all interaction is complete before the test ends,
    // so wait for threads to run to completion (shutdown)
    (tool.shutdown _).expects().once()
    (tool2.shutdown _).expects().once()
    scheduler.shutdown()
  }
}
