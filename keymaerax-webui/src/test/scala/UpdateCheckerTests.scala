import edu.cmu.cs.ls.keymaerax.hydra.{StringToVersion, UpdateChecker}
import org.scalatest.{Matchers, FlatSpec}

/**
  * Created by nfulton on 12/9/15.
  */
class UpdateCheckerTests extends FlatSpec with Matchers {
  "version comparison" should "work" in {
    StringToVersion("4.0b1") compareTo StringToVersion("4.0b1") shouldBe 0
    StringToVersion("4.0b1") >= StringToVersion("4.0b1") shouldBe true
    StringToVersion("4.0b1") > StringToVersion("4.0a99") shouldBe true
    StringToVersion("5.0") > StringToVersion("4.0") shouldBe true
    StringToVersion("4.0") > StringToVersion("4.0b99") shouldBe true
  }
  "update checker" should "check db for updates" in {
    UpdateChecker.needDatabaseUpgrade().get shouldBe false
  }
}
