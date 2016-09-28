package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.hydra.{StringToVersion, VersionString}
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}

/**
  * Tests the update checker string->version conversion.
  * @author Stefan Mitsch
  */
class UpdateCheckerTests extends FlatSpec with Matchers with BeforeAndAfterEach {

  // versions in ascending order
  private val versionStrings =
    ("4.0",   VersionString(4, 0, -1, None, None)) ::
    ("4.1a1", VersionString(4, 1, -1, Some('a'), Some(1))) ::
    ("4.1a2", VersionString(4, 1, -1, Some('a'), Some(2))) ::
    ("4.1a",  VersionString(4, 1, -1, Some('a'), None))  ::
    ("4.1b",  VersionString(4, 1, -1, Some('b'), None)) ::
    ("4.1",   VersionString(4, 1, -1, None, None)) ::
    ("4.1.1", VersionString(4, 1, 1, None, None)) ::
    ("4.2", VersionString(4, 2, -1, None, None)) ::
    ("11.33x7", VersionString(11, 33, -1, Some('x'), Some(7))) ::
    ("11.33.999", VersionString(11, 33, 999, None, None)) :: Nil

  private val invalidVersionStrings = "4" :: "4.1a22" :: "4.1a.2" :: "4.1.1a" :: Nil

  "Version string converter" should "convert correct version strings" in {
    versionStrings.map({case (s, v) => (s, StringToVersion(s), v)}).
      foreach({case (s, actual, expected) => withClue(s"Parsed $s") { actual shouldBe expected}})
  }

  it should "refuse to convert invalid strings" in {
    invalidVersionStrings.foreach(s => withClue(s"Parsed $s") {
      the [Exception] thrownBy StringToVersion(s) should have message s"requirement failed: Unexpected version string $s" })
  }

  "Update checker" should "correctly compare versions" in {
    val versions: Map[String, Int] = versionStrings.map(_._1).zipWithIndex.toMap
    versionStrings.map(_._1).combinations(2).foreach({case (s1 :: s2 :: Nil) =>
      withClue (s"Comparing $s1 with $s2") {
        StringToVersion(s1).compareTo(StringToVersion(s2)) shouldBe versions(s1).compareTo(versions(s2))
      }
    })
  }
}
