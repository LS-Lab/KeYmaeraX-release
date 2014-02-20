package pdl.tests

object RunAllTests {
  def main(args:Array[String]):Unit = {
    val allTests = ProgramParserTests.tests ++
                   CursorRewriteTests.tests ++
                   LFRewriteTests.tests
    TestHarness.runSuite(allTests)
  }
}