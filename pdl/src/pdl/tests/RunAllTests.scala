package pdl.tests

object RunAllTests {
  def main(args:Array[String]):Unit = {
    val allTests = ProgramParserTests.tests ++
                   CursorRewriteTests.tests ++
                   LFRewriteTests.tests     ++
                   MergeRewriteTests.tests
    TestHarness.runSuite(allTests)
  }
}