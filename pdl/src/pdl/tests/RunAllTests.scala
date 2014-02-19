package pdl.tests

object RunAllTests {
  def main(args:Array[String]):Unit = {
    val allTests = CursorRewriteTests.tests ++ ProgramParserTests.tests
    TestHarness.runSuite(allTests)
  }
}