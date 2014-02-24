package pdl.tests

object TestMain {
  def main(args:Array[String]):Unit = {
    val allTests = ProgramParserTests.tests     ++
                   CursorRewriteTests.tests     ++
                   LFRewriteTests.tests         ++
                   MergeRewriteTests.tests      ++
                   FormulaParserTests.tests     ++
                   MultiStageRewriteTests.tests 
    TestHarness.runSuite(allTests)
  }
}
