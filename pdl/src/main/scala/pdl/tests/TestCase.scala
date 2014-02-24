package pdl.tests

//////////////////////////////////////////////////////////////////////////////
object TestHarness {
  def runSuite(tests:Iterable[TestCase]) = {
    //Enforce an ordering on the tests, because later tests assume earlier tests
    //e.g. the multi-stage tests assume cursor rules work, and cursor rules 
    //assume that parsing works.
    var results = List[Boolean]()
    for(test <- tests) {
      results = results :+ test.runTest
    }
      
//      tests.map(_.runTest)
    
    println("TEST FAILURES: " + 
        results.filter(!_).size.toString() + 
        " / " + 
        results.size.toString())
  }
}
  
//////////////////////////////////////////////////////////////////////////////
abstract class TestCase {
  val name    = this.getClass().getSimpleName().replace("$","")
  
  def message : String
  def result  : Boolean
    
  def runTest:Boolean = {
    val theMessage = 
      if(!message.equals("")) {
        " (message: " + message + ")" 
      }
      else {
        message
      }
    
    if(this.result) {
      println("OK\t" + this.name + theMessage)
      true
    }
    else {
      println("NOT OK\t" + this.name + theMessage)
      false
    }
  }

}
