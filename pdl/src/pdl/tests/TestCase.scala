package pdl.tests

//////////////////////////////////////////////////////////////////////////////
object TestHarness {
  def runSuite(tests:Iterable[TestCase]) = {
    val results = tests.map(_.runTest)
    
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