package pdl.tests

import pdl.core._

object MergeRewriteTests {

  //////////////////////////////////////////////////////////////////////////////
  // Definitions
  //////////////////////////////////////////////////////////////////////////////
  abstract class MergeRewriteTest extends TestCase {
    val left     : LinearForm
    val right    : LinearForm
    val expected : Program
    val context  : Set[Channel]
    
    def rewriteResult = MergeRewrite.rewrite(left, right)
    def result        = rewriteResult.equals(expected)
    
    def message = "Original: " + left.prettyString + "~" + right.prettyString + "\t" +
                  "Expected: " + expected.prettyString + "\t" + 
                  "Result: " + rewriteResult.prettyString
  }
  
  
  val x = new PVar(new Var("x"))
  val y = new PVar(new Var("y"))
  val c = new Channel("c")
  val d = new Channel("d")
  
  val sendOnC = Send(c,Number("1"))
  val sendOnD = Send(c,Number("1"))
  
  val receiveXonC = Receive(c,Set(x))
  val receiveYonC = Receive(c,Set(y))
  val receiveXonD = Receive(d,Set(x))
  
  val nosyncP = NonDetAssignment(x)
  
  //////////////////////////////////////////////////////////////////////////////
  // M1
  //////////////////////////////////////////////////////////////////////////////
  object M1_appliesVanilla extends MergeRewriteTest {
    val left = LinearForm(None, Some(sendOnC), None, None)
    val right = LinearForm(None, Some(receiveXonC), None, None)
    val context = Set(c)
    val expected = Forward(c, Set(x), Number("1"))
  }
  
  object M1_appliesLeft extends MergeRewriteTest {
    val left = LinearForm(Some(nosyncP), Some(sendOnC), None, None)
    val right = LinearForm(Some(nosyncP), Some(receiveXonC), None, None)
    val context = Set(c)
    val expected = Sequence(Parallel(nosyncP,nosyncP), Forward(c, Set(x), Number("1")))
  }
  
  object M1_appliesRight extends MergeRewriteTest {
    val left = LinearForm(None, Some(sendOnC), None, Some(nosyncP))
    val right = LinearForm(None, Some(receiveXonC), None, Some(nosyncP))
    val context = Set(c)
    val expected = Sequence(Forward(c, Set(x), Number("1")),Remainder(Parallel(nosyncP,nosyncP)))
  }
  
  object M1_appliesLR extends MergeRewriteTest {
    val left = LinearForm(Some(nosyncP), Some(sendOnC), None, Some(nosyncP))
    val right = LinearForm(Some(nosyncP), Some(receiveXonC), None, Some(nosyncP))
    val context = Set(c)
    val expected = Sequence(Parallel(nosyncP,nosyncP), 
                   Sequence(Forward(c, Set(x), Number("1")),
                            Remainder(Parallel(nosyncP,nosyncP))))
  }
  
  object M1_wrongChannels extends MergeRewriteTest {
    val left = LinearForm(None, Some(sendOnC), None, None)
    val right = LinearForm(None, Some(receiveXonD), None, None)
    val context = Set(c)
    val expected = null
    
    override def message = "Sending on C but receiveing on D"
      
    override def result = try {
      rewriteResult
      false
    }
    catch {
      case e:DeadlockOnMerge => true
      case e:Exception       => false
    }
  }
  
   /**
   * v is ignored in M1. I'm not sure if the correct behavior here is to throw
   * and exception or to simply ignore the input. Therefore, I'm considering it
   * an error to be conservative.
   * 
   * This test form isn't mimicked below because the logic it's testing happens
   * at the top of the merge algorithm.
   */
  object M1_vDefined extends MergeRewriteTest {
    val left = LinearForm(Some(nosyncP), Some(sendOnC), Some(nosyncP), None)
    val right = LinearForm(Some(nosyncP), Some(receiveXonC), Some(nosyncP), None)
    val context = Set(c)
    val expected = Sequence(Parallel(nosyncP,nosyncP), Forward(c, Set(x), Number("1")))
    
    override def message = "v is defined and hsould not be."
      
    //Ensure that rewrite fails when v is defined.
    //For the alternative interpretation (ignoring v), simply remove the overriding
    //method.
    override def result = try {
      rewriteResult
      false
    }
    catch {
      case e:EncounteredVInMergeRewrite => true
      case e:DeadlockOnMerge            => true
      case e:Exception                  => false
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // M2
  //////////////////////////////////////////////////////////////////////////////
  object M2_appliesVanilla extends MergeRewriteTest {
    val left = LinearForm(None, Some(receiveYonC), None, None)
    val right = LinearForm(None, Some(receiveXonC), None, None)
    val context = Set(c)
    val expected = Receive(c, Set(x,y))
  }
  
  object M2_appliesLeft extends MergeRewriteTest {
    val left = LinearForm(Some(nosyncP), Some(receiveYonC), None, None)
    val right = LinearForm(Some(nosyncP), Some(receiveXonC), None, None)
    val context = Set(c)
    val expected = Sequence(Parallel(nosyncP,nosyncP), Receive(c, Set(x,y)))
  }
  
  object M2_appliesRight extends MergeRewriteTest {
    val left = LinearForm(None, Some(receiveYonC), None, Some(nosyncP))
    val right = LinearForm(None, Some(receiveXonC), None, Some(nosyncP))
    val context = Set(c)
    val expected = Sequence(Receive(c, Set(x,y)),Remainder(Parallel(nosyncP,nosyncP)))
  }
  
  object M2_appliesLR extends MergeRewriteTest {
    val left = LinearForm(Some(nosyncP), Some(receiveYonC), None, Some(nosyncP))
    val right = LinearForm(Some(nosyncP), Some(receiveXonC), None, Some(nosyncP))
    val context = Set(c)
    val expected = Sequence(Parallel(nosyncP,nosyncP), 
                   Sequence(Receive(c, Set(x,y)),
                            Remainder(Parallel(nosyncP,nosyncP))))
  }
  
  object M2_wrongChannels extends MergeRewriteTest {
    val left = LinearForm(None, Some(receiveYonC), None, None)
    val right = LinearForm(None, Some(receiveXonD), None, None)
    val context = Set(c)
    val expected = null
    
    override def message = "Receive on separate channels fails."
    
    override def result = try {
      rewriteResult
      false
    }
    catch {
      case e:DeadlockOnMerge => true
      case e:Exception       => false
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // M3
  //////////////////////////////////////////////////////////////////////////////
  object M3_appliesVanilla extends MergeRewriteTest {
    val left = LinearForm(None, Some(Forward(c, Set(x), Number("1"))), None, None)
    val right = LinearForm(None, Some(receiveXonC), None, None)
    val context = Set(c)
    val expected = Forward(c, Set(x), Number("1"))
  }
  
  object M3_appliesCombine extends MergeRewriteTest {
    val left = LinearForm(None, Some(Forward(c, Set(x), Number("1"))), None, None)
    val right = LinearForm(None, Some(receiveYonC), None, None)
    val context = Set(c)
    val expected = Forward(c, Set(x,y), Number("1"))
  }
  
  object M3_appliesLeft extends MergeRewriteTest {
    val left = LinearForm(Some(nosyncP), Some(Forward(c, Set(x), Number("1"))), None, None)
    val right = LinearForm(Some(nosyncP), Some(receiveXonC), None, None)
    val context = Set(c)
    val expected = Sequence(Parallel(nosyncP,nosyncP), Forward(c, Set(x), Number("1")))
  }
  
  object M3_appliesRight extends MergeRewriteTest {
    val left = LinearForm(None, Some(Forward(c, Set(x), Number("1"))), None, Some(nosyncP))
    val right = LinearForm(None, Some(receiveXonC), None, Some(nosyncP))
    val context = Set(c)
    val expected = Sequence(Forward(c, Set(x), Number("1")), Remainder(Parallel(nosyncP,nosyncP)))
  }
  
  object M3_appliesLR extends MergeRewriteTest {
    val left = LinearForm(Some(nosyncP), Some(Forward(c, Set(x), Number("1"))), None, Some(nosyncP))
    val right = LinearForm(Some(nosyncP), Some(receiveXonC), None, Some(nosyncP))
    val context = Set(c)
    val expected = Sequence(Parallel(nosyncP,nosyncP), 
                   Sequence(Forward(c, Set(x), Number("1")),
                            Remainder(Parallel(nosyncP,nosyncP))))
  }
  
  object M3_wrongChannels extends MergeRewriteTest {
    val left = LinearForm(None, Some(Forward(c, Set(x), Number("1"))), None, None)
    val right = LinearForm(None, Some(receiveXonD), None, None)
    val context = Set(c)
    val expected = null
    
    override def message = "Sending on C but receiveing on D"
      
    override def result = try {
      rewriteResult
      false
    }
    catch {
      case e:DeadlockOnMerge => true
      case e:Exception       => false
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // M4
  //////////////////////////////////////////////////////////////////////////////
  object M4_appliesVanilla extends MergeRewriteTest {
    val left = LinearForm(None, Some(Bottom()), None, None)
    val right = LinearForm(None, Some(Bottom()), None, None)
    val context = Set(c)
    val expected = Bottom()
  }
  
  object M4_appliesLeft extends MergeRewriteTest {
    val left = LinearForm(Some(nosyncP), Some(Bottom()), None, None)
    val right = LinearForm(Some(nosyncP), Some(Bottom()), None, None)
    val context = Set(c)
    val expected = Sequence(Parallel(nosyncP,nosyncP), Bottom())
  }
  
  
  //////////////////////////////////////////////////////////////////////////////
  // M5
  //////////////////////////////////////////////////////////////////////////////
  object M5_vanilla extends MergeRewriteTest {
    def diffeq(i:Int) = Eq(Derivative(x), Number(i.toString))

    val left = LinearForm(None, Some(Evolution(Set(diffeq(1)), True())), None, None)
    val right = LinearForm(None, Some(Evolution(Set(diffeq(2)), True())), None, None)
    val context = Set[Channel]()
    val expected = Evolution(Set(diffeq(1),diffeq(2)), And(True(),True()))
  }
  
  object M5_left extends MergeRewriteTest {
    def diffeq(i:Int) = Eq(Derivative(x), Number(i.toString))
    def evolution(i:Int) = Evolution(Set(diffeq(i)), True())
    
    val left = LinearForm(Some(nosyncP), Some(evolution(1)), None, None)
    val right = LinearForm(Some(nosyncP), Some(evolution(2)), None, None)
    val context = Set[Channel]()
    val expected = Sequence(Parallel(nosyncP, nosyncP), Evolution(Set(diffeq(1),diffeq(2)), And(True(),True())))
  }
  
  object M5_right extends MergeRewriteTest {
    def diffeq(i:Int) = Eq(Derivative(x), Number(i.toString))
    def evolution(i:Int) = Evolution(Set(diffeq(i)), True())
    
    val left = LinearForm(None, Some(evolution(1)), None, Some(nosyncP))
    val right = LinearForm(None, Some(evolution(2)), None, Some(nosyncP))
    val context = Set[Channel]()
    val expected = Sequence(Evolution(Set(diffeq(1),diffeq(2)), And(True(),True())), Remainder(Parallel(nosyncP, nosyncP)))
  }
  
  
  //////////////////////////////////////////////////////////////////////////////
  // Run tests
  //////////////////////////////////////////////////////////////////////////////
  def tests = M1_appliesVanilla ::
              M1_appliesLeft    ::
              M1_appliesRight   ::
              M1_appliesLR      ::
              M1_vDefined       ::
              M1_wrongChannels  ::
              M2_appliesVanilla ::
              M2_appliesLeft    ::
              M2_appliesRight   ::
              M2_appliesLR      ::
              M2_wrongChannels  ::
              M3_appliesVanilla ::
              M3_appliesCombine ::
              M3_appliesLeft    ::
              M3_appliesRight   ::
              M3_appliesLR      ::
              M3_wrongChannels  ::
              M4_appliesVanilla ::
              M4_appliesLeft    ::
              M5_vanilla        ::
              M5_left           ::
              M5_right          ::
              Nil
  
  def main(args:Array[String]):Unit = {
    TestHarness.runSuite(tests)
  }
}
