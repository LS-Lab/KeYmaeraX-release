package pdl.tests

import pdl.core._

object CursorRewriteTests {
  //////////////////////////////////////////////////////////////////////////////
  // Definitions
  //////////////////////////////////////////////////////////////////////////////
  
  val x = new PVar(new Var("x"))
  val y = new PVar(new Var("y"))
  val z = new PVar(new Var("z"))
  val c = new Channel("c")
  
  val cfp   = sendx(new Channel("NOT_IN_CTX")) //communication-free program.
  val nosyncP  = NonDetAssignment(x)
  
  def sendx(c:Channel)  = Send(c, Number("1"))
  def receivex(c:Channel) = Receive(c, Set(x))
      
  
  abstract class CursorRewriteTest extends TestCase {
    val original : Program
    val expected : Program
    val context  : Set[Channel]
    
    override def message = "Original: " + original.prettyString + 
      " Expected: " + expected.prettyString + 
      " Result: " + (try {
        CursorRewrite.rewrite(original, context).prettyString
      }catch {
        case e:Throwable => "ERROR"
      })
      
    override def result  = 
      CursorRewrite.rewrite(original, context).equals(expected)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // C1
  //////////////////////////////////////////////////////////////////////////////
  
  object C1_noCommunication extends CursorRewriteTest {
    val original = CursorBefore(cfp)
    val expected = CursorAfter(cfp)
    val context  = Set[Channel]()
  }
  
  object C1_communication extends CursorRewriteTest {
    val c = new Channel("c")
    val original = CursorBefore(sendx(c))
    val expected = CursorBefore(sendx(c))
    val context  = Set[Channel](c)

    override def result = {
      val applies    = C1.applies(original,context)
      val applyFails = try {
        C1.apply(original, context).equals(expected)
        false
      }
      catch {
        case e:CRDoesNotApply => true
        case e:Exception      => false
      }
      !applies && applyFails
    }
  }
  
  /**
   * We should not be able to rewrite bare variables, because #1 doesn't include
   * this as one of the program forms which can be processed by C1.
   */
  object C1_floatingVar extends CursorRewriteTest {
    val original = CursorBefore(x)
    val expected = CursorAfter(x)
    val context  = Set[Channel]()
    
    override def result = !super.result
  }
  
  
  //////////////////////////////////////////////////////////////////////////////
  // C2
  //////////////////////////////////////////////////////////////////////////////
  object c2_multistep extends CursorRewriteTest {
    val original = Sequence(CursorAfter(cfp), cfp)
    val expected = CursorAfter(Sequence(cfp, cfp))
    val context  = Set[Channel]()
  }
  
  object c2_multistep_by_c2 extends CursorRewriteTest {
    val original = Sequence(CursorAfter(cfp), cfp)
    val expected = CursorAfter(Sequence(cfp, cfp))
    val context  = Set[Channel]()
    
    override def result = C2.apply(original,context).equals(expected)
  }
  
  object c2_nostep extends CursorRewriteTest {
    val original = Sequence(CursorAfter(cfp), CursorBefore(cfp))
    val expected = original
    val context  = Set[Channel]()
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // C3
  //////////////////////////////////////////////////////////////////////////////
  abstract class C3Test extends CursorRewriteTest {
    val applies  : Boolean
    
    override def message = 
      PrettyPrinter.programToString(original) + 
      "-->" + 
      (try{PrettyPrinter.programToString(C3.apply(original,context))}catch{case e:Exception => e.toString()})

    override def result = if(applies) {
        C3.applies(original, context) &&
        C3.apply(original,context).equals(expected)
    } else {
      !C3.applies(original, context) && (try {
        C3.apply(original, context)
        false
      }
      catch {
        case e:CRDoesNotApply => true
        case e:Exception      => false
      })
    }
  }
  
  object c3_union extends C3Test {
    val applies  = true
    val original = CursorBefore(Choice(cfp,cfp))
    val expected = CursorBefore(Choice(CursorAfter(cfp), CursorAfter(cfp)))
    val context  = Set[Channel]()
  }
  
  object c3_doesNotApply extends C3Test {
    val applies = false
    val original = CursorBefore(cfp)
    val expected = original
    val context = Set[Channel]()
  }
  
  object c3_innerDoesNotApply extends C3Test {
    val applies = false
    val original = CursorBefore(Choice(CursorBefore(cfp),cfp))
    val expected = original
    val context = Set[Channel]()
  }

  //////////////////////////////////////////////////////////////////////////////
  // C4
  //////////////////////////////////////////////////////////////////////////////
  object c4_applies extends CursorRewriteTest {
    val original = CursorBefore(Choice(CursorAfter(cfp), CursorAfter(cfp)))
    val expected = CursorAfter(Choice(cfp,cfp))
    val context  = Set[Channel]()
  }
  
  object c4_appliesByC4 extends CursorRewriteTest {
    val original = CursorBefore(Choice(CursorAfter(cfp), CursorAfter(cfp)))
    val expected = CursorAfter(Choice(cfp,cfp))
    val context  = Set[Channel]()
    
    override def result = C4.apply(original,context).equals(expected)
  }
  
  object c4_doesNotApply extends CursorRewriteTest {
    val original = Choice(CursorAfter(cfp), CursorAfter(cfp))
    val expected = original
    val context  = Set[Channel]()
    
    override def result = try {
      C4.apply(original,context)
      false
    }
    catch {
      case e:CRDoesNotApply => true
      case e:Exception      => false
    }
  }
  
  object c4_doesNotApplyBecuaseCursorBefore extends CursorRewriteTest {
    val original = Choice(CursorBefore(cfp), CursorAfter(cfp))
    val expected = original
    val context  = Set[Channel]()
    
    override def result = try {
      C4.apply(original,context)
      false
    }
    catch {
      case e:CRDoesNotApply => true
      case e:Exception      => false
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // C5
  //////////////////////////////////////////////////////////////////////////////
  object c5_applies extends CursorRewriteTest {
    val original = CursorBefore(STClosure(cfp))
    val expected = CursorAfter(STClosure(cfp))
    val context  = Set[Channel]()
  }
  object c5_appliesByC5 extends CursorRewriteTest {
    val original = CursorBefore(STClosure(cfp))
    val expected = CursorAfter(STClosure(cfp))
    val context  = Set[Channel]()
    
    override def result = C5.apply(original, context).equals(expected)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // C6
  //////////////////////////////////////////////////////////////////////////////
  object c6_applies extends CursorRewriteTest {
    val original = CursorBefore(STClosure(CursorAfter(cfp)))
    val expected = CursorAfter(STClosure(cfp))
    val context  = Set[Channel]()
  }
  object c6_appliesByC6 extends CursorRewriteTest {
    val original = CursorBefore(STClosure(CursorAfter(cfp)))
    val expected = CursorAfter(STClosure(cfp))
    val context  = Set[Channel]()
    
    override def result = C6.apply(original, context).equals(expected)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // TODO-nrf: C7-C9
  //////////////////////////////////////////////////////////////////////////////
  
  
  //////////////////////////////////////////////////////////////////////////////
  // Precursors to other tests, usually because the other test failed with a
  // CRDoesNotApply exception.
  //////////////////////////////////////////////////////////////////////////////
  /**
   * Initially failed.
   */
  object L2_precursorSingleStep extends CursorRewriteTest {
    val original = CursorBefore(Sequence(Epsilon(), Assignment(x, Number("1"))))
    val expected = Sequence(CursorAfter(Epsilon()), Assignment(x, Number("1")))
    val context  = Set[Channel]()
    
    override def result = 
      C1.applies(original,context) && C1.apply(original,context).equals(expected)
  }
  /**
   * This test SHOULD fail after we've cleaned up the test suite for LR rules.
   * To make the test fail, go into DS and remove the Epsilon logic from C1.
   */
  object L2_precursor extends CursorRewriteTest {
    val original = CursorBefore(Sequence(Epsilon(), Assignment(x, Number("1"))))
    val expected = CursorAfter(Sequence(Epsilon(), Assignment(x, Number("1"))))
    val context  = Set[Channel]() 
  }
  
  /**
   * Initially failed. Real bug in C1!
   */
  object L3_precursor extends CursorRewriteTest {
    val original = Sequence(CursorBefore(nosyncP), 
                                Sequence(sendx(c), 
                                Sequence(nosyncP,
                                Sequence(Epsilon(), cfp))))
    val expected = Sequence(nosyncP,
                   Sequence(CursorBefore(sendx(c)),
                   Sequence(nosyncP,
                   Sequence(Epsilon(), cfp))))
    val context = Set[Channel](c)
    
    override def message = 
      "C1 rewrites .(a;b) into (.a;b) before applying, and C2 rewrites right-hand sequences correctly"
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // Run tests
  //////////////////////////////////////////////////////////////////////////////
  def tests =//C1 tests
             C1_noCommunication ::
             C1_floatingVar ::
             C1_communication ::
             //C2 tests
             c2_multistep ::
             c2_multistep_by_c2 ::
             c2_nostep ::
             //C3 tests
             c3_union ::
             c3_doesNotApply ::
             c3_innerDoesNotApply ::
             //C4 tests
             c4_applies ::
             c4_doesNotApply ::
             c4_appliesByC4 ::
             c4_doesNotApplyBecuaseCursorBefore ::
             //C5 tests
             c5_applies ::
             c5_appliesByC5 ::
             //C6 tests
             c6_applies ::
             c6_appliesByC6 ::
             //Precursor tests
             L2_precursorSingleStep ::
             L2_precursor ::
             L3_precursor ::
             Nil
  def main(args:Array[String]):Unit = {
    TestHarness.runSuite(tests)
  }
}
