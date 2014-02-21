package pdl.tests

import pdl.core._

object LFRewriteTests {
  //////////////////////////////////////////////////////////////////////////////
  // Definitions
  //////////////////////////////////////////////////////////////////////////////
  
  val xP = PVar(new Var("x"))
  /**
   * A program without any sync operations.
   */
  val nosyncP = Assignment(xP, Number("1"))
  
  /**
   * A program with a non-contextual sync operation.
   */
  val cfP = Send(new Channel("cfc"), Set(xP), Number("1"))
  
  val c = new Channel("c")
  
  /**
   * A contextual program
   */
  val sendOnC = Send(c, Set(xP), Number("1"))
  
  abstract class LFRewriteTest extends TestCase {
    val original : Program
    val expected : LFResult
    val context  : Set[Channel]
    
    def message = {
      val origStr = "Original: " + PrettyPrinter.programToString(original)
      val resultStr = "  Result: " + (try {
        val result = LFRewrite.rewrite(original, context)
        PrettyPrinter.LFResultToString(result)
      }
      catch {
        case e:LRDoesNotApply => "LF Rule Does Not Apply"
        case e:CRDoesNotApply => "Cursor Rule Failed"
        case e:Exception      => "ERROR"
      })
      val expectedStr = "  Expected: " + PrettyPrinter.LFResultToString(expected)
      origStr + resultStr + expectedStr
    }
    def result = LFRewrite.rewrite(original, context).equals(expected)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // L1
  //////////////////////////////////////////////////////////////////////////////
  object L1_applies extends LFRewriteTest {
    val original = CursorAfter(nosyncP)
    val expected = LinearForm(Some(nosyncP), Some(Bottom()), None, None)
    val context  = Set[Channel]()
  }
  
  object L1_doesNotApply extends LFRewriteTest {
    val original = CursorBefore(nosyncP)
    val expected = LinearForm(None,None,None,None)
    val context  = Set[Channel]()
    
    override def result = try {
      L1.apply(original, context)
      false
    } catch {
      case e:LRDoesNotApply => true
      case e:Exception      => false
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  // L2
  //////////////////////////////////////////////////////////////////////////////
  object L2_EpsilonVanilla extends LFRewriteTest {
    val original = CursorBefore(Epsilon())
    val expected = LinearForm(None, Some(Epsilon()), None, None)
    val context  = Set[Channel]()
  }
  
  /**
   * Initially failed b/c splitSequence had a bug. That method is now 
   * reimplemented and significantly simpler because it relies upon sequences
   * having a normal form.
   */
  object L2_EpsilonWithoutU extends LFRewriteTest {
    val original  = Sequence(CursorBefore(Epsilon()), nosyncP)
    val expected  = LinearForm(None, Some(Epsilon()), None, Some(nosyncP))
    val context   = Set[Channel]()
  }
  
  object L2_EpsilonWithU extends LFRewriteTest {
    val original  = Sequence(nosyncP, Sequence(CursorBefore(Epsilon()), nosyncP))
    val expected  = LinearForm(Some(nosyncP), Some(Epsilon()), None, Some(nosyncP))
    val context   = Set[Channel]()
  }
  
  object L2_dna extends LFRewriteTest {
    val original = CursorBefore(nosyncP)
    val expected = LinearForm(None,None,None,None)
    val context  = Set[Channel]()
    
    override def result = try {
      L2.apply(original, context)
      false
    } catch {
      case e:LRDoesNotApply => true
      case e:Exception      => false
    }
  }
  
  object L2_sendOnC extends LFRewriteTest {
    val original = CursorBefore(sendOnC)
    val expected = LinearForm(None, Some(sendOnC), None, None)
    val context  = Set(c)
  }

  /**
   * .[[c!{x}1]];ε;(c!{x}1)*
   */
  object L2_hangingCursor extends LFRewriteTest {
    val orig = Sequence(CursorBefore(sendOnC),Sequence(Epsilon(),sendOnC))
    val original = CursorRewrite.rewrite(orig, Set(c))
    val expected = LinearForm(None, Some(sendOnC), None, Some(Sequence(Epsilon(),sendOnC)))
    val context  = Set(c)
  }
  
  /**
   * Originally failed -- nosyncP occurred twice due to typo in Sequence.append
   */
  object L2_final extends LFRewriteTest {
    val context  = Set(c)
    val orig     = CursorBefore(Sequence(nosyncP, 
                                Sequence(sendOnC, 
                                Sequence(nosyncP,
                                Sequence(Epsilon(), 
                                         cfP)))))
    val original = CursorRewrite.rewrite(orig, context)
    val expected = LinearForm(Some(nosyncP),
                              Some(sendOnC),
                              None,
                              Some(Sequence(nosyncP, Sequence(Epsilon(), cfP))))
    override def result = 
      super.result
  }
  
  object L1_L2_split extends LFRewriteTest {
    val original = Sequence(nosyncP, CursorBefore(Epsilon()))
    val expected = LinearForm(Some(nosyncP), Some(Epsilon()), None, None)
    val context  = Set[Channel]()
  }
  
  //TODO non-epsilon communication

  
  //////////////////////////////////////////////////////////////////////////////
  // L3
  //////////////////////////////////////////////////////////////////////////////
  
  object L3_vanillaEps extends LFRewriteTest {
    val original = CursorBefore(Choice(Epsilon(), Epsilon()))
    
    val left = LinearForm(None,Some(Epsilon()),None,None)
    val right = left
    
    val expected = LFChoice(left,right)
    
    val context = Set[Channel]()
  }
  
  object L3_epsWithU extends LFRewriteTest {
    val original = Sequence(nosyncP, CursorBefore(Choice(CursorBefore(Epsilon()), CursorBefore(Epsilon()))))
    
    val left = LinearForm(Some(nosyncP),Some(Epsilon()),None,None)
    val right = left
    
    val expected = LFChoice(left,right)
    
    val context = Set[Channel]()
  }
  
  object L3_sendsyncWithU extends LFRewriteTest {
    val original = Sequence(nosyncP, CursorBefore(Choice(CursorBefore(sendOnC), CursorBefore(sendOnC))))
    
    //expected.
    val left = LinearForm(Some(nosyncP),Some(sendOnC),None,None)
    val right = left
    val expected = LFChoice(left,right)
    
    val context = Set[Channel](c)
  }
  
  //TODO test something with a gamma.
  
  //TODO test something with an intermediate
  
  //////////////////////////////////////////////////////////////////////////////
  // L4
  //////////////////////////////////////////////////////////////////////////////
  
  
  object L4_noUOrV extends LFRewriteTest {
    val orig = CursorBefore(STClosure(sendOnC))
    
    val context  = Set(c)
    val original = CursorRewrite.rewrite(orig, context)
    val expected = LFChoice(
        LinearForm(None, Some(sendOnC), None, Some(Sequence(Epsilon(), STClosure(sendOnC)))),
        LinearForm(None, Some(Epsilon()), None, None))
  }
  
  //TODO L4_noU
  //TODO L4_noV
  
  
  //////////////////////////////////////////////////////////////////////////////
  // Run tests
  //////////////////////////////////////////////////////////////////////////////
  def tests =  L1_applies          ::
               L1_doesNotApply     ::
               L2_EpsilonVanilla   ::
               L2_EpsilonWithoutU  ::
               L2_EpsilonWithU     ::
               L2_dna              ::
               L2_sendOnC          ::
               L1_L2_split         ::
               L2_hangingCursor    ::
               L2_final            :: 
               L3_vanillaEps       ::
               L3_epsWithU         ::
               L3_sendsyncWithU    ::
               L4_noUOrV           ::
               Nil
  
  def main(args:Array[String]):Unit = {
    TestHarness.runSuite(tests)
  }
}