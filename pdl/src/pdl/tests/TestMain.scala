package pdl.tests

import pdl.core.LFRewrite

object TestMain {
  def main(args:Array[String]):Unit = {
    import pdl.core._
    
    val c = new Channel("c")
    
    val channels : Set[Channel] = Set[Channel]() + c 
    
    val x = PVar(new pdl.core.Var("x"))
    val y = PVar(new pdl.core.Var("y"))
    
    val xAssign = NonDetAssignment(x)
    val yAssign = NonDetAssignment(y)
    
    val rcv = Receive(c,Set() + x)
    
//    val originalProgram = Parallel(
//        Receive(c,Set() + x),
//        Send(c, Set()+x, Number("0")) )
    
    val originalProgram = STClosure(Sequence(xAssign,rcv))
    
    val originalProgramWithCursor = CursorBefore(originalProgram)

    val rewrittenProgram = CursorRewrite.rewrite(originalProgramWithCursor, channels)
        
    val program = rewrittenProgram 
//    val program = originalProgram
    
    val str = PrettyPrinter.programToString(program)
    
    println("Initial program: " + str)
    println("Result of cursor rewrites: " + PrettyPrinter.programToString(rewrittenProgram))
  
   //Linear form.
   val lf = rewrittenProgram match {
      case CursorBefore(p) => LFRewrite.rewrite(rewrittenProgram, channels).toString()
      case _ => LFRewrite.rewrite(program, channels).toString()
    }
    
    println("Final result: " + lf.toString())
  }
  
}