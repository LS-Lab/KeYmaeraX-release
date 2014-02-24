package pdl.main
import pdl.core.Program
import pdl.core.Parser
import pdl.core.PdlRewrite

/**
 * Command line interface for the rewrite pipeline.
 */
object PDL {
  def main(args:Array[String]):Unit = {
    if(args.size < 1) {
      println("PDL Rewriter\nUsage: rewrite <file1> <file2>\nOutput: Rewritten programs delimited by double-newlines.")
      System.exit(0)
    }
    else {
      //Pass each file through the pipeline and separate output with double-newlines.
      try {
        println( args.map(parseFile(_)).map(PdlRewrite.rewrite(_)).map(_.prettyString).reduce(_+"\n\n"+_) )
      }
      catch {
        //die with an error code.
        case e:Exception => System.err.println("Encountered unknown error:" + e.toString); System.exit(-1)
      }
    }
  }
  
  def parseFile(name:String):Program = {
    val contents = scala.io.Source.fromFile(name).mkString
    Parser.parseProgram(contents)
  }
}