package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import scala.swing.FileChooser
import java.io.File
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import javax.swing.JOptionPane

object ParserTest {
  def main(args:Array[String]):Unit = {
    val file = false
    val theString = 
      if(file) {
        val chooser = new FileChooser()
        chooser.selectedFile_= (new File("/home/nfulton/dev/research/KeYmaera4/examples/dev/t/positive/"))
        io.Source.fromFile(chooser.selectedFile).mkString
      }
      else {
        val formula = JOptionPane.showInputDialog("Enter your formula:")
        "ProgramVariables.\n" + "R x." + "\nEnd." +
        "Problem.\n" + formula + "\nEnd."
      }
    val p = new KeYmaeraParser()
    val result = p.runParser(theString)
    
    println(KeYmaeraPrettyPrinter.stringify(result))
    
    //trying to build programs...
    val xVar = new Variable("X", None, Real)
    val assign = new Assign(xVar, Number(1))
    val e = new Imply(True, BoxModality(assign,True))
    val asdfsd = new Equals(Real, xVar, Number(1))
  }
}
