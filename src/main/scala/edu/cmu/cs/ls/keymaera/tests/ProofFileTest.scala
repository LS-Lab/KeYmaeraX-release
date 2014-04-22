package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import scala.swing.FileChooser
import java.io.File
import edu.cmu.cs.ls.keymaera.parser._
import javax.swing.JOptionPane

object ProofFileTest {
  def main(args:Array[String]):Unit = {
    val chooser = new FileChooser()
    chooser.selectedFile_= (new File("/home/nfulton/dev/research/KeYmaera4/examples/lemmas/axioms2.key.alp"))
//    chooser.showDialog(null, "Parse and print")
    
    val fileContents = io.Source.fromFile(chooser.selectedFile).mkString

    val kp = new KeYmaeraParser()
    
    val p = kp.ProofFileParser
    val result = p.runParser(fileContents)
    
    result.map(e => e match {
      case LoadedAxiom(n,f) => println(n + ":" + KeYmaeraPrettyPrinter.stringify(f))
      case LoadedLemma(n,f,_) => println(n + ":" + KeYmaeraPrettyPrinter.stringify(f)) 
    })
    
    //trying to build programs...
    val xVar = new Variable("X", None, Real)
    val assign = new Assign(xVar, Number(1))
    val e = new Imply(True, BoxModality(assign,True))
    val asdfsd = new Equals(Real, xVar, Number(1))
  }
}
